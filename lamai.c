/* Lama SM Bytecode interpreter */

# include <string.h>
# include <stdio.h>
# include <errno.h>
# include <stdlib.h>
# include <math.h>
# include <assert.h>
# include <stdbool.h>
#include <stdarg.h>

# include "runtime/runtime.h"

#define swap(x,y) do {    \
   typeof(x) _x = x;      \
   typeof(y) _y = y;      \
   x = _y;                \
   y = _x;                \
 } while(0)

//#define DEBUG

void *__start_custom_data;
void *__stop_custom_data;

char *code_stop_ptr;

extern size_t __gc_stack_top, __gc_stack_bottom;
//extern void __gc_root_scan_stack();

/* The unpacked representation of bytecode file */
typedef struct {
    char *string_ptr;              /* A pointer to the beginning of the string table */
    int  *public_ptr;              /* A pointer to the beginning of publics table    */
    char *code_ptr;                /* A pointer to the bytecode itself               */
    int  *global_ptr;              /* A pointer to the global area                   */
    int   stringtab_size;          /* The size (in bytes) of the string table        */
    int   global_area_size;        /* The size (in words) of global area             */
    int   public_symbols_number;   /* The number of public symbols                   */
    char  buffer[0];
} bytefile;

/* Gets a string from a string table by an index */
char* get_string (bytefile *f, int pos) {
    return &f->string_ptr[pos];
}

/* Gets a name for a public symbol */
char* get_public_name (bytefile *f, int i) {
    return get_string (f, f->public_ptr[i*2]);
}

/* Gets an offset for a public symbol */
int get_public_offset (bytefile *f, int i) {
    return f->public_ptr[i*2+1];
}

static void vfailure (char *s, va_list args) {
    fprintf(stderr, "*** FAILURE: ");
    vfprintf(stderr, s, args);   // vprintf (char *, va_list) <-> printf (char *, ...)
    exit(255);
}

void failure (char *s, ...) {
    va_list args;
    va_start(args, s);
    vfailure(s, args);
}

/* Reads a binary bytecode file by name and unpacks it */
bytefile* read_file (char *fname) {
    FILE *f = fopen (fname, "rb");
    long size;
    bytefile *file;

    if (f == 0) {
        failure ("%s\n", strerror (errno));
    }

    if (fseek (f, 0, SEEK_END) == -1) {
        failure ("%s\n", strerror (errno));
    }

    file = (bytefile*) malloc (sizeof(int)*4 + (size = ftell (f)));

    if (file == 0) {
        failure ("*** FAILURE: unable to allocate memory.\n");
    }

    rewind (f);

    if (size != fread (&file->stringtab_size, 1, size, f)) {
        failure ("%s\n", strerror (errno));
    }

    fclose (f);

    file->string_ptr  = &file->buffer [file->public_symbols_number * 2 * sizeof(int)];
    file->public_ptr  = (int*) file->buffer;
    file->code_ptr    = &file->string_ptr [file->stringtab_size];
    code_stop_ptr    = file->buffer + (size - 3 * sizeof(int)) - 1;
    file->global_ptr  = (int*) malloc (file->global_area_size * sizeof (int));

    return file;
}

#define INIT_STACK_SIZE 10000

typedef struct Lama_Loc {
    int idx;
    int tt;
} lama_Loc;

typedef void** StkId;

typedef struct Lama_CallInfo {
    int n_args, n_locs, n_caps;
    StkId base;
    char *ret_ip;
} lama_CallInfo;

typedef struct Lama_State {
    char *ip;
    StkId base;
    StkId stack_last;
    lama_CallInfo *base_ci;
    lama_CallInfo *ci;
    lama_CallInfo *end_ci;
    int size_ci;
    int stacksize;
    int n_globals;
} lama_State;

lama_State eval_state;

#define ttisnumber(o)(UNBOXED(o))
#define ttisstring(o)(!UNBOXED(o)&&TAG(TO_DATA(o)->tag)==STRING_TAG)
#define ttisarray(o)(!UNBOXED(o)&&TAG(TO_DATA(o)->tag)==ARRAY_TAG)
#define ttissexp(o)(!UNBOXED(o)&&TAG(TO_DATA(o)->tag)==SEXP_TAG)
#define ttisfunction(o)(!UNBOXED(o)&&TAG(TO_DATA(o)->tag)==CLOSURE_TAG)

#define cast(t,exp)((t)(exp))
#define check(p)assert(p)

#define stack_bottom cast(StkId, __gc_stack_bottom)
#define stack_top cast(StkId, __gc_stack_top)
#define foreach_stack(ptr) for(ptr = stack_bottom; ptr > stack_top; --ptr)
#define foreach_ci(L, ptr) for(ptr = L->base_ci; ptr >= L->ci; --ptr)

#define set_gc_ptr(ptr,v)ptr=cast(size_t,v)

#define alloc_stack(type,size)(cast(type*, malloc(sizeof(type) * size)) + size - 1)

static void lama_reallocstack(lama_State *L, int newsize) {
    StkId prev_base = L->base;
    StkId prev_stack_last = L->stack_last;
    StkId prev_stack_top = stack_top;
    StkId prev_stack_bottom = stack_bottom;
    int prev_stacksize = L->stacksize;

    set_gc_ptr(__gc_stack_bottom, alloc_stack(void*, newsize));
    int shift = stack_bottom - prev_stack_bottom;
    set_gc_ptr(__gc_stack_top, prev_stack_top + shift);
    L->base = prev_base + shift;
    L->stacksize = newsize;
    L->stack_last = stack_bottom - L->stacksize;

    memcpy(prev_stack_last + shift + 1,
           prev_stack_last + 1,
           prev_stacksize * sizeof(void*));

    StkId st_ptr;
    foreach_stack(st_ptr) {
        if (!UNBOXED(*st_ptr) && \
            prev_stack_last <= cast(StkId, *st_ptr) && \
            cast(StkId, *st_ptr) <= prev_stack_bottom)
        {
            *st_ptr = cast(StkId, *st_ptr) + shift;
        }
    }
    lama_CallInfo *ci_ptr;
    foreach_ci(L, ci_ptr)
        ci_ptr->base = ci_ptr->base + shift;
    free(prev_stack_last + 1);
}

static void lama_growstack(lama_State *L, int n) {
    if(n > L->stacksize)
        lama_reallocstack(L, L->stacksize + n);
    else
        lama_reallocstack(L, 2 * L->stacksize);
}

#define lama_checkstack(L,n)if(stack_top-(L->stack_last)<=n)lama_growstack(L,n);
#define incr_top(L){lama_checkstack(L,1);set_gc_ptr(__gc_stack_top, stack_top - 1);}

#define lama_numadd(a,b)((a)+(b))
#define lama_numsub(a,b)((a)-(b))
#define lama_nummul(a,b)((a)*(b))
#define lama_numdiv(a,b)((a)/(b))
#define lama_nummod(a,b)((a)-floor((a)/(b))*(b))
#define lama_numlt(a,b)((a)<(b))
#define lama_numle(a,b)((a)<=(b))
#define lama_numgt(a,b)((a)>(b))
#define lama_numge(a,b)((a)>=(b))
#define lama_numeq(a,b)((a)==(b))
#define lama_numneq(a,b)((a)!=(b))
#define lama_numand(a,b)(((a != 0) && (b != 0)) ? 1 : 0)
#define lama_numor(a,b)(((a != 0) || (b != 0)) ? 1 : 0)

#define FAIL check(false)

typedef enum{
    OP_ADD = 1,
    OP_SUB,
    OP_MUL,
    OP_DIV,
    OP_MOD,
    OP_LT,
    OP_LE,
    OP_GT,
    OP_GE,
    OP_EQ,
    OP_NEQ,
    OP_AND,
    OP_OR,
    OP_N
} OPS;

typedef enum{
    LOC_G = 0,
    LOC_L,
    LOC_A,
    LOC_C,
    LOC_N
} n_locs;

static void lama_settop(lama_State *L, int idx) {
    if(idx < 0)
        check(-idx <= (L->base - stack_top));
    else
        check(idx <= (stack_top - L->stack_last));
    set_gc_ptr(__gc_stack_top, stack_top - idx);
}

#define lama_pop(L,n)lama_settop(L,-(n))


static StkId idx2StkId(lama_State *L, int idx) {
    check(idx <= L->base - stack_top);
    return stack_top + idx;
}

#define lama_isdummy(L,n)(*idx2StkId(L,n)==idx2StkId)

static void **loc2adr(lama_State *L, lama_Loc loc) {
    int idx = loc.idx;
    check(idx >= 0);
    int n_caps = L->ci->n_caps;
    int n_args = L->ci->n_args;
    int n_locs = L->ci->n_locs;
    switch (loc.tt) {
        case LOC_G:
            check(idx < L->n_globals);
            return stack_bottom - idx;
        case LOC_L:
            check(idx < n_locs);
            return L->base + n_locs - idx;
        case LOC_C:
            check(idx < n_caps);
            return L->base + (n_caps + n_locs) - idx;
        case LOC_A:
            check(idx < n_args);
            return L->base + (n_caps + n_args + n_locs + 1) - idx;
        default: FAIL;
    }
}

static int lama_tonumber(lama_State *L, int idx) {
    void *o = *idx2StkId(L, idx);
    if(!UNBOXED(o)) FAIL;
    return UNBOX(o);
}

#define lama_push(L,o){*stack_top = o;incr_top(L);}
#define lama_pushnumber(L,o){*stack_top = cast(void*, BOX(o));incr_top(L);}
#define lama_pushdummy(L){*stack_top = cast(void*, __gc_stack_top);incr_top(L);}

static void lama_reallocCI(lama_State *L, int newsize) {
    lama_CallInfo *prev_base_ci = L->base_ci;
    lama_CallInfo *prev_end_ci = L->end_ci;
    lama_CallInfo *prev_ci = L->ci;
    int prev_size_ci = L->size_ci;

    L->base_ci = alloc_stack(lama_CallInfo, newsize);
    int shift = L->base_ci - prev_base_ci;

    L->size_ci = newsize;
    L->ci = prev_ci + shift;
    L->end_ci = L->base_ci - L->size_ci;

    memcpy(prev_end_ci + shift + 1,
           prev_end_ci + 1,
           prev_size_ci * sizeof(lama_CallInfo));
}

static void lama_growCI(lama_State *L, int n) {
    if(n > L->size_ci)
        lama_reallocCI(L, L->size_ci + n);
    else
        lama_reallocCI(L, 2 * L->size_ci);
}

#define lama_checkCI(L,n)if((L->ci)-(L->end_ci)<=n)lama_growCI(L,n);
#define inc_ci(L){lama_checkCI(L,1);--L->ci;}

#ifdef DEBUG
#define print_debug(...) printf(__VA_ARGS__)
#else
#define print_debug(...) (void)0
#endif

void printstack(lama_State *L) {
    printf("stack\n");
    for (int i = 0; i < L->base - stack_top; i++) {
        int idx = L->base - stack_top - i;
        void *d = *idx2StkId(L, idx);
        if(ttisnumber(d))
            printf("(int)");
        else if(ttissexp(d))
            printf("(sexp)");
        else if(ttisarray(d))
            printf("(arr)");
        else if(ttisstring(d))
            printf("(str)");
        else if(ttisfunction(d))
            printf("(fun)");
        printf("%s ", cast(char*, Bstringval(d)));
    }
    printf("\n");
}

void printglobals(lama_State *L) {
    printf("globals\n");
    for (int i = 0; i < L->n_globals; i++) {
        lama_Loc loc = {i, LOC_G};
        void *d = *loc2adr(L, loc);
        if(ttisnumber(d))
            printf("(int)");
        else if(ttissexp(d))
            printf("(sexp)");
        else if(ttisarray(d))
            printf("(arr)");
        else if(ttisstring(d))
            printf("(str)");
        else if(ttisfunction(d))
            printf("(fun)");
        printf("%s ", cast(char*, Bstringval(d)));
    }
    printf("\n");
}

void printlocals(lama_State *L) {
    printf("locals\n");
    for (int i = 0; i < L->ci->n_locs; i++) {
        lama_Loc loc = {i, LOC_L};
        void *d = *loc2adr(L, loc);
        if(ttisnumber(d))
            printf("(int)");
        else if(ttissexp(d))
            printf("(sexp)");
        else if(ttisarray(d))
            printf("(arr)");
        else if(ttisstring(d))
            printf("(str)");
        else if(ttisfunction(d))
            printf("(fun)");
        printf("%s ", cast(char*, Bstringval(d)));
    }
    printf("\n");
}

void printargs(lama_State *L) {
    printf("args\n");
    for (int i = 0; i < L->ci->n_args; i++) {
        lama_Loc loc = {i, LOC_A};
        void *d = *loc2adr(L, loc);
        if(ttisnumber(d))
            printf("(int)");
        else if(ttissexp(d))
            printf("(sexp)");
        else if(ttisarray(d))
            printf("(arr)");
        else if(ttisstring(d))
            printf("(str)");
        else if(ttisfunction(d))
            printf("(fun)");
        printf("%s ", cast(char*, Bstringval(d)));
    }
    printf("\n");
}

#ifndef DEBUG
#define printstack(l) (void)0
#define printglobals(l) (void)0
#define printlocals(l) (void)0
#define printargs(l) (void)0
#endif

static void lama_begin(lama_State *L, int n_caps, int n_args, int n_locs, char *retip, void *fun) {
    inc_ci(L)
    lama_CallInfo *ci = L->ci;
    ci->ret_ip = retip;
    ci->n_caps = n_caps;
    ci->n_args = n_args;
    ci->n_locs = n_locs;

    if(fun == NULL)
        lama_pushdummy(L)
    else
        lama_push(L, fun);

    lama_checkstack(L, n_caps + n_locs)
    lama_settop(L, n_caps + n_locs);
    L->base = ci->base = stack_top;

    for(int i = 0; i < n_caps; i++) {
        lama_Loc loc = {i, LOC_C};
        *loc2adr(L, loc) = cast(void**, fun)[i + 1];
    }
    for(int i = 0; i < n_locs; i++) {
        lama_Loc loc = {i, LOC_L};
        *loc2adr(L, loc) = cast(void*, 1);
    }
}

static void lama_end(lama_State *L) {
    void *ret = *idx2StkId(L, 1);
    int n_caps = L->ci->n_caps;
    int n_args = L->ci->n_args;
    int n_locs = L->ci->n_locs;
    check((L->base - stack_top) == 1);

    void *fun = *(L->base + (n_caps + n_locs + 1));
    for(int i = 0; i < n_caps; i++) {
        lama_Loc loc = {i, LOC_C};
        cast(void**, fun)[i + 1] = *loc2adr(L, loc);
    }

    set_gc_ptr(__gc_stack_top, stack_top + (n_caps + n_args + n_locs + 2));

    L->ip = L->ci->ret_ip;
    ++L->ci;
    L->base = L->ci->base;
    lama_push(L, ret);
}

void eval (bytefile *bf, char *fname) {
   lama_State *L = &eval_state;

#define INT (L->ip += sizeof (int), *(int*)(L->ip - sizeof (int)))
#define BYTE *L->ip++
#define STRING get_string (bf, INT)
#define OPFAIL failure ("ERROR: invalid opcode %d-%d\n", h, l)

    L->ip = bf->code_ptr;
    L->n_globals = bf->global_area_size;

    __gc_stack_top = set_gc_ptr(__gc_stack_bottom, alloc_stack(void*, INIT_STACK_SIZE));
    L->base = stack_bottom;
    L->stacksize = INIT_STACK_SIZE;
    L->stack_last = stack_top - L->stacksize;

    L->base_ci = L->ci = alloc_stack(lama_CallInfo, INIT_STACK_SIZE);
    L->size_ci = INIT_STACK_SIZE;
    L->end_ci = L->base_ci - L->size_ci;

    lama_settop(L, L->n_globals);

    L->base = stack_top;

    lama_pushnumber(L, 0);
    lama_pushnumber(L, 0);

    L->ci->n_locs = L->ci->n_args = 0;
    L->ci->base = L->base;
    lama_pushnumber(L, 0);
    lama_pushdummy(L);

    char *ret_ip = code_stop_ptr;

    for(int i = 0; i < L->n_globals; i++) {
        lama_Loc loc = {i, LOC_G};
        *loc2adr(L, loc) = cast(void*, 1);
    }

    do {
#ifdef DEBUG
        printstack(L);
        printglobals(L);
        printlocals(L);
        printargs(L);
        printf("=============\n");
#endif
        char x = BYTE, h = (x & 0xF0) >> 4, l = x & 0x0F;
        switch (h) {
            case 15:
                goto stop;
            case 0: { //BINOP
                print_debug("BINOP\n");

                int nc = cast(int, *idx2StkId(L, 1));
                if(UNBOXED(nc)) nc = UNBOX(nc);
                int nb = cast(int, *idx2StkId(L, 2));
                if(UNBOXED(nb)) nb = UNBOX(nb);
                lama_pop(L, 2);
                switch (l) {
                    case OP_ADD:    lama_pushnumber(L, lama_numadd(nb,nc)); break;
                    case OP_SUB:    lama_pushnumber(L, lama_numsub(nb,nc)); break;
                    case OP_MUL:    lama_pushnumber(L, lama_nummul(nb,nc)); break;
                    case OP_DIV:    lama_pushnumber(L, lama_numdiv(nb,nc)); break;
                    case OP_MOD:    lama_pushnumber(L, lama_nummod(nb,nc)); break;
                    case OP_LT:     lama_pushnumber(L, lama_numlt(nb,nc));  break;
                    case OP_LE:     lama_pushnumber(L, lama_numle(nb,nc));  break;
                    case OP_GT:     lama_pushnumber(L, lama_numgt(nb,nc));  break;
                    case OP_GE:     lama_pushnumber(L, lama_numge(nb,nc));  break;
                    case OP_EQ:     lama_pushnumber(L, lama_numeq(nb,nc));  break;
                    case OP_NEQ:    lama_pushnumber(L, lama_numneq(nb,nc)); break;
                    case OP_AND:    lama_pushnumber(L, lama_numand(nb,nc)); break;
                    case OP_OR:     lama_pushnumber(L, lama_numor(nb,nc));  break;
                    default: OPFAIL;
                }
                break;
            }
            case 1:
                switch (l) {
                    case 0: //CONST
                        print_debug("CONST\n");

                        lama_pushnumber(L, INT);
                        break;
                    case 1: //STRING
                        print_debug("STRING\n");

                        lama_push(L, Bstring(STRING));
                        break;
                    case 2: { //SEXP
                        print_debug("SEXP\n");

                        int tag = LtagHash(STRING);
                        int n = INT;
                        void* b = LmakeSexp(BOX(n + 1), tag);
                        for (int i = 0; i < n; i++)
                            cast(void**, b)[i] = *idx2StkId(L, n - i);
                        lama_pop(L, n);
                        lama_push(L, b);
                        break;
                    }
                    case 3: //STI
                        OPFAIL;
                    case 4: { //STA
                        print_debug("STA\n");

                        StkId v = *idx2StkId(L, 1);
                        int i = cast(int, *idx2StkId(L, 2));
                        StkId x = *idx2StkId(L, 3);
                        lama_pop(L, 3);
                        lama_push(L, Bsta(v, i, x));
                        break;
                    }
                    case 5: { //JMP
                        print_debug("JMP\n");

                        int addr = INT;
                        L->ip = bf->code_ptr + addr;
                        break;
                    }
                    case 6: //END
                        print_debug("END\n");

                        lama_end(L);
                        break;
                    case 7: //RET
                        OPFAIL;
                    case 8: //DROP
                        print_debug("DROP\n");

                        lama_pop(L, 1);
                        break;
                    case 9: //DUP
                        print_debug("DUP\n");

                        lama_push(L, *idx2StkId(L, 1));
                        break;
                    case 10: { //SWAP
                        print_debug("SWAP\n");

                        swap(*idx2StkId(L, 1), *idx2StkId(L, 2));
                        break;
                    }
                    case 11: { //ELEM
                        print_debug("ELEM\n");

                        int i = cast(int, *idx2StkId(L, 1));
                        void* p = *idx2StkId(L, 2);
                        lama_pop(L, 2);
                        lama_push(L, Belem(p, i));
                        break;
                    }
                    default:
                        OPFAIL;
                }
                break;
            case 2: { //LD
                print_debug("LD");

                lama_Loc loc = {INT, l};
                lama_push(L, *loc2adr(L, loc));
                break;
            }
            case 3: { //LDA
                print_debug("LDA\n");

                lama_Loc loc = {INT, l};
                lama_push(L, loc2adr(L, loc));
                lama_pushdummy(L);
                break;
            }
            case 4: { //ST
                print_debug("ST\n");

                lama_Loc loc = {INT, l};
                *loc2adr(L, loc) = *idx2StkId(L, 1);
                break;
            }
            case 5:
                switch (l) {
                    case 0: { //CJMPz
                        print_debug("CJMPz\n");

                        int n = lama_tonumber(L, 1);
                        lama_pop(L, 1);
                        int addr = INT;
                        if(n == 0) L->ip = bf->code_ptr + addr;
                        break;
                    }
                    case 1: { //CJMPnz
                        print_debug("CJMPnz\n");

                        int n = lama_tonumber(L, 1);
                        lama_pop(L, 1);
                        int addr = INT;
                        if(n != 0) L->ip = bf->code_ptr + addr;
                        break;
                    }
                    case 2: { //BEGIN
                        print_debug("BEGIN\n");

                        int n_caps = lama_tonumber(L, 2);
                        check(n_caps == 0);
                        void *fun = *idx2StkId(L, 1);
                        if(lama_isdummy(L, 1)) fun = NULL;

                        lama_pop(L, 2);
                        int n_args = INT, n_locs = INT;
                        lama_begin(L, 0, n_args, n_locs, ret_ip, fun);
                        break;
                    }
                    case 3: { //CBEGIN
                        print_debug("CBEGIN\n");

                        int n_caps = lama_tonumber(L, 2);
                        void *fun = *idx2StkId(L, 1);
                        if(lama_isdummy(L, 1)) fun = NULL;

                        lama_pop(L, 2);
                        int n_args = INT, n_locs = INT;
                        lama_begin(L, n_caps, n_args, n_locs, ret_ip, fun);
                        break;
                    }
                    case 4: { //CLOSURE
                        print_debug("CLOSURE\n");

                        int func_offset = INT;
                        int n_caps = INT;
                        void *fun = LMakeClosure(BOX(n_caps), bf->code_ptr + func_offset);
                        for (int i = 0; i < n_caps; i++) {
                            char tt = BYTE; int idx = INT;
                            lama_Loc loc = {idx, tt};
                            cast(void**, fun)[i + 1] = *loc2adr(L, loc);
                        }
                        lama_push(L, fun);
                        break;
                    }
                    case 5: { //CALLC
                        print_debug("CALLC\n");

                        int n_args = INT;
                        void *fun = *idx2StkId(L, n_args + 1);
                        check(ttisfunction(fun));
                        for(int i = n_args; i > 0; i--)
                            *idx2StkId(L, i + 1) = *idx2StkId(L, i);
                        lama_pop(L, 1);
                        int n_caps = LEN(TO_DATA(fun)->tag) - 1;
                        lama_pushnumber(L, n_caps); //n_caps
                        lama_push(L, fun);
                        ret_ip = L->ip;
                        char *func_ptr = cast(char**, fun)[0];
                        check(((*func_ptr & 0xF0) >> 4) == 5);
                        check((*func_ptr & 0x0F) == 2 || (*func_ptr & 0x0F) == 3);
                        L->ip = func_ptr;
                        break;
                    }
                    case 6: { //CALL
                        print_debug("CALL\n");

                        int func_offset = INT, n_args = INT;
                        char *func_ptr = bf->code_ptr + func_offset;
                        check(((*func_ptr & 0xF0) >> 4) == 5);
                        check((*func_ptr & 0x0F) == 2 || (*func_ptr & 0x0F) == 3);
                        lama_pushnumber(L, 0); //n_caps
                        lama_pushdummy(L);
                        ret_ip = L->ip;
                        L->ip = func_ptr;
                        break;
                    }
                    case 7: { //TAG
                        print_debug("TAG\n");

                        int t = LtagHash(STRING);
                        int n = INT;
                        *idx2StkId(L, 1) = cast(void*, Btag(*idx2StkId(L, 1), t, BOX(n)));
                        break;
                    }
                    case 8: { //ARRAY
                        print_debug("ARRAY\n");

                        int n = INT;
                        *idx2StkId(L, 1) = cast(void*, Barray_patt(*idx2StkId(L, 1), BOX(n)));
                        break;
                    }
                    case 9: { //FAIL
                        print_debug("FAIL\n");

                        int line = INT;
                        int col = INT;
                        void *v = *idx2StkId(L, 1);
                        Bmatch_failure(v, fname, line, col);
                        exit(0);
                    }
                    case 10: { //LINE
                        int line = INT;
                        print_debug("LINE %d\n", line);
                        break;
                    }
                    default:
                        OPFAIL;
                }
                break;
            case 6: { //PATT
                print_debug("PATT\n");

                switch (l) {
                    case 0: //=str
                        *idx2StkId(L, 2) = cast(void*, Bstring_patt(*idx2StkId(L, 2), *idx2StkId(L, 1)));
                        lama_pop(L, 1);
                        break;
                    case 1: //#string
                        *idx2StkId(L, 1) = cast(void*, Bstring_tag_patt(*idx2StkId(L, 1)));
                        break;
                    case 2: //#array
                        *idx2StkId(L, 1) = cast(void*, Barray_tag_patt(*idx2StkId(L, 1)));
                        break;
                    case 3: //#sexp
                        *idx2StkId(L, 1) = cast(void*, Bsexp_tag_patt(*idx2StkId(L, 1)));
                        break;
                    case 4: //#ref
                        *idx2StkId(L, 1) = cast(void*, Bboxed_patt(*idx2StkId(L, 1)));
                        break;
                    case 5: //#val
                        *idx2StkId(L, 1) = cast(void*, Bunboxed_patt(*idx2StkId(L, 1)));
                        break;
                    case 6: //#fun
                        *idx2StkId(L, 1) = cast(void*, Bclosure_tag_patt(*idx2StkId(L, 1)));
                        break;
                    default:
                        OPFAIL;
                }
                break;
            }
            case 7: {
                switch (l) {
                    case 0: // CALL Lread
                        print_debug("Lread\n");

                        lama_push(L, cast(void*, Lread()));
                        break;
                    case 1: //CALL Lwrite
                        print_debug("Lwrite\n");

                        Lwrite(cast(int, *idx2StkId(L, 1)));
                        break;
                    case 2: //CALL Llength
                        print_debug("Llength\n");

                        *idx2StkId(L, 1) = cast(void*, Blength(*idx2StkId(L, 1)));
                        break;
                    case 3: //CALL Lstring
                        print_debug("Lstring\n");

                        *idx2StkId(L, 1) = Bstringval(*idx2StkId(L, 1));
                        break;
                    case 4: { //CALL Barray
                        print_debug("Barray\n");

                        int n = INT;
                        void *p = LmakeArray(BOX(n));
                        for (int i = 0; i < n; i++)
                            cast(void**, p)[i] = *idx2StkId(L, n - i);
                        lama_pop(L, n);
                        lama_push(L, p);
                        break;
                    }
                    default:
                        OPFAIL;
                }
                break;
            }
            default:
                OPFAIL;
        }
    }
    while (true);
    stop:
    free(L->stack_last + 1);
    free(L->end_ci + 1);
}

int main (int argc, char* argv[]) {
    bytefile *f = read_file (argv[1]);
    eval (f, argv[1]);
    free(f->global_ptr);
    free(f);
    return 0;
}