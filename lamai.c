/* Lama SM Bytecode interpreter */

# include <string.h>
# include <stdio.h>
# include <errno.h>
# include <malloc.h>
# include <stdint.h>
# include <stdlib.h>
# include <math.h>
# include <assert.h>
# include <stdbool.h>

# include "runtime/runtime.h"

#define swap(x,y) do {    \
   typeof(x) _x = x;      \
   typeof(y) _y = y;      \
   x = _y;                \
   y = _x;                \
 } while(0)

void *__start_custom_data;
void *__stop_custom_data;

char *code_stop_ptr;

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

/* Gets an offset for a publie symbol */
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

typedef struct Lama_Loc {
    int idx;
    int tt;
} lama_Loc;

typedef void** StkId;

typedef struct callInfo {
    int n_args, n_locs, n_caps;
    StkId base;
    char *ret_ip;
} CallInfo;

typedef struct Lama_State {
    char *ip;
    void **global_mem;
    StkId stack;
    StkId base;
    StkId top;
    StkId stack_last;
    CallInfo *base_ci;
    CallInfo *ci;
    CallInfo *end_ci;
    int size_ci;
    int stacksize;
} lama_State;

#define check_exp(c,e)(e)

typedef enum{
    TP_NUM = 3,
    TP_STR,
    TP_ARR,
    TP_SEXP,
    TP_FUN,
    TP_N
} TYPES;

#define ttisnumber(o)(UNBOXED(o))
#define ttisstring(o)(!UNBOXED(o)&&TAG(TO_DATA(o)->tag)==STRING_TAG)
#define ttisarray(o)(!UNBOXED(o)&&TAG(TO_DATA(o)->tag)==ARRAY_TAG)
#define ttissexp(o)(!UNBOXED(o)&&TAG(TO_DATA(o)->tag)==SEXP_TAG)
#define ttisfunction(o)(!UNBOXED(o)&&TAG(TO_DATA(o)->tag)==CLOSURE_TAG)

#define cast(t,exp)((t)(exp))

static void lama_reallocstack(lama_State *L, int newsize) {
    void **oldstack = L->stack;
    L->stack = cast(void**, malloc(sizeof(void*) * newsize));
    memcpy(L->stack, oldstack, L->stacksize * sizeof(void*));
    L->stacksize = newsize;
    L->base = (L->base - oldstack) + L->stack;
    L->top = (L->top - oldstack) + L->stack;
    L->stack_last = L->stack + L->stacksize - 1;
}

static void lama_growstack(lama_State *L, int n) {
    lama_reallocstack(L, L->stacksize + n);
}

#define lama_checkstack(L,n)if((char*)L->stack_last-(char*)L->top<=(n)*(int)sizeof(void*))lama_growstack(L,n);
#define incr_top(L){lama_checkstack(L,1);L->top++;}

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

#define check(p)assert(p)
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
    if(idx > 0)
        check(idx <= (L->stack_last - L->base));
    else
        check(-idx <= (L->top - L->base));
    L->top += idx;
}

#define lama_pop(L,n)lama_settop(L,-(n))

static void **idx2StkId(lama_State *L, int idx) {
    check(idx <= L->top - L->base);
    return L->top - idx;
}

static void **loc2adr(lama_State *L, lama_Loc loc) {
    int idx = loc.idx;
    check(idx >= 0);
    int n_caps = L->ci->n_caps;
    int n_args = L->ci->n_args;
    int n_locs = L->ci->n_locs;
    switch (loc.tt) {
        case LOC_G:
            check(idx < 10000);
            return L->global_mem + idx;
        case LOC_L:
            check(idx < n_locs);
            return L->base - n_locs + idx;
        case LOC_A:
            check(idx < n_args);
            return L->base - (n_caps + n_args + n_locs) + idx;
        case LOC_C:
            check(idx < n_caps);
            return L->base - (n_caps + n_locs) + idx;
        default: FAIL;
    }
}

static int lama_tonumber(lama_State *L, int idx) {
    void *o = *idx2StkId(L, idx);
    if(!UNBOXED(o)) FAIL;
    return UNBOX(o);
}

#define lama_push(L,o){*L->top = o;incr_top(L);}
#define lama_pushnumber(L,o){*L->top = cast(void*, BOX(o));incr_top(L);}

static void lama_reallocCI(lama_State *L, int newsize) {
    CallInfo *oldci = L->base_ci;
    L->base_ci = cast(CallInfo*, malloc(sizeof(CallInfo) * newsize));
    memcpy(L->base_ci, oldci, L->size_ci * sizeof(CallInfo));
    L->size_ci = newsize;
    L->ci = (L->ci - oldci) + L->base_ci;
    L->end_ci = L->base_ci + L->size_ci - 1;
}

static void lama_growCI(lama_State *L, int n) {
    lama_reallocCI(L, L->size_ci + n);
}

#define lama_checkCI(L,n)if((char*)L->end_ci-(char*)L->ci<=(n)*(int)sizeof(CallInfo))lama_growCI(L,n);
#define inc_ci(L){lama_checkCI(L,1); ++L->ci;}

void printstack(lama_State *L) {
    printf("stack\n");
    for (int i = 0; i < L->top - L->base; i++) {
        int idx = L->top - L->base - i;
        printf("%d ", idx);
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
    for (int i = 0; i < 3; i++) {
        void *d = *(L->global_mem + i);
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

#define printstack(l) (void)0
#define printglobals(l) (void)0
#define printlocals(l) (void)0
#define printargs(l) (void)0

static void lama_begin(lama_State *L, int n_caps, int n_args, int n_locs, char *retip) {
    inc_ci(L)
    CallInfo *ci = L->ci;
    ci->ret_ip = retip;
    ci->n_caps = n_caps;
    ci->n_args = n_args;
    ci->n_locs = n_locs;

    lama_checkstack(L, n_locs)
    lama_settop(L, n_locs);

    for(int i = 0; i < n_locs; i++)
        *(L->top - i - 1) = cast(void*, BOX(0));

    StkId base = L->top;
    L->base = ci->base = base;
}

static void lama_end(lama_State *L) {
    void *ret = *idx2StkId(L, 1);
    int n_caps = L->ci->n_caps;
    int n_args = L->ci->n_args;
    int n_locs = L->ci->n_locs;
    check((L->top - L->base) == 1);
    L->top -= n_caps + n_args + n_locs + 1;
    L->ip = L->ci->ret_ip;
    --L->ci;
    L->base = L->ci->base;
    lama_push(L, ret);
}

void eval (FILE *f, bytefile *bf) {
    lama_State *L = cast(lama_State*, malloc(sizeof(lama_State)));

#define INT (L->ip += sizeof (int), *(int*)(L->ip - sizeof (int)))
#define BYTE *L->ip++
#define STRING get_string (bf, INT)
#define OPFAIL failure ("ERROR: invalid opcode %d-%d\n", h, l)

    L->ip = bf->code_ptr;
    L->global_mem = cast(void**, malloc(sizeof(void*) * 10000));
    L->stack = L->base = L->top = cast(void**, malloc(sizeof(void*) * 10000));

    L->base_ci = L->ci = cast(CallInfo*, malloc(sizeof(CallInfo) * 10000));
    L->stacksize = 10000;
    L->end_ci = L->ci + 10000;
    L->stack_last = L->stack + 10000;
    lama_settop(L, 2);
    for(int i = 1; i <= 2; i++)
        *cast(int*, idx2StkId(L, i)) |= 0x0001;
    L->ci->n_locs = L->ci->n_args = 0;
    L->ci->base = L->base;

    for(int i = 0; i < 10; i++) {
        cast(int*, L->global_mem)[i] |= 0x0001;
    }

    lama_pushnumber(L, 0);
    char *ret_ip = code_stop_ptr;
    //lama_push(L, cast(void*, code_stop_ptr));

    do {
        printstack(L);
        printglobals(L);
        printlocals(L);
        printargs(L);
        char x = BYTE, h = (x & 0xF0) >> 4, l = x & 0x0F;
        switch (h) {
            case 15:
                goto stop;
            case 0: { //BINOP
                //fprintf(f, "BINOP\n");
                fflush(f);

                int nc = lama_tonumber(L, 1);
                int nb = lama_tonumber(L, 2);
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
                        //fprintf (f, "CONST\n");
                        fflush(f);

                        lama_pushnumber(L, INT);
                        break;
                    case 1: //STRING
                        //fprintf (f, "STRING\n");
                        fflush(f);

                        lama_push(L, Bstring(STRING));
                        break;
                    case 2: { //SEXP
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
                        //fprintf (f, "STA\n");
                        fflush(f);

                        void *v = *idx2StkId(L, 1);
                        int i = cast(int, *idx2StkId(L, 2));
                        void *x = *idx2StkId(L, 3);
                        lama_pop(L, 3);
                        lama_push(L, Bsta(v, i, x));
                        break;
                    }
                    case 5: { //JMP
                        //fprintf (f, "JMP\n");
                        fflush(f);

                        int addr = INT;
                        L->ip = bf->code_ptr + addr;
                        break;
                    }
                    case 6: //END
                        //fprintf (f, "END\n");
                        fflush(f);

                        lama_end(L);
                        break;
                    case 7: //RET
                        OPFAIL;
                    case 8: //DROP
                        //fprintf (f, "DROP\n");
                        fflush(f);

                        lama_pop(L, 1);
                        break;
                    case 9: //DUP
                        //fprintf (f, "DUP\n");
                        fflush(f);

                        lama_push(L, *idx2StkId(L, 1));
                        break;
                    case 10: { //SWAP
                        //fprintf (f, "SWAP\n");
                        fflush(f);

                        swap(*idx2StkId(L, 1), *idx2StkId(L, 2));
                        break;
                    }
                    case 11: { //ELEM
                        //fprintf (f, "ELEM\n");
                        fflush(f);

                        int i = cast(int, *idx2StkId(L, 1));
                        void *p = *idx2StkId(L, 2);
                        lama_pop(L, 2);
                        lama_push(L, Belem(p, i));
                        break;
                    }
                    default:
                        OPFAIL;
                }
                break;
            case 2: { //LD
                //fprintf (f, "LD\n");
                fflush(f);

                lama_Loc loc = {INT, l};
                lama_push(L, *loc2adr(L, loc));
                break;
            }
            case 3: { //LDA
                //fprintf (f, "LDA\n");
                fflush(f);

                lama_Loc loc = {INT, l};
                //check(ttisarray(*loc2adr(L, loc)) || ttissexp(*loc2adr(L, loc)));
                lama_push(L, *loc2adr(L, loc));
                break;
            }
            case 4: { //ST
                //fprintf (f, "ST\n");
                fflush(f);
                lama_Loc loc = {INT, l};
                *loc2adr(L, loc) = *idx2StkId(L, 1);
                break;
            }
            case 5:
                switch (l) {
                    case 0: { //CJMPz
                        //fprintf (f, "CJMPz\n");
                        fflush(f);

                        int n = lama_tonumber(L, 1);
                        lama_pop(L, 1);
                        int addr = INT;
                        if(n == 0) L->ip = bf->code_ptr + addr;
                        break;
                    }
                    case 1: { //CJMPnz
                        //fprintf (f, "CJMPnz\n");
                        fflush(f);

                        int n = lama_tonumber(L, 1);
                        lama_pop(L, 1);
                        int addr = INT;
                        if(n != 0) L->ip = bf->code_ptr + addr;
                        break;
                    }
                    case 2: { //BEGIN
                        //fprintf (f, "BEGIN\n");
                        fflush(f);

                        //char *ret_ip = cast(char*, *idx2StkId(L, 1));
                        //int n_caps = lama_tonumber(L, 2);
                        int n_caps = lama_tonumber(L, 1);
                        check(n_caps == 0);
                        //lama_pop(L, 2);
                        lama_pop(L, 1);
                        int n_args = INT, n_locs = INT;
                        lama_begin(L, 0, n_args, n_locs, ret_ip);
                        break;
                    }
                    case 3: { //CBEGIN
                        //fprintf (f, "CBEGIN\n");
                        fflush(f);

                        //char *ret_ip = cast(char*, *idx2StkId(L, 1));
                        //int n_caps = lama_tonumber(L, 2);
                        int n_caps = lama_tonumber(L, 1);
                        //lama_pop(L, 2);
                        lama_pop(L, 1);
                        int n_args = INT, n_locs = INT;
                        lama_begin(L, n_caps, n_args, n_locs, ret_ip);
                        break;
                    }
                    case 4: { //CLOSURE
                        //fprintf (f, "CLOSURE\n");
                        fflush(f);

                        int func_offset = INT;
                        int n_caps = INT;
                        char *func_ptr = bf->code_ptr + func_offset;
                        void *fun = LMakeClosure(BOX(n_caps), func_ptr);
                        for (int i = 0; i < n_caps; i++) {
                            char tt = BYTE; int idx = INT;
                            lama_Loc loc = {idx, tt};
                            cast(void**, fun)[i + 1] = *loc2adr(L, loc);
                        }
                        lama_push(L, fun);
                        break;
                    }
                    case 5: { //CALLC
                        //fprintf (f, "CALLC\n");
                        fflush(f);

                        int n_args = INT;
                        void *fun = *idx2StkId(L, n_args + 1);
                        check(ttisfunction(fun));
                        for(int i = n_args; i > 0; i--)
                            *idx2StkId(L, i + 1) = *idx2StkId(L, i);
                        lama_pop(L, 1);
                        int n_caps = LEN(TO_DATA(fun)->tag) - 1;
                        for(int i = 0; i < n_caps; i++)
                            lama_push(L, cast(void**, fun)[i + 1]);
                        lama_pushnumber(L, n_caps); //n_caps
                        //lama_push(L, cast(void*, L->ip)); //ret_ip
                        ret_ip = L->ip;
                        char *func_ptr = cast(char**, fun)[0];
                        check(((*func_ptr & 0xF0) >> 4) == 5);
                        check((*func_ptr & 0x0F) == 2 || (*func_ptr & 0x0F) == 3);
                        L->ip = func_ptr;
                        break;
                    }
                    case 6: { //CALL
                        //fprintf (f, "CALL\n");
                        fflush(f);

                        int func_offset = INT, n_args = INT;
                        char *func_ptr = bf->code_ptr + func_offset;
                        check(((*func_ptr & 0xF0) >> 4) == 5);
                        check((*func_ptr & 0x0F) == 2 || (*func_ptr & 0x0F) == 3);
                        lama_pushnumber(L, 0); //n_caps
                        //lama_push(L, cast(void*, L->ip)); //ret_ip
                        ret_ip = L->ip;
                        L->ip = func_ptr;
                        break;
                    }
                    case 7: { //TAG
                        int t = LtagHash(STRING);
                        int n = INT;
                        *idx2StkId(L, 1) = cast(void*, Btag(*idx2StkId(L, 1), t, BOX(n)));
                        break;
                    }
                    case 8: { //ARRAY
                        //fprintf (f, "ARRAY\n");
                        fflush(f);

                        int n = INT;
                        *idx2StkId(L, 1) = cast(void*, Barray_patt(*idx2StkId(L, 1), BOX(n)));
                        break;
                    }
                    case 9: { //FAIL
                        //fprintf (f, "FAIL\t%d", INT);
                        //fprintf (f, "%d", INT);

                        int line = INT;
                        int col = INT;
                        void *v = *idx2StkId(L, 1);
                        char *fname = "test.lama";
                        Bmatch_failure(v, fname, line, col);
                        exit(0);
                    }
                    case 10: //LINE
                        //fprintf (f, "LINE\n");
                        fflush(f);

                        INT;
                        break;
                    default:
                        OPFAIL;
                }
                break;
            case 6: { //PATT
                //fprintf(f, "PATT\n");
                fflush(f);

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
                        lama_push(L, cast(void*, Lread()));
                        break;
                    case 1: //CALL Lwrite
                        Lwrite(cast(int, *idx2StkId(L, 1)));
                        break;
                    case 2: //CALL Llength
                        *idx2StkId(L, 1) = cast(void*, Blength(*idx2StkId(L, 1)));
                        break;
                    case 3: //CALL Lstring
                        *idx2StkId(L, 1) = Bstringval(*idx2StkId(L, 1));
                        break;
                    case 4: { //CALL Barray
                        int n = INT;
                        void *p = LmakeArray(BOX(n));
                        memcpy(p, idx2StkId(L, n), sizeof(int) * n);
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
        //fprintf (f, "\n");
    }
    while (true);
    stop:
    return;
}

int main (int argc, char* argv[]) {
    bytefile *f = read_file (argv[1]);
    eval (stdout, f);
    return 0;
}