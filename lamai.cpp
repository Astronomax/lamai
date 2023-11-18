/* Lama SM Bytecode interpreter */

# include <string.h>
# include <stdio.h>
# include <errno.h>
# include <malloc.h>
# include <cstdint>
# include <vector>
# include <cmath>
# include <cassert>

#include "runtime/runtime_common.h"
extern "C" {
# include "runtime/runtime.h"
}
/*
extern int Llength (void *p);
extern void *Bsexp_ (int n);
extern void *Bsexp (int n, ...);
extern void *Barray_ (int bn);
extern void *Barray (int bn, ...);
extern void *Bstring (void *);
extern void *Bclosure (int bn, void *entry, ...);
*/
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
struct TValue;
typedef int lama_Number;
typedef char* lama_String;
struct lama_Array {
    int n;
    TValue *arr;
};
struct lama_Sexp {
    int n;
    const char *name;
    TValue *arr;
};
struct lama_Loc {
    int idx;
    int tt;
};

typedef TValue* StkId;
//typedef TValue* lama_Ref;
struct lama_Ref {
    lama_Loc loc;
    TValue *ptr;
};

typedef union{
    lama_Number num;
    lama_String str;
    lama_Array arr;
    lama_Sexp sexp;
    lama_Ref ref;
} Value;

struct TValue{
    Value value;
    int tt;
};

struct CallInfo {
    int args, locs, caps;
    StkId base;
    char *retip;
};

struct lama_State {
    char *ip;
    TValue *global_mem;
    StkId stack;
    StkId base;
    StkId top;
    StkId stack_last;
    CallInfo *base_ci;
    CallInfo *ci;
    CallInfo *end_ci;
    int size_ci;
    int stacksize;
};

#define check_exp(c,e)(e)

#define ttype(o)((o)->tt)
#define ttisnumber(o)(ttype(o)==3)
#define ttisstring(o)(ttype(o)==4)
#define ttisarray(o)(ttype(o)==5)
#define ttissexp(o)(ttype(o)==6)
#define ttisfunction(o)(ttype(o)==7)
#define ttisref(o)(ttype(o)==8)

#define numvalue(o)check_exp(ttisnumber(o),&(o)->value.num)
#define strvalue(o)check_exp(ttisstring(o),&(o)->value.str)
#define clvalue(o)check_exp(ttisfunction(o),&(o)->value.cl)
#define arrvalue(o)check_exp(ttisarray(o),&(o)->value.arr)
#define sexpvalue(o)check_exp(ttissexp(o),&(o)->value.sexp)
#define refvalue(o)check_exp(ttisref(o),&(o)->value.ref)

#define cast(t,exp)((t)(exp))
#define cast_num(i)cast(lama_Number,(i))

#define lamaS_new(L,s)(lamaS_newlstr(L,s,strlen(s)))

#define setnumvalue(obj,x){TValue*i_o=(obj);i_o->value.num=(x);i_o->tt=3;}
#define setstrvalue(L,obj,x){TValue*i_o=(obj);i_o->value.str=(x);i_o->tt=4;}
#define setarrvalue(L,obj,x){TValue*i_o=(obj);i_o->value.arr=(x);i_o->tt=5;}
#define setsexpvalue(L,obj,x){TValue*i_o=(obj);i_o->value.sexp=(x);i_o->tt=6;}
#define setrefvalue(L,obj,x){TValue*i_o=(obj);i_o->value.ref=(x);i_o->tt=8;}

static void lama_reallocstack(lama_State *L, int newsize) {
    TValue *oldstack = L->stack;
    L->stack = new TValue [newsize];
    memcpy(L->stack, oldstack, L->stacksize * sizeof(TValue));
    L->stacksize = newsize;
    L->base = (L->base - oldstack) + L->stack;
    L->top = (L->top - oldstack) + L->stack;
    L->stack_last = L->stack + L->stacksize - 1;
}

static void lama_growstack(lama_State *L, int n) {
    lama_reallocstack(L, L->stacksize + n);
}

#define lama_checkstack(L,n)if((char*)L->stack_last-(char*)L->top<=(n)*(int)sizeof(TValue))lama_growstack(L,n);
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
#define not_implemented check(false)
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
} LOCS;

static void lama_settop(lama_State *L, int idx) {
    if(idx > 0)
        check(idx <= (L->stack_last - L->base));
    else
        check(-idx <= (L->top - L->base));
    L->top += idx;
}

#define lama_pop(L,n)lama_settop(L,-(n))

static TValue *idx2StkId(lama_State *L, int idx) {
    check(idx <= L->top - L->base);
    return L->top - idx;
}

static TValue *loc2adr(lama_State *L, lama_Loc loc) {
    int idx = loc.idx;
    check(idx >= 0);
    int caps = L->ci->caps;
    int args = L->ci->args;
    int locs = L->ci->locs;
    switch (loc.tt) {
        case LOC_G:
            check(idx < 10000);
            return L->global_mem + idx;
        case LOC_L:
            check(idx < locs);
            return L->base - locs + idx;
        case LOC_A:
            check(idx < args);
            return L->base - (args + locs) + idx;
        case LOC_C:
            check(idx < caps);
            return L->base - (caps + args + locs) + idx;
        default: FAIL;
    }
}

TValue *unref(TValue *o) {
    if (ttisref(o))
        return refvalue(o)->ptr;
    return o;
}

static lama_Number* lama_tonumber(lama_State *L, int idx) {
    TValue *o = unref(idx2StkId(L, idx));
    if(ttisnumber(o))
        return numvalue(o);
    else FAIL;
}

static lama_Array* lama_toarray(lama_State *L, int idx) {
    TValue *o = unref(idx2StkId(L, idx));
    if(ttisarray(o))
        return arrvalue(o);
    else FAIL;
}

static lama_Ref* lama_toref(lama_State *L, int idx) {
    TValue *o = idx2StkId(L, idx);
    if(ttisref(o))
        return refvalue(o);
    else FAIL;
}

static void lama_pushnumber(lama_State *L, lama_Number n) {
    setnumvalue(L->top, n);
    incr_top(L)
}

static void lama_pushstr(lama_State *L, lama_String str) {
    setstrvalue(L, L->top, str);
    incr_top(L)
}

static void lama_pusharr(lama_State *L, lama_Array arr) {
    setarrvalue(L, L->top, arr);
    incr_top(L)
}

static void lama_pushsexp(lama_State *L, lama_Sexp sexp) {
    setsexpvalue(L, L->top, sexp);
    incr_top(L)
}

static void lama_pushref(lama_State *L, lama_Ref ref) {
    setrefvalue(L, L->top, ref);
    incr_top(L)
}

static void lama_pushTValue(lama_State *L, TValue val) {
    *L->top = val;
    incr_top(L)
}

static void lama_reallocCI(lama_State *L, int newsize) {
    CallInfo *oldci = L->base_ci;
    L->base_ci = new CallInfo [newsize];
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

static TValue *allocArray(int n) {
    return new TValue [n];
}

void printstack(lama_State *L) {
    printf("stack\n");
    for (int i = 0; i < L->top - L->base; i++) {
        int idx = L->top - L->base - i;
        StkId id = idx2StkId(L, idx);
        if(ttisnumber(id)) {
            lama_Number n = *lama_tonumber(L, idx);
            printf("%d ", n);
        } else if(ttisref(id)) {
            switch(refvalue(id)->loc.tt) {
                case LOC_G: printf("G(%d) ", refvalue(id)->loc.idx); break;
                case LOC_L: printf("L(%d) ", refvalue(id)->loc.idx); break;
                case LOC_A: printf("A(%d) ", refvalue(id)->loc.idx); break;
                case LOC_C: printf("C(%d) ", refvalue(id)->loc.idx); break;
                default: FAIL;
            }
            if (ttisnumber(refvalue(id)->ptr))
                printf("(num) ");
            else if(ttisstring(refvalue(id)->ptr))
                printf("(str) ");
            else if(ttisref(refvalue(id)->ptr))
                printf("(ref) ");
            else if(ttissexp(refvalue(id)->ptr))
                printf("(sexp) ");
            else if(ttisarray(refvalue(id)->ptr)) {
                printf("(arr: [");
                lama_Array arr = *arrvalue(refvalue(id)->ptr);

                for(int j = 0; j < arr.n; j++) {
                    if(ttisnumber(arr.arr + j)) {
                        lama_Number n = *numvalue(arr.arr + j);
                        printf("%d ", n);
                    } else {
                        printf("- ");
                    }
                }
                printf("]) ");
            }
            else if(ttisfunction(refvalue(id)->ptr))
                printf("(fun) ");
            else printf("(undef) ");;
        } else {
            printf("- ");
        }
    }
    printf("\n");
}

void printglobals(lama_State *L) {
    printf("globals\n");
    for (int i = 0; i < 3; i++) {
        if(ttisnumber(L->global_mem + i)) {
            printf("%d ", *numvalue(L->global_mem + i));
        } else if(ttisref(L->global_mem + i)) {
            FAIL;
        } else if(ttisarray(L->global_mem + i)) {
            printf("[");
            lama_Array arr = *arrvalue(L->global_mem + i);

            for(int j = 0; j < arr.n; j++) {
                if(ttisnumber(arr.arr + j)) {
                    lama_Number n = *numvalue(arr.arr + j);
                    printf("%d ", n);
                } else {
                    printf("- ");
                }
            }
            printf("] ");
        } else {
            printf("- ");
        }
    }
    printf("\n");
}

void printlocals(lama_State *L) {
    printf("locals\n");
    for (int i = 0; i < L->ci->locs; i++) {
        lama_Loc loc = lama_Loc{i, LOC_L};
        TValue *ptr = loc2adr(L, loc);
        if(ttisnumber(ptr)) {
            printf("%d ", *numvalue(ptr));
        } else if(ttisref(ptr)) {
            FAIL;
        } else {
            printf("- ");
        }
    }
    printf("\n");
}

void printargs(lama_State *L) {
    printf("args\n");
    for (int i = 0; i < L->ci->args; i++) {
        lama_Loc loc = lama_Loc{i, LOC_A};
        TValue *ptr = loc2adr(L, loc);
        if(ttisnumber(ptr)) {
            printf("%d ", *numvalue(ptr));
        } else if(ttisref(ptr)) {
            FAIL;
        } else {
            printf("- ");
        }
    }
    printf("\n");
}

#define printstack(l) (void)0
#define printglobals(l) (void)0
#define printlocals(l) (void)0
#define printargs(l) (void)0

static void lama_begin(lama_State *L, int caps, int args, int locs, char *retip) {
    //printstack(L);

    inc_ci(L)
    CallInfo *ci = L->ci;
    ci->retip = retip;
    ci->caps = caps;
    ci->args = args;
    ci->locs = locs;

    for(int i = 0; i < args; i++)
        *idx2StkId(L, i + 1) = *unref(idx2StkId(L, i + 1));

    lama_checkstack(L, locs)
    lama_settop(L, locs);

    //printstack(L);

    StkId base = L->top;
    L->base = ci->base = base;
}

static void lama_end(lama_State *L) {
    TValue ret = *unref(idx2StkId(L, 1));
    int caps = L->ci->caps;
    int args = L->ci->args;
    int locs = L->ci->locs;
    check((L->top - L->base) == 1);
    L->top -= caps + args + locs + 1;
    L->ip = L->ci->retip;
    --L->ci;
    L->base = L->ci->base;
    //*idx2StkId(L, 0) = ret;
    //incr_top(L)
    lama_pushTValue(L, ret);
}

/* Disassembles the bytecode pool */
void disassemble (FILE *f, bytefile *bf) {


    //char *ip = bf->code_ptr;
    lama_State *L = new lama_State;

#define INT (L->ip += sizeof (int), *(int*)(L->ip - sizeof (int)))
#define BYTE *L->ip++
#define STRING get_string (bf, INT)
#define OPFAIL failure ("ERROR: invalid opcode %d-%d\n", h, l)

    L->ip = bf->code_ptr;
    L->global_mem = new TValue [10000];
    L->stack = L->base = L->top = new TValue [10000];

    L->base_ci = L->ci = new CallInfo [10000];
    L->stacksize = 10000;
    L->end_ci = L->ci + 10000;
    L->stack_last = L->stack + 10000;
    lama_settop(L, 2);
    L->ci->locs = L->ci->args = 0;
    L->ci->base = L->base;

    char *retip = code_stop_ptr;
    int caps, func_offset;

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

                lama_Number nb, nc;
                TValue *rc = unref(idx2StkId(L, 1));
                check(ttisnumber(rc));
                nc = *numvalue(rc);
                TValue *rb = unref(idx2StkId(L, 2));
                check(ttisnumber(rb));
                nb = *numvalue(rb);
                lama_pop(L, 2);
                //TValue *ra = idx2StkId(L, 0);
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
                //incr_top(L)
                //printstack(L);
                break;
            }
            case 1:
                switch (l) {
                    case 0: //CONST
                        //fprintf (f, "CONST\n");
                        fflush(f);

                        lama_pushnumber(L, INT);
                        //printstack(L);
                        break;
                    case 1: //STRING
                        //fprintf (f, "STRING\n");
                        fflush(f);

                        lama_pushstr(L, STRING);
                        break;
                    case 2: { //SEXP
                        char *name = STRING;
                        int n = INT;
                        TValue *arr = allocArray(n);
                        for (int i = 0; i < n; i++)
                            arr[i] = *idx2StkId(L, n - i);
                        lama_pushsexp(L, lama_Sexp{n, name, arr});
                        break;
                    }
                    case 3: //STI
                        not_implemented;
                    case 4: { //STA
                        //fprintf (f, "STA\n");
                        fflush(f);

                        TValue v = *unref(idx2StkId(L, 1));
                        lama_Number i = *lama_tonumber(L, 2);
                        TValue arr = *unref(idx2StkId(L, 3));
                        lama_pop(L, 3);
                        if (ttisarray(&arr))
                            arr.value.arr.arr[i] = v;
                        else if (ttissexp(&arr))
                            arr.value.sexp.arr[i] = v;
                        else if (ttisstring(&arr)) {
                            check(ttisnumber(&v));
                            arr.value.str[i] = (char)v.value.num;
                        } else
                            FAIL;
                        lama_pushTValue(L, v);
                        //*idx2StkId(L, 0) = v;
                        //incr_top(L);
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
                    case 7:
                        not_implemented;
                        fprintf (f, "RET");
                    case 8: //DROP
                        //fprintf (f, "DROP\n");
                        fflush(f);

                        lama_pop(L, 1);
                        break;
                    case 9: //DUP
                        //fprintf (f, "DUP\n");
                        fflush(f);

                        //*idx2StkId(L, 0) = *idx2StkId(L, 1);
                        //incr_top(L)
                        lama_pushTValue(L, *idx2StkId(L, 1));
                        break;
                    case 10: { //SWAP
                        //fprintf (f, "SWAP\n");
                        fflush(f);

                        //StkId a = idx2StkId(L, 1), b = idx2StkId(L, 2);
                        std::swap(*idx2StkId(L, 1), *idx2StkId(L, 2));
                        break;
                    }
                    case 11: { //ELEM
                        //fprintf (f, "ELEM\n");
                        fflush(f);

                        lama_Number i = *lama_tonumber(L, 1);
                        TValue* arr = unref(idx2StkId(L, 2));
                        lama_pop(L, 2);
                        if (ttisarray(arr))
                            lama_pushref(L, lama_Ref{{0, 0}, arr->value.arr.arr + i});
                            //lama_pushTValue(L, arr->value.arr.arr[i]);
                        else if (ttissexp(arr))
                            lama_pushref(L, lama_Ref{{0, 0}, arr->value.sexp.arr + i});
                            //lama_pushTValue(L, arr->value.sexp.arr[i]);
                        else
                            lama_pushnumber(L, (int)(arr->value.str[i]));
                        //incr_top(L);
                        break;
                    }
                    default:
                        OPFAIL;
                }
                break;
            case 2: { //LD
                //fprintf (f, "LD\n");
                fflush(f);

                lama_Loc loc = lama_Loc{INT, l};
                //check(!ttisarray(loc2adr(L, loc)) && !ttissexp(loc2adr(L, loc)));
                TValue *ptr = /*unref(*/loc2adr(L, loc)/*)*/;
                lama_pushref(L, lama_Ref{loc, ptr});
                break;
            }
            case 3: { //LDA
                //fprintf (f, "LDA\n");
                fflush(f);

                lama_Loc loc = lama_Loc{INT, l};
                check(ttisarray(loc2adr(L, loc)) || ttissexp(loc2adr(L, loc)));
                TValue *ptr = /*unref(*/loc2adr(L, loc)/*)*/;
                lama_pushref(L, lama_Ref{loc, ptr});
                break;
            }
            case 4: { //ST
                //fprintf (f, "ST\n");
                fflush(f);

                StkId id = unref(idx2StkId(L, 1));
                //if (ttisref(id)) id = id->value.ref;
                *loc2adr(L, lama_Loc{INT, l}) = *id;
                //lama_pop(L, 1);
                //printstack(L);
                //printglobals(L);
                break;
            }
            case 5:
                switch (l) {
                    case 0: { //CJMPz
                        //fprintf (f, "CJMPz\n");
                        fflush(f);
                        StkId id = unref(idx2StkId(L, 1));
                        lama_Number n = *numvalue(id);
                        lama_pop(L, 1);
                        int addr = INT;
                        if(n == 0) L->ip = bf->code_ptr + addr;
                        break;
                    }
                    case 1: { //CJMPnz
                        //fprintf (f, "CJMPnz\n");
                        fflush(f);
                        StkId id = unref(idx2StkId(L, 1));
                        lama_Number n = *numvalue(id);
                        lama_pop(L, 1);
                        int addr = INT;
                        if(n != 0) L->ip = bf->code_ptr + addr;
                        break;
                    }
                    case 2: { //BEGIN
                        //fprintf (f, "BEGIN\n");
                        fflush(f);

                        int args = INT, locs = INT;
                        lama_begin(L, 0, args, locs, retip);
                        break;
                    }
                    case 3: { //CBEGIN
                        //not_implemented;
                        //fprintf (f, "CBEGIN\n");
                        fflush(f);

                        int args = INT, locs = INT;
                        lama_begin(L, caps, args, locs, retip);
                        break;
                    }
                    case 4: { //CLOSURE
                        //fprintf (f, "CLOSURE\n");
                        fflush(f);

                        func_offset = INT;
                        caps = INT;
                        for (int i = 0; i < caps; i++) {
                            char tt = BYTE;
                            int idx = INT;
                            lama_pushTValue(L, *unref(loc2adr(L, lama_Loc{idx, tt})));
                        }
                        break;
                    }
                    case 5: { //CALLC
                        //not_implemented;
                        //fprintf (f, "CALLC\n");
                        fflush(f);

                        int args = INT;

                        char *func_ptr = bf->code_ptr + func_offset;
                        check(((*func_ptr & 0xF0) >> 4) == 5);
                        check((*func_ptr & 0x0F) == 2 || (*func_ptr & 0x0F) == 3);

                        retip = L->ip;
                        L->ip = func_ptr;
                        break;
                    }
                    case 6: { //CALL
                        //fprintf (f, "CALL\n");
                        fflush(f);

                        int func_offset = INT, args = INT;

                        char *func_ptr = bf->code_ptr + func_offset;
                        check(((*func_ptr & 0xF0) >> 4) == 5);
                        check((*func_ptr & 0x0F) == 2 || (*func_ptr & 0x0F) == 3);

                        retip = L->ip;
                        L->ip = func_ptr;
                        break;
                    }
                    case 7:
                        not_implemented;
                        //fprintf (f, "TAG\t%s ", STRING);
                        //fprintf (f, "%d", INT);
                    case 8: { //ARRAY
                        //fprintf (f, "ARRAY\n");
                        fflush(f);

                        int n = INT;
                        lama_Array arr = {n, allocArray(n)};
                        for (int i = 0; i < n; i++)
                            arr.arr[i] = *idx2StkId(L, n - i);
                        lama_pop(L, n);
                        lama_pusharr(L, arr);
                        break;
                    }
                    case 9:
                        not_implemented;
                        //fprintf (f, "FAIL\t%d", INT);
                        //fprintf (f, "%d", INT);
                    case 10: //LINE
                        //fprintf (f, "LINE\n");
                        fflush(f);

                        INT;
                        break;
                    default:
                        OPFAIL;
                }
                break;
            case 6:
                not_implemented;
                //fprintf (f, "PATT\t%s", pats[l]);
            case 7: {
                switch (l) {
                    case 0: { //CALL Lread
                        //fprintf (f, "READ\n");
                        fflush(f);

                        int n;
                        //lama_Ref ref = *lama_toref(L, 1);
                        fscanf(stdin, "%d", &n);
                        //setnumvalue(ref.ptr, n);
                        lama_pushnumber(L, n);
                        break;
                    }
                    case 1: { //CALL Lwrite
                        //fprintf (f, "WRITE\n");
                        fflush(f);

                        StkId id = unref(idx2StkId(L, 1));
                        //if (ttisref(id)) id = id->value.ref;
                        //check(ttisnumber(id));
                        fprintf(stdout, "%d\n", *numvalue(id));
                        //printstack(L);
                        break;
                    }
                    case 2: { //CALL Llength
                        StkId id = unref(idx2StkId(L, 1));
                        //if (ttisref(id)) id = id->value.ref;
                        lama_pop(L, 1);
                        if(ttisarray(id))
                            lama_pushnumber(L, id->value.arr.n);
                        else if(ttissexp(id))
                            lama_pushnumber(L, id->value.sexp.n);
                        else if(ttisstring(id))
                            lama_pushnumber(L, (int)strlen(*strvalue(id)));
                        else
                            FAIL;
                        break;
                    }
                    case 3:
                        not_implemented;
                        //fprintf (f, "CALL\tLstring");
                    case 4: { //CALL Barray
                        int n = INT;
                        lama_Array arr = {n, allocArray(n)};
                        for (int i = 0; i < n; i++)
                            arr.arr[i] = *idx2StkId(L, n - i);
                        lama_pop(L, n);
                        lama_pusharr(L, arr);
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
    while (1);
    stop: //fprintf (f, "<end>\n");
    return;
}

/* Dumps the contents of the file */
void dump_file (FILE *f, bytefile *bf) {
    int i;

    fprintf (f, "String table size       : %d\n", bf->stringtab_size);
    fprintf (f, "Global area size        : %d\n", bf->global_area_size);
    fprintf (f, "Number of public symbols: %d\n", bf->public_symbols_number);
    fprintf (f, "Public symbols          :\n");

    for (i=0; i < bf->public_symbols_number; i++)
        fprintf (f, "   0x%.8x: %s\n", get_public_offset (bf, i), get_public_name (bf, i));

    fprintf (f, "Code:\n");
    disassemble (f, bf);
}

int main (int argc, char* argv[]) {
    bytefile *f = read_file (argv[1]);
    dump_file (stdout, f);
    return 0;
}