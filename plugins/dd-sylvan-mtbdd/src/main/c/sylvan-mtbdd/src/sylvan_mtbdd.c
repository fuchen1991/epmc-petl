/*
 * Copyright 2011-2015 Formal Methods and Tools, University of Twente
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include <sylvan_config.h>

#include <assert.h>
#include <inttypes.h>
#include <math.h>
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <atomics.h>
// #include <avl.h>
#include <refs.h>
#include <sha2.h>
#include <sylvan.h>
#include <sylvan_common.h>

/**
 * MTBDD node structure
 */
typedef struct __attribute__((packed)) mtbddnode {
    uint64_t a, b;
} * mtbddnode_t; // 16 bytes

#define GETNODE(mtbdd) ((mtbddnode_t)llmsset_index_to_ptr(nodes, mtbdd&0x000000ffffffffff))

/**
 * Complement handling macros
 */
#define MTBDD_HASMARK(s)              (s&mtbdd_complement?1:0)
#define MTBDD_TOGGLEMARK(s)           (s^mtbdd_complement)
#define MTBDD_STRIPMARK(s)            (s&~mtbdd_complement)
#define MTBDD_TRANSFERMARK(from, to)  (to ^ (from & mtbdd_complement))
// Equal under mark
#define MTBDD_EQUALM(a, b)            ((((a)^(b))&(~mtbdd_complement))==0)

// Leaf: a = L=1, M, type; b = value
// Node: a = L=0, C, M, high; b = variable, low
// Only complement edge on "high"

static inline int
mtbddnode_isleaf(mtbddnode_t n)
{
    return n->a & 0x4000000000000000 ? 1 : 0;
}

static inline uint32_t
mtbddnode_gettype(mtbddnode_t n)
{
    return n->a & 0x00000000ffffffff;
}

static inline uint64_t
mtbddnode_getvalue(mtbddnode_t n)
{
    return n->b;
}

static inline int
mtbddnode_getcomp(mtbddnode_t n)
{
    return n->a & 0x8000000000000000 ? 1 : 0;
}

static inline uint64_t
mtbddnode_getlow(mtbddnode_t n)
{
    return n->b & 0x000000ffffffffff; // 40 bits
}

static inline uint64_t
mtbddnode_gethigh(mtbddnode_t n)
{
    return n->a & 0x800000ffffffffff; // 40 bits plus high bit of first
}

static inline uint32_t
mtbddnode_getvariable(mtbddnode_t n)
{
    return (uint32_t)(n->b >> 40);
}

static inline int
mtbddnode_getmark(mtbddnode_t n)
{
    return n->a & 0x2000000000000000 ? 1 : 0;
}

static inline void
mtbddnode_setmark(mtbddnode_t n, int mark)
{
    if (mark) n->a |= 0x2000000000000000;
    else n->a &= 0xdfffffffffffffff;
}

static inline void
mtbddnode_makeleaf(mtbddnode_t n, uint32_t type, uint64_t value)
{
    n->a = 0x4000000000000000 | (uint64_t)type;
    n->b = value;
}

static inline void
mtbddnode_makenode(mtbddnode_t n, uint32_t var, uint64_t low, uint64_t high)
{
    n->a = high;
    n->b = ((uint64_t)var)<<40 | low;
}

/* Primitives */
int
mtbdd_isleaf(MTBDD bdd)
{
    if (bdd == mtbdd_true || bdd == mtbdd_false) return 1;
    return mtbddnode_isleaf(GETNODE(bdd));
}

// for nodes
uint32_t
mtbdd_getvar(MTBDD node)
{
    return mtbddnode_getvariable(GETNODE(node));
}

MTBDD
node_getlow(MTBDD mtbdd, mtbddnode_t node)
{
    return MTBDD_TRANSFERMARK(mtbdd, mtbddnode_getlow(node));
}

MTBDD
node_gethigh(MTBDD mtbdd, mtbddnode_t node)
{
    return MTBDD_TRANSFERMARK(mtbdd, mtbddnode_gethigh(node));
}

MTBDD
mtbdd_getlow(MTBDD mtbdd)
{
    return node_getlow(mtbdd, GETNODE(mtbdd));
}

MTBDD
mtbdd_gethigh(MTBDD mtbdd)
{
    return node_gethigh(mtbdd, GETNODE(mtbdd));
}

// for leafs
uint32_t
mtbdd_gettype(MTBDD leaf)
{
    return mtbddnode_gettype(GETNODE(leaf));
}

uint64_t
mtbdd_getvalue(MTBDD leaf)
{
    return mtbddnode_getvalue(GETNODE(leaf));
}

double
mtbdd_getdouble(MTBDD leaf)
{
    uint64_t value = mtbdd_getvalue(leaf);
    double dv = *(double*)&value;
    if (mtbdd_isnegated(leaf)) return -dv;
    else return dv;
}

/**
 * Implementation of garbage collection
 */

/* Recursively mark MDD nodes as 'in use' */
VOID_TASK_IMPL_1(mtbdd_gc_mark_rec, MDD, mtbdd)
{
    if (mtbdd <= mtbdd_true) return;

    if (llmsset_mark(nodes, mtbdd)) {
        mtbddnode_t n = GETNODE(mtbdd);
        if (!mtbddnode_isleaf(n)) {
            SPAWN(mtbdd_gc_mark_rec, mtbddnode_getlow(n));
            CALL(mtbdd_gc_mark_rec, mtbddnode_gethigh(n));
            SYNC(mtbdd_gc_mark_rec);
        }
    }
}

/**
 * External references
 */

refs_table_t mtbdd_refs;
refs_table_t mtbdd_protected;
static int mtbdd_protected_created = 0;

MDD
mtbdd_ref(MDD a)
{
    if (a == mtbdd_true || a == mtbdd_false) return a;
    refs_up(&mtbdd_refs, a);
    return a;
}

void
mtbdd_deref(MDD a)
{
    if (a == mtbdd_true || a == mtbdd_false) return;
    refs_down(&mtbdd_refs, a);
}

size_t
mtbdd_count_refs()
{
    return refs_count(&mtbdd_refs);
}

void
mtbdd_protect(MTBDD *a)
{
    if (!mtbdd_protected_created) {
        // In C++, sometimes mtbdd_protect is called before Sylvan is initialized. Just create a table.
        protect_create(&mtbdd_protected, 4096);
        mtbdd_protected_created = 1;
    }
    protect_up(&mtbdd_protected, (size_t)a);
}

void
mtbdd_unprotect(MTBDD *a)
{
    protect_down(&mtbdd_protected, (size_t)a);
}

size_t
mtbdd_count_protected()
{
    return protect_count(&mtbdd_protected);
}

/* Called during garbage collection */
VOID_TASK_0(mtbdd_gc_mark_external_refs)
{
    // iterate through refs hash table, mark all found
    size_t count=0;
    uint64_t *it = refs_iter(&mtbdd_refs, 0, mtbdd_refs.refs_size);
    while (it != NULL) {
        SPAWN(mtbdd_gc_mark_rec, refs_next(&mtbdd_refs, &it, mtbdd_refs.refs_size));
        count++;
    }
    while (count--) {
        SYNC(mtbdd_gc_mark_rec);
    }
}

VOID_TASK_0(mtbdd_gc_mark_protected)
{
    // iterate through refs hash table, mark all found
    size_t count=0;
    uint64_t *it = protect_iter(&mtbdd_protected, 0, mtbdd_protected.refs_size);
    while (it != NULL) {
        BDD *to_mark = (BDD*)protect_next(&mtbdd_protected, &it, mtbdd_protected.refs_size);
        SPAWN(mtbdd_gc_mark_rec, *to_mark);
        count++;
    }
    while (count--) {
        SYNC(mtbdd_gc_mark_rec);
    }
}

/* Infrastructure for internal markings */
DECLARE_THREAD_LOCAL(mtbdd_refs_key, mtbdd_refs_internal_t);

VOID_TASK_0(mtbdd_refs_mark_task)
{
    LOCALIZE_THREAD_LOCAL(mtbdd_refs_key, mtbdd_refs_internal_t);
    size_t i, j=0;
    for (i=0; i<mtbdd_refs_key->r_count; i++) {
        if (j >= 40) {
            while (j--) SYNC(mtbdd_gc_mark_rec);
            j=0;
        }
        SPAWN(mtbdd_gc_mark_rec, mtbdd_refs_key->results[i]);
        j++;
    }
    for (i=0; i<mtbdd_refs_key->s_count; i++) {
        Task *t = mtbdd_refs_key->spawns[i];
        if (!TASK_IS_STOLEN(t)) break;
        if (TASK_IS_COMPLETED(t)) {
            if (j >= 40) {
                while (j--) SYNC(mtbdd_gc_mark_rec);
                j=0;
            }
            SPAWN(mtbdd_gc_mark_rec, *(BDD*)TASK_RESULT(t));
            j++;
        }
    }
    while (j--) SYNC(mtbdd_gc_mark_rec);
}

VOID_TASK_0(mtbdd_refs_mark)
{
    TOGETHER(mtbdd_refs_mark_task);
}

VOID_TASK_0(mtbdd_refs_init_task)
{
    mtbdd_refs_internal_t s = (mtbdd_refs_internal_t)malloc(sizeof(struct mtbdd_refs_internal));
    s->r_size = 128;
    s->r_count = 0;
    s->s_size = 128;
    s->s_count = 0;
    s->results = (BDD*)malloc(sizeof(BDD) * 128);
    s->spawns = (Task**)malloc(sizeof(Task*) * 128);
    SET_THREAD_LOCAL(mtbdd_refs_key, s);
}

VOID_TASK_0(mtbdd_refs_init)
{
    INIT_THREAD_LOCAL(mtbdd_refs_key);
    TOGETHER(mtbdd_refs_init_task);
    sylvan_gc_add_mark(10, TASK(mtbdd_refs_mark));
}

/**
 * Initialize and quit functions
 */

static void
mtbdd_quit()
{
    refs_free(&mtbdd_refs);
    if (mtbdd_protected_created) {
        protect_free(&mtbdd_protected);
        mtbdd_protected_created = 0;
    }
}

void
sylvan_init_mtbdd()
{
    sylvan_register_quit(mtbdd_quit);
    sylvan_gc_add_mark(10, TASK(mtbdd_gc_mark_external_refs));
    sylvan_gc_add_mark(10, TASK(mtbdd_gc_mark_protected));

    // Sanity check
    if (sizeof(struct mtbddnode) != 16) {
        fprintf(stderr, "Invalid size of mtbdd nodes: %ld\n", sizeof(struct mtbddnode));
        exit(1);
    }

    refs_create(&mtbdd_refs, 1024);
    if (!mtbdd_protected_created) {
        protect_create(&mtbdd_protected, 4096);
        mtbdd_protected_created = 1;
    }

    LACE_ME;
    CALL(mtbdd_refs_init);
}

/**
 * Primitives
 */
MTBDD
mtbdd_makeleaf(uint32_t type, uint64_t value)
{
    struct mtbddnode n;
    mtbddnode_makeleaf(&n, type, value);

    int created;
    uint64_t index = llmsset_lookup(nodes, n.a, n.b, &created);
    if (index == 0) {
        LACE_ME;

        sylvan_gc();

        index = llmsset_lookup(nodes, n.a, n.b, &created);
        if (index == 0) {
            fprintf(stderr, "BDD Unique table full, %zu of %zu buckets filled!\n", llmsset_count_marked(nodes), llmsset_get_size(nodes));
            exit(1);
        }
    }

    return (MTBDD)index;
}

MTBDD
mtbdd_makenode(uint32_t var, MTBDD low, MTBDD high)
{
    if (low == high) return low;

    // Normalization to keep canonicity
    // low will have no mark

    struct mtbddnode n;
    int mark, created;

    if (MTBDD_HASMARK(low)) {
        mark = 1;
        low = MTBDD_TOGGLEMARK(low);
        high = MTBDD_TOGGLEMARK(high);
    } else {
        mark = 0;
    }

    mtbddnode_makenode(&n, var, low, high);

    MTBDD result;
    uint64_t index = llmsset_lookup(nodes, n.a, n.b, &created);
    if (index == 0) {
        LACE_ME;

        mtbdd_refs_push(low);
        mtbdd_refs_push(high);
        sylvan_gc();
        mtbdd_refs_pop(2);

        index = llmsset_lookup(nodes, n.a, n.b, &created);
        if (index == 0) {
            fprintf(stderr, "BDD Unique table full, %zu of %zu buckets filled!\n", llmsset_count_marked(nodes), llmsset_get_size(nodes));
            exit(1);
        }
    }

    result = index;
    return mark ? result | mtbdd_complement : result;
}

/* Operations */

/**
 * Create leafs of unsigned/signed integers and doubles
 */

MTBDD
mtbdd_uint64(uint64_t value)
{
    return mtbdd_makeleaf(0, value);
}

MTBDD
mtbdd_double(double value)
{
    if (value < 0.0) {
        value = -value;
        return mtbdd_negate(mtbdd_makeleaf(1, *(uint64_t*)&value));
    } else {
        return mtbdd_makeleaf(1, *(uint64_t*)&value);
    }
}

/**
 * Create the cube of variables in arr.
 */
MTBDD
mtbdd_fromarray(uint32_t* arr, size_t length)
{
    if (length == 0) return mtbdd_true;
    else if (length == 1) return mtbdd_makenode(*arr, mtbdd_false, mtbdd_true);
    else return mtbdd_makenode(*arr, mtbdd_false, mtbdd_fromarray(arr+1, length-1));
}

/**
 * Create a MTBDD cube representing the conjunction of variables in their positive or negative
 * form depending on whether the cube[idx] equals 0 (negative), 1 (positive) or 2 (any).
 * Use cube[idx]==3 for "s=s'" in interleaved variables (matches with next variable)
 * <variables> is the cube of variables
 */
MTBDD
mtbdd_cube(MTBDD variables, uint8_t *cube, MTBDD terminal)
{
    if (variables == mtbdd_true) return terminal;
    mtbddnode_t n = GETNODE(variables);

    BDD result;
    switch (*cube) {
    case 0:
        result = mtbdd_cube(node_gethigh(variables, n), cube+1, terminal);
        result = mtbdd_makenode(mtbddnode_getvariable(n), result, mtbdd_false);
        return result;
    case 1:
        result = mtbdd_cube(node_gethigh(variables, n), cube+1, terminal);
        result = mtbdd_makenode(mtbddnode_getvariable(n), mtbdd_false, result);
        return result;
    case 2:
        return mtbdd_cube(node_gethigh(variables, n), cube+1, terminal);
    case 3:
    {
        MTBDD variables2 = node_gethigh(variables, n);
        mtbddnode_t n2 = GETNODE(variables2);
        uint32_t var2 = mtbddnode_getvariable(n2);
        result = mtbdd_cube(node_gethigh(variables2, n2), cube+2, terminal);
        BDD low = mtbdd_makenode(var2, result, mtbdd_false);
        mtbdd_refs_push(low);
        BDD high = mtbdd_makenode(var2, mtbdd_false, result);
        mtbdd_refs_pop(1);
        result = mtbdd_makenode(mtbddnode_getvariable(n), low, high);
        return result;
    }
    default:
        return mtbdd_false; // ?
    }
}

/**
 * Same as mtbdd_cube, but also performs "or" with existing MTBDD,
 * effectively adding an item to the set
 */
TASK_IMPL_4(MTBDD, mtbdd_union_cube, MTBDD, mtbdd, MTBDD, vars, uint8_t*, cube, MTBDD, terminal)
{
    /* Terminal cases */
    if (mtbdd == terminal) return terminal;
    if (mtbdd == mtbdd_false) return mtbdd_cube(vars, cube, terminal);
    if (vars == mtbdd_true) return terminal;

    sylvan_gc_test();

    mtbddnode_t nv = GETNODE(vars);
    uint32_t v = mtbddnode_getvariable(nv);

    mtbddnode_t na = GETNODE(mtbdd);
    uint32_t va = mtbddnode_getvariable(na);

    if (va < v) {
        MTBDD low = node_getlow(mtbdd, na);
        MTBDD high = node_gethigh(mtbdd, na);
        SPAWN(mtbdd_union_cube, high, vars, cube, terminal);
        BDD new_low = mtbdd_union_cube(low, vars, cube, terminal);
        mtbdd_refs_push(new_low);
        BDD new_high = SYNC(mtbdd_union_cube);
        mtbdd_refs_pop(1);
        if (new_low != low || new_high != high) return mtbdd_makenode(va, new_low, new_high);
        else return mtbdd;
    } else if (va == v) {
        MTBDD low = node_getlow(mtbdd, na);
        MTBDD high = node_gethigh(mtbdd, na);
        switch (*cube) {
        case 0:
        {
            MTBDD new_low = mtbdd_union_cube(low, node_gethigh(vars, nv), cube+1, terminal);
            if (new_low != low) return mtbdd_makenode(v, new_low, high);
            else return mtbdd;
        }
        case 1:
        {
            MTBDD new_high = mtbdd_union_cube(high, node_gethigh(vars, nv), cube+1, terminal);
            if (new_high != high) return mtbdd_makenode(v, low, new_high);
            return mtbdd;
        }
        case 2:
        {
            SPAWN(mtbdd_union_cube, high, node_gethigh(vars, nv), cube+1, terminal);
            MTBDD new_low = mtbdd_union_cube(low, node_gethigh(vars, nv), cube+1, terminal);
            mtbdd_refs_push(new_low);
            MTBDD new_high = SYNC(mtbdd_union_cube);
            mtbdd_refs_pop(1);
            if (new_low != low || new_high != high) return mtbdd_makenode(v, new_low, new_high);
            return mtbdd;
        }
        case 3:
        {
            return mtbdd_false; // currently not implemented
        }
        default:
            return mtbdd_false;
        }
    } else /* va > v */ {
        switch (*cube) {
        case 0:
        {
            MTBDD new_low = mtbdd_union_cube(mtbdd, node_gethigh(vars, nv), cube+1, terminal);
            return mtbdd_makenode(v, new_low, mtbdd_false);
        }
        case 1:
        {
            MTBDD new_high = mtbdd_union_cube(mtbdd, node_gethigh(vars, nv), cube+1, terminal);
            return mtbdd_makenode(v, mtbdd_false, new_high);
        }
        case 2:
        {
            SPAWN(mtbdd_union_cube, mtbdd, node_gethigh(vars, nv), cube+1, terminal);
            MTBDD new_low = mtbdd_union_cube(mtbdd, node_gethigh(vars, nv), cube+1, terminal);
            mtbdd_refs_push(new_low);
            MTBDD new_high = SYNC(mtbdd_union_cube);
            mtbdd_refs_pop(1);
            return mtbdd_makenode(v, new_low, new_high);
        }
        case 3:
        {
            return mtbdd_false; // currently not implemented
        }
        default:
            return mtbdd_false;
        }
    }
}

/**
 * Apply a binary operation <op> to <a> and <b>.
 */
TASK_IMPL_3(MTBDD, mtbdd_apply, MTBDD, a, MTBDD, b, mtbdd_apply_op, op)
{
    /* Check terminal case */
    MTBDD result = WRAP(op, &a, &b);
    if (result != mtbdd_invalid) return result;

    /* Maybe perform garbage collection */
    sylvan_gc_test();

    /* Check cache */
    if (cache_get(a | CACHE_MTBDD_APPLY, b, (size_t)op, &result)) return result;

    /* Get top variable */
    int la = mtbdd_isleaf(a);
    int lb = mtbdd_isleaf(b);
    mtbddnode_t na = la ? 0 : GETNODE(a);
    mtbddnode_t nb = lb ? 0 : GETNODE(b);
    uint32_t va = la ? 0xffffffff : mtbddnode_getvariable(na);
    uint32_t vb = lb ? 0xffffffff : mtbddnode_getvariable(nb);
    uint32_t v = va < vb ? va : vb;

    /* Get cofactors */
    MTBDD alow, ahigh, blow, bhigh;
    alow  = (!la && va == v) ? node_getlow(a, na)  : a;
    ahigh = (!la && va == v) ? node_gethigh(a, na) : a;
    blow  = (!lb && vb == v) ? node_getlow(b, nb)  : b;
    bhigh = (!lb && vb == v) ? node_gethigh(b, nb) : b;

    /* Recursive */
    mtbdd_refs_spawn(SPAWN(mtbdd_apply, ahigh, bhigh, op));
    MTBDD low = mtbdd_refs_push(CALL(mtbdd_apply, alow, blow, op));
    MTBDD high = mtbdd_refs_sync(SYNC(mtbdd_apply));
    result = mtbdd_makenode(v, low, high);
    mtbdd_refs_pop(1);

    /* Store in cache */
    cache_put(a | CACHE_MTBDD_APPLY, b, (size_t)op, result);
    return result;
}

/**
 * Apply a unary operation <op> to <dd>.
 */
TASK_IMPL_3(MTBDD, mtbdd_uapply, MTBDD, dd, mtbdd_uapply_op, op, size_t, param)
{
    /* Maybe perform garbage collection */
    sylvan_gc_test();

    /* Check cache */
    MTBDD result;
    if (cache_get(dd | CACHE_MTBDD_UAPPLY, (size_t)op, param, &result)) return result;

    /* Check terminal case */
    result = WRAP(op, dd, param);
    if (result != mtbdd_invalid) {
        /* Store in cache */
        cache_put(dd | CACHE_MTBDD_UAPPLY, (size_t)op, param, result);
        return result;
    }

    /* Get cofactors */
    mtbddnode_t ndd = GETNODE(dd);
    MTBDD ddlow = node_getlow(dd, ndd);
    MTBDD ddhigh = node_gethigh(dd, ndd);

    /* Recursive */
    mtbdd_refs_spawn(SPAWN(mtbdd_uapply, ddhigh, op, param));
    MTBDD low = mtbdd_refs_push(CALL(mtbdd_uapply, ddlow, op, param));
    MTBDD high = mtbdd_refs_sync(SYNC(mtbdd_uapply));
    result = mtbdd_makenode(mtbddnode_getvariable(ndd), low, high);
    mtbdd_refs_pop(1);

    /* Store in cache */
    cache_put(dd | CACHE_MTBDD_UAPPLY, (size_t)op, param, result);
    return result;
}

/**
 * Abstract the variables in <v> from <a> using the operation <op>
 */
TASK_IMPL_3(MTBDD, mtbdd_abstract, MTBDD, a, MTBDD, v, mtbdd_apply_op, op)
{
    /* Check terminal case */
    if (a == mtbdd_false) return mtbdd_false;
    if (a == mtbdd_true) return mtbdd_true;
    if (v == mtbdd_true) return a;

    /* Maybe perform garbage collection */
    sylvan_gc_test();

    /* Check cache */
    MTBDD result;
    if (cache_get(a | CACHE_MTBDD_ABSTRACT, v, (size_t)op, &result)) return result;

    /* a != constant, v != constant */
    mtbddnode_t na = GETNODE(a);
    mtbddnode_t nv = GETNODE(v);

    /* Recursive */
    if (mtbddnode_isleaf(na)) {
        result = CALL(mtbdd_abstract, a, node_gethigh(v, nv), op);
        mtbdd_refs_push(result);
        result = mtbdd_apply(result, result, op);
        mtbdd_refs_pop(1);
    } else {
        uint32_t var_a = mtbddnode_getvariable(na);
        uint32_t var_v = mtbddnode_getvariable(nv);
        if (var_a < var_v) {
            SPAWN(mtbdd_abstract, node_gethigh(a, na), v, op);
            MTBDD low = CALL(mtbdd_abstract, node_getlow(a, na), v, op);
            mtbdd_refs_push(low);
            MTBDD high = SYNC(mtbdd_abstract);
            mtbdd_refs_pop(1);
            result = mtbdd_makenode(var_a, low, high);
        } else if (var_a > var_v) {
            result = CALL(mtbdd_abstract, a, node_gethigh(v, nv), op);
            mtbdd_refs_push(result);
            result = mtbdd_apply(result, result, op);
            mtbdd_refs_pop(1);
        } else /* var_a == var_v */ {
            SPAWN(mtbdd_abstract, node_gethigh(a, na), node_gethigh(v, nv), op);
            MTBDD low = CALL(mtbdd_abstract, node_getlow(a, na), node_gethigh(v, nv), op);
            mtbdd_refs_push(low);
            MTBDD high = SYNC(mtbdd_abstract);
            mtbdd_refs_push(high);
            result = mtbdd_apply(low, high, op);
            mtbdd_refs_pop(2);
        }
    }

    /* Store in cache */
    cache_put(a | CACHE_MTBDD_ABSTRACT, v, (size_t)op, result);
    return result;
}

/**
 * Binary operation Plus (for MTBDDs of same type)
 * Only for MTBDDs where either all leafs are Boolean, or Integer, or Double.
 * For Integer/Double MTBDDs, mtbdd_false is interpreted as "0" or "0.0".
 */
TASK_IMPL_2(MTBDD, mtbdd_op_plus, MTBDD*, pa, MTBDD*, pb)
{
    MTBDD a = *pa, b = *pb;
    if (a == mtbdd_false) return b;
    if (b == mtbdd_false) return a;

    // Handle Boolean MTBDDs: interpret as Or
    if (a == mtbdd_true) return mtbdd_true;
    if (b == mtbdd_true) return mtbdd_true;

    mtbddnode_t na = GETNODE(a);
    mtbddnode_t nb = GETNODE(b);

    if (mtbddnode_isleaf(na) && mtbddnode_isleaf(nb)) {
        uint64_t val_a = mtbddnode_getvalue(na);
        uint64_t val_b = mtbddnode_getvalue(nb);
        if (mtbddnode_gettype(na) == 0 && mtbddnode_gettype(nb) == 0) {
            // both uint64_t
            if (val_a == 0) return b;
            else if (val_b == 0) return a;
            else {
                int nega = mtbdd_isnegated(a);
                int negb = mtbdd_isnegated(b);
                if (nega) {
                    if (negb) {
                        // -a + -b = -(a+b)
                        return mtbdd_negate(mtbdd_uint64(val_a + val_b));
                    } else {
                        // b - a
                        if (val_b >= val_a) {
                            return mtbdd_uint64(val_b - val_a);
                        } else {
                            return mtbdd_negate(mtbdd_uint64(val_a - val_b));
                        }
                    }
                } else {
                    if (negb) {
                        // a - b
                        if (val_a >= val_b) {
                            return mtbdd_uint64(val_a - val_b);
                        } else {
                            return mtbdd_negate(mtbdd_uint64(val_b - val_a));
                        }
                    } else {
                        // a + b
                        return mtbdd_uint64(val_a + val_b);
                    }
                }
            }
        } else if (mtbddnode_gettype(na) == 1 && mtbddnode_gettype(nb) == 1) {
            // both double
            double vval_a = *(double*)&val_a;
            double vval_b = *(double*)&val_b;
            if (vval_a == 0.0) return b;
            else if (vval_b == 0.0) return a;
            else {
                int nega = mtbdd_isnegated(a);
                int negb = mtbdd_isnegated(b);
                if (nega) {
                    if (negb) {
                        // -a + -b = -(a+b)
                        return mtbdd_negate(mtbdd_double(vval_a + vval_b));
                    } else {
                        // b - a
                        if (val_b >= val_a) {
                            return mtbdd_double(vval_b - vval_a);
                        } else {
                            return mtbdd_negate(mtbdd_double(vval_a - vval_b));
                        }
                    }
                } else {
                    if (negb) {
                        // a - b
                        if (val_a >= val_b) {
                            return mtbdd_double(vval_a - vval_b);
                        } else {
                            return mtbdd_negate(mtbdd_double(vval_b - vval_a));
                        }
                    } else {
                        // a + b
                        return mtbdd_double(vval_a + vval_b);
                    }
                }
            }
        }
    }

    if (a < b) {
        *pa = b;
        *pb = a;
    }

    return mtbdd_invalid;
}

/**
 * Binary operation Times (for MTBDDs of same type)
 * Only for MTBDDs where either all leafs are Boolean, or Integer, or Double.
 * For Integer/Double MTBDD, if either operand is mtbdd_false (not defined),
 * then the result is mtbdd_false (i.e. not defined).
 */
TASK_IMPL_2(MTBDD, mtbdd_op_times, MTBDD*, pa, MTBDD*, pb)
{
    MTBDD a = *pa, b = *pb;
    if (a == mtbdd_false || b == mtbdd_false) return mtbdd_false;

    // Handle Boolean MTBDDs: interpret as And
    if (a == mtbdd_true) return b;
    if (b == mtbdd_true) return a;

    mtbddnode_t na = GETNODE(a);
    mtbddnode_t nb = GETNODE(b);

    if (mtbddnode_isleaf(na) && mtbddnode_isleaf(nb)) {
        uint64_t val_a = mtbddnode_getvalue(na);
        uint64_t val_b = mtbddnode_getvalue(nb);
        if (mtbddnode_gettype(na) == 0 && mtbddnode_gettype(nb) == 0) {
            // both uint64_t
            if (val_a == 0) return a;
            else if (val_b == 0) return b;
            else {
                MTBDD result;
                if (val_a == 1) result = b;
                else if (val_b == 1) result = a;
                else result = mtbdd_uint64(val_a*val_b);
                int nega = mtbdd_isnegated(a);
                int negb = mtbdd_isnegated(b);
                if (nega ^ negb) return mtbdd_negate(result);
                else return result;
            }
        } else if (mtbddnode_gettype(na) == 1 && mtbddnode_gettype(nb) == 1) {
            // both double
            double vval_a = *(double*)&val_a;
            double vval_b = *(double*)&val_b;
            if (vval_a == 0.0) return a;
            else if (vval_b == 0.0) return b;
            else {
                MTBDD result;
                if (vval_a == 1.0) result = b;
                else if (vval_b == 1.0) result = a;
                else result = mtbdd_double(vval_a*vval_b);
                int nega = mtbdd_isnegated(a);
                int negb = mtbdd_isnegated(b);
                if (nega ^ negb) return mtbdd_negate(result);
                else return result;
            }
        }
    }

    if (a < b) {
        *pa = b;
        *pb = a;
    }

    return mtbdd_invalid;
}

/**
 * Binary operation Minimum (for MTBDDs of same type)
 * Only for MTBDDs where either all leafs are Boolean, or Integer, or Double.
 * For Integer/Double MTBDD, if either operand is mtbdd_false (not defined),
 * then the result is the other operand.
 */
TASK_IMPL_2(MTBDD, mtbdd_op_min, MTBDD*, pa, MTBDD*, pb)
{
    MTBDD a = *pa, b = *pb;
    if (a == mtbdd_true) return b;
    if (b == mtbdd_true) return a;
    if (a == b) return a;

    // Special case where "false" indicates a partial function
    if (a == mtbdd_false && b != mtbdd_false && mtbddnode_isleaf(GETNODE(b))) return b;
    if (b == mtbdd_false && a != mtbdd_false && mtbddnode_isleaf(GETNODE(a))) return a;

    mtbddnode_t na = GETNODE(a);
    mtbddnode_t nb = GETNODE(b);

    if (mtbddnode_isleaf(na) && mtbddnode_isleaf(nb)) {
        uint64_t val_a = mtbddnode_getvalue(na);
        uint64_t val_b = mtbddnode_getvalue(nb);
        if (mtbddnode_gettype(na) == 0 && mtbddnode_gettype(nb) == 0) {
            // both uint64_t
            int nega = mtbdd_isnegated(a);
            int negb = mtbdd_isnegated(b);
            if (nega) {
                if (negb) return val_a > val_b ? a : b;
                else return a;
            } else {
                if (negb) return b;
                else return val_a < val_b ? a : b;
            }
        } else if (mtbddnode_gettype(na) == 1 && mtbddnode_gettype(nb) == 1) {
            // both double
            double vval_a = *(double*)&val_a;
            double vval_b = *(double*)&val_b;
            int nega = mtbdd_isnegated(a);
            int negb = mtbdd_isnegated(b);
            if (nega) {
                if (negb) return vval_a > vval_b ? a : b;
                else return a;
            } else {
                if (negb) return b;
                else return vval_a < vval_b ? a : b;
            }
         }
    }

    if (a < b) {
        *pa = b;
        *pb = a;
    }

    return mtbdd_invalid;
}

/**
 * Binary operation Maximum (for MTBDDs of same type)
 * Only for MTBDDs where either all leafs are Boolean, or Integer, or Double.
 * For Integer/Double MTBDD, if either operand is mtbdd_false (not defined),
 * then the result is the other operand.
 */
TASK_IMPL_2(MTBDD, mtbdd_op_max, MTBDD*, pa, MTBDD*, pb)
{
    MTBDD a = *pa, b = *pb;
    if (a == mtbdd_true) return a;
    if (b == mtbdd_true) return b;
    if (a == mtbdd_false) return b;
    if (b == mtbdd_false) return a;
    if (a == b) return a;

    mtbddnode_t na = GETNODE(a);
    mtbddnode_t nb = GETNODE(b);

    if (mtbddnode_isleaf(na) && mtbddnode_isleaf(nb)) {
        uint64_t val_a = mtbddnode_getvalue(na);
        uint64_t val_b = mtbddnode_getvalue(nb);
        if (mtbddnode_gettype(na) == 0 && mtbddnode_gettype(nb) == 0) {
            // both uint64_t
            int nega = mtbdd_isnegated(a);
            int negb = mtbdd_isnegated(b);
            if (nega) {
                if (negb) return val_a < val_b ? a : b;
                else return b;
            } else {
                if (negb) return a;
                else return val_a > val_b ? a : b;
            }
        } else if (mtbddnode_gettype(na) == 1 && mtbddnode_gettype(nb) == 1) {
            // both double
            double vval_a = *(double*)&val_a;
            double vval_b = *(double*)&val_b;
            int nega = mtbdd_isnegated(a);
            int negb = mtbdd_isnegated(b);
            if (nega) {
                if (negb) return vval_a < vval_b ? a : b;
                else return b;
            } else {
                if (negb) return a;
                else return vval_a > vval_b ? a : b;
            }
         }
    }

    if (a < b) {
        *pa = b;
        *pb = a;
    }

    return mtbdd_invalid;
}

/**
 * Compute IF <f> THEN <g> ELSE <h>.
 * <f> must be a Boolean MTBDD (or standard BDD).
 */
TASK_IMPL_3(MTBDD, mtbdd_ite, MTBDD, f, MTBDD, g, MTBDD, h)
{
    /* Terminal cases */
    if (f == mtbdd_true) return g;
    if (f == mtbdd_false) return h;
    if (g == h) return g;
    if (g == mtbdd_true && h == mtbdd_false) return f;
    if (h == mtbdd_true && g == mtbdd_false) return MTBDD_TOGGLEMARK(f);

    // If all MTBDD's are Boolean, then there could be further optimizations (see sylvan_bdd.c)

    /* Maybe perform garbage collection */
    sylvan_gc_test();

    /* Check cache */
    MTBDD result;
    if (cache_get(f | CACHE_MTBDD_ITE, g, h, &result)) return result;

    /* Get top variable */
    int lg = mtbdd_isleaf(g);
    int lh = mtbdd_isleaf(h);
    mtbddnode_t nf = GETNODE(f);
    mtbddnode_t ng = lg ? 0 : GETNODE(g);
    mtbddnode_t nh = lh ? 0 : GETNODE(h);
    uint32_t vf = mtbddnode_getvariable(nf);
    uint32_t vg = lg ? 0 : mtbddnode_getvariable(ng);
    uint32_t vh = lh ? 0 : mtbddnode_getvariable(nh);
    uint32_t v = vf;
    if (!lg && vg < v) v = vg;
    if (!lh && vh < v) v = vh;

    /* Get cofactors */
    MTBDD flow, fhigh, glow, ghigh, hlow, hhigh;
    flow = (vf == v) ? node_getlow(f, nf) : f;
    fhigh = (vf == v) ? node_gethigh(f, nf) : f;
    glow = (!lg && vg == v) ? node_getlow(g, ng) : g;
    ghigh = (!lg && vg == v) ? node_gethigh(g, ng) : g;
    hlow = (!lh && vh == v) ? node_getlow(h, nh) : h;
    hhigh = (!lh && vh == v) ? node_gethigh(h, nh) : h;

    /* Recursive calls */
    mtbdd_refs_spawn(SPAWN(mtbdd_ite, fhigh, ghigh, hhigh));
    MTBDD low = mtbdd_refs_push(CALL(mtbdd_ite, flow, glow, hlow));
    MTBDD high = mtbdd_refs_push(mtbdd_refs_sync(SYNC(mtbdd_ite)));
    result = mtbdd_makenode(v, low, high);
    mtbdd_refs_pop(2);

    /* Store in cache */
    cache_put(f | CACHE_MTBDD_ITE, g, h, result);
    return result;
}

/**
 * Monad that converts double to a Boolean MTBDD, translate terminals >= value to 1 and to 0 otherwise;
 */
TASK_IMPL_2(MTBDD, mtbdd_op_threshold_double, MTBDD, a, double, value)
{
    /* We only expect "double" terminals, or false */
    if (a == mtbdd_false) return mtbdd_false;
    if (a == mtbdd_true) return mtbdd_invalid;

    // a != constant
    mtbddnode_t na = GETNODE(a);

    if (mtbddnode_isleaf(na) && mtbddnode_gettype(na) == 1) {
        return mtbdd_getdouble(a) >= value ? mtbdd_true : mtbdd_false;
    }

    return mtbdd_invalid;
}

/**
 * Monad that converts double to a Boolean BDD, translate terminals > value to 1 and to 0 otherwise;
 */
TASK_IMPL_2(MTBDD, mtbdd_op_strict_threshold_double, MTBDD, a, double, value)
{
    /* We only expect "double" terminals, or false */
    if (a == mtbdd_false) return mtbdd_false;
    if (a == mtbdd_true) return mtbdd_invalid;

    // a != constant
    mtbddnode_t na = GETNODE(a);

    if (mtbddnode_isleaf(na) && mtbddnode_gettype(na) == 1) {
        return mtbdd_getdouble(a) > value ? mtbdd_true : mtbdd_false;
    }

    return mtbdd_invalid;
}

/**
 * Multiply <a> and <b>, and abstract variables <vars> using summation.
 * This is similar to the "and_exists" operation in BDDs.
 */
TASK_IMPL_3(MTBDD, mtbdd_and_exists, MTBDD, a, MTBDD, b, MTBDD, v)
{
    /* Check terminal case */
    if (v == mtbdd_true) return mtbdd_apply(a, b, TASK(mtbdd_op_times));
    MTBDD result = CALL(mtbdd_op_times, &a, &b);
    if (result != mtbdd_invalid) return mtbdd_abstract(result, v, TASK(mtbdd_op_plus));

    /* Maybe perform garbage collection */
    sylvan_gc_test();

    /* Check cache */
    if (cache_get(a | CACHE_MTBDD_AND_EXISTS, b, v, &result)) return result;

    /* Now, v is not a constant, and either a or b is not a constant */

    /* Get top variable */
    int la = mtbdd_isleaf(a);
    int lb = mtbdd_isleaf(b);
    mtbddnode_t na = la ? 0 : GETNODE(a);
    mtbddnode_t nb = lb ? 0 : GETNODE(b);
    uint32_t va = la ? 0xffffffff : mtbddnode_getvariable(na);
    uint32_t vb = lb ? 0xffffffff : mtbddnode_getvariable(nb);
    uint32_t var = va < vb ? va : vb;

    mtbddnode_t nv = GETNODE(v);
    uint32_t vv = mtbddnode_getvariable(nv);

    if (vv < var) {
        /* Recursive, then abstract result */
        result = CALL(mtbdd_and_exists, a, b, node_gethigh(v, nv));
        mtbdd_refs_push(result);
        result = mtbdd_apply(result, result, TASK(mtbdd_op_plus));
        mtbdd_refs_pop(1);
    } else {
        /* Get cofactors */
        MTBDD alow, ahigh, blow, bhigh;
        alow  = (!la && va == var) ? node_getlow(a, na)  : a;
        ahigh = (!la && va == var) ? node_gethigh(a, na) : a;
        blow  = (!lb && vb == var) ? node_getlow(b, nb)  : b;
        bhigh = (!lb && vb == var) ? node_gethigh(b, nb) : b;

        if (vv == var) {
            /* Recursive, then abstract result */
            mtbdd_refs_spawn(SPAWN(mtbdd_and_exists, ahigh, bhigh, node_gethigh(v, nv)));
            MTBDD low = mtbdd_refs_push(CALL(mtbdd_and_exists, alow, blow, node_gethigh(v, nv)));
            MTBDD high = mtbdd_refs_push(mtbdd_refs_sync(SYNC(mtbdd_and_exists)));
            result = CALL(mtbdd_apply, low, high, TASK(mtbdd_op_plus));
            mtbdd_refs_pop(2);
        } else /* vv > v */ {
            /* Recursive, then create node */
            mtbdd_refs_spawn(SPAWN(mtbdd_and_exists, ahigh, bhigh, v));
            MTBDD low = mtbdd_refs_push(CALL(mtbdd_and_exists, alow, blow, v));
            MTBDD high = mtbdd_refs_sync(SYNC(mtbdd_and_exists));
            mtbdd_refs_pop(1);
            result = mtbdd_makenode(var, low, high);
        }
    }

    /* Store in cache */
    cache_put(a | CACHE_MTBDD_AND_EXISTS, b, v, result);
    return result;
}

/**
 * Calculate the support of a MTBDD, i.e. the cube of all variables that appear in the MTBDD nodes.
 */
TASK_IMPL_1(MTBDD, mtbdd_support, MTBDD, dd)
{
    /* Terminal case */
    if (mtbdd_isleaf(dd)) return mtbdd_true;

    /* Maybe perform garbage collection */
    sylvan_gc_test();

    /* Check cache */
    MTBDD result;
    if (cache_get(dd | CACHE_MTBDD_SUPPORT, 0, 0, &result)) return result;

    /* Recursive calls */
    mtbddnode_t n = GETNODE(dd);
    mtbdd_refs_spawn(SPAWN(mtbdd_support, node_getlow(dd, n)));
    MTBDD high = mtbdd_refs_push(CALL(mtbdd_support, node_gethigh(dd, n)));
    MTBDD low = mtbdd_refs_push(mtbdd_refs_sync(SYNC(mtbdd_support)));

    /* Compute result */
    result = mtbdd_makenode(mtbddnode_getvariable(n), mtbdd_false, mtbdd_times(low, high));
    mtbdd_refs_pop(2);

    /* Write to cache */
    cache_put(dd | CACHE_MTBDD_SUPPORT, 0, 0, result);
    return result;
}

/**
 * Function composition, for each node with variable <key> which has a <key,value> pair in <map>,
 * replace the node by the result of mtbdd_ite(<value>, <low>, <high>).
 * Each <value> in <map> must be a Boolean MTBDD.
 */
TASK_IMPL_2(MTBDD, mtbdd_compose, MTBDD, a, MTBDDMAP, map)
{
    /* Terminal case */
    if (mtbdd_isleaf(a) || mtbdd_map_isempty(map)) return a;

    /* Determine top level */
    mtbddnode_t n = GETNODE(a);
    uint32_t v = mtbddnode_getvariable(n);

    /* Find in map */
    while (mtbdd_map_key(map) < v) {
        map = mtbdd_map_next(map);
        if (mtbdd_map_isempty(map)) return a;
    }

    /* Perhaps execute garbage collection */
    sylvan_gc_test();

    /* Check cache */
    MTBDD result;
    if (cache_get(a | CACHE_MTBDD_COMPOSE, map, 0, &result)) return result;

    /* Recursive calls */
    mtbdd_refs_spawn(SPAWN(mtbdd_compose, node_getlow(a, n), map));
    MTBDD high = mtbdd_refs_push(CALL(mtbdd_compose, node_gethigh(a, n), map));
    MTBDD low = mtbdd_refs_push(mtbdd_refs_sync(SYNC(mtbdd_compose)));

    /* Calculate result */
    MTBDD r = mtbdd_map_key(map) == v ? mtbdd_map_value(map) : mtbdd_makenode(v, mtbdd_false, mtbdd_true);
    mtbdd_refs_push(r);
    result = CALL(mtbdd_ite, r, high, low);
    mtbdd_refs_pop(3);

    /* Store in cache */
    cache_put(a | CACHE_MTBDD_COMPOSE, map, 0, result);
    return result;
}

/**
 * Helper function for recursive unmarking
 */
static void
mtbdd_unmark_rec(MTBDD mtbdd)
{
    mtbddnode_t n = GETNODE(mtbdd);
    if (!mtbddnode_getmark(n)) return;
    mtbddnode_setmark(n, 0);
    if (mtbddnode_isleaf(n)) return;
    mtbdd_unmark_rec(mtbddnode_getlow(n));
    mtbdd_unmark_rec(mtbddnode_gethigh(n));
}

/**
 * Count number of nodes in MTBDD
 */

static size_t
mtbdd_nodecount_mark(MTBDD mtbdd)
{
    if (mtbdd <= mtbdd_true) return 0; // do not count true/false leaf
    mtbddnode_t n = GETNODE(mtbdd);
    if (mtbddnode_getmark(n)) return 0;
    mtbddnode_setmark(n, 1);
    if (mtbddnode_isleaf(n)) return 1; // count leaf as 1
    return 1 + mtbdd_nodecount_mark(mtbddnode_getlow(n)) + mtbdd_nodecount_mark(mtbddnode_gethigh(n));
}

size_t
mtbdd_nodecount(MTBDD mtbdd)
{
    size_t result = mtbdd_nodecount_mark(mtbdd);
    mtbdd_unmark_rec(mtbdd);
    return result;
}

/**
 * Export to .dot file
 */

static void
mtbdd_fprintdot_rec(FILE *out, MTBDD mtbdd, print_terminal_label_cb cb)
{
    mtbddnode_t n = GETNODE(mtbdd); // also works for mtbdd_false
    if (mtbddnode_getmark(n)) return;
    mtbddnode_setmark(n, 1);

    if (mtbdd == mtbdd_true || mtbdd == mtbdd_false) {
        fprintf(out, "0 [shape=box, style=filled, label=\"F\"];\n");
    } else if (mtbddnode_isleaf(n)) {
        uint32_t type = mtbddnode_gettype(n);
        uint64_t value = mtbddnode_getvalue(n);
        fprintf(out, "%" PRIu64 " [shape=box, style=filled, label=\"", MTBDD_STRIPMARK(mtbdd));
        switch (type) {
        case 0:
            fprintf(out, "%" PRIu64, value);
            break;
        case 1:
            fprintf(out, "%f", *(double*)&value);
            break;
        default:
            cb(out, type, value);
            break;
        }
        fprintf(out, "\"];\n");
    } else {
        fprintf(out, "%" PRIu64 " [label=\"%" PRIu32 "\"];\n",
                MTBDD_STRIPMARK(mtbdd), mtbddnode_getvariable(n));

        mtbdd_fprintdot_rec(out, mtbddnode_getlow(n), cb);
        mtbdd_fprintdot_rec(out, mtbddnode_gethigh(n), cb);

        fprintf(out, "%" PRIu64 " -> %" PRIu64 " [style=dashed];\n",
                mtbdd, mtbddnode_getlow(n));
        fprintf(out, "%" PRIu64 " -> %" PRIu64 " [style=solid dir=both arrowtail=%s];\n",
                mtbdd, MTBDD_STRIPMARK(mtbddnode_gethigh(n)),
                mtbddnode_getcomp(n) ? "dot" : "none");
    }
}

void
mtbdd_fprintdot(FILE *out, MTBDD mtbdd, print_terminal_label_cb cb)
{
    fprintf(out, "digraph \"DD\" {\n");
    fprintf(out, "graph [dpi = 300];\n");
    fprintf(out, "center = true;\n");
    fprintf(out, "edge [dir = forward];\n");
    fprintf(out, "root [style=invis];\n");
    fprintf(out, "root -> %" PRIu64 " [style=solid dir=both arrowtail=%s];\n",
            MTBDD_STRIPMARK(mtbdd), MTBDD_HASMARK(mtbdd) ? "dot" : "none");

    mtbdd_fprintdot_rec(out, mtbdd, cb);
    mtbdd_unmark_rec(mtbdd);

    fprintf(out, "}\n");
}

/**
 * Return 1 if the map contains the key, 0 otherwise.
 */
int
mtbdd_map_contains(MTBDDMAP map, uint32_t key)
{
    while (!mtbdd_map_isempty(map)) {
        mtbddnode_t n = GETNODE(map);
        uint32_t k = mtbddnode_getvariable(n);
        if (k == key) return 1;
        if (k > key) return 0;
        map = node_getlow(map, n);
    }

    return 0;
}

/**
 * Retrieve the number of keys in the map.
 */
size_t
mtbdd_map_count(MTBDDMAP map)
{
    size_t r = 0;

    while (!mtbdd_map_isempty(map)) {
        r++;
        map = mtbdd_map_next(map);
    }

    return r;
}

/**
 * Add the pair <key,value> to the map, overwrites if key already in map.
 */
MTBDDMAP
mtbdd_map_add(MTBDDMAP map, uint32_t key, MTBDD value)
{
    if (mtbdd_map_isempty(map)) return mtbdd_makenode(key, mtbdd_map_empty(), value);

    mtbddnode_t n = GETNODE(map);
    uint32_t k = mtbddnode_getvariable(n);

    if (k < key) {
        // add recursively and rebuild tree
        MTBDDMAP low = mtbdd_map_add(node_getlow(map, n), key, value);
        return mtbdd_makenode(k, low, node_gethigh(map, n));
    } else if (k > key) {
        return mtbdd_makenode(key, map, value);
    } else {
        // replace old
        return mtbdd_makenode(key, node_getlow(map, n), value);
    }
}

/**
 * Add all values from map2 to map1, overwrites if key already in map1.
 */
MTBDDMAP
mtbdd_map_addall(MTBDDMAP map1, MTBDDMAP map2)
{
    if (mtbdd_map_isempty(map1)) return map2;
    if (mtbdd_map_isempty(map2)) return map1;

    mtbddnode_t n1 = GETNODE(map1);
    mtbddnode_t n2 = GETNODE(map2);
    uint32_t k1 = mtbddnode_getvariable(n1);
    uint32_t k2 = mtbddnode_getvariable(n2);

    MTBDDMAP result;
    if (k1 < k2) {
        MTBDDMAP low = mtbdd_map_addall(node_getlow(map1, n1), map2);
        result = mtbdd_makenode(k1, low, node_gethigh(map1, n1));
    } else if (k1 > k2) {
        MTBDDMAP low = mtbdd_map_addall(map1, node_getlow(map2, n2));
        result = mtbdd_makenode(k2, low, node_gethigh(map2, n2));
    } else {
        MTBDDMAP low = mtbdd_map_addall(node_getlow(map1, n1), node_getlow(map2, n2));
        result = mtbdd_makenode(k2, low, node_gethigh(map2, n2));
    }

    return result;
}

/**
 * Remove the key <key> from the map and return the result
 */
MTBDDMAP
mtbdd_map_remove(MTBDDMAP map, uint32_t key)
{
    if (mtbdd_map_isempty(map)) return map;

    mtbddnode_t n = GETNODE(map);
    uint32_t k = mtbddnode_getvariable(n);

    if (k < key) {
        MTBDDMAP low = mtbdd_map_remove(node_getlow(map, n), key);
        return mtbdd_makenode(k, low, node_gethigh(map, n));
    } else if (k > key) {
        return map;
    } else {
        return node_getlow(map, n);
    }
}

/**
 * Remove all keys in the cube <variables> from the map and return the result
 */
MTBDDMAP
mtbdd_map_removeall(MTBDDMAP map, MTBDD variables)
{
    if (mtbdd_map_isempty(map)) return map;
    if (variables == mtbdd_true) return map;

    mtbddnode_t n1 = GETNODE(map);
    mtbddnode_t n2 = GETNODE(variables);
    uint32_t k1 = mtbddnode_getvariable(n1);
    uint32_t k2 = mtbddnode_getvariable(n2);

    if (k1 < k2) {
        MTBDDMAP low = mtbdd_map_removeall(node_getlow(map, n1), variables);
        return mtbdd_makenode(k1, low, node_gethigh(map, n1));
    } else if (k1 > k2) {
        return mtbdd_map_removeall(map, node_gethigh(variables, n2));
    } else {
        return mtbdd_map_removeall(node_getlow(map, n1), node_gethigh(variables, n2));
    }
}
