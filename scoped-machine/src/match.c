#define _POSIX_C_SOURCE 200809L
#include "match.h"

Graph *graph_new(void) { Graph *g = calloc(1, sizeof *g); require(g, "out of memory"); return g; }
void graph_free(Graph *g) {
    if (!g) return;
    for (size_t i = 0; i < g->nodes.len; i++) { free(g->nodes.data[i].label); vec_free(&g->nodes.data[i].ordered); vec_free(&g->nodes.data[i].unordered); }
    vec_free(&g->nodes); vec_free(&g->roots); vec_free(&g->setroots);
    free(g);
}
size_t graph_node(Graph *g, int kind, const char *label) {
    GNode n; memset(&n, 0, sizeof n); n.kind = kind; n.label = strdup(label); require(n.label, "out of memory");
    vec_push(&g->nodes, n);
    return g->nodes.len - 1;
}
void graph_ordered(Graph *g, size_t p, size_t c) { vec_push(&g->nodes.data[p].ordered, c); }
void graph_unordered(Graph *g, size_t p, size_t c) { vec_push(&g->nodes.data[p].unordered, c); }
void graph_root(Graph *g, size_t n) { vec_push(&g->roots, n); }
void graph_setroot(Graph *g, size_t n) { vec_push(&g->setroots, n); }

/* ---- joint refinement on the disjoint union (candidate classes only) ---- */

typedef struct { const Graph *a, *b; size_t na; size_t *cls; } Joint;
static const GNode *jnode(const Joint *j, size_t v) { return v < j->na ? &j->a->nodes.data[v] : &j->b->nodes.data[v - j->na]; }
static size_t jchild(const Joint *j, size_t v, size_t c) { return v < j->na ? c : c + j->na; }

typedef struct { size_t node; Words sig; } Sig;
static int cmp_sig(const void *x, const void *y) {
    const Sig *p = x, *q = y;
    size_t n = p->sig.n < q->sig.n ? p->sig.n : q->sig.n;
    for (size_t i = 0; i < n; i++) if (p->sig.w[i] != q->sig.w[i]) return p->sig.w[i] < q->sig.w[i] ? -1 : 1;
    if (p->sig.n != q->sig.n) return p->sig.n < q->sig.n ? -1 : 1;
    return 0;
}
static const Joint *sort_ctx;
static int cmp_label(const void *x, const void *y) {
    size_t p = *(const size_t *)x, q = *(const size_t *)y;
    const GNode *np = jnode(sort_ctx, p), *nq = jnode(sort_ctx, q);
    if (np->kind != nq->kind) return np->kind < nq->kind ? -1 : 1;
    return strcmp(np->label, nq->label);
}
static int label_eq(const GNode *x, const GNode *y) { return x->kind == y->kind && strcmp(x->label, y->label) == 0; }

static size_t refine(Joint *j) {
    size_t n = j->na + j->b->nodes.len;
    j->cls = calloc(n ? n : 1, sizeof(size_t));
    size_t *order = malloc((n ? n : 1) * sizeof(size_t));
    for (size_t i = 0; i < n; i++) order[i] = i;
    sort_ctx = j;
    qsort(order, n, sizeof(size_t), cmp_label);
    size_t ncls = 0;
    for (size_t i = 0; i < n; i++) {
        if (i > 0 && !label_eq(jnode(j, order[i]), jnode(j, order[i - 1]))) ncls++;
        j->cls[order[i]] = ncls + 1;
    }
    ncls = n ? ncls + 1 : 0;
    free(order);
    Sig *sigs = malloc((n ? n : 1) * sizeof(Sig));
    for (size_t round = 0; round < n + 2; round++) {
        for (size_t v = 0; v < n; v++) {
            const GNode *g = jnode(j, v);
            sigs[v].node = v; words_init(&sigs[v].sig);
            words_push(&sigs[v].sig, j->cls[v]);
            words_push(&sigs[v].sig, g->ordered.len);
            for (size_t k = 0; k < g->ordered.len; k++) words_push(&sigs[v].sig, j->cls[jchild(j, v, g->ordered.data[k])]);
            size_t base = sigs[v].sig.n;
            for (size_t k = 0; k < g->unordered.len; k++) words_push(&sigs[v].sig, j->cls[jchild(j, v, g->unordered.data[k])]);
            qsort(sigs[v].sig.w + base, g->unordered.len, sizeof(uint64_t), cmp_u64);
        }
        qsort(sigs, n, sizeof(Sig), cmp_sig);
        size_t k = 0;
        for (size_t i = 0; i < n; i++) { if (i > 0 && cmp_sig(&sigs[i], &sigs[i - 1]) != 0) k++; j->cls[sigs[i].node] = k + 1; }
        for (size_t v = 0; v < n; v++) words_free(&sigs[v].sig);
        size_t newn = n ? k + 1 : 0;
        if (newn == ncls) break;
        ncls = newn;
    }
    free(sigs);
    return ncls;
}

/* ---- exact matching with backtracking ----
 *
 * A complete depth-first search over bijections. The agenda holds pending
 * obligations: PAIR(l,r) "l must map to r", and SET "match the remaining
 * left elements of an unordered collection into the unused right elements".
 * Every choice made for a SET is a backtrack point for the whole remaining
 * agenda, so an inner choice is revisited when a later obligation
 * contradicts it. The joint refinement classes only filter candidates. */

typedef struct { int kind; size_t l, r; const size_t *L, *R; size_t n; bool *used; size_t i; } Item;   /* kind 0 PAIR, 1 SET */
typedef VEC(Item) Agenda;

typedef struct {
    const Graph *a, *b;
    const Joint *j;
    size_t *map;              /* a-node → b-node + 1 (0 = unmapped) */
    size_t *pre;              /* b-node → a-node + 1 */
    VEC(size_t) trail;        /* a-nodes assigned, for undo */
    VEC(bool *) pools;        /* used-flag arrays to free at the end */
    MatchReport *rep;
} Matcher;

static void undo_to(Matcher *m, size_t mark) {
    while (m->trail.len > mark) {
        size_t l = m->trail.data[--m->trail.len];
        size_t r = m->map[l] - 1;
        m->map[l] = 0; m->pre[r] = 0;
    }
}

static void fail_reason(Matcher *m, const char *what, size_t l, size_t r) {
    snprintf(m->rep->reason, sizeof m->rep->reason, "%s: left [%s] vs right [%s]", what, m->a->nodes.data[l].label, r < m->b->nodes.len ? m->b->nodes.data[r].label : "-");
}

static bool *new_used(Matcher *m, size_t n) { bool *u = calloc(n ? n : 1, sizeof(bool)); require(u, "out of memory"); vec_push(&m->pools, u); return u; }

/* map l to r if admissible, pushing the children obligations */
static bool unify(Matcher *m, size_t l, size_t r, Agenda *ag) {
    if (m->map[l]) { if (m->map[l] - 1 != r) { fail_reason(m, "sharing: left node already mapped elsewhere", l, r); return false; } return true; }
    if (m->pre[r]) { fail_reason(m, "sharing: right node already has a different preimage", l, r); return false; }
    const GNode *x = &m->a->nodes.data[l], *y = &m->b->nodes.data[r];
    if (!label_eq(x, y)) { fail_reason(m, "kind/label", l, r); return false; }
    if (x->ordered.len != y->ordered.len || x->unordered.len != y->unordered.len) { fail_reason(m, "arity", l, r); return false; }
    if (m->j->cls[l] != m->j->cls[r + m->j->na]) { fail_reason(m, "refinement class", l, r); return false; }
    m->map[l] = r + 1; m->pre[r] = l + 1; vec_push(&m->trail, l);
    if (x->unordered.len) {
        Item it = { 1, 0, 0, x->unordered.data, y->unordered.data, x->unordered.len, new_used(m, x->unordered.len), 0 };
        vec_push(ag, it);
    }
    for (size_t k = x->ordered.len; k-- > 0;) { Item it = { 0, x->ordered.data[k], y->ordered.data[k], NULL, NULL, 0, NULL, 0 }; vec_push(ag, it); }
    return true;
}

static bool solve(Matcher *m, Agenda *ag) {
    if (ag->len == 0) return true;
    Item it = ag->data[--ag->len];
    size_t agmark = ag->len, mark = m->trail.len;
    if (it.kind == 0) {
        if (unify(m, it.l, it.r, ag) && solve(m, ag)) return true;
        undo_to(m, mark); ag->len = agmark; vec_push(ag, it);
        return false;
    }
    if (it.i == it.n) { if (solve(m, ag)) return true; ag->len = agmark; vec_push(ag, it); return false; }
    size_t left = it.L[it.i];
    for (size_t k = 0; k < it.n; k++) {
        if (it.used[k]) continue;
        size_t right = it.R[k];
        if (m->j->cls[left] != m->j->cls[right + m->j->na]) continue;
        if (m->map[left] && m->map[left] - 1 != right) continue;
        if (m->pre[right] && m->pre[right] - 1 != left) continue;
        it.used[k] = true;
        Item rest = it; rest.i = it.i + 1;
        vec_push(ag, rest);
        Item pair = { 0, left, right, NULL, NULL, 0, NULL, 0 };
        vec_push(ag, pair);
        if (solve(m, ag)) return true;
        undo_to(m, mark); ag->len = agmark;
        it.used[k] = false;
        m->rep->backtracks++;
    }
    if (!m->rep->reason[0]) fail_reason(m, "no admissible partner in an unordered collection", left, (size_t)-1);
    vec_push(ag, it);
    return false;
}

bool graph_match(const Graph *a, const Graph *b, MatchReport *rep) {
    memset(rep, 0, sizeof *rep);
    if (a->roots.len != b->roots.len || a->setroots.len != b->setroots.len) { snprintf(rep->reason, sizeof rep->reason, "different number of roots"); return false; }
    Joint j; j.a = a; j.b = b; j.na = a->nodes.len; j.cls = NULL;
    rep->classes_joint = refine(&j);
    Matcher m; memset(&m, 0, sizeof m);
    m.a = a; m.b = b; m.j = &j; m.rep = rep;
    m.map = calloc(a->nodes.len ? a->nodes.len : 1, sizeof(size_t));
    m.pre = calloc(b->nodes.len ? b->nodes.len : 1, sizeof(size_t));
    Agenda ag = {0};
    if (a->setroots.len) { Item it = { 1, 0, 0, a->setroots.data, b->setroots.data, a->setroots.len, new_used(&m, a->setroots.len), 0 }; vec_push(&ag, it); }
    for (size_t i = a->roots.len; i-- > 0;) { Item it = { 0, a->roots.data[i], b->roots.data[i], NULL, NULL, 0, NULL, 0 }; vec_push(&ag, it); }
    bool ok = solve(&m, &ag);
    rep->equal = ok;
    if (ok) rep->reason[0] = 0;
    for (size_t i = 0; i < m.pools.len; i++) free(m.pools.data[i]);
    vec_free(&m.pools); vec_free(&ag);
    free(m.map); free(m.pre); vec_free(&m.trail); free(j.cls);
    return ok;
}
