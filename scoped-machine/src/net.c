/* net.c — cells, wiring, the interaction rules, and building a net from
 * compiled syntax. */
#include "core.h"
#include <string.h>

long stat_steps, stat_kind[K_END], stat_cells;

Cell *cell(int kind, int n) {
    Cell *c = calloc(1, sizeof(Cell) + (size_t)n * sizeof(Port));
    if (!c) { fputs("out of memory\n", stderr); exit(2); }
    c->kind = (uint16_t)kind; c->n = (uint16_t)n;
    stat_cells++;
    return c;
}
void cell_free(Cell *c) { stat_cells--; free(c); }
static Cell *clone(const Cell *v) { Cell *c = cell(v->kind, v->n); c->x = v->x; c->a = v->a; c->p = v->p; return c; }

/* ---------------- active pairs ---------------- */
typedef struct { Cell *op, *v; } Redex;
static Redex *rq; static size_t rq_head, rq_len, rq_cap;
void net_push(Cell *op, Cell *v) {
    if (rq_len == rq_cap) {
        if (rq_head > 0) { memmove(rq, rq + rq_head, (rq_len - rq_head) * sizeof(Redex)); rq_len -= rq_head; rq_head = 0; }
        if (rq_len == rq_cap) { rq_cap = rq_cap ? rq_cap * 2 : 1024; rq = realloc(rq, rq_cap * sizeof(Redex)); }
    }
    rq[rq_len++] = (Redex){ op, v };
}
void link(Port a, Port b) {
    if (a) PC(a)->port[PI(a)] = b;
    if (b) PC(b)->port[PI(b)] = a;
    if (a && b && PI(a) == 0 && PI(b) == 0) {
        Cell *x = PC(a), *y = PC(b);
        if (is_value(x->kind) && !is_value(y->kind)) { if (y->kind != O_ROOT) net_push(y, x); }
        else if (is_value(y->kind) && !is_value(x->kind)) { if (x->kind != O_ROOT) net_push(x, y); }
    }
}
/* move whatever is wired to c's port k onto port `to` */
static void mv(Cell *c, int k, Port to) { link(c->port[k], to); }
static Port out_of(Cell *o) { return o->port[o->n - 1]; }

/* ---------------- small constructors ---------------- */
static void era(Port prov) { Cell *e = cell(O_ERA, 1); link(prov, P(e, 0)); }
static Port sub(Port prov, Subst *s) { Cell *c = cell(O_SUBST, 2); c->p = s; link(prov, P(c, 0)); return P(c, 1); }
static Port mkplam_of(Port prov, Dim i) { Cell *m = cell(O_MKPLAM, 2); m->a = i; link(prov, P(m, 0)); return P(m, 1); }
static Port iv_cell(Dnf *r) { Cell *c = cell(V_IV, 1); c->p = r; return P(c, 0); }
/* m providers sharing one value (a chain of duplicators) */
static void split(Port prov, int m, Port *out) {
    if (m == 0) { era(prov); return; }
    for (int k = 0; k < m - 1; k++) { Cell *d = cell(O_DUP, 3); link(prov, P(d, 0)); out[k] = P(d, 1); prov = P(d, 2); }
    out[m - 1] = prov;
}
static void split_restrict(Port prov, Clause **cl, int m, Port *out) {
    split(prov, m, out);
    for (int k = 0; k < m; k++) out[k] = sub(out[k], subst_of_clause(cl[k]));
}
static Port apply_global(const char *name, Port *args, int n) {
    long g = global_lookup(name);
    if (g < 0) { fprintf(stderr, "missing library definition %s\n", name); exit(2); }
    Cell *gc = cell(V_GLOBAL, 1); gc->a = (uint64_t)g;
    Port f = P(gc, 0);
    for (int k = 0; k < n; k++) { Cell *a = cell(O_APP, 3); link(f, P(a, 0)); link(args[k], P(a, 1)); f = P(a, 2); }
    return f;
}

/* ---------------- structural rules ---------------- */
static void rule_dup(Cell *o, Cell *v) {
    Port o1 = o->port[1], o2 = o->port[2];
    Cell *c1 = clone(v), *c2 = clone(v);
    for (int k = 1; k < v->n; k++) {
        Cell *d = cell(O_DUP, 3);
        link(v->port[k], P(d, 0)); link(P(d, 1), P(c1, k)); link(P(d, 2), P(c2, k));
    }
    link(P(c1, 0), o1); link(P(c2, 0), o2);
    cell_free(o); cell_free(v);
}
static void rule_era(Cell *o, Cell *v) {
    for (int k = 1; k < v->n; k++) era(v->port[k]);
    cell_free(o); cell_free(v);
}

/* substitution of dimensions */
static void rule_subst(Cell *o, Cell *v) {
    Subst *s = o->p;
    Port out = o->port[1];
    switch (v->kind) {
    case V_NVAR: case V_GLOBAL: case V_U:
        link(P(v, 0), out); cell_free(o); return;
    case V_IV: v->p = iv_subst(v->p, s); link(P(v, 0), out); cell_free(o); return;
    case V_FACE: v->p = face_subst(v->p, s); link(P(v, 0), out); cell_free(o); return;
    case V_PLAM: {
        Dim j = (Dim)v->a, j2 = j;
        Subst *t = subst_without(s, j);
        if (subst_range_mentions(t, j)) { j2 = fresh_dim(); t = subst_with(t, j, iv_atom(j2)); }
        link(mkplam_of(sub(v->port[1], t), j2), out);
        cell_free(o); cell_free(v); return;
    }
    case V_SYS: {
        int nb = v->n - 1;
        Clause **cl = v->p;
        Dnf **f = malloc((size_t)(nb + 1) * sizeof(Dnf *));
        int total = 0;
        for (int k = 0; k < nb; k++) { f[k] = face_subst(face_of_clause(cl[k]), s); total += (int)f[k]->n; }
        for (int k = 0; k < nb; k++) if (dnf_is_one(f[k])) {
            /* the substitution entails this branch's clause: the system is that value */
            link(sub(v->port[k + 1], s), out);
            for (int m = 0; m < nb; m++) if (m != k) era(v->port[m + 1]);
            free(f); cell_free(o); cell_free(v); return;
        }
        Cell *ns = cell(V_SYS, total + 1);
        Clause **ncl = malloc((size_t)(total + 1) * sizeof(Clause *));
        ns->p = ncl;
        int idx = 0;
        for (int k = 0; k < nb; k++) {
            int m = (int)f[k]->n;
            Port *cp = malloc((size_t)(m + 1) * sizeof(Port));
            split(v->port[k + 1], m, cp);
            for (int q = 0; q < m; q++) {
                ncl[idx] = f[k]->c[q];
                link(sub(cp[q], subst_then_clause(s, f[k]->c[q])), P(ns, idx + 1));
                idx++;
            }
            free(cp);
        }
        link(P(ns, 0), out);
        free(f); cell_free(o); cell_free(v); return;
    }
    /* neutrals and reducible constructors become their operations again */
    case V_NAPP: { Cell *a = cell(O_APP, 3); link(sub(v->port[1], s), P(a, 0)); link(sub(v->port[2], s), P(a, 1)); link(P(a, 2), out); break; }
    case V_NFST: case V_NSND: { Cell *a = cell(v->kind == V_NFST ? O_FST : O_SND, 2); link(sub(v->port[1], s), P(a, 0)); link(P(a, 1), out); break; }
    case V_NPAPP: {
        Cell *a = cell(O_PAPPR, v->x ? 5 : 3); a->x = v->x;
        link(iv_cell(iv_subst(v->p, s)), P(a, 0));
        link(sub(v->port[1], s), P(a, 1));
        if (v->x) { link(sub(v->port[2], s), P(a, 2)); link(sub(v->port[3], s), P(a, 3)); }
        link(P(a, a->n - 1), out);
        break;
    }
    case V_NCOMP: { Cell *a = cell(O_COMP, 4); link(sub(v->port[2], s), P(a, 0)); link(sub(v->port[1], s), P(a, 1)); link(sub(v->port[3], s), P(a, 2)); link(P(a, 3), out); break; }
    case V_NUNGLUE: { Cell *a = cell(O_UNGLUE, 3); link(sub(v->port[1], s), P(a, 0)); link(sub(v->port[2], s), P(a, 1)); link(P(a, 2), out); break; }
    case V_GLUE: { Cell *a = cell(O_MKGLUE, 3); link(sub(v->port[2], s), P(a, 0)); link(sub(v->port[1], s), P(a, 1)); link(P(a, 2), out); break; }
    case V_GLUEV: { Cell *a = cell(O_MKGLUEV, 3); link(sub(v->port[1], s), P(a, 0)); link(sub(v->port[2], s), P(a, 1)); link(P(a, 2), out); break; }
    default: {
        /* constructors: λ (its environment), pair, Π, Σ, PathP */
        Cell *c = clone(v);
        for (int k = 1; k < v->n; k++) link(sub(v->port[k], s), P(c, k));
        link(P(c, 0), out);
        break;
    }
    }
    cell_free(o); cell_free(v);
}

/* a value is put under a dimension binder; a system whose clauses avoid the
 * dimension is a system of lines */
static void rule_mkplam(Cell *o, Cell *v) {
    Dim i = (Dim)o->a;
    Port out = o->port[1];
    if (v->kind == V_SYS) {
        Clause **cl = v->p;
        int nb = v->n - 1;
        bool avoid = true;
        for (int k = 0; k < nb; k++) if (clause_mentions(cl[k], i)) avoid = false;
        if (avoid) {
            Cell *ns = cell(V_SYS, nb + 1); ns->p = cl;
            for (int k = 0; k < nb; k++) link(mkplam_of(v->port[k + 1], i), P(ns, k + 1));
            link(P(ns, 0), out);
            cell_free(o); cell_free(v); return;
        }
    }
    Cell *pl = cell(V_PLAM, 2); pl->a = i;
    link(P(v, 0), P(pl, 1));
    link(P(pl, 0), out);
    cell_free(o);
}

/* an eliminator meets a system: it acts branchwise, every other operand
 * restricted to the branch's clause */
static void distribute(Cell *o, Cell *v) {
    int nb = v->n - 1;
    Clause **cl = v->p;
    Cell *ns = cell(V_SYS, nb + 1); ns->p = cl;
    Port ex[2] = { 0, 0 }; int ne = 0;
    switch (o->kind) {
    case O_APP: case O_UNGLUE2: case O_SYSMAP: ex[ne++] = o->port[1]; break;
    case O_PAPPP: if (o->x) { ex[ne++] = o->port[1]; ex[ne++] = o->port[2]; } break;
    case O_COMPA: ex[ne++] = o->port[1]; ex[ne++] = o->port[2]; break;
    default: break;
    }
    Port out = out_of(o);
    Port *cp[2];
    for (int e = 0; e < ne; e++) { cp[e] = malloc((size_t)(nb + 1) * sizeof(Port)); split_restrict(ex[e], cl, nb, cp[e]); }
    for (int b = 0; b < nb; b++) {
        Port val = v->port[b + 1], res = P(ns, b + 1);
        Cell *c;
        switch (o->kind) {
        case O_APP: c = cell(O_APP, 3); link(val, P(c, 0)); link(cp[0][b], P(c, 1)); link(P(c, 2), res); break;
        case O_SYSMAP: c = cell(O_APP, 3); link(cp[0][b], P(c, 0)); link(val, P(c, 1)); link(P(c, 2), res); break;
        case O_FST: case O_SND: case O_FORCE: c = cell(o->kind, 2); link(val, P(c, 0)); link(P(c, 1), res); break;
        case O_FACEOF: c = cell(O_FACEOF, 2); link(val, P(c, 0)); link(P(c, 1), res); break;
        case O_PAPPP:
            c = cell(O_PAPPR, o->x ? 5 : 3); c->x = o->x;
            link(iv_cell(iv_subst(o->p, subst_of_clause(cl[b]))), P(c, 0));
            link(val, P(c, 1));
            if (o->x) { link(cp[0][b], P(c, 2)); link(cp[1][b], P(c, 3)); }
            link(P(c, c->n - 1), res);
            break;
        case O_UNGLUE2: c = cell(O_UNGLUE, 3); link(cp[0][b], P(c, 0)); link(val, P(c, 1)); link(P(c, 2), res); break;
        case O_COMPA: c = cell(O_COMP, 4); link(cp[0][b], P(c, 0)); link(val, P(c, 1)); link(cp[1][b], P(c, 2)); link(P(c, 3), res); break;
        default: fprintf(stderr, "distribute: kind %d\n", o->kind); exit(2);
        }
    }
    for (int e = 0; e < ne; e++) free(cp[e]);
    link(P(ns, 0), out);
    cell_free(o); cell_free(v);
}

/* a stuck elimination is a neutral value retaining every operand */
static void neutral1(Cell *o, Cell *v, int kind) {
    Cell *n = cell(kind, 2);
    link(P(v, 0), P(n, 1));
    link(P(n, 0), out_of(o));
    cell_free(o);
}

/* ---------------- the rules ---------------- */
static void interact(Cell *o, Cell *v) {
    stat_steps++; stat_kind[o->kind]++;
    switch (o->kind) {
    case O_ERA: rule_era(o, v); return;
    case O_DUP: rule_dup(o, v); return;
    case O_SUBST: rule_subst(o, v); return;
    case O_MKPLAM: rule_mkplam(o, v); return;
    default: break;
    }
    if (v->kind == V_GLOBAL) {
        /* a definition is used: its value is copied in */
        Port r = global_copy((long)v->a);
        if (!r) { global_park((long)v->a, o, v); return; }
        link(r, P(o, 0));
        cell_free(v);
        return;
    }
    int vk = v->kind;
    switch (o->kind) {
    case O_APP:
        if (vk == V_LAM && ((Record *)v->p)->nparam == 1) {
            Port r = record_build(v->p, o->port[1], &v->port[1]);
            link(r, o->port[2]);
            cell_free(o); cell_free(v);
        } else if (vk == V_SYS) distribute(o, v);
        else { Cell *n = cell(V_NAPP, 3); link(P(v, 0), P(n, 1)); mv(o, 1, P(n, 2)); link(P(n, 0), o->port[2]); cell_free(o); }
        return;
    case O_FORCE:
        if (vk == V_LAM && ((Record *)v->p)->nparam == 0) {
            link(record_build(v->p, 0, &v->port[1]), o->port[1]);
            cell_free(o); cell_free(v);
        } else if (vk == V_SYS) distribute(o, v);
        else { link(P(v, 0), o->port[1]); cell_free(o); }
        return;
    case O_FST: case O_SND:
        if (vk == V_PAIR) {
            int keep = o->kind == O_FST ? 1 : 2;
            link(v->port[keep], o->port[1]); era(v->port[3 - keep]);
            cell_free(o); cell_free(v);
        } else if (vk == V_SYS) distribute(o, v);
        else neutral1(o, v, o->kind == O_FST ? V_NFST : V_NSND);
        return;
    case O_PAPPR: {
        if (vk != V_IV) { fprintf(stderr, "path applied to a non-interval\n"); exit(2); }
        Dnf *r = v->p;
        if (o->x && (dnf_is_zero(r) || dnf_is_one(r))) {
            /* an endpoint: answered without the path */
            int z = dnf_is_zero(r);
            link(o->port[z ? 2 : 3], o->port[4]);
            era(o->port[1]); era(o->port[z ? 3 : 2]);
        } else {
            Cell *pp = cell(O_PAPPP, o->x ? 4 : 2); pp->x = o->x; pp->p = r;
            mv(o, 1, P(pp, 0));
            if (o->x) { mv(o, 2, P(pp, 1)); mv(o, 3, P(pp, 2)); }
            link(P(pp, pp->n - 1), out_of(o));
        }
        cell_free(o); cell_free(v);
        return;
    }
    case O_PAPPP:
        if (vk == V_PLAM) {
            link(sub(v->port[1], subst_single((Dim)v->a, o->p)), out_of(o));
            if (o->x) { era(o->port[1]); era(o->port[2]); }
            cell_free(o); cell_free(v);
        } else if (vk == V_SYS) distribute(o, v);
        else {
            Cell *n = cell(V_NPAPP, o->x ? 4 : 2); n->x = o->x; n->p = o->p;
            link(P(v, 0), P(n, 1));
            if (o->x) { mv(o, 1, P(n, 2)); mv(o, 2, P(n, 3)); }
            link(P(n, 0), out_of(o));
            cell_free(o);
        }
        return;
    case O_COMP:
        if (vk == V_SYS) {
            /* the tube is partial: look at the family */
            Cell *ca = cell(O_COMPA, 4);
            mv(o, 1, P(ca, 0)); link(P(v, 0), P(ca, 1)); mv(o, 2, P(ca, 2)); link(P(ca, 3), o->port[3]);
        } else {
            /* the tube covers: its end */
            Cell *pr = cell(O_PAPPR, 3);
            link(iv_cell(dnf_one()), P(pr, 0)); link(P(v, 0), P(pr, 1)); link(P(pr, 2), o->port[3]);
            era(o->port[1]); era(o->port[2]);
        }
        cell_free(o);
        return;
    case O_COMPA:
        if (vk == V_PLAM) {
            /* the family at its own fresh dimension; its head decides */
            Cell *ch = cell(O_COMPH, 4); ch->a = v->a;
            link(v->port[1], P(ch, 0)); mv(o, 1, P(ch, 1)); mv(o, 2, P(ch, 2)); link(P(ch, 3), o->port[3]);
            cell_free(o); cell_free(v);
        } else if (vk == V_SYS) distribute(o, v);
        else {
            Cell *n = cell(V_NCOMP, 4);
            link(P(v, 0), P(n, 1)); mv(o, 1, P(n, 2)); mv(o, 2, P(n, 3)); link(P(n, 0), o->port[3]);
            cell_free(o);
        }
        return;
    case O_COMPH: {
        Dim i = (Dim)o->a;
        Port u = o->port[1], a0 = o->port[2], out = o->port[3];
        Port args[5];
        const char *clause = NULL; int n = 0;
        switch (vk) {
        case V_PI: case V_SIGMA:
            args[0] = mkplam_of(v->port[1], i); args[1] = mkplam_of(v->port[2], i); args[2] = u; args[3] = a0; n = 4;
            clause = vk == V_PI ? "%comp-pi" : "%comp-sigma"; break;
        case V_PATHP:
            args[0] = mkplam_of(v->port[1], i); args[1] = mkplam_of(v->port[2], i); args[2] = mkplam_of(v->port[3], i);
            args[3] = u; args[4] = a0; n = 5; clause = "%comp-path"; break;
        case V_U: args[0] = u; args[1] = a0; n = 2; clause = "%comp-u"; break;
        case V_GLUE:
            args[0] = mkplam_of(v->port[1], i); args[1] = mkplam_of(v->port[2], i); args[2] = u; args[3] = a0; n = 4;
            clause = "%comp-glue"; break;
        case V_SYS: {
            /* a system of families: each branch whose clause holds along the
             * whole line, ∀i, composes in its own family */
            int nb = v->n - 1; Clause **cl = v->p;
            int keep = 0;
            for (int k = 0; k < nb; k++) if (!clause_mentions(cl[k], i)) keep++;
            Cell *ns = cell(V_SYS, keep + 1);
            Clause **ncl = malloc((size_t)(keep + 1) * sizeof(Clause *)); ns->p = ncl;
            Port *uc = malloc((size_t)(keep + 1) * sizeof(Port)), *ac = malloc((size_t)(keep + 1) * sizeof(Port));
            int q = 0;
            for (int k = 0; k < nb; k++) if (!clause_mentions(cl[k], i)) ncl[q++] = cl[k];
            split_restrict(u, ncl, keep, uc); split_restrict(a0, ncl, keep, ac);
            q = 0;
            for (int k = 0; k < nb; k++) {
                if (clause_mentions(cl[k], i)) { era(v->port[k + 1]); continue; }
                Cell *c = cell(O_COMP, 4);
                link(uc[q], P(c, 0)); link(mkplam_of(v->port[k + 1], i), P(c, 1)); link(ac[q], P(c, 2)); link(P(c, 3), P(ns, q + 1));
                q++;
            }
            free(uc); free(ac);
            link(P(ns, 0), out);
            cell_free(o); cell_free(v);
            return;
        }
        default: {
            Cell *nc = cell(V_NCOMP, 4);
            link(mkplam_of(P(v, 0), i), P(nc, 1)); link(u, P(nc, 2)); link(a0, P(nc, 3)); link(P(nc, 0), out);
            cell_free(o);
            return;
        }
        }
        link(apply_global(clause, args, n), out);
        cell_free(o); cell_free(v);
        return;
    }
    case O_MKGLUE:
        if (vk == V_SYS) { Cell *g = cell(V_GLUE, 3); mv(o, 1, P(g, 1)); link(P(v, 0), P(g, 2)); link(P(g, 0), o->port[2]); }
        else { Cell *f = cell(O_FST, 2); link(P(v, 0), P(f, 0)); link(P(f, 1), o->port[2]); era(o->port[1]); }
        cell_free(o);
        return;
    case O_MKGLUEV:
        if (vk == V_SYS) { Cell *g = cell(V_GLUEV, 3); link(P(v, 0), P(g, 1)); mv(o, 1, P(g, 2)); link(P(g, 0), o->port[2]); }
        else { link(P(v, 0), o->port[2]); era(o->port[1]); }
        cell_free(o);
        return;
    case O_UNGLUE:
        if (vk == V_SYS) {
            Cell *u2 = cell(O_UNGLUE2, 3);
            mv(o, 1, P(u2, 0)); link(P(v, 0), P(u2, 1)); link(P(u2, 2), o->port[2]);
        } else {
            /* on the face: the equivalence's map */
            Cell *sn = cell(O_SND, 2), *f = cell(O_FST, 2), *a = cell(O_APP, 3);
            link(P(v, 0), P(sn, 0)); link(P(sn, 1), P(f, 0)); link(P(f, 1), P(a, 0)); mv(o, 1, P(a, 1)); link(P(a, 2), o->port[2]);
        }
        cell_free(o);
        return;
    case O_UNGLUE2:
        if (vk == V_GLUEV) {
            link(v->port[2], o->port[2]); era(v->port[1]); era(o->port[1]);
            cell_free(o); cell_free(v);
        } else if (vk == V_SYS) distribute(o, v);
        else {
            Cell *n = cell(V_NUNGLUE, 3);
            mv(o, 1, P(n, 1)); link(P(v, 0), P(n, 2)); link(P(n, 0), o->port[2]);
            cell_free(o);
        }
        return;
    case O_FACEOF: {
        Cell *f = cell(V_FACE, 1);
        if (vk == V_SYS) {
            f->p = face_of_clauses((Clause **)v->p, (uint32_t)(v->n - 1));
            for (int k = 1; k < v->n; k++) era(v->port[k]);
            cell_free(v);
        } else { f->p = dnf_one(); era(P(v, 0)); }
        link(P(f, 0), o->port[1]);
        cell_free(o);
        return;
    }
    case O_NEG:
        if (vk != V_IV) { fprintf(stderr, "~ of a non-interval\n"); exit(2); }
        v->p = iv_neg(v->p); link(P(v, 0), o->port[1]); cell_free(o);
        return;
    case O_BIN: {
        if (vk != V_IV && vk != V_FACE) { fprintf(stderr, "lattice operation on a non-interval\n"); exit(2); }
        Cell *b = cell(O_BIN2, 2); b->x = o->x; b->p = v->p;
        mv(o, 1, P(b, 0)); link(P(b, 1), o->port[2]);
        cell_free(o); cell_free(v);
        return;
    }
    case O_BIN2: {
        bool face = o->x == B_FAND || o->x == B_FOR;
        if (vk != (face ? V_FACE : V_IV)) { fprintf(stderr, "lattice operation on mismatched operands\n"); exit(2); }
        v->p = (o->x == B_MEET || o->x == B_FAND) ? dnf_meet(o->p, v->p, face) : dnf_join(o->p, v->p, face);
        link(P(v, 0), o->port[1]); cell_free(o);
        return;
    }
    case O_FEQ: {
        if (vk != V_IV) { fprintf(stderr, "(= r e) of a non-interval\n"); exit(2); }
        Cell *f = cell(V_FACE, 1); f->p = face_eq(v->p, (int)o->a);
        link(P(f, 0), o->port[1]); cell_free(o); cell_free(v);
        return;
    }
    case O_FORALL:
        if (vk != V_FACE) { fprintf(stderr, "forall of a non-face\n"); exit(2); }
        v->p = face_forall(v->p, (Dim)o->a); link(P(v, 0), o->port[1]); cell_free(o);
        return;
    case O_SYSCONS: {
        if (vk != V_FACE) { fprintf(stderr, "system branch guarded by a non-face\n"); exit(2); }
        Dnf *f = v->p;
        if (dnf_is_one(f)) {
            Cell *fo = cell(O_FORCE, 2); mv(o, 1, P(fo, 0)); link(P(fo, 1), o->port[3]); era(o->port[2]);
        } else if (dnf_is_zero(f)) {
            link(o->port[2], o->port[3]); era(o->port[1]);
        } else {
            Cell *s2 = cell(O_SYSCONS2, 3); s2->p = f;
            mv(o, 2, P(s2, 0)); mv(o, 1, P(s2, 1)); link(P(s2, 2), o->port[3]);
        }
        cell_free(o); cell_free(v);
        return;
    }
    case O_SYSCONS2:
        if (vk == V_SYS) {
            /* the branch, forced under each clause of its face, joins the system */
            Dnf *f = o->p;
            int nb = v->n - 1, m = (int)f->n;
            Cell *ns = cell(V_SYS, nb + m + 1);
            Clause **ncl = malloc((size_t)(nb + m + 1) * sizeof(Clause *)); ns->p = ncl;
            Clause **cl = v->p;
            for (int k = 0; k < nb; k++) { ncl[k] = cl[k]; mv(v, k + 1, P(ns, k + 1)); }
            Port *cp = malloc((size_t)(m + 1) * sizeof(Port));
            split_restrict(o->port[1], f->c, m, cp);
            for (int q = 0; q < m; q++) {
                ncl[nb + q] = f->c[q];
                Cell *fo = cell(O_FORCE, 2); link(cp[q], P(fo, 0)); link(P(fo, 1), P(ns, nb + q + 1));
            }
            free(cp);
            link(P(ns, 0), o->port[2]);
            cell_free(o); cell_free(v);
        } else {
            /* the rest is total */
            link(P(v, 0), o->port[2]); era(o->port[1]);
            cell_free(o);
        }
        return;
    case O_SYSMAP:
        if (vk == V_SYS) distribute(o, v);
        else { Cell *a = cell(O_APP, 3); mv(o, 1, P(a, 0)); link(P(v, 0), P(a, 1)); link(P(a, 2), o->port[2]); cell_free(o); }
        return;
    default:
        fprintf(stderr, "no rule for operation %d\n", o->kind); exit(2);
    }
}

long net_run(long limit) {
    long n = 0;
    while (rq_head < rq_len && (limit < 0 || n < limit)) {
        Redex r = rq[rq_head++];
        if (rq_head == rq_len) rq_head = rq_len = 0;
        interact(r.op, r.v);
        n++;
    }
    return n;
}
/* an observation: reduce (fairly, in arrival order) until the observed port
 * holds a value; the rest of the net is left as it stands */
bool net_observe(Cell *root, long limit) {
    long n = 0;
    for (;;) {
        Port q = root->port[0];
        if (q && PI(q) == 0 && is_value(PC(q)->kind)) return true;
        if (rq_head >= rq_len || (limit >= 0 && n >= limit)) return false;
        Redex r = rq[rq_head++];
        if (rq_head == rq_len) rq_head = rq_len = 0;
        interact(r.op, r.v);
        n++;
    }
}

/* ---------------- building a net from syntax ---------------- */
typedef struct { Port *sup; int cur, n; } Supply;
typedef struct { Supply *s; int nslots; const int *uses; } Frame;

static void bind(Frame *f, int slot, Port prov) {
    int u = f->uses[slot];
    Supply *s = &f->s[slot];
    s->sup = malloc((size_t)(u + 1) * sizeof(Port)); s->n = u; s->cur = 0;
    split(prov, u, s->sup);
}
static void bind_dim(Frame *f, int slot, Dim i) {
    int u = f->uses[slot];
    Supply *s = &f->s[slot];
    s->sup = malloc((size_t)(u + 1) * sizeof(Port)); s->n = u; s->cur = 0;
    for (int k = 0; k < u; k++) s->sup[k] = iv_cell(iv_atom(i));
}
static Port build(Syn *t, Frame *f);
static Port op1(int kind, Syn *a, Frame *f) { Cell *c = cell(kind, 2); link(build(a, f), P(c, 0)); return P(c, 1); }

static Port build(Syn *t, Frame *f) {
    Cell *c;
    switch (t->tag) {
    case S_VAR: {
        Supply *s = &f->s[t->slot];
        if (s->cur >= s->n) { fprintf(stderr, "internal: slot %d used beyond its count\n", t->slot); exit(2); }
        return s->sup[s->cur++];
    }
    case S_LAM:
        c = cell(V_LAM, t->n + 1); c->p = t->rec;
        for (int k = 0; k < t->n; k++) link(build(t->k[k], f), P(c, k + 1));
        return P(c, 0);
    case S_APP: c = cell(O_APP, 3); link(build(t->k[0], f), P(c, 0)); link(build(t->k[1], f), P(c, 1)); return P(c, 2);
    case S_PAIR: c = cell(V_PAIR, 3); goto fields;
    case S_PI: c = cell(V_PI, 3); goto fields;
    case S_SIGMA: c = cell(V_SIGMA, 3); goto fields;
    case S_PATHP: c = cell(V_PATHP, 4); goto fields;
    fields:
        for (int k = 0; k < c->n - 1; k++) link(build(t->k[k], f), P(c, k + 1));
        return P(c, 0);
    case S_FST: return op1(O_FST, t->k[0], f);
    case S_SND: return op1(O_SND, t->k[0], f);
    case S_U: return P(cell(V_U, 1), 0);
    case S_PLAM: {
        Dim i = fresh_dim();
        bind_dim(f, t->slot, i);
        Cell *m = cell(O_MKPLAM, 2); m->a = i;
        link(build(t->k[0], f), P(m, 0));
        return P(m, 1);
    }
    case S_FORALL: {
        Dim i = fresh_dim();
        bind_dim(f, t->slot, i);
        Cell *m = cell(O_FORALL, 2); m->a = i;
        link(build(t->k[0], f), P(m, 0));
        return P(m, 1);
    }
    case S_PAPP:
        c = cell(O_PAPPR, t->x ? 5 : 3); c->x = t->x;
        link(build(t->k[1], f), P(c, 0)); link(build(t->k[0], f), P(c, 1));
        if (t->x) { link(build(t->k[2], f), P(c, 2)); link(build(t->k[3], f), P(c, 3)); }
        return P(c, c->n - 1);
    case S_IV0: return iv_cell(dnf_zero());
    case S_IV1: return iv_cell(dnf_one());
    case S_NEG: return op1(O_NEG, t->k[0], f);
    case S_BIN: c = cell(O_BIN, 3); c->x = t->x; link(build(t->k[0], f), P(c, 0)); link(build(t->k[1], f), P(c, 1)); return P(c, 2);
    case S_FEQ: c = cell(O_FEQ, 2); c->a = t->x; link(build(t->k[0], f), P(c, 0)); return P(c, 1);
    case S_FTT: c = cell(V_FACE, 1); c->p = dnf_one(); return P(c, 0);
    case S_FFF: c = cell(V_FACE, 1); c->p = dnf_zero(); return P(c, 0);
    case S_FACEOF: return op1(O_FACEOF, t->k[0], f);
    case S_SYS0: c = cell(V_SYS, 1); c->p = NULL; return P(c, 0);
    case S_SYSCONS:
        c = cell(O_SYSCONS, 4);
        link(build(t->k[0], f), P(c, 0)); link(build(t->k[1], f), P(c, 1)); link(build(t->k[2], f), P(c, 2));
        return P(c, 3);
    case S_SYSMAP: c = cell(O_SYSMAP, 3); link(build(t->k[1], f), P(c, 0)); link(build(t->k[0], f), P(c, 1)); return P(c, 2);
    case S_COMP:
        c = cell(O_COMP, 4);
        link(build(t->k[1], f), P(c, 0)); link(build(t->k[0], f), P(c, 1)); link(build(t->k[2], f), P(c, 2));
        return P(c, 3);
    case S_GLUE: c = cell(O_MKGLUE, 3); link(build(t->k[1], f), P(c, 0)); link(build(t->k[0], f), P(c, 1)); return P(c, 2);
    case S_GLUEV: c = cell(O_MKGLUEV, 3); link(build(t->k[0], f), P(c, 0)); link(build(t->k[1], f), P(c, 1)); return P(c, 2);
    case S_UNGLUE: c = cell(O_UNGLUE, 3); link(build(t->k[0], f), P(c, 0)); link(build(t->k[1], f), P(c, 1)); return P(c, 2);
    case S_GLOBAL: c = cell(V_GLOBAL, 1); c->a = (uint64_t)t->id; return P(c, 0);
    case S_AXIOM: c = cell(V_NVAR, 1); c->a = (uint64_t)t->id; return P(c, 0);
    case S_LET: {
        bind(f, t->slot, build(t->k[0], f));
        return build(t->k[1], f);
    }
    }
    fprintf(stderr, "build: tag %d\n", t->tag); exit(2);
}

static Port run_frame(Syn *body, int nslots, const int *uses, int nparam, Port param, int nenv, const int *env_slot, const Port *env) {
    Frame f = { calloc((size_t)nslots + 1, sizeof(Supply)), nslots, uses };
    if (nparam) bind(&f, 0, param);
    for (int k = 0; k < nenv; k++) bind(&f, env_slot[k], env[k]);
    Port r = build(body, &f);
    for (int k = 0; k < nslots; k++) {
        if (f.s[k].cur != f.s[k].n) { fprintf(stderr, "internal: slot %d built %d of %d uses\n", k, f.s[k].cur, f.s[k].n); exit(2); }
        free(f.s[k].sup);
    }
    free(f.s);
    return r;
}
Port record_build(const Record *r, Port param, const Port *env) {
    return run_frame(r->body, r->nslots, r->uses, r->nparam, param, r->nenv, r->env_slot, env);
}
Port top_build(Syn *body, int nslots, const int *uses) {
    return run_frame(body, nslots, uses, 0, 0, 0, NULL, NULL);
}
