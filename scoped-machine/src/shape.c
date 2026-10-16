/* shape.c — structural computation identity (§76). See shape.h. */
#include "shape.h"
#include "state.h"
#include "reuse.h"

static ShapeId shape_intern(const Words *w) { pthread_mutex_lock(&M.shape_mu); ShapeId id = interner_intern(&M.shapes, w->w, w->n, NULL); pthread_mutex_unlock(&M.shape_mu); return id; }
static bool memo_get(RefId t, MapId rho, uint32_t depth, ShapeId *out) { uint64_t k[3] = { t, rho, depth }; pthread_mutex_lock(&M.shape_mu); bool h = wordmap_get(&M.shape_memo, k, 3, out); pthread_mutex_unlock(&M.shape_mu); return h; }
static void memo_put(RefId t, MapId rho, uint32_t depth, ShapeId v) { uint64_t k[3] = { t, rho, depth }; pthread_mutex_lock(&M.shape_mu); wordmap_put(&M.shape_memo, k, 3, v); pthread_mutex_unlock(&M.shape_mu); }

/* ρ extended by one bound identity */
static MapId rho_extend(MapId rho, Sort sort, uint64_t concrete, uint32_t depth, BinderSlot slot) {
    MapBuilder b; mapb_init(&b);
    size_t nt = map_n_terms(rho), nd = map_n_dims(rho);
    for (size_t k = 0; k < nt; k++) { TermVarId x; RefId im; map_term_entry(rho, k, &x, &im); if (!(sort == S_TERM && x == concrete)) mapb_term(&b, x, im); }
    for (size_t k = 0; k < nd; k++) { DimVarId i; IntervalId im; map_dim_entry(rho, k, &i, &im); if (!(sort == S_DIM && i == concrete)) mapb_dim(&b, i, im); }
    if (sort == S_TERM) mapb_term(&b, concrete, ref_var(bound_id(depth, slot))); else mapb_dim(&b, concrete, iv_var(bound_id(depth, slot)));
    return mapb_finish(&b);
}

ShapeId shape_under(RefId t, MapId rho, uint32_t depth) {
    ShapeId memo;
    if (memo_get(t, rho, depth, &memo)) return memo;
    Words w; words_init(&w);
    if (ref_is_var(t)) {
        TermVarId x = ref_var_id(t);
        RefId im = map_term_image(rho, x);
        if (im != t && ref_is_var(im) && is_bound_id(ref_var_id(im))) { words_push(&w, SH_BOUND); words_push(&w, ref_var_id(im)); }
        else { words_push(&w, SH_FREE); words_push(&w, x); }
    } else {
        Head h; open_ref(t, &h);
        words_push(&w, SH_NODE); words_push(&w, h.tag); words_push(&w, h.payload); words_push(&w, h.levels);
        words_push(&w, fc_reindex(ref_required(t), rho));
        words_push(&w, h.n);
        for (size_t k = 0; k < h.n; k++) {
            const HField *f = &h.f[k];
            words_push(&w, f->kind);
            if (!f->is_binder) {
                words_push(&w, 0);
                switch (f->kind) {
                case F_REF: words_push(&w, shape_under(f->id, rho, depth)); break;
                case F_INTERVAL: words_push(&w, iv_reindex(f->id, rho)); break;
                case F_FACE: words_push(&w, fc_reindex(f->id, rho)); break;
                }
                continue;
            }
            words_push(&w, f->sort);
            if (f->sort == S_TERM) {
                TermOpen o = resolve_term_binder(t, f->slot, f->index);
                MapId rho2 = rho_extend(rho, S_TERM, o.x, depth, f->slot);
                words_push(&w, shape_under(o.body, rho2, depth + 1));
            } else {
                DimOpen o = resolve_dim_binder(t, f->slot, f->index);
                MapId rho2 = rho_extend(rho, S_DIM, o.j, depth, f->slot);
                words_push(&w, shape_under(o.body, rho2, depth + 1));
            }
        }
        head_free(&h);
    }
    reuse_bump(REUSE_SHAPE_NODE);
    ShapeId id = shape_intern(&w);
    words_free(&w);
    memo_put(t, rho, depth, id);
    return id;
}
ShapeId shape_of(RefId t) { return shape_under(t, map_identity(), 0); }
const uint64_t *shape_words(ShapeId s, size_t *n) { return interner_get(&M.shapes, s, n); }
size_t shape_count(void) { return interner_count(&M.shapes); }
