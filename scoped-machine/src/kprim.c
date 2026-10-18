/* kprim.c — the input-sized loops of the kernel primitives as frame families
 * (kframe.h): the heap sort with deduplication (one sift — at most 64
 * iterations, an architecture-fixed bound — or one dedupe step per
 * transition) and the variable-length word copy (one word per transition). */
#include "common.h"
#include "fine.h"

KF_DECL_EXT(sort_unique_u64, size_t, sort_unique_u64_PARAMS, size_t i, e, j;)
KF_STEP(sort_unique_u64) {
    KF_BEGIN(sort_unique_u64);
    if (F->n < 2) KF_RET(F->n);
    for (F->i = F->n / 2; F->i > 0; F->i--) { sift_down_u64(F->a, F->n, F->i - 1); kernel_sort_step(); KF_SAFE(); }
    for (F->e = F->n - 1; F->e > 0; F->e--) { uint64_t t = F->a[0]; F->a[0] = F->a[F->e]; F->a[F->e] = t; sift_down_u64(F->a, F->e, 0); kernel_sort_step(); KF_SAFE(); }
    F->j = 1;
    for (F->i = 1; F->i < F->n; F->i++) { if (F->a[F->i] != F->a[F->j - 1]) F->a[F->j++] = F->a[F->i]; kernel_sort_step(); KF_SAFE(); }
    KF_RET(F->j);
    KF_END;
}
KF_SYNC_DEF(sort_unique_u64, size_t, sort_unique_u64_PARAMS, sort_unique_u64(uint64_t *a, size_t n))

KF_DECL_EXT(k_copy_words, void, k_copy_words_PARAMS, size_t i;)
KF_STEP(k_copy_words) {
    KF_BEGIN(k_copy_words);
    for (F->i = 0; F->i < F->n; F->i++) { F->dst[F->i] = F->src[F->i]; fine_bump(FC_COPY_WORDS); KF_SAFE(); }
    KF_RETV();
    KF_END;
}
KF_SYNC_VOID_DEF(k_copy_words, k_copy_words_PARAMS, k_copy_words(uint64_t *dst, const uint64_t *src, size_t n))

KF_DECL_EXT(words_reserve, void, words_reserve_PARAMS, size_t nc;)
KF_STEP(words_reserve) {
    KF_BEGIN(words_reserve);
    if (F->b->n + F->extra <= F->b->cap) KF_RETV();
    F->nc = F->b->cap ? F->b->cap * 2 : 16;
    while (F->nc < F->b->n + F->extra) F->nc *= 2;
    KF_CALL(k_regrow, (void **)&F->b->w, F->b->w, F->nc * sizeof(uint64_t));
    F->b->cap = F->nc;
    KF_RETV();
    KF_END;
}

KF_DECL_EXT(words_append, void, words_append_PARAMS,)
KF_STEP(words_append) {
    KF_BEGIN(words_append);
    KF_CALL(words_reserve, NULL, F->b, F->n);
    KF_CALL(k_copy_words, NULL, F->b->w + F->b->n, F->x, F->n);
    F->b->n += F->n;
    KF_RETV();
    KF_END;
}
