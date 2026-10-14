#include "intern.h"

static uint64_t hash_words(const uint64_t *w, size_t n) {
    uint64_t h = 1469598103934665603ULL;
    for (size_t i = 0; i < n; i++) {
        uint64_t x = w[i];
        for (int b = 0; b < 8; b++) {
            h ^= (x & 0xff);
            h *= 1099511628211ULL;
            x >>= 8;
        }
    }
    h ^= (uint64_t)n;
    h *= 1099511628211ULL;
    return h ? h : 1;
}

void interner_init(Interner *t) {
    memset(t, 0, sizeof *t);
    t->nslots = 1024;
    t->slots = calloc(t->nslots, sizeof(uint64_t));
    require(t->slots, "out of memory");
}

void interner_free(Interner *t) {
    free(t->store); free(t->off); free(t->len); free(t->hash); free(t->slots);
    memset(t, 0, sizeof *t);
}

static bool rec_equal(const Interner *t, uint64_t id, const uint64_t *w, size_t n) {
    size_t i = id - 1;
    if (t->len[i] != n) return false;
    return n == 0 || memcmp(t->store + t->off[i], w, n * sizeof(uint64_t)) == 0;
}

static void grow_slots(Interner *t) {
    size_t ns = t->nslots * 2;
    uint64_t *slots = calloc(ns, sizeof(uint64_t));
    require(slots, "out of memory");
    for (size_t s = 0; s < t->nslots; s++) {
        uint64_t id = t->slots[s];
        if (!id) continue;
        size_t p = t->hash[id - 1] & (ns - 1);
        while (slots[p]) p = (p + 1) & (ns - 1);
        slots[p] = id;
    }
    free(t->slots);
    t->slots = slots;
    t->nslots = ns;
}

uint64_t interner_find(const Interner *t, const uint64_t *w, size_t n) {
    uint64_t h = hash_words(w, n);
    size_t p = h & (t->nslots - 1);
    while (t->slots[p]) {
        uint64_t id = t->slots[p];
        if (t->hash[id - 1] == h && rec_equal(t, id, w, n)) return id;
        p = (p + 1) & (t->nslots - 1);
    }
    return 0;
}

uint64_t interner_intern(Interner *t, const uint64_t *w, size_t n, bool *created) {
    uint64_t h = hash_words(w, n);
    size_t p = h & (t->nslots - 1);
    while (t->slots[p]) {
        uint64_t id = t->slots[p];
        if (t->hash[id - 1] == h && rec_equal(t, id, w, n)) {
            if (created) *created = false;
            return id;
        }
        p = (p + 1) & (t->nslots - 1);
    }
    /* insert */
    if (t->n == t->cap) {
        t->cap = t->cap ? t->cap * 2 : 64;
        t->off = realloc(t->off, t->cap * sizeof(size_t));
        t->len = realloc(t->len, t->cap * sizeof(size_t));
        t->hash = realloc(t->hash, t->cap * sizeof(uint64_t));
        require(t->off && t->len && t->hash, "out of memory");
    }
    if (t->store_len + n > t->store_cap) {
        size_t nc = t->store_cap ? t->store_cap * 2 : 256;
        while (nc < t->store_len + n) nc *= 2;
        t->store = realloc(t->store, nc * sizeof(uint64_t));
        require(t->store, "out of memory");
        t->store_cap = nc;
    }
    size_t i = t->n++;
    t->off[i] = t->store_len;
    t->len[i] = n;
    t->hash[i] = h;
    if (n) memcpy(t->store + t->store_len, w, n * sizeof(uint64_t));
    t->store_len += n;
    uint64_t id = (uint64_t)(i + 1);
    t->slots[p] = id;
    if (t->n * 2 > t->nslots) grow_slots(t);
    if (created) *created = true;
    return id;
}

const uint64_t *interner_get(const Interner *t, uint64_t id, size_t *n) {
    require(id >= 1 && id <= t->n, "bad interned id %llu", (unsigned long long)id);
    if (n) *n = t->len[id - 1];
    return t->store + t->off[id - 1];
}

/* ---- WordMap ---- */
void wordmap_init(WordMap *m) { interner_init(&m->keys); m->vals = NULL; m->cap = 0; }
void wordmap_free(WordMap *m) { interner_free(&m->keys); free(m->vals); m->vals = NULL; m->cap = 0; }

bool wordmap_get(WordMap *m, const uint64_t *k, size_t n, uint64_t *out) {
    uint64_t id = interner_find(&m->keys, k, n);
    if (!id) return false;
    *out = m->vals[id - 1];
    return true;
}

void wordmap_put(WordMap *m, const uint64_t *k, size_t n, uint64_t v) {
    bool created;
    uint64_t id = interner_intern(&m->keys, k, n, &created);
    if (id > m->cap) {
        size_t nc = m->cap ? m->cap * 2 : 64;
        while (nc < id) nc *= 2;
        m->vals = realloc(m->vals, nc * sizeof(uint64_t));
        require(m->vals, "out of memory");
        m->cap = nc;
    }
    m->vals[id - 1] = v;
}
