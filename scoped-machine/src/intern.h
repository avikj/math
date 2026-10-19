/* intern.h — structural interning of immutable word records.
 *
 * A record is a finite sequence of 64-bit words. Two records are equal
 * exactly when their word sequences are equal; hash equality alone is never
 * taken as equality. Ids are dense, start at 1, and are never reused. Record
 * storage is contiguous and never moves: a pointer returned by interner_get
 * stays valid for the table's lifetime.
 *
 * The law and its overlap cases are INTERNING.md. A small record (at most
 * INTERN_SMALL words) is interned by one bounded unit: lock-free descent of a
 * compressed trie, comparison, and on absence reservation, copy and
 * publication by CAS. A large record is identified by a canonical tree of
 * small records (its content identity, built by a number of units fixed by
 * its length); its contiguous record is the value of one owner keyed by the
 * tree root (the `intern.flatten` producer), which every other requester
 * awaits.
 */
#ifndef CUBICAL_INTERN_H
#define CUBICAL_INTERN_H

#include "common.h"
#include <pthread.h>

#define CHUNK_BITS 11
#define CHUNK_SIZE ((size_t)1 << CHUNK_BITS)
#define MAX_CHUNKS ((size_t)1 << 15)

/* Non-moving, lazily chunked array of fixed-size elements. Element i lives
 * at a stable address once created. Creation of a chunk is done under the
 * caller's lock; the chunk pointer is published with release semantics so a
 * reader that learned of index i through a synchronized channel can read it
 * without the lock. */
typedef struct {
    void *dir[MAX_CHUNKS];
    size_t elem;
} Chunked;

void chunked_init(Chunked *c, size_t elem);
void chunked_free(Chunked *c);
void *chunked_at(Chunked *c, size_t i);           /* creates the chunk if needed (zeroed) */
void *chunked_get(const Chunked *c, size_t i);    /* read-only: chunk must exist */
void *chunked_peek(const Chunked *c, size_t i);   /* read-only: NULL when the chunk does not exist yet */

typedef struct { uint64_t *w; size_t n; uint64_t hash; uint64_t live; uint64_t flat; } Rec;   /* live: the record is published; flat: of a tree root, its flat record id (0 none) */

/* A record's search key is the word stream (hash, n, w[0..n-1]). Records are
 * found through a 16-ary radix trie over the nibbles of that stream, with a
 * leaf at the first nibble that separates a record from every other: distinct
 * records have distinct streams, so a lookup or an insertion visits at most
 * 16·(n+2) nodes — a bound fixed by the key width, independent of the number
 * of records and of hash collisions. The trie only grows; no rehash exists.
 * Slot word: 0 empty, (id<<1)|1 a leaf, idx<<1 an inner node. */
typedef struct { uint64_t c[16]; } TrieNode;

#define WPAGE_WORDS 4096
typedef struct Interner Interner;
struct Interner {
    Chunked recs;             /* Rec per id (index id-1) */
    Chunked nodes;            /* TrieNode per index-1; index 1 is the root */
    size_t n;                 /* ids reserved so far (atomic) */
    size_t nnodes;            /* nodes allocated so far (atomic) */
    uint64_t *pages;          /* every page and oversized record, linked through word 0 (pushed by CAS); each thread carves its own current page */
    Interner *tree;           /* the canonical trees of large records (small records only), created on first use */
    size_t index;             /* registry index (never reused) */
};
#define INTERN_SMALL 16       /* a record of at most this many words is interned by one unit */
#define TREE_FAN 15           /* words per leaf, children per inner node */
#define TREE_LEVELS 18
enum { TREE_LEAF = 1, TREE_NODE = 2, TREE_ROOT = 3 };
extern __thread int intern_in_step;   /* set by the evaluator around a counted step */
Interner *interner_by_index(size_t index);
/* the evaluator's route to a large record's flat record: request the
 * flatten key from a root (the interner sits below the evaluator) */
typedef uint64_t (*FlattenHook)(Interner *t, uint64_t root);
void interner_set_flatten_hook(FlattenHook h);
/* the flatten owner's operations (one owner per (table, root)) */
uint64_t interner_flat_of(Interner *t, uint64_t root);                 /* the published flat id, or 0 */
const uint64_t *interner_tree_get(Interner *t, uint64_t id, size_t *n); /* a tree record */
uint64_t *interner_flat_reserve(Interner *t, size_t n);
uint64_t interner_flat_publish(Interner *t, uint64_t root, uint64_t *dst, size_t n);

void interner_init(Interner *t);
void interner_free(Interner *t);
/* returns id; *created set to true when the record did not exist before */
uint64_t interner_intern(Interner *t, const uint64_t *w, size_t n, bool *created);
/* lookup without creating; returns 0 when absent */
uint64_t interner_find(Interner *t, const uint64_t *w, size_t n);
const uint64_t *interner_get(const Interner *t, uint64_t id, size_t *n);
size_t interner_count(Interner *t);   /* ids reserved: records, plus ids of lost insertion races */
bool interner_live(const Interner *t, uint64_t id);   /* id names a published record */

/* ---- records under construction ----
 * A word buffer is appended one word per operation into fixed-size pooled
 * pages, with the record hash maintained incrementally. */
#define WB_PAGE 62
typedef struct WPage { struct WPage *next; uint64_t w[WB_PAGE]; } WPage;
typedef struct { WPage *head, *tail; size_t n; uint64_t h; } WordBuf;
void wordbuf_init(WordBuf *b);
void wordbuf_push(WordBuf *b, uint64_t x);
void wordbuf_clear(WordBuf *b);       /* releases every page (one release per page) */
bool wordbuf_drain_one(WordBuf *b);   /* releases one page; false when none is left (the buffer is then empty) */
uint64_t wordbuf_intern(Interner *t, WordBuf *b);   /* host (outside counted steps): the buffer's record interned at once; the buffer is emptied */

/* ---- stepped interning ----
 * One unit is one small intern (or find). A small record is one unit; a
 * large record is its tree: one unit per leaf (≤ TREE_FAN words read from the
 * source, a consumed buffer page released in the same unit), one per inner
 * node (carried or folded), one for the root — a count fixed by n. Then the
 * flat record is requested (INTERN_FLATTEN). The source is a contiguous array
 * or a word buffer, which is empty afterwards. */
typedef struct {
    Interner *t;
    const uint64_t *arr; WordBuf *buf; size_t n;
    size_t pos; const WPage *pg; size_t pbase;               /* source cursor */
    uint64_t lvl[TREE_LEVELS][TREE_FAN]; uint8_t cnt[TREE_LEVELS];
    uint64_t carry; unsigned phase, fi; bool find;
    uint64_t root, result; bool created;
} InternState;
enum { INTERN_RUNNING = 0, INTERN_DONE, INTERN_FLATTEN };
void intern_begin(InternState *s, Interner *t, const uint64_t *arr, WordBuf *buf, size_t n);
int intern_advance(InternState *s, size_t budget);   /* DONE: s->result; FLATTEN: the tree root s->root is built */
uint64_t intern_complete(InternState *s);            /* outside jobs: the flat record of s->root */



#endif
