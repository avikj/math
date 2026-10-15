/* match.h — exact pairwise comparison of labelled graphs modulo renaming
 * (§37), with sharing preserved.
 *
 * A Graph is a plain exported structure (no machine references): nodes with
 * a kind, a label holding every non-renamable scalar, ordered children,
 * unordered children, and a root list. Two graphs are equal when one
 * bijection between their reachable nodes preserves kinds, labels, ordered
 * children by position and unordered children as sets. Partition refinement
 * on the disjoint union only narrows candidates; equality is decided by
 * exact matching with backtracking over unordered collections, never by
 * refinement classes or hashes alone.
 */
#ifndef CUBICAL_MATCH_H
#define CUBICAL_MATCH_H

#include "common.h"

typedef struct {
    int kind;
    char *label;
    VEC(size_t) ordered;
    VEC(size_t) unordered;
} GNode;

typedef struct {
    VEC(GNode) nodes;
    VEC(size_t) roots;        /* matched in order */
    VEC(size_t) setroots;     /* matched as a set (e.g. cache keys) */
} Graph;

Graph *graph_new(void);
void graph_free(Graph *g);
size_t graph_node(Graph *g, int kind, const char *label);
void graph_ordered(Graph *g, size_t parent, size_t child);
void graph_unordered(Graph *g, size_t parent, size_t child);
void graph_root(Graph *g, size_t node);
void graph_setroot(Graph *g, size_t node);

typedef struct {
    bool equal;
    char reason[512];         /* first mismatch: kinds/labels/arity/sharing, with node labels */
    size_t backtracks;        /* diagnostics: tentative assignments undone */
    size_t classes_joint;     /* refinement classes on the disjoint union */
} MatchReport;

bool graph_match(const Graph *a, const Graph *b, MatchReport *rep);

#endif
