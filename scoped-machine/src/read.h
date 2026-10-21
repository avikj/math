/* read.h — the reader: text into term records (read.c has the syntax).
 * An input boundary: it builds the records the machine runs and decides
 * nothing about them. */
#ifndef CUBICAL_READ_H
#define CUBICAL_READ_H
#include "term.h"
#include <setjmp.h>

typedef struct Reader Reader;
Reader *reader_new(void);
void reader_free(Reader *r);
/* a sequence of (def name A t) / (axiom name A); false on a syntax error */
bool reader_program(Reader *r, const char *src);
/* one term over the program's definitions; 0 on a syntax error */
RefId reader_term(Reader *r, const char *src);
RefId reader_global(const Reader *r, const char *name);   /* 0 when absent */
const char *reader_error(const Reader *r);
#endif
