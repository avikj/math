/* cubical.h — the machine as a library. One machine per process; calls from one thread.
 *
 * A program is text in the machine's language (README.md). Loading runs its forms: definitions,
 * checked definitions, data types, identities, inputs. Every call returns instead of exiting:
 * an error in the text is reported by cub_error(). Strings returned are the caller's to free
 * with cub_free. */
#ifndef CUBICAL_H
#define CUBICAL_H
#ifdef __cplusplus
extern "C" {
#endif

/* start the machine with n worker threads besides the caller (0: the caller only) */
int cub_init(int workers);
/* where verdicts and readings of loaded forms are written (NULL: standard output) */
void cub_output(void *file /* FILE * */);

/* load a file (its imports first; once per file; the check cache applies), or text: the number of
 * failed forms, or -1 on an error (cub_error) */
int cub_load_file(const char *path);
int cub_load_string(const char *text);

/* the normal form of a term, read back as text; NULL on an error */
char *cub_eval(const char *term);

/* check a term at a type without defining it. ok: 1 accepted, 0 rejected, -1 error.
 * reason: on rejection, the failing subterm, the reason and the values it concerns */
typedef struct { int ok; char *reason; long steps; } cub_verdict;
cub_verdict cub_check(const char *type, const char *term);
/* check and define name := term : type (on acceptance) */
cub_verdict cub_define(const char *name, const char *type, const char *term);

/* supply a declared input (input name) with a term: 0, or -1 on an error */
int cub_supply(const char *input, const char *term);

/* interactions performed so far */
long cub_steps(void);
const char *cub_error(void);
void cub_free(void *p);

#ifdef __cplusplus
}
#endif
#endif
