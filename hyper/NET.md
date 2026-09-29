# net.c, explained

`hyper/net.c` is HVM4's runtime (HigherOrderCO/HVM4 commit 6defdfc, `src/hvm.c`), taken literally. `diff` against
upstream shows exactly four changes, all from `research/sat_fibre/build_profile.py`:

1. **The receipt table** (`net.c:183-212`) is added: `SAT_NAMES`, `SAT_COUNTS`, `sat_report`, `sat_init` and `sat_tick`.
2. **`ITRS_INC`** (`:217`) calls `sat_tick(name)` before `ITRS++`.
3. **`DUP-SUP` is split** (`:3971`) into `DUP-SUP-SAME` and `DUP-SUP-DIFF` by comparing labels. The reduction is unchanged.
4. **Budgets.** `heap_alloc` (`:363`) stops at `SAT_MAX_HEAP`, and `main` (`:6419`) calls `sat_init()`.

Every other rule name in a receipt, such as `"1"`, `"-"`, `EQL-CTR-MIS` or `EQL-MAT-MIS`, is HVM4's own string.

The explanation follows the file top to bottom. Line numbers are `net.c` line numbers. A rewrite is written as HVM4's
own comment writes it: the redex, a rule line naming the receipt, then the result. `x ← v` means "the variable x is
substituted by v".

---

## 1. Header, types, macro (`1-46`)

- **`1-10`:** provenance comment.
- **`11-15`:** HVM4's own header.
- **`17-24`:** libc headers. `sys/mman.h` is for `mmap`.
- **`29-33`:** fixed-width aliases `u8 … u64`, and `str` = `const char*`.
- **`35` `Term = u64`:** every node and every pointer is one 64-bit word.
- **`37-40` `Copy {k0,k1}`:** the two ends of a duplication, returned by the clone helpers.
- **`45` `fn`:** `static inline`. Every function in the file is file-local.

## 2. Tags (`48-96`)

The tag is a node's kind.

**Hot tags, 0–7:**

| Tag | Meaning |
|---|---|
| `APP` | application, 2 fields: fun, arg |
| `VAR` | an occurrence of a lambda-bound variable; val = the lambda's body slot |
| `LAM` | lambda, 1 field: body |
| `DP0`/`DP1` | the two occurrences of a duplicated value; val = the shared slot, ext = label |
| `SUP` | superposition `&L{a,b}`, 2 fields |
| `DUP` | the binder `! X &L = v; body`, 2 fields |
| `ALO` | a lazy instantiation of a book fragment |

**Everything else:**

| Tag | Meaning |
|---|---|
| `REF` | `@name`; ext = book id |
| `NAM` | a stuck name `^x` |
| `DRY` | a stuck application `^(f x)` |
| `ERA` | the eraser `&{}` |
| `MAT` | one case of a constructor match: field 0 = the case body, field 1 = the rest of the chain |
| `C00`–`C16` | a constructor with 0–16 fields; the tag encodes arity, ext = constructor name |
| `NUM` | u32 literal, unboxed in val |
| `SWI` | `MAT` on a number (`ext` = the number); distinct only for printing |
| `USE` | `λ{f}`: force the argument, then apply f |
| `OP2` | numeric binary op; ext = opcode |
| `DSU`/`DDU` | superposition and duplication with a label computed at run time |
| `EQL` | structural equality |
| `AND`/`OR` | short-circuit |
| `UNS` | unscoped binder |
| `ANY` | wildcard `*` |
| `INC` | `↑x`, a priority wrapper read only by the collapse queue |
| `BJV`/`BJ0`/`BJ1` | variables of a *static* (book) term as de Bruijn levels |

**Frame and opcode definitions:**

- **`100` `LAM_ERA_MASK`:** bit 23 of a lambda's ext is set when the parser saw zero uses of the binder.
- **`105-107`:** frame tags that exist only on the WNF stack:
  - `F_OP2_NUM`: the left operand is already a number;
  - `F_EQL_L`: defined but never pushed;
  - `F_EQL_R`: the left side is reduced and the right side is being reduced.
- **`110-126`:** opcodes 0–16.

## 3. Bit layout, capacities, globals (`128-234`)

**Bit layout (`133-143`).** A term is `[sub:1][tag:7][ext:24][val:32]`.

- The top bit of the tag byte is the **SUB bit**. A heap slot with SUB set holds a *substitution*: the value its variable
  now stands for (§6).
- `ext` carries a label, constructor name, opcode, lambda level or ALO length.
- `val` carries a heap location or an unboxed number.

**ALO pair (`145-150`).** One heap word packs `ls_loc<<32 | tm_loc`: the bind-list head and the book term's location.

**Capacities (`155-157`).**

- Heap: 2³² words.
- Book: 2²⁴ ids.
- WNF stack: 2³² frames.

The stack is reserved with `mmap`, so only touched pages cost memory.

**Globals (`162-181`).**

- `HEAP` and the bump pointer `HEAP_NEXT` start at 1, so location 0 means "none".
- `BOOK[id]` is the heap location of definition `id`, or 0.
- `WnfBank` is the explicit reduction stack.
- `ITRS` is the interaction count.

**Receipts (`183-212`).**

- **`SAT_NAMES`:** all 60 rule names.
- **`sat_report`:** runs at exit and prints `SAT_PROFILE {"interactions","heap_nodes","rules":{…}}` to stderr.
  - `heap_nodes` is `HEAP_NEXT-1`, i.e. words ever allocated. Nothing is freed; there is no garbage collector.
- **`sat_init`:** reads the budgets `SAT_MAX_ITRS` (default 5,000,000) and `SAT_MAX_HEAP` (32,000,000 words).
- **`sat_tick`:**
  - exits 124 when the interaction budget is reached;
  - otherwise increments the named rule;
  - exits 125 on a name not in the table, so an uncounted rule cannot be silently added.

**`ITRS_INC(name)` (`217-226`).** The only place interactions are counted.

- It counts only when `ITRS_ENABLED`. `runtime_eval_main` enables counting for `-s`, `-S` and `-D`; satcheck runs with `-s`.
- It also records the last rule name, for `-D`.

**Other flags (`227-234`).**

- `FRESH` is the counter for names made by `EQL-LAM`.
- `DEBUG`, `SILENT`, and the `STEPS_*` state are for `-D`.

## 4. Parser types and globals (`236-271`)

- **`nick_alphabet`:** 64 symbols. A name of up to 4 characters packs into 24 bits, 6 bits per character.
- **`PState`:** the source text and the cursor.
- **`PBind`:** one entry of the scope stack.
  - `name`;
  - `lvl`, the de Bruijn level it binds;
  - `lab`: 0 for a lambda/let variable, the label for a dup variable, `PARSE_DYN_LAB` (= 0xFFFFFF) for a dynamic-label dup;
  - `forked`;
  - `cloned` (written `&x`: may be used many times);
  - `side` (0/1 for a destructured dup `&{a,b}`, otherwise -1).
- **Globals:**
  - `PARSE_BINDS` is the stack.
  - `PARSE_FRESH_LAB` starts at 0x800000; the labels the parser invents come from there, so they never meet small user labels.
  - `PARSE_FORK_SIDE` says which branch of a fork is being parsed.

## 5. Terms and the heap (`273-674`)

**Word access (`276-302`).**

- `term_new` packs sub, tag, ext and val.
- The getters unpack them.
- `term_tag` masks off the SUB bit.

**Arity (`304-355`).** `TERM_ARITY` gives the number of heap fields per tag. Everything with arity 0 lives entirely
in its word (`VAR`, `DP0/1`, `NUM`, `ERA`, `REF`, `NAM`, the `BJ*`); `ALO` has arity 0 because its one word is not
a child. `term_arity` looks it up.

**Heap (`360-394`).**

- `heap_alloc(size)` bumps `HEAP_NEXT` and never frees. It stops with exit 124 past the heap budget, and exit 1 past 2³² words.
- `heap_read` / `heap_set` are plain access.
- `heap_take` reads a slot that must be nonzero; it aborts otherwise, which catches reading a dup slot that was never filled.

**Constructors (`399-638`).** Each `term_new_X` allocates the node's fields, writes them and returns the pointer word.
The `_at` variants write into a location the caller already has; the rules use these to reuse the redex's own memory.

| Constructor | Words |
|---|---|
| `lam` | 1 |
| `app`, `sup`, `dup`, `mat`, `swi`, `op2`, `eql`, `and`, `or`, `dry` | 2 |
| `use`, `uns`, `inc` | 1 |
| `dsu`, `ddu` | 3 |
| `ctr` with arity n | n (arity 0 is unboxed: `C00` with val 0) |
| `num`, `era`, `any`, `ref`, `nam`, `var`, `dp0/1` | 0 (unboxed) |

`term_new_alo(ls, len, tm)`: with an empty bind list (`len==0`) the ALO word is `ALO` with val = `tm` and costs nothing;
otherwise it costs one word holding the packed pair.

**Clone (`640-674`).** This is how the net duplicates.

- `term_clone(lab, v)` writes `v` into one fresh slot and returns `DP0(lab, slot)` and `DP1(lab, slot)`: two
  occurrences sharing one value, which is a `DUP` node of arity 1. **1 word.**
- `term_clone_at(loc, lab)` makes the two occurrences over a slot that already holds the value. **0 words.**
- `term_clone2`, `term_clone3` and `term_clone_many` do this for several values.

The duplication is lazy. Nothing is copied until a `DP0` or `DP1` is reduced and meets what is in the slot (§8.3).

## 6. Arithmetic, substitution, names, system, table (`676-992`)

**`term_op2_u32` (`685-746`).** 32-bit wrap-around arithmetic.

- `x/0` and `x%0` are 0.
- `OP_NOT` ignores `a` and returns `~b`.
- Comparisons return 0 or 1.
- `OP_SUB` is tested first as the likely case.

**Substitution (`751-762`).** This is the whole binding mechanism.

- A lambda's body lives in one slot, and every `VAR` of that lambda points at that slot.
- `heap_subst_var(loc, v)` overwrites the slot with `v` marked SUB. The body was already read out by the rule (`APP-LAM`).
- A `VAR` that reaches a SUB slot takes the value (§8.1).
- A dup occurrence works the same way. `heap_subst_cop(side, loc, r0, r1)` is used when one side of a duplication
  has been computed:
  - it stores the *other* side's result in the shared slot, marked SUB;
  - it returns this side's result.
  - When the other occurrence is reached later, it finds its value waiting.

**Nick encoding (`767-853`).**

- `nick_letter_to_b64` / `nick_b64_to_letter` convert between characters and 6-bit codes.
- `nick_to_str` unpacks up to 4 characters.
- `nick_from_str` packs them.

Labels and `^names` are *numbers* spelled in this alphabet; `&A{…}` is label 27.

**Built-in symbols (`858-870`).** `SYM_ZER`, `SUC`, `NIL`, `CON` and `CHR` are interned constructor names used by the
sugar for naturals `3n`, lists `[a,b]`, `h<>t` and strings.

**System (`875-939`).**

- `sys_error` and `sys_runtime_error` exit 1.
- `sys_path_join` resolves `#include` relative to the including file.
- `sys_file_read` reads a whole file.
- `sys_mmap_anon` is a lazily backed anonymous mapping.

**Name table (`949-992`).** One global intern table for definition names, constructor names and labels. `table_find`
scans linearly and adds the name if it is missing; ids fit in 24 bits. `table_get` returns the string for an id.

## 7. Printer (`994-1805`)

The printer only reads and allocates nothing, so it does not affect counts or heap.

**Helpers.**

- **`print_name` (`998`):** base-64 nick of a number; used for labels and `^names`.
- **`print_utf8*` (`1014-1124`):** emit UTF-8 and decide which characters can be shown escaped inside `'…'` or `"…"`.

**Naming state (`1140-1264`).**

- `PrintState` holds the naming tables.
  - A runtime lambda is named by its body location: `print_state_lam` gives the next lowercase name.
  - A runtime dup is named by its shared slot: `print_state_dup` gives the next uppercase name.
  - Both are recorded in fixed arrays of 65536 entries.
- `quoted`, `subst` and `subst_len` are set while printing inside an `ALO`: book terms use levels, and the ALO bind list
  says which levels are already bound to runtime locations.
- `alo_subst_get` walks that list.

**Name printers (`1276-1309`).** `print_def_name` and `print_sym_name` print interned names. `print_mat_name` prints a
case label: `0n`, `1n+`, `[]`, `<>`, or `#Name`.

**`print_app` (`1312`).** Flattens an `APP`/`DRY` spine into `f(x,y,…)`.

**`print_ctr` (`1339`).** Constructor sugar:

- `Nn` or `Nn+x` for SUC/ZER chains;
- `'c'` for `#CHR{n}`;
- `"…"` for a proper list of printable `CHR`s;
- `[a,b]` for a proper list;
- `h<>t` for an improper one;
- otherwise `#Name{…}`.

**`print_term_go` (`1433-1748`).** One case per tag.

- **Variables:**
  - `VAR`/`DP0`/`DP1` whose slot carries SUB print the substituted value; otherwise they print their name, with `₀`/`₁` for dup sides.
  - `BJ*` inside an ALO print the runtime variable they are bound to, or a depth-based name.
- **Binders:**
  - `LAM` prints `λname.body`.
  - A runtime `DUP` binder prints only its body and queues the dup.
  - `MAT`/`SWI` chains print `λ{k:v;…;default}`. A `NUM 0` tail means no default, and a `USE` tail is unwrapped.
- **Everything else:**
  - `ALO` prints `@{…}` in quoted mode.
  - `OP2`/`EQL`/`AND`/`OR` print infix.
  - `DSU`/`DDU` print with a parenthesised label.
  - `UNS` prints `! f = λ v ; body`.
  - `INC` prints `↑`.

**Finishing (`1751-1805`).**

- `print_term_finish` prints the queued dups as `;!A&L=value;` after the term.
- `print_term` prints a runtime term.
- `print_term_quoted` prints a static one; the collapse uses it to print each result.

## 8. Parser (`1807-3691`)

The parser turns source into **static book terms**: variables are de Bruijn **levels** (`BJV`/`BJ0`/`BJ1`, val = level),
and `LAM`'s ext is the level it binds (plus `LAM_ERA_MASK` when unused). A definition is stored once. It becomes
runtime structure only through `ALO` (§9.2), one layer at a time, as reduction demands it.

**Plumbing (`1815-1955`).**

- `RuntimeEvalCfg` holds the CLI flags.
- `parse_error*` report and exit 1.
  - `parse_error_affine` fires when a non-`&` variable is used twice: every variable is **affine** unless declared cloned.
- `peek`, `advance`, `starts_with`, `match` and `sep` (`,` or `;`) are cursor operations.
- `parse_skip` skips spaces and `//` comments.
- `parse_consume` requires a literal.

**Scope (`1957-2000`).**

- `parse_bind_push` / `_push_side` push a `PBind` at level `depth+1`; `parse_bind_pop` pops it.
- `parse_bind_lookup(name, side)` searches innermost-first and skips "false shadowing":
  - a bare `x` skips dup binders unless they are forked or destructured;
  - `x₀` or `x₁` skip plain binders.
  - It reports `skipped` so the error can say which mistake was made.

**Auto-dup (`2004-2137`).** This is how a cloned variable becomes linear.

- `count_uses` counts occurrences of one level in a parsed body.
- `parse_auto_dup(body, lvl, base, tgt, ext, uses)`: for n = uses-1 fresh labels, `auto_dup_go` rewrites the k-th
  occurrence to `BJ0(lab+k)` (the last one to `BJ1(lab+n-1)`) and shifts outer levels by n. The body is then wrapped in
  the chain `!d0&=x; !d1&=d0₁; …`.
- Result: `[x,x,x]` becomes `!d0&=x; !d1&=d0₁; [d0₀,d1₀,d1₁]`. Every value is used once; sharing is explicit dups.

**Names (`2139-2226`).**

- `parse_name` interns an identifier.
- `parse_name_num` reads it as a 24-bit number; used for labels and `^names`, and exits if it overflows.
- `parse_name_ref` interns a definition name.
- `parse_utf8` decodes one codepoint.

**`parse_term_lam` (`2231-2493`).** Handles everything after `λ`.

- **`λ{}` is `ERA`.**
- **`λ{…}` with cases** builds a `MAT`/`SWI` chain. `tip` points at the chain's tail slot, which starts as `NUM 0`
  meaning "no default".
  - A case label is one of: `'c'`, a number, `0n`, `1n+`, `#Name`, `[]`, `<>`.
  - After the cases:
    - `}` ends the chain;
    - `_:` or a bare term is the default;
    - a body with no case labels at all is `λ{f}` = `USE f`.
- **`λ$x. b` (unscoped)** becomes `UNS(λf. λx. f(b))`, with x affine.
- **`λx&L. b`** is a lambda whose body is `! X &L = x; b`, with uses of `x₀`/`x₁` counted and auto-duped if `&x`.
- **`λx&(e). b`** is the same with a label computed at run time: `λx. DDU(e, x, λx0.λx1. b)`.
- **`λ&x. b` / `λx. b`** is a plain lambda.
  - With `&`, uses are auto-duped.
  - Without `&`, more than one use is an error.
  - Zero uses sets `LAM_ERA_MASK`.
- **`λx, y. b`** recurses on the separator.

**`!` forms (`2497-2783`).**

- **`!&L{a,b} = v; t` / `!&{a,b} = v; t` / `!&(e){a,b} = v; t`** destructure a dup into two named sides
  (`parse_term_dup_pat`).
- **`! x = v; t`** is a let: `(λx.t)(v)`.
- **`!! x = v; t`** is a strict let: `(λ{λx.t})(v)`. The `USE` forces v first.
- **`! f = λ v; t`** is an unscoped pair (`UNS`).
- **`! X &L = v; t`**, **`! X & = v; t`** (fresh label) and **`! X &(e) = v; t`** (`DDU`) are dups; X is used as `X₀`/`X₁`.

**Forks (`2790-3108`).** Sugar for duplicating several variables under one label and superposing two branches.

- **`&Lλx,y{A;B}`** is `λx&L.λy&L.&L{A;B}`. A uses the `₀` sides and B the `₁` sides.
- **`&L[x,&y]{A;B}`** dups the named in-scope variables (a leading `&` means cloned inside each branch).
- **`&L!{A;B}`** dups every variable in scope.
- `PARSE_FORK_SIDE` tells a bare forked variable which side it is.

**`parse_term_sup` (`3115`).** Handles:

- `&{}` = `ERA`;
- `&L{a,b}` = `SUP`;
- `&(e){a,b}` = `DSU`;
- the three fork forms.

**Atoms (`3161-3362`).**

- `#Name{…}` is a constructor of up to 16 fields.
- `@name` is `REF`.
- `^name` is `NAM`; `^(f x)` is `DRY`.
- `( … )` is grouping.
- Numbers: `123` is `NUM`; `3n` / `3n+x` are SUC chains.
- `'c'` is `#CHR{c}`.
- `"…"` / `` `…` `` is a `CON`/`NIL` list of `CHR`.
- `[a,b]` is a list.
- `*` is `ANY`.
- A variable, with optional `₀`/`₁`, resolves to:
  - `BJV(level)` for a plain binder;
  - `BJ0`/`BJ1(lab, level)` for a dup side;
  - `BJV(level+side)` for a dynamic dup, because `DDU`'s body is `λx0.λx1.…`.

**Operators and application (`3368-3585`).**

- `parse_term_opr_*` handle precedence climbing over `+ - * / % ^ ~ << >> < <= > >= == != && ||`.
  - Tightest to loosest: `^`, then `* / %`, `+ -`, shifts, comparisons, equality, `&&`, `||`.
- `parse_term_app_prec` handles:
  - `<>` (cons);
  - `===` (`EQL`), `.&.` (`AND`) and `.|.` (`OR`);
  - infix ops;
  - application `f(a,b)` = `((f a) b)`.
- `parse_term_atom` dispatches on the first character. `↑x` is `INC`.
- `parse_term` = atom followed by its applications and operators.

**Definitions (`3589-3691`).**

- `#include "file"` is parsed once per resolved path.
- `@name = term` resets the scope, parses at depth 0, writes the root into one heap slot, and sets `BOOK[id]` to it.
- `parse_program` parses a whole file.

## 9. Reduction: the interaction rules (`3693-4698`)

Each rule is one function. The table gives the rewrite, the receipt, and the heap words it allocates. The allocations
are what `heap_nodes` sums, together with parsing, ALO, and collapse lifting.

### 9.1 Application

| Rule (receipt) | Rewrite | Words |
|---|---|---|
| `APP-ERA` `3754` | `(&{} a)` → `&{}` | 0 |
| (none) `APP-NAM` `3762` | `(^n a)` → `^(^n a)`: stuck, reuses the APP node as DRY | 0, uncounted |
| (none) `APP-DRY` `3770` | `(^(f x) a)` → `^(^(f x) a)` | 0, uncounted |
| `APP-LAM` `3779` | `(λx.f a)` → `x ← a; f`. If the binder is unused (`LAM_ERA_MASK`), `a` is dropped without being written anywhere | 0 |
| `APP-SUP` `3795` | `(&L{f,g} a)` → `! A &L = a; &L{(f A₀),(g A₁)}`. The SUP's node becomes the first APP, and the APP's node becomes the new SUP | 3 |
| `APP-INC` `3810` | `(↑f x)` → `↑(f x)` | 0 |
| `APP-MAT-SUP` `3827` | `(λ{#K:h;m} &L{a,b})` → `! M &L = mat; &L{(M₀ a),(M₁ b)}` | 5 |
| `APP-MAT-CTR-MAT` `3844` | `(λ{#K:h;m} #K{a,b,…})` → `(h a b …)`. The MAT and CTR nodes become the first two APPs; `m` is dropped | 2·max(0,ari−2) |
| `APP-MAT-CTR-MIS` | `(λ{#K:h;m} #J{…})` → `(m #J{…})`; `h` is dropped | 0 |
| `APP-MAT-NUM-MAT` `3887` | `(λ{n:h;m} n)` → `h`; `m` is dropped | 0 |
| `APP-MAT-NUM-MIS` | `(λ{n:h;m} k)` → `(m k)` | 0 |
| `MAT-INC` `3904` | `(λ{…} ↑x)` → `↑(λ{…} x)` | 2 |

### 9.2 Duplication

`X` is the shared slot `loc`, and `side` says which occurrence was reduced. The rule computes both sides, returns this
side's, and parks the other with `heap_subst_cop`.

| Rule (receipt) | Rewrite | Words |
|---|---|---|
| `DUP-NAM` `3917` | `! X &L = ^n` → `X₀,X₁ ← ^n` (also for a stuck `BJ*`) | 0 |
| `DUP-LAM` `3929` | `! F &L = λx.f` → `F₀ ← λx0.G₀; F₁ ← λx1.G₁; x ← &L{x0,x1}; ! G &L = f`. Layout: `a+0,a+1` = the two new bodies (`G₀`,`G₁`), `a+2,a+3` = the SUP of their variables, `a+4` = the shared `f` | 5 (3 if x is unused: no SUP) |
| `DUP-SUP-SAME` `3970` | `! X &L = &L{a,b}` → `X₀ ← a; X₁ ← b`. The pair is routed and nothing is built | **0** |
| `DUP-SUP-DIFF` | `! X &L = &R{a,b}` → `! A &L = a; ! B &L = b; X₀ ← &R{A₀,B₀}; X₁ ← &R{A₁,B₁}`. The two dups are made over the SUP's own fields | **4** |
| `DUP-NOD` `3996` | `! X &L = T{a,b,…}` → dup each field, `X₀ ← T{A₀,…}; X₁ ← T{A₁,…}`. Applies to constructors, `MAT`/`SWI`/`USE`/`INC`/`OP2`/`DSU`/`DDU`/`DRY`. For arity 0 (`ERA`, `NUM`, `ANY`, nullary CTR) both sides get the atom | 2·ari |

`DUP` never meets `APP`: line `5157` says so explicitly. A dup of an unreduced application waits until the application
reduces.

### 9.3 Book instantiation: ALO (uncounted)

`@{s} t` means "book term `t` under bind list `s`".

- **The bind list** is a linked list in the heap. Each entry is 2 words:
  - `[0]` is the runtime slot the level is bound to: a new lambda's body slot or a new dup's shared slot;
  - `[1]` is `NUM(next entry)`.
- **Levels** are counted from the outside, so level `lvl` is entry `len-lvl` from the head.

| Rule | Rewrite | Words |
|---|---|---|
| `ALO-VAR` `4022` | `@{s} n` → `VAR(s[n])`: a runtime variable pointing at the bound slot | 0 |
| `ALO-DP0/1` `4044` | `@{s} n₀` → `DP0(lab, s[n])` | 0 |
| `ALO-LAM` `4065` | `@{s} λ.f` → `λ.@{x',s} f`. The new entry's slot 0 *is* the new lambda's body slot, so every `VAR` produced for this level points at the body slot, which is where `APP-LAM` writes the argument | 2 (+1 if s was empty) |
| `ALO-DUP` `4081` | `@{s} ! &L = v; t` → entry slot 0 = `@{s} v` (the shared slot), then `@{x',s} t`. The runtime has no DUP node here: `t`'s occurrences become `DP0/DP1` pointing at the entry | 3 |
| `ALO-NOD` `4093` | `@{s} T{a,b,…}` → `T{@{s}a, @{s}b, …}` | ari (+ ari−1 if s nonempty) |
| atoms | `NUM`/`NAM`/`REF`/`ERA`/`ANY` are returned as they are | 0 |

`REF` → `ALO(0,0,BOOK[id])` (`4834`) is also uncounted. Unfolding a definition and copying its structure are not
interactions in this runtime's count. They do allocate, so they appear in `heap_nodes`.

### 9.4 Numbers

| Rule | Rewrite | Words |
|---|---|---|
| `OP2-ERA` `4112` | `(&{} op y)` → `&{}` | 0 |
| `OP2-SUP` `4121` | `(&L{a,b} op y)` → `! Y &L = y; &L{(a op Y₀),(b op Y₁)}` | 3 |
| `OP2-NUM-ERA` `4134` | `(#n op &{})` → `&{}` | 0 |
| `OP2-NUM-NUM` `4142` | `(#a op #b)` → `#(a op b)` | 0 |
| `OP2-NUM-SUP` `4155` | `(#n op &L{a,b})` → `&L{(#n op a),(#n op b)}`. A number is one unboxed word and is copied without a dup, despite the rule's comment | 4 |
| `OP2-INC-X` / `-Y` `4167` | lift `↑` out of either operand | 2 |

### 9.5 Dynamic labels

| Rule | Rewrite | Words |
|---|---|---|
| `DSU-ERA` / `DDU-ERA` | label `&{}` → `&{}` | 0 |
| `DSU-NUM` `4199` | `&(#n){a,b}` → `&n{a,b}` | 2 |
| `DSU-SUP` `4210` | `&(&L{x,y}){a,b}` → `! A &L = a; ! B &L = b; &L{&(x){A₀,B₀}, &(y){A₁,B₁}}` | 8 |
| `DDU-NUM` `4246` | `! X &(#n) = v; b` → `! X &n = v; b(X₀,X₁)` | 5 |
| `DDU-SUP` `4260` | the same split as `DSU-SUP` over val and body | 8 |
| `DSU-INC` / `DDU-INC` | lift `↑` | 3 |

### 9.6 USE, EQL, AND, OR, UNS

**USE.**

| Rule | Rewrite | Words |
|---|---|---|
| `USE-ERA` | `(λ{f} &{})` → `&{}` | 0 |
| `USE-SUP` `4296` | `(λ{f} &L{a,b})` → `! F &L = f; &L{(λ{F₀} a),(λ{F₁} b)}` | 6 |
| `USE-VAL` `4312` | `(λ{f} v)` → `(f v)` once v is in weak normal form | 2 |
| `USE-INC` | lift `↑` | 2 |

**EQL.**

| Rule | Rewrite | Words |
|---|---|---|
| `EQL-ERA-L/R` | `&{}` → `&{}` | 0 |
| `"1"` (EQL-ANY) | `*` on either side → `#1` | 0 |
| `EQL-SUP-L/R` | split over the SUP, cloning the other side | 3 |
| `EQL-NUM` | compare the numbers | 0 |
| `EQL-LAM` `4411` | substitute both binders with one fresh `^name` and compare the bodies | 2 |
| `EQL-CTR-MIS` `4435` | *Counted under this name whether or not the constructors match.* Different → `#0`; nullary → `#1`; arity n → `↑(a0===b0 .&. ↑(a1===b1 .&. ↑(…)))`. The `↑`s only order the collapse | 5n−4 |
| `EQL-MAT-MIS` `4482` | Same counting convention. Different case label → `#0`; same → `(h===h') .&. (m===m')` | 4 |
| `EQL-USE` | compare the bodies | 0 |
| `"-"` (EQL-NAM) | same word → `#1`, else `#0` | 0 |
| `EQL-DRY` | compare fun and arg | 4 |
| `EQL-INC-L/R` | lift `↑` | 0 |
| `EQL-NOT` `5359` | any other pair of weak normal forms → `#0` | 0 |

**AND / OR.**

| Rule | Rewrite | Words |
|---|---|---|
| `AND-ERA` / `OR-ERA` | → `&{}` | 0 |
| `AND-SUP` / `OR-SUP` | split, cloning `b` | 3 |
| `AND-ZER` | `(#0 .&. b)` → `#0`; `b` is dropped | 0 |
| `AND-ONE` | `(#n .&. b)` → `b` | 0 |
| `OR-ZER` | `(#0 .\|. b)` → `b` | 0 |
| `OR-ONE` | `(#n .\|. b)` → `#1`; `b` is dropped | 0 |
| `AND-INC` / `OR-INC` | lift `↑` | 0 |

**UNS.**

| Rule | Rewrite | Words |
|---|---|---|
| `WNF-UNS` `4688` | `! ${f,v}; t` → `t(λy.λ$x.y, $x)`: two lambdas whose variables cross scopes | 6 |

## 10. The reducer: `wnf` (`4700-5535`)

`wnf(term)` reduces to weak head normal form with an explicit stack; there is no C recursion. It has two phases.

**enter (`4777-4980`)** walks toward the head:

- **`VAR` (`4788`):** if its slot carries SUB, continue with the substituted value; otherwise the variable is free, which is a normal form.
- **`DP0/DP1` (`4799`):** if the shared slot carries SUB, the other side already ran and this side's value is waiting.
  Otherwise push this occurrence as a frame and enter the shared value.
- **`APP` (`4812`):** push the application and enter the function.
- **`DUP` (`4820`):** a runtime DUP binder is only scoping: enter its body. Its occurrences already point at its slot.
- **`UNS` (`4827`):** fire `WNF-UNS`.
- **`REF` (`4832`):** if defined, becomes `ALO(0,0,BOOK[id])`; otherwise it is a stuck name.
- **`ALO` (`4842`):** unpack `(ls, tm, len)` and fire the ALO rule for the book node's tag (§9.3).
- **`OP2`, `EQL`, `AND`, `OR` (`4909-4939`):** push and enter field 0 (the strict side).
- **`DSU`, `DDU`:** push and enter the label.
- **Anything else is already in weak head normal form:** `NAM BJ* DRY ERA SUP LAM NUM MAT SWI USE INC` and constructors.

**apply (`4982-5501`)** pops frames and fires the interaction between the frame and the normal form reached:

- **`APP` frame:** dispatch on the function (§9.1).
  - `MAT`/`SWI`/`USE` push *themselves* as a frame and enter the argument; a match is strict in its scrutinee.
  - A number or constructor in function position is a runtime error (exit 1).
  - Anything else (a free `VAR`, a stuck `DP`) rebuilds the application and stays stuck.
- **`MAT`/`SWI` frame:** dispatch on the scrutinee.
  - `ERA` → `APP-ERA`.
  - `SUP` → `APP-MAT-SUP`.
  - `INC` → `MAT-INC`.
  - A constructor or number → `MAT`/`MIS`.
  - A stuck name → `DRY`.
  - Otherwise it stays an application.
- **`USE` frame:** `ERA`, `SUP` or `INC`; otherwise `USE-VAL`.
- **`DP0/DP1` frame:** dispatch on the shared value.
  - `NAM`/`BJ*` → `DUP-NAM`.
  - `LAM` → `DUP-LAM`.
  - `SUP` → `DUP-SUP-SAME` or `-DIFF`.
  - Atoms and nodes → `DUP-NOD`.
  - Otherwise (a free `VAR`, an `APP` stuck on one): write the normal form back into the slot and stay a stuck occurrence.
- **`OP2` frame:**
  - `ERA` → `OP2-ERA`.
  - `NUM` → `OP2-NUM-NUM` immediately if the right side is already a number; otherwise push `F_OP2_NUM` and enter the right side.
  - `SUP` / `INC` → their rules.
- **`F_OP2_NUM` frame:** the right-side rules.
- **`EQL` frame:** `ERA`, `ANY`, `SUP` or `INC` on the left; otherwise store the left normal form in field 0, push
  `F_EQL_R` and enter the right side.
- **`F_EQL_R` frame:** the right-side `ERA`/`ANY`/`SUP`/`INC` rules; otherwise compare by the pair of tags (§9.6).
- **`DSU`/`DDU`/`AND`/`OR` frames:** dispatch on the reduced label or left operand.
- **Stuck:** in each case the node is rebuilt with the normal form written back into its strict field.

Whenever a rule's result may itself be reducible (`APP-LAM`, `MAT` hits, `DUP-SUP`, `DUP-NOD` on a node, `EQL`
structure, `AND`/`OR` on a number, `DDU-NUM`, `USE-VAL`), control goes back to **enter**. Otherwise the result is in
weak head normal form and the next frame is popped.

**Helpers around `wnf`.**

- **`wnf_rebuild` (`4707`):** used only by `-D`, to stop after one interaction. Pops the frames and writes the partial
  result back into their nodes, so the heap is a well-formed term again.
- **`wnf_at(loc)` (`5507`):** reduces the term in a slot and writes the result back. This is the sharing: a node
  reduced once is reduced for every holder of its location.
- **`wnf_steps_at` (`5550`):** for `-D`; one interaction at a time with the whole root printed between steps.

## 11. Runtime, CNF and the two readouts (`5597-6274`)

**Setup (`5605-5693`).**

- `runtime_init`:
  - allocates the book;
  - allocates the name table;
  - reserves the 2³²-word heap with `mmap`;
  - interns the symbols.
- `runtime_free` releases them.
- `runtime_entry` finds `@main`.
- `runtime_prepare` parses and requires `@main`.

**`runtime_eval_main` (`5710`).**

- Turns counting on for `-s`, `-S` and `-D`.
- Runs either `eval_collapse` (`-C`) or `eval_normalize`.
- Prints:
  - with `-s`: `- Itrs: N interactions`, `- Heap: N nodes`, time and rate;
  - with `-S`: only `Itrs`.

satcheck reads `Itrs`/`Heap` and the `SAT_PROFILE` line.

**`Uset` (`5767-5813`).** A bitset over heap locations; `eval_normalize` uses it as its visited set.

**`cnf_at` (`5823-5953`).** One collapse step.

- **Reduce** to weak normal form.
- **Atoms, `SUP` and `INC`** are returned as they are.
- **`LAM`:**
  - bind its variable to the level `BJV(depth+1)`;
  - collapse the body;
  - `ERA` inside becomes `ERA`;
  - `INC` inside is lifted out;
  - a `SUP` inside becomes `&L{λ.a, λ.b}`.
- **Any other node:**
  - collapse each field;
  - any `ERA` field makes the whole node `ERA`, because a branch with an erased part is discarded;
  - the *first* `SUP` field is lifted over the node: `T{…,&L{a,b},…}` → `&L{T{…,a,…}, T{…,b,…}}`, with every other
    field cloned at label L.
- The lifting allocates (`term_clone` per other field, a new node, a SUP), so it appears in `heap_nodes`. It is not an
  interaction: nothing calls `ITRS_INC`. Its clones become ordinary `DP0/DP1`, and when they are reduced *those* are
  counted.

**`eval_normalize` (`5962-6075`), used without `-C`.**

- Depth-first over every reachable slot: `wnf_at` each one.
- A `DP0/DP1` that stays stuck leads to its shared slot.
- Each location is visited at most once.

**`eval_collapse` (`6077-6274`), used with `-C`, `-C1`, `-CN`.** Enumerates the leaves of the superposition tree.

- Each task is a heap slot with `key` = SUP depth and `credit` = INC count, capped at 128.
- The queue is a binary min-heap on `key − credit/16`, with ties broken first-in first-out.
- `eval_collapse_process` runs `cnf` on the slot:
  - **`INC`:** unwrap it, `key−1`, `credit+1`, repeat.
  - **`SUP`:** push both fields at `key+1`.
  - **`ERA`:** the branch is erased; print nothing.
  - **Anything else:** a leaf. Print it with `print_term_quoted` and count it.
- The loop stops after `N` leaves (`-C1`: one).

## 12. CLI (`6276-6483`)

- **`CliOpts`, `cli_prog_name`, `cli_is_uint`, `cli_print_help*`:** usage text.
- **`parse_opts`:**
  - `-s` stats;
  - `-S` silent;
  - `-C[N]` / `--collapse[=N]`;
  - `-D` steps;
  - `-d` debug;
  - `-v`;
  - `-h`;
  - one file.
- **`main`:**
  - `sat_init()`;
  - parse options;
  - `-D` with `-C` is refused;
  - `runtime_init`;
  - read the file;
  - `realpath` (for includes);
  - `runtime_prepare`;
  - `runtime_eval_main`;
  - free.
  - At exit, `sat_report` prints the receipt.

---

## 13. What this file does and does not establish

**Established.**

- **The recorded SAT results.** `satcheck.py` runs all 282 cases of `research/sat_fibre` on this file and matches every
  output, interaction count, heap count and rule count exactly.
- **The label distinction is a real split in the machine.**
  - `DUP-SUP-SAME` allocates nothing.
  - `DUP-SUP-DIFF` allocates 4 words and creates two new dups, which can go on to cross again.

**Not established by this file.** Each of these was stated elsewhere in this repository and is checked here against
the code.

1. **The collapse is a scheduler.** `eval_collapse` is a priority queue with a heuristic (`COLLAPSE_CREDIT_STRIDE`,
   `COLLAPSE_CREDIT_CAP`). This is where `-C1` decides which branch it follows first.
   - Under `-C` (all leaves) every branch is taken, so the set of leaves does not depend on the order.
   - Under `-C1` the order decides which witness is printed and how many interactions happen before it.
   - The recorded `first` counts are counts *of this order*.
2. **The count is of lazy reduction, and dropped values are free.**
   - `APP-LAM` on an unused binder, `APP-MAT-*` (the unused branch), `AND-ZER` and `OR-ONE` discard a subterm without
     any interaction and without reducing it.
   - There is no erasure interaction for garbage and no collector.
   - Both of these contradict the statement "a forgotten port is charged at the projection" in `MAP.md` §0 item 4.
     Forgetting is charged exactly the one interaction of the rule that forgets.
   - `InteractionGeodesic.agda` proves that complete reductions of a system with the one-step diamond have one length.
     That this machine's lazy count equals that length for the net it reduces is a further claim, and nothing here
     proves it.
3. **Not everything is counted.** Uncounted: `REF` unfolding, every `ALO` rule, `APP-NAM`/`APP-DRY`, the stuck rebuilds,
   and the `cnf` lifting. They are counted only as heap words.
4. **Two receipts are coarse.** `EQL-CTR-MIS` and `EQL-MAT-MIS` count both the matching and the mismatching case under
   one name, as upstream does.
5. **`OP2` and `EQL` are not single-principal-port agents.** They are strict in two positions, reduced left then right.
   They are deterministic, so confluence holds, but they are sequenced rules, not a single active pair.
