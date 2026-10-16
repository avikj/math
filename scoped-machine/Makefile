CC      ?= gcc
CFLAGS  ?= -std=c11 -O1 -g -Wall -Wextra -Wno-unused-parameter -Wno-missing-field-initializers -fsanitize=address,undefined -fno-omit-frame-pointer -pthread -Isrc
LDFLAGS ?= -fsanitize=address,undefined -pthread

SRC := src/intern.c src/dnf.c src/machine.c src/interval.c src/face.c src/term.c src/scope.c src/template.c src/eval.c src/lib.c src/net.c src/match.c src/canon.c src/check.c src/compiler.c src/work.c src/shape.c src/reuse.c
OBJ := $(SRC:.c=.o)

all: build/tests build/schedule build/concurrent build/match build/check build/templates build/review-regressions build/compiler build/review-followup build/review-claim-wait build/review-checker-lifecycle build/review-ae756a1 build/review-0f787a3 build/review-9eadaf2 build/review-end-to-end build/review-nested-scope build/demo-speculation build/work build/reuse build/accept-boundaries build/accept-checker build/accept-handles

build/tests: $(OBJ) tests/test_main.o
	@mkdir -p build
	$(CC) $(LDFLAGS) -o $@ $^

%.o: %.c src/*.h
	$(CC) $(CFLAGS) -c -o $@ $<

build/accept-boundaries: $(OBJ) tests/accept_sharing_boundaries.o
	@mkdir -p build
	$(CC) $(LDFLAGS) -o $@ $^

build/accept-checker: $(OBJ) tests/accept_check_weakening.o
	@mkdir -p build
	$(CC) $(LDFLAGS) -o $@ $^

build/accept-handles: $(OBJ) tests/accept_shared_work_handle.o
	@mkdir -p build
	$(CC) $(LDFLAGS) -o $@ $^

build/reuse: $(OBJ) tests/test_reuse.o
	@mkdir -p build
	$(CC) $(LDFLAGS) -o $@ $^

build/work: $(OBJ) tests/test_work.o
	@mkdir -p build
	$(CC) $(LDFLAGS) -o $@ $^

build/schedule: $(OBJ) tests/test_schedule.o
	@mkdir -p build
	$(CC) $(LDFLAGS) -o $@ $^

build/concurrent: $(OBJ) tests/test_concurrent.o
	@mkdir -p build
	$(CC) $(LDFLAGS) -o $@ $^

build/match: $(OBJ) tests/test_match.o
	@mkdir -p build
	$(CC) $(LDFLAGS) -o $@ $^

build/check: $(OBJ) tests/test_check.o
	@mkdir -p build
	$(CC) $(LDFLAGS) -o $@ $^

build/templates: $(OBJ) tests/test_templates.o
	@mkdir -p build
	$(CC) $(LDFLAGS) -o $@ $^

build/review-regressions: $(OBJ) tests/review_regressions.o
	@mkdir -p build
	$(CC) $(LDFLAGS) -o $@ $^

build/compiler: $(OBJ) tests/test_compiler.o
	@mkdir -p build
	$(CC) $(LDFLAGS) -o $@ $^

build/review-followup: $(OBJ) tests/review_followup.o
	@mkdir -p build
	$(CC) $(LDFLAGS) -o $@ $^

# includes check.c directly to stage a claim interleaving: linked without check.o
build/review-claim-wait: $(filter-out src/check.o,$(OBJ)) tests/review_claim_wait.o
	@mkdir -p build
	$(CC) $(LDFLAGS) -o $@ $^

build/review-checker-lifecycle: $(OBJ) tests/review_checker_lifecycle.o
	@mkdir -p build
	$(CC) $(LDFLAGS) -o $@ $^

build/review-ae756a1: $(OBJ) tests/review_ae756a1.o
	@mkdir -p build
	$(CC) $(LDFLAGS) -o $@ $^

build/review-0f787a3: $(OBJ) tests/review_0f787a3.o
	@mkdir -p build
	$(CC) $(LDFLAGS) -o $@ $^

REVIEW_AE_MODES := signature scope annotations missing-level environment retry partial-context publication canon publication-concurrent diagnostics-concurrent
REVIEW_0F_MODES := scope-level scope-locals call-boundary binder-boundary machine-restart missing-level

build/review-9eadaf2: $(OBJ) tests/review_9eadaf2.o
	@mkdir -p build
	$(CC) $(LDFLAGS) -o $@ $^

REVIEW_9E_MODES := scope-depth scope-sort nested-control kappa-restart kappa-alias kappa-thread

build/review-end-to-end: $(OBJ) tests/review_end_to_end.o
	@mkdir -p build
	$(CC) $(LDFLAGS) -o $@ $^

build/review-nested-scope: $(OBJ) tests/review_nested_scope.o
	@mkdir -p build
	$(CC) $(LDFLAGS) -o $@ $^

build/demo-speculation: $(OBJ) tests/demo_speculation.o
	@mkdir -p build
	$(CC) $(LDFLAGS) -o $@ $^

REVIEW_E2E_MODES := candidate guard false-scope coe-scope net-tview diagram-session net-race positive

test: all
	./build/check
	./build/match
	./build/templates
	./build/compiler
	./build/review-regressions
	./build/review-regressions recursive
	./build/review-regressions concurrent
	./build/review-regressions wordmap-window
	./build/tests
	./build/schedule
	./build/concurrent
	CUBICAL_WORKERS=4 ./build/tests
	CUBICAL_WORKERS=4 ./build/schedule
	CUBICAL_WORKERS=4 ./build/check
	CUBICAL_WORKERS=4 ./build/templates
	CUBICAL_WORKERS=4 ./build/compiler
	./build/review-followup
	./build/review-followup formation
	./build/review-followup admission
	./build/review-followup call
	./build/review-claim-wait
	./build/review-checker-lifecycle
	for m in $(REVIEW_AE_MODES); do ./build/review-ae756a1 $$m || exit 1; done
	for m in $(REVIEW_0F_MODES); do ./build/review-0f787a3 $$m || exit 1; done
	for m in $(REVIEW_9E_MODES); do ./build/review-9eadaf2 $$m || exit 1; done
	for m in $(REVIEW_E2E_MODES) universe packed-level; do ./build/review-end-to-end $$m || exit 1; done
	CUBICAL_WORKERS=4 ./build/review-end-to-end positive
	./build/review-nested-scope
	./build/demo-speculation
	./build/work
	CUBICAL_WORKERS=4 ./build/work
	./build/reuse
	CUBICAL_WORKERS=4 ./build/reuse
	for m in $(ACCEPT_MODES); do ./build/accept-boundaries $$m || exit 1; done
	./build/accept-checker
	./build/accept-handles

ACCEPT_MODES := origin alpha face specialize environment identity-name work
TSAN_TESTS := test_main test_schedule test_concurrent test_check test_match test_templates test_compiler review_regressions review_followup review_checker_lifecycle review_ae756a1 review_0f787a3 review_9eadaf2 review_end_to_end review_nested_scope test_work test_reuse accept_sharing_boundaries accept_check_weakening accept_shared_work_handle
TSAN_CORE  := $(patsubst src/%.c,build/tsan/%.o,$(SRC))
tsan:
	@mkdir -p build/tsan
	for f in $(SRC) $(patsubst %,tests/%.c,$(TSAN_TESTS)); do $(CC) -std=c11 -O1 -g -pthread -Isrc -fsanitize=thread -c -o build/tsan/$$(basename $$f .c).o $$f || exit 1; done
	for t in $(TSAN_TESTS); do $(CC) -pthread -fsanitize=thread -o build/tsan/$$t $(TSAN_CORE) build/tsan/$$t.o || exit 1; done
	CUBICAL_WORKERS=4 ./build/tsan/test_main
	CUBICAL_WORKERS=4 ./build/tsan/test_schedule
	./build/tsan/test_concurrent
	CUBICAL_WORKERS=4 ./build/tsan/test_check
	./build/tsan/test_match
	CUBICAL_WORKERS=4 ./build/tsan/test_templates
	CUBICAL_WORKERS=4 ./build/tsan/test_compiler
	TSAN_OPTIONS=halt_on_error=1 ./build/tsan/review_regressions
	TSAN_OPTIONS=halt_on_error=1 ./build/tsan/review_regressions recursive
	TSAN_OPTIONS=halt_on_error=1 ./build/tsan/review_regressions concurrent
	TSAN_OPTIONS=halt_on_error=1 ./build/tsan/review_regressions wordmap-window
	TSAN_OPTIONS=halt_on_error=1 ./build/tsan/review_followup call
	TSAN_OPTIONS=halt_on_error=1 ./build/tsan/review_checker_lifecycle
	for m in $(REVIEW_AE_MODES); do TSAN_OPTIONS=halt_on_error=1 ./build/tsan/review_ae756a1 $$m || exit 1; done
	for m in $(REVIEW_0F_MODES); do TSAN_OPTIONS=halt_on_error=1 ./build/tsan/review_0f787a3 $$m || exit 1; done
	for m in $(REVIEW_9E_MODES); do TSAN_OPTIONS=halt_on_error=1 ./build/tsan/review_9eadaf2 $$m || exit 1; done
	for m in $(REVIEW_E2E_MODES) diagram-race; do TSAN_OPTIONS=halt_on_error=1 ./build/tsan/review_end_to_end $$m || exit 1; done
	CUBICAL_WORKERS=4 TSAN_OPTIONS=halt_on_error=1 ./build/tsan/review_end_to_end positive
	TSAN_OPTIONS=halt_on_error=1 ./build/tsan/review_nested_scope
	$(CC) -std=c11 -O1 -g -pthread -fsanitize=thread -o build/tsan/review_claim_wait tests/review_claim_wait.c $(filter-out build/tsan/check.o,$(TSAN_CORE))
	TSAN_OPTIONS=halt_on_error=1 ./build/tsan/review_claim_wait
	TSAN_OPTIONS=halt_on_error=1 ./build/tsan/test_work
	CUBICAL_WORKERS=4 TSAN_OPTIONS=halt_on_error=1 ./build/tsan/test_work
	TSAN_OPTIONS=halt_on_error=1 ./build/tsan/test_reuse
	CUBICAL_WORKERS=4 TSAN_OPTIONS=halt_on_error=1 ./build/tsan/test_reuse
	for m in $(ACCEPT_MODES); do CUBICAL_WORKERS=4 TSAN_OPTIONS=halt_on_error=1 ./build/tsan/accept_sharing_boundaries $$m || exit 1; done
	CUBICAL_WORKERS=4 TSAN_OPTIONS=halt_on_error=1 ./build/tsan/accept_check_weakening
	CUBICAL_WORKERS=4 TSAN_OPTIONS=halt_on_error=1 ./build/tsan/accept_shared_work_handle

clean:
	rm -f src/*.o tests/*.o
	rm -rf build

.PHONY: all test tsan clean
