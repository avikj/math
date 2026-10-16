CC      ?= gcc
CFLAGS  ?= -std=c11 -O1 -g -Wall -Wextra -Wno-unused-parameter -Wno-missing-field-initializers -fsanitize=address,undefined -fno-omit-frame-pointer -pthread -Isrc -Itests
LDFLAGS ?= -fsanitize=address,undefined -pthread

SRC := src/intern.c src/dnf.c src/machine.c src/interval.c src/face.c src/term.c src/scope.c src/template.c src/eval.c src/lib.c src/net.c src/match.c src/canon.c src/check.c src/compiler.c src/work.c src/shape.c src/reuse.c src/fine.c src/proof.c src/runtime.c
OBJ := $(SRC:.c=.o)

all: build/tests build/schedule build/concurrent build/match build/check build/templates build/review-regressions build/compiler build/review-followup build/review-claim-wait build/review-checker-lifecycle build/review-ae756a1 build/review-0f787a3 build/review-9eadaf2 build/review-end-to-end build/review-nested-scope build/demo-speculation build/work build/reuse build/accept-boundaries build/accept-checker build/accept-handles build/fine build/proof-use build/runtime build/review-alias-scope build/review-alias-faces build/review-work-budget build/review-proof-boundary build/review-certificate-boundary build/review-frame-cost build/review-singleton build/review-generic-action build/review-runtime-presentations build/review-runtime-nodes build/review-runtime-edges build/review-work-edges build/review-node-level

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
	./build/fine
	./build/proof-use
	CUBICAL_WORKERS=4 ./build/proof-use
	./build/runtime
	./build/review-alias-scope 0
	./build/review-alias-scope 4
	./build/review-alias-faces 0
	./build/review-alias-faces 4
	./build/review-work-budget
	./build/review-proof-boundary
	./build/review-certificate-boundary
	./build/review-frame-cost
	./build/review-singleton
	./build/review-generic-action
	./build/review-runtime-presentations
	./build/review-runtime-nodes 0
	./build/review-runtime-nodes 4
	./build/review-runtime-nodes 0 levels
	for m in levels residual commute runtime-cold proof-cold; do ./build/review-runtime-edges $$m || exit 1; done
	for m in interleave same-key growth drain; do ./build/review-work-edges $$m || exit 1; done
	./build/review-node-level

ACCEPT_MODES := origin alpha face specialize environment identity-name work
TSAN_TESTS := review_node_level review_runtime_edges review_runtime_nodes test_fine_cost test_proof_use review_alias_scope review_alias_faces test_proof_boundary review_certificate_boundary review_frame_cost review_singleton_witnesses review_generic_identity_action review_runtime_presentations test_main test_schedule test_concurrent test_check test_match test_templates test_compiler review_regressions review_followup review_checker_lifecycle review_ae756a1 review_0f787a3 review_9eadaf2 review_end_to_end review_nested_scope test_work test_reuse accept_sharing_boundaries accept_check_weakening accept_shared_work_handle
TSAN_CORE  := $(patsubst src/%.c,build/tsan/%.o,$(SRC))
tsan:
	@mkdir -p build/tsan
	for f in $(SRC) $(patsubst %,tests/%.c,$(TSAN_TESTS)); do $(CC) -std=c11 -O1 -g -pthread -Isrc -Itests -fsanitize=thread -c -o build/tsan/$$(basename $$f .c).o $$f || exit 1; done
	$(CC) -std=c11 -O1 -g -pthread -Isrc -Itests -fsanitize=thread -c -o build/tsan/proof_boundary.o tests/proof_boundary.c
	for t in $(TSAN_TESTS); do $(CC) -pthread -fsanitize=thread -o build/tsan/$$t $(TSAN_CORE) build/tsan/$$t.o build/tsan/proof_boundary.o || exit 1; done
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
	TSAN_OPTIONS=halt_on_error=1 ./build/tsan/test_fine_cost
	TSAN_OPTIONS=halt_on_error=1 ./build/tsan/test_proof_use
	CUBICAL_WORKERS=4 TSAN_OPTIONS=halt_on_error=1 ./build/tsan/test_proof_use
	TSAN_OPTIONS=halt_on_error=1 ./build/tsan/review_alias_scope 0
	TSAN_OPTIONS=halt_on_error=1 ./build/tsan/review_alias_scope 4
	TSAN_OPTIONS=halt_on_error=1 ./build/tsan/review_alias_faces 0
	TSAN_OPTIONS=halt_on_error=1 ./build/tsan/review_alias_faces 4
	TSAN_OPTIONS=halt_on_error=1 ./build/tsan/test_proof_boundary
	TSAN_OPTIONS=halt_on_error=1 ./build/tsan/review_certificate_boundary
	TSAN_OPTIONS=halt_on_error=1 ./build/tsan/review_frame_cost
	TSAN_OPTIONS=halt_on_error=1 ./build/tsan/review_singleton_witnesses
	TSAN_OPTIONS=halt_on_error=1 ./build/tsan/review_generic_identity_action
	TSAN_OPTIONS=halt_on_error=1 ./build/tsan/review_runtime_presentations
	TSAN_OPTIONS=halt_on_error=1 ./build/tsan/review_node_level
	TSAN_OPTIONS=halt_on_error=1 ./build/tsan/review_runtime_nodes 0
	TSAN_OPTIONS=halt_on_error=1 ./build/tsan/review_runtime_nodes 4
	TSAN_OPTIONS=halt_on_error=1 ./build/tsan/review_runtime_nodes 0 levels
	for m in levels residual commute runtime-cold proof-cold; do TSAN_OPTIONS=halt_on_error=1 ./build/tsan/review_runtime_edges $$m || exit 1; done
	$(CC) -std=c11 -O1 -g -pthread -Isrc -Itests -fsanitize=thread -o build/tsan/review_work_edges tests/review_work_edges.c $(filter-out build/tsan/work.o,$(TSAN_CORE))
	for m in interleave same-key growth drain; do TSAN_OPTIONS=halt_on_error=1 ./build/tsan/review_work_edges $$m || exit 1; done
	$(CC) -std=c11 -O1 -g -pthread -Isrc -Itests -fsanitize=thread -o build/tsan/review_work_budget tests/review_work_budget.c $(filter-out build/tsan/work.o,$(TSAN_CORE))
	TSAN_OPTIONS=halt_on_error=1 ./build/tsan/review_work_budget

clean:
	rm -f src/*.o tests/*.o
	rm -rf build

.PHONY: all test tsan clean

build/fine: $(OBJ) tests/test_fine_cost.o
	@mkdir -p build
	$(CC) $(LDFLAGS) -o $@ $^

build/runtime: $(OBJ) tests/test_runtime.o
	@mkdir -p build
	$(CC) $(LDFLAGS) -o $@ $^

build/proof-use: $(OBJ) tests/test_proof_use.o
	@mkdir -p build
	$(CC) $(LDFLAGS) -o $@ $^

build/review-alias-scope: $(OBJ) tests/review_alias_scope.o
	@mkdir -p build
	$(CC) $(LDFLAGS) -o $@ $^
build/review-alias-faces: $(OBJ) tests/review_alias_faces.o
	@mkdir -p build
	$(CC) $(LDFLAGS) -o $@ $^
build/review-work-budget: $(filter-out src/work.o,$(OBJ)) tests/review_work_budget.c
	@mkdir -p build
	$(CC) $(CFLAGS) -Itests $(LDFLAGS) -o $@ tests/review_work_budget.c $(filter-out src/work.o,$(OBJ))
build/review-proof-boundary: $(OBJ) tests/proof_boundary.o tests/test_proof_boundary.o
	@mkdir -p build
	$(CC) $(LDFLAGS) -o $@ $^
build/review-certificate-boundary: $(OBJ) tests/proof_boundary.o tests/review_certificate_boundary.o
	@mkdir -p build
	$(CC) $(LDFLAGS) -o $@ $^
build/review-frame-cost: $(OBJ) tests/review_frame_cost.o
	@mkdir -p build
	$(CC) $(LDFLAGS) -o $@ $^
build/review-singleton: $(OBJ) tests/review_singleton_witnesses.o
	@mkdir -p build
	$(CC) $(LDFLAGS) -o $@ $^
build/review-generic-action: $(OBJ) tests/review_generic_identity_action.o
	@mkdir -p build
	$(CC) $(LDFLAGS) -o $@ $^
build/review-runtime-presentations: $(OBJ) tests/review_runtime_presentations.o
	@mkdir -p build
	$(CC) $(LDFLAGS) -o $@ $^

# §83/§87 evidence run: the direct checker over the fully expanded composites
# (two-level action maps, exported two-node diagram); unsanitized build —
# under ASan the expanded two-node export exceeds the host's memory
runtime-full:
	@mkdir -p build/plain
	$(CC) -std=c11 -O1 -g -pthread -Isrc -Itests -o build/plain/runtime tests/test_runtime.c $(SRC)
	./build/plain/runtime full
build/review-runtime-nodes: $(OBJ) tests/review_runtime_nodes.o
	@mkdir -p build
	$(CC) $(LDFLAGS) -o $@ $^
build/review-runtime-edges: $(OBJ) tests/review_runtime_edges.o
	@mkdir -p build
	$(CC) $(LDFLAGS) -o $@ $^
build/review-node-level: $(OBJ) tests/review_node_level.o
	@mkdir -p build
	$(CC) $(LDFLAGS) -o $@ $^
build/review-work-edges: $(filter-out src/work.o,$(OBJ)) tests/review_work_edges.c
	@mkdir -p build
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ tests/review_work_edges.c $(filter-out src/work.o,$(OBJ))
