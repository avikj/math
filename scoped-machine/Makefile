CC      ?= gcc
CFLAGS  ?= -std=c11 -O1 -g -Wall -Wextra -Wno-unused-parameter -Wno-missing-field-initializers -fsanitize=address,undefined -fno-omit-frame-pointer -pthread -Isrc -Itests
LDFLAGS ?= -fsanitize=address,undefined -pthread

SRC := src/radix.c src/arena.c src/kalloc.c src/kcont.c src/intern.c src/dnf.c src/machine.c src/interval.c src/face.c src/term.c src/scope.c src/template.c src/eval.c src/lib.c src/net.c src/match.c src/canon.c src/check.c src/compiler.c src/work.c src/shape.c src/reuse.c src/fine.c src/proof.c src/runtime.c
OBJ := $(SRC:.c=.o)

all: build/tests build/schedule build/concurrent build/match build/check build/templates build/review-regressions build/compiler build/review-followup build/review-claim-wait build/review-checker-lifecycle build/review-ae756a1 build/review-0f787a3 build/review-9eadaf2 build/review-end-to-end build/review-nested-scope build/demo-speculation build/work build/reuse build/accept-boundaries build/accept-checker build/accept-handles build/fine build/proof-use build/runtime build/review-alias-scope build/review-alias-faces build/review-work-budget build/review-proof-boundary build/review-certificate-boundary build/review-frame-cost build/review-singleton build/review-generic-action build/review-runtime-presentations build/review-runtime-nodes build/review-runtime-edges build/review-work-edges build/review-node-level build/review-reservation-budget build/review-store-growth build/review-store-interleave build/review-prepare-boundary build/review-arena-budget build/review-audit-budget build/review-v19 build/review-v19-work build/review-assumption-copy build/review-kernel-budget build/review-v20 build/review-v20-intern build/review-live-prefix build/test-prefix build/review-v21 build/review-bounds build/test-v21-extra

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
	./build/review-reservation-budget
	./build/review-store-growth
	./build/review-store-interleave
	./build/review-prepare-boundary 64
	./build/review-prepare-boundary 4096
	./build/review-arena-budget
	./build/review-audit-budget 256
	for m in arena-directory arena-empty audit-admission audit-marks; do ./build/review-v19 $$m || exit 1; done
	for m in sync-reap audit-sharing; do ./build/review-v19-work $$m || exit 1; done
	for m in both transform reference; do ./build/review-assumption-copy $$m || exit 1; done
	./build/review-kernel-budget 64
	for m in independent independent-release independent-cone retry prepare-retry lifecycle fresh-retire; do ./build/review-v20 $$m || exit 1; done
	for n in 32 256 1024; do ./build/review-v20 evaluator $$n || exit 1; done
	for n in 64 512; do ./build/review-v20 map-sort $$n || exit 1; done
	for n in 64 300; do ./build/review-v20-intern $$n || exit 1; done
	for m in specialize restrict; do for w in 0 4; do ./build/review-live-prefix $$m $$w || exit 1; done; done
	./build/test-prefix all
	for m in zero-head zero-order ledger capacity wait-owner cleanup-wait cleanup-drain zero-stress; do ./build/review-v21 $$m || exit 1; done
	$(MAKE) --no-print-directory bounds-test
	for m in ledger-mixed wait-shared wait-early growth cleanup-orders; do ./build/test-v21-extra $$m || exit 1; done

ACCEPT_MODES := origin alpha face specialize environment identity-name work
TSAN_TESTS := review_v19 review_node_level review_runtime_edges review_runtime_nodes test_fine_cost test_proof_use review_alias_scope review_alias_faces test_proof_boundary review_certificate_boundary review_frame_cost review_singleton_witnesses review_generic_identity_action review_runtime_presentations test_main test_schedule test_concurrent test_check test_match test_templates test_compiler review_regressions review_followup review_checker_lifecycle review_ae756a1 review_0f787a3 review_9eadaf2 review_end_to_end review_nested_scope test_work test_reuse accept_sharing_boundaries accept_check_weakening accept_shared_work_handle
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
	$(CC) -std=c11 -O1 -g -pthread -Isrc -Itests -fsanitize=thread -o build/tsan/review_reservation_budget tests/review_reservation_budget.c $(filter-out build/tsan/work.o,$(TSAN_CORE))
	TSAN_OPTIONS=halt_on_error=1 ./build/tsan/review_reservation_budget
	$(CC) -std=c11 -O1 -g -pthread -Isrc -Itests -fsanitize=thread -o build/tsan/review_store_growth tests/review_store_growth.c $(filter-out build/tsan/work.o,$(TSAN_CORE))
	TSAN_OPTIONS=halt_on_error=1 ./build/tsan/review_store_growth
	$(CC) -std=c11 -O1 -g -pthread -Isrc -Itests -fsanitize=thread -o build/tsan/review_store_interleave tests/review_store_interleave.c $(filter-out build/tsan/work.o,$(TSAN_CORE))
	TSAN_OPTIONS=halt_on_error=1 ./build/tsan/review_store_interleave
	$(CC) -std=c11 -O1 -g -pthread -Isrc -Itests -fsanitize=thread -o build/tsan/review_prepare_boundary tests/review_prepare_boundary.c $(filter-out build/tsan/work.o,$(TSAN_CORE))
	TSAN_OPTIONS=halt_on_error=1 ./build/tsan/review_prepare_boundary 64
	TSAN_OPTIONS=halt_on_error=1 ./build/tsan/review_prepare_boundary 4096
	$(CC) -std=c11 -O1 -g -pthread -Isrc -Itests -fsanitize=thread -o build/tsan/review_arena_budget tests/review_arena_budget.c $(filter-out build/tsan/work.o,$(TSAN_CORE))
	TSAN_OPTIONS=halt_on_error=1 ./build/tsan/review_arena_budget
	$(CC) -std=c11 -O1 -g -pthread -Isrc -Itests -fsanitize=thread -o build/tsan/review_audit_budget tests/review_audit_budget.c $(filter-out build/tsan/work.o,$(TSAN_CORE))
	TSAN_OPTIONS=halt_on_error=1 ./build/tsan/review_audit_budget 64
	for m in arena-directory arena-empty audit-admission audit-marks; do TSAN_OPTIONS=halt_on_error=1 ./build/tsan/review_v19 $$m || exit 1; done
	$(CC) -std=c11 -O1 -g -pthread -Isrc -Itests -fsanitize=thread -o build/tsan/review_v19_work tests/review_v19_work.c $(filter-out build/tsan/work.o,$(TSAN_CORE))
	for m in sync-reap audit-sharing; do TSAN_OPTIONS=halt_on_error=1 ./build/tsan/review_v19_work $$m || exit 1; done
	$(CC) -std=c11 -O1 -g -pthread -Isrc -Itests -fsanitize=thread -o build/tsan/review_assumption_copy tests/review_assumption_copy.c $(filter-out build/tsan/work.o,$(TSAN_CORE))
	for m in both transform reference; do TSAN_OPTIONS=halt_on_error=1 ./build/tsan/review_assumption_copy $$m || exit 1; done
	$(CC) -std=c11 -O1 -g -pthread -Isrc -Itests -fsanitize=thread -o build/tsan/review_kernel_budget tests/review_kernel_budget.c $(filter-out build/tsan/work.o,$(TSAN_CORE))
	TSAN_OPTIONS=halt_on_error=1 ./build/tsan/review_kernel_budget 32
	$(CC) -std=c11 -O1 -g -pthread -Isrc -Itests -fsanitize=thread -Wl,--wrap=qsort -o build/tsan/review_v20 tests/review_v20.c $(filter-out build/tsan/work.o,$(TSAN_CORE))
	for m in independent independent-release independent-cone retry prepare-retry lifecycle fresh-retire; do TSAN_OPTIONS=halt_on_error=1 ./build/tsan/review_v20 $$m || exit 1; done
	for n in 32 256; do TSAN_OPTIONS=halt_on_error=1 ./build/tsan/review_v20 evaluator $$n || exit 1; done
	for n in 64 512; do TSAN_OPTIONS=halt_on_error=1 ./build/tsan/review_v20 map-sort $$n || exit 1; done
	$(CC) -std=c11 -O1 -g -pthread -Isrc -Itests -fsanitize=thread -o build/tsan/review_v20_intern tests/review_v20_intern.c $(TSAN_CORE)
	for n in 64 300; do TSAN_OPTIONS=halt_on_error=1 ./build/tsan/review_v20_intern $$n || exit 1; done
	$(CC) -std=c11 -O1 -g -pthread -Isrc -Itests -fsanitize=thread -o build/tsan/review_live_prefix tests/review_live_prefix.c $(TSAN_CORE)
	for m in specialize restrict; do for w in 0 4; do TSAN_OPTIONS=halt_on_error=1 ./build/tsan/review_live_prefix $$m $$w || exit 1; done; done
	$(CC) -std=c11 -O1 -g -pthread -Isrc -Itests -fsanitize=thread -o build/tsan/test_prefix tests/test_prefix.c $(TSAN_CORE)
	TSAN_OPTIONS=halt_on_error=1 ./build/tsan/test_prefix all
	$(CC) -std=c11 -O1 -g -pthread -Isrc -Itests -fsanitize=thread -o build/tsan/review_v21 tests/review_v21.c $(filter-out build/tsan/work.o,$(TSAN_CORE))
	for m in zero-head zero-order ledger capacity wait-owner cleanup-wait cleanup-drain zero-stress; do TSAN_OPTIONS=halt_on_error=1 ./build/tsan/review_v21 $$m || exit 1; done
	$(CC) -std=c11 -O1 -g -pthread -Isrc -Itests -fsanitize=thread -o build/tsan/review_bounds tests/review_bounds.c $(TSAN_CORE)
	$(CC) -std=c11 -O1 -g -pthread -Isrc -Itests -fsanitize=thread -o build/tsan/test_v21_extra tests/test_v21_extra.c $(filter-out build/tsan/work.o,$(TSAN_CORE))
	for m in ledger-mixed wait-shared wait-early growth cleanup-orders; do TSAN_OPTIONS=halt_on_error=1 ./build/tsan/test_v21_extra $$m || exit 1; done
	for a in 'interval 129' 'scope 129' 'net-capture 129' 'net-apply 129' 'mixed 129' 'required 4096' chunked sparse bound-encoding signature; do TSAN_OPTIONS=halt_on_error=1 ./build/tsan/review_bounds $$a || exit 1; done

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
build/review-reservation-budget: $(filter-out src/work.o,$(OBJ)) tests/review_reservation_budget.c src/work.c
	@mkdir -p build
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ tests/review_reservation_budget.c $(filter-out src/work.o,$(OBJ))
build/review-store-growth: $(filter-out src/work.o,$(OBJ)) tests/review_store_growth.c src/work.c
	@mkdir -p build
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ tests/review_store_growth.c $(filter-out src/work.o,$(OBJ))
build/review-store-interleave: $(filter-out src/work.o,$(OBJ)) tests/review_store_interleave.c src/work.c
	@mkdir -p build
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ tests/review_store_interleave.c $(filter-out src/work.o,$(OBJ))
build/review-prepare-boundary: $(filter-out src/work.o,$(OBJ)) tests/review_prepare_boundary.c src/work.c
	@mkdir -p build
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ tests/review_prepare_boundary.c $(filter-out src/work.o,$(OBJ))
build/review-arena-budget: $(filter-out src/work.o,$(OBJ)) tests/review_arena_budget.c src/work.c
	@mkdir -p build
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ tests/review_arena_budget.c $(filter-out src/work.o,$(OBJ))
build/review-audit-budget: $(filter-out src/work.o,$(OBJ)) tests/review_audit_budget.c src/work.c
	@mkdir -p build
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ tests/review_audit_budget.c $(filter-out src/work.o,$(OBJ))
build/review-v19: $(OBJ) tests/review_v19.o
	@mkdir -p build
	$(CC) $(LDFLAGS) -o $@ $^
build/review-v19-work: $(filter-out src/work.o,$(OBJ)) tests/review_v19_work.c src/work.c
	@mkdir -p build
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ tests/review_v19_work.c $(filter-out src/work.o,$(OBJ))
build/review-assumption-copy: $(filter-out src/work.o,$(OBJ)) tests/review_assumption_copy.c src/work.c
	@mkdir -p build
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ tests/review_assumption_copy.c $(filter-out src/work.o,$(OBJ))
build/review-kernel-budget: $(filter-out src/work.o,$(OBJ)) tests/review_kernel_budget.c src/work.c
	@mkdir -p build
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ tests/review_kernel_budget.c $(filter-out src/work.o,$(OBJ))
build/review-v20: $(filter-out src/work.o,$(OBJ)) tests/review_v20.c src/work.c
	@mkdir -p build
	$(CC) $(CFLAGS) $(LDFLAGS) -Wl,--wrap=qsort -o $@ tests/review_v20.c $(filter-out src/work.o,$(OBJ))
build/test-v21-extra: $(filter-out src/work.o,$(OBJ)) tests/test_v21_extra.c src/work.c
	@mkdir -p build
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ tests/test_v21_extra.c $(filter-out src/work.o,$(OBJ))
build/review-v21: $(filter-out src/work.o,$(OBJ)) tests/review_v21.c src/work.c
	@mkdir -p build
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ tests/review_v21.c $(filter-out src/work.o,$(OBJ))
build/test-prefix: $(OBJ) tests/test_prefix.c
	@mkdir -p build
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ tests/test_prefix.c $(OBJ)
build/review-live-prefix: $(OBJ) tests/review_live_prefix.c
	@mkdir -p build
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ tests/review_live_prefix.c $(OBJ)
build/review-v20-intern: $(OBJ) tests/review_v20_intern.c
	@mkdir -p build
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ tests/review_v20_intern.c $(OBJ)
build/review-work-edges: $(filter-out src/work.o,$(OBJ)) tests/review_work_edges.c
	@mkdir -p build
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ tests/review_work_edges.c $(filter-out src/work.o,$(OBJ))

# Bounds correction regressions implemented in the supplied patch.
# Exact-number and allocator completion probes are separately tracked in BOUNDS-COMPLETION.md.
build/review-bounds: $(OBJ) tests/review_bounds.o
	@mkdir -p build
	$(CC) $(LDFLAGS) -o $@ $^
bounds-test: build/review-bounds
	./build/review-bounds interval 129
	./build/review-bounds scope 129
	./build/review-bounds net-capture 17
	./build/review-bounds net-capture 129
	./build/review-bounds net-apply 17
	./build/review-bounds net-apply 129
	./build/review-bounds mixed 129
	./build/review-bounds required 4096
	./build/review-bounds chunked
	./build/review-bounds sparse
	./build/review-bounds bound-encoding
	./build/review-bounds signature
.PHONY: bounds-test
