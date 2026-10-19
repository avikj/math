CC      ?= gcc
CFLAGS  ?= -std=c11 -O1 -g -Wall -Wextra -Wno-unused-parameter -Wno-missing-field-initializers -fsanitize=address,undefined -fno-omit-frame-pointer -pthread
LDFLAGS ?= -fsanitize=address,undefined -pthread

SRC := src/intern.c src/count.c src/pool.c src/dnfam.c src/subst.c src/construct.c src/scopefam.c src/machine.c src/interval.c src/face.c src/term.c src/scope.c src/template.c src/eval.c src/lib.c src/check.c src/compiler.c src/pins.c src/judge.c src/proof.c src/chain.c src/effect.c
OBJ := $(SRC:.c=.o)
TESTS := test_protocol test_chain test_effect test_records test_dnf test_subst test_alpha test_check test_templates test_compiler test_proof_use test_main review_singleton_witnesses review_generic_identity_action review_runtime_nodes
BINS := $(addprefix build/,$(TESTS))

all: $(BINS)

$(BINS): build/%: tests/%.o $(OBJ)
	@mkdir -p build
	$(CC) $(LDFLAGS) -o $@ $^

%.o: %.c src/*.h
	$(CC) $(CFLAGS) -c -o $@ $<

test: all
	for t in $(BINS); do ./$$t || exit 1; done
	CUBICAL_WORKERS=4 ./build/test_compiler

TSAN_CORE := $(patsubst src/%.c,build/tsan/%.o,$(SRC))
tsan:
	@mkdir -p build/tsan
	for f in $(SRC) $(patsubst %,tests/%.c,$(TESTS)); do $(CC) -std=c11 -O1 -g -pthread -fsanitize=thread -c -o build/tsan/$$(basename $$f .c).o $$f || exit 1; done
	for t in $(TESTS); do $(CC) -pthread -fsanitize=thread -o build/tsan/$$t $(TSAN_CORE) build/tsan/$$t.o || exit 1; done
	for t in $(TESTS); do CUBICAL_WORKERS=4 TSAN_OPTIONS=halt_on_error=1 ./build/tsan/$$t || exit 1; done

clean:
	rm -f src/*.o tests/*.o
	rm -rf build

.PHONY: all test tsan clean
