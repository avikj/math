CC      ?= gcc
CFLAGS  ?= -std=c11 -O1 -g -Wall -Wextra -Wno-unused-parameter -fsanitize=address,undefined -fno-omit-frame-pointer -pthread
LDFLAGS ?= -fsanitize=address,undefined -pthread

SRC := src/intern.c src/dnf.c src/machine.c src/interval.c src/face.c src/term.c src/eval.c src/lib.c src/net.c src/match.c src/canon.c src/check.c
OBJ := $(SRC:.c=.o)

all: build/tests build/schedule build/concurrent build/match build/check build/templates build/review-regressions

build/tests: $(OBJ) tests/test_main.o
	@mkdir -p build
	$(CC) $(LDFLAGS) -o $@ $^

%.o: %.c src/*.h
	$(CC) $(CFLAGS) -c -o $@ $<

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

test: all
	./build/check
	./build/match
	./build/templates
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

TSAN_TESTS := test_main test_schedule test_concurrent test_check test_match test_templates review_regressions
TSAN_CORE  := $(patsubst src/%.c,build/tsan/%.o,$(SRC))
tsan:
	@mkdir -p build/tsan
	for f in $(SRC) $(patsubst %,tests/%.c,$(TSAN_TESTS)); do $(CC) -std=c11 -O1 -g -pthread -fsanitize=thread -c -o build/tsan/$$(basename $$f .c).o $$f || exit 1; done
	for t in $(TSAN_TESTS); do $(CC) -pthread -fsanitize=thread -o build/tsan/$$t $(TSAN_CORE) build/tsan/$$t.o || exit 1; done
	CUBICAL_WORKERS=4 ./build/tsan/test_main
	CUBICAL_WORKERS=4 ./build/tsan/test_schedule
	./build/tsan/test_concurrent
	CUBICAL_WORKERS=4 ./build/tsan/test_check
	./build/tsan/test_match
	CUBICAL_WORKERS=4 ./build/tsan/test_templates
	TSAN_OPTIONS=halt_on_error=1 ./build/tsan/review_regressions
	TSAN_OPTIONS=halt_on_error=1 ./build/tsan/review_regressions recursive
	TSAN_OPTIONS=halt_on_error=1 ./build/tsan/review_regressions concurrent
	TSAN_OPTIONS=halt_on_error=1 ./build/tsan/review_regressions wordmap-window

clean:
	rm -f src/*.o tests/*.o
	rm -rf build

.PHONY: all test tsan clean
