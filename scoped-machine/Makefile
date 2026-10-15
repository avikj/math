CC      ?= gcc
CFLAGS  ?= -std=c11 -O1 -g -Wall -Wextra -Wno-unused-parameter -fsanitize=address,undefined -fno-omit-frame-pointer -pthread
LDFLAGS ?= -fsanitize=address,undefined -pthread

SRC := src/intern.c src/dnf.c src/machine.c src/interval.c src/face.c src/term.c src/eval.c src/lib.c src/net.c src/match.c src/canon.c src/check.c
OBJ := $(SRC:.c=.o)

all: build/tests build/schedule build/concurrent build/match build/check

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

test: build/tests build/schedule build/concurrent build/match build/check
	./build/check
	./build/match
	./build/tests
	./build/schedule
	./build/concurrent
	CUBICAL_WORKERS=4 ./build/tests
	CUBICAL_WORKERS=4 ./build/schedule
	CUBICAL_WORKERS=4 ./build/check

tsan: 
	@mkdir -p build/tsan
	for f in $(SRC) tests/test_main.c tests/test_schedule.c tests/test_concurrent.c tests/test_check.c; do $(CC) -std=c11 -O1 -g -pthread -fsanitize=thread -c -o build/tsan/$$(basename $$f .c).o $$f || exit 1; done
	$(CC) -pthread -fsanitize=thread -o build/tsan/tests $$(ls build/tsan/*.o | grep -v test_schedule | grep -v test_concurrent | grep -v test_check)
	$(CC) -pthread -fsanitize=thread -o build/tsan/schedule $$(ls build/tsan/*.o | grep -v test_main | grep -v test_concurrent | grep -v test_check)
	$(CC) -pthread -fsanitize=thread -o build/tsan/concurrent $$(ls build/tsan/*.o | grep -v test_main | grep -v test_schedule | grep -v test_check)
	$(CC) -pthread -fsanitize=thread -o build/tsan/check $$(ls build/tsan/*.o | grep -v test_main | grep -v test_schedule | grep -v test_concurrent)
	CUBICAL_WORKERS=4 ./build/tsan/tests && CUBICAL_WORKERS=4 ./build/tsan/schedule && ./build/tsan/concurrent && CUBICAL_WORKERS=4 ./build/tsan/check

clean:
	rm -f src/*.o tests/*.o
	rm -rf build

.PHONY: all test tsan clean
