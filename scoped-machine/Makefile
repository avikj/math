CC      ?= gcc
CFLAGS  ?= -std=c11 -O1 -g -Wall -Wextra -Wno-unused-parameter -fsanitize=address,undefined -fno-omit-frame-pointer -pthread
LDFLAGS ?= -fsanitize=address,undefined -pthread

SRC := src/intern.c src/dnf.c src/machine.c src/interval.c src/face.c src/term.c src/eval.c src/lib.c src/net.c src/canon.c
OBJ := $(SRC:.c=.o)

all: build/tests build/schedule build/concurrent

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

test: build/tests build/schedule build/concurrent
	./build/tests
	./build/schedule
	./build/concurrent
	CUBICAL_WORKERS=4 ./build/tests
	CUBICAL_WORKERS=4 ./build/schedule

tsan: 
	@mkdir -p build/tsan
	for f in $(SRC) tests/test_main.c tests/test_schedule.c tests/test_concurrent.c; do $(CC) -std=c11 -O1 -g -pthread -fsanitize=thread -c -o build/tsan/$$(basename $$f .c).o $$f || exit 1; done
	$(CC) -pthread -fsanitize=thread -o build/tsan/tests $$(ls build/tsan/*.o | grep -v test_schedule | grep -v test_concurrent)
	$(CC) -pthread -fsanitize=thread -o build/tsan/schedule $$(ls build/tsan/*.o | grep -v test_main | grep -v test_concurrent)
	$(CC) -pthread -fsanitize=thread -o build/tsan/concurrent $$(ls build/tsan/*.o | grep -v test_main | grep -v test_schedule)
	CUBICAL_WORKERS=4 ./build/tsan/tests && CUBICAL_WORKERS=4 ./build/tsan/schedule && ./build/tsan/concurrent

clean:
	rm -f src/*.o tests/*.o
	rm -rf build

.PHONY: all test tsan clean
