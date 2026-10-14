CC      ?= gcc
CFLAGS  ?= -std=c11 -O1 -g -Wall -Wextra -Wno-unused-parameter -fsanitize=address,undefined -fno-omit-frame-pointer
LDFLAGS ?= -fsanitize=address,undefined

SRC := src/intern.c src/dnf.c src/machine.c src/interval.c src/face.c src/term.c src/eval.c src/lib.c src/net.c src/canon.c
OBJ := $(SRC:.c=.o)

all: build/tests build/schedule

build/tests: $(OBJ) tests/test_main.o
	@mkdir -p build
	$(CC) $(LDFLAGS) -o $@ $^

%.o: %.c src/*.h
	$(CC) $(CFLAGS) -c -o $@ $<

build/schedule: $(OBJ) tests/test_schedule.o
	@mkdir -p build
	$(CC) $(LDFLAGS) -o $@ $^

test: build/tests build/schedule
	./build/tests
	./build/schedule

clean:
	rm -f src/*.o tests/*.o
	rm -rf build

.PHONY: all test clean
