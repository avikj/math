CC      ?= gcc
CFLAGS  ?= -std=gnu11 -O2 -g -Wall -Wextra -Wno-unused-parameter
SAN     := -fsanitize=address,undefined -fno-omit-frame-pointer

SRC := src/dnf.c src/net.c src/lang.c

all: build/cubical

build/cubical: $(SRC) src/core.h
	@mkdir -p build
	$(CC) $(CFLAGS) -o $@ $(SRC)

build/cubical-asan: $(SRC) src/core.h
	@mkdir -p build
	$(CC) $(CFLAGS) $(SAN) -o $@ $(SRC)

test: build/cubical build/cubical-asan
	./build/cubical lib/prelude.ctt tests/cubical.ctt
	ASAN_OPTIONS=detect_leaks=0 ./build/cubical-asan lib/prelude.ctt tests/cubical.ctt > /dev/null

clean:
	rm -rf build
