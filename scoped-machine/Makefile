CC      ?= gcc
CFLAGS  ?= -std=gnu11 -O2 -g -Wall -Wextra -Wno-unused-parameter
SAN     := -fsanitize=address,undefined -fno-omit-frame-pointer

SRC := src/dnf.c src/net.c src/lang.c

all: build/cubical

build/cubical: $(SRC) src/core.h
	@mkdir -p build
	$(CC) $(CFLAGS) -o $@ $(SRC) -lpthread

build/cubical-asan: $(SRC) src/core.h
	@mkdir -p build
	$(CC) $(CFLAGS) $(SAN) -o $@ $(SRC) -lpthread

test: build/cubical build/cubical-asan
	./build/cubical lib/prelude.ctt tests/cubical.ctt
	./build/cubical lib/prelude.ctt lib/code.ctt tests/code.ctt
	./build/cubical lib/prelude.ctt tests/identity.ctt
	./build/cubical lib/prelude.ctt tests/hit.ctt
	./build/cubical lib/prelude.ctt lib/code.ctt lib/check.ctt tests/check.ctt
	./build/cubical lib/prelude.ctt lib/code.ctt lib/check.ctt lib/std.ctt
	CUBICAL_WORKERS=4 ./build/cubical lib/prelude.ctt tests/identity.ctt > /dev/null
	CUBICAL_WORKERS=4 ./build/cubical lib/prelude.ctt tests/hit.ctt > /dev/null
	CUBICAL_WORKERS=4 ./build/cubical lib/prelude.ctt lib/code.ctt lib/check.ctt tests/check.ctt > /dev/null
	CUBICAL_WORKERS=4 ./build/cubical lib/prelude.ctt tests/cubical.ctt > /dev/null
	CUBICAL_WORKERS=4 ./build/cubical lib/prelude.ctt lib/code.ctt tests/code.ctt > /dev/null
	ASAN_OPTIONS=detect_leaks=0 ./build/cubical-asan lib/prelude.ctt tests/cubical.ctt > /dev/null
	ASAN_OPTIONS=detect_leaks=0 ./build/cubical-asan lib/prelude.ctt lib/code.ctt tests/code.ctt > /dev/null
	ASAN_OPTIONS=detect_leaks=0 ./build/cubical-asan lib/prelude.ctt tests/identity.ctt > /dev/null
	ASAN_OPTIONS=detect_leaks=0 ./build/cubical-asan lib/prelude.ctt tests/hit.ctt > /dev/null
	ASAN_OPTIONS=detect_leaks=0 ./build/cubical-asan lib/prelude.ctt lib/code.ctt lib/check.ctt tests/check.ctt > /dev/null

# the checked library and the acceptance tests (the paper's terms, 9.15's sorting): long, run once
library: build/cubical
	./build/cubical lib/prelude.ctt lib/code.ctt lib/check.ctt lib/std.ctt tests/boxes.ctt
	./build/cubical lib/prelude.ctt lib/code.ctt lib/check.ctt lib/std.ctt tests/sort.ctt

build/cubical-tsan: $(SRC) src/core.h
	@mkdir -p build
	$(CC) -std=gnu11 -O1 -g -fsanitize=thread -o $@ $(SRC) -lpthread

tsan: build/cubical-tsan
	CUBICAL_WORKERS=4 TSAN_OPTIONS=halt_on_error=1 ./build/cubical-tsan lib/prelude.ctt tests/cubical.ctt > /dev/null
	CUBICAL_WORKERS=4 TSAN_OPTIONS=halt_on_error=1 ./build/cubical-tsan lib/prelude.ctt lib/code.ctt tests/code.ctt > /dev/null
	CUBICAL_WORKERS=4 TSAN_OPTIONS=halt_on_error=1 ./build/cubical-tsan lib/prelude.ctt tests/identity.ctt > /dev/null
	CUBICAL_WORKERS=4 TSAN_OPTIONS=halt_on_error=1 ./build/cubical-tsan lib/prelude.ctt tests/hit.ctt > /dev/null
	CUBICAL_WORKERS=4 TSAN_OPTIONS=halt_on_error=1 ./build/cubical-tsan lib/prelude.ctt lib/code.ctt lib/check.ctt tests/check.ctt > /dev/null

clean:
	rm -rf build
