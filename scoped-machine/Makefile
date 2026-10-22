CC      ?= gcc
CFLAGS  ?= -std=gnu11 -O2 -g -Wall -Wextra -Wno-unused-parameter
SAN     := -fsanitize=address,undefined -fno-omit-frame-pointer

LIBSRC := src/dnf.c src/big.c src/net.c src/lang.c
SRC := $(LIBSRC) src/main.c

all: build/cubical build/libcubical.a

build/cubical: $(SRC) src/core.h
	@mkdir -p build
	$(CC) $(CFLAGS) -o $@ $(SRC) -lpthread

build/cubical-asan: $(SRC) src/core.h
	@mkdir -p build
	$(CC) $(CFLAGS) $(SAN) -o $@ $(SRC) -lpthread

# the machine as a library (include/cubical.h), and a host program using it
build/libcubical.a: $(LIBSRC) src/core.h include/cubical.h
	@mkdir -p build/obj
	for f in $(LIBSRC); do $(CC) $(CFLAGS) -fPIC -c $$f -o build/obj/$$(basename $$f .c).o || exit 1; done
	ar rcs $@ build/obj/dnf.o build/obj/big.o build/obj/net.o build/obj/lang.o

build/embed: examples/embed.c build/libcubical.a include/cubical.h
	$(CC) $(CFLAGS) -Iinclude -o $@ examples/embed.c build/libcubical.a -lpthread

# tests check: the module cache is off, except in the cache test (a fresh directory, run twice)
test: export CUBICAL_NOCACHE = 1
test: build/cubical build/cubical-asan build/embed
	./build/cubical lib/prelude.ctt tests/cubical.ctt
	./build/cubical lib/prelude.ctt lib/code.ctt tests/code.ctt
	./build/cubical lib/prelude.ctt tests/identity.ctt
	./build/cubical lib/prelude.ctt tests/hit.ctt
	./build/cubical lib/prelude.ctt lib/code.ctt lib/check.ctt tests/check.ctt
	./build/cubical lib/prelude.ctt lib/code.ctt lib/check.ctt lib/std.ctt tests/reject.ctt tests/implicit.ctt
	./build/embed | diff - examples/embed.out
	rm -rf build/cache-test
	env -u CUBICAL_NOCACHE CUBICAL_CACHE=build/cache-test ./build/cubical lib/prelude.ctt lib/code.ctt lib/check.ctt lib/std.ctt tests/mod/main.ctt | tail -1
	env -u CUBICAL_NOCACHE CUBICAL_CACHE=build/cache-test ./build/cubical lib/prelude.ctt lib/code.ctt lib/check.ctt lib/std.ctt tests/mod/main.ctt | grep -c "^cached: " | grep -qx 6
	CUBICAL_WORKERS=4 ./build/cubical lib/prelude.ctt tests/identity.ctt > /dev/null
	CUBICAL_WORKERS=4 ./build/cubical lib/prelude.ctt lib/code.ctt lib/check.ctt lib/std.ctt tests/implicit.ctt > /dev/null
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
library: export CUBICAL_NOCACHE = 1
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
