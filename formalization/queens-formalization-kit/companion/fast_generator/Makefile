# Build and check the table-driven greedy-queen generator (Section 7).
#
#   make            build/queens_fast and build/knuth_packed
#   make verify     rebuild the table in memory and compare it with generated/,
#                   then replay every local case and four-input path in C
#   make test       compare coordinates with independent calculations and
#                   test the C interface
#   make sanitize   AddressSanitizer/UBSan builds of the CLI and the API test
#   make regen      rewrite generated/ from ../verification/history.json
#
# Release builds use CFLAGS; the test builds keep assertions enabled.

CC ?= cc
PYTHON ?= python3
CFLAGS ?= -O3 -std=c11 -DNDEBUG -fwrapv
WARN = -Wall -Wextra -Wpedantic
DEBUG_FLAGS = -O2 -g -std=c11
SANITIZE_FLAGS = -O1 -g -std=c11 -fsanitize=address,undefined -fno-omit-frame-pointer
GENERATOR = src/queens_fast.c src/queens_fast.h generated/tables.h
CLI = src/queens_fast.c src/main.c

.PHONY: all debug sanitize verify test regen clean
all: build/queens_fast build/knuth_packed

build:
	mkdir -p build

# The generator and the packed Knuth comparator, built alike (Section 7.5).
build/queens_fast: $(GENERATOR) src/main.c | build
	$(CC) $(CFLAGS) $(WARN) $(CLI) -o $@
build/knuth_packed: knuth/knuth_packed.c | build
	$(CC) $(CFLAGS) $(WARN) $< -o $@

# Test builds: assertions enabled; a buffer budget of one byte for every copy;
# the separate local-rule implementation; the C interface test.
debug: build/queens_debug build/queens_budget1 build/local_rule_reference build/test_api
build/queens_debug: $(GENERATOR) src/main.c | build
	$(CC) $(DEBUG_FLAGS) $(WARN) $(CLI) -o $@
build/queens_budget1: $(GENERATOR) src/main.c | build
	$(CC) $(CFLAGS) $(WARN) -DQF_BUFFER=1 $(CLI) -o $@
build/local_rule_reference: tests/local_rule_reference.c | build
	$(CC) $(CFLAGS) $(WARN) $< -o $@
build/test_api: tests/test_api.c $(GENERATOR) | build
	$(CC) $(DEBUG_FLAGS) $(WARN) src/queens_fast.c tests/test_api.c -o $@

sanitize: build/queens_sanitize build/test_api_sanitize
build/queens_sanitize: $(GENERATOR) src/main.c | build
	$(CC) $(SANITIZE_FLAGS) $(WARN) $(CLI) -o $@
build/test_api_sanitize: tests/test_api.c $(GENERATOR) | build
	$(CC) $(SANITIZE_FLAGS) $(WARN) src/queens_fast.c tests/test_api.c -o $@

# Finite checks of the table against the separate local-rule implementation.
build/check_local_steps: tests/check_local_steps.c tests/local_rule_reference.c | build
	$(CC) $(DEBUG_FLAGS) $(WARN) $< -o $@
build/check_table_paths: tests/check_table_paths.c tests/local_rule_reference.c generated/tables.h | build
	$(CC) $(DEBUG_FLAGS) $(WARN) $< -o $@

verify: build/check_local_steps build/check_table_paths
	$(PYTHON) tools/build_tables.py --check
	build/check_local_steps generated/local_cases.txt
	build/check_table_paths generated/block_cases.txt

test: all debug
	$(PYTHON) tests/check_coordinates.py --count 1000000
	build/test_api

regen:
	$(PYTHON) tools/build_tables.py

# Measurement tools: the native benchmark launcher (Linux) and the scanner of
# Knuth's ranges (needs 128-bit integers, as in GCC and Clang).
build/benchmark_native: bench/benchmark_native.c | build
	$(CC) -O2 -std=c11 $(WARN) $< -o $@
build/scan_bounds: src/scan_bounds.c src/bounds_exact.h $(GENERATOR) | build
	$(CC) $(CFLAGS) $(WARN) src/queens_fast.c src/scan_bounds.c -lm -o $@

clean:
	rm -rf build
