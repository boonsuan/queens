# Build and check Spire (see README.md).
#
#   make         build/spire and build/spire-rows
#   make check   compare their output with the Section 7 generator's rows
#   make clean
#
# Needs an x86-64 processor with AVX2 and BMI2, GCC (for OpenMP and the assembly), and
# Python 3 (for the generated headers). The generated headers go in build/ with the programs.

ifeq ($(origin CC),default)
CC = gcc
endif
PYTHON ?= python3
CFLAGS ?= -O3 -march=native
WARN = -Wall -Wextra
X = $(if $(filter Windows_NT,$(OS)),.exe,)
GENERATED = ../fast_generator/generated
SPIRE = spire.c loops.S layout.h $(GENERATED)/tables.h build/records.h

.PHONY: all check clean
all: build/spire$(X) build/spire-rows$(X)

build:
	mkdir -p build

# The 300 paused records, as C tables (checks the counter formulas on the way).
build/records.h: make_records.py $(GENERATED)/paused_records.json $(GENERATED)/tables.h | build
	$(PYTHON) make_records.py $@

# The plan: which states and transitions the tables hold, and where (under a second).
build/spire-plan$(X): $(SPIRE)
	$(CC) $(CFLAGS) -fopenmp $(WARN) -DTRAIN -Ibuild -I$(GENERATED) spire.c loops.S -o $@
build/plan.h: build/spire-plan$(X)
	build/spire-plan$(X) --plan > $@

build/spire$(X): $(SPIRE) build/plan.h
	$(CC) $(CFLAGS) -fopenmp $(WARN) -Ibuild -I$(GENERATED) spire.c loops.S -o $@
build/spire-rows$(X): spire-rows.c $(SPIRE) build/plan.h
	$(CC) $(CFLAGS) -fopenmp $(WARN) -Ibuild -I$(GENERATED) spire-rows.c loops.S -o $@

# The reference: the Section 7 generator, one row at a time.
build/reference$(X): reference.c ../fast_generator/src/queens_fast.c ../fast_generator/src/queens_fast.h $(GENERATED)/tables.h | build
	$(CC) -O3 -std=c11 -DNDEBUG -fwrapv $(WARN) -I../fast_generator/src reference.c ../fast_generator/src/queens_fast.c -o $@

check: build/spire$(X) build/spire-rows$(X) build/reference$(X)
	$(PYTHON) check.py

clean:
	rm -rf build
