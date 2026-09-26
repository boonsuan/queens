# Build and check Spire (see README.md).
#
#   make         build/spire and build/spire-rows
#   make check   compare their output with the Section 7 generator's rows
#   make clean
#
# Needs a C compiler with OpenMP (GCC; on macOS, Apple's clang with Homebrew's libomp) and
# Python 3 (for the generated headers). The generated headers go in build/ with the programs.

SYSTEM := $(shell uname -s)
MACHINE := $(shell uname -m)
ifeq ($(origin CC),default)
CC = $(if $(filter Darwin,$(SYSTEM)),clang,gcc)
endif
PYTHON ?= python3
X = $(if $(filter Windows_NT,$(OS)),.exe,)
GENERATED = ../fast_generator/generated

# OpenMP: Apple's clang has none of its own, so it uses Homebrew's libomp (brew install libomp).
ifeq ($(SYSTEM)$(findstring clang,$(CC)),Darwinclang)
LIBOMP := $(shell brew --prefix libomp 2>/dev/null)
OPENMP = -Xpreprocessor -fopenmp -I$(LIBOMP)/include -L$(LIBOMP)/lib -lomp
ifeq ($(wildcard $(LIBOMP)/include/omp.h)$(filter clean,$(MAKECMDGOALS)),)
$(error OpenMP not found: install it with `brew install libomp`)
endif
else
OPENMP = -fopenmp
endif

# On x86-64 the inner loops are the assembly of loops.S (used when the processor has AVX2 and
# BMI2); elsewhere, or with `make PORTABLE=1`, they are the C of loops.c.
ifneq ($(filter x86_64 amd64,$(MACHINE)),)
CFLAGS ?= -O3 -march=native
ASM = $(if $(PORTABLE)$(filter Darwin,$(SYSTEM)),,loops.S)
else
CFLAGS ?= -O3 -mcpu=native
ASM =
endif
DEFINES = $(if $(PORTABLE),-DSPIRE_PORTABLE,)
WARN = -Wall -Wextra
SPIRE = spire.c loops.c loops.S layout.h $(GENERATED)/tables.h build/records.h
BUILD = $(CC) $(CFLAGS) $(WARN) $(DEFINES) -Ibuild -I$(GENERATED)

.PHONY: all check clean
all: build/spire$(X) build/spire-rows$(X)

build:
	mkdir -p build

# The 300 paused records, as C tables (checks the counter formulas on the way).
build/records.h: make_records.py $(GENERATED)/paused_records.json $(GENERATED)/tables.h | build
	$(PYTHON) make_records.py $@

# The plan: which states and transitions the tables hold, and where (under a second).
build/spire-plan$(X): $(SPIRE)
	$(BUILD) -DTRAIN spire.c $(ASM) $(OPENMP) -o $@
build/plan.h: build/spire-plan$(X)
	build/spire-plan$(X) --plan > $@

build/spire$(X): $(SPIRE) build/plan.h
	$(BUILD) spire.c $(ASM) $(OPENMP) -o $@
build/spire-rows$(X): spire-rows.c $(SPIRE) build/plan.h
	$(BUILD) spire-rows.c $(ASM) $(OPENMP) -o $@

# The reference: the Section 7 generator, one row at a time.
build/reference$(X): reference.c ../fast_generator/src/queens_fast.c ../fast_generator/src/queens_fast.h $(GENERATED)/tables.h | build
	$(CC) -O3 -std=c11 -DNDEBUG -fwrapv $(WARN) -I../fast_generator/src reference.c ../fast_generator/src/queens_fast.c -o $@

check: build/spire$(X) build/spire-rows$(X) build/reference$(X)
	$(PYTHON) check.py

clean:
	rm -rf build
