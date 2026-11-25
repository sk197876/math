# Build of the DPGPR subproject in an external artifact tree.
# The sources stay here; prepare-build links them into BUILD_DIR, where
# compilation runs. The Federer library is read from its own build tree.
COQMAKEFILE ?= rocq makefile
COQC ?= rocq compile
COQCHK ?= rocqchk
BUILD_DIR ?= /opt/rocq/DPGPR2026-build
BUILD_DIR := $(abspath $(BUILD_DIR))
BUILD_UMASK ?= 0002
SOURCES := $(filter %.v,$(shell cat _CoqProject))
LOADPATH := $(shell grep -E '^-(Q|R) ' _CoqProject)
WARNINGS = -notation-overridden,-ambiguous-paths,-redundant-canonical-projection,-notation-incompatible-prefix
MODULES := $(subst /,.,$(patsubst theories/%.v,DPGPR/%,$(filter theories/%.v,$(SOURCES))))
.DEFAULT_GOAL := all
.PHONY: all prepare-build check audit clean

prepare-build:
	umask $(BUILD_UMASK); python3 -B ../tools/subproject_build.py --build-dir "$(BUILD_DIR)" \
	  --coqmakefile "$(COQMAKEFILE) -docroot DPGPR" prepare

all: prepare-build
	umask $(BUILD_UMASK); $(MAKE) -C "$(BUILD_DIR)" -f Makefile.coq all

# One recursive make shares prerequisites even for several focused targets.
FOCUSED_TARGETS := $(filter %.vo %.vos %.vok %.glob,$(MAKECMDGOALS))
ifneq ($(strip $(FOCUSED_TARGETS)),)
.PHONY: focused-build $(FOCUSED_TARGETS)
$(FOCUSED_TARGETS): focused-build
focused-build: prepare-build
	umask $(BUILD_UMASK); $(MAKE) -C "$(BUILD_DIR)" -f Makefile.coq $(FOCUSED_TARGETS)
endif

# Kernel check of every module of this subproject. The modules of other
# subprojects and of Federer that they load are checked recursively.
check: all
	umask $(BUILD_UMASK); cd "$(BUILD_DIR)" && $(COQCHK) -silent $(LOADPATH) $(MODULES)
	@echo "Kernel check passed."

audit: all
	umask $(BUILD_UMASK); cd "$(BUILD_DIR)" && $(COQC) -w $(WARNINGS) $(LOADPATH) \
	  tests/Assumptions.v > "$(CURDIR)/docs/assumptions.log" 2>&1
	@cat docs/assumptions.log

clean: prepare-build
	umask $(BUILD_UMASK); $(MAKE) -C "$(BUILD_DIR)" -f Makefile.coq cleanall
