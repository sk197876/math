COQMAKEFILE ?= rocq makefile
COQC ?= rocq compile
COQCHK ?= rocqchk
BUILD_DIR ?= $(if $(wildcard .build-dir),$(shell cat .build-dir),_build)
BUILD_DIR := $(abspath $(BUILD_DIR))
export BUILD_DIR
# Preserve llm group write access in the shared external build tree.
BUILD_UMASK ?= 0002
.DEFAULT_GOAL := all
WARNINGS = -notation-overridden,-ambiguous-paths,-redundant-canonical-projection,-notation-incompatible-prefix
LOADPATH = -Q theories Federer -Q tests FedererTests
DOCFLAGS = --utf8 --interpolate --gallina --multi-index --index identifiers \
  --title "Federer-Rocq: Geometric Measure Theory in Rocq"

.PHONY: all clean check audit doc prepare-build migrate-build

all: prepare-build
	umask $(BUILD_UMASK); $(MAKE) -C "$(BUILD_DIR)" -f Makefile.coq all

prepare-build:
	umask $(BUILD_UMASK); python3 -B tools/build_tree.py --build-dir "$(BUILD_DIR)" $(if $(ADOPT),--adopt) prepare
	umask $(BUILD_UMASK); cd "$(BUILD_DIR)" && if [ ! -f Makefile.coq ] || [ _CoqProject -nt Makefile.coq ]; then \
	  $(COQMAKEFILE) -f _CoqProject -docroot Federer -o Makefile.coq; fi

migrate-build:
	umask $(BUILD_UMASK); python3 -B tools/build_tree.py --build-dir "$(BUILD_DIR)" migrate

# One recursive make shares prerequisites even for several focused targets.
FOCUSED_TARGETS := $(filter %.vo %.vos %.vok %.glob,$(MAKECMDGOALS))
ifneq ($(strip $(FOCUSED_TARGETS)),)
.PHONY: focused-build $(FOCUSED_TARGETS)
$(FOCUSED_TARGETS): focused-build
focused-build: prepare-build
	umask $(BUILD_UMASK); $(MAKE) -C "$(BUILD_DIR)" -f Makefile.coq $(FOCUSED_TARGETS)
endif

clean: prepare-build
	umask $(BUILD_UMASK); $(MAKE) -C "$(BUILD_DIR)" -f Makefile.coq cleanall
	umask $(BUILD_UMASK); rm -rf "$(BUILD_DIR)/html"
	umask $(BUILD_UMASK); cd "$(BUILD_DIR)/tests" && rm -f Assumptions.vo Assumptions.vos Assumptions.vok Assumptions.glob .Assumptions.aux

check: all
	umask $(BUILD_UMASK); cd "$(BUILD_DIR)" && $(COQCHK) -silent $(LOADPATH) Federer.GrassmannSpaces Federer.TensorFamily Federer.MeasureTheory Federer.Rectifiability FedererTests.Examples FedererTests.GradedExamples FedererTests.SignedExamples FedererTests.ExteriorExamples FedererTests.MeasureExamples FedererTests.CoveringExamples FedererTests.DerivationExamples FedererTests.CaratheodoryExamples FedererTests.DifferentialExamples FedererTests.InverseFunctionExamples FedererTests.BrunnMinkowskiExamples FedererTests.BoundaryLayerVolumeExamples FedererTests.IsoperimetricExamples FedererTests.RectifiableBoundaryIsoperimetricExamples FedererTests.RiemannianTransformationExamples FedererTests.SphericalOrthogonalExamples FedererTests.SphericalKinematicExamples FedererTests.StructureConeExamples FedererTests.StructureDensityExamples FedererTests.StructureFibreExamples FedererTests.StructureTrichotomyExamples FedererTests.StructureConeSectionExamples FedererTests.StructurePureConeExamples FedererTests.StructureProjectionMassExamples FedererTests.StructureZeroGrowthExamples FedererTests.StructureInfiniteProjectionExamples FedererTests.StructurePureStructureExamples FedererTests.StructureProjectionDecompositionExamples FedererTests.StructureHausdorffStructureExamples FedererTests.StructureInfinityRectifiabilityExamples FedererTests.StructurePositiveDensityExamples FedererTests.StructureGeometricReplacementExamples FedererTests.StructureSmallConeExamples FedererTests.StructureMeasureRectifiableExamples FedererTests.CircularDiscExampleExamples FedererTests.BinaryCantorSquareExamples FedererTests.DivergingCantorSquareExamples FedererTests.CriticalValueProblemExamples FedererTests.CriticalValueEstimatesExamples FedererTests.CriticalValueUpperExamples FedererTests.CriticalValueSharpnessExamples FedererTests.AnalyticGermExamples FedererTests.WeierstrassExamples
	@echo "Kernel check passed."

audit: all
	umask $(BUILD_UMASK); cd "$(BUILD_DIR)" && $(COQC) -w $(WARNINGS) $(LOADPATH) tests/Assumptions.v > "$(CURDIR)/docs/assumptions.log" 2>&1
	@umask $(BUILD_UMASK); cat docs/assumptions.log

doc: all
	umask $(BUILD_UMASK); rm -rf "$(BUILD_DIR)/html"
	umask $(BUILD_UMASK); $(MAKE) -C "$(BUILD_DIR)" -f Makefile.coq html COQDOCFLAGS='$(DOCFLAGS)'
	umask $(BUILD_UMASK); python3 -B tools/coqdoc_index.py
