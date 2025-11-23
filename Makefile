# ==============================================================================
# NVIDIA GPU Interconnect NoC Verification - Makefile
# SystemVerilog UVM Verification Environment
# ==============================================================================
#
# This Makefile provides targets for compiling, simulating, and analyzing
# the NoC verification testbench using VCS or Questa simulators.
#
# Usage:
#   make help              - Display this help message
#   make compile           - Compile the design and testbench
#   make sim_simple        - Run simple directed test
#   make sim_random        - Run random constrained test
#   make sim_stress        - Run stress test with high traffic
#   make sim_formal        - Run formal verification (if supported)
#   make coverage_report   - Generate coverage report
#   make clean             - Remove all generated files
#
# ==============================================================================

# ==============================================================================
# Configuration Variables
# ==============================================================================

# Simulator selection: vcs, questa, xcelium
SIMULATOR ?= vcs

# Test selection: simple, random, stress, formal
TEST ?= simple

# Coverage options: yes, no
COVERAGE ?= yes

# Debug verbosity: UVM_NONE, UVM_LOW, UVM_MEDIUM, UVM_HIGH, UVM_FULL, UVM_DEBUG
UVM_VERBOSITY ?= UVM_MEDIUM

# Seed for randomization (0 = random seed)
SEED ?= 0

# Number of test iterations
ITERATIONS ?= 1

# Timeout in simulation time units
TIMEOUT ?= 1000000

# ==============================================================================
# Directory Structure
# ==============================================================================

# Source directories
RTL_DIR        := rtl
TB_DIR         := tb
PKG_DIR        := pkg
TEST_DIR       := tests
CONFIG_DIR     := config

# Output directories
BUILD_DIR      := build
LOG_DIR        := logs
COV_DIR        := coverage
WAVE_DIR       := waves
REPORT_DIR     := reports

# ==============================================================================
# File Lists
# ==============================================================================

# RTL source files (add your RTL files here)
RTL_FILES      := $(wildcard $(RTL_DIR)/*.sv) \
                  $(wildcard $(RTL_DIR)/*.v)

# Testbench files
TB_FILES       := $(wildcard $(TB_DIR)/**/*.sv) \
                  $(wildcard $(TB_DIR)/*.sv)

# Package files
PKG_FILES      := $(wildcard $(PKG_DIR)/*.sv) \
                  $(wildcard $(PKG_DIR)/*.svh)

# Test files
TEST_FILES     := $(wildcard $(TEST_DIR)/*.sv)

# All source files
ALL_FILES      := $(RTL_FILES) $(TB_FILES) $(PKG_FILES) $(TEST_FILES)

# ==============================================================================
# Simulator-Specific Configuration
# ==============================================================================

# VCS (Synopsys) options
VCS_OPTS       := -full64 \
                  -sverilog \
                  -ntb_opts uvm-1.2 \
                  +incdir+$(PKG_DIR) \
                  +incdir+$(TB_DIR) \
                  +incdir+$(RTL_DIR) \
                  +incdir+$(TEST_DIR) \
                  -timescale=1ns/1ps \
                  -l $(LOG_DIR)/compile.log \
                  -o $(BUILD_DIR)/simv

# VCS coverage options
# Note: Do not specify -cm_dir at compile time since TEST/SEED are simulation-time parameters
# The -cm_dir is specified at simulation time (in VCS_SIM_COV_OPTS) to avoid directory mismatch
# Coverage from multiple test runs will be merged using urg tool in coverage_report target
VCS_COV_OPTS   := -cm line+cond+fsm+branch+tgl

# VCS simulation options
# Note: Coverage options are added conditionally based on COVERAGE variable
# Coverage instrumentation must be enabled at compile time for simulation coverage to work
VCS_SIM_OPTS   := +UVM_VERBOSITY=$(UVM_VERBOSITY) \
                  +UVM_TESTNAME=$(TEST) \
                  +ntb_random_seed=$(SEED) \
                  -l $(LOG_DIR)/sim_$(TEST)_$(SEED).log
# Coverage options added conditionally - only if COVERAGE=yes
VCS_SIM_COV_OPTS := -cm line+cond+fsm+branch+tgl \
                    -cm_dir $(COV_DIR)/$(TEST)_$(SEED)

# Questa (Mentor Graphics) options
QUESTA_OPTS    := -64 \
                  -sv \
                  -work work \
                  +incdir+$(PKG_DIR) \
                  +incdir+$(TB_DIR) \
                  +incdir+$(RTL_DIR) \
                  +incdir+$(TEST_DIR) \
                  -timescale 1ns/1ps \
                  -l $(LOG_DIR)/compile.log

# Questa coverage options
QUESTA_COV_OPTS := +cover=cfst \
                   -coverage \
                   -coveroptions coverstore

# Questa simulation options
# Note: Coverage options are added conditionally based on COVERAGE variable
# Coverage instrumentation must be enabled at compile time for simulation coverage to work
QUESTA_SIM_OPTS := -voptargs="+acc" \
                   +UVM_VERBOSITY=$(UVM_VERBOSITY) \
                   +UVM_TESTNAME=$(TEST) \
                   +ntb_random_seed=$(SEED) \
                   -l $(LOG_DIR)/sim_$(TEST)_$(SEED).log
# Coverage options added conditionally - only if COVERAGE=yes
QUESTA_SIM_COV_OPTS := -coverage \
                       -voptargs="+cover=cfst"

# ==============================================================================
# Default Target
# ==============================================================================

.PHONY: all
all: help

# ==============================================================================
# Help Target
# ==============================================================================

.PHONY: help
help:
	@echo "=============================================================================="
	@echo "NVIDIA GPU Interconnect NoC Verification - Makefile"
	@echo "=============================================================================="
	@echo ""
	@echo "Available targets:"
	@echo "  compile           - Compile design and testbench (SIMULATOR=$(SIMULATOR))"
	@echo "  sim_simple        - Run simple directed test"
	@echo "  sim_random        - Run random constrained test"
	@echo "  sim_stress        - Run stress test with high traffic"
	@echo "  sim_formal        - Run formal verification"
	@echo "  coverage_report   - Generate coverage report"
	@echo "  clean             - Remove all generated files"
	@echo "  help              - Display this help message"
	@echo ""
	@echo "Configuration variables:"
	@echo "  SIMULATOR         - Simulator: vcs, questa, xcelium (default: vcs)"
	@echo "  TEST              - Test name: simple, random, stress (default: simple)"
	@echo "  COVERAGE          - Enable coverage: yes, no (default: yes)"
	@echo "  UVM_VERBOSITY     - UVM verbosity level (default: UVM_MEDIUM)"
	@echo "  SEED              - Random seed (0 = random, default: 0)"
	@echo "  ITERATIONS        - Number of test iterations (default: 1)"
	@echo ""
	@echo "Examples:"
	@echo "  make compile                    # Compile with default settings"
	@echo "  make sim_random SEED=42        # Run random test with seed 42"
	@echo "  make sim_stress COVERAGE=yes   # Run stress test with coverage"
	@echo "  make SIMULATOR=questa compile  # Compile with Questa"
	@echo ""

# ==============================================================================
# Directory Creation
# ==============================================================================

$(BUILD_DIR) $(LOG_DIR) $(COV_DIR) $(WAVE_DIR) $(REPORT_DIR):
	@mkdir -p $@

# ==============================================================================
# Compilation Targets
# ==============================================================================

.PHONY: compile
compile: $(BUILD_DIR) $(LOG_DIR) $(COV_DIR)
	@echo "=============================================================================="
	@echo "Compiling with $(SIMULATOR)..."
	@echo "=============================================================================="
ifeq ($(SIMULATOR),vcs)
	@which vcs > /dev/null || (echo "Error: VCS not found. Please set up your environment." && exit 1)
	vcs $(VCS_OPTS) $(if $(filter yes,$(COVERAGE)),$(VCS_COV_OPTS),) \
	    $(ALL_FILES) 2>&1 | tee $(LOG_DIR)/compile.log; \
	COMPILE_STATUS=$$?; \
	if [ $$COMPILE_STATUS -eq 0 ]; then \
		echo "Compilation complete. Log: $(LOG_DIR)/compile.log"; \
		echo "$(COVERAGE)" > $(BUILD_DIR)/.coverage_state; \
	else \
		echo "Compilation failed. Log: $(LOG_DIR)/compile.log"; \
		rm -f $(BUILD_DIR)/.coverage_state; \
		exit $$COMPILE_STATUS; \
	fi
else ifeq ($(SIMULATOR),questa)
	@which vlog > /dev/null || (echo "Error: Questa not found. Please set up your environment." && exit 1)
	vlib work
	vlog $(QUESTA_OPTS) $(if $(filter yes,$(COVERAGE)),$(QUESTA_COV_OPTS),) \
	     $(ALL_FILES) 2>&1 | tee $(LOG_DIR)/compile.log; \
	COMPILE_STATUS=$$?; \
	if [ $$COMPILE_STATUS -eq 0 ]; then \
		echo "Compilation complete. Log: $(LOG_DIR)/compile.log"; \
		echo "$(COVERAGE)" > $(BUILD_DIR)/.coverage_state; \
	else \
		echo "Compilation failed. Log: $(LOG_DIR)/compile.log"; \
		rm -f $(BUILD_DIR)/.coverage_state; \
		exit $$COMPILE_STATUS; \
	fi
else
	@echo "Error: Unsupported simulator '$(SIMULATOR)'. Use 'vcs' or 'questa'."
	@exit 1
endif

# ==============================================================================
# Simulation Targets
# ==============================================================================

.PHONY: sim_simple sim_random sim_stress sim_formal

sim_simple: compile
	@# Check coverage consistency: coverage must be enabled at compile time if enabled at simulation time
	@if [ "$(COVERAGE)" = "yes" ]; then \
		if [ ! -f $(BUILD_DIR)/.coverage_state ]; then \
			echo "ERROR: Coverage state file not found. Code may not be compiled with coverage."; \
			echo "       Recompile with: make compile COVERAGE=yes"; \
			exit 1; \
		fi; \
		COMPILED_COV=$$(cat $(BUILD_DIR)/.coverage_state); \
		if [ "$$COMPILED_COV" != "yes" ]; then \
			echo "ERROR: Coverage enabled at simulation (COVERAGE=yes) but code was compiled without coverage."; \
			echo "       Coverage instrumentation must be enabled at compile time. Recompile with: make compile COVERAGE=yes"; \
			exit 1; \
		fi; \
	fi
	@# Set default test name if TEST not specified (allows override via TEST variable)
	@# Note: +UVM_TESTNAME=$$TEST_NAME will override +UVM_TESTNAME=$(TEST) from VCS_SIM_OPTS/QUESTA_SIM_OPTS
	@TEST_NAME=$${TEST:-simple_test}; \
	echo "=============================================================================="; \
	echo "Running simple test (TEST=$$TEST_NAME)..."; \
	echo "=============================================================================="; \
	if [ "$(SIMULATOR)" = "vcs" ]; then \
		$(BUILD_DIR)/simv +UVM_TESTNAME=$$TEST_NAME $(VCS_SIM_OPTS) $(if $(filter yes,$(COVERAGE)),$(VCS_SIM_COV_OPTS),); \
	elif [ "$(SIMULATOR)" = "questa" ]; then \
		vsim -c -do "run -all; quit -f" work.top +UVM_TESTNAME=$$TEST_NAME $(QUESTA_SIM_OPTS) $(if $(filter yes,$(COVERAGE)),$(QUESTA_SIM_COV_OPTS),); \
	fi
	@echo "Simulation complete. Log: $(LOG_DIR)/sim_simple_$(SEED).log"

sim_random: compile
	@# Check coverage consistency: coverage must be enabled at compile time if enabled at simulation time
	@if [ "$(COVERAGE)" = "yes" ]; then \
		if [ ! -f $(BUILD_DIR)/.coverage_state ]; then \
			echo "ERROR: Coverage state file not found. Code may not be compiled with coverage."; \
			echo "       Recompile with: make compile COVERAGE=yes"; \
			exit 1; \
		fi; \
		COMPILED_COV=$$(cat $(BUILD_DIR)/.coverage_state); \
		if [ "$$COMPILED_COV" != "yes" ]; then \
			echo "ERROR: Coverage enabled at simulation (COVERAGE=yes) but code was compiled without coverage."; \
			echo "       Coverage instrumentation must be enabled at compile time. Recompile with: make compile COVERAGE=yes"; \
			exit 1; \
		fi; \
	fi
	@# Set default test name if TEST not specified (allows override via TEST variable)
	@# Note: +UVM_TESTNAME=$$TEST_NAME will override +UVM_TESTNAME=$(TEST) from VCS_SIM_OPTS/QUESTA_SIM_OPTS
	@TEST_NAME=$${TEST:-random_test}; \
	echo "=============================================================================="; \
	echo "Running random test (TEST=$$TEST_NAME, seed=$(SEED))..."; \
	echo "=============================================================================="; \
	if [ "$(SIMULATOR)" = "vcs" ]; then \
		$(BUILD_DIR)/simv +UVM_TESTNAME=$$TEST_NAME $(VCS_SIM_OPTS) $(if $(filter yes,$(COVERAGE)),$(VCS_SIM_COV_OPTS),); \
	elif [ "$(SIMULATOR)" = "questa" ]; then \
		vsim -c -do "run -all; quit -f" work.top +UVM_TESTNAME=$$TEST_NAME $(QUESTA_SIM_OPTS) $(if $(filter yes,$(COVERAGE)),$(QUESTA_SIM_COV_OPTS),); \
	fi
	@echo "Simulation complete. Log: $(LOG_DIR)/sim_random_$(SEED).log"

sim_stress: compile
	@# Check coverage consistency: coverage must be enabled at compile time if enabled at simulation time
	@if [ "$(COVERAGE)" = "yes" ]; then \
		if [ ! -f $(BUILD_DIR)/.coverage_state ]; then \
			echo "ERROR: Coverage state file not found. Code may not be compiled with coverage."; \
			echo "       Recompile with: make compile COVERAGE=yes"; \
			exit 1; \
		fi; \
		COMPILED_COV=$$(cat $(BUILD_DIR)/.coverage_state); \
		if [ "$$COMPILED_COV" != "yes" ]; then \
			echo "ERROR: Coverage enabled at simulation (COVERAGE=yes) but code was compiled without coverage."; \
			echo "       Coverage instrumentation must be enabled at compile time. Recompile with: make compile COVERAGE=yes"; \
			exit 1; \
		fi; \
	fi
	@# Set default test name if TEST not specified (allows override via TEST variable)
	@# Note: +UVM_TESTNAME=$$TEST_NAME will override +UVM_TESTNAME=$(TEST) from VCS_SIM_OPTS/QUESTA_SIM_OPTS
	@TEST_NAME=$${TEST:-stress_test}; \
	echo "=============================================================================="; \
	echo "Running stress test (TEST=$$TEST_NAME)..."; \
	echo "=============================================================================="; \
	if [ "$(SIMULATOR)" = "vcs" ]; then \
		$(BUILD_DIR)/simv +UVM_TESTNAME=$$TEST_NAME TIMEOUT=$(TIMEOUT) $(VCS_SIM_OPTS) $(if $(filter yes,$(COVERAGE)),$(VCS_SIM_COV_OPTS),); \
	elif [ "$(SIMULATOR)" = "questa" ]; then \
		vsim -c -do "run -all; quit -f" work.top +UVM_TESTNAME=$$TEST_NAME TIMEOUT=$(TIMEOUT) $(QUESTA_SIM_OPTS) $(if $(filter yes,$(COVERAGE)),$(QUESTA_SIM_COV_OPTS),); \
	fi
	@echo "Simulation complete. Log: $(LOG_DIR)/sim_stress_$(SEED).log"

sim_formal: compile
	@echo "=============================================================================="
	@echo "Running formal verification..."
	@echo "=============================================================================="
	@echo "Note: Formal verification requires additional setup and tools."
	@echo "This is a placeholder target. Implement based on your formal tool."
	@echo "Formal verification not yet implemented."

# ==============================================================================
# Coverage Report Target
# ==============================================================================

.PHONY: coverage_report
coverage_report: $(REPORT_DIR)
	@echo "=============================================================================="
	@echo "Generating coverage report..."
	@echo "=============================================================================="
ifeq ($(SIMULATOR),vcs)
	@which dve > /dev/null || (echo "Error: DVE not found." && exit 1)
	urg -full64 -dir $(COV_DIR)/* -report $(REPORT_DIR)/coverage_report \
	    -format both -log $(LOG_DIR)/coverage.log
	@echo "Coverage report generated: $(REPORT_DIR)/coverage_report"
	@echo "Open with: dve -full64 -cov -covdir $(COV_DIR)"
else ifeq ($(SIMULATOR),questa)
	vcover merge $(COV_DIR)/merged.ucdb $(COV_DIR)/*.ucdb
	vcover report -html -htmldir $(REPORT_DIR)/coverage_html $(COV_DIR)/merged.ucdb
	@echo "Coverage report generated: $(REPORT_DIR)/coverage_html/index.html"
	@echo "Open with: vsim -viewcov $(COV_DIR)/merged.ucdb"
else
	@echo "Error: Coverage report not supported for simulator '$(SIMULATOR)'."
endif

# ==============================================================================
# Clean Targets
# ==============================================================================

.PHONY: clean
clean:
	@echo "=============================================================================="
	@echo "Cleaning generated files..."
	@echo "=============================================================================="
	rm -rf $(BUILD_DIR)
	rm -rf $(LOG_DIR)
	rm -rf $(COV_DIR)
	rm -rf $(WAVE_DIR)
	rm -rf $(REPORT_DIR)
	rm -rf work
	rm -rf csrc
	rm -rf simv simv.daidir
	rm -rf *.vpd *.vcd *.fsdb *.wlf *.wdb
	rm -rf *.log *.key
	rm -rf .vcs_lib_lock
	rm -rf modelsim.ini
	rm -rf transcript
	@echo "Clean complete."

.PHONY: distclean
distclean: clean
	@echo "=============================================================================="
	@echo "Deep cleaning (including backups)..."
	@echo "=============================================================================="
	find . -type f -name "*.bak" -delete
	find . -type f -name "*.backup" -delete
	find . -type f -name "*~" -delete
	@echo "Deep clean complete."

# ==============================================================================
# Utility Targets
# ==============================================================================

.PHONY: check-env
check-env:
	@echo "=============================================================================="
	@echo "Checking environment..."
	@echo "=============================================================================="
	@echo "Simulator: $(SIMULATOR)"
ifeq ($(SIMULATOR),vcs)
	@which vcs && echo "VCS: Found" || echo "VCS: Not found"
	@which dve && echo "DVE: Found" || echo "DVE: Not found"
else ifeq ($(SIMULATOR),questa)
	@which vlog && echo "vlog: Found" || echo "vlog: Not found"
	@which vsim && echo "vsim: Found" || echo "vsim: Not found"
endif
	@echo "Coverage: $(COVERAGE)"
	@echo "UVM Verbosity: $(UVM_VERBOSITY)"

.PHONY: list-tests
list-tests:
	@echo "=============================================================================="
	@echo "Available test files:"
	@echo "=============================================================================="
	@ls -1 $(TEST_DIR)/*.sv 2>/dev/null || echo "No test files found in $(TEST_DIR)"

# ==============================================================================
# End of Makefile
# ==============================================================================

