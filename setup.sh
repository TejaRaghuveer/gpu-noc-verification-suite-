#!/bin/bash
# ==============================================================================
# NVIDIA GPU Interconnect NoC Verification - Environment Setup Script
# SystemVerilog UVM Verification Environment
# ==============================================================================
#
# This script detects and configures the verification environment for VCS or
# Questa simulators. It sets up necessary environment variables and checks
# for required tools.
#
# Usage:
#   source setup.sh              # Setup for auto-detected simulator
#   source setup.sh vcs          # Force VCS setup
#   source setup.sh questa       # Force Questa setup
#
# ==============================================================================

set -e  # Exit on error

# ==============================================================================
# Configuration
# ==============================================================================

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$SCRIPT_DIR"

# Color codes for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# ==============================================================================
# Utility Functions
# ==============================================================================

print_info() {
    echo -e "${BLUE}[INFO]${NC} $1"
}

print_success() {
    echo -e "${GREEN}[SUCCESS]${NC} $1"
}

print_warning() {
    echo -e "${YELLOW}[WARNING]${NC} $1"
}

print_error() {
    echo -e "${RED}[ERROR]${NC} $1"
}

# ==============================================================================
# Simulator Detection Functions
# ==============================================================================

detect_vcs() {
    # Check for VCS (Synopsys)
    if command -v vcs &> /dev/null; then
        VCS_VERSION=$(vcs -ID 2>&1 | head -1 || echo "unknown")
        print_success "VCS detected: $VCS_VERSION"
        return 0
    else
        return 1
    fi
}

detect_questa() {
    # Check for Questa (Mentor Graphics)
    if command -v vlog &> /dev/null && command -v vsim &> /dev/null; then
        QUESTA_VERSION=$(vlog -version 2>&1 | head -1 || echo "unknown")
        print_success "Questa detected: $QUESTA_VERSION"
        return 0
    else
        return 1
    fi
}

detect_xcelium() {
    # Check for Xcelium (Cadence)
    if command -v xrun &> /dev/null; then
        XCELIUM_VERSION=$(xrun -version 2>&1 | head -1 || echo "unknown")
        print_success "Xcelium detected: $XCELIUM_VERSION"
        return 0
    else
        return 1
    fi
}

# ==============================================================================
# Simulator Setup Functions
# ==============================================================================

setup_vcs() {
    print_info "Setting up VCS environment..."
    
    # Check if VCS is available
    if ! detect_vcs; then
        print_error "VCS not found. Please ensure VCS is installed and in PATH."
        print_info "Typical VCS setup:"
        print_info "  source /path/to/vcs/setup.sh"
        return 1
    fi
    
    # Set VCS-specific environment variables
    export SIMULATOR="vcs"
    
    # VCS license (if needed)
    if [ -n "$SNPSLMD_LICENSE_FILE" ]; then
        print_info "VCS license: $SNPSLMD_LICENSE_FILE"
    else
        print_warning "SNPSLMD_LICENSE_FILE not set. License may be required."
    fi
    
    # Set up Synopsys simulation setup file
    if [ -f "$PROJECT_ROOT/synopsys_sim.setup" ]; then
        export SYNOPSYS_SIM_SETUP="$PROJECT_ROOT/synopsys_sim.setup"
        print_info "Using synopsys_sim.setup: $SYNOPSYS_SIM_SETUP"
    fi
    
    # Check for DVE (VCS GUI)
    if command -v dve &> /dev/null; then
        print_success "DVE (VCS GUI) available"
    else
        print_warning "DVE not found. GUI debugging may not be available."
    fi
    
    # Check for Verdi (debugging tool)
    if command -v verdi &> /dev/null; then
        print_success "Verdi available"
        export VERDI_HOME=$(dirname $(dirname $(which verdi)))
    fi
    
    print_success "VCS environment configured"
    return 0
}

setup_questa() {
    print_info "Setting up Questa environment..."
    
    # Check if Questa is available
    if ! detect_questa; then
        print_error "Questa not found. Please ensure Questa is installed and in PATH."
        print_info "Typical Questa setup:"
        print_info "  source /path/to/questa/QUESTA_HOME/setup.sh"
        return 1
    fi
    
    # Set Questa-specific environment variables
    export SIMULATOR="questa"
    
    # Questa license (if needed)
    if [ -n "$MGLS_LICENSE_FILE" ]; then
        print_info "Questa license: $MGLS_LICENSE_FILE"
    else
        print_warning "MGLS_LICENSE_FILE not set. License may be required."
    fi
    
    # Set up Questa ini file
    if [ -f "$PROJECT_ROOT/questa.ini" ]; then
        export QUESTA_INI="$PROJECT_ROOT/questa.ini"
        print_info "Using questa.ini: $QUESTA_INI"
        # Copy to work directory if it doesn't exist
        if [ ! -f "modelsim.ini" ]; then
            cp "$QUESTA_INI" modelsim.ini 2>/dev/null || true
        fi
    fi
    
    # Set Questa work directory
    export QUESTA_WORK="$PROJECT_ROOT/work"
    
    print_success "Questa environment configured"
    return 0
}

setup_xcelium() {
    print_info "Setting up Xcelium environment..."
    
    # Check if Xcelium is available
    if ! detect_xcelium; then
        print_error "Xcelium not found. Please ensure Xcelium is installed and in PATH."
        return 1
    fi
    
    # Set Xcelium-specific environment variables
    export SIMULATOR="xcelium"
    
    # Cadence license (if needed)
    if [ -n "$CDS_LIC_FILE" ]; then
        print_info "Xcelium license: $CDS_LIC_FILE"
    else
        print_warning "CDS_LIC_FILE not set. License may be required."
    fi
    
    print_success "Xcelium environment configured"
    return 0
}

# ==============================================================================
# Common Environment Setup
# ==============================================================================

setup_common() {
    print_info "Setting up common environment variables..."
    
    # Project directories
    export PROJECT_ROOT="$PROJECT_ROOT"
    export RTL_DIR="$PROJECT_ROOT/rtl"
    export TB_DIR="$PROJECT_ROOT/tb"
    export PKG_DIR="$PROJECT_ROOT/pkg"
    export TEST_DIR="$PROJECT_ROOT/tests"
    export CONFIG_DIR="$PROJECT_ROOT/config"
    
    # Output directories
    export BUILD_DIR="$PROJECT_ROOT/build"
    export LOG_DIR="$PROJECT_ROOT/logs"
    export COV_DIR="$PROJECT_ROOT/coverage"
    export WAVE_DIR="$PROJECT_ROOT/waves"
    export REPORT_DIR="$PROJECT_ROOT/reports"
    
    # Create directories if they don't exist
    mkdir -p "$BUILD_DIR" "$LOG_DIR" "$COV_DIR" "$WAVE_DIR" "$REPORT_DIR"
    
    # UVM environment
    export UVM_HOME="${UVM_HOME:-}"
    if [ -z "$UVM_HOME" ]; then
        print_warning "UVM_HOME not set. UVM may be included via simulator options."
    else
        print_info "UVM_HOME: $UVM_HOME"
    fi
    
    # Add project directories to PATH (if needed)
    export PATH="$PROJECT_ROOT/scripts:$PATH"
    
    print_success "Common environment configured"
}

# ==============================================================================
# Main Setup Logic
# ==============================================================================

main() {
    echo "=============================================================================="
    echo "NVIDIA GPU Interconnect NoC Verification - Environment Setup"
    echo "=============================================================================="
    echo ""
    
    # Determine which simulator to use
    REQUESTED_SIM="$1"
    
    if [ -n "$REQUESTED_SIM" ]; then
        # User specified simulator
        print_info "User requested simulator: $REQUESTED_SIM"
        case "$REQUESTED_SIM" in
            vcs)
                if setup_vcs; then
                    SIM_SETUP="vcs"
                else
                    print_error "Failed to setup VCS"
                    return 1
                fi
                ;;
            questa)
                if setup_questa; then
                    SIM_SETUP="questa"
                else
                    print_error "Failed to setup Questa"
                    return 1
                fi
                ;;
            xcelium)
                if setup_xcelium; then
                    SIM_SETUP="xcelium"
                else
                    print_error "Failed to setup Xcelium"
                    return 1
                fi
                ;;
            *)
                print_error "Unknown simulator: $REQUESTED_SIM"
                print_info "Supported simulators: vcs, questa, xcelium"
                return 1
                ;;
        esac
    else
        # Auto-detect simulator
        print_info "Auto-detecting simulator..."
        if detect_vcs; then
            if setup_vcs; then
                SIM_SETUP="vcs"
            fi
        elif detect_questa; then
            if setup_questa; then
                SIM_SETUP="questa"
            fi
        elif detect_xcelium; then
            if setup_xcelium; then
                SIM_SETUP="xcelium"
            fi
        else
            print_error "No supported simulator detected!"
            print_info "Please ensure one of the following is installed and in PATH:"
            print_info "  - VCS (Synopsys)"
            print_info "  - Questa (Mentor Graphics)"
            print_info "  - Xcelium (Cadence)"
            print_info ""
            print_info "Or specify manually: source setup.sh <simulator>"
            return 1
        fi
    fi
    
    # Setup common environment
    setup_common
    
    echo ""
    echo "=============================================================================="
    print_success "Environment setup complete!"
    echo "=============================================================================="
    echo ""
    echo "Simulator: $SIM_SETUP"
    echo "Project Root: $PROJECT_ROOT"
    echo ""
    echo "Next steps:"
    echo "  make compile          # Compile the design and testbench"
    echo "  make sim_simple       # Run a simple test"
    echo "  make help             # See all available targets"
    echo ""
}

# ==============================================================================
# Execute Main Function
# ==============================================================================

# Only run main if script is sourced (not executed)
if [[ "${BASH_SOURCE[0]}" == "${0}" ]]; then
    print_error "This script must be sourced, not executed."
    print_info "Usage: source setup.sh [simulator]"
    exit 1
else
    main "$@"
fi

# ==============================================================================
# End of Setup Script
# ==============================================================================

