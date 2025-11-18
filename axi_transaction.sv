// ==============================================================================
// File: axi_transaction.sv
// Description: AXI4 Transaction Class for GPU Interconnect NoC Verification
// Author: Verification Team
// Date: January 2025
// Copyright (c) 2025 NVIDIA Corporation
//
// This file implements a comprehensive AXI4 transaction class for use in UVM
// verification environments. It supports all AXI4 protocol features including
// write and read channels, burst types, QoS, atomic operations, and transaction
// tracking for performance analysis.
//
// Reference: ARM AMBA 5 AXI4 Protocol Specification (ARM IHI 0022E)
// ==============================================================================

`ifndef AXI_TRANSACTION_SV
`define AXI_TRANSACTION_SV

import uvm_pkg::*;
`include "uvm_macros.svh"

// ==============================================================================
// Transaction Type Enumeration
// ==============================================================================
//
// Defines the types of transactions supported by the AXI4 protocol.
// READ and WRITE are standard operations, while ATOMIC operations provide
// atomic memory operations for synchronization.
//
typedef enum {
    READ,              // Standard read transaction
    WRITE,             // Standard write transaction
    ATOMIC_ADD,        // Atomic add operation (fetch-and-add)
    ATOMIC_SWAP,       // Atomic swap operation
    ATOMIC_CMP_SWAP    // Atomic compare-and-swap operation
} trans_type_e;

// ==============================================================================
// AXI4 Transaction Class
// ==============================================================================
//
// This class encapsulates a complete AXI4 transaction including all five
// channels: Write Address (AW), Write Data (W), Write Response (B),
// Read Address (AR), and Read Data (R).
//
// The class extends uvm_sequence_item to enable use in UVM sequences and
// provides methods for transaction manipulation, validation, and analysis.
//
class axi_transaction extends uvm_sequence_item;

    // UVM Factory Registration
    `uvm_object_utils(axi_transaction)

    // ==========================================================================
    // Transaction Type
    // ==========================================================================
    //
    // Identifies the type of transaction (READ, WRITE, or ATOMIC operation)
    //
    rand trans_type_e trans_type;

    // ==========================================================================
    // AXI4 Write Address Channel (AW)
    // ==========================================================================
    //
    // The write address channel carries address and control information for
    // write transactions. All write transactions begin with an address phase
    // on this channel.
    //
    // Reference: ARM AMBA 5 AXI4 Specification, Section 3.1.1
    //
    rand bit [31:0] awaddr;      // Write address (32-bit address space)
                                 // Constraint: Must be aligned to burst size
    
    rand bit [7:0]  awlen;       // Burst length: Number of transfers minus 1
                                 // Range: 0-255 (represents 1-256 transfers)
                                 // Constraint: awlen in [0:255]
    
    rand bit [2:0]  awsize;      // Burst size: Number of bytes per transfer
                                 // Encoding: 0=1B, 1=2B, 2=4B, 3=8B, 4=16B,
                                 //           5=32B, 6=64B, 7=128B
                                 // Constraint: awsize in [0:7]
    
    rand bit [1:0]  awburst;    // Burst type:
                                 // 0 = FIXED: Address remains constant
                                 // 1 = INCR: Address increments by burst size
                                 // 2 = WRAP: Address wraps at boundary
                                 // Constraint: awburst in [0:2]
    
    rand bit [3:0]  awid;        // Transaction ID: Identifies transaction
                                 // Range: 0-15 (4-bit ID)
                                 // Constraint: awid in [0:15]
                                 // Used for out-of-order completion
    
    rand bit [3:0]  awqos;       // Quality of Service: Transaction priority
                                 // Range: 0-15 (0=lowest, 15=highest)
                                 // Constraint: awqos in [0:15]
                                 // Higher QoS gets priority in arbitration
    
    rand bit [3:0]  awregion;    // Region identifier: For address translation
                                 // Range: 0-15
                                 // Used in systems with multiple address spaces
    
    rand bit        awlock;       // Lock type: Atomic/exclusive access
                                 // 0 = Normal access
                                 // 1 = Exclusive/atomic access
                                 // Must be set for atomic operations
    
    rand bit [3:0]  awcache;     // Cache attributes:
                                 // Bit 0: Bufferable
                                 // Bit 1: Cacheable
                                 // Bit 2: Read-allocate
                                 // Bit 3: Write-allocate
    
    rand bit [2:0]  awprot;      // Protection type:
                                 // Bit 0: Privileged (0=user, 1=privileged)
                                 // Bit 1: Secure (0=secure, 1=non-secure)
                                 // Bit 2: Instruction (0=data, 1=instruction)

    // ==========================================================================
    // AXI4 Write Data Channel (W)
    // ==========================================================================
    //
    // The write data channel carries the actual data to be written.
    // Multiple data transfers can occur for burst transactions.
    //
    // Reference: ARM AMBA 5 AXI4 Specification, Section 3.1.2
    //
    rand bit [127:0] wdata;      // Write data: 128-bit data payload
                                 // For bursts, this represents one transfer
                                 // Multiple transfers use multiple wdata values
    
    rand bit [15:0]  wstrb;      // Write strobes: Byte enables
                                 // Each bit enables one byte of wdata
                                 // wstrb[0] enables wdata[7:0]
                                 // wstrb[15] enables wdata[127:120]
                                 // Constraint: wstrb != 0 (at least one byte)
    
    rand bit         wlast;      // Last transfer indicator
                                 // 1 = Last transfer in burst
                                 // 0 = More transfers follow
                                 // Must be 1 for final transfer
    
    rand bit [7:0]   wuser;      // User signal: Optional user-defined data
                                 // Can be used for custom metadata

    // ==========================================================================
    // AXI4 Write Response Channel (B)
    // ==========================================================================
    //
    // The write response channel indicates completion status of write
    // transactions. Each write transaction receives exactly one response.
    //
    // Reference: ARM AMBA 5 AXI4 Specification, Section 3.1.3
    //
    rand bit [1:0]   bresp;      // Write response:
                                 // 0 = OKAY: Normal success
                                 // 1 = EXOKAY: Exclusive access success
                                 // 2 = SLVERR: Slave error
                                 // 3 = DECERR: Decode error (interconnect)
                                 // Constraint: bresp != EXOKAY unless atomic
    
    rand bit [3:0]   bid;         // Response transaction ID
                                 // Must match awid of corresponding write
                                 // Enables out-of-order completion
    
    rand bit [7:0]   buser;      // User signal: Optional user-defined data

    // ==========================================================================
    // AXI4 Read Address Channel (AR)
    // ==========================================================================
    //
    // The read address channel carries address and control information for
    // read transactions. Similar to write address channel but for reads.
    //
    // Reference: ARM AMBA 5 AXI4 Specification, Section 3.1.4
    //
    rand bit [31:0] araddr;      // Read address (32-bit address space)
                                 // Constraint: Must be aligned to burst size
    
    rand bit [7:0]  arlen;       // Burst length: Number of transfers minus 1
                                 // Range: 0-255 (represents 1-256 transfers)
                                 // Constraint: arlen in [0:255]
    
    rand bit [2:0]  arsize;      // Burst size: Number of bytes per transfer
                                 // Encoding: Same as awsize
                                 // Constraint: arsize in [0:7]
    
    rand bit [1:0]  arburst;    // Burst type: Same as awburst
                                 // Constraint: arburst in [0:2]
    
    rand bit [3:0]  arid;        // Transaction ID: Identifies transaction
                                 // Range: 0-15 (4-bit ID)
                                 // Constraint: arid in [0:15]
    
    rand bit [3:0]  arqos;       // Quality of Service: Transaction priority
                                 // Range: 0-15 (0=lowest, 15=highest)
                                 // Constraint: arqos in [0:15]
    
    rand bit [3:0]  arregion;    // Region identifier: For address translation
                                 // Range: 0-15
    
    rand bit        arlock;       // Lock type: Atomic/exclusive access
                                 // 0 = Normal access
                                 // 1 = Exclusive/atomic access
    
    rand bit [3:0]  arcache;     // Cache attributes: Same as awcache
    
    rand bit [2:0]  arprot;      // Protection type: Same as awprot

    // ==========================================================================
    // AXI4 Read Data Channel (R)
    // ==========================================================================
    //
    // The read data channel carries data from read transactions.
    // Multiple data transfers occur for burst reads.
    //
    // Reference: ARM AMBA 5 AXI4 Specification, Section 3.1.5
    //
    rand bit [127:0] rdata;      // Read data: 128-bit data payload
                                 // For bursts, this represents one transfer
    
    rand bit [1:0]   rresp;      // Read response:
                                 // 0 = OKAY: Normal success
                                 // 1 = EXOKAY: Exclusive access success
                                 // 2 = SLVERR: Slave error
                                 // 3 = DECERR: Decode error
    
    rand bit [3:0]   rid;        // Response transaction ID
                                 // Must match arid of corresponding read
    
    rand bit         rlast;      // Last transfer indicator
                                 // 1 = Last transfer in burst
                                 // 0 = More transfers follow
    
    rand bit [7:0]   ruser;      // User signal: Optional user-defined data

    // ==========================================================================
    // Transaction Tracking Fields
    // ==========================================================================
    //
    // These fields are used for verification and performance analysis.
    // They track transaction flow through the NoC and enable latency
    // and throughput measurements.
    //
    int source_id;                // Source router ID in NoC
                                 // Identifies which processing element
                                 // injected this transaction
    
    int dest_id;                  // Destination router ID in NoC
                                 // Identifies target memory/device
    
    longint start_time;           // Transaction injection time
                                 // Set when transaction is injected into NoC
                                 // Units: simulation time
    
    longint end_time;             // Transaction completion time
                                 // Set when response received
                                 // Units: simulation time
    
    real injection_rate;          // Injection rate percentage
                                 // Percentage of cycles injecting traffic
                                 // Range: 0.0 to 1.0 (0% to 100%)
    
    int qos_level;                // Classified QoS level for analysis
                                 // Derived from awqos/arqos
                                 // Used for performance binning

    // ==========================================================================
    // Constraints
    // ==========================================================================
    //
    // Constraints ensure generated transactions are valid according to AXI4
    // protocol rules and GPU-specific requirements.
    //

    // Burst length constraints
    // AXI4 supports bursts of 1 to 256 transfers
    constraint c_awlen_range {
        awlen >= 0;
        awlen <= 255;  // Represents 1-256 transfers
    }

    constraint c_arlen_range {
        arlen >= 0;
        arlen <= 255;  // Represents 1-256 transfers
    }

    // Burst size constraints
    // Valid sizes: 1, 2, 4, 8, 16, 32, 64, 128 bytes
    constraint c_awsize_range {
        awsize >= 0;
        awsize <= 7;  // Maximum 128 bytes (2^7)
    }

    constraint c_arsize_range {
        arsize >= 0;
        arsize <= 7;  // Maximum 128 bytes (2^7)
    }

    // Burst type constraints
    // Valid types: FIXED (0), INCR (1), WRAP (2)
    constraint c_awburst_range {
        awburst >= 0;
        awburst <= 2;
    }

    constraint c_arburst_range {
        arburst >= 0;
        arburst <= 2;
    }

    // Transaction ID constraints
    // 4-bit ID supports 16 concurrent transactions
    constraint c_awid_range {
        awid >= 0;
        awid <= 15;
    }

    constraint c_arid_range {
        arid >= 0;
        arid <= 15;
    }

    // QoS constraints
    // Valid range: 0 (lowest) to 15 (highest)
    constraint c_awqos_range {
        awqos >= 0;
        awqos <= 15;
    }

    constraint c_arqos_range {
        arqos >= 0;
        arqos <= 15;
    }

    // Write strobe constraint
    // At least one byte must be enabled for write
    constraint c_wstrb_valid {
        wstrb != 0;  // At least one byte enabled
    }

    // Response constraint
    // EXOKAY response only valid for atomic/exclusive operations
    constraint c_bresp_atomic {
        (bresp == 2'b01) -> (awlock == 1'b1 || trans_type inside {ATOMIC_ADD, ATOMIC_SWAP, ATOMIC_CMP_SWAP});
    }

    // Transaction type distribution
    // GPU workloads typically have more writes than reads
    // Weighted distribution: 70% WRITE, 30% READ
    constraint c_trans_type_dist {
        trans_type dist {
            WRITE := 70,
            READ := 30,
            ATOMIC_ADD := 0,
            ATOMIC_SWAP := 0,
            ATOMIC_CMP_SWAP := 0
        };
    }

    // Address alignment constraint
    // Address must be aligned to burst size
    // For awsize=3 (8 bytes), address must be 8-byte aligned
    constraint c_awaddr_alignment {
        (awsize == 0) -> (awaddr % 1 == 0);
        (awsize == 1) -> (awaddr % 2 == 0);
        (awsize == 2) -> (awaddr % 4 == 0);
        (awsize == 3) -> (awaddr % 8 == 0);
        (awsize == 4) -> (awaddr % 16 == 0);
        (awsize == 5) -> (awaddr % 32 == 0);
        (awsize == 6) -> (awaddr % 64 == 0);
        (awsize == 7) -> (awaddr % 128 == 0);
    }

    constraint c_araddr_alignment {
        (arsize == 0) -> (araddr % 1 == 0);
        (arsize == 1) -> (araddr % 2 == 0);
        (arsize == 2) -> (araddr % 4 == 0);
        (arsize == 3) -> (araddr % 8 == 0);
        (arsize == 4) -> (araddr % 16 == 0);
        (arsize == 5) -> (araddr % 32 == 0);
        (arsize == 6) -> (araddr % 64 == 0);
        (arsize == 7) -> (araddr % 128 == 0);
    }

    // ==========================================================================
    // Constructor
    // ==========================================================================
    //
    // Creates a new AXI4 transaction instance.
    //
    // Arguments:
    //   name - Instance name for UVM object
    //
    function new(string name = "axi_transaction");
        super.new(name);
        
        // Initialize tracking fields
        source_id = -1;
        dest_id = -1;
        start_time = 0;
        end_time = 0;
        injection_rate = 0.0;
        qos_level = 0;
        
        // Initialize response ID to match address ID
        bid = 0;
        rid = 0;
    endfunction

    // ==========================================================================
    // Post-Randomize Validation
    // ==========================================================================
    //
    // Validates transaction after randomization to ensure protocol compliance.
    // Called automatically after randomize() completes successfully.
    //
    // Validations performed:
    //   1. Burst length consistency
    //   2. QoS level validation
    //   3. Address alignment
    //   4. Atomic operation consistency
    //
    function void post_randomize();
        // Validate burst length consistency
        if (trans_type == WRITE) begin
            if (awlen > 255) begin
                `uvm_warning("AXI_TX", $sformatf(
                    "Invalid burst length: awlen=%0d (max 255)", awlen))
            end
        end else if (trans_type == READ) begin
            if (arlen > 255) begin
                `uvm_warning("AXI_TX", $sformatf(
                    "Invalid burst length: arlen=%0d (max 255)", arlen))
            end
        end

        // Validate QoS level
        if (trans_type == WRITE) begin
            if (awqos > 15) begin
                `uvm_warning("AXI_TX", $sformatf(
                    "Invalid QoS: awqos=%0d (max 15)", awqos))
            end
            qos_level = awqos;
        end else if (trans_type == READ) begin
            if (arqos > 15) begin
                `uvm_warning("AXI_TX", $sformatf(
                    "Invalid QoS: arqos=%0d (max 15)", arqos))
            end
            qos_level = arqos;
        end

        // Validate address alignment
        if (trans_type == WRITE) begin
            int alignment = 1 << awsize;
            if (awaddr % alignment != 0) begin
                `uvm_error("AXI_TX", $sformatf(
                    "Address misaligned: awaddr=0x%0h, awsize=%0d (requires %0d-byte alignment)",
                    awaddr, awsize, alignment))
            end
        end else if (trans_type == READ) begin
            int alignment = 1 << arsize;
            if (araddr % alignment != 0) begin
                `uvm_error("AXI_TX", $sformatf(
                    "Address misaligned: araddr=0x%0h, arsize=%0d (requires %0d-byte alignment)",
                    araddr, arsize, alignment))
            end
        end

        // Validate atomic operation consistency
        if (trans_type inside {ATOMIC_ADD, ATOMIC_SWAP, ATOMIC_CMP_SWAP}) begin
            if (awlock != 1'b1) begin
                `uvm_warning("AXI_TX", $sformatf(
                    "Atomic operation without awlock set: trans_type=%s",
                    trans_type.name()))
            end
        end

        // Set response IDs to match address IDs
        if (trans_type == WRITE) begin
            bid = awid;
        end else if (trans_type == READ) begin
            rid = arid;
        end

        `uvm_info("AXI_TX", $sformatf(
            "Transaction randomized: type=%s, addr=0x%0h, len=%0d, qos=%0d",
            trans_type.name(),
            (trans_type == WRITE) ? awaddr : araddr,
            (trans_type == WRITE) ? awlen : arlen,
            qos_level), UVM_DEBUG)
    endfunction

    // ==========================================================================
    // Convert to String
    // ==========================================================================
    //
    // Returns a detailed string representation of the transaction for debugging.
    //
    // Returns:
    //   String containing all transaction fields
    //
    function string convert2string();
        string s;
        s = $sformatf("AXI Transaction:\n");
        s = {s, $sformatf("  Type: %s\n", trans_type.name())};
        
        if (trans_type == WRITE) begin
            s = {s, $sformatf("  Write Address Channel:\n")};
            s = {s, $sformatf("    AWADDR: 0x%0h\n", awaddr)};
            s = {s, $sformatf("    AWLEN:  %0d (burst length)\n", awlen)};
            s = {s, $sformatf("    AWSIZE: %0d (%0d bytes)\n", awsize, 1<<awsize)};
            s = {s, $sformatf("    AWBURST: %0d (%s)\n", awburst,
                (awburst == 0) ? "FIXED" : (awburst == 1) ? "INCR" : "WRAP")};
            s = {s, $sformatf("    AWID:   %0d\n", awid)};
            s = {s, $sformatf("    AWQOS:  %0d\n", awqos)};
            s = {s, $sformatf("  Write Data Channel:\n")};
            s = {s, $sformatf("    WDATA:  0x%0h\n", wdata)};
            s = {s, $sformatf("    WSTRB:  0x%04h\n", wstrb)};
            s = {s, $sformatf("    WLAST:  %0b\n", wlast)};
            s = {s, $sformatf("  Write Response Channel:\n")};
            s = {s, $sformatf("    BRESP:  %0d (%s)\n", bresp,
                (bresp == 0) ? "OKAY" : (bresp == 1) ? "EXOKAY" :
                (bresp == 2) ? "SLVERR" : "DECERR")};
            s = {s, $sformatf("    BID:    %0d\n", bid)};
        end else if (trans_type == READ) begin
            s = {s, $sformatf("  Read Address Channel:\n")};
            s = {s, $sformatf("    ARADDR: 0x%0h\n", araddr)};
            s = {s, $sformatf("    ARLEN:  %0d (burst length)\n", arlen)};
            s = {s, $sformatf("    ARSIZE: %0d (%0d bytes)\n", arsize, 1<<arsize)};
            s = {s, $sformatf("    ARBURST: %0d (%s)\n", arburst,
                (arburst == 0) ? "FIXED" : (arburst == 1) ? "INCR" : "WRAP")};
            s = {s, $sformatf("    ARID:   %0d\n", arid)};
            s = {s, $sformatf("    ARQOS:  %0d\n", arqos)};
            s = {s, $sformatf("  Read Data Channel:\n")};
            s = {s, $sformatf("    RDATA:  0x%0h\n", rdata)};
            s = {s, $sformatf("    RRESP:  %0d (%s)\n", rresp,
                (rresp == 0) ? "OKAY" : (rresp == 1) ? "EXOKAY" :
                (rresp == 2) ? "SLVERR" : "DECERR")};
            s = {s, $sformatf("    RID:    %0d\n", rid)};
            s = {s, $sformatf("    RLAST:  %0b\n", rlast)};
        end else begin
            s = {s, $sformatf("  Atomic Operation:\n")};
            s = {s, $sformatf("    Type: %s\n", trans_type.name())};
            s = {s, $sformatf("    AWADDR: 0x%0h\n", awaddr)};
            s = {s, $sformatf("    AWLOCK: %0b\n", awlock)};
        end
        
        s = {s, $sformatf("  Tracking:\n")};
        s = {s, $sformatf("    Source ID: %0d\n", source_id)};
        s = {s, $sformatf("    Dest ID:   %0d\n", dest_id)};
        s = {s, $sformatf("    Start Time: %0d\n", start_time)};
        s = {s, $sformatf("    End Time:   %0d\n", end_time)};
        if (end_time > start_time) begin
            s = {s, $sformatf("    Latency:    %0d cycles\n", end_time - start_time)};
        end
        
        return s;
    endfunction

    // ==========================================================================
    // Copy Method
    // ==========================================================================
    //
    // Creates a deep copy of this transaction.
    //
    // Arguments:
    //   rhs - Right-hand side transaction to copy from
    //
    function void do_copy(uvm_object rhs);
        axi_transaction tx;
        
        if (!$cast(tx, rhs)) begin
            `uvm_error("AXI_TX", "do_copy: argument is not an axi_transaction")
            return;
        end
        
        super.do_copy(rhs);
        
        // Copy all fields
        trans_type = tx.trans_type;
        
        // Write address channel
        awaddr = tx.awaddr;
        awlen = tx.awlen;
        awsize = tx.awsize;
        awburst = tx.awburst;
        awid = tx.awid;
        awqos = tx.awqos;
        awregion = tx.awregion;
        awlock = tx.awlock;
        awcache = tx.awcache;
        awprot = tx.awprot;
        
        // Write data channel
        wdata = tx.wdata;
        wstrb = tx.wstrb;
        wlast = tx.wlast;
        wuser = tx.wuser;
        
        // Write response channel
        bresp = tx.bresp;
        bid = tx.bid;
        buser = tx.buser;
        
        // Read address channel
        araddr = tx.araddr;
        arlen = tx.arlen;
        arsize = tx.arsize;
        arburst = tx.arburst;
        arid = tx.arid;
        arqos = tx.arqos;
        arregion = tx.arregion;
        arlock = tx.arlock;
        arcache = tx.arcache;
        arprot = tx.arprot;
        
        // Read data channel
        rdata = tx.rdata;
        rresp = tx.rresp;
        rid = tx.rid;
        rlast = tx.rlast;
        ruser = tx.ruser;
        
        // Tracking fields
        source_id = tx.source_id;
        dest_id = tx.dest_id;
        start_time = tx.start_time;
        end_time = tx.end_time;
        injection_rate = tx.injection_rate;
        qos_level = tx.qos_level;
    endfunction

    // ==========================================================================
    // Compare Method
    // ==========================================================================
    //
    // Compares this transaction with another for scoreboard checking.
    //
    // Arguments:
    //   rhs - Right-hand side transaction to compare with
    //
    // Returns:
    //   1 if transactions match, 0 otherwise
    //
    function bit do_compare(uvm_object rhs, uvm_comparer comparer);
        axi_transaction tx;
        bit match = 1;
        
        if (!$cast(tx, rhs)) begin
            `uvm_error("AXI_TX", "do_compare: argument is not an axi_transaction")
            return 0;
        end
        
        // Compare transaction type
        if (trans_type != tx.trans_type) begin
            `uvm_info("AXI_TX", $sformatf(
                "Transaction type mismatch: %s vs %s",
                trans_type.name(), tx.trans_type.name()), UVM_MEDIUM)
            match = 0;
        end
        
        // Compare based on transaction type
        if (trans_type == WRITE) begin
            // Compare write fields
            if (awaddr != tx.awaddr) match = 0;
            if (awlen != tx.awlen) match = 0;
            if (awsize != tx.awsize) match = 0;
            if (awburst != tx.awburst) match = 0;
            if (awid != tx.awid) match = 0;
            if (wdata != tx.wdata) match = 0;
            if (wstrb != tx.wstrb) match = 0;
            if (bid != tx.bid) match = 0;
            if (bresp != tx.bresp) match = 0;
        end else if (trans_type == READ) begin
            // Compare read fields
            if (araddr != tx.araddr) match = 0;
            if (arlen != tx.arlen) match = 0;
            if (arsize != tx.arsize) match = 0;
            if (arburst != tx.arburst) match = 0;
            if (arid != tx.arid) match = 0;
            if (rid != tx.rid) match = 0;
            if (rresp != tx.rresp) match = 0;
            if (rdata != tx.rdata) match = 0;
        end
        
        return match;
    endfunction

    // ==========================================================================
    // Get Latency
    // ==========================================================================
    //
    // Calculates and returns the transaction latency in cycles.
    //
    // Returns:
    //   Latency in cycles (end_time - start_time), or 0 if not completed
    //
    function longint get_latency();
        if (end_time > start_time && start_time > 0) begin
            return (end_time - start_time);
        end else begin
            return 0;
        end
    endfunction

    // ==========================================================================
    // Is Write Transaction
    // ==========================================================================
    //
    // Checks if this is a write transaction.
    //
    // Returns:
    //   1 if write transaction, 0 otherwise
    //
    function bit is_write();
        return (trans_type == WRITE);
    endfunction

    // ==========================================================================
    // Is Read Transaction
    // ==========================================================================
    //
    // Checks if this is a read transaction.
    //
    // Returns:
    //   1 if read transaction, 0 otherwise
    //
    function bit is_read();
        return (trans_type == READ);
    endfunction

    // ==========================================================================
    // Is Atomic Transaction
    // ==========================================================================
    //
    // Checks if this is an atomic transaction.
    //
    // Returns:
    //   1 if atomic transaction, 0 otherwise
    //
    function bit is_atomic();
        return (trans_type inside {ATOMIC_ADD, ATOMIC_SWAP, ATOMIC_CMP_SWAP});
    endfunction

endclass

`endif // AXI_TRANSACTION_SV

