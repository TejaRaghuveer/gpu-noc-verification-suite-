// ==============================================================================
// File: ace_lite_transaction.sv
// Description: ACE-Lite Transaction Class for Cache-Coherent I/O Verification
// Author: Verification Team
// Date: January 2025
// Copyright (c) 2025 NVIDIA Corporation
//
// This file implements an ACE-Lite transaction class that extends the AXI4
// transaction class to support cache coherency for I/O masters. ACE-Lite
// provides one-way coherency where I/O masters can snoop CPU/GPU caches but
// caches do not snoop back to I/O masters.
//
// ACE-Lite is a subset of ACE (AXI Coherency Extensions) designed for I/O
// devices that need coherent access to cached data but don't maintain their
// own caches. Common use cases include DMA engines, network controllers, and
// video encoders/decoders accessing GPU memory.
//
// Reference: ARM AMBA 5 ACE-Lite Protocol Specification (ARM IHI 0027E)
// ==============================================================================

`ifndef ACE_LITE_TRANSACTION_SV
`define ACE_LITE_TRANSACTION_SV

import uvm_pkg::*;
`include "uvm_macros.svh"
`include "axi_transaction.sv"

// ==============================================================================
// ACE-Lite Coherent Transaction Type Enumeration
// ==============================================================================
//
// Defines the types of coherent operations supported by ACE-Lite.
// These operations enable I/O masters to interact with cached data.
//
typedef enum {
    WRITE_UNIQUE,    // Allocate cache line exclusively (write-allocate)
                     // Snoops caches to ensure exclusive ownership
                     // Used when I/O master needs to write to cache line
    
    WRITE_BACK,      // Writeback modified cache line to memory
                     // Used when cache line is dirty and needs to be flushed
                     // Ensures memory has latest data before I/O access
    
    CACHE_STASH      // Read from shared cache (read-allocate)
                     // Snoops caches to get latest data
                     // Used when I/O master needs to read cached data
} coherent_type_e;

// ==============================================================================
// Snoop Result Enumeration
// ==============================================================================
//
// Indicates the result of a cache snoop operation.
// Snoops check if caches have the requested data and its state.
//
typedef enum {
    NOT_DIRTY,      // Cache line found but not modified (clean)
                     // Data can be read directly from cache
                     // No writeback required
    
    DIRTY,          // Cache line found and modified (dirty)
                     // Data must be written back to memory first
                     // Ensures coherency before I/O access
    
    PASS            // Cache line not found in any cache (miss)
                     // Data must be fetched from memory
                     // No snoop response needed
} snoop_result_e;

// ==============================================================================
// Cache Line State Enumeration
// ==============================================================================
//
// Represents the MESI (Modified, Exclusive, Shared, Invalid) cache line states
// as extended for ACE-Lite coherency protocol.
//
typedef enum {
    INVALID,         // Cache line not present or invalid
                     // No valid data in cache
    
    SHARED_CLEAN,    // Cache line shared among multiple caches (clean)
                     // Multiple readers, no writer
                     // Data matches memory
    
    UNIQUE_CLEAN,    // Cache line exclusively owned (clean)
                     // Single owner, not modified
                     // Data matches memory
    
    SHARED_DIRTY,    // Cache line shared but modified (dirty)
                     // Multiple readers, one writer
                     // Data may differ from memory
    
    UNIQUE_DIRTY     // Cache line exclusively owned and modified (dirty)
                     // Single owner, modified
                     // Data differs from memory
} cache_line_state_e;

// ==============================================================================
// ACE-Lite Transaction Class
// ==============================================================================
//
// This class extends axi_transaction to add ACE-Lite coherency support.
// ACE-Lite enables I/O masters to perform cache-coherent transactions without
// maintaining their own caches.
//
// Key Differences from Full ACE:
//   1. One-way coherency: I/O masters snoop caches, but caches don't snoop I/O
//   2. Simplified protocol: No cache maintenance from I/O side
//   3. I/O-focused: Designed for DMA engines and I/O controllers
//
class ace_lite_transaction extends axi_transaction;

    // UVM Factory Registration
    `uvm_object_utils(ace_lite_transaction)

    // ==========================================================================
    // ACE-Lite Coherency Fields
    // ==========================================================================
    //
    // These fields extend the base AXI4 transaction with ACE-Lite coherency
    // information. They track snoop operations, cache states, and coherency
    // protocol compliance.
    //
    
    rand bit is_coherent;                    // Is this a coherent transaction?
                                            // 1 = Uses ACE-Lite coherency
                                            // 0 = Normal AXI4 transaction
                                            // Coherent transactions snoop caches
    
    rand coherent_type_e coherent_type;     // Type of coherent operation
                                            // WRITE_UNIQUE: Exclusive allocation
                                            // WRITE_BACK: Writeback dirty line
                                            // CACHE_STASH: Shared read
    
    rand snoop_result_e snoop_result;       // Result of cache snoop operation
                                            // NOT_DIRTY: Clean cache hit
                                            // DIRTY: Dirty cache hit
                                            // PASS: Cache miss
    
    rand cache_line_state_e cache_line_state; // Current cache line state
                                            // Tracks MESI state for coherency
                                            // Updated based on snoop results
    
    bit [127:0] snoop_data;                 // Data returned by snoop operation
                                            // Contains cache line data if snooped
                                            // 128 bits = typical cache line width
    
    int snoop_latency;                      // Cycles taken for snoop operation
                                            // Measures coherency overhead
                                            // Typical range: 5-20 cycles

    // ==========================================================================
    // Constraints
    // ==========================================================================
    //
    // Constraints ensure ACE-Lite protocol compliance and valid coherency
    // operations. These constraints validate the relationship between coherent
    // transaction types and their required snoop behaviors.
    //

    // Coherent transaction validation
    // If transaction is coherent, coherent_type must be valid
    constraint c_coherent_type_valid {
        is_coherent == 1 -> coherent_type inside {WRITE_UNIQUE, WRITE_BACK, CACHE_STASH};
        is_coherent == 0 -> coherent_type == WRITE_UNIQUE; // Default when not coherent
    }

    // WRITE_UNIQUE constraint
    // WRITE_UNIQUE requires snoop to ensure exclusive ownership
    // Snoop result cannot be PASS (must find or allocate cache line)
    constraint c_write_unique_snoop {
        (coherent_type == WRITE_UNIQUE && is_coherent == 1) -> 
            snoop_result != PASS;
    }

    // CACHE_STASH constraint
    // CACHE_STASH is read-only operation (read-allocate)
    // Must be a READ transaction, not WRITE
    constraint c_cache_stash_read_only {
        (coherent_type == CACHE_STASH && is_coherent == 1) -> 
            trans_type == READ;
    }

    // WRITE_BACK constraint
    // WRITE_BACK requires dirty cache line
    // Cache line state must be dirty (SHARED_DIRTY or UNIQUE_DIRTY)
    constraint c_write_back_dirty {
        (coherent_type == WRITE_BACK && is_coherent == 1) -> 
            cache_line_state inside {SHARED_DIRTY, UNIQUE_DIRTY};
    }

    // Snoop result and cache state consistency
    // Snoop result must match cache line state
    constraint c_snoop_state_consistency {
        (snoop_result == NOT_DIRTY) -> 
            cache_line_state inside {SHARED_CLEAN, UNIQUE_CLEAN};
        (snoop_result == DIRTY) -> 
            cache_line_state inside {SHARED_DIRTY, UNIQUE_DIRTY};
        (snoop_result == PASS) -> 
            cache_line_state == INVALID;
    }

    // Snoop latency constraint
    // Snoop latency depends on cache state and system load
    // Typical range: 5-20 cycles
    constraint c_snoop_latency_range {
        snoop_latency >= 5;
        snoop_latency <= 20;
    }

    // ==========================================================================
    // Constructor
    // ==========================================================================
    //
    // Creates a new ACE-Lite transaction instance.
    // Initializes coherency fields to default values.
    //
    function new(string name = "ace_lite_transaction");
        super.new(name);
        
        // Initialize ACE-Lite specific fields
        is_coherent = 0;
        coherent_type = WRITE_UNIQUE;
        snoop_result = PASS;
        cache_line_state = INVALID;
        snoop_data = 0;
        snoop_latency = 0;
    endfunction

    // ==========================================================================
    // Post-Randomize Validation
    // ==========================================================================
    //
    // Validates ACE-Lite transaction after randomization to ensure protocol
    // compliance. Called automatically after randomize() completes successfully.
    //
    function void post_randomize();
        // Call parent post_randomize for AXI4 validation
        super.post_randomize();
        
        // Validate coherency constraints
        if (is_coherent == 1) begin
            // Validate coherent transaction type
            if (!(coherent_type inside {WRITE_UNIQUE, WRITE_BACK, CACHE_STASH})) begin
                `uvm_warning("ACE_LITE_TX", $sformatf(
                    "Invalid coherent_type: %s", coherent_type.name()))
            end
            
            // Validate WRITE_UNIQUE snoop requirement
            if (coherent_type == WRITE_UNIQUE && snoop_result == PASS) begin
                `uvm_warning("ACE_LITE_TX", 
                    "WRITE_UNIQUE should not have PASS snoop result")
            end
            
            // Validate CACHE_STASH is read-only
            if (coherent_type == CACHE_STASH && trans_type != READ) begin
                `uvm_error("ACE_LITE_TX", $sformatf(
                    "CACHE_STASH must be READ transaction, got %s",
                    trans_type.name()))
            end
            
            // Validate WRITE_BACK requires dirty state
            if (coherent_type == WRITE_BACK && 
                !(cache_line_state inside {SHARED_DIRTY, UNIQUE_DIRTY})) begin
                `uvm_warning("ACE_LITE_TX", 
                    "WRITE_BACK should have dirty cache line state")
            end
            
            `uvm_info("ACE_LITE_TX", $sformatf(
                "ACE-Lite transaction: coherent=%0b, type=%s, snoop=%s, state=%s",
                is_coherent, coherent_type.name(), snoop_result.name(),
                cache_line_state.name()), UVM_DEBUG)
        end
    endfunction

    // ==========================================================================
    // Is Snoop Required
    // ==========================================================================
    //
    // Determines if this transaction requires a cache snoop operation.
    // Snoops are required for coherent transactions to maintain cache coherency.
    //
    // Returns:
    //   1 if snoop required, 0 otherwise
    //
    function bit is_snoop_required();
        // Snoop required for coherent transactions
        if (is_coherent == 0) begin
            return 0;  // Non-coherent transactions don't snoop
        end
        
        // All coherent transaction types require snoops
        // WRITE_UNIQUE: Snoop to ensure exclusive ownership
        // WRITE_BACK: Snoop to find dirty cache line
        // CACHE_STASH: Snoop to get latest cached data
        return 1;
    endfunction

    // ==========================================================================
    // Get Snoop Latency
    // ==========================================================================
    //
    // Simulates and returns the snoop response time based on cache state
    // and system conditions. This models the coherency overhead.
    //
    // Returns:
    //   Snoop latency in cycles
    //
    function int get_snoop_latency();
        int base_latency;
        int state_overhead;
        
        // Base latency depends on coherent transaction type
        case (coherent_type)
            WRITE_UNIQUE: base_latency = 8;   // Exclusive allocation overhead
            WRITE_BACK:   base_latency = 10;  // Writeback overhead
            CACHE_STASH:  base_latency = 6;   // Read snoop overhead
            default:      base_latency = 5;   // Default overhead
        endcase
        
        // Additional latency based on cache line state
        case (cache_line_state)
            INVALID:      state_overhead = 0;  // No cache, fast miss
            SHARED_CLEAN: state_overhead = 2;  // Shared clean, moderate overhead
            UNIQUE_CLEAN: state_overhead = 1;  // Unique clean, low overhead
            SHARED_DIRTY: state_overhead = 5; // Shared dirty, high overhead
            UNIQUE_DIRTY: state_overhead = 4; // Unique dirty, high overhead
            default:      state_overhead = 0;
        endcase
        
        // Total snoop latency
        snoop_latency = base_latency + state_overhead;
        return snoop_latency;
    endfunction

    // ==========================================================================
    // Cache State to String
    // ==========================================================================
    //
    // Converts cache line state enumeration to human-readable string.
    // Useful for debugging and logging.
    //
    // Returns:
    //   String representation of cache line state
    //
    function string cache_state_to_string();
        case (cache_line_state)
            INVALID:      return "INVALID";
            SHARED_CLEAN: return "SHARED_CLEAN";
            UNIQUE_CLEAN: return "UNIQUE_CLEAN";
            SHARED_DIRTY: return "SHARED_DIRTY";
            UNIQUE_DIRTY: return "UNIQUE_DIRTY";
            default:      return "UNKNOWN";
        endcase
    endfunction

    // ==========================================================================
    // Convert to String (Override)
    // ==========================================================================
    //
    // Returns a detailed string representation including ACE-Lite fields.
    // Extends parent convert2string() with coherency information.
    //
    function string convert2string();
        string s;
        
        // Call parent to get AXI4 transaction details
        s = super.convert2string();
        
        // Add ACE-Lite specific information
        s = {s, $sformatf("  ACE-Lite Coherency:\n")};
        s = {s, $sformatf("    Is Coherent:     %0b\n", is_coherent)};
        
        if (is_coherent == 1) begin
            s = {s, $sformatf("    Coherent Type:   %s\n", coherent_type.name())};
            s = {s, $sformatf("    Snoop Result:    %s\n", snoop_result.name())};
            s = {s, $sformatf("    Cache State:     %s\n", cache_state_to_string())};
            s = {s, $sformatf("    Snoop Latency:   %0d cycles\n", snoop_latency)};
            s = {s, $sformatf("    Snoop Data:       0x%0h\n", snoop_data)};
        end
        
        return s;
    endfunction

    // ==========================================================================
    // Copy Method (Override)
    // ==========================================================================
    //
    // Creates a deep copy of this ACE-Lite transaction.
    // Extends parent copy() to include ACE-Lite fields.
    //
    function void do_copy(uvm_object rhs);
        ace_lite_transaction tx;
        
        if (!$cast(tx, rhs)) begin
            `uvm_error("ACE_LITE_TX", 
                "do_copy: argument is not an ace_lite_transaction")
            return;
        end
        
        // Call parent to copy AXI4 fields
        super.do_copy(rhs);
        
        // Copy ACE-Lite specific fields
        is_coherent = tx.is_coherent;
        coherent_type = tx.coherent_type;
        snoop_result = tx.snoop_result;
        cache_line_state = tx.cache_line_state;
        snoop_data = tx.snoop_data;
        snoop_latency = tx.snoop_latency;
    endfunction

    // ==========================================================================
    // Compare Method (Override)
    // ==========================================================================
    //
    // Compares this transaction with another for scoreboard checking.
    // Extends parent compare() to include ACE-Lite fields.
    //
    function bit do_compare(uvm_object rhs, uvm_comparer comparer);
        ace_lite_transaction tx;
        bit match = 1;
        
        if (!$cast(tx, rhs)) begin
            `uvm_error("ACE_LITE_TX", 
                "do_compare: argument is not an ace_lite_transaction")
            return 0;
        end
        
        // Call parent to compare AXI4 fields
        match = super.do_compare(rhs, comparer);
        
        // Compare ACE-Lite specific fields
        if (is_coherent != tx.is_coherent) match = 0;
        if (coherent_type != tx.coherent_type) match = 0;
        if (snoop_result != tx.snoop_result) match = 0;
        if (cache_line_state != tx.cache_line_state) match = 0;
        if (snoop_data != tx.snoop_data) match = 0;
        
        return match;
    endfunction

    // ==========================================================================
    // ACE-Lite Transaction Flow Examples
    // ==========================================================================
    //
    // The following comments illustrate typical ACE-Lite transaction flows:
    //
    // Example 1: WRITE_UNIQUE (DMA Write to Cached Memory)
    //   1. I/O master initiates WRITE_UNIQUE transaction
    //   2. System snoops all caches for address
    //   3. If cache hit (DIRTY or NOT_DIRTY):
    //      - Invalidate cache line in all caches
    //      - If DIRTY: Writeback to memory first
    //   4. Allocate cache line exclusively for I/O master
    //   5. Complete write transaction
    //
    // Example 2: CACHE_STASH (DMA Read from Cached Memory)
    //   1. I/O master initiates CACHE_STASH transaction
    //   2. System snoops all caches for address
    //   3. If cache hit:
    //      - Read data from cache (snoop_data)
    //      - Return data to I/O master
    //   4. If cache miss (PASS):
    //      - Read data from memory
    //      - Return data to I/O master
    //
    // Example 3: WRITE_BACK (Flush Dirty Cache Line)
    //   1. I/O master initiates WRITE_BACK transaction
    //   2. System snoops caches for dirty line
    //   3. If DIRTY cache hit:
    //      - Writeback dirty data to memory
    //      - Invalidate cache line
    //   4. Complete writeback transaction
    //
    // Key Advantage: One-way coherency means I/O masters don't need to
    // maintain caches or respond to snoops, simplifying I/O controller design.

endclass

`endif // ACE_LITE_TRANSACTION_SV

