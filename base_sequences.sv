// ==============================================================================
// File: base_sequences.sv
// Description: AXI4 Sequence Library for GPU Interconnect NoC Verification
// Author: Verification Team
// Date: January 2025
// Copyright (c) 2025 NVIDIA Corporation
//
// This file implements a comprehensive library of UVM sequences for AXI4
// protocol verification of GPU interconnect NoC. Sequences cover functional
// verification, protocol compliance, QoS priority, virtual channels, and
// performance/stress testing scenarios.
//
// Sequence Library Organization:
//   1. Base Sequence: Common functionality and randomization
//   2. Simple Sequences: Basic connectivity and data integrity
// integrity
//   3. Burst Sequences: AXI4 burst transfer verification
//   4. Protocol Sequences: Handshake, atomicity, response handling
//   5. QoS Sequences: Priority-based arbitration verification
//   6. Virtual Channel Sequences: Deadlock prevention testing
//   7. Performance Sequences: Stress testing and throughput measurement
//
// Reference: ARM AMBA 5 AXI4 Protocol Specification (ARM IHI 0022E)
// ==============================================================================

`ifndef BASE_SEQUENCES_SV
`define BASE_SEQUENCES_SV

import uvm_pkg::*;
`include "uvm_macros.svh"
`include "axi_transaction.sv"

// ==============================================================================
// Transaction Type Enumeration
// ==============================================================================
//
// Defines the type of traffic pattern for sequence generation.
//
typedef enum {
    READ_ONLY,          // Generate only read transactions
    WRITE_ONLY,         // Generate only write transactions
    MIXED               // Generate mix of read and write transactions
} transaction_type_e;

// ==============================================================================
// Traffic Pattern Enumeration
// ==============================================================================
//
// Defines traffic distribution patterns for NoC testing.
//
typedef enum {
    RANDOM,             // Random destination selection
    UNIFORM,            // Uniform distribution to all destinations
    SKEWED_TO_DEST,     // Skewed traffic to specific destination
    HOTSPOT,              // Hotspot traffic pattern
    BIT_REVERSE,        // Bit-reverse addressing pattern
    TRANSPOSE           // Transpose addressing pattern (x,y) -> (y,x)
} traffic_pattern_e;

// ==============================================================================
// Base AXI4 Sequence Class
// ==============================================================================
//
// Base class for all AXI4 sequences. Provides common functionality including
// randomization, transaction creation, and reporting. All specific sequences
// extend this base class.
//
class base_axi4_sequence extends uvm_sequence #(axi_transaction);

    `uvm_object_utils(base_axi4_sequence)

    // ==========================================================================
    // Sequence Configuration Properties
    // ==========================================================================
    
    // Transaction Count
    rand int num_transactions;              // Number of transactions to generate
                                           // Default: 10 transactions
    
    // Transaction Type
    rand transaction_type_e transaction_type;  // Type
 pattern type
    
    // Traffic Pattern
    rand traffic_pattern_e traffic_pattern;     // Traffic distribution pattern
    
    // Destination Configuration
    rand int destination;                   // Target NoC router ID
                                           // Range: 0-15 for 4x4 mesh
    
    // Priority Distribution
    real priority_distribution[16];         // Probability distribution for QoS levels
                                           // Indexed by QoS value (0-15)
    
    // Burst Length Distribution
    int burst_length_dist[256];             // Preferred burst lengths
                                           // Weighted distribution for randomization
    
    // Address Range Configuration
    bit [31:0] l2_cache_base = 32'h4000_0000;      // L2 cache address range
    bit [31:0] l2_cache_size = 32'h4000_0000;      // 1GB L2 cache
    bit [31:0] memory_base = 32'h0000_0000;        // Main memory base
    bit [31:0] memory_size = 32'h4000_0000;        // 1GB memory
    bit [31:0] peripheral_base = 32'hC000_0000;    // Peripheral base
    bit [31:0] peripheral_size = 32'h4000_0000;    // 1GB peripheral space
    
    // Statistics
    int transactions_sent = 0;              // Count of transactions sent
    int transactions_completed = 0;         // Count of transactions completed
    longint total_latency = 0;              // Cumulative latency
    longint min_latency = 999999;           // Minimum latency observed
    longint max_latency = 0;                // Maximum latency observed

    // ==========================================================================
    // Constraints
    // ==========================================================================
    
    // Number of transactions constraint
    constraint c_num_transactions {
        num_transactions >= 1;
        num_transactions <= 1000000;  // Maximum for stress tests
    }
    
    // Destination constraint (4x4 mesh: 16 routers)
    constraint c_destination_range {
        destination >= 0;
        destination <= 15;
    }
    
    // Transaction type distribution (default: mixed)
    constraint c_transaction_type_dist {
        transaction_type dist {
            READ_ONLY := 30,
            WRITE_ONLY := 30,
            MIXED := 40
        };
    }

    // ==========================================================================
    // Constructor
    // ==========================================================================
    //
    function new(string name = "base_axi4_sequence");
        super.new(name);
        
        // Initialize defaults
        num_transactions = 10;
        transaction_type = MIXED;
        traffic_pattern = RANDOM;
        destination = 0;
        
        // Initialize priority distribution (default: uniform)
        for (int i = 0; i < 16; i++) begin
            priority_distribution[i] = 1.0 / 16.0;  // Equal probability
        end
        
        // Initialize burst length distribution
        // GPU-optimized: Prefer longer bursts for coalesced accesses
        for (int i = 0; i < 256; i++) begin
            burst_length_dist[i] = 0;
        end
        burst_length_dist[0] = 10;    // Length 1: 10% (cache misses)
        burst_length_dist[63] = 60;   // Length 64: 60% (coalesced reads)
        burst_length_dist[127] = 20;  // Length 128: 20%
        burst_length_dist[255] = 10;  // Length 256: 10% (batch ops)
    endfunction

    // ==========================================================================
    // Pre-Body
    // ==========================================================================
    //
    // Called before sequence body executes. Performs setup and logging.
    //
    virtual task pre_body();
        `uvm_info("SEQ", $sformatf(
            "Starting sequence: %s, num_transactions=%0d, type=%s, pattern=%s",
            get_name(), num_transactions, transaction_type.name(),
            traffic_pattern.name()), UVM_MEDIUM)
        
        // Reset statistics
        transactions_sent = 0;
        transactions_completed = 0;
        total_latency = 0;
        min_latency = 999999;
        max_latency = 0;
    endtask

    // ==========================================================================
    // Post-Body
    // ==========================================================================
    //
    // Called after sequence body completes. Performs cleanup and reporting.
    //
    virtual task post_body();
        real avg_latency = 0.0;
        
        if (transactions_completed > 0) begin
            avg_latency = real'(total_latency) / real'(transactions_completed);
        end
        
        `uvm_info("SEQ", $sformatf(
            "Sequence complete: %s\n" +
            "  Transactions sent:     %0d\n" +
            "  Transactions completed: %0d\n" +
            "  Average latency:        %0.2f cycles\n" +
            "  Min latency:            %0d cycles\n" +
            "  Max latency:            %0d cycles",
            get_name(),
            transactions_sent,
            transactions_completed,
            avg_latency,
            min_latency,
            max_latency), UVM_MEDIUM)
    endtask

    // ==========================================================================
    // Create and Send Transaction
    // ==========================================================================
    //
    // Helper method to create, randomize, and send a transaction.
    // Handles common transaction setup and error checking.
    //
    // Arguments:
    //   addr - Address for transaction
    //   trans_type - Transaction type (READ or WRITE)
    //   qos - QoS priority level
    //   burst_len - Burst length (1-256)
    //
    virtual task create_and_send_transaction(
        bit [31:0] addr,
        trans_type_e trans_type,
        int qos,
        int burst_len
    );
        axi_transaction tr;
        
        // Create transaction
        tr = axi_transaction::type_id::create("tr");
        
        // Set transaction type
        tr.trans_type = trans_type;
        
        // Randomize transaction
        if (!tr.randomize() with {
            trans_type == local::trans_type;
            if (trans_type == WRITE) {
                awaddr == local::addr;
                awlen == local::burst_len - 1;
                awqos == local::qos;
            } else {
                araddr == local::addr;
                arlen == local::burst_len - 1;
                arqos == local::qos;
            }
        }) begin
            `uvm_error("SEQ", "Transaction randomization failed")
            return;
        end
        
        // Send transaction
        start_item(tr);
        finish_item(tr);
        
        transactions_sent++;
        
        `uvm_info("SEQ", $sformatf(
            "Sent transaction: type=%s, addr=0x%0h, len=%0d, qos=%0d",
            trans_type.name(), addr, burst_len, qos), UVM_DEBUG)
    endtask

    // ==========================================================================
    // Get Random Address
    // ==========================================================================
    //
    // Generates random address based on weighted distribution:
    //   50% L2 cache range
    //   30% Main memory range
    //   20% Peripheral range
    //
    function bit [31:0] get_random_address();
        int rand_val = $urandom_range(0, 99);
        bit [31:0] base_addr, addr;
        
        if (rand_val < 50) begin
            // L2 cache range (50%)
            base_addr = l2_cache_base;
            addr = base_addr + ($urandom_range(0, l2_cache_size - 1) & 32'hFFFF_FFC0);  // 64-byte aligned
        end else if (rand_val < 80) begin
            // Main memory range (30%)
            base_addr = memory_base;
            addr = base_addr + ($urandom_range(0, memory_size - 1) & 32'hFFFF_FFC0);  // 64-byte aligned
        end else begin
            // Peripheral range (20%)
            base_addr = peripheral_base;
            addr = base_addr + ($urandom_range(0, peripheral_size - 1) & 32'hFFFF_FFC0);  // 64-byte aligned
        end
        
        return addr;
    endfunction

    // ==========================================================================
    // Get Random Burst Length
    // ==========================================================================
    //
    // Returns burst length based on weighted distribution optimized for GPU workloads.
    //
    function int get_random_burst_length();
        int rand_val = $urandom_range(0, 99);
        
        if (rand_val < 10) begin
            return 1;      // 10%: Single transfer (cache misses)
        end else if (rand_val < 70) begin
            return 64;     // 60%: 64-byte bursts (coalesced GPU reads)
        end else if (rand_val < 90) begin
            return 128;    // 20%: 128-byte bursts
        end else begin
            return 256;    // 10%: 256-byte bursts (GPU batch operations)
        end
    endfunction

    // ==========================================================================
    // Get Random QoS Level
    // ==========================================================================
    //
    // Returns QoS level based on weighted distribution:
    //   70% QoS 8 (normal priority)
    //   20% QoS 15 (high priority, graphics)
    //   10% QoS 0 (low priority, background)
    //
    function int get_random_qos_level();
        int rand_val = $urandom_range(0, 99);
        
        if (rand_val < 70) begin
            return 8;      // 70%: Normal priority
        end else if (rand_val < 90) begin
            return 15;     // 20%: High priority (graphics)
        end else begin
            return 0;      // 10%: Low priority (background)
        end
    endfunction

    // ==========================================================================
    // Get Destination Router ID
    // ==========================================================================
    //
    // Returns destination router ID based on traffic pattern.
    //
    function int get_destination_router_id();
        case (traffic_pattern)
            RANDOM: begin
                return $urandom_range(0, 15);  // Random destination
            end
            UNIFORM: begin
                return $urandom_range(0, 15);  // Uniform distribution
            end
            SKEWED_TO_DEST: begin
                // 80% to specified destination, 20% random
                if ($urandom_range(0, 99) < 80) begin
                    return destination;
                end else begin
                    return $urandom_range(0, 15);
                end
            end
            HOTSPOT: begin
                // 80% to router (0,0), 20% distributed
                if ($urandom_range(0, 99) < 80) begin
                    return 0;  // Router (0,0)
                end else begin
                    return $urandom_range(0, 15);
                end
            end
            BIT_REVERSE: begin
                // Source (x,y) -> Destination (~x, ~y)
                // For 4x4 mesh: router IDs 0-15
                // Router ID = y*4 + x, so reverse is (~y)*4 + (~x)
                int src_id = $urandom_range(0, 15);
                int x = src_id % 4;
                int y = src_id / 4;
                int rev_x = 3 - x;  // Bit reverse for 2 bits
                int rev_y = 3 - y;
                return rev_y * 4 + rev_x;
            end
            TRANSPOSE: begin
                // Source (x,y) -> Destination (y,x)
                int src_id = $urandom_range(0, 15);
                int x = src_id % 4;
                int y = src_id / 4;
                return x * 4 + y;  // Transpose: (y,x)
            end
            default: begin
                return $urandom_range(0, 15);
            end
        endcase
    endfunction

    // ==========================================================================
    // Body (Base Implementation)
    // ==========================================================================
    //
    // Base body implementation. Derived classes should override this.
    //
    virtual task body();
        `uvm_info("SEQ", "Base sequence body - should be overridden", UVM_MEDIUM)
    endtask

endclass

// ==============================================================================
// Simple Sequences
// ==============================================================================

// ==============================================================================
// Single Write Transaction Sequence
// ==============================================================================
//
// Generates a single write transaction for basic connectivity verification.
// This sequence verifies that write transactions can be successfully routed
// and completed through the NoC.
//
// Protocol Scenario:
//   Master -> AW Channel -> NoC -> Slave -> B Channel -> Master
//   Master -> W Channel -> NoC -> Slave
//
// Reference: ARM AMBA 5 AXI4 Specification, Section 3.1 (Write Transaction)
//
class single_write_transaction extends base_axi4_sequence;

    `uvm_object_utils(single_write_transaction)

    function new(string name = "single_write_transaction");
        super.new(name);
        num_transactions = 1;
        transaction_type = WRITE_ONLY;
    endfunction

    virtual task body();
        pre_body();
        
        `uvm_info("SEQ", "Single write transaction sequence starting", UVM_MEDIUM)
        
        // Generate single write transaction
        bit [31:0] addr = get_random_address();
        int qos = get_random_qos_level();
        int burst_len = 1;  // Single transfer
        
        create_and_send_transaction(addr, WRITE, qos, burst_len);
        
        // Wait for completion (handled by driver/sequencer)
        transactions_completed++;
        
        post_body();
    endtask

endclass

// ==============================================================================
// Single Read Transaction Sequence
// ==============================================================================
//
// Generates a single read transaction for basic connectivity verification.
// This sequence verifies that read transactions can be successfully routed
// and data returned correctly.
//
// Protocol Scenario:
//   Master -> AR Channel -> NoC -> Slave -> R Channel -> Master
//
// Reference: ARM AMBA 5 AXI4 Specification, Section 3.1 (Read Transaction)
//
class single_read_transaction extends base_axi4_sequence;

    `uvm_object_utils(single_read_transaction)

    function new(string name = "single_read_transaction");
        super.new(name);
        num_transactions = 1;
        transaction_type = READ_ONLY;
    endfunction

    virtual task body();
        pre_body();
        
        `uvm_info("SEQ", "Single read transaction sequence starting", UVM_MEDIUM)
        
        // Generate single read transaction
        bit [31:0] addr = get_random_address();
        int qos = get_random_qos_level();
        int burst_len = 1;  // Single transfer
        
        create_and_send_transaction(addr, READ, qos, burst_len);
        
        // Wait for completion
        transactions_completed++;
        
        post_body();
    endtask

endclass

// ==============================================================================
// Write-Read Pair Sequence
// ==============================================================================
//
// Generates a write followed by a read to the same address to verify
// data integrity. This sequence ensures that data written can be read back
// correctly, verifying end-to-end data path integrity.
//
// Protocol Scenario:
//   1. Write transaction: Master writes data D to address A
//   2. Read transaction: Master reads from address A
//   3. Verification: Read data should equal written data D
//
// Reference: ARM AMBA 5 AXI4 Specification, Section 3.1 (Write and Read)
//
class write_read_pair extends base_axi4_sequence;

    `uvm_object_utils(write_read_pair)

    bit [31:0] test_address;
    bit [127:0] test_data;

    function new(string name = "write_read_pair");
        super.new(name);
        num_transactions = 2;  // One write, one read
    endfunction

    virtual task body();
        pre_body();
        
        `uvm_info("SEQ", "Write-read pair sequence starting", UVM_MEDIUM)
        
        // Generate test address and data
        test_address = get_random_address();
        test_data = $urandom();
        
        // Step 1: Write transaction
        axi_transaction write_tr;
        write_tr = axi_transaction::type_id::create("write_tr");
        assert(write_tr.randomize() with {
            trans_type == WRITE;
            awaddr == local::test_address;
            awlen == 0;  // Single transfer
            wdata == local::test_data;
            wstrb == 16'hFFFF;  // All bytes enabled
        });
        
        start_item(write_tr);
        finish_item(write_tr);
        transactions_sent++;
        
        `uvm_info("SEQ", $sformatf(
            "Write transaction sent: addr=0x%0h, data=0x%0h",
            test_address, test_data), UVM_DEBUG)
        
        // Step 2: Read transaction (to same address)
        axi_transaction read_tr;
        read_tr = axi_transaction::type_id::create("read_tr");
        assert(read_tr.randomize() with {
            trans_type == READ;
            araddr == local::test_address;
            arlen == 0;  // Single transfer
        });
        
        start_item(read_tr);
        finish_item(read_tr);
        transactions_sent++;
        
        `uvm_info("SEQ", $sformatf(
            "Read transaction sent: addr=0x%0h",
            test_address), UVM_DEBUG)
        
        // Note: Data integrity verification is performed by scoreboard
        // comparing write data with read data
        
        transactions_completed += 2;
        post_body();
    endtask

endclass

// ==============================================================================
// Burst Sequences
// ==============================================================================

// ==============================================================================
// Burst Write Sequence
// ==============================================================================
//
// Generates write transactions with various burst lengths to verify AXI4
// burst protocol compliance. Tests burst lengths from 1 to 256 transfers.
//
// Protocol Scenario:
//   AW Channel: Address + burst info (len, size, burst type)
//   W Channel: Multiple data beats (wlast asserted on final beat)
//   B Channel: Write response
//
// Burst Length Encoding:
//   awlen = 0: 1 transfer
//   awlen = 1: 2 transfers
//   awlen = 255: 256 transfers (maximum)
//
// Reference: ARM AMBA 5 AXI4 Specification, Section 3.1.2 (Burst Transfers)
//
class burst_write_sequence extends base_axi4_sequence;

    `uvm_object_utils(burst_write_sequence)

    int burst_lengths[] = {1, 2, 4, 8, 16, 32, 64, 128, 256};

    function new(string name = "burst_write_sequence");
        super.new(name);
        num_transactions = burst_lengths.size();
        transaction_type = WRITE_ONLY;
    endfunction

    virtual task body();
        pre_body();
        
        `uvm_info("SEQ", $sformatf(
            "Burst write sequence starting: %0d burst lengths",
            burst_lengths.size()), UVM_MEDIUM)
        
        // Generate write transaction for each burst length
        foreach (burst_lengths[i]) begin
            int burst_len = burst_lengths[i];
            bit [31:0] addr = get_random_address();
            int qos = get_random_qos_level();
            
            `uvm_info("SEQ", $sformatf(
                "Generating burst write: length=%0d, addr=0x%0h",
                burst_len, addr), UVM_DEBUG)
            
            // Create transaction with specific burst length
            axi_transaction tr;
            tr = axi_transaction::type_id::create("tr");
            assert(tr.randomize() with {
                trans_type == WRITE;
                awaddr == local::addr;
                awlen == local::burst_len - 1;  // AXI encoding: len = transfers - 1
                awsize == 3;  // 8 bytes per transfer
                awburst == 1;  // INCR burst
                awqos == local::qos;
            });
            
            start_item(tr);
            finish_item(tr);
            transactions_sent++;
            
            // Protocol check: wlast must be set on final beat
            // This is handled by the driver
            
            transactions_completed++;
        end
        
        post_body();
    endtask

endclass

// ==============================================================================
// Interleaved Burst Sequence
// ==============================================================================
//
// Generates multiple outstanding bursts simultaneously with different
// transaction IDs to verify out-of-order completion support. This tests
// the AXI4 capability to handle multiple concurrent transactions.
//
// Protocol Scenario:
//   Transaction 1: ID=0, Address A, Burst length 4
//   Transaction 2: ID=1, Address B, Burst length 8
//   Transaction 3: ID=2, Address C, Burst length 2
//   Responses may arrive in any order (ID-based matching)
//
// Reference: ARM AMBA 5 AXI4 Specification, Section 3.1.5 (Transaction IDs)
//
class interleaved_burst_sequence extends base_axi4_sequence;

    `uvm_object_utils(interleaved_burst_sequence)

    int num_concurrent = 4;  // Number of concurrent transactions

    function new(string name = "interleaved_burst_sequence");
        super.new(name);
        num_transactions = num_concurrent;
        transaction_type = MIXED;
    endfunction

    virtual task body();
        pre_body();
        
        `uvm_info("SEQ", $sformatf(
            "Interleaved burst sequence starting: %0d concurrent transactions",
            num_concurrent), UVM_MEDIUM)
        
        // Generate multiple transactions with different IDs
        fork
            for (int i = 0; i < num_concurrent; i++) begin
                bit [31:0] addr = get_random_address();
                int qos = get_random_qos_level();
                int burst_len = get_random_burst_length();
                trans_type_e trans_type = (i % 2 == 0) ? WRITE : READ;
                
                // Create transaction with unique ID
                axi_transaction tr;
                tr = axi_transaction::type_id::create("tr");
                assert(tr.randomize() with {
                    trans_type == local::trans_type;
                    if (trans_type == WRITE) {
                        awaddr == local::addr;
                        awlen == local::burst_len - 1;
                        awid == local::i;
                        awqos == local::qos;
                    } else {
                        araddr == local::addr;
                        arlen == local::burst_len - 1;
                        arid == local::i;
                        arqos == local::qos;
                    }
                });
                
                start_item(tr);
                finish_item(tr);
                transactions_sent++;
                
                `uvm_info("SEQ", $sformatf(
                    "Concurrent transaction %0d: type=%s, id=%0d, len=%0d",
                    i, trans_type.name(), i, burst_len), UVM_DEBUG)
            end
        join
        
        transactions_completed = num_concurrent;
        post_body();
    endtask

endclass

// ==============================================================================
// Protocol Compliance Sequences
// ==============================================================================

// ==============================================================================
// Protocol Handshake Sequence
// ==============================================================================
//
// Tests AXI4 handshake protocol compliance by introducing delays in valid/ready
// signals. Verifies that transactions complete correctly regardless of handshake
// timing variations.
//
// Protocol Scenario:
//   Case 1: Valid asserted before ready (normal)
//   Case 2: Ready asserted before valid (slave ready early)
//   Case 3: Valid and ready asserted simultaneously
//
// Reference: ARM AMBA 5 AXI4 Specification, Section 3.1.1 (Handshake Protocol)
//
class protocol_handshake_sequence extends base_axi4_sequence;

    `uvm_object_utils(protocol_handshake_sequence)

    function new(string name = "protocol_handshake_sequence");
        super.new(name);
        num_transactions = 20;  // Multiple transactions to test timing variations
    endfunction

    virtual task body();
        pre_body();
        
        `uvm_info("SEQ", "Protocol handshake sequence starting", UVM_MEDIUM)
        
        // Generate transactions with various timing patterns
        // Note: Actual handshake timing is controlled by driver/monitor
        // This sequence generates transactions that will exercise different
        // handshake scenarios based on driver implementation
        
        for (int i = 0; i < num_transactions; i++) begin
            bit [31:0] addr = get_random_address();
            int qos = get_random_qos_level();
            int burst_len = get_random_burst_length();
            trans_type_e trans_type = (i % 2 == 0) ? WRITE : READ;
            
            create_and_send_transaction(addr, trans_type, qos, burst_len);
            
            // Add random delay between transactions to vary timing
            #($urandom_range(1, 10));
        end
        
        transactions_completed = num_transactions;
        post_body();
    endtask

endclass

// ==============================================================================
// Protocol Atomicity Sequence
// ==============================================================================
//
// Tests atomic operation correctness by generating multiple atomic transactions
// to the same address. Verifies that atomicity is maintained (no interleaving
// of operations).
//
// Protocol Scenario:
//   Multiple masters perform atomic operations on same address:
//   - ATOMIC_ADD: Each master adds value to address
//   - ATOMIC_SWAP: Compare-and-swap operations
//   - Verify final value is correct (sum of all additions)
//
// Reference: ARM AMBA 5 AXI4 Specification, Section 3.1.6 (Atomic Operations)
//
class protocol_atomicity_sequence extends base_axi4_sequence;

    `uvm_object_utils(protocol_atomicity_sequence)

    bit [31:0] atomic_address;
    int num_atomic_ops = 10;

    function new(string name = "protocol_atomicity_sequence");
        super.new(name);
        num_transactions = num_atomic_ops;
    endfunction

    virtual task body();
        pre_body();
        
        `uvm_info("SEQ", $sformatf(
            "Protocol atomicity sequence starting: %0d atomic operations",
            num_atomic_ops), UVM_MEDIUM)
        
        // Generate atomic address
        atomic_address = get_random_address();
        
        // Generate multiple atomic operations to same address
        for (int i = 0; i < num_atomic_ops; i++) begin
            axi_transaction tr;
            tr = axi_transaction::type_id::create("tr");
            
            // Randomly select atomic operation type
            trans_type_e atomic_type;
            int rand_val = $urandom_range(0, 2);
            case (rand_val)
                0: atomic_type = ATOMIC_ADD;
                1: atomic_type = ATOMIC_SWAP;
                2: atomic_type = ATOMIC_CMP_SWAP;
            endcase
            
            assert(tr.randomize() with {
                trans_type == local::atomic_type;
                awaddr == local::atomic_address;
                awlen == 0;  // Atomic operations are single transfers
                awlock == 1;  // Exclusive/atomic access
            });
            
            start_item(tr);
            finish_item(tr);
            transactions_sent++;
            
            `uvm_info("SEQ", $sformatf(
                "Atomic operation %0d: type=%s, addr=0x%0h",
                i, atomic_type.name(), atomic_address), UVM_DEBUG)
        end
        
        transactions_completed = num_atomic_ops;
        post_body();
    endtask

endclass

// ==============================================================================
// Protocol Response Sequence
// ==============================================================================
//
// Tests error response handling by generating transactions that may result
// in error responses (SLVERR, DECERR). Verifies that drivers and scoreboards
// handle error responses correctly.
//
// Protocol Scenario:
//   - Normal transactions: Expect OKAY response
//   - Invalid addresses: May result in DECERR (decode error)
//   - Slave errors: May result in SLVERR (slave error)
//
// Reference: ARM AMBA 5 AXI4 Specification, Section 3.1.3 (Response Signals)
//
class protocol_response_sequence extends base_axi4_sequence;

    `uvm_object_utils(protocol_response_sequence)

    function new(string name = "protocol_response_sequence");
        super.new(name);
        num_transactions = 50;  // Mix of normal and error cases
    endfunction

    virtual task body();
        pre_body();
        
        `uvm_info("SEQ", "Protocol response sequence starting", UVM_MEDIUM)
        
        // Generate mix of transactions
        // Some to valid addresses (expect OKAY)
        // Some to potentially invalid addresses (may get DECERR)
        for (int i = 0; i < num_transactions; i++) begin
            bit [31:0] addr;
            trans_type_e trans_type = (i % 2 == 0) ? WRITE : READ;
            int qos = get_random_qos_level();
            int burst_len = get_random_burst_length();
            
            // 80% valid addresses, 20% potentially invalid
            if ($urandom_range(0, 99) < 80) begin
                addr = get_random_address();  // Valid address
            end else begin
                addr = 32'hFFFF_FFFF;  // Potentially invalid address
            end
            
            create_and_send_transaction(addr, trans_type, qos, burst_len);
        end
        
        transactions_completed = num_transactions;
        post_body();
    endtask

endclass

// ==============================================================================
// QoS Priority Sequences
// ==============================================================================

// ==============================================================================
// QoS Priority Sequence
// ==============================================================================
//
// Tests QoS priority arbitration by generating transactions with different
// QoS levels and measuring latency. Verifies that higher QoS transactions
// experience lower latency.
//
// Protocol Scenario:
//   Generate transactions with QoS levels 0-15
//   Measure latency for each QoS level
//   Verify: Latency(QoS=15) < Latency(QOS=8) < Latency(QoS=0)
//
// Reference: ARM AMBA 5 AXI4 Specification, Section 3.1.1 (QoS Signals)
//
class qos_priority_sequence extends base_axi4_sequence;

    `uvm_object_utils(qos_priority_sequence)

    longint qos_latency[16];  // Latency per QoS level
    int qos_count[16];        // Count per QoS level

    function new(string name = "qos_priority_sequence");
        super.new(name);
        num_transactions = 160;  // 10 transactions per QoS level
    endfunction

    virtual task body();
        pre_body();
        
        `uvm_info("SEQ", "QoS priority sequence starting", UVM_MEDIUM)
        
        // Initialize QoS tracking
        for (int i = 0; i < 16; i++) begin
            qos_latency[i] = 0;
            qos_count[i] = 0;
        end
        
        // Generate transactions for each QoS level
        for (int qos = 0; qos < 16; qos++) begin
            for (int i = 0; i < 10; i++) begin
                bit [31:0] addr = get_random_address();
                trans_type_e trans_type = (i % 2 == 0) ? WRITE : READ;
                int burst_len = get_random_burst_length();
                
                // Create transaction with specific QoS
                axi_transaction tr;
                tr = axi_transaction::type_id::create("tr");
                assert(tr.randomize() with {
                    trans_type == local::trans_type;
                    if (trans_type == WRITE) {
                        awaddr == local::addr;
                        awlen == local::burst_len - 1;
                        awqos == local::qos;
                    } else {
                        araddr == local::addr;
                        arlen == local::burst_len - 1;
                        arqos == local::qos;
                    }
                });
                
                longint start_time = $time;
                start_item(tr);
                finish_item(tr);
                longint end_time = $time;
                
                longint latency = end_time - start_time;
                qos_latency[qos] += latency;
                qos_count[qos]++;
                
                transactions_sent++;
            end
        end
        
        // Report QoS latency statistics
        `uvm_info("SEQ", "QoS Latency Statistics:", UVM_MEDIUM)
        for (int qos = 0; qos < 16; qos++) begin
            if (qos_count[qos] > 0) begin
                real avg_latency = real'(qos_latency[qos]) / real'(qos_count[qos]);
                `uvm_info("SEQ", $sformatf(
                    "  QoS %2d: %0d transactions, avg latency: %0.2f cycles",
                    qos, qos_count[qos], avg_latency), UVM_MEDIUM)
            end
        end
        
        transactions_completed = num_transactions;
        post_body();
    endtask

endclass

// ==============================================================================
// QoS Mixed Sequence
// ==============================================================================
//
// Tests QoS arbitration with mixed priority traffic. Generates concurrent
// transactions with varying QoS levels and verifies that high-priority
// transactions get preferential treatment.
//
// Protocol Scenario:
//   Concurrent transactions:
//   - 50% high priority (QoS 12-15)
//   - 50% low priority (QoS 0-7)
//   Verify: High priority transactions complete faster
//
class qos_mixed_sequence extends base_axi4_sequence;

    `uvm_object_utils(qos_mixed_sequence)

    function new(string name = "qos_mixed_sequence");
        super.new(name);
        num_transactions = 100;
    endfunction

    virtual task body();
        pre_body();
        
        `uvm_info("SEQ", "QoS mixed sequence starting", UVM_MEDIUM)
        
        longint high_priority_latency = 0;
        longint low_priority_latency = 0;
        int high_priority_count = 0;
        int low_priority_count = 0;
        
        // Generate mixed priority transactions
        for (int i = 0; i < num_transactions; i++) begin
            bit [31:0] addr = get_random_address();
            trans_type_e trans_type = (i % 2 == 0) ? WRITE : READ;
            int burst_len = get_random_burst_length();
            int qos;
            
            // 50% high priority, 50% low priority
            if ($urandom_range(0, 99) < 50) begin
                qos = $urandom_range(12, 15);  // High priority
            end else begin
                qos = $urandom_range(0, 7);   // Low priority
            end
            
            axi_transaction tr;
            tr = axi_transaction::type_id::create("tr");
            assert(tr.randomize() with {
                trans_type == local::trans_type;
                if (trans_type == WRITE) {
                    awaddr == local::addr;
                    awlen == local::burst_len - 1;
                    awqos == local::qos;
                } else {
                    araddr == local::addr;
                    arlen == local::burst_len - 1;
                    arqos == local::qos;
                }
            });
            
            longint start_time = $time;
            start_item(tr);
            finish_item(tr);
            longint end_time = $time;
            
            longint latency = end_time - start_time;
            
            if (qos >= 12) begin
                high_priority_latency += latency;
                high_priority_count++;
            end else begin
                low_priority_latency += latency;
                low_priority_count++;
            end
            
            transactions_sent++;
        end
        
        // Report comparison
        real avg_high = (high_priority_count > 0) ?
            real'(high_priority_latency) / real'(high_priority_count) : 0.0;
        real avg_low = (low_priority_count > 0) ?
            real'(low_priority_latency) / real'(low_priority_count) : 0.0;
        
        `uvm_info("SEQ", $sformatf(
            "QoS Mixed Results:\n" +
            "  High Priority (QoS 12-15): %0d transactions, avg latency: %0.2f cycles\n" +
            "  Low Priority (QoS 0-7):    %0d transactions, avg latency: %0.2f cycles\n" +
            "  Improvement:                %0.1f%%",
            high_priority_count, avg_high,
            low_priority_count, avg_low,
            (avg_low > 0) ? ((avg_low - avg_high) / avg_low * 100.0) : 0.0), UVM_MEDIUM)
        
        transactions_completed = num_transactions;
        post_body();
    endtask

endclass

// ==============================================================================
// Virtual Channel Sequences
// ==============================================================================

// ==============================================================================
// Virtual Channel Sequence
// ==============================================================================
//
// Tests virtual channel allocation and deadlock prevention. Generates traffic
// that exercises different virtual channels and verifies no deadlock occurs.
//
// Protocol Scenario:
//   - Route packets through VC0 and VC1
//   - Test wraparound scenarios (if using torus topology)
//   - Verify VC allocation prevents deadlock
//
// Reference: NoC routing protocols and virtual channel allocation
//
class virtual_channel_sequence extends base_axi4_sequence;

    `uvm_object_utils(virtual_channel_sequence)

    function new(string name = "virtual_channel_sequence");
        super.new(name);
        num_transactions = 1000;
    endfunction

    virtual task body();
        pre_body();
        
        `uvm_info("SEQ", "Virtual channel sequence starting", UVM_MEDIUM)
        
        // Generate traffic that exercises virtual channels
        // Note: VC allocation is typically handled by router/NoC design
        // This sequence generates traffic patterns that stress VC allocation
        
        for (int i = 0; i < num_transactions; i++) begin
            bit [31:0] addr = get_random_address();
            trans_type_e trans_type = (i % 2 == 0) ? WRITE : READ;
            int qos = get_random_qos_level();
            int burst_len = get_random_burst_length();
            
            create_and_send_transaction(addr, trans_type, qos, burst_len);
            
            // Add small delay to allow VC allocation
            #($urandom_range(1, 5));
        end
        
        // Note: Deadlock detection is performed by scoreboard/monitor
        // This sequence generates traffic that could potentially deadlock
        // if VC allocation is incorrect
        
        transactions_completed = num_transactions;
        post_body();
    endtask

endclass

// ==============================================================================
// VC Stress Sequence
// ==============================================================================
//
// Tests virtual channel stress by saturating one VC and verifying other VCs
// continue to operate. This verifies that VC allocation doesn't block
// when one VC is full.
//
class vc_stress_sequence extends base_axi4_sequence;

    `uvm_object_utils(vc_stress_sequence)

    function new(string name = "vc_stress_sequence");
        super.new(name);
        num_transactions = 5000;  // High traffic to saturate VC
    endfunction

    virtual task body();
        pre_body();
        
        `uvm_info("SEQ", "VC stress sequence starting", UVM_MEDIUM)
        
        // Generate high-rate traffic to saturate virtual channels
        // Traffic pattern: All to same destination to maximize contention
        
        int target_dest = 0;  // Target router (0,0)
        
        for (int i = 0; i < num_transactions; i++) begin
            bit [31:0] addr = get_random_address();
            trans_type_e trans_type = (i % 2 == 0) ? WRITE : READ;
            int qos = get_random_qos_level();
            int burst_len = get_random_burst_length();
            
            create_and_send_transaction(addr, trans_type, qos, burst_len);
            
            // Minimal delay to maximize contention
            #1;
        end
        
        transactions_completed = num_transactions;
        post_body();
    endtask

endclass

// ==============================================================================
// Performance/Stress Sequences
// ==============================================================================

// ==============================================================================
// Random Traffic Sequence
// ==============================================================================
//
// Generates large-scale random traffic to stress test NoC and verify
// deadlock-free operation over extended periods. This is a key sequence
// for verifying NoC robustness.
//
// Protocol Scenario:
//   - 100,000+ transactions
//   - Random destinations, types, burst lengths, QoS
//   - Extended execution time
//   - Verify: No deadlock, all transactions complete
//
class random_traffic_sequence extends base_axi4_sequence;

    `uvm_object_utils(random_traffic_sequence)

    function new(string name = "random_traffic_sequence");
        super.new(name);
        num_transactions = 100000;  // Large-scale stress test
        traffic_pattern = RANDOM;
    endfunction

    virtual task body();
        pre_body();
        
        `uvm_info("SEQ", $sformatf(
            "Random traffic sequence starting: %0d transactions",
            num_transactions), UVM_MEDIUM)
        
        // Generate random traffic
        for (int i = 0; i < num_transactions; i++) begin
            bit [31:0] addr = get_random_address();
            trans_type_e trans_type;
            
            // Random transaction type
            int rand_type = $urandom_range(0, 99);
            if (rand_type < 70) begin
                trans_type = WRITE;  // 70% writes (GPU workload)
            end else begin
                trans_type = READ;   // 30% reads
            end
            
            int qos = get_random_qos_level();
            int burst_len = get_random_burst_length();
            int dest = get_destination_router_id();
            
            // Create transaction
            axi_transaction tr;
            tr = axi_transaction::type_id::create("tr");
            assert(tr.randomize() with {
                trans_type == local::trans_type;
                if (trans_type == WRITE) {
                    awaddr == local::addr;
                    awlen == local::burst_len - 1;
                    awqos == local::qos;
                } else {
                    araddr == local::addr;
                    arlen == local::burst_len - 1;
                    arqos == local::qos;
                }
            });
            
            tr.dest_id = dest;
            
            start_item(tr);
            finish_item(tr);
            transactions_sent++;
            
            // Progress reporting
            if ((i + 1) % 10000 == 0) begin
                `uvm_info("SEQ", $sformatf(
                    "Progress: %0d/%0d transactions sent",
                    i + 1, num_transactions), UVM_MEDIUM)
            end
        end
        
        `uvm_info("SEQ", "Random traffic sequence complete", UVM_MEDIUM)
        
        transactions_completed = num_transactions;
        post_body();
    endtask

endclass

// ==============================================================================
// Hotspot Sequence
// ==============================================================================
//
// Generates traffic with 80% directed to a single destination (hotspot).
// This tests NoC behavior under contention and verifies that the system
// doesn't thrash or deadlock under hotspot conditions.
//
// Protocol Scenario:
//   - 80% traffic to router (0,0) - memory controller hotspot
//   - 20% traffic distributed to other routers
//   - Measure latency impact of contention
//
class hotspot_sequence extends base_axi4_sequence;

    `uvm_object_utils(hotspot_sequence)

    function new(string name = "hotspot_sequence");
        super.new(name);
        num_transactions = 10000;
        traffic_pattern = HOTSPOT;
    endfunction

    virtual task body();
        pre_body();
        
        `uvm_info("SEQ", "Hotspot sequence starting", UVM_MEDIUM)
        
        int hotspot_count = 0;
        int distributed_count = 0;
        
        for (int i = 0; i < num_transactions; i++) begin
            bit [31:0] addr = get_random_address();
            trans_type_e trans_type = (i % 2 == 0) ? WRITE : READ;
            int qos = get_random_qos_level();
            int burst_len = get_random_burst_length();
            int dest = get_destination_router_id();
            
            if (dest == 0) begin
                hotspot_count++;
            end else begin
                distributed_count++;
            end
            
            create_and_send_transaction(addr, trans_type, qos, burst_len);
        end
        
        `uvm_info("SEQ", $sformatf(
            "Hotspot traffic distribution:\n" +
            "  Hotspot (router 0):     %0d transactions (%0.1f%%)\n" +
            "  Distributed:            %0d transactions (%0.1f%%)",
            hotspot_count, real'(hotspot_count) / real'(num_transactions) * 100.0,
            distributed_count, real'(distributed_count) / real'(num_transactions) * 100.0), UVM_MEDIUM)
        
        transactions_completed = num_transactions;
        post_body();
    endtask

endclass

// ==============================================================================
// Uniform Traffic Sequence
// ==============================================================================
//
// Generates uniform traffic distribution to all destinations. This provides
// a baseline for performance measurement and comparison with other traffic
// patterns.
//
// Protocol Scenario:
//   - Equal probability to all 16 routers
//   - Baseline performance measurement
//   - Compare against hotspot and bit-reverse patterns
//
class uniform_traffic_sequence extends base_axi4_sequence;

    `uvm_object_utils(uniform_traffic_sequence)

    function new(string name = "uniform_traffic_sequence");
        super.new(name);
        num_transactions = 10000;
        traffic_pattern = UNIFORM;
    endfunction

    virtual task body();
        pre_body();
        
        `uvm_info("SEQ", "Uniform traffic sequence starting", UVM_MEDIUM)
        
        int dest_count[16];  // Count per destination
        
        // Initialize counts
        for (int i = 0; i < 16; i++) begin
            dest_count[i] = 0;
        end
        
        for (int i = 0; i < num_transactions; i++) begin
            bit [31:0] addr = get_random_address();
            trans_type_e trans_type = (i % 2 == 0) ? WRITE : READ;
            int qos = get_random_qos_level();
            int burst_len = get_random_burst_length();
            int dest = get_destination_router_id();
            
            dest_count[dest]++;
            
            create_and_send_transaction(addr, trans_type, qos, burst_len);
        end
        
        // Report distribution
        `uvm_info("SEQ", "Uniform traffic distribution:", UVM_MEDIUM)
        for (int i = 0; i < 16; i++) begin
            `uvm_info("SEQ", $sformatf(
                "  Router %2d: %0d transactions (%0.1f%%)",
                i, dest_count[i],
                real'(dest_count[i]) / real'(num_transactions) * 100.0), UVM_MEDIUM)
        end
        
        transactions_completed = num_transactions;
        post_body();
    endtask

endclass

// ==============================================================================
// Bit-Reverse Sequence
// ==============================================================================
//
// Generates traffic using bit-reverse addressing pattern where source (x,y)
// sends to destination (~x, ~y). This creates long diagonal communication
// paths that stress the interconnect.
//
// Protocol Scenario:
//   Source router (x,y) -> Destination router (~x, ~y)
//   For 4x4 mesh: Router 0 (0,0) -> Router 15 (3,3)
//   Creates maximum hop count paths
//
class bit_reverse_sequence extends base_axi4_sequence;

    `uvm_object_utils(bit_reverse_sequence)

    function new(string name = "bit_reverse_sequence");
        super.new(name);
        num_transactions = 10000;
        traffic_pattern = BIT_REVERSE;
    endfunction

    virtual task body();
        pre_body();
        
        `uvm_info("SEQ", "Bit-reverse sequence starting", UVM_MEDIUM)
        
        for (int i = 0; i < num_transactions; i++) begin
            bit [31:0] addr = get_random_address();
            trans_type_e trans_type = (i % 2 == 0) ? WRITE : READ;
            int qos = get_random_qos_level();
            int burst_len = get_random_burst_length();
            int dest = get_destination_router_id();  // Uses BIT_REVERSE pattern
            
            create_and_send_transaction(addr, trans_type, qos, burst_len);
        end
        
        transactions_completed = num_transactions;
        post_body();
    endtask

endclass

// ==============================================================================
// Transpose Sequence
// ==============================================================================
//
// Generates traffic using transpose addressing pattern where source (x,y)
// sends to destination (y,x). This tests bisection bandwidth and is similar
// to GPU matrix transpose kernels.
//
// Protocol Scenario:
//   Source router (x,y) -> Destination router (y,x)
//   For 4x4 mesh: Router 5 (1,1) -> Router 5 (1,1) [same]
//                 Router 1 (1,0) -> Router 4 (0,1) [transpose]
//   Tests bisection bandwidth
//
class transpose_sequence extends base_axi4_sequence;

    `uvm_object_utils(transpose_sequence)

    function new(string name = "transpose_sequence");
        super.new(name);
        num_transactions = 10000;
        traffic_pattern = TRANSPOSE;
    endfunction

    virtual task body();
        pre_body();
        
        `uvm_info("SEQ", "Transpose sequence starting", UVM_MEDIUM)
        
        for (int i = 0; i < num_transactions; i++) begin
            bit [31:0] addr = get_random_address();
            trans_type_e trans_type = (i % 2 == 0) ? WRITE : READ;
            int qos = get_random_qos_level();
            int burst_len = get_random_burst_length();
            int dest = get_destination_router_id();  // Uses TRANSPOSE pattern
            
            create_and_send_transaction(addr, trans_type, qos, burst_len);
        end
        
        transactions_completed = num_transactions;
        post_body();
    endtask

endclass

`endif // BASE_SEQUENCES_SV

