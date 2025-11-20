// ==============================================================================
// File: noc_scoreboard.sv
// Description: Self-Checking Scoreboard for GPU Interconnect NoC Verification
// Author: Verification Team
// Date: January 2025
// Copyright (c) 2025 NVIDIA Corporation
//
// This file implements a comprehensive self-checking scoreboard that verifies
// transaction correctness, protocol compliance, and performance metrics for
// the GPU interconnect NoC. The scoreboard receives transactions from master
// and slave monitors, matches them, and performs extensive validation.
//
// Self-Checking Strategy:
//   1. Input Tracking: Store transactions sent by masters in inflight queue
//   2. Output Matching: Match received transactions to inflight by ID/address
//   3. Protocol Validation: Check AXI4 compliance, data integrity, latency
//   4. Performance Analysis: Track latencies, throughput, QoS impact
//   5. Deadlock Detection: Monitor for stalled transactions
//
// Transaction Matching Algorithm:
//   - Match by transaction ID (awid/arid) for out-of-order completion
//   - Fallback to address matching if ID unavailable
//   - Handle burst transactions (multiple beats per transaction)
//   - Support concurrent transactions with same destination
//
// Reference: ARM AMBA 5 AXI4 Protocol Specification (ARM IHI 0022E)
// ==============================================================================

`ifndef NOC_SCOREBOARD_SV
`define NOC_SCOREBOARD_SV

import uvm_pkg::*;
`include "uvm_macros.svh"
`include "axi_transaction.sv"

// ==============================================================================
// Scoreboard Configuration Constants
// ==============================================================================
//
// These constants define thresholds and limits for scoreboard checking.
//
parameter int MAX_LATENCY_CYCLES = 1000;      // Maximum expected latency
parameter int MAX_WAIT_CYCLES = 10000;       // Maximum wait before starvation warning
parameter int DEADLOCK_CHECK_INTERVAL = 100; // Cycles between deadlock checks
parameter int MAX_OUTSTANDING_TRANS = 16;    // Maximum outstanding transactions per ID

// ==============================================================================
// Transaction Tracking Structure
// ==============================================================================
//
// Tracks in-flight transactions with metadata for matching and validation.
//
typedef struct {
    axi_transaction tr;           // Transaction object
    longint inject_time;          // Time transaction was injected
    longint last_progress_time;   // Last time transaction made progress
    int progress_count;           // Number of times progress was made
    bit matched;                  // Whether transaction has been matched
    int source_id;                // Source router ID
    int dest_id;                  // Destination router ID
} tracked_transaction_t;

// ==============================================================================
// Protocol Violation Structure
// ==============================================================================
//
// Records protocol violations with details for debugging.
//
typedef struct {
    string violation_type;        // Type of violation
    string description;           // Detailed description
    longint timestamp;            // When violation occurred
    int transaction_id;           // Transaction ID (if applicable)
    string expected_value;        // Expected value
    string actual_value;          // Actual value
    string likely_cause;          // Suggested root cause
} protocol_violation_t;

// ==============================================================================
// Latency Log Entry Structure
// ==============================================================================
//
// Records latency information for performance analysis.
//
typedef struct {
    int trans_id;                 // Transaction ID
    longint latency;              // Latency in cycles
    trans_type_e trans_type;      // Transaction type
    int qos_level;                // QoS level
    int source_id;                // Source router ID
    int dest_id;                  // Destination router ID
} latency_log_entry_t;

// ==============================================================================
// NoC Scoreboard Class
// ==============================================================================
//
// The scoreboard implements self-checking by comparing transactions sent by
// masters with transactions received at slaves. It validates protocol compliance,
// data integrity, and performance metrics.
//
class noc_scoreboard extends uvm_scoreboard;

    // UVM Factory Registration
    `uvm_component_utils(noc_scoreboard)

    // ==========================================================================
    // Analysis Exports
    // ==========================================================================
    //
    // Multiple analysis exports allow the scoreboard to receive transactions
    // from different sources (master monitors, slave monitors, internal monitors).
    //
    uvm_analysis_imp #(axi_transaction, noc_scoreboard) input_analysis_export;
    uvm_analysis_imp #(axi_transaction, noc_scoreboard) output_analysis_export;
    uvm_analysis_imp #(axi_transaction, noc_scoreboard) internal_export;
    
    // Helper to identify which export received the transaction
    string last_write_source;

    // ==========================================================================
    // Transaction Queues
    // ==========================================================================
    
    // In-Flight Transactions
    tracked_transaction_t inflight_transactions[$];  // Transactions sent but not yet received
    
    // Completed Transactions
    axi_transaction completed_transactions[$];       // Successfully matched transactions
    
    // Protocol Violations
    protocol_violation_t protocol_violations[$];     // Recorded violations
    
    // Latency Log
    latency_log_entry_t latency_log[$];              // Latency records for analysis
    
    // ==========================================================================
    // Statistics
    // ==========================================================================
    
    // Transaction Counters
    int total_input_transactions = 0;                // Transactions sent by masters
    int total_output_transactions = 0;               // Transactions received at slaves
    int matched_transactions = 0;                    // Successfully matched transactions
    int unmatched_input_transactions = 0;            // Sent but never received
    int unexpected_output_transactions = 0;          // Received but never sent
    
    // Protocol Violation Counters
    int protocol_violation_count = 0;                // Total protocol violations
    int data_integrity_errors = 0;                   // Data mismatch errors
    int latency_violations = 0;                      // Latency threshold violations
    int fairness_violations = 0;                     // Starvation violations
    int deadlock_detections = 0;                     // Deadlock detections
    
    // Performance Metrics
    longint total_write_latency = 0;                 // Cumulative write latency
    longint total_read_latency = 0;                  // Cumulative read latency
    longint min_write_latency = 999999;               // Minimum write latency
    longint max_write_latency = 0;                   // Maximum write latency
    longint min_read_latency = 999999;                // Minimum read latency
    longint max_read_latency = 0;                    // Maximum read latency
    
    // Latency Histogram
    int latency_histogram[int];                      // Latency distribution histogram
    
    // QoS Performance Tracking
    longint qos_latency_sum[16];                     // Latency sum per QoS level
    int qos_transaction_count[16];                   // Transaction count per QoS level
    
    // Transaction Type Tracking
    int write_transaction_count = 0;                 // Write transaction count
    int read_transaction_count = 0;                  // Read transaction count
    int atomic_transaction_count = 0;                // Atomic transaction count
    
    // Deadlock Detection
    longint last_deadlock_check_time = 0;            // Last deadlock check timestamp
    int inflight_count_at_last_check = 0;            // In-flight count at last check

    // ==========================================================================
    // Constructor
    // ==========================================================================
    //
    function new(string name = "noc_scoreboard", uvm_component parent = null);
        super.new(name, parent);
        input_analysis_export = new("input_analysis_export", this);
        output_analysis_export = new("output_analysis_export", this);
        internal_export = new("internal_export", this);
    endfunction

    // ==========================================================================
    // Build Phase
    // ==========================================================================
    //
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Initialize QoS tracking arrays
        for (int i = 0; i < 16; i++) begin
            qos_latency_sum[i] = 0;
            qos_transaction_count[i] = 0;
        end
        
        `uvm_info("NOC_SB", "NoC scoreboard built successfully", UVM_MEDIUM)
    endfunction

    // ==========================================================================
    // Run Phase
    // ==========================================================================
    //
    // Starts deadlock monitoring task.
    //
    virtual task run_phase(uvm_phase phase);
        `uvm_info("NOC_SB", "NoC scoreboard starting run phase", UVM_MEDIUM)
        
        // Fork deadlock monitoring task
        fork
            monitor_deadlock();
        join_none
    endtask

    // ==========================================================================
    // Write Methods for Analysis Exports
    // ==========================================================================
    //
    // UVM requires write() methods for uvm_analysis_imp. Since we have multiple
    // exports, we use a naming convention where the method name matches the
    // export purpose. In production, consider using separate imp classes or
    // uvm_tlm_analysis_fifo for better separation.
    //
    // Note: For uvm_analysis_imp, the standard pattern requires a 'write' method.
    // This implementation uses wrapper methods that route to implementation methods.
    //
    
    // Write method for input_analysis_export
    function void write_input(axi_transaction tr);
        axi_transaction tr_copy;
        
        // Create copy of transaction for tracking
        tr_copy = axi_transaction::type_id::create("tr_copy");
        tr_copy.copy(tr);
        
        // Create tracked transaction entry
        tracked_transaction_t tracked;
        tracked.tr = tr_copy;
        tracked.inject_time = $time;
        tracked.last_progress_time = $time;
        tracked.progress_count = 0;
        tracked.matched = 0;
        tracked.source_id = tr.source_id;
        tracked.dest_id = tr.dest_id;
        
        // Check for duplicate transaction IDs within outstanding window
        check_duplicate_id(tr);
        
        // Store in inflight queue
        inflight_transactions.push_back(tracked);
        total_input_transactions++;
        
        // Update transaction type counters
        case (tr.trans_type)
            WRITE: write_transaction_count++;
            READ: read_transaction_count++;
            default: atomic_transaction_count++;
        endcase
        
        `uvm_info("NOC_SB", $sformatf(
            "Input transaction received: type=%s, id=%0d, addr=0x%0h, source=%0d, dest=%0d",
            tr.trans_type.name(),
            (tr.trans_type == WRITE) ? tr.awid : tr.arid,
            (tr.trans_type == WRITE) ? tr.awaddr : tr.araddr,
            tr.source_id, tr.dest_id), UVM_DEBUG)
    endfunction

    // ==========================================================================
    // Write Output (Slave-Side Transactions)
    // ==========================================================================
    //
    // Called when a transaction is received at a slave. Searches inflight
    // queue for matching transaction and performs validation.
    //
    // Arguments:
    //   tr - Transaction received at slave
    //
    function void write_output(axi_transaction tr);
        tracked_transaction_t matched_tracked;
        int match_index = -1;
        bit found_match = 0;
        
        // Search inflight transactions for match
        for (int i = 0; i < inflight_transactions.size(); i++) begin
            axi_transaction inflight_tr = inflight_transactions[i].tr;
            
            // Match by transaction ID (primary method)
            if (tr.trans_type == WRITE) begin
                if (inflight_tr.trans_type == WRITE &&
                    inflight_tr.awid == tr.bid) begin
                    match_index = i;
                    found_match = 1;
                    break;
                end
            end else if (tr.trans_type == READ) begin
                if (inflight_tr.trans_type == READ &&
                    inflight_tr.arid == tr.rid) begin
                    match_index = i;
                    found_match = 1;
                    break;
                end
            end
        end
        
        // Fallback: Match by address if ID match failed
        if (!found_match) begin
            for (int i = 0; i < inflight_transactions.size(); i++) begin
                axi_transaction inflight_tr = inflight_transactions[i].tr;
                
                if (tr.trans_type == WRITE && inflight_tr.trans_type == WRITE) begin
                    if (inflight_tr.awaddr == tr.awaddr &&
                        inflight_tr.awlen == tr.awlen) begin
                        match_index = i;
                        found_match = 1;
                        `uvm_warning("NOC_SB", $sformatf(
                            "Matched by address (ID mismatch): expected id=%0d, got id=%0d",
                            inflight_tr.awid, tr.bid))
                        break;
                    end
                end else if (tr.trans_type == READ && inflight_tr.trans_type == READ) begin
                    if (inflight_tr.araddr == tr.araddr &&
                        inflight_tr.arlen == tr.arlen) begin
                        match_index = i;
                        found_match = 1;
                        `uvm_warning("NOC_SB", $sformatf(
                            "Matched by address (ID mismatch): expected id=%0d, got id=%0d",
                            inflight_tr.arid, tr.rid))
                        break;
                    end
                end
            end
        end
        
        if (found_match) begin
            // Found matching transaction
            matched_tracked = inflight_transactions[match_index];
            axi_transaction expected = matched_tracked.tr;
            
            // Calculate latency
            longint latency = $time - matched_tracked.inject_time;
            
            // Protocol compliance checks
            check_axi4_compliance(tr);
            check_data_integrity(expected, tr);
            check_latency_compliance(tr, latency);
            
            // Update transaction with received data
            tr.start_time = matched_tracked.inject_time;
            tr.end_time = $time;
            
            // Store in completed transactions
            completed_transactions.push_back(tr);
            
            // Update latency log
            latency_log_entry_t latency_entry;
            latency_entry.trans_id = (tr.trans_type == WRITE) ? tr.bid : tr.rid;
            latency_entry.latency = latency;
            latency_entry.trans_type = tr.trans_type;
            latency_entry.qos_level = (tr.trans_type == WRITE) ? tr.awqos : tr.arqos;
            latency_entry.source_id = matched_tracked.source_id;
            latency_entry.dest_id = matched_tracked.dest_id;
            latency_log.push_back(latency_entry);
            
            // Update performance metrics
            update_performance_metrics(tr, latency);
            
            // Remove from inflight queue
            inflight_transactions.delete(match_index);
            matched_transactions++;
            total_output_transactions++;
            
            `uvm_info("NOC_SB", $sformatf(
                "Output transaction matched: type=%s, id=%0d, latency=%0d cycles",
                tr.trans_type.name(),
                (tr.trans_type == WRITE) ? tr.bid : tr.rid,
                latency), UVM_DEBUG)
        end else begin
            // Unexpected transaction - not found in inflight queue
            `uvm_error("NOC_SB", $sformatf(
                "Unexpected transaction at output: type=%s, id=%0d, addr=0x%0h",
                tr.trans_type.name(),
                (tr.trans_type == WRITE) ? tr.bid : tr.rid,
                (tr.trans_type == WRITE) ? tr.awaddr : tr.araddr))
            
            unexpected_output_transactions++;
            total_output_transactions++;
            
            // Log as spurious transaction
            log_protocol_violation("UNEXPECTED_TRANSACTION",
                $sformatf("Transaction received but never sent: id=%0d",
                    (tr.trans_type == WRITE) ? tr.bid : tr.rid),
                "Transaction corruption or monitor error");
        end
    endfunction

    // ==========================================================================
    // Write Internal (Internal NoC Events)
    // ==========================================================================
    //
    // Called for internal NoC events (routing, arbitration, etc.).
    // Currently a placeholder for future expansion.
    //
    function void write_internal(axi_transaction tr);
        // Placeholder for internal NoC event monitoring
        // Can be used to track routing decisions, arbitration, etc.
        `uvm_info("NOC_SB", "Internal event received", UVM_DEBUG)
    endfunction

    // ==========================================================================
    // Protocol Checking Methods
    // ==========================================================================

    // ==========================================================================
    // Check AXI4 Compliance
    // ==========================================================================
    //
    // Validates transaction complies with AXI4 protocol requirements.
    //
    function void check_axi4_compliance(axi_transaction tr);
        // Validate burst length (1-256 transfers)
        if (tr.trans_type == WRITE) begin
            if (tr.awlen > 255) begin
                log_protocol_violation("BURST_LENGTH_ERROR",
                    $sformatf("Invalid burst length: %0d (max 255)", tr.awlen),
                    "Protocol violation: burst length out of range");
            end
        end else if (tr.trans_type == READ) begin
            if (tr.arlen > 255) begin
                log_protocol_violation("BURST_LENGTH_ERROR",
                    $sformatf("Invalid burst length: %0d (max 255)", tr.arlen),
                    "Protocol violation: burst length out of range");
            end
        end
        
        // Validate response codes
        if (tr.trans_type == WRITE) begin
            if (!(tr.bresp inside {2'b00, 2'b01, 2'b10, 2'b11})) begin
                log_protocol_violation("INVALID_RESPONSE",
                    $sformatf("Invalid write response: %0b", tr.bresp),
                    "Protocol violation: invalid response code");
            end
        end else if (tr.trans_type == READ) begin
            if (!(tr.rresp inside {2'b00, 2'b01, 2'b10, 2'b11})) begin
                log_protocol_violation("INVALID_RESPONSE",
                    $sformatf("Invalid read response: %0b", tr.rresp),
                    "Protocol violation: invalid response code");
            end
        end
        
        // Verify ID consistency
        if (tr.trans_type == WRITE) begin
            if (tr.bid != tr.awid) begin
                log_protocol_violation("ID_MISMATCH",
                    $sformatf("Write ID mismatch: awid=%0d, bid=%0d", tr.awid, tr.bid),
                    "Protocol violation: response ID doesn't match request ID");
            end
        end else if (tr.trans_type == READ) begin
            if (tr.rid != tr.arid) begin
                log_protocol_violation("ID_MISMATCH",
                    $sformatf("Read ID mismatch: arid=%0d, rid=%0d", tr.arid, tr.rid),
                    "Protocol violation: response ID doesn't match request ID");
            end
        end
    endfunction

    // ==========================================================================
    // Check Data Integrity
    // ==========================================================================
    //
    // Validates data integrity for write transactions by comparing sent
    // data with received data (if write-through is enabled).
    //
    function void check_data_integrity(axi_transaction expected, axi_transaction actual);
        if (expected.trans_type == WRITE) begin
            // For write transactions, compare data bits enabled by wstrb
            bit [127:0] expected_data = expected.wdata;
            bit [127:0] actual_data = actual.wdata;
            bit [15:0] strb = expected.wstrb;
            
            // Compare only enabled bytes
            for (int byte_idx = 0; byte_idx < 16; byte_idx++) begin
                if (strb[byte_idx]) begin
                    bit [7:0] expected_byte = expected_data[byte_idx*8 +: 8];
                    bit [7:0] actual_byte = actual_data[byte_idx*8 +: 8];
                    
                    if (expected_byte != actual_byte) begin
                        log_protocol_violation("DATA_MISMATCH",
                            $sformatf("Data mismatch at byte %0d: expected=0x%02h, actual=0x%02h",
                                byte_idx, expected_byte, actual_byte),
                            "Data corruption during transmission");
                        data_integrity_errors++;
                    end
                end
            end
        end else if (expected.trans_type == READ) begin
            // For read transactions, data integrity is typically checked by
            // comparing with expected memory contents (not implemented here)
            // This would require a memory model or reference model
        end
    endfunction

    // ==========================================================================
    // Check Latency Compliance
    // ==========================================================================
    //
    // Validates transaction latency meets requirements.
    //
    function void check_latency_compliance(axi_transaction tr, longint latency);
        if (latency > MAX_LATENCY_CYCLES) begin
            log_protocol_violation("LATENCY_VIOLATION",
                $sformatf("Latency exceeds threshold: %0d cycles (max %0d)",
                    latency, MAX_LATENCY_CYCLES),
                "Performance degradation or congestion");
            latency_violations++;
        end
        
        // Update latency histogram
        int bin = latency / 10;  // 10-cycle bins
        latency_histogram[bin]++;
    endfunction

    // ==========================================================================
    // Check Fairness
    // ==========================================================================
    //
    // Checks for transaction starvation (fairness violation).
    //
    function void check_fairness(axi_transaction tr);
        // Check if any transaction to same destination is starved
        foreach (inflight_transactions[i]) begin
            if (inflight_transactions[i].dest_id == tr.dest_id &&
                !inflight_transactions[i].matched) begin
                longint wait_time = $time - inflight_transactions[i].inject_time;
                
                if (wait_time > MAX_WAIT_CYCLES) begin
                    log_protocol_violation("STARVATION",
                        $sformatf("Transaction starved: id=%0d, wait_time=%0d cycles",
                            (inflight_transactions[i].tr.trans_type == WRITE) ?
                            inflight_transactions[i].tr.awid :
                            inflight_transactions[i].tr.arid,
                            wait_time),
                        "Potential deadlock or starvation");
                    fairness_violations++;
                end
            end
        end
    endfunction

    // ==========================================================================
    // Check Duplicate ID
    // ==========================================================================
    //
    // Checks for duplicate transaction IDs within outstanding window.
    //
    function void check_duplicate_id(axi_transaction tr);
        int id = (tr.trans_type == WRITE) ? tr.awid : tr.arid;
        int duplicate_count = 0;
        
        foreach (inflight_transactions[i]) begin
            axi_transaction inflight_tr = inflight_transactions[i].tr;
            int inflight_id = (inflight_tr.trans_type == WRITE) ?
                              inflight_tr.awid : inflight_tr.arid;
            
            if (inflight_id == id && !inflight_transactions[i].matched) begin
                duplicate_count++;
            end
        end
        
        if (duplicate_count >= MAX_OUTSTANDING_TRANS) begin
            `uvm_warning("NOC_SB", $sformatf(
                "Maximum outstanding transactions reached for ID %0d", id))
        end
    endfunction

    // ==========================================================================
    // Deadlock Detection
    // ==========================================================================

    // ==========================================================================
    // Monitor Deadlock
    // ==========================================================================
    //
    // Periodically checks for deadlock conditions by monitoring transaction
    // progress. Deadlock is detected if no transactions complete over a
    // period of time despite inflight transactions existing.
    //
    task monitor_deadlock();
        forever begin
            #(DEADLOCK_CHECK_INTERVAL);
            
            check_no_deadlock();
        end
    endtask

    // ==========================================================================
    // Check No Deadlock
    // ==========================================================================
    //
    // Checks if system is deadlocked by comparing current inflight count
    // with previous check. If count hasn't decreased, potential deadlock.
    //
    function void check_no_deadlock();
        int current_inflight_count = inflight_transactions.size();
        longint current_time = $time;
        
        // Check if inflight transactions are making progress
        if (current_inflight_count > 0) begin
            if (last_deadlock_check_time > 0) begin
                longint time_since_check = current_time - last_deadlock_check_time;
                
                // If inflight count hasn't decreased and time has passed
                if (current_inflight_count >= inflight_count_at_last_check &&
                    time_since_check > DEADLOCK_CHECK_INTERVAL) begin
                    
                    // Check if any transaction made progress
                    bit progress_made = 0;
                    foreach (inflight_transactions[i]) begin
                        if (inflight_transactions[i].progress_count > 0) begin
                            progress_made = 1;
                            break;
                        end
                    end
                    
                    if (!progress_made) begin
                        `uvm_error("NOC_SB", $sformatf(
                            "Potential deadlock detected: %0d transactions stalled for %0d cycles",
                            current_inflight_count, time_since_check))
                        
                        // Log transaction details
                        foreach (inflight_transactions[i]) begin
                            axi_transaction tr = inflight_transactions[i].tr;
                            `uvm_info("NOC_SB", $sformatf(
                                "Stalled transaction: type=%s, id=%0d, addr=0x%0h, age=%0d cycles",
                                tr.trans_type.name(),
                                (tr.trans_type == WRITE) ? tr.awid : tr.arid,
                                (tr.trans_type == WRITE) ? tr.awaddr : tr.araddr,
                                current_time - inflight_transactions[i].inject_time),
                                UVM_MEDIUM)
                        end
                        
                        deadlock_detections++;
                        log_protocol_violation("DEADLOCK",
                            $sformatf("Deadlock detected: %0d transactions stalled",
                                current_inflight_count),
                            "Circular dependency or resource exhaustion");
                    end
                end
            end
        end
        
        // Update check state
        last_deadlock_check_time = current_time;
        inflight_count_at_last_check = current_inflight_count;
    endfunction

    // ==========================================================================
    // Performance Monitoring
    // ==========================================================================

    // ==========================================================================
    // Update Performance Metrics
    // ==========================================================================
    //
    // Updates performance tracking metrics including latency statistics
    // and QoS-based performance analysis.
    //
    function void update_performance_metrics(axi_transaction tr, longint latency);
        int qos_level = (tr.trans_type == WRITE) ? tr.awqos : tr.arqos;
        
        // Update transaction type latency
        if (tr.trans_type == WRITE) begin
            total_write_latency += latency;
            if (latency < min_write_latency) min_write_latency = latency;
            if (latency > max_write_latency) max_write_latency = latency;
        end else if (tr.trans_type == READ) begin
            total_read_latency += latency;
            if (latency < min_read_latency) min_read_latency = latency;
            if (latency > max_read_latency) max_read_latency = latency;
        end
        
        // Update QoS performance tracking
        if (qos_level >= 0 && qos_level < 16) begin
            qos_latency_sum[qos_level] += latency;
            qos_transaction_count[qos_level]++;
        end
    endfunction

    // ==========================================================================
    // Log Protocol Violation
    // ==========================================================================
    //
    // Records a protocol violation with details for debugging.
    //
    function void log_protocol_violation(string violation_type, string description,
                                         string likely_cause);
        protocol_violation_t violation;
        violation.violation_type = violation_type;
        violation.description = description;
        violation.timestamp = $time;
        violation.likely_cause = likely_cause;
        
        protocol_violations.push_back(violation);
        protocol_violation_count++;
        
        `uvm_warning("NOC_SB", $sformatf(
            "Protocol violation [%s]: %s (Likely cause: %s)",
            violation_type, description, likely_cause))
    endfunction

    // ==========================================================================
    // Query Methods
    // ==========================================================================

    // ==========================================================================
    // Get Latency Percentile
    // ==========================================================================
    //
    // Calculates and returns latency percentile (p50, p95, p99).
    //
    function longint get_latency_percentile(int percent);
        int sorted_latencies[$];
        
        // Collect all latencies
        foreach (latency_log[i]) begin
            sorted_latencies.push_back(latency_log[i].latency);
        end
        
        // Sort latencies
        sorted_latencies.sort();
        
        // Calculate percentile index
        int index = (percent * sorted_latencies.size()) / 100;
        if (index >= sorted_latencies.size()) begin
            index = sorted_latencies.size() - 1;
        end
        
        return sorted_latencies[index];
    endfunction

    // ==========================================================================
    // Get Total Transactions
    // ==========================================================================
    //
    function int get_total_transactions();
        return total_input_transactions;
    endfunction

    // ==========================================================================
    // Get Protocol Violations
    // ==========================================================================
    //
    function int get_protocol_violations();
        return protocol_violation_count;
    endfunction

    // ==========================================================================
    // Is Deadlocked
    // ==========================================================================
    //
    function bit is_deadlocked();
        return (deadlock_detections > 0);
    endfunction

    // ==========================================================================
    // Report Phase
    // ==========================================================================
    //
    // Generates comprehensive report of scoreboard statistics including
    // transaction matching, protocol violations, latency analysis, and
    // performance metrics.
    //
    virtual function void report_phase(uvm_phase phase);
        real avg_write_latency = 0.0;
        real avg_read_latency = 0.0;
        longint p50_latency = 0;
        longint p95_latency = 0;
        longint p99_latency = 0;
        
        // Calculate average latencies
        if (write_transaction_count > 0) begin
            avg_write_latency = real'(total_write_latency) / real'(write_transaction_count);
        end
        if (read_transaction_count > 0) begin
            avg_read_latency = real'(total_read_latency) / real'(read_transaction_count);
        end
        
        // Calculate percentiles
        if (latency_log.size() > 0) begin
            p50_latency = get_latency_percentile(50);
            p95_latency = get_latency_percentile(95);
            p99_latency = get_latency_percentile(99);
        end
        
        `uvm_info("NOC_SB", $sformatf(
            "\n" +
            "================================================================\n" +
            "                    NoC Scoreboard Report\n" +
            "================================================================\n" +
            "\n" +
            "Transaction Statistics:\n" +
            "  Total Input Transactions:      %0d\n" +
            "  Total Output Transactions:     %0d\n" +
            "  Matched Transactions:          %0d\n" +
            "  Unmatched Input Transactions:  %0d\n" +
            "  Unexpected Output Transactions: %0d\n" +
            "\n" +
            "Transaction Type Breakdown:\n" +
            "  Write Transactions:            %0d\n" +
            "  Read Transactions:             %0d\n" +
            "  Atomic Transactions:           %0d\n" +
            "\n" +
            "Latency Statistics:\n" +
            "  Write Latency:\n" +
            "    Average:                     %0.2f cycles\n" +
            "    Minimum:                     %0d cycles\n" +
            "    Maximum:                     %0d cycles\n" +
            "  Read Latency:\n" +
            "    Average:                     %0.2f cycles\n" +
            "    Minimum:                     %0d cycles\n" +
            "    Maximum:                     %0d cycles\n" +
            "  Overall Percentiles:\n" +
            "    P50:                         %0d cycles\n" +
            "    P95:                         %0d cycles\n" +
            "    P99:                         %0d cycles\n" +
            "\n" +
            "Protocol Violations:\n" +
            "  Total Violations:              %0d\n" +
            "  Data Integrity Errors:         %0d\n" +
            "  Latency Violations:            %0d\n" +
            "  Fairness Violations:           %0d\n" +
            "  Deadlock Detections:           %0d\n" +
            "\n" +
            "In-Flight Transactions:          %0d\n" +
            "  (Non-zero indicates potential issues)\n" +
            "\n" +
            "================================================================\n",
            total_input_transactions,
            total_output_transactions,
            matched_transactions,
            unmatched_input_transactions,
            unexpected_output_transactions,
            write_transaction_count,
            read_transaction_count,
            atomic_transaction_count,
            avg_write_latency,
            min_write_latency,
            max_write_latency,
            avg_read_latency,
            min_read_latency,
            max_read_latency,
            p50_latency,
            p95_latency,
            p99_latency,
            protocol_violation_count,
            data_integrity_errors,
            latency_violations,
            fairness_violations,
            deadlock_detections,
            inflight_transactions.size()), UVM_MEDIUM)
        
        // Print QoS performance breakdown
        print_qos_performance();
        
        // Print inflight transactions if any
        if (inflight_transactions.size() > 0) begin
            `uvm_warning("NOC_SB", $sformatf(
                "Warning: %0d transactions still in-flight at end of simulation",
                inflight_transactions.size()))
            foreach (inflight_transactions[i]) begin
                axi_transaction tr = inflight_transactions[i].tr;
                `uvm_info("NOC_SB", $sformatf(
                    "  In-flight: type=%s, id=%0d, addr=0x%0h, age=%0d cycles",
                    tr.trans_type.name(),
                    (tr.trans_type == WRITE) ? tr.awid : tr.arid,
                    (tr.trans_type == WRITE) ? tr.awaddr : tr.araddr,
                    $time - inflight_transactions[i].inject_time), UVM_MEDIUM)
            end
        end
        
        // Write results to file
        write_results_to_file();
    endfunction

    // ==========================================================================
    // Print QoS Performance
    // ==========================================================================
    //
    // Prints latency breakdown by QoS level.
    //
    function void print_qos_performance();
        `uvm_info("NOC_SB", "\nQoS Performance Breakdown:", UVM_MEDIUM)
        
        for (int qos = 0; qos < 16; qos++) begin
            if (qos_transaction_count[qos] > 0) begin
                real avg_qos_latency = real'(qos_latency_sum[qos]) /
                                       real'(qos_transaction_count[qos]);
                `uvm_info("NOC_SB", $sformatf(
                    "  QoS %2d: %0d transactions, avg latency: %0.2f cycles",
                    qos, qos_transaction_count[qos], avg_qos_latency), UVM_MEDIUM)
            end
        end
    endfunction

    // ==========================================================================
    // Write Results to File
    // ==========================================================================
    //
    // Writes scoreboard results to files for analysis and plotting.
    //
    task write_results_to_file();
        int file_handle;
        string filename;
        
        // Write latency log to CSV
        filename = "scoreboard_latency_log.csv";
        file_handle = $fopen(filename, "w");
        
        if (file_handle) begin
            $fwrite(file_handle, "Transaction_ID,Latency,Type,QoS,Source_ID,Dest_ID\n");
            
            foreach (latency_log[i]) begin
                $fwrite(file_handle, "%0d,%0d,%s,%0d,%0d,%0d\n",
                    latency_log[i].trans_id,
                    latency_log[i].latency,
                    latency_log[i].trans_type.name(),
                    latency_log[i].qos_level,
                    latency_log[i].source_id,
                    latency_log[i].dest_id);
            end
            
            $fclose(file_handle);
            `uvm_info("NOC_SB", $sformatf("Latency log written to %s", filename), UVM_MEDIUM)
        end
        
        // Write latency histogram to CSV
        filename = "scoreboard_latency_histogram.csv";
        file_handle = $fopen(filename, "w");
        
        if (file_handle) begin
            $fwrite(file_handle, "Latency_Bin,Count\n");
            
            foreach (latency_histogram[bin]) begin
                $fwrite(file_handle, "%0d,%0d\n", bin * 10, latency_histogram[bin]);
            end
            
            $fclose(file_handle);
            `uvm_info("NOC_SB", $sformatf("Latency histogram written to %s", filename), UVM_MEDIUM)
        end
        
        // Write protocol violations to report
        filename = "scoreboard_violations.txt";
        file_handle = $fopen(filename, "w");
        
        if (file_handle) begin
            $fwrite(file_handle, "Protocol Violations Report\n");
            $fwrite(file_handle, "==========================\n\n");
            
            foreach (protocol_violations[i]) begin
                $fwrite(file_handle, "Violation %0d:\n", i+1);
                $fwrite(file_handle, "  Type:         %s\n", protocol_violations[i].violation_type);
                $fwrite(file_handle, "  Description:  %s\n", protocol_violations[i].description);
                $fwrite(file_handle, "  Timestamp:    %0d\n", protocol_violations[i].timestamp);
                $fwrite(file_handle, "  Likely Cause: %s\n\n", protocol_violations[i].likely_cause);
            end
            
            $fclose(file_handle);
            `uvm_info("NOC_SB", $sformatf("Violations report written to %s", filename), UVM_MEDIUM)
        end
    endtask

endclass

`endif // NOC_SCOREBOARD_SV

