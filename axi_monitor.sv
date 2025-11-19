// ==============================================================================
// File: axi_monitor.sv
// Description: AXI4 Protocol Monitor for GPU Interconnect NoC Verification
// Author: Verification Team
// Date: January 2025
// Copyright (c) 2025 NVIDIA Corporation
//
// This file implements a comprehensive AXI4 monitor that observes all AXI4
// channels and reconstructs transactions for protocol verification and
// performance analysis. The monitor tracks in-flight transactions, detects
// protocol violations, measures latency, and publishes complete transactions
// via analysis port for scoreboard and coverage collection.
//
// AXI4 Monitoring Strategy:
//   Write Transaction: Monitor AW → W → B channels, match by transaction ID
//   Read Transaction:  Monitor AR → R channels, match by transaction ID
//   Protocol Checks:   Address alignment, burst compliance, ID matching
//   Performance:       Latency measurement, throughput calculation
//
// Reference: ARM AMBA 5 AXI4 Protocol Specification (ARM IHI 0022E)
// ==============================================================================

`ifndef AXI_MONITOR_SV
`define AXI_MONITOR_SV

import uvm_pkg::*;
`include "uvm_macros.svh"
`include "axi_transaction.sv"

// ==============================================================================
// Performance Tracking Structure
// ==============================================================================
//
// Tracks performance metrics for each transaction including latency,
// throughput, and timing information.
//
typedef struct {
    longint start_time;           // Transaction start time
    longint end_time;             // Transaction completion time
    longint latency;              // Calculated latency (end - start)
    int source_id;                // Source router ID
    int dest_id;                  // Destination router ID
    int qos_level;                // QoS priority level
    trans_type_e trans_type;      // Transaction type (READ/WRITE)
} performance_data_t;

// ==============================================================================
// In-Flight Transaction Tracking Structure
// ==============================================================================
//
// Tracks incomplete transactions waiting for responses.
// Used to match address phase with data/response phases.
//
typedef struct {
    axi_transaction tr;           // Transaction object
    int beat_count;               // Number of data beats received
    int expected_beats;           // Expected number of beats (len + 1)
    longint start_time;           // Transaction start timestamp
    bit address_complete;         // Address phase completed
    bit data_complete;            // Data phase completed
    bit response_complete;        // Response phase completed
} inflight_transaction_t;

// ==============================================================================
// AXI4 Monitor Class
// ==============================================================================
//
// The monitor observes all AXI4 channels and reconstructs complete transactions.
// It runs in parallel threads monitoring write and read channels independently,
// matching transactions by ID, and detecting protocol violations.
//
class axi_monitor extends uvm_monitor;

    // UVM Factory Registration
    `uvm_component_utils(axi_monitor)

    // ==========================================================================
    // Analysis Port
    // ==========================================================================
    //
    // Publishes complete transactions to subscribers (scoreboard, coverage, etc.)
    //
    uvm_analysis_port #(axi_transaction) analysis_port;

    // ==========================================================================
    // Properties
    // ==========================================================================
    
    // Virtual Interface
    virtual axi_if vif;                    // Virtual interface to DUT
                                          // Provides access to AXI4 signals
    
    // Configuration
    noc_config cfg;                       // NoC configuration object
    
    // Transaction Counters
    int trans_count = 0;                  // Total transactions monitored
    int write_count = 0;                  // Write transactions monitored
    int read_count = 0;                   // Read transactions monitored
    
    // In-Flight Transaction Tracking
    inflight_transaction_t inflight_write_transactions[int];  // Keyed by awid
    inflight_transaction_t inflight_read_transactions[int];   // Keyed by arid
    
    // Performance Tracking
    performance_data_t performance_data[$];  // Performance metrics for all transactions
    longint write_latency_sum = 0;          // Cumulative write latency
    longint read_latency_sum = 0;           // Cumulative read latency
    longint min_write_latency = 999999;      // Minimum write latency
    longint max_write_latency = 0;           // Maximum write latency
    longint min_read_latency = 999999;       // Minimum read latency
    longint max_read_latency = 0;            // Maximum read latency
    
    // Protocol Violation Tracking
    int protocol_violations = 0;            // Total protocol violations
    int address_alignment_errors = 0;       // Address misalignment errors
    int burst_compliance_errors = 0;        // Burst parameter errors
    int id_mismatch_errors = 0;            // ID mismatch errors
    int handshake_errors = 0;               // Handshake protocol errors
    int timeout_errors = 0;                 // Transaction timeout errors
    
    // Latency Histogram
    int latency_histogram[longint];         // Latency distribution histogram
    int latency_bins[10];                  // Predefined latency bins

    // ==========================================================================
    // Constructor
    // ==========================================================================
    //
    function new(string name = "axi_monitor", uvm_component parent = null);
        super.new(name, parent);
        analysis_port = new("analysis_port", this);
    endfunction

    // ==========================================================================
    // Build Phase
    // ==========================================================================
    //
    // Retrieves virtual interface and configuration from UVM ConfigDB.
    //
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Get virtual interface from ConfigDB
        if (!uvm_config_db#(virtual axi_if)::get(this, "", "vif", vif)) begin
            `uvm_fatal("AXI_MON", "Virtual interface not found in ConfigDB")
        end
        
        // Get configuration object
        if (!uvm_config_db#(noc_config)::get(this, "", "cfg", cfg)) begin
            `uvm_warning("AXI_MON", "Configuration object not found, using defaults")
        end
        
        `uvm_info("AXI_MON", "AXI4 monitor built successfully", UVM_MEDIUM)
    endfunction

    // ==========================================================================
    // Run Phase
    // ==========================================================================
    //
    // Main monitoring loop. Forks parallel threads to monitor write and read
    // channels independently. Each thread observes its respective channels and
    // reconstructs complete transactions.
    //
    virtual task run_phase(uvm_phase phase);
        `uvm_info("AXI_MON", "AXI4 monitor starting run phase", UVM_MEDIUM)
        
        // Wait for reset deassertion
        wait(vif.aresetn == 1'b1);
        @(posedge vif.aclk);
        
        // Fork parallel monitoring threads
        fork
            // Monitor write channels (AW, W, B)
            monitor_write_channels();
            
            // Monitor read channels (AR, R)
            monitor_read_channels();
            
            // Monitor for timeouts
            monitor_timeouts();
        join
    endtask

    // ==========================================================================
    // Monitor Write Channels
    // ==========================================================================
    //
    // Monitors all write-related channels (AW, W, B) and reconstructs complete
    // write transactions. Handles out-of-order completion by matching
    // transactions using transaction IDs.
    //
    // Protocol Flow:
    //   1. AW channel: Capture address and control
    //   2. W channel:  Capture data beats (may be interleaved with other writes)
    //   3. B channel:  Capture response, match to AW by ID
    //
    task monitor_write_channels();
        `uvm_info("AXI_MON", "Write channel monitoring started", UVM_MEDIUM)
        
        fork
            // Monitor write address channel
            monitor_write_address_channel();
            
            // Monitor write data channel
            monitor_write_data_channel();
            
            // Monitor write response channel
            monitor_write_response_channel();
        join
    endtask

    // ==========================================================================
    // Monitor Write Address Channel
    // ==========================================================================
    //
    // Observes AW channel handshakes and captures address/control information.
    // Creates initial transaction object and stores in in-flight queue.
    //
    task monitor_write_address_channel();
        forever begin
            // Wait for address handshake
            @(posedge vif.aclk);
            if (vif.awvalid && vif.awready) begin
                // Capture address channel signals
                axi_transaction tr;
                tr = axi_transaction::type_id::create("tr");
                tr.trans_type = WRITE;
                tr.awaddr   = vif.awaddr;
                tr.awlen    = vif.awlen;
                tr.awsize   = vif.awsize;
                tr.awburst  = vif.awburst;
                tr.awid     = vif.awid;
                tr.awqos    = vif.awqos;
                tr.awregion = vif.awregion;
                tr.awlock   = vif.awlock;
                tr.awcache  = vif.awcache;
                tr.awprot   = vif.awprot;
                
                // Protocol compliance checks
                if (!check_address_alignment(tr.awaddr, tr.awsize)) begin
                    `uvm_error("AXI_MON", $sformatf(
                        "Write address misaligned: addr=0x%0h, size=%0d",
                        tr.awaddr, tr.awsize))
                    address_alignment_errors++;
                    protocol_violations++;
                end
                
                if (!check_burst_compliance(tr.awlen, tr.awsize, tr.awburst)) begin
                    `uvm_error("AXI_MON", $sformatf(
                        "Write burst non-compliant: len=%0d, size=%0d, burst=%0d",
                        tr.awlen, tr.awsize, tr.awburst))
                    burst_compliance_errors++;
                    protocol_violations++;
                end
                
                // Create in-flight transaction entry
                inflight_transaction_t inflight;
                inflight.tr = tr;
                inflight.beat_count = 0;
                inflight.expected_beats = tr.awlen + 1;
                inflight.start_time = $time;
                inflight.address_complete = 1;
                inflight.data_complete = 0;
                inflight.response_complete = 0;
                
                // Store in in-flight queue (keyed by awid)
                inflight_write_transactions[tr.awid] = inflight;
                
                `uvm_info("AXI_MON", $sformatf(
                    "AW channel: addr=0x%0h, len=%0d, id=%0d, qos=%0d",
                    tr.awaddr, tr.awlen, tr.awid, tr.awqos), UVM_DEBUG)
            end
        end
    endtask

    // ==========================================================================
    // Monitor Write Data Channel
    // ==========================================================================
    //
    // Observes W channel handshakes and captures data beats. Matches beats to
    // in-flight transactions using implicit ordering (first W after AW).
    //
    task monitor_write_data_channel();
        forever begin
            // Wait for data handshake
            @(posedge vif.aclk);
            if (vif.wvalid && vif.wready) begin
                // Find matching in-flight transaction
                // In AXI4, W channel follows AW channel (implicit ordering)
                // We match by finding the oldest incomplete write transaction
                int matched_id = -1;
                longint oldest_time = $time;
                
                foreach (inflight_write_transactions[id]) begin
                    if (!inflight_write_transactions[id].data_complete &&
                        inflight_write_transactions[id].start_time < oldest_time) begin
                        matched_id = id;
                        oldest_time = inflight_write_transactions[id].start_time;
                    end
                end
                
                if (matched_id >= 0) begin
                    inflight_transaction_t inflight = inflight_write_transactions[matched_id];
                    axi_transaction tr = inflight.tr;
                    
                    // Capture data beat
                    tr.wdata = vif.wdata;
                    tr.wstrb = vif.wstrb;
                    tr.wlast = vif.wlast;
                    tr.wuser = vif.wuser;
                    
                    // Update beat count
                    inflight.beat_count++;
                    
                    // Protocol check: wlast must be asserted on final beat
                    if (inflight.beat_count == inflight.expected_beats) begin
                        if (!vif.wlast) begin
                            `uvm_error("AXI_MON", $sformatf(
                                "wlast not asserted on final beat: id=%0d, beat=%0d/%0d",
                                matched_id, inflight.beat_count, inflight.expected_beats))
                            protocol_violations++;
                        end
                        inflight.data_complete = 1;
                    end else begin
                        if (vif.wlast) begin
                            `uvm_error("AXI_MON", $sformatf(
                                "wlast asserted prematurely: id=%0d, beat=%0d/%0d",
                                matched_id, inflight.beat_count, inflight.expected_beats))
                            protocol_violations++;
                        end
                    end
                    
                    // Update in-flight transaction
                    inflight_write_transactions[matched_id] = inflight;
                    
                    `uvm_info("AXI_MON", $sformatf(
                        "W channel beat: id=%0d, beat=%0d/%0d, data=0x%0h, last=%0b",
                        matched_id, inflight.beat_count, inflight.expected_beats,
                        vif.wdata, vif.wlast), UVM_DEBUG)
                end else begin
                    `uvm_warning("AXI_MON", 
                        "W channel data received but no matching AW transaction found")
                end
            end
        end
    endtask

    // ==========================================================================
    // Monitor Write Response Channel
    // ==========================================================================
    //
    // Observes B channel handshakes and captures responses. Matches responses
    // to in-flight transactions using transaction ID (bid matches awid).
    //
    task monitor_write_response_channel();
        forever begin
            // Wait for response handshake
            @(posedge vif.aclk);
            if (vif.bvalid && vif.bready) begin
                int bid = vif.bid;
                
                // Find matching in-flight transaction by ID
                if (inflight_write_transactions.exists(bid)) begin
                    inflight_transaction_t inflight = inflight_write_transactions[bid];
                    axi_transaction tr = inflight.tr;
                    
                    // Capture response
                    tr.bresp = vif.bresp;
                    tr.bid = vif.bid;
                    tr.buser = vif.buser;
                    
                    // Protocol check: ID matching
                    if (tr.bid != tr.awid) begin
                        `uvm_error("AXI_MON", $sformatf(
                            "Write response ID mismatch: awid=%0d, bid=%0d",
                            tr.awid, tr.bid))
                        id_mismatch_errors++;
                        protocol_violations++;
                    end
                    
                    // Complete transaction
                    tr.end_time = $time;
                    tr.start_time = inflight.start_time;
                    
                    // Calculate latency
                    longint latency = tr.end_time - tr.start_time;
                    tr.end_time = tr.start_time + latency;  // Store in transaction
                    
                    // Update performance metrics
                    update_write_performance(tr, latency);
                    
                    // Collect complete transaction
                    collect_write_transaction(tr);
                    
                    // Remove from in-flight queue
                    inflight_write_transactions.delete(bid);
                    
                    `uvm_info("AXI_MON", $sformatf(
                        "B channel response: id=%0d, resp=%0d, latency=%0d cycles",
                        bid, vif.bresp, latency), UVM_DEBUG)
                end else begin
                    `uvm_warning("AXI_MON", $sformatf(
                        "B channel response received but no matching AW transaction: bid=%0d",
                        bid))
                end
            end
        end
    endtask

    // ==========================================================================
    // Monitor Read Channels
    // ==========================================================================
    //
    // Monitors all read-related channels (AR, R) and reconstructs complete
    // read transactions. Handles out-of-order completion by matching
    // transactions using transaction IDs.
    //
    // Protocol Flow:
    //   1. AR channel: Capture address and control
    //   2. R channel:  Capture data beats, match by rid
    //
    task monitor_read_channels();
        `uvm_info("AXI_MON", "Read channel monitoring started", UVM_MEDIUM)
        
        fork
            // Monitor read address channel
            monitor_read_address_channel();
            
            // Monitor read data channel
            monitor_read_data_channel();
        join
    endtask

    // ==========================================================================
    // Monitor Read Address Channel
    // ==========================================================================
    //
    // Observes AR channel handshakes and captures address/control information.
    // Creates initial transaction object and stores in in-flight queue.
    //
    task monitor_read_address_channel();
        forever begin
            // Wait for address handshake
            @(posedge vif.aclk);
            if (vif.arvalid && vif.arready) begin
                // Capture address channel signals
                axi_transaction tr;
                tr = axi_transaction::type_id::create("tr");
                tr.trans_type = READ;
                tr.araddr   = vif.araddr;
                tr.arlen    = vif.arlen;
                tr.arsize   = vif.arsize;
                tr.arburst  = vif.arburst;
                tr.arid     = vif.arid;
                tr.arqos    = vif.arqos;
                tr.arregion = vif.arregion;
                tr.arlock   = vif.arlock;
                tr.arcache  = vif.arcache;
                tr.arprot   = vif.arprot;
                
                // Protocol compliance checks
                if (!check_address_alignment(tr.araddr, tr.arsize)) begin
                    `uvm_error("AXI_MON", $sformatf(
                        "Read address misaligned: addr=0x%0h, size=%0d",
                        tr.araddr, tr.arsize))
                    address_alignment_errors++;
                    protocol_violations++;
                end
                
                if (!check_burst_compliance(tr.arlen, tr.arsize, tr.arburst)) begin
                    `uvm_error("AXI_MON", $sformatf(
                        "Read burst non-compliant: len=%0d, size=%0d, burst=%0d",
                        tr.arlen, tr.arsize, tr.arburst))
                    burst_compliance_errors++;
                    protocol_violations++;
                end
                
                // Create in-flight transaction entry
                inflight_transaction_t inflight;
                inflight.tr = tr;
                inflight.beat_count = 0;
                inflight.expected_beats = tr.arlen + 1;
                inflight.start_time = $time;
                inflight.address_complete = 1;
                inflight.data_complete = 0;
                inflight.response_complete = 0;
                
                // Store in in-flight queue (keyed by arid)
                inflight_read_transactions[tr.arid] = inflight;
                
                `uvm_info("AXI_MON", $sformatf(
                    "AR channel: addr=0x%0h, len=%0d, id=%0d, qos=%0d",
                    tr.araddr, tr.arlen, tr.arid, tr.arqos), UVM_DEBUG)
            end
        end
    endtask

    // ==========================================================================
    // Monitor Read Data Channel
    // ==========================================================================
    //
    // Observes R channel handshakes and captures data beats. Matches beats to
    // in-flight transactions using transaction ID (rid matches arid).
    //
    task monitor_read_data_channel();
        forever begin
            // Wait for data handshake
            @(posedge vif.aclk);
            if (vif.rvalid && vif.rready) begin
                int rid = vif.rid;
                
                // Find matching in-flight transaction by ID
                if (inflight_read_transactions.exists(rid)) begin
                    inflight_transaction_t inflight = inflight_read_transactions[rid];
                    axi_transaction tr = inflight.tr;
                    
                    // Capture data beat
                    tr.rdata = vif.rdata;
                    tr.rresp = vif.rresp;
                    tr.rid = vif.rid;
                    tr.rlast = vif.rlast;
                    tr.ruser = vif.ruser;
                    
                    // Protocol check: ID matching
                    if (tr.rid != tr.arid) begin
                        `uvm_error("AXI_MON", $sformatf(
                            "Read data ID mismatch: arid=%0d, rid=%0d",
                            tr.arid, tr.rid))
                        id_mismatch_errors++;
                        protocol_violations++;
                    end
                    
                    // Update beat count
                    inflight.beat_count++;
                    
                    // Protocol check: rlast must be asserted on final beat
                    if (inflight.beat_count == inflight.expected_beats) begin
                        if (!vif.rlast) begin
                            `uvm_error("AXI_MON", $sformatf(
                                "rlast not asserted on final beat: id=%0d, beat=%0d/%0d",
                                rid, inflight.beat_count, inflight.expected_beats))
                            protocol_violations++;
                        end
                        inflight.data_complete = 1;
                        
                        // Complete transaction
                        tr.end_time = $time;
                        tr.start_time = inflight.start_time;
                        
                        // Calculate latency
                        longint latency = tr.end_time - tr.start_time;
                        
                        // Update performance metrics
                        update_read_performance(tr, latency);
                        
                        // Collect complete transaction
                        collect_read_transaction(tr);
                        
                        // Remove from in-flight queue
                        inflight_read_transactions.delete(rid);
                        
                        `uvm_info("AXI_MON", $sformatf(
                            "R channel complete: id=%0d, beats=%0d, latency=%0d cycles",
                            rid, inflight.beat_count, latency), UVM_DEBUG)
                    end else begin
                        if (vif.rlast) begin
                            `uvm_error("AXI_MON", $sformatf(
                                "rlast asserted prematurely: id=%0d, beat=%0d/%0d",
                                rid, inflight.beat_count, inflight.expected_beats))
                            protocol_violations++;
                        end
                        
                        // Update in-flight transaction
                        inflight_read_transactions[rid] = inflight;
                    end
                    
                    `uvm_info("AXI_MON", $sformatf(
                        "R channel beat: id=%0d, beat=%0d/%0d, data=0x%0h, last=%0b",
                        rid, inflight.beat_count, inflight.expected_beats,
                        vif.rdata, vif.rlast), UVM_DEBUG)
                end else begin
                    `uvm_warning("AXI_MON", $sformatf(
                        "R channel data received but no matching AR transaction: rid=%0d",
                        rid))
                end
            end
        end
    endtask

    // ==========================================================================
    // Monitor Timeouts
    // ==========================================================================
    //
    // Monitors in-flight transactions for timeout conditions. Warns if
    // transactions exceed maximum expected latency.
    //
    task monitor_timeouts();
        int timeout_limit = 10000;  // Maximum cycles before timeout
        
        forever begin
            @(posedge vif.aclk);
            
            // Check write transactions
            foreach (inflight_write_transactions[id]) begin
                longint age = $time - inflight_write_transactions[id].start_time;
                if (age > timeout_limit) begin
                    `uvm_warning("AXI_MON", $sformatf(
                        "Write transaction timeout: id=%0d, age=%0d cycles",
                        id, age))
                    timeout_errors++;
                end
            end
            
            // Check read transactions
            foreach (inflight_read_transactions[id]) begin
                longint age = $time - inflight_read_transactions[id].start_time;
                if (age > timeout_limit) begin
                    `uvm_warning("AXI_MON", $sformatf(
                        "Read transaction timeout: id=%0d, age=%0d cycles",
                        id, age))
                    timeout_errors++;
                end
            end
        end
    endtask

    // ==========================================================================
    // Protocol Compliance Methods
    // ==========================================================================

    // ==========================================================================
    // Check Address Alignment
    // ==========================================================================
    //
    function bit check_address_alignment(bit [31:0] addr, bit [2:0] size);
        int alignment = 1 << size;
        
        if (addr % alignment != 0) begin
            return 0;
        end
        
        return 1;
    endfunction

    // ==========================================================================
    // Check Burst Compliance
    // ==========================================================================
    //
    function bit check_burst_compliance(bit [7:0] len, bit [2:0] size, bit [1:0] burst);
        // Check burst length
        if (len > 255) return 0;
        
        // Check burst size
        if (size > 7) return 0;
        
        // Check burst type
        if (burst > 2) return 0;
        
        return 1;
    endfunction

    // ==========================================================================
    // Check ID Matching
    // ==========================================================================
    //
    function bit check_id_matching(int request_id, int response_id);
        if (request_id != response_id) begin
            return 0;
        end
        return 1;
    endfunction

    // ==========================================================================
    // Check Handshake Protocol
    // ==========================================================================
    //
    function void check_handshake_protocol(bit valid, bit ready, string channel);
        // Protocol rule: Transfer occurs when both valid and ready are high
        // Valid can be asserted independently, ready can be asserted independently
        // No specific timing requirement beyond both being high for transfer
        
        // Check for glitches (both signals changing simultaneously)
        static bit last_valid[$];
        static bit last_ready[$];
        
        // This is a simplified check - real implementation would use clocking blocks
        // to detect glitches more accurately
    endfunction

    // ==========================================================================
    // Transaction Collection Methods
    // ==========================================================================

    // ==========================================================================
    // Collect Write Transaction
    // ==========================================================================
    //
    // Assembles complete write transaction and publishes via analysis port.
    //
    function void collect_write_transaction(axi_transaction tr);
        write_count++;
        trans_count++;
        
        // Update transaction tracking
        tr.source_id = cfg != null ? cfg.get_source_id("monitor") : -1;
        
        // Broadcast transaction
        broadcast_transaction(tr);
    endfunction

    // ==========================================================================
    // Collect Read Transaction
    // ==========================================================================
    //
    // Assembles complete read transaction and publishes via analysis port.
    //
    function void collect_read_transaction(axi_transaction tr);
        read_count++;
        trans_count++;
        
        // Update transaction tracking
        tr.source_id = cfg != null ? cfg.get_source_id("monitor") : -1;
        
        // Broadcast transaction
        broadcast_transaction(tr);
    endfunction

    // ==========================================================================
    // Broadcast Transaction
    // ==========================================================================
    //
    // Publishes transaction to analysis port for subscribers (scoreboard,
    // coverage, performance monitors, etc.).
    //
    function void broadcast_transaction(axi_transaction tr);
        `uvm_info("AXI_MON", $sformatf(
            "Broadcasting transaction: type=%s, addr=0x%0h, id=%0d, latency=%0d",
            tr.trans_type.name(),
            (tr.trans_type == WRITE) ? tr.awaddr : tr.araddr,
            (tr.trans_type == WRITE) ? tr.awid : tr.arid,
            tr.get_latency()), UVM_DEBUG)
        
        analysis_port.write(tr);
    endfunction

    // ==========================================================================
    // Performance Tracking Methods
    // ==========================================================================

    // ==========================================================================
    // Update Write Performance
    // ==========================================================================
    //
    function void update_write_performance(axi_transaction tr, longint latency);
        write_latency_sum += latency;
        
        if (latency < min_write_latency) begin
            min_write_latency = latency;
        end
        if (latency > max_write_latency) begin
            max_write_latency = latency;
        end
        
        // Update histogram
        latency_histogram[latency]++;
        
        // Store performance data
        performance_data_t perf;
        perf.start_time = tr.start_time;
        perf.end_time = tr.end_time;
        perf.latency = latency;
        perf.source_id = tr.source_id;
        perf.dest_id = tr.dest_id;
        perf.qos_level = tr.qos_level;
        perf.trans_type = WRITE;
        performance_data.push_back(perf);
    endfunction

    // ==========================================================================
    // Update Read Performance
    // ==========================================================================
    //
    function void update_read_performance(axi_transaction tr, longint latency);
        read_latency_sum += latency;
        
        if (latency < min_read_latency) begin
            min_read_latency = latency;
        end
        if (latency > max_read_latency) begin
            max_read_latency = latency;
        end
        
        // Update histogram
        latency_histogram[latency]++;
        
        // Store performance data
        performance_data_t perf;
        perf.start_time = tr.start_time;
        perf.end_time = tr.end_time;
        perf.latency = latency;
        perf.source_id = tr.source_id;
        perf.dest_id = tr.dest_id;
        perf.qos_level = tr.qos_level;
        perf.trans_type = READ;
        performance_data.push_back(perf);
    endfunction

    // ==========================================================================
    // Report Phase
    // ==========================================================================
    //
    // Generates comprehensive report of monitoring statistics including
    // transaction counts, latencies, protocol violations, and performance metrics.
    //
    virtual function void report_phase(uvm_phase phase);
        real avg_write_latency = 0.0;
        real avg_read_latency = 0.0;
        
        // Calculate average latencies
        if (write_count > 0) begin
            avg_write_latency = real'(write_latency_sum) / real'(write_count);
        end
        if (read_count > 0) begin
            avg_read_latency = real'(read_latency_sum) / real'(read_count);
        end
        
        `uvm_info("AXI_MON", $sformatf(
            "\n=== AXI4 Monitor Statistics ===\n" +
            "Total Transactions Monitored: %0d\n" +
            "  Write Transactions:        %0d\n" +
            "  Read Transactions:         %0d\n" +
            "Write Latency:\n" +
            "  Average:                   %0.2f cycles\n" +
            "  Minimum:                   %0d cycles\n" +
            "  Maximum:                   %0d cycles\n" +
            "Read Latency:\n" +
            "  Average:                   %0.2f cycles\n" +
            "  Minimum:                   %0d cycles\n" +
            "  Maximum:                   %0d cycles\n" +
            "Protocol Violations:          %0d\n" +
            "  Address Alignment Errors:  %0d\n" +
            "  Burst Compliance Errors:   %0d\n" +
            "  ID Mismatch Errors:        %0d\n" +
            "  Handshake Errors:          %0d\n" +
            "  Timeout Errors:            %0d\n" +
            "In-Flight Transactions:\n" +
            "  Write:                     %0d\n" +
            "  Read:                      %0d\n" +
            "================================",
            trans_count,
            write_count,
            read_count,
            avg_write_latency,
            min_write_latency,
            max_write_latency,
            avg_read_latency,
            min_read_latency,
            max_read_latency,
            protocol_violations,
            address_alignment_errors,
            burst_compliance_errors,
            id_mismatch_errors,
            handshake_errors,
            timeout_errors,
            inflight_write_transactions.size(),
            inflight_read_transactions.size()), UVM_MEDIUM)
        
        // Generate performance CSV file
        generate_performance_report();
    endfunction

    // ==========================================================================
    // Generate Performance Report
    // ==========================================================================
    //
    // Generates CSV file with performance data for analysis.
    //
    function void generate_performance_report();
        int file_handle;
        string filename = "axi_performance_report.csv";
        
        file_handle = $fopen(filename, "w");
        
        if (file_handle) begin
            // Write CSV header
            $fwrite(file_handle, "Transaction_Type,Start_Time,End_Time,Latency,Source_ID,Dest_ID,QoS_Level\n");
            
            // Write performance data
            foreach (performance_data[i]) begin
                $fwrite(file_handle, "%s,%0d,%0d,%0d,%0d,%0d,%0d\n",
                    performance_data[i].trans_type.name(),
                    performance_data[i].start_time,
                    performance_data[i].end_time,
                    performance_data[i].latency,
                    performance_data[i].source_id,
                    performance_data[i].dest_id,
                    performance_data[i].qos_level);
            end
            
            $fclose(file_handle);
            `uvm_info("AXI_MON", $sformatf(
                "Performance report generated: %s", filename), UVM_MEDIUM)
        end else begin
            `uvm_warning("AXI_MON", "Failed to create performance report file")
        end
    endfunction

endclass

`endif // AXI_MONITOR_SV

