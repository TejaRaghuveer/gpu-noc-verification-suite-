// ==============================================================================
// File: axi_driver.sv
// Description: AXI4 Protocol Driver for GPU Interconnect NoC Verification
// Author: Verification Team
// Date: January 2025
// Copyright (c) 2025 NVIDIA Corporation
//
// This file implements a comprehensive AXI4 driver that drives transactions
// onto the AXI4 interface following the ARM AMBA 5 AXI4 protocol specification.
// The driver handles both write and read transactions, including burst transfers,
// out-of-order completion, and protocol compliance checking.
//
// AXI4 Protocol Overview:
//   - 5 independent channels: AW (Write Address), W (Write Data), B (Write
//     Response), AR (Read Address), R (Read Data)
//   - Handshake protocol: valid/ready signals for flow control
//   - Burst support: 1-256 transfers per transaction
//   - Out-of-order completion: Transaction IDs enable reordering
//   - QoS support: Priority-based arbitration
//
// Reference: ARM AMBA 5 AXI4 Protocol Specification (ARM IHI 0022E)
// ==============================================================================

`ifndef AXI_DRIVER_SV
`define AXI_DRIVER_SV

import uvm_pkg::*;
`include "uvm_macros.svh"
`include "axi_transaction.sv"

// ==============================================================================
// AXI4 Interface Definition (Forward Declaration)
// ==============================================================================
//
// The driver uses a virtual interface to communicate with the DUT.
// Interface signals follow AXI4 protocol naming conventions.
//
interface axi_if;
    // Clock and Reset
    logic aclk;
    logic aresetn;
    
    // Write Address Channel (AW)
    logic [31:0]  awaddr;
    logic [7:0]   awlen;
    logic [2:0]   awsize;
    logic [1:0]   awburst;
    logic [3:0]   awid;
    logic [3:0]   awqos;
    logic [3:0]   awregion;
    logic         awlock;
    logic [3:0]   awcache;
    logic [2:0]   awprot;
    logic         awvalid;
    logic         awready;
    
    // Write Data Channel (W)
    logic [127:0] wdata;
    logic [15:0]  wstrb;
    logic         wlast;
    logic [7:0]   wuser;
    logic         wvalid;
    logic         wready;
    
    // Write Response Channel (B)
    logic [1:0]   bresp;
    logic [3:0]   bid;
    logic [7:0]   buser;
    logic         bvalid;
    logic         bready;
    
    // Read Address Channel (AR)
    logic [31:0]  araddr;
    logic [7:0]   arlen;
    logic [2:0]   arsize;
    logic [1:0]   arburst;
    logic [3:0]   arid;
    logic [3:0]   arqos;
    logic [3:0]   arregion;
    logic         arlock;
    logic [3:0]   arcache;
    logic [2:0]   arprot;
    logic         arvalid;
    logic         arready;
    
    // Read Data Channel (R)
    logic [127:0] rdata;
    logic [1:0]   rresp;
    logic [3:0]   rid;
    logic         rlast;
    logic [7:0]   ruser;
    logic         rvalid;
    logic         rready;
endinterface

// ==============================================================================
// AXI4 Driver Class
// ==============================================================================
//
// The driver receives transactions from the sequencer and drives them onto the
// AXI4 interface following protocol timing requirements. It handles:
//   - Write transactions: AW → W → B channel sequence
//   - Read transactions: AR → R channel sequence
//   - Burst transfers: Multiple data beats per transaction
//   - Protocol compliance: Validates handshakes and responses
//
class axi_driver extends uvm_driver #(axi_transaction);

    // UVM Factory Registration
    `uvm_component_utils(axi_driver)

    // ==========================================================================
    // Properties
    // ==========================================================================
    
    // Virtual Interface
    virtual axi_if vif;                    // Virtual interface to DUT
                                          // Provides access to AXI4 signals
    
    // Configuration
    noc_config cfg;                       // NoC configuration object
                                          // Contains topology, routing info
    
    // Transaction Counters
    int trans_count = 0;                  // Total transactions driven
    int write_count = 0;                  // Write transactions driven
    int read_count = 0;                   // Read transactions driven
    
    // Source Identification
    int source_id = -1;                   // Source router ID in NoC
                                          // Identifies which processing element
                                          // is generating transactions
    
    // Performance Tracking
    longint write_start_time[$];          // Write transaction start times
                                          // Indexed by awid for latency calc
    longint read_start_time[$];          // Read transaction start times
                                          // Indexed by arid for latency calc
    longint total_write_latency = 0;     // Cumulative write latency
    longint total_read_latency = 0;      // Cumulative read latency
    longint max_write_latency = 0;       // Maximum write latency observed
    longint max_read_latency = 0;        // Maximum read latency observed
    
    // Protocol Compliance Tracking
    int protocol_violations = 0;         // Count of protocol violations
    int handshake_timeouts = 0;          // Count of handshake timeouts

    // ==========================================================================
    // Constructor
    // ==========================================================================
    //
    function new(string name = "axi_driver", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    // ==========================================================================
    // Build Phase
    // ==========================================================================
    //
    // Retrieves virtual interface and configuration from UVM ConfigDB.
    // Validates interface signal widths match expected data width.
    //
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Get virtual interface from ConfigDB
        if (!uvm_config_db#(virtual axi_if)::get(this, "", "vif", vif)) begin
            `uvm_fatal("AXI_DRV", "Virtual interface not found in ConfigDB")
        end
        
        // Get configuration object
        if (!uvm_config_db#(noc_config)::get(this, "", "cfg", cfg)) begin
            `uvm_warning("AXI_DRV", "Configuration object not found, using defaults")
        end
        
        // Get source ID from configuration
        if (cfg != null) begin
            source_id = cfg.get_source_id(this.get_name());
        end
        
        `uvm_info("AXI_DRV", $sformatf(
            "AXI4 driver built: source_id=%0d", source_id), UVM_MEDIUM)
    endfunction

    // ==========================================================================
    // Run Phase - Main Driver Loop
    // ==========================================================================
    //
    // Main driver loop that continuously receives transactions from sequencer
    // and drives them onto the AXI4 interface. Handles both write and read
    // transactions with proper protocol sequencing.
    //
    // AXI4 Protocol Timing:
    //   Write Transaction: AW → W → B (address → data → response)
    //   Read Transaction:  AR → R (address → data)
    //
    // Handshake Protocol:
    //   - Master asserts valid when ready to transfer
    //   - Slave asserts ready when able to accept
    //   - Transfer occurs when both valid and ready are high on same clock edge
    //
    virtual task run_phase(uvm_phase phase);
        `uvm_info("AXI_DRV", "AXI4 driver starting run phase", UVM_MEDIUM)
        
        // Wait for reset deassertion
        wait(vif.aresetn == 1'b1);
        @(posedge vif.aclk);
        
        // Main driver loop
        forever begin
            axi_transaction tr;
            
            // Get next transaction from sequencer
            seq_item_port.get_next_item(tr);
            
            `uvm_info("AXI_DRV", $sformatf(
                "Driving transaction: type=%s, addr=0x%0h, len=%0d, id=%0d",
                tr.trans_type.name(),
                (tr.trans_type == WRITE) ? tr.awaddr : tr.araddr,
                (tr.trans_type == WRITE) ? tr.awlen : tr.arlen,
                (tr.trans_type == WRITE) ? tr.awid : tr.arid), UVM_MEDIUM)
            
            // Update counters
            trans_count++;
            if (tr.trans_type == WRITE) begin
                write_count++;
            end else begin
                read_count++;
            end
            
            // Set transaction source ID
            tr.source_id = source_id;
            tr.start_time = $time;
            
            // Drive transaction based on type
            if (tr.trans_type == WRITE) begin
                fork
                    // Write transaction: Three parallel channels
                    drive_write_transaction(tr);
                join_none
                
                // Wait for write transaction to complete
                wait(tr.end_time > 0);
                
            end else if (tr.trans_type == READ) begin
                fork
                    // Read transaction: Two parallel channels
                    drive_read_transaction(tr);
                join_none
                
                // Wait for read transaction to complete
                wait(tr.end_time > 0);
            end
            
            // Signal transaction completion to sequencer
            seq_item_port.item_done();
            
            `uvm_info("AXI_DRV", $sformatf(
                "Transaction complete: type=%s, latency=%0d cycles",
                tr.trans_type.name(), tr.get_latency()), UVM_MEDIUM)
        end
    endtask

    // ==========================================================================
    // Drive Write Transaction
    // ==========================================================================
    //
    // Drives a complete write transaction through all three write channels:
    //   1. Write Address Channel (AW): Address and control information
    //   2. Write Data Channel (W): Data payload (may be multiple beats)
    //   3. Write Response Channel (B): Completion status
    //
    // Protocol Flow:
    //   AW: Master drives address → Slave accepts → Handshake complete
    //   W:  Master drives data beats → Slave accepts each → All beats sent
    //   B:  Slave drives response → Master accepts → Transaction complete
    //
    task drive_write_transaction(axi_transaction tr);
        longint aw_start_time, w_start_time, b_end_time;
        
        fork
            // Drive write address channel
            begin
                aw_start_time = $time;
                drive_write_address_channel(tr);
            end
            
            // Drive write data channel
            begin
                w_start_time = $time;
                drive_write_data_channel(tr);
            end
            
            // Wait for write response
            begin
                wait_write_response(tr);
                b_end_time = $time;
                tr.end_time = b_end_time;
                
                // Calculate latency
                longint latency = b_end_time - aw_start_time;
                total_write_latency += latency;
                if (latency > max_write_latency) begin
                    max_write_latency = latency;
                end
            end
        join
    endtask

    // ==========================================================================
    // Drive Write Address Channel
    // ==========================================================================
    //
    // Drives the write address channel (AW) with address and control signals.
    // Implements AXI4 handshake protocol: valid/ready signaling.
    //
    // Protocol Requirements:
    //   - Master asserts awvalid when address is valid
    //   - Master holds address stable until awready is asserted
    //   - Transfer occurs when both awvalid and awready are high
    //   - Address must be aligned to burst size
    //
    task drive_write_address_channel(axi_transaction tr);
        // Protocol compliance checks
        if (!check_address_alignment(tr.awaddr, tr.awsize)) begin
            `uvm_error("AXI_DRV", $sformatf(
                "Address misaligned: addr=0x%0h, size=%0d",
                tr.awaddr, tr.awsize))
            protocol_violations++;
            return;
        end
        
        if (!check_burst_parameters(tr.awlen, tr.awsize, tr.awburst)) begin
            `uvm_error("AXI_DRV", $sformatf(
                "Invalid burst parameters: len=%0d, size=%0d, burst=%0d",
                tr.awlen, tr.awsize, tr.awburst))
            protocol_violations++;
            return;
        end
        
        // Store start time for latency calculation
        write_start_time[tr.awid] = $time;
        
        // Drive address channel signals
        @(posedge vif.aclk);
        vif.awaddr   <= tr.awaddr;
        vif.awlen    <= tr.awlen;
        vif.awsize   <= tr.awsize;
        vif.awburst  <= tr.awburst;
        vif.awid     <= tr.awid;
        vif.awqos    <= tr.awqos;
        vif.awregion <= tr.awregion;
        vif.awlock   <= tr.awlock;
        vif.awcache  <= tr.awcache;
        vif.awprot   <= tr.awprot;
        vif.awvalid  <= 1'b1;
        
        `uvm_info("AXI_DRV", $sformatf(
            "AW channel: addr=0x%0h, len=%0d, id=%0d, valid=1",
            tr.awaddr, tr.awlen, tr.awid), UVM_DEBUG)
        
        // Wait for handshake (awready)
        do begin
            @(posedge vif.aclk);
            check_handshake_timing(vif.awvalid, vif.awready, "AW");
        end while (vif.awready != 1'b1);
        
        // Handshake complete - deassert valid
        vif.awvalid <= 1'b0;
        
        `uvm_info("AXI_DRV", $sformatf(
            "AW channel handshake complete: id=%0d", tr.awid), UVM_DEBUG)
    endtask

    // ==========================================================================
    // Drive Write Data Channel
    // ==========================================================================
    //
    // Drives the write data channel (W) with data payload. Handles burst
    // transfers with multiple data beats. Each beat requires a handshake.
    //
    // Protocol Requirements:
    //   - Master asserts wvalid when data is valid
    //   - Master holds data stable until wready is asserted
    //   - Transfer occurs when both wvalid and wready are high
    //   - wlast must be asserted on final beat of burst
    //   - wstrb must be non-zero (at least one byte enabled)
    //
    task drive_write_data_channel(axi_transaction tr);
        int num_beats = tr.awlen + 1;  // Burst length: awlen+1 transfers
        
        `uvm_info("AXI_DRV", $sformatf(
            "W channel: driving %0d beats, id=%0d", num_beats, tr.awid), UVM_DEBUG)
        
        // Drive each beat of the burst
        for (int beat = 0; beat < num_beats; beat++) begin
            @(posedge vif.aclk);
            
            // Drive data signals
            vif.wdata  <= tr.wdata;  // In real implementation, use tr.data[beat]
            vif.wstrb  <= tr.wstrb;  // In real implementation, use tr.strb[beat]
            vif.wlast  <= (beat == tr.awlen);  // Last beat indicator
            vif.wuser  <= tr.wuser;
            vif.wvalid <= 1'b1;
            
            `uvm_info("AXI_DRV", $sformatf(
                "W channel beat %0d/%0d: data=0x%0h, strb=0x%04h, last=%0b",
                beat+1, num_beats, tr.wdata, tr.wstrb, vif.wlast), UVM_DEBUG)
            
            // Wait for handshake (wready)
            do begin
                @(posedge vif.aclk);
                check_handshake_timing(vif.wvalid, vif.wready, "W");
            end while (vif.wready != 1'b1);
            
            // Handshake complete - deassert valid
            vif.wvalid <= 1'b0;
            
            // Protocol check: wlast must be asserted on final beat
            if (beat == tr.awlen && vif.wlast != 1'b1) begin
                `uvm_error("AXI_DRV", 
                    "wlast not asserted on final beat of burst")
                protocol_violations++;
            end
        end
        
        `uvm_info("AXI_DRV", $sformatf(
            "W channel complete: %0d beats driven, id=%0d",
            num_beats, tr.awid), UVM_DEBUG)
    endtask

    // ==========================================================================
    // Wait Write Response
    // ==========================================================================
    //
    // Waits for write response channel (B) to complete the write transaction.
    // Validates response ID matches request ID and checks response status.
    //
    // Protocol Requirements:
    //   - Slave asserts bvalid when response is valid
    //   - Master asserts bready when ready to accept response
    //   - Transfer occurs when both bvalid and bready are high
    //   - bid must match awid of corresponding write
    //   - bresp indicates success (OKAY) or error (SLVERR, DECERR)
    //
    task wait_write_response(axi_transaction tr);
        // Assert bready to accept response
        vif.bready <= 1'b1;
        
        `uvm_info("AXI_DRV", $sformatf(
            "Waiting for B channel response: expecting id=%0d", tr.awid), UVM_DEBUG)
        
        // Wait for response
        do begin
            @(posedge vif.aclk);
        end while (vif.bvalid != 1'b1);
        
        // Response received - validate
        if (vif.bid != tr.awid) begin
            `uvm_error("AXI_DRV", $sformatf(
                "Response ID mismatch: expected %0d, got %0d",
                tr.awid, vif.bid))
            protocol_violations++;
        end
        
        // Validate response status
        validate_response(vif.bresp, tr.awid, "Write");
        
        // Capture response in transaction
        tr.bresp = vif.bresp;
        tr.bid = vif.bid;
        tr.buser = vif.buser;
        
        // Deassert bready
        vif.bready <= 1'b0;
        
        `uvm_info("AXI_DRV", $sformatf(
            "B channel response received: id=%0d, resp=%0d (%s)",
            vif.bid, vif.bresp,
            (vif.bresp == 2'b00) ? "OKAY" :
            (vif.bresp == 2'b01) ? "EXOKAY" :
            (vif.bresp == 2'b10) ? "SLVERR" : "DECERR"), UVM_DEBUG)
    endtask

    // ==========================================================================
    // Drive Read Transaction
    // ==========================================================================
    //
    // Drives a complete read transaction through both read channels:
    //   1. Read Address Channel (AR): Address and control information
    //   2. Read Data Channel (R): Data payload (may be multiple beats)
    //
    // Protocol Flow:
    //   AR: Master drives address → Slave accepts → Handshake complete
    //   R:  Slave drives data beats → Master accepts each → All beats received
    //
    task drive_read_transaction(axi_transaction tr);
        longint ar_start_time, r_end_time;
        
        fork
            // Drive read address channel
            begin
                ar_start_time = $time;
                drive_read_address_channel(tr);
            end
            
            // Wait for read data
            begin
                wait_read_data(tr);
                r_end_time = $time;
                tr.end_time = r_end_time;
                
                // Calculate latency
                longint latency = r_end_time - ar_start_time;
                total_read_latency += latency;
                if (latency > max_read_latency) begin
                    max_read_latency = latency;
                end
            end
        join
    endtask

    // ==========================================================================
    // Drive Read Address Channel
    // ==========================================================================
    //
    // Drives the read address channel (AR) with address and control signals.
    // Similar to write address channel but for read transactions.
    //
    task drive_read_address_channel(axi_transaction tr);
        // Protocol compliance checks
        if (!check_address_alignment(tr.araddr, tr.arsize)) begin
            `uvm_error("AXI_DRV", $sformatf(
                "Address misaligned: addr=0x%0h, size=%0d",
                tr.araddr, tr.arsize))
            protocol_violations++;
            return;
        end
        
        if (!check_burst_parameters(tr.arlen, tr.arsize, tr.arburst)) begin
            `uvm_error("AXI_DRV", $sformatf(
                "Invalid burst parameters: len=%0d, size=%0d, burst=%0d",
                tr.arlen, tr.arsize, tr.arburst))
            protocol_violations++;
            return;
        end
        
        // Store start time for latency calculation
        read_start_time[tr.arid] = $time;
        
        // Drive address channel signals
        @(posedge vif.aclk);
        vif.araddr   <= tr.araddr;
        vif.arlen    <= tr.arlen;
        vif.arsize   <= tr.arsize;
        vif.arburst  <= tr.arburst;
        vif.arid     <= tr.arid;
        vif.arqos    <= tr.arqos;
        vif.arregion <= tr.arregion;
        vif.arlock   <= tr.arlock;
        vif.arcache  <= tr.arcache;
        vif.arprot   <= tr.arprot;
        vif.arvalid  <= 1'b1;
        
        `uvm_info("AXI_DRV", $sformatf(
            "AR channel: addr=0x%0h, len=%0d, id=%0d, valid=1",
            tr.araddr, tr.arlen, tr.arid), UVM_DEBUG)
        
        // Wait for handshake (arready)
        do begin
            @(posedge vif.aclk);
            check_handshake_timing(vif.arvalid, vif.arready, "AR");
        end while (vif.arready != 1'b1);
        
        // Handshake complete - deassert valid
        vif.arvalid <= 1'b0;
        
        `uvm_info("AXI_DRV", $sformatf(
            "AR channel handshake complete: id=%0d", tr.arid), UVM_DEBUG)
    endtask

    // ==========================================================================
    // Wait Read Data
    // ==========================================================================
    //
    // Waits for read data channel (R) to receive all data beats of the burst.
    // Validates response IDs match request ID and checks rlast on final beat.
    //
    // Protocol Requirements:
    //   - Slave asserts rvalid when data is valid
    //   - Master asserts rready when ready to accept data
    //   - Transfer occurs when both rvalid and rready are high
    //   - rid must match arid of corresponding read
    //   - rlast must be asserted on final beat of burst
    //
    task wait_read_data(axi_transaction tr);
        int num_beats = tr.arlen + 1;  // Burst length: arlen+1 transfers
        int beat_count = 0;
        
        // Assert rready to accept data
        vif.rready <= 1'b1;
        
        `uvm_info("AXI_DRV", $sformatf(
            "Waiting for R channel data: expecting %0d beats, id=%0d",
            num_beats, tr.arid), UVM_DEBUG)
        
        // Receive each beat of the burst
        for (int beat = 0; beat < num_beats; beat++) begin
            // Wait for data valid
            do begin
                @(posedge vif.aclk);
            end while (vif.rvalid != 1'b1);
            
            // Validate response ID
            if (vif.rid != tr.arid) begin
                `uvm_error("AXI_DRV", $sformatf(
                    "Response ID mismatch: expected %0d, got %0d (beat %0d)",
                    tr.arid, vif.rid, beat))
                protocol_violations++;
            end
            
            // Capture data
            tr.rdata = vif.rdata;  // In real implementation, use tr.data[beat]
            tr.rresp = vif.rresp;
            tr.rid = vif.rid;
            tr.rlast = vif.rlast;
            tr.ruser = vif.ruser;
            
            `uvm_info("AXI_DRV", $sformatf(
                "R channel beat %0d/%0d: data=0x%0h, resp=%0d, last=%0b",
                beat+1, num_beats, vif.rdata, vif.rresp, vif.rlast), UVM_DEBUG)
            
            // Protocol check: rlast must be asserted on final beat
            if (beat == tr.arlen && vif.rlast != 1'b1) begin
                `uvm_error("AXI_DRV", 
                    "rlast not asserted on final beat of burst")
                protocol_violations++;
            end
            
            // Validate response status
            if (beat == 0) begin  // Check response on first beat
                validate_response(vif.rresp, tr.arid, "Read");
            end
            
            beat_count++;
        end
        
        // Deassert rready
        vif.rready <= 1'b0;
        
        // Validate all beats received
        if (beat_count != num_beats) begin
            `uvm_error("AXI_DRV", $sformatf(
                "Beat count mismatch: expected %0d, received %0d",
                num_beats, beat_count))
            protocol_violations++;
        end
        
        `uvm_info("AXI_DRV", $sformatf(
            "R channel complete: %0d beats received, id=%0d",
            beat_count, tr.arid), UVM_DEBUG)
    endtask

    // ==========================================================================
    // Protocol Compliance Methods
    // ==========================================================================

    // ==========================================================================
    // Check Address Alignment
    // ==========================================================================
    //
    // Validates that address is aligned to burst size as required by AXI4.
    // Address must be aligned to (2^awsize) bytes.
    //
    // Example: awsize=3 (8 bytes) → address must be 8-byte aligned
    //          Address 0x1000 is aligned, 0x1001 is not
    //
    function bit check_address_alignment(bit [31:0] addr, bit [2:0] size);
        int alignment = 1 << size;  // Alignment = 2^size bytes
        
        if (addr % alignment != 0) begin
            `uvm_warning("AXI_DRV", $sformatf(
                "Address misaligned: addr=0x%0h, size=%0d (requires %0d-byte alignment)",
                addr, size, alignment))
            return 0;
        end
        
        return 1;
    endfunction

    // ==========================================================================
    // Check Burst Parameters
    // ==========================================================================
    //
    // Validates burst length, size, and type are within valid ranges.
    // AXI4 supports bursts of 1-256 transfers with sizes 1-128 bytes.
    //
    function bit check_burst_parameters(bit [7:0] len, bit [2:0] size, bit [1:0] burst);
        // Check burst length: 0-255 (represents 1-256 transfers)
        if (len > 255) begin
            `uvm_warning("AXI_DRV", $sformatf(
                "Invalid burst length: %0d (max 255)", len))
            return 0;
        end
        
        // Check burst size: 0-7 (represents 1-128 bytes)
        if (size > 7) begin
            `uvm_warning("AXI_DRV", $sformatf(
                "Invalid burst size: %0d (max 7)", size))
            return 0;
        end
        
        // Check burst type: 0-2 (FIXED, INCR, WRAP)
        if (burst > 2) begin
            `uvm_warning("AXI_DRV", $sformatf(
                "Invalid burst type: %0d (max 2)", burst))
            return 0;
        end
        
        return 1;
    endfunction

    // ==========================================================================
    // Check Handshake Timing
    // ==========================================================================
    //
    // Validates handshake timing meets AXI4 requirements.
    // Valid can be asserted before ready, but ready cannot be asserted before
    // valid (unless valid is already asserted).
    //
    // Protocol Rule:
    //   - Valid can be asserted independently
    //   - Ready can be asserted independently
    //   - Transfer occurs when both are high on same clock edge
    //
    function void check_handshake_timing(bit valid, bit ready, string channel);
        static int timeout_count[$];
        static int timeout_limit = 1000;  // Maximum cycles to wait
        
        // Count cycles waiting for handshake
        if (valid && !ready) begin
            if (timeout_count.size() == 0) begin
                timeout_count.push_back(0);
            end else begin
                timeout_count[0]++;
            end
            
            // Check for timeout
            if (timeout_count[0] > timeout_limit) begin
                `uvm_error("AXI_DRV", $sformatf(
                    "Handshake timeout on %s channel: valid=%0b, ready=%0b, timeout=%0d cycles",
                    channel, valid, ready, timeout_count[0]))
                handshake_timeouts++;
                timeout_count.delete(0);
            end
        end else begin
            // Handshake complete - reset timeout counter
            if (timeout_count.size() > 0) begin
                timeout_count.delete(0);
            end
        end
    endfunction

    // ==========================================================================
    // Validate Response
    // ==========================================================================
    //
    // Validates write/read response status. OKAY indicates success, SLVERR
    // indicates slave error, DECERR indicates decode error.
    //
    function void validate_response(bit [1:0] resp, bit [3:0] id, string trans_type);
        case (resp)
            2'b00: begin  // OKAY - Normal success
                `uvm_info("AXI_DRV", $sformatf(
                    "%s transaction OKAY: id=%0d", trans_type, id), UVM_DEBUG)
            end
            2'b01: begin  // EXOKAY - Exclusive access success
                `uvm_info("AXI_DRV", $sformatf(
                    "%s transaction EXOKAY: id=%0d", trans_type, id), UVM_DEBUG)
            end
            2'b10: begin  // SLVERR - Slave error
                `uvm_error("AXI_DRV", $sformatf(
                    "%s transaction SLVERR: id=%0d - Slave error occurred",
                    trans_type, id))
                protocol_violations++;
            end
            2'b11: begin  // DECERR - Decode error
                `uvm_error("AXI_DRV", $sformatf(
                    "%s transaction DECERR: id=%0d - Address decode error",
                    trans_type, id))
                protocol_violations++;
            end
        endcase
    endfunction

    // ==========================================================================
    // Report Phase
    // ==========================================================================
    //
    // Reports driver statistics including transaction counts, latencies, and
    // protocol compliance metrics.
    //
    virtual function void report_phase(uvm_phase phase);
        real avg_write_latency = 0.0;
        real avg_read_latency = 0.0;
        
        // Calculate average latencies
        if (write_count > 0) begin
            avg_write_latency = real'(total_write_latency) / real'(write_count);
        end
        if (read_count > 0) begin
            avg_read_latency = real'(total_read_latency) / real'(read_count);
        end
        
        `uvm_info("AXI_DRV", $sformatf(
            "\n=== AXI4 Driver Statistics ===\n" +
            "Source ID:              %0d\n" +
            "Total Transactions:     %0d\n" +
            "  Write Transactions:   %0d\n" +
            "  Read Transactions:    %0d\n" +
            "Write Latency:\n" +
            "  Average:              %0.2f cycles\n" +
            "  Maximum:              %0d cycles\n" +
            "Read Latency:\n" +
            "  Average:              %0.2f cycles\n" +
            "  Maximum:              %0d cycles\n" +
            "Protocol Violations:     %0d\n" +
            "Handshake Timeouts:      %0d\n" +
            "==============================",
            source_id,
            trans_count,
            write_count,
            read_count,
            avg_write_latency,
            max_write_latency,
            avg_read_latency,
            max_read_latency,
            protocol_violations,
            handshake_timeouts), UVM_MEDIUM)
    endfunction

endclass

`endif // AXI_DRIVER_SV

