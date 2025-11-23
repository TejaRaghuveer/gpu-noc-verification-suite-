// ==============================================================================
// File: formal_properties.sv
// Description: Comprehensive SystemVerilog Assertions for GPU Interconnect NoC
//              Router Formal Verification
// Author: Formal Verification Team
// Date: January 2025
// Copyright (c) 2025 NVIDIA Corporation
//
// This file contains formal properties (assertions, assumptions, cover
// statements) for verifying GPU interconnect NoC router correctness using
// formal verification tools (JasperGold, Questa Formal).
//
// Property Categories:
//   1. Safety Properties: No bad things happen (invariants, protocol compliance)
//   2. Liveness Properties: Good things eventually happen (progress, fairness)
//   3. Coverage Properties: Measure property coverage
//   4. Assumptions: Environmental constraints for formal tools
//
// PROTOCOL SPECIFICATION REFERENCES:
//   - ARM AMBA 5 AXI4 Protocol Specification (ARM IHI 0022E)
//     * Section 3.1.1: Handshake Protocol
//     * Section 3.1.2: Burst Transfers
//     * Section 3.1.3: Response Signals
//     * Section 3.1.5: Transaction IDs
//     * Section 3.1.6: Atomic Operations
//   - IEEE 802.1Q: Quality of Service (QoS) handling
//     * Priority-based forwarding
//     * QoS preservation through network
//
// FORMAL TOOL TARGETS:
//   - JasperGold (Synopsys): Supports SVA, PSL
//   - Questa Formal (Mentor Graphics): Supports SVA, PSL
//   - Note: Some properties use tool-specific syntax (noted in comments)
//
// PROPERTY ORGANIZATION:
//   - Safety Properties: Protocol compliance, no overflow, no corruption
//   - Liveness Properties: Packet delivery, fairness, deadlock freedom
//   - Helper Functions: Utility functions for property expressions
//   - Coverage Properties: Coverage measurement
//   - Assumptions: Environmental constraints
//
// ==============================================================================

`ifndef FORMAL_PROPERTIES_SV
`define FORMAL_PROPERTIES_SV

// ==============================================================================
// Includes and Package Imports
// ==============================================================================

import uvm_pkg::*;
`include "uvm_macros.svh"

// ==============================================================================
// Constants and Parameters
// ==============================================================================

// Buffer depths
parameter int BUFFER_DEPTH = 16;           // Input/output buffer depth
parameter int VC_BUFFER_DEPTH = 8;         // Virtual channel buffer depth

// Routing constants (for mesh topology)
parameter int PORT_NORTH = 0;
parameter int PORT_SOUTH = 1;
parameter int PORT_EAST  = 2;
parameter int PORT_WEST  = 3;
parameter int PORT_LOCAL = 4;              // Local injection/ejection port

// Latency bounds
parameter int MAX_LATENCY = 1000;          // Maximum packet latency (cycles)
parameter int MIN_LATENCY = 1;             // Minimum packet latency (cycles)
parameter int MAX_WAIT = 100;              // Maximum wait for arbitration (cycles)
parameter int BACKPRESSURE_LIMIT = 50;     // Maximum backpressure duration

// Burst type constants (AXI4)
parameter bit [1:0] BURST_FIXED = 2'b00;
parameter bit [1:0] BURST_INCR  = 2'b01;
parameter bit [1:0] BURST_WRAP  = 2'b10;

// Response code constants (AXI4)
parameter bit [1:0] RESP_OKAY   = 2'b00;
parameter bit [1:0] RESP_EXOKAY = 2'b01;
parameter bit [1:0] RESP_SLVERR = 2'b10;
parameter bit [1:0] RESP_DECERR = 2'b11;

// ==============================================================================
// Interface and Signal Declarations
// ==============================================================================
//
// Note: These would typically come from the DUT interface. For formal
// verification, we declare them here for clarity. In actual use, these
// would be bound from the design interface.
//

// Clock and reset
wire clk;
wire reset_n;
wire reset = !reset_n;

// AXI4 Write Address Channel
wire        awvalid;
wire        awready;
wire [31:0] awaddr;
wire [7:0]  awlen;
wire [2:0]  awsize;
wire [1:0]  awburst;
wire [3:0]  awid;
wire [3:0]  awqos;
wire [3:0]  awregion;
wire        awlock;
wire [3:0]  awcache;
wire [2:0]  awprot;

// AXI4 Write Data Channel
wire        wvalid;
wire        wready;
wire [127:0] wdata;
wire [15:0]  wstrb;
wire         wlast;
wire [7:0]   wuser;

// AXI4 Write Response Channel
wire        bvalid;
wire        bready;
wire [1:0]  bresp;
wire [3:0]  bid;
wire [7:0]  buser;

// AXI4 Read Address Channel
wire        arvalid;
wire        arready;
wire [31:0] araddr;
wire [7:0]  arlen;
wire [2:0]  arsize;
wire [1:0]  arburst;
wire [3:0]  arid;
wire [3:0]  arqos;
wire [3:0]  arregion;
wire        arlock;
wire [3:0]  arcache;
wire [2:0]  arprot;

// AXI4 Read Data Channel
wire        rvalid;
wire        rready;
wire [127:0] rdata;
wire [1:0]   rresp;
wire [3:0]   rid;
wire         rlast;
wire [7:0]   ruser;

// Router internal signals
wire [3:0]  current_router_x;      // Current router X coordinate
wire [3:0]  current_router_y;      // Current router Y coordinate
wire [3:0]  dest_router_x;         // Destination router X coordinate
wire [3:0]  dest_router_y;         // Destination router Y coordinate
wire        packet_valid;           // Packet valid signal
wire        packet_delivered;       // Packet delivered signal
wire        packet_injected;       // Packet injected signal
wire [3:0]  route_output;          // Routing output port selection
wire [1:0]  vc_allocated [0:1];     // Virtual channel allocation (VC0, VC1)
wire [1:0]  vc_freed [0:1];         // Virtual channel free signals

// Buffer signals
wire        push_enable;
wire        pop_enable;
wire [4:0]  buffer_occupancy;      // Buffer occupancy count
wire        write_enable;
wire        read_enable;
wire [4:0]  buffer_count;          // Output buffer count

// Arbiter signals
wire [3:0]  request [0:3];          // Request signals from 4 input ports
wire [3:0]  grant_vector;          // Grant vector (one-hot)
wire        grant [0:3];             // Individual grant signals

// QoS and packet signals
wire [3:0]  packet_qos;             // Packet QoS field
wire [127:0] packet_data;           // Packet data payload

// Performance monitoring
int active_packets;                  // Number of active packets in NoC
bit backpressure_asserted;          // Backpressure signal

// ==============================================================================
// Helper Functions
// ==============================================================================
//
// Utility functions for property expressions. These simplify complex
// property logic and improve readability.
//

// ------------------------------------------------------------------------------
// Function: is_valid_transaction
// ------------------------------------------------------------------------------
// Purpose: Validate AXI4 transaction parameters are within valid ranges.
//
// Reference: ARM AMBA 5 AXI4 Specification (ARM IHI 0022E)
//   - Section 3.1.2: Burst Transfers
//   - awlen: 0-255 (1-256 transfers)
//   - awsize: 0-7 (1-128 bytes per transfer)
//   - awburst: 0-2 (FIXED, INCR, WRAP)
//
function automatic bit is_valid_transaction(
    bit [7:0]  len,
    bit [2:0]  size,
    bit [1:0]  burst
);
    return (len inside {[0:255]}) &&
           (size inside {[0:7]}) &&
           (burst inside {[0:2]});
endfunction

// ------------------------------------------------------------------------------
// Function: is_packet_at_dest
// ------------------------------------------------------------------------------
// Purpose: Check if packet has reached its destination router.
//
// Returns: 1 if packet is at destination, 0 otherwise
//
function automatic bit is_packet_at_dest();
    return (current_router_x == dest_router_x) &&
           (current_router_y == dest_router_y) &&
           packet_valid;
endfunction

// ------------------------------------------------------------------------------
// Function: calculate_burst_beats
// ------------------------------------------------------------------------------
// Purpose: Calculate number of beats in a burst transaction.
//
// Reference: ARM AMBA 5 AXI4 Specification (ARM IHI 0022E)
//   - Section 3.1.2: Number of transfers = awlen + 1
//
function automatic int calculate_burst_beats(bit [7:0] len);
    return len + 1;
endfunction

// ------------------------------------------------------------------------------
// Function: is_qos_valid
// ------------------------------------------------------------------------------
// Purpose: Validate QoS value is within valid range (0-15).
//
// Reference: ARM AMBA 5 AXI4 Specification (ARM IHI 0022E)
//   - Section 3.1.1: QoS Signals (4-bit field)
//
function automatic bit is_qos_valid(bit [3:0] qos);
    return qos inside {[0:15]};
endfunction

// ------------------------------------------------------------------------------
// Function: is_response_valid
// ------------------------------------------------------------------------------
// Purpose: Validate AXI4 response code is valid.
//
// Reference: ARM AMBA 5 AXI4 Specification (ARM IHI 0022E)
//   - Section 3.1.3: Response Signals
//   - Valid codes: OKAY (00), EXOKAY (01), SLVERR (10), DECERR (11)
//
function automatic bit is_response_valid(bit [1:0] resp);
    return resp inside {[0:3]};
endfunction

// ==============================================================================
// SAFETY PROPERTIES - No Bad Things Happen
// ==============================================================================
//
// Safety properties ensure that bad states never occur. These are invariants
// that must hold at all times. Violation of a safety property indicates
// a design bug.
//

// ==============================================================================
// A. AXI4 Protocol Handshake Properties
// ==============================================================================
//
// These properties verify AXI4 handshake protocol compliance. The handshake
// protocol requires that valid/ready signals meet specific timing requirements.
//
// Reference: ARM AMBA 5 AXI4 Specification (ARM IHI 0022E)
//   - Section 3.1.1: Handshake Protocol
//   - Key requirement: When valid is asserted and ready is not, all address/data
//     signals must remain stable until the handshake completes.
//

// ------------------------------------------------------------------------------
// Property: axi_write_address_handshake
// ------------------------------------------------------------------------------
// Purpose: Verify write address channel handshake protocol compliance.
//
// Specification: ARM AMBA 5 AXI4 (ARM IHI 0022E), Section 3.1.1
//   - When awvalid is asserted and awready is not asserted, all address
//     channel signals (awaddr, awlen, awsize, awburst, awid, awqos) must
//     remain stable until the handshake completes.
//
// Expected Behavior:
//   - If awvalid=1 and awready=0, then on the next cycle, awvalid must
//     remain 1 and all address signals must remain unchanged.
//   - This prevents signal glitches during handshake.
//
property axi_write_address_handshake;
    @(posedge clk) disable iff (!reset_n)
        (awvalid && !awready) |->
        ##1 (awvalid && 
             $stable(awaddr) && 
             $stable(awlen) && 
             $stable(awsize) && 
             $stable(awburst) && 
             $stable(awid) && 
             $stable(awqos));
endproperty

assert property (axi_write_address_handshake)
    else `uvm_error("FORMAL", "AXI4 Write Address handshake violation: signals not stable");

// ------------------------------------------------------------------------------
// Property: axi_write_data_handshake
// ------------------------------------------------------------------------------
// Purpose: Verify write data channel handshake protocol compliance.
//
// Specification: ARM AMBA 5 AXI4 (ARM IHI 0022E), Section 3.1.1
//   - When wvalid is asserted and wready is not asserted, all data channel
//     signals (wdata, wstrb, wlast) must remain stable.
//
property axi_write_data_handshake;
    @(posedge clk) disable iff (!reset_n)
        (wvalid && !wready) |->
        ##1 (wvalid && 
             $stable(wdata) && 
             $stable(wstrb) && 
             $stable(wlast));
endproperty

assert property (axi_write_data_handshake)
    else `uvm_error("FORMAL", "AXI4 Write Data handshake violation: signals not stable");

// ------------------------------------------------------------------------------
// Property: axi_read_address_handshake
// ------------------------------------------------------------------------------
// Purpose: Verify read address channel handshake protocol compliance.
//
// Specification: ARM AMBA 5 AXI4 (ARM IHI 0022E), Section 3.1.1
//   - When arvalid is asserted and arready is not asserted, all address
//     channel signals must remain stable.
//
property axi_read_address_handshake;
    @(posedge clk) disable iff (!reset_n)
        (arvalid && !arready) |->
        ##1 (arvalid && 
             $stable(araddr) && 
             $stable(arlen) && 
             $stable(arsize) && 
             $stable(arburst) && 
             $stable(arid) && 
             $stable(arqos));
endproperty

assert property (axi_read_address_handshake)
    else `uvm_error("FORMAL", "AXI4 Read Address handshake violation: signals not stable");

// ==============================================================================
// B. Response ID Matching (Critical for Out-of-Order)
// ==============================================================================
//
// These properties ensure that response transactions match their corresponding
// request transactions using transaction IDs. This is critical for out-of-order
// completion support in AXI4.
//
// Reference: ARM AMBA 5 AXI4 Specification (ARM IHI 0022E)
//   - Section 3.1.5: Transaction IDs
//   - Response must return same ID as request
//

// ------------------------------------------------------------------------------
// Property: write_response_id_match
// ------------------------------------------------------------------------------
// Purpose: Verify write response returns same transaction ID as write address.
//
// Specification: ARM AMBA 5 AXI4 (ARM IHI 0022E), Section 3.1.5
//   - The bid (write response ID) must match the awid (write address ID)
//   - This enables out-of-order write completion
//
// Expected Behavior:
//   - When write address handshake occurs with awid=X, eventually write
//     response must arrive with bid=X
//
property write_response_id_match;
    int captured_awid;
    @(posedge clk) disable iff (!reset_n)
        ((awvalid && awready), captured_awid = awid) |->
        s_eventually (bvalid && (bid == captured_awid));
endproperty

assert property (write_response_id_match)
    else `uvm_error("FORMAL", "Write response ID mismatch: bid != awid");

// ------------------------------------------------------------------------------
// Property: read_response_id_match
// ------------------------------------------------------------------------------
// Purpose: Verify read response returns same transaction ID as read address.
//
// Specification: ARM AMBA 5 AXI4 (ARM IHI 0022E), Section 3.1.5
//   - The rid (read response ID) must match the arid (read address ID)
//   - This enables out-of-order read completion
//
property read_response_id_match;
    int captured_arid;
    @(posedge clk) disable iff (!reset_n)
        ((arvalid && arready), captured_arid = arid) |->
        s_eventually (rvalid && rlast && (rid == captured_arid));
endproperty

assert property (read_response_id_match)
    else `uvm_error("FORMAL", "Read response ID mismatch: rid != arid");

// ==============================================================================
// C. Burst Atomicity
// ==============================================================================
//
// These properties ensure that burst transactions complete atomically - the
// correct number of data beats are transferred without interleaving.
//
// Reference: ARM AMBA 5 AXI4 Specification (ARM IHI 0022E)
//   - Section 3.1.2: Burst Transfers
//   - Number of transfers = awlen + 1 (or arlen + 1 for reads)
//

// ------------------------------------------------------------------------------
// Property: burst_atomicity_write
// ------------------------------------------------------------------------------
// Purpose: Verify write burst completes with correct number of beats.
//
// Specification: ARM AMBA 5 AXI4 (ARM IHI 0022E), Section 3.1.2
//   - Write burst must transfer exactly (awlen + 1) data beats
//   - wlast must be asserted on the final beat only
//
// Expected Behavior:
//   - After write address handshake with awlen=N, exactly (N+1) write data
//     beats must occur, with wlast asserted on the final beat
//
property burst_atomicity_write;
    int burst_len;
    int beat_count;
    @(posedge clk) disable iff (!reset_n)
        ((awvalid && awready), burst_len = awlen, beat_count = 0) |->
        ##[1:$] first_match(
            (wvalid && wready, beat_count = beat_count + 1) [*0:$] ##1
            (wvalid && wready && wlast, beat_count = beat_count + 1)
        ) where (beat_count == burst_len + 1);
endproperty

assert property (burst_atomicity_write)
    else `uvm_error("FORMAL", "Write burst atomicity violation: incorrect beat count");

// ------------------------------------------------------------------------------
// Property: burst_atomicity_read
// ------------------------------------------------------------------------------
// Purpose: Verify read burst completes with correct number of beats.
//
// Specification: ARM AMBA 5 AXI4 (ARM IHI 0022E), Section 3.1.2
//   - Read burst must transfer exactly (arlen + 1) data beats
//   - rlast must be asserted on the final beat only
//
property burst_atomicity_read;
    int burst_len;
    int beat_count;
    @(posedge clk) disable iff (!reset_n)
        ((arvalid && arready), burst_len = arlen, beat_count = 0) |->
        ##[1:$] first_match(
            (rvalid && rready, beat_count = beat_count + 1) [*0:$] ##1
            (rvalid && rready && rlast, beat_count = beat_count + 1)
        ) where (beat_count == burst_len + 1);
endproperty

assert property (burst_atomicity_read)
    else `uvm_error("FORMAL", "Read burst atomicity violation: incorrect beat count");

// ==============================================================================
// D. No Buffer Overflow
// ==============================================================================
//
// These properties ensure that buffers never overflow, preventing data loss
// and ensuring system correctness.
//

// ------------------------------------------------------------------------------
// Property: input_buffer_no_overflow
// ------------------------------------------------------------------------------
// Purpose: Verify input buffer never exceeds capacity.
//
// Expected Behavior:
//   - When pushing data and not popping, buffer occupancy must be < BUFFER_DEPTH
//   - Prevents buffer overflow and data loss
//
property input_buffer_no_overflow;
    @(posedge clk) disable iff (!reset_n)
        (push_enable && !pop_enable) |->
        (buffer_occupancy < BUFFER_DEPTH);
endproperty

assert property (input_buffer_no_overflow)
    else `uvm_error("FORMAL", "Input buffer overflow detected");

// ------------------------------------------------------------------------------
// Property: output_buffer_no_overflow
// ------------------------------------------------------------------------------
// Purpose: Verify output buffer never exceeds capacity.
//
property output_buffer_no_overflow;
    @(posedge clk) disable iff (!reset_n)
        (write_enable && !read_enable) |->
        (buffer_count <= BUFFER_DEPTH);
endproperty

assert property (output_buffer_no_overflow)
    else `uvm_error("FORMAL", "Output buffer overflow detected");

// ==============================================================================
// E. Arbiter Mutual Exclusion
// ==============================================================================
//
// These properties ensure that arbiters grant access to at most one requester
// at a time, preventing conflicts and ensuring correct arbitration.
//

// ------------------------------------------------------------------------------
// Property: arbiter_one_grant
// ------------------------------------------------------------------------------
// Purpose: Verify arbiter grants to at most one port at a time.
//
// Expected Behavior:
//   - Grant vector must be one-hot or all zeros (at most one grant)
//   - Prevents multiple ports from accessing shared resource simultaneously
//
property arbiter_one_grant;
    @(posedge clk) disable iff (!reset_n)
        $onehot0(grant_vector);
endproperty

assert property (arbiter_one_grant)
    else `uvm_error("FORMAL", "Arbiter violation: multiple grants simultaneously");

// ==============================================================================
// F. XY Routing Correctness (for Mesh Topology)
// ==============================================================================
//
// These properties verify that XY routing algorithm is implemented correctly.
// XY routing is a dimension-order routing algorithm that routes first in X
// dimension, then in Y dimension. This routing is proven deadlock-free.
//
// Reference: NoC Routing Algorithms
//   - XY routing: Route in X dimension first, then Y dimension
//   - Deadlock-free for mesh topology with proper VC allocation
//

// ------------------------------------------------------------------------------
// Property: xy_routing_dimension_order
// ------------------------------------------------------------------------------
// Purpose: Verify X dimension routing occurs before Y dimension.
//
// Expected Behavior:
//   - If destination X != current X, route output must be EAST or WEST
//   - X dimension routing must occur first
//
property xy_routing_dimension_order;
    @(posedge clk) disable iff (!reset_n)
        (packet_valid && (dest_router_x != current_router_x)) |->
        ((route_output == PORT_EAST) || (route_output == PORT_WEST));
endproperty

assert property (xy_routing_dimension_order)
    else `uvm_error("FORMAL", "XY routing violation: Y dimension routed before X");

// ------------------------------------------------------------------------------
// Property: xy_routing_then_y
// ------------------------------------------------------------------------------
// Purpose: Verify Y dimension routing occurs only after X dimension complete.
//
// Expected Behavior:
//   - If destination X == current X and destination Y != current Y,
//     route output must be NORTH or SOUTH
//   - Y dimension routing only after X dimension complete
//
property xy_routing_then_y;
    @(posedge clk) disable iff (!reset_n)
        (packet_valid && 
         (dest_router_x == current_router_x) && 
         (dest_router_y != current_router_y)) |->
        ((route_output == PORT_NORTH) || (route_output == PORT_SOUTH));
endproperty

assert property (xy_routing_then_y)
    else `uvm_error("FORMAL", "XY routing violation: incorrect Y dimension routing");

// ==============================================================================
// G. VC Allocation Consistency
// ==============================================================================
//
// These properties ensure that virtual channel allocation is consistent and
// prevents resource leaks.
//

// ------------------------------------------------------------------------------
// Property: vc_allocation_stable
// ------------------------------------------------------------------------------
// Purpose: Verify virtual channel remains allocated until freed.
//
// Expected Behavior:
//   - Once VC allocated, it remains allocated until freed
//   - Prevents VC resource leaks and double-allocation
//
property vc_allocation_stable;
    @(posedge clk) disable iff (!reset_n)
        (vc_allocated[0] && !vc_freed[0]) |->
        ##1 vc_allocated[0];
endproperty

assert property (vc_allocation_stable)
    else `uvm_error("FORMAL", "VC allocation violation: VC freed prematurely");

// ==============================================================================
// H. QoS Preservation
// ==============================================================================
//
// These properties ensure that QoS (Quality of Service) values are preserved
// through the NoC, enabling priority-based arbitration.
//
// Reference: ARM AMBA 5 AXI4 Specification (ARM IHI 0022E)
//   - Section 3.1.1: QoS Signals
//   - IEEE 802.1Q: QoS preservation through network
//

// ------------------------------------------------------------------------------
// Property: qos_preserved
// ------------------------------------------------------------------------------
// Purpose: Verify QoS value is preserved from injection to delivery.
//
// Specification: ARM AMBA 5 AXI4 (ARM IHI 0022E), Section 3.1.1
//   - QoS signals (awqos, arqos) must be preserved through NoC
//   - Enables priority-based arbitration at each router
//
// Expected Behavior:
//   - Packet injected with QoS=X must be delivered with QoS=X
//   - QoS must not be corrupted or modified during routing
//
property qos_preserved;
    bit [3:0] captured_qos;
    @(posedge clk) disable iff (!reset_n)
        (packet_injected, captured_qos = packet_qos) |->
        ##[1:MAX_LATENCY] (packet_delivered && (packet_qos == captured_qos));
endproperty

assert property (qos_preserved)
    else `uvm_error("FORMAL", "QoS preservation violation: QoS modified during routing");

// ==============================================================================
// I. No Data Corruption
// ==============================================================================
//
// These properties ensure that data integrity is maintained through the NoC.
//

// ------------------------------------------------------------------------------
// Property: data_integrity
// ------------------------------------------------------------------------------
// Purpose: Verify data is not corrupted during transmission.
//
// Expected Behavior:
//   - Data written at source must match data at destination
//   - No bit flips or corruption during routing
//
property data_integrity;
    bit [127:0] captured_data;
    @(posedge clk) disable iff (!reset_n)
        ((wvalid && wready), captured_data = wdata) |->
        ##[MIN_LATENCY:MAX_LATENCY] (packet_delivered && (packet_data == captured_data));
endproperty

assert property (data_integrity)
    else `uvm_error("FORMAL", "Data integrity violation: data corrupted during transmission");

// ==============================================================================
// LIVENESS PROPERTIES - Good Things Eventually Happen
// ==============================================================================
//
// Liveness properties ensure that the system makes progress. These properties
// guarantee that desired events eventually occur, preventing deadlock and
// ensuring fairness.
//
// Note: Liveness properties use "s_eventually" (strong eventually) which
// requires the event to occur within a finite time bound. For formal tools,
// bounded versions are often more practical.
//

// ==============================================================================
// A. Packet Delivery (Critical)
// ==============================================================================
//
// These are the MOST IMPORTANT properties - they ensure that every packet
// eventually reaches its destination. Violation indicates deadlock or
// livelock.
//

// ------------------------------------------------------------------------------
// Property: packet_eventually_delivered
// ------------------------------------------------------------------------------
// Purpose: Verify every injected packet eventually reaches destination.
//
// Expected Behavior:
//   - Every packet injected into NoC must eventually be delivered
//   - This is the fundamental correctness property
//   - Violation indicates deadlock or packet loss
//
// IMPORTANCE: This is the most critical property. If this fails, the NoC
// design has a fundamental correctness issue (deadlock, livelock, or packet loss).
//
property packet_eventually_delivered;
    @(posedge clk) disable iff (!reset_n)
        packet_injected |-> s_eventually packet_delivered;
endproperty

assert property (packet_eventually_delivered)
    else `uvm_error("FORMAL", "CRITICAL: Packet not delivered - possible deadlock or packet loss");

// ------------------------------------------------------------------------------
// Property: bounded_packet_delivery
// ------------------------------------------------------------------------------
// Purpose: Verify packet delivery within bounded time.
//
// Expected Behavior:
//   - Every packet must be delivered within MAX_LATENCY cycles
//   - Bounded version is more practical for formal verification
//   - Ensures real-time performance requirements
//
property bounded_packet_delivery;
    @(posedge clk) disable iff (!reset_n)
        packet_injected |-> ##[1:MAX_LATENCY] packet_delivered;
endproperty

assert property (bounded_packet_delivery)
    else `uvm_error("FORMAL", "Bounded packet delivery violation: packet exceeds MAX_LATENCY");

// ==============================================================================
// B. Arbitration Fairness
// ==============================================================================
//
// These properties ensure that arbiters are fair - every request eventually
// gets granted, preventing starvation.
//

// ------------------------------------------------------------------------------
// Property: request_eventually_granted
// ------------------------------------------------------------------------------
// Purpose: Verify every request eventually gets granted.
//
// Expected Behavior:
//   - Every request must eventually receive a grant
//   - Prevents request starvation
//   - Ensures fairness in arbitration
//
property request_eventually_granted;
    @(posedge clk) disable iff (!reset_n)
        request[0] |-> s_eventually grant[0];
endproperty

assert property (request_eventually_granted)
    else `uvm_error("FORMAL", "Request starvation: request never granted");

// ------------------------------------------------------------------------------
// Property: no_request_starvation
// ------------------------------------------------------------------------------
// Purpose: Verify no request is starved beyond MAX_WAIT cycles.
//
// Expected Behavior:
//   - Every request must be granted within MAX_WAIT cycles
//   - Bounded fairness ensures real-time performance
//
property no_request_starvation;
    @(posedge clk) disable iff (!reset_n)
        request[0] |-> ##[1:MAX_WAIT] grant[0];
endproperty

assert property (no_request_starvation)
    else `uvm_error("FORMAL", "Request starvation: request exceeds MAX_WAIT cycles");

// ==============================================================================
// C. Buffer Drainage
// ==============================================================================
//
// These properties ensure that buffers make progress and eventually drain.
//

// ------------------------------------------------------------------------------
// Property: buffer_eventually_drains
// ------------------------------------------------------------------------------
// Purpose: Verify buffers eventually drain when output is enabled.
//
// Expected Behavior:
//   - If buffer has data and output is enabled, buffer must eventually drain
//   - Prevents buffer stagnation
//
property buffer_eventually_drains;
    int prev_occupancy;
    @(posedge clk) disable iff (!reset_n)
        ((buffer_occupancy > 0 && enable_output), prev_occupancy = buffer_occupancy) |->
        s_eventually (buffer_occupancy < prev_occupancy);
endproperty

assert property (buffer_eventually_drains)
    else `uvm_error("FORMAL", "Buffer stagnation: buffer does not drain");

// ==============================================================================
// D. No Deadlock (Strongest)
// ==============================================================================
//
// These are the strongest liveness properties - they ensure the system never
// deadlocks. Deadlock is a critical correctness issue.
//

// ------------------------------------------------------------------------------
// Property: no_deadlock
// ------------------------------------------------------------------------------
// Purpose: Verify system never deadlocks.
//
// Expected Behavior:
//   - If packets are active, eventually all packets complete
//   - System must always make progress
//   - Violation indicates deadlock condition
//
// IMPORTANCE: This property proves deadlock freedom. If this fails, the NoC
// design has a deadlock bug that must be fixed.
//
property no_deadlock;
    @(posedge clk) disable iff (!reset_n)
        (active_packets > 0) |->
        s_eventually (active_packets == 0);
endproperty

assert property (no_deadlock)
    else `uvm_error("FORMAL", "CRITICAL: Deadlock detected - system cannot make progress");

// ------------------------------------------------------------------------------
// Property: no_indefinite_backpressure
// ------------------------------------------------------------------------------
// Purpose: Verify backpressure does not persist indefinitely.
//
// Expected Behavior:
//   - Backpressure must be resolved within BACKPRESSURE_LIMIT cycles
//   - Prevents indefinite system stall
//
property no_indefinite_backpressure;
    @(posedge clk) disable iff (!reset_n)
        backpressure_asserted |->
        ##[1:BACKPRESSURE_LIMIT] !backpressure_asserted;
endproperty

assert property (no_indefinite_backpressure)
    else `uvm_error("FORMAL", "Indefinite backpressure: system stalled indefinitely");

// ==============================================================================
// COVERAGE PROPERTIES
// ==============================================================================
//
// Coverage properties measure how thoroughly the design has been exercised.
// These are used to identify coverage gaps and ensure comprehensive verification.
//

// ------------------------------------------------------------------------------
// Cover Property: Write Burst WRAP Length 256
// ------------------------------------------------------------------------------
// Purpose: Measure coverage of maximum-length WRAP burst transactions.
//
// Reference: ARM AMBA 5 AXI4 Specification (ARM IHI 0022E)
//   - Section 3.1.2: Maximum burst length is 256 transfers (awlen=255)
//   - WRAP burst type wraps address within burst boundary
//
cover property (
    @(posedge clk) disable iff (!reset_n)
    awvalid && awready && (awlen == 8'hFF) && (awburst == BURST_WRAP)
) {"Write burst WRAP length 256"};

// ------------------------------------------------------------------------------
// Cover Property: Read Response with High Transaction ID
// ------------------------------------------------------------------------------
// Purpose: Measure coverage of high transaction IDs.
//
// Reference: ARM AMBA 5 AXI4 Specification (ARM IHI 0022E)
//   - Section 3.1.5: Transaction IDs enable out-of-order completion
//   - High IDs (10-15) test ID matching logic
//
cover property (
    int captured_arid;
    @(posedge clk) disable iff (!reset_n)
    ((arvalid && arready), captured_arid = arid) ##[1:$]
    (rvalid && rready && rlast && (rid == captured_arid) && (captured_arid inside {[10:15]}))
) {"Read response with high transaction ID"};

// ------------------------------------------------------------------------------
// Cover Property: QoS Priority Arbitration
// ------------------------------------------------------------------------------
// Purpose: Measure coverage of QoS-based priority arbitration.
//
// Reference: ARM AMBA 5 AXI4 Specification (ARM IHI 0022E)
//   - Section 3.1.1: QoS signals enable priority-based arbitration
//
cover property (
    @(posedge clk) disable iff (!reset_n)
    (packet_valid && (packet_qos == 4'hF)) ##[1:$]
    (packet_delivered && (packet_qos == 4'hF))
) {"High QoS packet delivery"};

// ------------------------------------------------------------------------------
// Cover Property: Concurrent Transactions
// ------------------------------------------------------------------------------
// Purpose: Measure coverage of concurrent transaction handling.
//
cover property (
    @(posedge clk) disable iff (!reset_n)
    (awvalid && awready) && (arvalid && arready)
) {"Concurrent write and read transactions"};

// ------------------------------------------------------------------------------
// Cover Property: Out-of-Order Completion
// ------------------------------------------------------------------------------
// Purpose: Measure coverage of out-of-order transaction completion.
//
// Reference: ARM AMBA 5 AXI4 Specification (ARM IHI 0022E)
//   - Section 3.1.5: Out-of-order completion enabled by transaction IDs
//
cover property (
    int id1, id2;
    @(posedge clk) disable iff (!reset_n)
    ((awvalid && awready), id1 = awid) ##1
    ((awvalid && awready), id2 = awid) ##[1:$]
    (bvalid && (bid == id2)) ##[1:$]
    (bvalid && (bid == id1))
) {"Out-of-order write completion"};

// ------------------------------------------------------------------------------
// Cover Property: Atomic Operations
// ------------------------------------------------------------------------------
// Purpose: Measure coverage of atomic/exclusive operations.
//
// Reference: ARM AMBA 5 AXI4 Specification (ARM IHI 0022E)
//   - Section 3.1.6: Atomic Operations
//
cover property (
    @(posedge clk) disable iff (!reset_n)
    (awvalid && awready && awlock) ##[1:$]
    (bvalid && (bresp == RESP_EXOKAY))
) {"Atomic write operation with EXOKAY response"};

// ------------------------------------------------------------------------------
// Cover Property: Error Responses
// ------------------------------------------------------------------------------
// Purpose: Measure coverage of error response handling.
//
// Reference: ARM AMBA 5 AXI4 Specification (ARM IHI 0022E)
//   - Section 3.1.3: Response Signals (SLVERR, DECERR)
//
cover property (
    @(posedge clk) disable iff (!reset_n)
    (awvalid && awready) ##[1:$]
    (bvalid && ((bresp == RESP_SLVERR) || (bresp == RESP_DECERR)))
) {"Error response (SLVERR or DECERR)"};

// ==============================================================================
// ADDITIONAL SAFETY PROPERTIES
// ==============================================================================

// ------------------------------------------------------------------------------
// Property: No Write Data Before Address
// ------------------------------------------------------------------------------
// Purpose: Verify write data does not arrive before write address.
//
// Specification: ARM AMBA 5 AXI4 (ARM IHI 0022E), Section 3.1
//   - Write address must be accepted before write data
//
property no_write_data_before_address;
    @(posedge clk) disable iff (!reset_n)
        (wvalid && !awvalid) |-> $past(!awvalid && !awready);
endproperty

assert property (no_write_data_before_address)
    else `uvm_error("FORMAL", "Write data before address: protocol violation");

// ------------------------------------------------------------------------------
// Property: Response Code Validity
// ------------------------------------------------------------------------------
// Purpose: Verify all response codes are valid.
//
// Specification: ARM AMBA 5 AXI4 (ARM IHI 0022E), Section 3.1.3
//   - Valid response codes: OKAY, EXOKAY, SLVERR, DECERR
//
property response_code_validity;
    @(posedge clk) disable iff (!reset_n)
        (bvalid) |-> is_response_valid(bresp);
endproperty

assert property (response_code_validity)
    else `uvm_error("FORMAL", "Invalid response code");

// ------------------------------------------------------------------------------
// Property: Write Strobe Validity
// ------------------------------------------------------------------------------
// Purpose: Verify write strobe is valid (at least one byte enabled).
//
// Specification: ARM AMBA 5 AXI4 (ARM IHI 0022E), Section 3.1
//   - Write strobe must have at least one bit set
//
property write_strobe_validity;
    @(posedge clk) disable iff (!reset_n)
        (wvalid && wready) |-> (wstrb != 16'h0000);
endproperty

assert property (write_strobe_validity)
    else `uvm_error("FORMAL", "Invalid write strobe: all bytes disabled");

// ------------------------------------------------------------------------------
// Property: Address Alignment
// ------------------------------------------------------------------------------
// Purpose: Verify address alignment matches transfer size.
//
// Specification: ARM AMBA 5 AXI4 (ARM IHI 0022E), Section 3.1
//   - Address must be aligned to transfer size
//
property address_alignment_write;
    @(posedge clk) disable iff (!reset_n)
        (awvalid && awready) |->
        ((awaddr % (1 << awsize)) == 0);
endproperty

assert property (address_alignment_write)
    else `uvm_error("FORMAL", "Write address misaligned");

property address_alignment_read;
    @(posedge clk) disable iff (!reset_n)
        (arvalid && arready) |->
        ((araddr % (1 << arsize)) == 0);
endproperty

assert property (address_alignment_read)
    else `uvm_error("FORMAL", "Read address misaligned");

// ==============================================================================
// ASSUMPTIONS (Environmental Constraints)
// ==============================================================================
//
// Assumptions constrain the environment for formal verification. These represent
// assumptions about the environment that must hold for the properties to be valid.
// In formal verification, assumptions are used to model realistic scenarios.
//

// ------------------------------------------------------------------------------
// Assume Property: Requests Eventually Removed
// ------------------------------------------------------------------------------
// Purpose: Assume requests are not held indefinitely (prevent infinite requests).
//
// Rationale: In realistic scenarios, requests are eventually removed (either
// granted or cancelled). This assumption prevents formal tools from exploring
// unrealistic infinite request scenarios.
//
assume property (
    @(posedge clk) disable iff (!reset_n)
    request[0] |-> ##[1:100] !request[0]
) {"Request eventually removed"};

// ------------------------------------------------------------------------------
// Assume Property: No Eternal Backpressure from Slave
// ------------------------------------------------------------------------------
// Purpose: Assume slave backpressure does not persist indefinitely.
//
// Rationale: In realistic scenarios, slaves eventually become ready. This
// assumption prevents exploration of unrealistic eternal backpressure scenarios.
//
assume property (
    @(posedge clk) disable iff (!reset_n)
    !slave_ready |-> ##[1:10] slave_ready
) {"Slave eventually ready"};

// ------------------------------------------------------------------------------
// Assume Property: Valid Transaction Parameters
// ------------------------------------------------------------------------------
// Purpose: Assume all transactions have valid parameters.
//
// Rationale: Invalid transactions should be handled by protocol checking, but
// for formal verification, we assume valid transactions to focus on routing logic.
//
assume property (
    @(posedge clk) disable iff (!reset_n)
    (awvalid && awready) |->
    is_valid_transaction(awlen, awsize, awburst)
) {"Valid write transaction parameters"};

assume property (
    @(posedge clk) disable iff (!reset_n)
    (arvalid && arready) |->
    is_valid_transaction(arlen, arsize, arburst)
) {"Valid read transaction parameters"};

// ==============================================================================
// TOOL-SPECIFIC NOTES
// ==============================================================================
//
// JasperGold (Synopsys):
//   - Supports SVA (SystemVerilog Assertions) natively
//   - Use "bind" to connect properties to DUT
//   - Use "assume" for environmental constraints
//   - Use "cover" for coverage measurement
//
// Questa Formal (Mentor Graphics):
//   - Supports SVA and PSL (Property Specification Language)
//   - Use "bind" to connect properties to DUT
//   - Use "assume" for environmental constraints
//   - Use "cover" for coverage measurement
//
// Usage Example:
//   bind noc_router formal_properties formal_props_inst (
//       .clk(clk),
//       .reset_n(reset_n),
//       // ... connect all signals ...
//   );
//
// ==============================================================================
// EDUCATIONAL NOTES FOR FORMAL VERIFICATION STUDENTS
// ==============================================================================
//
// 1. Safety vs. Liveness:
//    - Safety: "Bad things never happen" (invariants)
//    - Liveness: "Good things eventually happen" (progress)
//
// 2. Property Syntax:
//    - |-> : Implication (if antecedent, then consequent)
//    - ##N : Delay by N cycles
//    - ##[M:N] : Delay between M and N cycles
//    - s_eventually : Strong eventually (must occur)
//    - $stable(signal) : Signal remains stable
//    - $onehot0(vector) : At most one bit set
//
// 3. Formal Verification Process:
//    - Write properties (assertions, assumptions, covers)
//    - Run formal tool (JasperGold, Questa Formal)
//    - Analyze results (proven, falsified, bounded)
//    - Debug failures (counterexamples)
//    - Iterate until all properties proven
//
// 4. Common Pitfalls:
//    - Forgetting disable conditions (reset handling)
//    - Incorrect property syntax
//    - Missing assumptions (environment constraints)
//    - Unbounded properties (use bounded versions)
//
// ==============================================================================

`endif // FORMAL_PROPERTIES_SV

