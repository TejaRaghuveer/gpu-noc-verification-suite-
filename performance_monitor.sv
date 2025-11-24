//=============================================================================
// File: performance_monitor.sv
// Description: Comprehensive performance monitoring for GPU interconnect NoC
//              verification. Tracks latency, throughput, utilization, traffic
//              patterns, contention, QoS impact, and deadlock risk.
// Author: NVIDIA GPU Interconnect NoC Verification Team
// Date: January 2025
//
// Note: This monitor requires the following interface signals to be available
//       in noc_if (adapt as needed for your specific interface):
//       - vif.router_active[i] : bit array indicating router activity
//       - vif.link_transmitting[i] : bit array indicating link transmission
//       - vif.buffer_depth[i] : int array indicating buffer occupancy
//       - vif.clk, vif.reset_n : clock and reset signals
//=============================================================================

`ifndef PERFORMANCE_MONITOR_SV
`define PERFORMANCE_MONITOR_SV

`include "uvm_macros.svh"
import uvm_pkg::*;

// Note: axi_transaction class should be included before this file
// or via package includes. This monitor expects axi_transaction to be defined.

//=============================================================================
// Class: noc_performance_monitor
// Description: Comprehensive performance monitoring component for GPU NoC
//              verification. Collects latency, throughput, utilization,
//              traffic pattern, contention, and QoS metrics.
//
// Key Features:
//   - Latency tracking with percentiles (p50, p95, p99, p999)
//   - Throughput measurement (actual vs. theoretical)
//   - Router and link utilization analysis
//   - Buffer occupancy monitoring
//   - Traffic pattern analysis (source-destination matrix)
//   - Contention and fairness metrics
//   - QoS impact analysis
//   - Deadlock risk detection
//
// Usage:
//   - Instantiate in testbench environment
//   - Connect to transaction analysis ports
//   - Automatically collects metrics during simulation
//   - Generates comprehensive reports in report_phase
//=============================================================================
class noc_performance_monitor extends uvm_monitor;

  `uvm_component_utils(noc_performance_monitor)

  //===========================================================================
  // Virtual Interface
  //===========================================================================
  virtual noc_if vif;  // NoC interface for cycle-level monitoring

  //===========================================================================
  // Configuration
  //===========================================================================
  noc_config cfg;  // NoC configuration (topology, router count, etc.)

  // Clock and reset
  bit clk;
  bit reset_n;

  //===========================================================================
  // Latency Tracking
  //===========================================================================
  //
  // Latency Definition:
  //   Latency = (packet_delivery_time - packet_injection_time) / clock_period
  //   Measured in clock cycles
  //
  // GPU Performance Standards:
  //   - Average latency: <50 cycles (typical GPU NoC target)
  //   - p95 latency: <100 cycles (95% of packets within 100 cycles)
  //   - p99 latency: <150 cycles (99% of packets within 150 cycles)
  //   - Frame-critical traffic (QoS 15): <30 cycles average
  //
  // Latency Components:
  //   1. Router processing delay (arbitration, routing decision)
  //   2. Link traversal delay (propagation through links)
  //   3. Buffer queuing delay (waiting in input buffers)
  //   4. Contention delay (waiting for port arbitration)
  //
  // Reference: NVIDIA GPU Architecture Whitepapers, ARM AMBA AXI4 Spec
  //===========================================================================
  
  // Latency histogram: maps latency cycles -> packet count
  // Used for: Latency distribution analysis, percentile calculation
  // Example: latency_histogram[50] = 1000 means 1000 packets had 50-cycle latency
  int latency_histogram[int];
  
  // Aggregate latency metrics
  longint total_latency;      // Sum of all latencies (for average calculation)
  int min_latency;            // Minimum observed latency (best case)
  int max_latency;            // Maximum observed latency (worst case)
  real avg_latency;           // Average latency = total_latency / total_packets
  int total_packets;          // Total packets delivered
  
  // Latency percentiles
  // Percentile definition: pX = latency value below which X% of packets fall
  // Key: percentile value (50, 95, 99, 999) -> latency in cycles
  // p50 = median latency (50% of packets below this value)
  // p95 = 95th percentile (95% of packets below this value, important for SLA)
  // p99 = 99th percentile (tail latency, critical for worst-case analysis)
  // p999 = 99.9th percentile (extreme tail, used for outlier detection)
  int latency_percentile[int];
  
  // Latency per QoS level: QoS[0-15] -> latency histogram
  // Purpose: Analyze QoS impact on latency
  // Example: latency_per_qos[15][30] = 500 means 500 QoS15 packets had 30-cycle latency
  int latency_per_qos[int][int];
  
  // Latency per hop count: hop_count -> latency histogram
  // Purpose: Analyze relationship between distance and latency
  // Hop count = Manhattan distance (|dx| + |dy|) in mesh topology
  // Expected: latency increases linearly with hop count
  int latency_per_hop_count[int][int];
  
  // Pending packets for latency calculation
  typedef struct {
    axi_transaction tr;
    longint injection_time;
    int source_id;
    int dest_id;
    int qos_level;
    int hop_count;  // Manhattan distance
  } pending_packet_t;
  
  pending_packet_t pending_packets[$];
  
  // All collected latencies for percentile calculation
  int all_latencies[$];

  //===========================================================================
  // Throughput Tracking
  //===========================================================================
  //
  // Throughput Definition:
  //   Throughput = (flits_delivered / total_cycles) * flit_width * frequency
  //   Measured in: Gbps (Gigabits per second) or flits/cycle
  //
  // Theoretical Throughput:
  //   theoretical = num_links * flit_width * frequency
  //   For 4x4 mesh: 16 routers * 4 links/router * 128 bits/flit * 1 GHz = 8.192 Tbps
  //
  // Actual Throughput:
  //   Limited by: contention, routing inefficiency, buffer backpressure
  //   Typical GPU NoC: 60-80% of theoretical (due to contention and routing overhead)
  //
  // Throughput Metrics:
  //   - Peak Throughput: Maximum throughput in any 1K-cycle window
  //   - Sustained Throughput: Average throughput over long period (100K+ cycles)
  //   - Throughput Efficiency: (actual / theoretical) * 100%
  //
  // GPU Performance Standards:
  //   - Sustained throughput: >70% of theoretical (for balanced workloads)
  //   - Peak throughput: >85% of theoretical (burst capability)
  //
  // Reference: IEEE 802.1Q (QoS), GPU Interconnect Performance Analysis
  //===========================================================================
  
  longint total_flits_delivered;      // Total flits (flow control units) delivered
  longint total_cycles;               // Total simulation cycles
  longint flits_delivered_last_period; // For sliding window calculation
  
  real throughput_percent;      // Actual throughput / theoretical * 100
  real peak_throughput;         // Peak throughput in any 1K-cycle window (flits/cycle)
  real sustained_throughput;    // Average throughput over long window (100K cycles)
  
  // Throughput measurement windows
  longint window_start_cycle;
  longint window_flits;
  real window_throughput[1000];  // Sliding window measurements
  int window_index;

  //===========================================================================
  // Utilization Tracking
  //===========================================================================
  
  // Per-link utilization: link_id -> fraction of cycles used
  real per_link_utilization[int];
  int link_active_cycles[int];
  
  // Per-router utilization: router_id -> activity percentage
  real per_router_utilization[int];
  int router_active_cycles[int];
  
  // Buffer occupancy tracking
  real average_buffer_occupancy[int];  // router_id -> avg depth
  int buffer_occupancy_histogram[int][int];  // router_id -> depth -> count
  longint buffer_occupancy_sum[int];
  int buffer_max_depth[int];

  //===========================================================================
  // Traffic Pattern Tracking
  //===========================================================================
  
  // Source-destination matrix: source_id -> dest_id -> packet count
  int source_destination_matrix[int][int];
  
  int total_traffic_packets;
  real traffic_concentration;  // % of traffic to top 10% destinations
  real hotspot_latency_impact;  // Latency increase at hot destinations
  
  // Hotspot detection
  int hotspot_destinations[$];  // Top 10% destinations by traffic
  int hotspot_packet_count[int];
  real hotspot_avg_latency[int];
  real non_hotspot_avg_latency;

  //===========================================================================
  // Contention Tracking
  //===========================================================================
  
  int collision_count;              // Total port arbitration collisions
  longint collision_latency_impact; // Extra cycles due to collisions
  real fairness_ratio;             // max_latency_master / min_latency_master
  
  // Per-master latency tracking for fairness
  int master_latency_sum[int];
  int master_packet_count[int];
  real master_avg_latency[int];

  //===========================================================================
  // QoS Impact Tracking
  //===========================================================================
  
  real qos_priority_gap;        // Latency ratio (QoS15 / QoS0)
  int qos_sla_violations;      // Transactions exceeding QoS threshold
  real qos_fairness;           // Min latency gap between QoS levels
  
  // QoS latency statistics
  real qos_avg_latency[int];   // QoS level -> average latency
  int qos_packet_count[int];   // QoS level -> packet count
  int qos_sla_threshold[int];   // QoS level -> SLA threshold (cycles)

  //===========================================================================
  // Deadlock Risk Detection
  //===========================================================================
  
  int cycles_without_progress;
  int max_no_progress_cycles;
  bit deadlock_detected;
  
  longint last_progress_cycle;
  longint last_packet_count;

  //===========================================================================
  // Analysis Ports
  //===========================================================================
  
  uvm_analysis_imp #(axi_transaction, noc_performance_monitor) input_analysis_imp;
  uvm_analysis_imp #(axi_transaction, noc_performance_monitor) output_analysis_imp;

  //===========================================================================
  // Constructor
  //===========================================================================
  function new(string name = "noc_performance_monitor", uvm_component parent = null);
    super.new(name, parent);
    
    // Initialize analysis ports
    input_analysis_imp = new("input_analysis_imp", this);
    output_analysis_imp = new("output_analysis_imp", this);
    
    // Initialize metrics
    total_latency = 0;
    total_packets = 0;
    min_latency = '1;  // Maximum int
    max_latency = 0;
    total_flits_delivered = 0;
    total_cycles = 0;
    collision_count = 0;
    qos_sla_violations = 0;
    cycles_without_progress = 0;
    deadlock_detected = 0;
    max_no_progress_cycles = 10000;  // 10K cycles without progress = deadlock
    
    // Initialize QoS SLA thresholds (cycles)
    for (int i = 0; i < 16; i++) begin
      qos_sla_threshold[i] = 50 + (15 - i) * 5;  // Higher QoS = stricter SLA
    end
    
    window_index = 0;
    window_start_cycle = 0;
  endfunction

  //===========================================================================
  // Build Phase
  //===========================================================================
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    
    // Get virtual interface from ConfigDB
    if (!uvm_config_db#(virtual noc_if)::get(this, "", "noc_vif", vif)) begin
      `uvm_fatal("NOC_VIF", "NoC virtual interface not found in ConfigDB")
    end
    
    // Get configuration object
    if (!uvm_config_db#(noc_config)::get(this, "", "noc_config", cfg)) begin
      `uvm_fatal("NOC_CFG", "NoC configuration not found in ConfigDB")
    end
    
    `uvm_info("BUILD", $sformatf("Performance monitor built for %dx%d mesh", 
                                  cfg.mesh_size_x, cfg.mesh_size_y), UVM_LOW)
  endfunction

  //===========================================================================
  // Run Phase
  //===========================================================================
  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    
    `uvm_info("RUN", "Starting performance monitoring", UVM_LOW)
    
    // Wait for reset release
    wait(vif.reset_n == 1'b1);
    @(posedge vif.clk);
    
    // Fork background monitoring tasks
    fork
      collect_latency_measurements();
      collect_throughput_measurements();
      collect_utilization_measurements();
      monitor_deadlock_risk();
      periodic_status_report();
    join_none
    
    `uvm_info("RUN", "Performance monitoring tasks started", UVM_LOW)
  endtask

  //===========================================================================
  // Analysis Port Write Methods
  //===========================================================================
  
  // Called when transaction injected into NoC
  function void write_input(axi_transaction tr);
    record_packet_injection(tr);
  endfunction
  
  // Called when transaction delivered from NoC
  function void write_output(axi_transaction tr);
    record_packet_delivery(tr);
  endfunction

  //===========================================================================
  // Latency Measurement Methods
  //===========================================================================
  
  // Record packet injection with timestamp
  function void record_packet_injection(axi_transaction tr);
    pending_packet_t pkt;
    
    pkt.tr = tr;
    pkt.injection_time = $time;
    pkt.source_id = tr.source_id;
    pkt.dest_id = tr.dest_id;
    pkt.qos_level = tr.awqos;  // Use write QoS (same for read)
    if (tr.trans_type == READ) begin
      pkt.qos_level = tr.arqos;
    end
    
    // Calculate Manhattan distance (hop count)
    int source_x = pkt.source_id % cfg.mesh_size_x;
    int source_y = pkt.source_id / cfg.mesh_size_x;
    int dest_x = pkt.dest_id % cfg.mesh_size_x;
    int dest_y = pkt.dest_id / cfg.mesh_size_x;
    pkt.hop_count = (dest_x > source_x ? dest_x - source_x : source_x - dest_x) +
                    (dest_y > source_y ? dest_y - source_y : source_y - dest_y);
    
    pending_packets.push_back(pkt);
    
    // Update traffic pattern matrix
    if (!source_destination_matrix.exists(pkt.source_id)) begin
      source_destination_matrix[pkt.source_id] = '{default: 0};
    end
    source_destination_matrix[pkt.source_id][pkt.dest_id]++;
    total_traffic_packets++;
    
    `uvm_info("LATENCY", $sformatf("Packet injected: src=%0d, dst=%0d, hops=%0d, QoS=%0d",
                                    pkt.source_id, pkt.dest_id, pkt.hop_count, pkt.qos_level),
              UVM_DEBUG)
  endfunction
  
  // Record packet delivery and calculate latency
  function void record_packet_delivery(axi_transaction tr);
    int latency;
    int qos_level;
    int hop_count;
    int source_id, dest_id;
    bit found = 0;
    
    // Find matching pending packet
    // Match by transaction ID and address
    for (int i = 0; i < pending_packets.size(); i++) begin
      if (pending_packets[i].tr.awid == tr.awid || 
          pending_packets[i].tr.arid == tr.arid) begin
        // Match found
        latency = ($time - pending_packets[i].injection_time) / cfg.clock_period;
        qos_level = pending_packets[i].qos_level;
        hop_count = pending_packets[i].hop_count;
        source_id = pending_packets[i].source_id;
        dest_id = pending_packets[i].dest_id;
        
        // Update latency histogram
        if (!latency_histogram.exists(latency)) begin
          latency_histogram[latency] = 0;
        end
        latency_histogram[latency]++;
        
        // Update aggregate metrics
        total_latency += latency;
        total_packets++;
        if (latency < min_latency) min_latency = latency;
        if (latency > max_latency) max_latency = latency;
        
        // Store for percentile calculation
        all_latencies.push_back(latency);
        
        // Update per-QoS latency
        if (!latency_per_qos.exists(qos_level)) begin
          latency_per_qos[qos_level] = '{default: 0};
        end
        if (!latency_per_qos[qos_level].exists(latency)) begin
          latency_per_qos[qos_level][latency] = 0;
        end
        latency_per_qos[qos_level][latency]++;
        
        // Update per-hop-count latency
        if (!latency_per_hop_count.exists(hop_count)) begin
          latency_per_hop_count[hop_count] = '{default: 0};
        end
        if (!latency_per_hop_count[hop_count].exists(latency)) begin
          latency_per_hop_count[hop_count][latency] = 0;
        end
        latency_per_hop_count[hop_count][latency]++;
        
        // Update QoS statistics
        if (!qos_avg_latency.exists(qos_level)) begin
          qos_avg_latency[qos_level] = 0.0;
          qos_packet_count[qos_level] = 0;
        end
        qos_avg_latency[qos_level] = (qos_avg_latency[qos_level] * qos_packet_count[qos_level] + latency) /
                                      (qos_packet_count[qos_level] + 1);
        qos_packet_count[qos_level]++;
        
        // Check QoS SLA violation
        if (latency > qos_sla_threshold[qos_level]) begin
          qos_sla_violations++;
          `uvm_warning("QOS_SLA", $sformatf("QoS %0d SLA violation: latency=%0d, threshold=%0d",
                                            qos_level, latency, qos_sla_threshold[qos_level]))
        end
        
        // Update master latency for fairness
        if (!master_avg_latency.exists(source_id)) begin
          master_avg_latency[source_id] = 0.0;
          master_packet_count[source_id] = 0;
          master_latency_sum[source_id] = 0;
        end
        master_latency_sum[source_id] += latency;
        master_packet_count[source_id]++;
        master_avg_latency[source_id] = real'(master_latency_sum[source_id]) / master_packet_count[source_id];
        
        // Update hotspot latency
        if (hotspot_packet_count.exists(dest_id)) begin
          if (!hotspot_avg_latency.exists(dest_id)) begin
            hotspot_avg_latency[dest_id] = 0.0;
            hotspot_packet_count[dest_id] = 0;
          end
          hotspot_avg_latency[dest_id] = (hotspot_avg_latency[dest_id] * hotspot_packet_count[dest_id] + latency) /
                                          (hotspot_packet_count[dest_id] + 1);
          hotspot_packet_count[dest_id]++;
        end
        
        // Remove from pending
        pending_packets.delete(i);
        found = 1;
        break;
      end
    end
    
    if (!found) begin
      `uvm_warning("LATENCY", $sformatf("Packet delivery without matching injection: ID=%0d",
                                        tr.awid | tr.arid))
    end else begin
      `uvm_info("LATENCY", $sformatf("Packet delivered: latency=%0d cycles, QoS=%0d, hops=%0d",
                                      latency, qos_level, hop_count), UVM_DEBUG)
    end
    
    // Update throughput
    total_flits_delivered += (tr.awlen + 1);  // Burst length + 1
    if (tr.trans_type == READ) begin
      total_flits_delivered += (tr.arlen + 1);
    end
  endfunction
  
  // Calculate latency percentiles
  function void calculate_latency_percentiles();
    int sorted_latencies[$];
    int index;
    
    if (all_latencies.size() == 0) begin
      `uvm_warning("PERCENTILE", "No latencies collected, cannot calculate percentiles")
      return;
    end
    
    // Sort latencies
    sorted_latencies = all_latencies;
    sorted_latencies.sort();
    
    // Calculate percentiles
    index = (sorted_latencies.size() * 50) / 100;
    latency_percentile[50] = sorted_latencies[index];
    
    index = (sorted_latencies.size() * 95) / 100;
    latency_percentile[95] = sorted_latencies[index];
    
    index = (sorted_latencies.size() * 99) / 100;
    latency_percentile[99] = sorted_latencies[index];
    
    index = (sorted_latencies.size() * 999) / 1000;
    latency_percentile[999] = sorted_latencies[index];
    
    `uvm_info("PERCENTILE", $sformatf("Latency percentiles: p50=%0d, p95=%0d, p99=%0d, p999=%0d",
                                       latency_percentile[50], latency_percentile[95],
                                       latency_percentile[99], latency_percentile[999]), UVM_MEDIUM)
  endfunction
  
  // Get latency at requested percentile
  function real get_latency_percentile(int percent);
    int sorted_latencies[$];
    int index;
    
    if (all_latencies.size() == 0) return 0.0;
    
    sorted_latencies = all_latencies;
    sorted_latencies.sort();
    
    index = (sorted_latencies.size() * percent) / 100;
    if (index >= sorted_latencies.size()) index = sorted_latencies.size() - 1;
    
    return real'(sorted_latencies[index]);
  endfunction

  //===========================================================================
  // Throughput Measurement
  //===========================================================================
  
  task automatic collect_throughput_measurements();
    longint cycle_count = 0;
    longint window_cycle_count = 0;
    longint last_window_flits = 0;
    
    forever @(posedge vif.clk) begin
      if (vif.reset_n == 1'b0) continue;
      
      total_cycles++;
      cycle_count++;
      window_cycle_count++;
      
      // Update sliding window throughput (every 1000 cycles)
      if (window_cycle_count >= 1000) begin
        real current_throughput;
        longint flits_in_window = total_flits_delivered - last_window_flits;
        
        current_throughput = real'(flits_in_window) / real'(window_cycle_count);
        window_throughput[window_index] = current_throughput;
        window_index = (window_index + 1) % 1000;
        
        // Update peak throughput
        if (current_throughput > peak_throughput) begin
          peak_throughput = current_throughput;
        end
        
        last_window_flits = total_flits_delivered;
        window_cycle_count = 0;
      end
      
      // Update sustained throughput (average of last 100 windows)
      if (cycle_count >= 100000) begin
        real sum = 0.0;
        int count = 0;
        for (int i = 0; i < 1000; i++) begin
          if (window_throughput[i] > 0) begin
            sum += window_throughput[i];
            count++;
          end
        end
        if (count > 0) begin
          sustained_throughput = sum / real'(count);
        end
        cycle_count = 0;
      end
    end
  endtask
  
  // Calculate throughput percentage (actual / theoretical)
  function real calculate_throughput_percentage();
    real theoretical_bandwidth;
    real actual_throughput;
    
    if (total_cycles == 0) return 0.0;
    
    // Theoretical bandwidth: num_links * flit_width * frequency
    // Assuming bidirectional links, mesh topology
    int num_links = cfg.mesh_size_x * cfg.mesh_size_y * 4;  // 4 directions per router
    int flit_width = cfg.data_width;  // Bits per flit
    real frequency = 1.0 / (cfg.clock_period * 1e-9);  // GHz
    
    theoretical_bandwidth = real'(num_links) * real'(flit_width) * frequency;  // Gbps
    
    // Actual throughput: flits delivered per cycle
    actual_throughput = (real'(total_flits_delivered) * real'(flit_width)) / 
                        (real'(total_cycles) * cfg.clock_period * 1e-9);  // Gbps
    
    throughput_percent = (actual_throughput / theoretical_bandwidth) * 100.0;
    
    return throughput_percent;
  endfunction
  
  // Calculate peak throughput in any 1K-cycle window
  function real calculate_peak_throughput();
    return peak_throughput;
  endfunction

  //===========================================================================
  // Router and Link Utilization
  //===========================================================================
  
  task automatic collect_utilization_measurements();
    forever @(posedge vif.clk) begin
      if (vif.reset_n == 1'b0) continue;
      
      // Track router utilization (simplified: if router processing any packet)
      // In real implementation, would sample router state from interface
      for (int i = 0; i < cfg.mesh_size_x * cfg.mesh_size_y; i++) begin
        // Check if router i is active (processing packets)
        // This is a placeholder - actual implementation would sample vif signals
        if (vif.router_active[i]) begin
          router_active_cycles[i]++;
        end
      end
      
      // Track link utilization
      for (int i = 0; i < cfg.num_links; i++) begin
        if (vif.link_transmitting[i]) begin
          link_active_cycles[i]++;
        end
      end
      
      // Track buffer occupancy
      track_buffer_occupancy();
    end
  endtask
  
  // Track router utilization percentage
  function void track_router_utilization();
    for (int i = 0; i < cfg.mesh_size_x * cfg.mesh_size_y; i++) begin
      if (total_cycles > 0) begin
        per_router_utilization[i] = real'(router_active_cycles[i]) / real'(total_cycles) * 100.0;
      end
    end
  endfunction
  
  // Track link utilization percentage
  function void track_link_utilization();
    for (int i = 0; i < cfg.num_links; i++) begin
      if (total_cycles > 0) begin
        per_link_utilization[i] = real'(link_active_cycles[i]) / real'(total_cycles) * 100.0;
      end
    end
  endfunction

  //===========================================================================
  // Buffer Monitoring
  //===========================================================================
  
  function void track_buffer_occupancy();
    // Sample buffer occupancy from interface
    // This is a placeholder - actual implementation would sample vif.buffer_depth[i]
    for (int i = 0; i < cfg.mesh_size_x * cfg.mesh_size_y; i++) begin
      int current_depth = vif.buffer_depth[i];  // Assume interface provides this
      
      buffer_occupancy_sum[i] += current_depth;
      
      if (!buffer_occupancy_histogram.exists(i)) begin
        buffer_occupancy_histogram[i] = '{default: 0};
      end
      if (!buffer_occupancy_histogram[i].exists(current_depth)) begin
        buffer_occupancy_histogram[i][current_depth] = 0;
      end
      buffer_occupancy_histogram[i][current_depth]++;
      
      if (current_depth > buffer_max_depth[i]) begin
        buffer_max_depth[i] = current_depth;
      end
      
      // Calculate average occupancy
      if (total_cycles > 0) begin
        average_buffer_occupancy[i] = real'(buffer_occupancy_sum[i]) / real'(total_cycles);
      end
      
      // Warning if buffer near capacity
      if (average_buffer_occupancy[i] > cfg.buffer_depth * 0.8) begin
        `uvm_warning("BUFFER", $sformatf("Router %0d buffer occupancy high: %.2f%% (depth=%0d)",
                                         i, average_buffer_occupancy[i] / cfg.buffer_depth * 100.0,
                                         cfg.buffer_depth))
      end
    end
  endfunction

  //===========================================================================
  // Deadlock Risk Detection
  //===========================================================================
  
  task automatic monitor_deadlock_risk();
    longint last_check_cycle = 0;
    longint last_packet_count_check = 0;
    
    forever @(posedge vif.clk) begin
      if (vif.reset_n == 1'b0) continue;
      
      // Check every 100 cycles
      if (($time / cfg.clock_period) - last_check_cycle >= 100) begin
        check_progress();
        last_check_cycle = $time / cfg.clock_period;
      end
      
      // Check for packets pending too long
      for (int i = 0; i < pending_packets.size(); i++) begin
        int pending_cycles = ($time - pending_packets[i].injection_time) / cfg.clock_period;
        if (pending_cycles > 1000) begin
          `uvm_error("DEADLOCK", $sformatf("Packet pending >1000 cycles: src=%0d, dst=%0d, cycles=%0d",
                                           pending_packets[i].source_id, pending_packets[i].dest_id,
                                           pending_cycles))
          deadlock_detected = 1;
        end
      end
      
      // Check if no packets delivered in last period
      if (pending_packets.size() > 0 && total_packets == last_packet_count_check) begin
        cycles_without_progress++;
        if (cycles_without_progress > max_no_progress_cycles) begin
          `uvm_error("DEADLOCK", $sformatf("No progress for %0d cycles - probable deadlock",
                                            cycles_without_progress))
          deadlock_detected = 1;
        end
      end else begin
        cycles_without_progress = 0;
      end
      
      last_packet_count_check = total_packets;
    end
  endtask
  
  // Check if system is making progress
  function void check_progress();
    longint current_packet_count = total_packets;
    longint current_cycle = $time / cfg.clock_period;
    
    if (current_packet_count == last_packet_count && pending_packets.size() > 0) begin
      cycles_without_progress++;
      if (cycles_without_progress > max_no_progress_cycles) begin
        `uvm_error("DEADLOCK", $sformatf("No progress detected: %0d cycles without packet delivery",
                                         cycles_without_progress))
        deadlock_detected = 1;
      end
    end else begin
      cycles_without_progress = 0;
      last_packet_count = current_packet_count;
      last_progress_cycle = current_cycle;
    end
  endfunction

  //===========================================================================
  // Traffic Pattern Analysis
  //===========================================================================
  
  function void analyze_traffic_patterns();
    int dest_counts[int];
    int sorted_dest_counts[$];
    int top_10_percent_count;
    int top_10_percent_packets = 0;
    
    // Count packets per destination
    foreach (source_destination_matrix[i]) begin
      foreach (source_destination_matrix[i][j]) begin
        if (!dest_counts.exists(j)) begin
          dest_counts[j] = 0;
        end
        dest_counts[j] += source_destination_matrix[i][j];
      end
    end
    
    // Sort destinations by packet count
    foreach (dest_counts[i]) begin
      sorted_dest_counts.push_back(dest_counts[i]);
    end
    sorted_dest_counts.sort();
    sorted_dest_counts.reverse();
    
    // Calculate top 10% destinations
    top_10_percent_count = (dest_counts.size() * 10) / 100;
    if (top_10_percent_count == 0) top_10_percent_count = 1;
    
    for (int i = 0; i < top_10_percent_count && i < sorted_dest_counts.size(); i++) begin
      top_10_percent_packets += sorted_dest_counts[i];
      hotspot_destinations.push_back(i);
    end
    
    // Calculate traffic concentration
    if (total_traffic_packets > 0) begin
      traffic_concentration = real'(top_10_percent_packets) / real'(total_traffic_packets) * 100.0;
    end
    
    // Calculate hotspot latency impact
    real hotspot_latency_sum = 0.0;
    int hotspot_latency_count = 0;
    real non_hotspot_latency_sum = 0.0;
    int non_hotspot_latency_count = 0;
    
    foreach (hotspot_avg_latency[i]) begin
      if (hotspot_packet_count[i] > 0) begin
        hotspot_latency_sum += hotspot_avg_latency[i];
        hotspot_latency_count++;
      end
    end
    
    if (hotspot_latency_count > 0) begin
      real avg_hotspot_latency = hotspot_latency_sum / real'(hotspot_latency_count);
      // Calculate non-hotspot average (simplified)
      if (total_packets > 0 && avg_latency > 0) begin
        hotspot_latency_impact = (avg_hotspot_latency - avg_latency) / avg_latency * 100.0;
      end
    end
  endfunction

  //===========================================================================
  // Contention and Fairness Analysis
  //===========================================================================
  
  function void analyze_fairness();
    real min_master_latency = 999999.0;
    real max_master_latency = 0.0;
    
    foreach (master_avg_latency[i]) begin
      if (master_avg_latency[i] < min_master_latency) begin
        min_master_latency = master_avg_latency[i];
      end
      if (master_avg_latency[i] > max_master_latency) begin
        max_master_latency = master_avg_latency[i];
      end
    end
    
    if (min_master_latency > 0) begin
      fairness_ratio = max_master_latency / min_master_latency;
    end
    
    `uvm_info("FAIRNESS", $sformatf("Fairness ratio: %.2f (min=%.2f, max=%.2f)",
                                    fairness_ratio, min_master_latency, max_master_latency), UVM_MEDIUM)
  endfunction

  //===========================================================================
  // QoS Impact Analysis
  //===========================================================================
  
  function void analyze_qos_impact();
    real qos0_avg = 0.0;
    real qos15_avg = 0.0;
    
    if (qos_avg_latency.exists(0) && qos_packet_count[0] > 0) begin
      qos0_avg = qos_avg_latency[0];
    end
    if (qos_avg_latency.exists(15) && qos_packet_count[15] > 0) begin
      qos15_avg = qos_avg_latency[15];
    end
    
    if (qos0_avg > 0) begin
      qos_priority_gap = qos15_avg / qos0_avg;
    end
    
    // Calculate QoS fairness (min gap between adjacent QoS levels)
    real min_gap = 999999.0;
    for (int i = 0; i < 15; i++) begin
      if (qos_avg_latency.exists(i) && qos_avg_latency.exists(i+1)) begin
        real gap = qos_avg_latency[i] - qos_avg_latency[i+1];
        if (gap >= 0 && gap < min_gap) begin
          min_gap = gap;
        end
      end
    end
    qos_fairness = min_gap;
    
    `uvm_info("QOS", $sformatf("QoS priority gap: %.2f (QoS15/QoS0), SLA violations: %0d",
                                qos_priority_gap, qos_sla_violations), UVM_MEDIUM)
  endfunction

  //===========================================================================
  // Periodic Status Report
  //===========================================================================
  
  task automatic periodic_status_report();
    forever begin
      #1000000;  // Every 1M cycles (adjust based on simulation time)
      
      if (total_packets > 0) begin
        avg_latency = real'(total_latency) / real'(total_packets);
        `uvm_info("STATUS", $sformatf("Performance Status: packets=%0d, avg_latency=%.2f, throughput=%.2f%%",
                                      total_packets, avg_latency, calculate_throughput_percentage()), UVM_LOW)
      end
    end
  endtask

  //===========================================================================
  // Statistical Analysis Functions
  //===========================================================================
  //
  // Purpose: Calculate statistical metrics for latency analysis
  //
  // Standard Deviation:
  //   - Measures spread/dispersion of latency values
  //   - Higher std dev = more variable latency (less predictable)
  //   - Formula: sqrt(sum((x_i - mean)^2) / N)
  //
  // Coefficient of Variation:
  //   - Normalized measure of variability (std_dev / mean)
  //   - Lower CoV = more consistent latency (better for real-time systems)
  //   - GPU Performance Standard: CoV < 0.3 (30%) for consistent frame timing
  //   - Ideal: CoV < 0.2 (20%) for graphics workloads
  //
  // Reference: IEEE 802.1Q (QoS), GPU Performance Analysis Best Practices
  //===========================================================================
  
  // Calculate standard deviation of latencies
  // Returns: sqrt(variance) where variance = E[(X - mean)^2]
  function real calculate_standard_deviation();
    real mean = 0.0;
    real variance = 0.0;
    int count = 0;
    
    if (all_latencies.size() == 0) begin
      `uvm_warning("STATS", "No latencies collected, cannot calculate standard deviation")
      return 0.0;
    end
    
    // Calculate mean
    foreach (all_latencies[i]) begin
      mean += real'(all_latencies[i]);
      count++;
    end
    if (count > 0) begin
      mean = mean / real'(count);
    end
    
    // Calculate variance
    foreach (all_latencies[i]) begin
      real diff = real'(all_latencies[i]) - mean;
      variance += diff * diff;
    end
    if (count > 0) begin
      variance = variance / real'(count);
    end
    
    // Return standard deviation
    return $sqrt(variance);
  endfunction
  
  // Calculate coefficient of variation
  // Returns: std_dev / avg_latency (normalized measure of variability)
  // Lower values = more consistent latency (better for real-time systems)
  function real calculate_coefficient_of_variation();
    real std_dev = calculate_standard_deviation();
    
    if (avg_latency <= 0) begin
      `uvm_warning("STATS", "Average latency is zero or negative, cannot calculate CoV")
      return 0.0;
    end
    
    // Coefficient of Variation = std_dev / mean
    // Expressed as percentage: (std_dev / mean) * 100
    return (std_dev / avg_latency);
  endfunction

  //===========================================================================
  // Report Phase
  //===========================================================================
  
  function void report_phase(uvm_phase phase);
    super.report_phase(phase);
    
    // Calculate final metrics
    if (total_packets > 0) begin
      avg_latency = real'(total_latency) / real'(total_packets);
    end
    
    calculate_latency_percentiles();
    calculate_throughput_percentage();
    track_router_utilization();
    track_link_utilization();
    analyze_traffic_patterns();
    analyze_fairness();
    analyze_qos_impact();
    
    // Print reports
    print_latency_summary();
    print_throughput_summary();
    print_utilization_summary();
    print_fairness_summary();
    print_qos_analysis();
    print_traffic_pattern_summary();
    
    // Write CSV files
    write_performance_csv();
    
    // Summary
    `uvm_info("REPORT", "Performance monitoring report complete", UVM_LOW)
  endfunction

  //===========================================================================
  // Print Methods
  //===========================================================================
  
  function void print_latency_summary();
    `uvm_info("LATENCY", "==============================================================================", UVM_LOW)
    `uvm_info("LATENCY", "LATENCY SUMMARY", UVM_LOW)
    `uvm_info("LATENCY", "==============================================================================", UVM_LOW)
    `uvm_info("LATENCY", $sformatf("Total Packets: %0d", total_packets), UVM_LOW)
    `uvm_info("LATENCY", $sformatf("Min Latency: %0d cycles", min_latency), UVM_LOW)
    `uvm_info("LATENCY", $sformatf("Max Latency: %0d cycles", max_latency), UVM_LOW)
    `uvm_info("LATENCY", $sformatf("Avg Latency: %.2f cycles", avg_latency), UVM_LOW)
    `uvm_info("LATENCY", $sformatf("p50 Latency: %0d cycles", latency_percentile[50]), UVM_LOW)
    `uvm_info("LATENCY", $sformatf("p95 Latency: %0d cycles", latency_percentile[95]), UVM_LOW)
    `uvm_info("LATENCY", $sformatf("p99 Latency: %0d cycles", latency_percentile[99]), UVM_LOW)
    `uvm_info("LATENCY", $sformatf("p999 Latency: %0d cycles", latency_percentile[999]), UVM_LOW)
    `uvm_info("LATENCY", "==============================================================================", UVM_LOW)
  endfunction
  
  function void print_throughput_summary();
    `uvm_info("THROUGHPUT", "==============================================================================", UVM_LOW)
    `uvm_info("THROUGHPUT", "THROUGHPUT SUMMARY", UVM_LOW)
    `uvm_info("THROUGHPUT", "==============================================================================", UVM_LOW)
    `uvm_info("THROUGHPUT", $sformatf("Total Cycles: %0d", total_cycles), UVM_LOW)
    `uvm_info("THROUGHPUT", $sformatf("Total Flits Delivered: %0d", total_flits_delivered), UVM_LOW)
    `uvm_info("THROUGHPUT", $sformatf("Throughput: %.2f%% of theoretical", throughput_percent), UVM_LOW)
    `uvm_info("THROUGHPUT", $sformatf("Peak Throughput: %.2f%%", peak_throughput), UVM_LOW)
    `uvm_info("THROUGHPUT", $sformatf("Sustained Throughput: %.2f%%", sustained_throughput), UVM_LOW)
    `uvm_info("THROUGHPUT", "==============================================================================", UVM_LOW)
  endfunction
  
  function void print_utilization_summary();
    real avg_router_util = 0.0;
    real avg_link_util = 0.0;
    int router_count = 0;
    int link_count = 0;
    int over_utilized_routers[$];
    int under_utilized_routers[$];
    int over_utilized_links[$];
    int under_utilized_links[$];
    real over_util_threshold = 80.0;  // >80% is over-utilized
    real under_util_threshold = 20.0; // <20% is under-utilized
    
    `uvm_info("UTILIZATION", "==============================================================================", UVM_LOW)
    `uvm_info("UTILIZATION", "UTILIZATION SUMMARY", UVM_LOW)
    `uvm_info("UTILIZATION", "==============================================================================", UVM_LOW)
    
    // Calculate average router utilization and identify over/under-utilized routers
    foreach (per_router_utilization[i]) begin
      avg_router_util += per_router_utilization[i];
      router_count++;
      
      // Identify over-utilized routers (>80%)
      if (per_router_utilization[i] > over_util_threshold) begin
        over_utilized_routers.push_back(i);
      end
      
      // Identify under-utilized routers (<20%)
      if (per_router_utilization[i] < under_util_threshold) begin
        under_utilized_routers.push_back(i);
      end
      
      `uvm_info("UTILIZATION", $sformatf("Router %0d Utilization: %.2f%%", i, per_router_utilization[i]), UVM_MEDIUM)
    end
    if (router_count > 0) begin
      avg_router_util = avg_router_util / real'(router_count);
      `uvm_info("UTILIZATION", $sformatf("Average Router Utilization: %.2f%%", avg_router_util), UVM_LOW)
    end
    
    // Calculate average link utilization and identify over/under-utilized links
    foreach (per_link_utilization[i]) begin
      avg_link_util += per_link_utilization[i];
      link_count++;
      
      // Identify over-utilized links (>80%)
      if (per_link_utilization[i] > over_util_threshold) begin
        over_utilized_links.push_back(i);
      end
      
      // Identify under-utilized links (<20%)
      if (per_link_utilization[i] < under_util_threshold) begin
        under_utilized_links.push_back(i);
      end
      
      `uvm_info("UTILIZATION", $sformatf("Link %0d Utilization: %.2f%%", i, per_link_utilization[i]), UVM_MEDIUM)
    end
    if (link_count > 0) begin
      avg_link_util = avg_link_util / real'(link_count);
      `uvm_info("UTILIZATION", $sformatf("Average Link Utilization: %.2f%%", avg_link_util), UVM_LOW)
    end
    
    // Buffer occupancy
    real avg_buffer_occ = 0.0;
    int buffer_count = 0;
    foreach (average_buffer_occupancy[i]) begin
      avg_buffer_occ += average_buffer_occupancy[i];
      buffer_count++;
      `uvm_info("UTILIZATION", $sformatf("Router %0d Avg Buffer Occupancy: %.2f / %0d", 
                                          i, average_buffer_occupancy[i], cfg.buffer_depth), UVM_MEDIUM)
    end
    if (buffer_count > 0) begin
      avg_buffer_occ = avg_buffer_occ / real'(buffer_count);
      `uvm_info("UTILIZATION", $sformatf("Average Buffer Occupancy: %.2f / %0d", avg_buffer_occ, cfg.buffer_depth), UVM_LOW)
    end
    
    // Report over-utilized components
    `uvm_info("UTILIZATION", "------------------------------------------------------------------------------", UVM_LOW)
    `uvm_info("UTILIZATION", "OVER-UTILIZED COMPONENTS (>80% utilization):", UVM_LOW)
    if (over_utilized_routers.size() > 0) begin
      string router_list = "";
      foreach (over_utilized_routers[i]) begin
        router_list = {router_list, $sformatf("Router %0d (%.2f%%)", 
                                               over_utilized_routers[i], 
                                               per_router_utilization[over_utilized_routers[i]])};
        if (i < over_utilized_routers.size() - 1) router_list = {router_list, ", "};
      end
      `uvm_warning("UTILIZATION", $sformatf("Over-utilized Routers: %s", router_list))
    end else begin
      `uvm_info("UTILIZATION", "  No over-utilized routers detected", UVM_LOW)
    end
    
    if (over_utilized_links.size() > 0) begin
      string link_list = "";
      foreach (over_utilized_links[i]) begin
        link_list = {link_list, $sformatf("Link %0d (%.2f%%)", 
                                          over_utilized_links[i], 
                                          per_link_utilization[over_utilized_links[i]])};
        if (i < over_utilized_links.size() - 1) link_list = {link_list, ", "};
      end
      `uvm_warning("UTILIZATION", $sformatf("Over-utilized Links: %s", link_list))
    end else begin
      `uvm_info("UTILIZATION", "  No over-utilized links detected", UVM_LOW)
    end
    
    // Report under-utilized components
    `uvm_info("UTILIZATION", "------------------------------------------------------------------------------", UVM_LOW)
    `uvm_info("UTILIZATION", "UNDER-UTILIZED COMPONENTS (<20% utilization):", UVM_LOW)
    if (under_utilized_routers.size() > 0) begin
      string router_list = "";
      foreach (under_utilized_routers[i]) begin
        router_list = {router_list, $sformatf("Router %0d (%.2f%%)", 
                                               under_utilized_routers[i], 
                                               per_router_utilization[under_utilized_routers[i]])};
        if (i < under_utilized_routers.size() - 1) router_list = {router_list, ", "};
      end
      `uvm_info("UTILIZATION", $sformatf("Under-utilized Routers: %s (potential routing inefficiency)", router_list), UVM_MEDIUM)
    end else begin
      `uvm_info("UTILIZATION", "  No under-utilized routers detected", UVM_LOW)
    end
    
    if (under_utilized_links.size() > 0) begin
      string link_list = "";
      foreach (under_utilized_links[i]) begin
        link_list = {link_list, $sformatf("Link %0d (%.2f%%)", 
                                          under_utilized_links[i], 
                                          per_link_utilization[under_utilized_links[i]])};
        if (i < under_utilized_links.size() - 1) link_list = {link_list, ", "};
      end
      `uvm_info("UTILIZATION", $sformatf("Under-utilized Links: %s (potential bandwidth waste)", link_list), UVM_MEDIUM)
    end else begin
      `uvm_info("UTILIZATION", "  No under-utilized links detected", UVM_LOW)
    end
    
    // Summary statistics
    `uvm_info("UTILIZATION", "------------------------------------------------------------------------------", UVM_LOW)
    `uvm_info("UTILIZATION", "UTILIZATION STATISTICS:", UVM_LOW)
    `uvm_info("UTILIZATION", $sformatf("  Total Routers: %0d", router_count), UVM_LOW)
    `uvm_info("UTILIZATION", $sformatf("  Over-utilized Routers: %0d (%.1f%%)", 
                                       over_utilized_routers.size(), 
                                       router_count > 0 ? real'(over_utilized_routers.size()) / real'(router_count) * 100.0 : 0.0), UVM_LOW)
    `uvm_info("UTILIZATION", $sformatf("  Under-utilized Routers: %0d (%.1f%%)", 
                                       under_utilized_routers.size(), 
                                       router_count > 0 ? real'(under_utilized_routers.size()) / real'(router_count) * 100.0 : 0.0), UVM_LOW)
    `uvm_info("UTILIZATION", $sformatf("  Total Links: %0d", link_count), UVM_LOW)
    `uvm_info("UTILIZATION", $sformatf("  Over-utilized Links: %0d (%.1f%%)", 
                                       over_utilized_links.size(), 
                                       link_count > 0 ? real'(over_utilized_links.size()) / real'(link_count) * 100.0 : 0.0), UVM_LOW)
    `uvm_info("UTILIZATION", $sformatf("  Under-utilized Links: %0d (%.1f%%)", 
                                       under_utilized_links.size(), 
                                       link_count > 0 ? real'(under_utilized_links.size()) / real'(link_count) * 100.0 : 0.0), UVM_LOW)
    
    `uvm_info("UTILIZATION", "==============================================================================", UVM_LOW)
  endfunction
  
  function void print_fairness_summary();
    real min_master_latency = 999999.0;
    real max_master_latency = 0.0;
    real avg_master_latency = 0.0;
    real latency_variance = 0.0;
    real latency_stddev = 0.0;
    int master_count = 0;
    int starved_masters[$];
    real starvation_threshold = 1.5;  // 1.5x average latency = starved
    
    `uvm_info("FAIRNESS", "==============================================================================", UVM_LOW)
    `uvm_info("FAIRNESS", "FAIRNESS SUMMARY", UVM_LOW)
    `uvm_info("FAIRNESS", "==============================================================================", UVM_LOW)
    
    // Calculate statistics across all masters
    foreach (master_avg_latency[i]) begin
      if (master_avg_latency[i] < min_master_latency) begin
        min_master_latency = master_avg_latency[i];
      end
      if (master_avg_latency[i] > max_master_latency) begin
        max_master_latency = master_avg_latency[i];
      end
      avg_master_latency += master_avg_latency[i];
      master_count++;
    end
    
    if (master_count > 0) begin
      avg_master_latency = avg_master_latency / real'(master_count);
      
      // Calculate standard deviation
      foreach (master_avg_latency[i]) begin
        real diff = master_avg_latency[i] - avg_master_latency;
        latency_variance += diff * diff;
      end
      latency_variance = latency_variance / real'(master_count);
      latency_stddev = $sqrt(latency_variance);
      
      // Identify starved masters (latency > 1.5x average)
      foreach (master_avg_latency[i]) begin
        if (master_avg_latency[i] > avg_master_latency * starvation_threshold) begin
          starved_masters.push_back(i);
        end
      end
    end
    
    // Fairness metrics
    `uvm_info("FAIRNESS", "FAIRNESS METRICS:", UVM_LOW)
    `uvm_info("FAIRNESS", $sformatf("  Fairness Ratio: %.2f (max/min latency, lower is better)", fairness_ratio), UVM_LOW)
    `uvm_info("FAIRNESS", $sformatf("  Min Master Latency: %.2f cycles", min_master_latency), UVM_LOW)
    `uvm_info("FAIRNESS", $sformatf("  Max Master Latency: %.2f cycles", max_master_latency), UVM_LOW)
    `uvm_info("FAIRNESS", $sformatf("  Average Master Latency: %.2f cycles", avg_master_latency), UVM_LOW)
    `uvm_info("FAIRNESS", $sformatf("  Latency Std Deviation: %.2f cycles", latency_stddev), UVM_LOW)
    `uvm_info("FAIRNESS", $sformatf("  Coefficient of Variation: %.2f%%", 
                                     avg_master_latency > 0 ? (latency_stddev / avg_master_latency) * 100.0 : 0.0), UVM_LOW)
    
    // Fairness assessment
    string fairness_assessment;
    if (fairness_ratio < 1.2) begin
      fairness_assessment = "EXCELLENT";
    end else if (fairness_ratio < 1.5) begin
      fairness_assessment = "GOOD";
    end else if (fairness_ratio < 2.0) begin
      fairness_assessment = "FAIR";
    end else begin
      fairness_assessment = "POOR";
    end
    `uvm_info("FAIRNESS", $sformatf("  Fairness Assessment: %s", fairness_assessment), UVM_LOW)
    
    // Contention metrics
    `uvm_info("FAIRNESS", "------------------------------------------------------------------------------", UVM_LOW)
    `uvm_info("FAIRNESS", "CONTENTION METRICS:", UVM_LOW)
    `uvm_info("FAIRNESS", $sformatf("  Total Collision Count: %0d", collision_count), UVM_LOW)
    if (total_cycles > 0) begin
      `uvm_info("FAIRNESS", $sformatf("  Collision Rate: %.4f collisions/cycle", 
                                      real'(collision_count) / real'(total_cycles)), UVM_LOW)
    end
    if (collision_latency_impact > 0 && total_packets > 0) begin
      `uvm_info("FAIRNESS", $sformatf("  Avg Latency Impact per Collision: %.2f cycles", 
                                      real'(collision_latency_impact) / real'(collision_count)), UVM_LOW)
    end
    
    // Per-master details
    `uvm_info("FAIRNESS", "------------------------------------------------------------------------------", UVM_LOW)
    `uvm_info("FAIRNESS", "PER-MASTER LATENCY BREAKDOWN:", UVM_LOW)
    foreach (master_avg_latency[i]) begin
      real deviation_from_avg = master_avg_latency[i] - avg_master_latency;
      real deviation_pct = avg_master_latency > 0 ? (deviation_from_avg / avg_master_latency) * 100.0 : 0.0;
      string status = "";
      
      if (master_avg_latency[i] > avg_master_latency * starvation_threshold) begin
        status = " [STARVED]";
      end else if (master_avg_latency[i] < avg_master_latency * 0.8) begin
        status = " [FAVORED]";
      end
      
      `uvm_info("FAIRNESS", $sformatf("  Master %0d: %.2f cycles (%0d packets, %.1f%% from avg)%s", 
                                       i, master_avg_latency[i], master_packet_count[i], 
                                       deviation_pct, status), UVM_MEDIUM)
    end
    
    // Starvation analysis
    `uvm_info("FAIRNESS", "------------------------------------------------------------------------------", UVM_LOW)
    `uvm_info("FAIRNESS", "STARVATION ANALYSIS:", UVM_LOW)
    if (starved_masters.size() > 0) begin
      string starved_list = "";
      foreach (starved_masters[i]) begin
        starved_list = {starved_list, $sformatf("Master %0d (%.2f cycles, %.1fx avg)", 
                                                starved_masters[i], 
                                                master_avg_latency[starved_masters[i]],
                                                master_avg_latency[starved_masters[i]] / avg_master_latency)};
        if (i < starved_masters.size() - 1) starved_list = {starved_list, ", "};
      end
      `uvm_warning("FAIRNESS", $sformatf("Starved Masters (>%.1fx average): %s", 
                                         starvation_threshold, starved_list))
    end else begin
      `uvm_info("FAIRNESS", "  No starved masters detected (all within acceptable range)", UVM_LOW)
    end
    
    `uvm_info("FAIRNESS", "==============================================================================", UVM_LOW)
  endfunction
  
  //===========================================================================
  // QoS Analysis Function
  //===========================================================================
  // 
  // Purpose: Analyze Quality of Service (QoS) impact on NoC performance
  //
  // QoS in GPU NoCs:
  //   - 4-bit QoS field (0-15) where higher values = higher priority
  //   - QoS 0: Best-effort traffic (background, low priority)
  //   - QoS 8: Normal priority (typical compute workloads)
  //   - QoS 15: Critical priority (graphics, real-time, frame-critical)
  //
  // Performance Standards (GPU Industry):
  //   - QoS 15 should have <20% latency penalty vs. QoS 0
  //   - QoS priority gap (QoS15/QoS0) should be <1.2x for fairness
  //   - SLA violations should be <1% of transactions per QoS level
  //
  // Reference: ARM AMBA 5 AXI4 Specification, Section 4.3 (QoS Signaling)
  //            NVIDIA GPU Architecture Whitepapers (QoS for Graphics/Compute)
  //===========================================================================
  function void print_qos_analysis();
    real qos0_avg = 0.0;
    real qos15_avg = 0.0;
    int qos_sla_violations_per_level[int];
    real qos_min_latency[int];
    real qos_max_latency[int];
    
    // Calculate SLA violations per QoS level and min/max latencies
    foreach (latency_per_qos[qos_level]) begin
      qos_min_latency[qos_level] = 999999.0;
      qos_max_latency[qos_level] = 0.0;
      qos_sla_violations_per_level[qos_level] = 0;
      
      foreach (latency_per_qos[qos_level][latency]) begin
        int count = latency_per_qos[qos_level][latency];
        
        // Track min/max latency for this QoS level
        if (latency < qos_min_latency[qos_level]) begin
          qos_min_latency[qos_level] = real'(latency);
        end
        if (latency > qos_max_latency[qos_level]) begin
          qos_max_latency[qos_level] = real'(latency);
        end
        
        // Count SLA violations (latency exceeds threshold)
        if (latency > qos_sla_threshold[qos_level]) begin
          qos_sla_violations_per_level[qos_level] += count;
        end
      end
    end
    
    // Get QoS0 and QoS15 average latencies for priority gap calculation
    if (qos_avg_latency.exists(0) && qos_packet_count[0] > 0) begin
      qos0_avg = qos_avg_latency[0];
    end
    if (qos_avg_latency.exists(15) && qos_packet_count[15] > 0) begin
      qos15_avg = qos_avg_latency[15];
    end
    
    `uvm_info("QOS", "==============================================================================", UVM_LOW)
    `uvm_info("QOS", "QOS IMPACT ANALYSIS", UVM_LOW)
    `uvm_info("QOS", "==============================================================================", UVM_LOW)
    
    // Priority Gap Analysis
    // Priority gap = QoS15 latency / QoS0 latency
    // Ideal: <1.2x (high priority gets benefit without starving low priority)
    // Acceptable: <1.5x
    // Poor: >2.0x (excessive priority discrimination)
    `uvm_info("QOS", "PRIORITY GAP ANALYSIS:", UVM_LOW)
    if (qos0_avg > 0) begin
      `uvm_info("QOS", $sformatf("  QoS15 Average Latency: %.2f cycles", qos15_avg), UVM_LOW)
      `uvm_info("QOS", $sformatf("  QoS0 Average Latency: %.2f cycles", qos0_avg), UVM_LOW)
      `uvm_info("QOS", $sformatf("  Priority Gap (QoS15/QoS0): %.2fx", qos_priority_gap), UVM_LOW)
      
      string gap_assessment;
      if (qos_priority_gap < 1.2) begin
        gap_assessment = "EXCELLENT (ideal priority discrimination)";
      end else if (qos_priority_gap < 1.5) begin
        gap_assessment = "GOOD (acceptable priority benefit)";
      end else if (qos_priority_gap < 2.0) begin
        gap_assessment = "FAIR (moderate priority benefit)";
      end else begin
        gap_assessment = "POOR (excessive priority discrimination, QoS0 may be starved)";
      end
      `uvm_info("QOS", $sformatf("  Gap Assessment: %s", gap_assessment), UVM_LOW)
    end else begin
      `uvm_warning("QOS", "Cannot calculate priority gap: QoS0 data not available")
    end
    
    // SLA Violations Summary
    // SLA (Service Level Agreement) violations occur when latency exceeds QoS-specific threshold
    // GPU Performance Standard: <1% violation rate per QoS level
    `uvm_info("QOS", "------------------------------------------------------------------------------", UVM_LOW)
    `uvm_info("QOS", "SLA VIOLATIONS SUMMARY:", UVM_LOW)
    `uvm_info("QOS", $sformatf("  Total SLA Violations: %0d", qos_sla_violations), UVM_LOW)
    if (total_packets > 0) begin
      `uvm_info("QOS", $sformatf("  Overall Violation Rate: %.2f%%", 
                                 real'(qos_sla_violations) / real'(total_packets) * 100.0), UVM_LOW)
    end
    
    // Per-QoS Level Detailed Analysis
    // Shows latency statistics, packet count, SLA threshold, and violation rate per QoS level
    `uvm_info("QOS", "------------------------------------------------------------------------------", UVM_LOW)
    `uvm_info("QOS", "LATENCY PER QoS LEVEL:", UVM_LOW)
    `uvm_info("QOS", "QoS | Avg Latency | Min Latency | Max Latency | Packets | SLA | Violations | Viol Rate", UVM_LOW)
    `uvm_info("QOS", "----|-------------|-------------|-------------|---------|-----|------------|----------", UVM_LOW)
    
    for (int i = 0; i < 16; i++) begin
      if (qos_avg_latency.exists(i) && qos_packet_count[i] > 0) begin
        real violation_rate = 0.0;
        if (qos_packet_count[i] > 0) begin
          violation_rate = real'(qos_sla_violations_per_level[i]) / real'(qos_packet_count[i]) * 100.0;
        end
        
        string violation_status = "";
        if (violation_rate > 1.0) begin
          violation_status = " [HIGH]";
        end else if (violation_rate > 0.5) begin
          violation_status = " [MODERATE]";
        end else if (violation_rate > 0) begin
          violation_status = " [LOW]";
        end else begin
          violation_status = " [NONE]";
        end
        
        `uvm_info("QOS", $sformatf(" %2d | %11.2f | %11.2f | %11.2f | %7d | %3d | %10d | %.2f%%%s",
                                    i, qos_avg_latency[i], 
                                    qos_min_latency.exists(i) ? qos_min_latency[i] : 0.0,
                                    qos_max_latency.exists(i) ? qos_max_latency[i] : 0.0,
                                    qos_packet_count[i], qos_sla_threshold[i],
                                    qos_sla_violations_per_level[i], violation_rate, violation_status), UVM_MEDIUM)
      end
    end
    
    // QoS Fairness Analysis
    // Measures minimum latency gap between adjacent QoS levels
    // Lower gap = more gradual priority discrimination (better fairness)
    `uvm_info("QOS", "------------------------------------------------------------------------------", UVM_LOW)
    `uvm_info("QOS", "QOS FAIRNESS ANALYSIS:", UVM_LOW)
    `uvm_info("QOS", $sformatf("  Minimum Gap Between Adjacent QoS Levels: %.2f cycles", qos_fairness), UVM_LOW)
    
    // Check for QoS levels with no packets (coverage gap)
    int uncovered_qos[$];
    for (int i = 0; i < 16; i++) begin
      if (!qos_avg_latency.exists(i) || qos_packet_count[i] == 0) begin
        uncovered_qos.push_back(i);
      end
    end
    if (uncovered_qos.size() > 0) begin
      string uncovered_list = "";
      foreach (uncovered_qos[i]) begin
        uncovered_list = {uncovered_list, $sformatf("QoS %0d", uncovered_qos[i])};
        if (i < uncovered_qos.size() - 1) uncovered_list = {uncovered_list, ", "};
      end
      `uvm_info("QOS", $sformatf("  Uncovered QoS Levels (no packets): %s", uncovered_list), UVM_MEDIUM)
    end
    
    `uvm_info("QOS", "==============================================================================", UVM_LOW)
  endfunction
  
  function void print_traffic_pattern_summary();
    `uvm_info("TRAFFIC", "==============================================================================", UVM_LOW)
    `uvm_info("TRAFFIC", "TRAFFIC PATTERN SUMMARY", UVM_LOW)
    `uvm_info("TRAFFIC", "==============================================================================", UVM_LOW)
    `uvm_info("TRAFFIC", $sformatf("Total Traffic Packets: %0d", total_traffic_packets), UVM_LOW)
    `uvm_info("TRAFFIC", $sformatf("Traffic Concentration: %.2f%% (top 10%% destinations)", traffic_concentration), UVM_LOW)
    `uvm_info("TRAFFIC", $sformatf("Hotspot Latency Impact: %.2f%%", hotspot_latency_impact), UVM_LOW)
    `uvm_info("TRAFFIC", "Top 5 Source-Destination Pairs:", UVM_LOW)
    // Print top source-destination pairs (simplified)
    `uvm_info("TRAFFIC", "==============================================================================", UVM_LOW)
  endfunction

  //===========================================================================
  // CSV File Writing
  //===========================================================================
  //
  // Purpose: Export performance metrics to CSV files for post-processing,
  //          visualization, and regression analysis
  //
  // CSV Files Generated:
  //   1. performance_latency.csv - Latency histogram (cycle_count, packet_count)
  //   2. performance_throughput.csv - Throughput metrics summary
  //   3. performance_qos.csv - QoS breakdown (qos_level, avg_latency, max_latency)
  //   4. performance_router_utilization.csv - Per-router utilization
  //   5. performance_link_utilization.csv - Per-link utilization
  //   6. performance_src_dest_matrix.csv - Source-destination traffic matrix
  //
  // Usage: Import CSV files into Excel, Python pandas, or MATLAB for:
  //   - Latency distribution plots
  //   - Throughput vs. injection rate curves
  //   - QoS impact analysis charts
  //   - Heatmaps of router/link utilization
  //   - Traffic pattern visualization
  //===========================================================================
  
  task write_performance_csv();
    int file_handle;
    string filename;
    
    //=========================================================================
    // 1. Latency Histogram CSV
    // Format: cycle_count, packet_count
    // Purpose: Plot latency distribution (histogram) to identify latency modes
    //=========================================================================
    filename = "performance_latency.csv";
    file_handle = $fopen(filename, "w");
    if (file_handle) begin
      $fdisplay(file_handle, "Latency_Cycles,Packet_Count");
      foreach (latency_histogram[i]) begin
        $fdisplay(file_handle, "%0d,%0d", i, latency_histogram[i]);
      end
      $fclose(file_handle);
      `uvm_info("CSV", $sformatf("Wrote latency histogram to %s", filename), UVM_LOW)
    end
    
    //=========================================================================
    // 2. Throughput CSV
    // Format: Metric, Value
    // Purpose: Summary of throughput metrics for regression tracking
    //=========================================================================
    filename = "performance_throughput.csv";
    file_handle = $fopen(filename, "w");
    if (file_handle) begin
      $fdisplay(file_handle, "Metric,Value");
      $fdisplay(file_handle, "Total_Cycles,%0d", total_cycles);
      $fdisplay(file_handle, "Total_Flits,%0d", total_flits_delivered);
      $fdisplay(file_handle, "Throughput_Percent,%.2f", throughput_percent);
      $fdisplay(file_handle, "Peak_Throughput,%.2f", peak_throughput);
      $fdisplay(file_handle, "Sustained_Throughput,%.2f", sustained_throughput);
      $fclose(file_handle);
      `uvm_info("CSV", $sformatf("Wrote throughput data to %s", filename), UVM_LOW)
    end
    
    //=========================================================================
    // 3. QoS Breakdown CSV
    // Format: qos_level, avg_latency, min_latency, max_latency, packet_count, sla_threshold, sla_violations
    // Purpose: Analyze QoS impact on latency, identify SLA violations per level
    //=========================================================================
    filename = "performance_qos.csv";
    file_handle = $fopen(filename, "w");
    if (file_handle) begin
      $fdisplay(file_handle, "QoS_Level,Avg_Latency,Min_Latency,Max_Latency,Packet_Count,SLA_Threshold,SLA_Violations");
      
      // Calculate min/max and SLA violations per QoS level
      for (int i = 0; i < 16; i++) begin
        if (qos_avg_latency.exists(i) && qos_packet_count[i] > 0) begin
          real qos_min = 999999.0;
          real qos_max = 0.0;
          int qos_violations = 0;
          
          // Find min/max and count violations from histogram
          if (latency_per_qos.exists(i)) begin
            foreach (latency_per_qos[i][latency]) begin
              int count = latency_per_qos[i][latency];
              if (latency < qos_min) qos_min = real'(latency);
              if (latency > qos_max) qos_max = real'(latency);
              if (latency > qos_sla_threshold[i]) begin
                qos_violations += count;
              end
            end
          end
          
          $fdisplay(file_handle, "%0d,%.2f,%.2f,%.2f,%0d,%0d,%0d", 
                    i, qos_avg_latency[i], qos_min, qos_max,
                    qos_packet_count[i], qos_sla_threshold[i], qos_violations);
        end
      end
      $fclose(file_handle);
      `uvm_info("CSV", $sformatf("Wrote QoS breakdown to %s", filename), UVM_LOW)
    end
    
    //=========================================================================
    // 4. Per-Router Utilization CSV
    // Format: router_id, utilization_percent
    // Purpose: Identify hot-spot routers and routing inefficiencies
    //=========================================================================
    filename = "performance_router_utilization.csv";
    file_handle = $fopen(filename, "w");
    if (file_handle) begin
      $fdisplay(file_handle, "Router_ID,Utilization_Percent");
      foreach (per_router_utilization[i]) begin
        $fdisplay(file_handle, "%0d,%.2f", i, per_router_utilization[i]);
      end
      $fclose(file_handle);
      `uvm_info("CSV", $sformatf("Wrote router utilization to %s", filename), UVM_LOW)
    end
    
    //=========================================================================
    // 5. Per-Link Utilization CSV
    // Format: link_id, utilization_percent
    // Purpose: Identify bottleneck links and underutilized links
    //=========================================================================
    filename = "performance_link_utilization.csv";
    file_handle = $fopen(filename, "w");
    if (file_handle) begin
      $fdisplay(file_handle, "Link_ID,Utilization_Percent");
      foreach (per_link_utilization[i]) begin
        $fdisplay(file_handle, "%0d,%.2f", i, per_link_utilization[i]);
      end
      $fclose(file_handle);
      `uvm_info("CSV", $sformatf("Wrote link utilization to %s", filename), UVM_LOW)
    end
    
    //=========================================================================
    // 6. Source-Destination Traffic Matrix CSV
    // Format: source_id, dest_id, packet_count
    // Purpose: Analyze traffic patterns, identify hotspots, optimize routing
    //          Can be imported into MATLAB/Python for heatmap visualization
    //=========================================================================
    filename = "performance_src_dest_matrix.csv";
    file_handle = $fopen(filename, "w");
    if (file_handle) begin
      $fdisplay(file_handle, "Source_ID,Dest_ID,Packet_Count");
      foreach (source_destination_matrix[i]) begin
        foreach (source_destination_matrix[i][j]) begin
          if (source_destination_matrix[i][j] > 0) begin
            $fdisplay(file_handle, "%0d,%0d,%0d", i, j, source_destination_matrix[i][j]);
          end
        end
      end
      $fclose(file_handle);
      `uvm_info("CSV", $sformatf("Wrote source-destination matrix to %s", filename), UVM_LOW)
    end
    
    //=========================================================================
    // 7. Buffer Occupancy CSV (Additional metric)
    // Format: router_id, avg_occupancy, max_occupancy
    // Purpose: Identify buffer bottlenecks
    //=========================================================================
    filename = "performance_buffer_occupancy.csv";
    file_handle = $fopen(filename, "w");
    if (file_handle) begin
      $fdisplay(file_handle, "Router_ID,Avg_Occupancy,Max_Occupancy,Buffer_Depth");
      foreach (average_buffer_occupancy[i]) begin
        $fdisplay(file_handle, "%0d,%.2f,%0d,%0d", i, average_buffer_occupancy[i],
                  buffer_max_depth.exists(i) ? buffer_max_depth[i] : 0, cfg.buffer_depth);
      end
      $fclose(file_handle);
      `uvm_info("CSV", $sformatf("Wrote buffer occupancy to %s", filename), UVM_LOW)
    end
    
    `uvm_info("CSV", "All performance CSV files written successfully", UVM_LOW)
  endtask

endclass

`endif // PERFORMANCE_MONITOR_SV
