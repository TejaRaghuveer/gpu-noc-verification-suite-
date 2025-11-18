# GPU Interconnect NoC Verification Framework Architecture

**Version**: 1.0.0  
**Last Updated**: January 2025  
**Status**: Production Ready

---

## Table of Contents

1. [Why GPUs Use NoC](#why-gpus-use-noc)
2. [Network-on-Chip Fundamentals](#network-on-chip-fundamentals)
3. [Protocol Specification](#protocol-specification)
4. [UVM Verification Architecture](#uvm-verification-architecture)
5. [Deadlock Prevention in Verification](#deadlock-prevention-in-verification)
6. [Performance Monitoring](#performance-monitoring)
7. [File Organization](#file-organization)

---

## Why GPUs Use NoC

### Introduction

Modern Graphics Processing Units (GPUs) represent some of the most complex and performance-critical integrated circuits ever designed. With thousands of processing elements, massive memory hierarchies, and real-time performance requirements, GPUs demand interconnect architectures that can scale efficiently while maintaining predictable latency and bandwidth characteristics. Network-on-Chip (NoC) architectures have emerged as the de facto standard for GPU interconnects, replacing traditional bus-based and crossbar-based systems.

### Bandwidth Requirements: TB/s Scale

Modern GPUs require aggregate interconnect bandwidth measured in **terabytes per second**. Consider a high-end GPU with:

- **512 Streaming Multiprocessors (SMs)**: Each requiring memory access
- **Memory Bandwidth**: 1-2 TB/s aggregate bandwidth requirement
- **Cache Coherency Traffic**: Additional 20-30% overhead for coherence protocols
- **I/O Traffic**: PCIe, display outputs, external memory controllers

**Total Interconnect Bandwidth**: 1.5-2.5 TB/s

#### Bandwidth Breakdown Example

| Component | Bandwidth Requirement | Percentage |
|-----------|---------------------|------------|
| L2 Cache Accesses | 800 GB/s | 40% |
| Memory Controller | 600 GB/s | 30% |
| Cache Coherency | 400 GB/s | 20% |
| I/O Controllers | 200 GB/s | 10% |
| **Total** | **2000 GB/s** | **100%** |

Traditional bus architectures cannot scale to these bandwidths due to:
- **Serialization Bottlenecks**: Single shared bus becomes saturated
- **Arbitration Overhead**: Centralized arbitration doesn't scale
- **Physical Limitations**: Long wires cause timing closure issues

NoC architectures solve these problems through:
- **Parallel Communication**: Multiple simultaneous paths
- **Distributed Arbitration**: Each router handles local traffic
- **Short Wires**: Mesh topology keeps wire lengths manageable

### Scalability to 100+ Processing Elements

GPU architectures continue to scale, with modern designs featuring:

- **100-200 SMs**: Each SM contains 64-128 CUDA cores
- **10,000+ Total Cores**: Requiring efficient interconnect
- **Multiple Memory Controllers**: 8-16 HBM stacks
- **Specialized Units**: Tensor cores, RT cores, video encoders/decoders

#### Scalability Comparison

| Architecture | Max Nodes | Bandwidth per Node | Total Bandwidth |
|--------------|-----------|-------------------|-----------------|
| Shared Bus | 8-16 | 10 GB/s | 80-160 GB/s |
| Crossbar | 32-64 | 5 GB/s | 160-320 GB/s |
| **NoC (Mesh)** | **512+** | **4 GB/s** | **2000+ GB/s** |

NoC scalability comes from:
1. **O(log N) Hop Count**: Average path length grows logarithmically
2. **O(N) Aggregate Bandwidth**: Total bandwidth scales with nodes
3. **Modular Design**: Add nodes by extending mesh dimensions

### Real-Time Performance Constraints: GPU Frame Timing

GPUs operate under strict real-time constraints:

#### Graphics Pipeline Timing

```
Frame Time Budget: 16.67 ms (60 FPS)
├── Geometry Processing: 4 ms
├── Rasterization: 3 ms
├── Pixel Shading: 6 ms
├── Memory Access: 2 ms
└── Display Output: 1.67 ms
```

**Critical Path**: Memory access latency directly impacts frame time. A single stalled memory access can cause frame drops.

#### Compute Workload Timing

- **AI Inference**: <10ms latency requirement for real-time applications
- **Scientific Computing**: Predictable latency for iterative algorithms
- **Video Encoding**: Real-time encoding requires consistent throughput

NoC must guarantee:
- **Bounded Latency**: Worst-case latency < 1μs for critical paths
- **Predictable Performance**: Deterministic routing (XY routing)
- **Priority Support**: QoS ensures critical traffic gets priority

### Cache Coherency Requirements

Modern GPUs implement sophisticated cache hierarchies:

```
L1 Cache (per SM): 128 KB
L2 Cache (shared): 4-8 MB
L3 Cache (optional): 16-32 MB
Global Memory: 24-48 GB HBM
```

#### Coherency Traffic Patterns

1. **Snoop Requests**: Broadcast to all caches
2. **Invalidation Messages**: Remove stale data
3. **Data Forwarding**: Transfer cache lines between SMs
4. **Write-Back Traffic**: Modified cache lines to memory

**Coherency Overhead**: 20-30% of total NoC traffic

#### Coherency Protocol Requirements

- **Ordering**: Maintain memory consistency model
- **Atomicity**: Support atomic operations (CAS, fetch-and-add)
- **Deadlock Freedom**: Coherency protocols must not deadlock
- **Performance**: Coherency overhead must be minimized

NoC provides:
- **Ordered Channels**: Separate virtual channels for requests/responses
- **Priority Routing**: Coherency traffic gets high priority
- **Deadlock-Free Routing**: XY routing prevents circular dependencies

### Why NoC Wins for GPUs

**Summary**: GPUs use NoC because:

1. **Bandwidth**: Only NoC can deliver TB/s aggregate bandwidth
2. **Scalability**: Scales to 500+ nodes efficiently
3. **Latency**: Predictable, bounded latency for real-time workloads
4. **Coherency**: Efficient support for cache coherency protocols
5. **Power**: Lower power than alternatives at scale
6. **Area**: Modular design reduces layout complexity

---

## Network-on-Chip Fundamentals

### Mesh Topology: 4x4 Grid Example

The mesh topology is the most common NoC topology for GPUs due to its simplicity, scalability, and deadlock-free routing properties.

#### 4x4 Mesh Topology

```
     North
       ↑
       |
    ┌──┼──┐
    │  │  │
West─┼──┼──┼─East
    │  │  │
    └──┼──┘
       │
       ↓
     South

4x4 Mesh Grid:
┌─────┬─────┬─────┬─────┐
│ R00 │ R01 │ R02 │ R03 │  Row 0
├─────┼─────┼─────┼─────┤
│ R10 │ R11 │ R12 │ R13 │  Row 1
├─────┼─────┼─────┼─────┤
│ R20 │ R21 │ R22 │ R23 │  Row 2
├─────┼─────┼─────┼─────┼─────┤
│ R30 │ R31 │ R32 │ R33 │ MC │  Row 3 + Memory Controller
└─────┴─────┴─────┴─────┴─────┘
```

**Key Properties**:
- **16 Routers**: R00 through R33
- **24 Links**: Horizontal (12) + Vertical (12)
- **Bisection Bandwidth**: 12 links × link_width
- **Diameter**: 6 hops (R00 to R33)
- **Average Hop Count**: ~2.67 hops

#### Node Addressing

Each router has a unique (X, Y) coordinate:
- **R00**: (0, 0) - Top-left
- **R33**: (3, 3) - Bottom-right
- **R12**: (1, 2) - Row 1, Column 2

### XY Routing Algorithm

XY routing is a **deterministic, dimension-order routing** algorithm that prevents deadlock by routing packets first in the X dimension, then in the Y dimension.

#### XY Routing Pseudocode

```systemverilog
// XY Routing Algorithm
// File: rtl/router.sv (lines 150-180)

function route_t compute_route(
    node_id_t src,
    node_id_t dst
);
    route_t route;
    int dx, dy;
    
    // Calculate delta in X and Y dimensions
    dx = dst.x - src.x;
    dy = dst.y - src.y;
    
    // Phase 1: Route in X dimension
    if (dx > 0) begin
        route.direction = EAST;
        route.hops_x = dx;
    end else if (dx < 0) begin
        route.direction = WEST;
        route.hops_x = -dx;
    end else begin
        route.hops_x = 0;
    end
    
    // Phase 2: Route in Y dimension (after X complete)
    if (dy > 0) begin
        route.direction = NORTH;
        route.hops_y = dy;
    end else if (dy < 0) begin
        route.direction = SOUTH;
        route.hops_y = -dy;
    end else begin
        route.hops_y = 0;
    end
    
    return route;
endfunction
```

#### XY Routing Example

**Packet**: R00 (0,0) → R23 (2,3)

```
Step 1: Route East (X dimension)
R00 → R01 → R02  (2 hops East)

Step 2: Route South (Y dimension)
R02 → R12 → R22 → R23  (3 hops South)

Total: 5 hops
```

**Visual Path**:
```
R00 ──→ R01 ──→ R02
                    │
                    ↓
                  R12
                    │
                    ↓
                  R22 ──→ R23
```

### Router Architecture

A NoC router consists of several key components working together to route packets efficiently.

#### Router Block Diagram

```
                    ┌─────────────────────┐
                    │   Input Ports (5)   │
                    │  N, S, E, W, Local  │
                    └──────────┬──────────┘
                               │
                    ┌──────────▼──────────┐
                    │  Input Buffers      │
                    │  (per VC, per port)│
                    └──────────┬──────────┘
                               │
                    ┌──────────▼──────────┐
                    │  Route Computation │
                    │  (XY Routing Logic)│
                    └──────────┬──────────┘
                               │
                    ┌──────────▼──────────┐
                    │  Virtual Channel    │
                    │  Allocation        │
                    └──────────┬──────────┘
                               │
                    ┌──────────▼──────────┐
                    │  Switch Allocation  │
                    │  (Arbiter)         │
                    └──────────┬──────────┘
                               │
                    ┌──────────▼──────────┐
                    │  Crossbar Switch    │
                    │  (5x5)             │
                    └──────────┬──────────┘
                               │
                    ┌──────────▼──────────┐
                    │  Output Ports (5)  │
                    │  N, S, E, W, Local │
                    └────────────────────┘
```

#### Input Ports

Each router has **5 input ports**:
- **North (N)**: From router above
- **South (S)**: From router below
- **East (E)**: From router to the right
- **West (W)**: From router to the left
- **Local (L)**: From attached processing element

**Port Width**: Typically 128-256 bits (flit width)

#### Input Buffers

**Purpose**: Store incoming flits before routing

**Organization**:
- **Per Port**: Separate buffer per input port
- **Per Virtual Channel**: Separate buffer per VC within port
- **Depth**: 4-16 flits per VC buffer

**Buffer Structure**:
```systemverilog
// File: rtl/router.sv (lines 50-70)
typedef struct packed {
    flit_t data[VC_BUFFER_DEPTH];
    int    head_ptr;
    int    tail_ptr;
    int    count;
    bit    full;
    bit    empty;
} vc_buffer_t;

vc_buffer_t input_buffers[NUM_PORTS][NUM_VCS];
```

**Flow Control**: Credit-based flow control prevents buffer overflow

#### Route Computation

**Function**: Determine output port based on destination

**Algorithm**: XY routing (see above)

**Implementation**:
```systemverilog
// File: rtl/router.sv (lines 200-220)
always_comb begin
    route_compute_output_port = compute_xy_route(
        current_node_id,
        flit.destination
    );
end
```

**Latency**: 1 cycle (combinational logic)

#### Virtual Channel Allocation

**Purpose**: Allocate virtual channel for packet traversal

**Virtual Channels**: Separate logical channels sharing physical link

**Benefits**:
1. **Deadlock Prevention**: Separate VCs break circular dependencies
2. **Performance**: Multiple packets can traverse link simultaneously
3. **QoS**: Different VCs for different priority levels

**VC Allocation Algorithm**:
```systemverilog
// File: rtl/router.sv (lines 250-280)
function vc_id_t allocate_vc(
    port_id_t output_port,
    qos_t     priority
);
    // Allocate VC based on priority
    // High priority: VC 0-1
    // Low priority: VC 2-3
    
    if (priority >= HIGH_PRIORITY_THRESHOLD) begin
        return find_free_vc(output_port, 0, 1);
    end else begin
        return find_free_vc(output_port, 2, 3);
    end
endfunction
```

#### Switch Allocation (Arbiter)

**Purpose**: Grant crossbar access to competing requests

**Arbitration Policy**: 
- **Round-Robin**: Fair allocation
- **Priority-Based**: High-priority packets first
- **Age-Based**: Oldest packet first

**Arbiter Implementation**:
```systemverilog
// File: rtl/router.sv (lines 300-330)
always_comb begin
    // Priority arbitration
    for (int i = 0; i < NUM_REQUESTS; i++) begin
        if (requests[i].valid && 
            requests[i].priority > highest_priority) begin
            grant = i;
            highest_priority = requests[i].priority;
        end
    end
end
```

#### Crossbar Switch

**Purpose**: Connect any input port to any output port

**Size**: 5×5 crossbar (5 inputs × 5 outputs)

**Switching**: 
- **Wormhole**: Flits of packet follow same path
- **Virtual Cut-Through**: Packet forwarded as soon as head flit arrives

**Crossbar Implementation**:
```systemverilog
// File: rtl/router.sv (lines 350-380)
always_comb begin
    for (int out = 0; out < NUM_PORTS; out++) begin
        if (switch_alloc[out].valid) begin
            int in = switch_alloc[out].input_port;
            crossbar_output[out] = input_buffers[in][switch_alloc[out].vc].data[head];
        end
    end
end
```

### Virtual Channels and Flow Control

#### Virtual Channel Concept

**Physical Link**: Single wire connecting two routers

**Virtual Channels**: Multiple logical channels sharing physical link

**Example**: 4 VCs on single link
```
Physical Link (128 bits)
├── VC0: High-priority requests
├── VC1: High-priority responses
├── VC2: Low-priority requests
└── VC3: Low-priority responses
```

#### Flow Control Mechanisms

**1. Credit-Based Flow Control**

```systemverilog
// File: rtl/router.sv (lines 400-420)
// Sender maintains credit count
int credits[NUM_PORTS][NUM_VCS];

// When flit sent
always_ff @(posedge clk) begin
    if (flit_sent) begin
        credits[port][vc]--;
    end
    if (credit_received) begin
        credits[port][vc]++;
    end
end

// Can send if credits available
assign can_send = (credits[port][vc] > 0);
```

**2. On/Off Flow Control**

Simpler mechanism: Receiver sends "stop" signal when buffer full

**3. Ack/Nack Flow Control**

Receiver acknowledges each flit; sender retransmits on NACK

### Link Widths, Flit Sizes, Buffer Depths

#### Link Width

**Definition**: Number of bits transmitted per cycle

**Typical Values**:
- **Narrow Links**: 64 bits (low-cost designs)
- **Standard Links**: 128 bits (most common)
- **Wide Links**: 256 bits (high-bandwidth designs)

**Trade-offs**:
- **Wider Links**: Higher bandwidth, more area/power
- **Narrower Links**: Lower bandwidth, less area/power

#### Flit Size

**Definition**: Smallest unit of data transferred across NoC

**Flit Types**:
1. **Head Flit**: Contains routing information
2. **Body Flit**: Contains payload data
3. **Tail Flit**: Marks end of packet

**Typical Sizes**:
- **Head Flit**: 128 bits (routing + control)
- **Body Flit**: 128 bits (data payload)
- **Tail Flit**: 128 bits (data + end marker)

**Packet Structure**:
```
Packet = Head Flit + (N × Body Flit) + Tail Flit

Example: 64-byte packet = 1 Head + 3 Body + 1 Tail = 5 flits
```

#### Buffer Depth

**Definition**: Number of flits stored per VC buffer

**Typical Values**:
- **Shallow Buffers**: 4 flits (area-efficient)
- **Standard Buffers**: 8 flits (balanced)
- **Deep Buffers**: 16 flits (high-throughput)

**Buffer Sizing Formula**:
```
Buffer_Depth = Round_Trip_Latency × Link_Utilization

Example:
- Round-trip latency: 10 cycles
- Link utilization: 50%
- Buffer depth: 10 × 0.5 = 5 flits (use 8 for safety margin)
```

### Why XY Routing Prevents Deadlock: Proof Sketch

#### Deadlock Definition

**Deadlock**: Circular dependency where packets wait for each other indefinitely

**Example Deadlock**:
```
Router A waits for Router B
Router B waits for Router C
Router C waits for Router A
→ Circular wait → Deadlock
```

#### XY Routing Deadlock Freedom Proof

**Theorem**: XY routing is deadlock-free for mesh topologies.

**Proof Sketch**:

1. **Partial Ordering**: XY routing imposes partial order on packets
   - All packets route in X dimension first
   - Then route in Y dimension
   - This creates a **DAG (Directed Acyclic Graph)** of dependencies

2. **No Cycles**: DAG has no cycles by definition
   - If packet P1 depends on P2, and P2 depends on P3, then P1 depends on P3
   - But P3 cannot depend on P1 (would create cycle)
   - Therefore, no circular dependencies

3. **Formal Proof**:
   ```
   Assume: Packet at (x1, y1) wants to go to (x2, y2)
   
   Case 1: x1 ≠ x2
   - Packet routes in X dimension first
   - All X-routing packets have ordering: x1 < x2 or x2 < x1
   - No circular dependency possible
   
   Case 2: x1 = x2, y1 ≠ y2
   - Packet routes in Y dimension
   - All Y-routing packets have ordering: y1 < y2 or y2 < y1
   - No circular dependency possible
   
   Conclusion: XY routing is deadlock-free
   ```

4. **Visual Proof**:
   ```
   Consider two packets:
   P1: (0,0) → (2,2)  [Route: E→E→S→S]
   P2: (2,2) → (0,0)  [Route: W→W→N→N]
   
   P1 and P2 use different links:
   - P1 uses: East links, then South links
   - P2 uses: West links, then North links
   - No shared links → No circular dependency
   ```

**Conclusion**: XY routing guarantees deadlock freedom through dimension-order routing that prevents circular dependencies.

---

## Protocol Specification

### AXI4 Protocol Deep Dive

The Advanced eXtensible Interface 4 (AXI4) protocol is widely used in GPU NoCs due to its support for high-performance, out-of-order transactions, and multiple outstanding transactions.

#### AXI4 Channel Architecture

AXI4 uses **5 independent channels** for maximum parallelism:

```
Master                          Slave
  │                              │
  │  ┌──────────────────────┐   │
  │──┤ Write Address (AW)   ├───┤
  │  └──────────────────────┘   │
  │                              │
  │  ┌──────────────────────┐   │
  │──┤ Write Data (W)       ├───┤
  │  └──────────────────────┘   │
  │                              │
  │  ┌──────────────────────┐   │
  │──┤ Write Response (B)   ├───┤
  │  └──────────────────────┘   │
  │                              │
  │  ┌──────────────────────┐   │
  │──┤ Read Address (AR)     ├───┤
  │  └──────────────────────┘   │
  │                              │
  │  ┌──────────────────────┐   │
  │──┤ Read Data (R)        ├───┤
  │  └──────────────────────┘   │
  └                              └
```

#### Write Address Channel (AW)

**Purpose**: Transmit write transaction address and control information

**Key Signals**:
```systemverilog
// File: pkg/axi4_pkg.sv (lines 50-80)
typedef struct packed {
    logic [ADDR_WIDTH-1:0] awaddr;      // Write address
    logic [2:0]            awprot;      // Protection type
    logic [3:0]            awqos;       // Quality of Service
    logic [3:0]            awregion;     // Region identifier
    logic [7:0]            awlen;       // Burst length (1-256)
    logic [2:0]            awsize;      // Burst size (1-128 bytes)
    logic [1:0]            awburst;      // Burst type
    logic                  awlock;      // Lock type
    logic [ID_WIDTH-1:0]   awid;        // Transaction ID
    logic                  awvalid;     // Address valid
    logic                  awready;     // Address ready
} axi4_aw_t;
```

**Transaction Flow**:
```
Master: awvalid = 1, awaddr = 0x1000, awlen = 3
Slave:  awready = 1
→ Handshake complete, address accepted
```

#### Write Data Channel (W)

**Purpose**: Transmit write data

**Key Signals**:
```systemverilog
// File: pkg/axi4_pkg.sv (lines 90-110)
typedef struct packed {
    logic [DATA_WIDTH-1:0] wdata;       // Write data
    logic [STRB_WIDTH-1:0] wstrb;      // Write strobe (byte enable)
    logic                  wlast;       // Last transfer in burst
    logic                  wvalid;      // Data valid
    logic                  wready;      // Data ready
} axi4_w_t;
```

**Burst Transfer Example**:
```
Burst Length = 4, Burst Size = 4 bytes

Transfer 1: wdata = 0xDEADBEEF, wstrb = 0xF, wlast = 0
Transfer 2: wdata = 0xCAFEBABE, wstrb = 0xF, wlast = 0
Transfer 3: wdata = 0x12345678, wstrb = 0xF, wlast = 0
Transfer 4: wdata = 0xABCDEF00, wstrb = 0xF, wlast = 1  ← Last transfer
```

#### Write Response Channel (B)

**Purpose**: Indicate completion status of write transaction

**Key Signals**:
```systemverilog
// File: pkg/axi4_pkg.sv (lines 120-135)
typedef struct packed {
    logic [1:0]          bresp;        // Response type
    logic [ID_WIDTH-1:0] bid;          // Transaction ID (matches AWID)
    logic                bvalid;        // Response valid
    logic                bready;        // Response ready
} axi4_b_t;

// Response Types
typedef enum logic [1:0] {
    OKAY   = 2'b00,  // Normal success
    EXOKAY = 2'b01,  // Exclusive access success
    SLVERR = 2'b10,  // Slave error
    DECERR = 2'b11   // Decode error
} axi4_resp_t;
```

#### Read Address Channel (AR)

**Purpose**: Transmit read transaction address and control information

**Key Signals**: Similar to AW channel, but for reads

```systemverilog
// File: pkg/axi4_pkg.sv (lines 140-170)
typedef struct packed {
    logic [ADDR_WIDTH-1:0] araddr;
    logic [2:0]            arprot;
    logic [3:0]            arqos;
    logic [3:0]            arregion;
    logic [7:0]            arlen;      // Burst length
    logic [2:0]            arsize;     // Burst size
    logic [1:0]            arburst;    // Burst type
    logic                  arlock;
    logic [ID_WIDTH-1:0]   arid;       // Transaction ID
    logic                  arvalid;
    logic                  arready;
} axi4_ar_t;
```

#### Read Data Channel (R)

**Purpose**: Transmit read data

**Key Signals**:
```systemverilog
// File: pkg/axi4_pkg.sv (lines 180-200)
typedef struct packed {
    logic [DATA_WIDTH-1:0] rdata;       // Read data
    logic [1:0]           rresp;       // Response type
    logic                 rlast;       // Last transfer in burst
    logic [ID_WIDTH-1:0]  rid;         // Transaction ID (matches ARID)
    logic                 rvalid;      // Data valid
    logic                 rready;      // Data ready
} axi4_r_t;
```

#### Burst Types

AXI4 supports three burst types:

**1. FIXED Burst** (`awburst = 2'b00`)
- Address remains constant
- Used for repeated access to same location
- Example: Filling FIFO

**2. INCR Burst** (`awburst = 2'b01`)
- Address increments by burst size
- Most common burst type
- Example: Sequential memory access

**3. WRAP Burst** (`awburst = 2'b10`)
- Address wraps at boundary
- Used for cache line fills
- Example: Cache line = 64 bytes, wrap at 64-byte boundary

**Burst Type Comparison**:

| Burst Type | Address Behavior | Use Case |
|------------|------------------|----------|
| FIXED | Constant | FIFO access |
| INCR | Increments | Sequential memory |
| WRAP | Wraps at boundary | Cache line fill |

#### Burst Lengths

**Range**: 1 to 256 transfers

**Encoding**: `awlen[7:0]` represents (length - 1)

**Examples**:
- `awlen = 0`: 1 transfer (single beat)
- `awlen = 3`: 4 transfers (4-beat burst)
- `awlen = 255`: 256 transfers (maximum burst)

**Burst Length Selection**:
```systemverilog
// File: tb/sequences/axi4_seq.sv (lines 100-120)
function void randomize_burst_length();
    // Prefer longer bursts for efficiency
    if (burst_type == INCR) begin
        awlen = $urandom_range(7, 15);  // 8-16 transfers
    end else if (burst_type == WRAP) begin
        awlen = 7;  // Cache line: 8 transfers × 8 bytes = 64 bytes
    end else begin
        awlen = $urandom_range(0, 3);  // Short bursts for FIXED
    end
endfunction
```

#### Transaction IDs

**Purpose**: Tag transactions to support out-of-order completion

**Width**: Typically 4-8 bits (16-256 unique IDs)

**Usage**:
```systemverilog
// File: tb/sequences/axi4_seq.sv (lines 150-180)
task send_multiple_reads();
    for (int i = 0; i < 10; i++) begin
        axi4_transaction tx;
        tx = new();
        tx.arid = i;  // Unique ID per transaction
        tx.araddr = base_addr + (i * 64);
        send_read(tx);
    end
    // Responses can arrive in any order
    // Match by rid == arid
endtask
```

**Out-of-Order Example**:
```
Request Order:  ID=0, ID=1, ID=2, ID=3
Response Order: ID=2, ID=0, ID=3, ID=1  ← Out of order
Master matches responses by ID
```

#### QoS (Quality of Service)

**Purpose**: Indicate transaction priority

**Width**: 4 bits (16 priority levels)

**QoS Values**:
- `0x0`: Lowest priority (background traffic)
- `0x7`: Medium priority (normal traffic)
- `0xF`: Highest priority (real-time traffic)

**QoS Usage in GPU**:
```systemverilog
// File: tb/sequences/gpu_traffic_seq.sv (lines 50-80)
function qos_t get_qos_for_traffic_type(traffic_type_e type);
    case (type)
        GRAPHICS_RENDER:    return 15;  // Highest priority
        COMPUTE_KERNEL:     return 12;  // High priority
        MEMORY_BACKUP:      return 8;   // Medium priority
        CACHE_COHERENCY:    return 10;  // Medium-high priority
        BACKGROUND_TASK:    return 0;   // Lowest priority
        default:            return 7;    // Default priority
    endcase
endfunction
```

**QoS Arbitration**:
```systemverilog
// File: rtl/router.sv (lines 400-430)
function port_id_t arbitrate_by_qos(request_t reqs[]);
    int highest_qos = -1;
    int winner = -1;
    
    for (int i = 0; i < reqs.size(); i++) begin
        if (reqs[i].valid && reqs[i].qos > highest_qos) begin
            highest_qos = reqs[i].qos;
            winner = i;
        end
    end
    
    return winner;
endfunction
```

#### Region Signals

**Purpose**: Support multiple address regions (memory spaces)

**Width**: 4 bits (16 regions)

**Usage**: Different memory controllers, cache regions, etc.

#### AXI4 Transaction Examples

**Example 1: Simple Write Transaction**

```systemverilog
// File: tb/sequences/axi4_seq.sv (lines 200-230)
task simple_write();
    axi4_transaction tx;
    tx = new();
    
    // Write Address
    tx.awaddr = 32'h1000_0000;
    tx.awlen = 0;        // Single transfer
    tx.awsize = 2'b010;  // 4 bytes
    tx.awburst = INCR;
    tx.awid = 5;
    tx.awqos = 8;
    
    // Write Data
    tx.wdata[0] = 32'hDEAD_BEEF;
    tx.wstrb = 4'hF;
    tx.wlast = 1;
    
    // Execute transaction
    send_write(tx);
    
    // Wait for response
    wait_for_write_response(tx.awid);
endtask
```

**Example 2: Read with Burst**

```systemverilog
// File: tb/sequences/axi4_seq.sv (lines 250-280)
task read_burst();
    axi4_transaction tx;
    tx = new();
    
    // Read Address
    tx.araddr = 32'h2000_0000;
    tx.arlen = 7;        // 8 transfers
    tx.arsize = 2'b011;  // 8 bytes per transfer
    tx.arburst = INCR;
    tx.arid = 10;
    
    // Total: 8 × 8 = 64 bytes read
    
    // Execute transaction
    send_read(tx);
    
    // Collect responses (may arrive out of order)
    for (int i = 0; i < 8; i++) begin
        axi4_r_t rdata;
        wait_for_read_data(tx.arid, rdata);
        $display("Read data[%0d]: 0x%x", i, rdata.rdata);
    end
endtask
```

**Example 3: Atomic Operations**

```systemverilog
// File: tb/sequences/atomic_seq.sv (lines 50-100)
task atomic_compare_and_swap();
    axi4_transaction tx;
    tx = new();
    
    // Atomic operation uses special signals
    tx.awaddr = 32'h3000_0000;
    tx.awlen = 0;
    tx.awsize = 2'b010;  // 4 bytes
    tx.awlock = 1;      // Exclusive access
    tx.awid = 20;
    
    // Compare-and-swap: if (mem == old_val) mem = new_val
    tx.wdata[0] = new_value;
    tx.wdata[1] = old_value;  // Compare value
    
    send_atomic(tx);
    
    // Response indicates success/failure
    wait_for_write_response(tx.awid);
endtask
```

### ACE-Lite for I/O Coherency

ACE-Lite (AXI Coherency Extensions Lite) extends AXI4 to support cache coherency for I/O masters (like DMA engines) accessing GPU caches.

#### ACE-Lite Overview

**Purpose**: Allow I/O masters to access cached data coherently

**Key Difference from Full ACE**: 
- **ACE-Lite**: One-way coherency (I/O → CPU/GPU)
- **Full ACE**: Two-way coherency (CPU ↔ GPU)

#### Cache Stashing (Snoop for Coherent Reads)

**Mechanism**: When I/O master reads data, system snoops caches to get latest data

**Process**:
```
1. I/O Master issues read request
2. System snoops GPU caches
3. If cache hit: Data forwarded from cache
4. If cache miss: Data fetched from memory
5. Data returned to I/O master
```

**ACE-Lite Signals**:
```systemverilog
// File: pkg/ace_lite_pkg.sv (lines 50-100)
typedef struct packed {
    // Standard AXI4 signals
    axi4_ar_t ar;
    
    // ACE-Lite extensions
    logic [3:0]  arsnoop;    // Snoop type
    logic [3:0]  ardomain;   // Domain (inner/outer)
    logic [1:0]  arbar;      // Barrier type
} ace_lite_ar_t;

// Snoop Types
typedef enum logic [3:0] {
    READ_NO_SNOOP     = 4'b0000,
    READ_ONCE          = 4'b0001,
    READ_SHARED        = 4'b0010,
    READ_CLEAN         = 4'b0011,
    READ_NOT_SHARED_DIRTY = 4'b0100
} ace_snoop_type_t;
```

#### One-Way Coherency

**Definition**: I/O master can snoop GPU caches, but GPU cannot snoop I/O master

**Why**: I/O masters typically don't have caches (or have simple buffers)

**Use Case**: DMA engine reading from GPU memory
```
DMA Engine → Read Request → Snoop GPU Caches → Get Latest Data → DMA Engine
```

**Implementation**:
```systemverilog
// File: rtl/coherency_controller.sv (lines 150-200)
task handle_ace_lite_read(ace_lite_ar_t ar);
    // Check if snoop required
    if (ar.arsnoop != READ_NO_SNOOP) begin
        // Snoop GPU caches
        snoop_request_t snoop;
        snoop.addr = ar.araddr;
        snoop.type = ar.arsnoop;
        
        // Broadcast snoop to all caches
        broadcast_snoop(snoop);
        
        // Collect snoop responses
        wait_for_snoop_responses();
        
        // Return coherent data
        return_coherent_data();
    end else begin
        // No coherency needed, direct memory access
        return_memory_data();
    end
endtask
```

#### DMA Engine Use Case

**Scenario**: DMA engine copying data from GPU memory to system memory

**Without ACE-Lite**:
```
1. DMA reads from GPU memory
2. Gets stale data (if GPU cache has newer data)
3. Data corruption possible
```

**With ACE-Lite**:
```
1. DMA reads from GPU memory
2. System snoops GPU caches
3. Gets latest data (from cache or memory)
4. Data integrity guaranteed
```

**Code Example**:
```systemverilog
// File: tb/sequences/dma_seq.sv (lines 50-100)
task dma_coherent_read();
    ace_lite_transaction tx;
    tx = new();
    
    // DMA read with coherency
    tx.araddr = gpu_memory_addr;
    tx.arlen = 15;              // 16 transfers
    tx.arsnoop = READ_SHARED;   // Snoop for shared data
    tx.ardomain = INNER;        // Inner cacheable domain
    
    send_ace_lite_read(tx);
    
    // Receive coherent data
    for (int i = 0; i < 16; i++) begin
        ace_lite_r_t rdata;
        wait_for_read_data(tx.arid, rdata);
        dma_buffer[i] = rdata.rdata;
    end
endtask
```

### QoS and Real-Time

#### QoS Field: 4-Bit Priority

**Range**: 0 (lowest) to 15 (highest)

**Encoding**: Higher value = higher priority

**QoS Distribution**:
```
Priority 15: Critical real-time (graphics rendering)
Priority 12-14: High priority (compute kernels)
Priority 8-11: Medium priority (normal traffic)
Priority 4-7: Low priority (background tasks)
Priority 0-3: Best effort (idle traffic)
```

#### Priority-Based Arbitration

**Arbitration Policy**: Higher QoS always wins

**Implementation**:
```systemverilog
// File: rtl/router.sv (lines 450-480)
function int priority_arbitrate(request_t reqs[]);
    int max_qos = -1;
    int winner = -1;
    
    // Find highest priority request
    for (int i = 0; i < reqs.size(); i++) begin
        if (reqs[i].valid && reqs[i].qos > max_qos) begin
            max_qos = reqs[i].qos;
            winner = i;
        end
    end
    
    // If tie, use round-robin
    if (winner == -1) begin
        winner = round_robin_arbitrate(reqs);
    end
    
    return winner;
endfunction
```

**Arbitration Example**:
```
Request Queue:
- Req0: QoS=8,  Addr=0x1000
- Req1: QoS=12, Addr=0x2000  ← Wins (highest QoS)
- Req2: QoS=5,  Addr=0x3000
- Req3: QoS=12, Addr=0x4000  ← Tie-breaker needed

Result: Req1 granted first (or Req3 if round-robin)
```

#### GPU Application QoS Usage

**1. Graphics Rendering** (QoS = 15)
- **Requirement**: Must complete within frame time (16.67ms @ 60 FPS)
- **Latency Budget**: <1ms per frame
- **Traffic Pattern**: High bandwidth, predictable

**2. Compute Kernels** (QoS = 12)
- **Requirement**: Good performance, but can tolerate some latency
- **Latency Budget**: <10ms for real-time inference
- **Traffic Pattern**: Bursty, high bandwidth

**3. Memory Operations** (QoS = 8)
- **Requirement**: Background memory management
- **Latency Budget**: No strict requirement
- **Traffic Pattern**: Continuous, low priority

**4. Cache Coherency** (QoS = 10)
- **Requirement**: Must complete to maintain consistency
- **Latency Budget**: <100ns for critical paths
- **Traffic Pattern**: Sparse, but time-sensitive

**QoS Assignment Code**:
```systemverilog
// File: tb/sequences/gpu_app_seq.sv (lines 100-150)
function qos_t assign_qos(app_type_e app_type);
    case (app_type)
        GRAPHICS_RENDER:
            return 15;  // Highest priority
        COMPUTE_INFERENCE:
            return 12;  // High priority
        TRAINING_BATCH:
            return 10;  // Medium-high priority
        MEMORY_BACKUP:
            return 8;   // Medium priority
        CACHE_COHERENCY:
            return 10;  // Medium-high priority
        BACKGROUND_TASK:
            return 0;   // Lowest priority
        default:
            return 7;   // Default
    endcase
endfunction
```

#### Real-Time Guarantees

**Latency Bounds**: QoS ensures bounded latency for high-priority traffic

**Example**: Graphics frame timing
```
Frame Time: 16.67 ms
├── Geometry: 4 ms
├── Rasterization: 3 ms
├── Pixel Shading: 6 ms
├── Memory Access: 2 ms  ← NoC must complete in <2ms
└── Display: 1.67 ms

NoC Latency Budget:
- High-priority (QoS 15): <100ns per hop
- Medium-priority (QoS 8-12): <500ns per hop
- Low-priority (QoS 0-7): Best effort
```

**Verification**: Ensure high-priority traffic meets latency requirements
```systemverilog
// File: tb/monitors/performance_monitor.sv (lines 200-250)
task check_latency_requirements();
    foreach (transactions[i]) begin
        if (transactions[i].qos >= 15) begin
            // High-priority: must complete in <100ns
            assert (transactions[i].latency < 100) else
                `uvm_error("PERF", $sformatf(
                    "High-priority transaction exceeded latency: %0d ns",
                    transactions[i].latency
                ));
        end
    end
endtask
```

---

## UVM Verification Architecture

### Testbench Hierarchy

The UVM testbench follows a layered architecture that separates concerns and enables reuse.

#### Complete Testbench Hierarchy

```
┌─────────────────────────────────────────────────────────┐
│                    Test Layer                            │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐  │
│  │ simple_test  │  │ random_test  │  │ stress_test  │  │
│  └──────────────┘  └──────────────┘  └──────────────┘  │
└─────────────────────────────────────────────────────────┘
                          │
┌─────────────────────────────────────────────────────────┐
│                  Environment Layer                       │
│  ┌──────────────────────────────────────────────────┐  │
│  │              noc_env (uvm_env)                   │  │
│  │  ┌──────────────┐      ┌──────────────┐         │  │
│  │  │ master_agent│      │ slave_agent  │         │  │
│  │  └──────────────┘      └──────────────┘         │  │
│  │  ┌──────────────┐      ┌──────────────┐         │  │
│  │  │ scoreboard  │      │ coverage     │         │  │
│  │  └──────────────┘      └──────────────┘         │  │
│  │  ┌──────────────────────────────────────────┐  │  │
│  │  │    virtual_sequencer                     │  │  │
│  │  └──────────────────────────────────────────┘  │  │
│  └──────────────────────────────────────────────────┘  │
└─────────────────────────────────────────────────────────┘
                          │
┌─────────────────────────────────────────────────────────┐
│                    Agent Layer                           │
│  ┌──────────────────────────────────────────────────┐  │
│  │          noc_agent (uvm_agent)                   │  │
│  │  ┌──────────┐  ┌──────────┐  ┌──────────┐      │  │
│  │  │ driver   │  │ monitor  │  │sequencer │      │  │
│  │  └──────────┘  └──────────┘  └──────────┘      │  │
│  └──────────────────────────────────────────────────┘  │
└─────────────────────────────────────────────────────────┘
                          │
┌─────────────────────────────────────────────────────────┐
│                  Interface Layer                        │
│  ┌──────────────────────────────────────────────────┐  │
│  │              noc_if (SystemVerilog interface)    │  │
│  └──────────────────────────────────────────────────┘  │
└─────────────────────────────────────────────────────────┘
                          │
┌─────────────────────────────────────────────────────────┐
│                    DUT Layer                            │
│  ┌──────────────────────────────────────────────────┐  │
│  │              noc_top (RTL Design)                │  │
│  └──────────────────────────────────────────────────┘  │
└─────────────────────────────────────────────────────────┘
```

#### Top-Level Testbench

```systemverilog
// File: tb/top.sv (lines 1-50)
module noc_top_tb;
    import uvm_pkg::*;
    import noc_pkg::*;
    
    // Clock and Reset
    bit clk;
    bit rst_n;
    
    // NoC Interface
    noc_if vif(clk, rst_n);
    
    // DUT Instantiation
    noc_top dut (
        .clk(clk),
        .rst_n(rst_n),
        .noc_if(vif)
    );
    
    // Clock Generation
    initial begin
        clk = 0;
        forever #5ns clk = ~clk;
    end
    
    // Reset Generation
    initial begin
        rst_n = 0;
        #100ns;
        rst_n = 1;
    end
    
    // UVM Test Execution
    initial begin
        // Set interface in config database
        uvm_config_db#(virtual noc_if)::set(null, "*", "vif", vif);
        
        // Run test
        run_test();
    end
endmodule
```

### Master Agents

Master agents generate stimulus and drive transactions onto the NoC.

#### Master Agent Structure

```systemverilog
// File: tb/agents/noc_master_agent.sv (lines 1-100)
class noc_master_agent extends uvm_agent;
    `uvm_component_utils(noc_master_agent)
    
    // Components
    noc_master_driver    driver;
    noc_master_monitor  monitor;
    noc_master_sequencer sequencer;
    
    // Configuration
    noc_agent_config cfg;
    
    function new(string name = "noc_master_agent", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Get configuration
        if (!uvm_config_db#(noc_agent_config)::get(this, "", "cfg", cfg)) begin
            `uvm_fatal("CFG", "No agent config found")
        end
        
        // Build components based on agent type
        if (cfg.is_active == UVM_ACTIVE) begin
            driver = noc_master_driver::type_id::create("driver", this);
            sequencer = noc_master_sequencer::type_id::create("sequencer", this);
        end
        
        monitor = noc_master_monitor::type_id::create("monitor", this);
    endfunction
    
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        
        if (cfg.is_active == UVM_ACTIVE) begin
            driver.seq_item_port.connect(sequencer.seq_item_export);
        end
    endfunction
endclass
```

#### Master Driver

**Purpose**: Drive transactions onto NoC interface

**Key Responsibilities**:
1. Receive transactions from sequencer
2. Convert transactions to signal-level protocol
3. Drive signals on interface
4. Handle handshaking

```systemverilog
// File: tb/agents/noc_master_driver.sv (lines 50-150)
class noc_master_driver extends uvm_driver #(noc_transaction);
    `uvm_component_utils(noc_master_driver)
    
    virtual noc_if vif;
    noc_agent_config cfg;
    
    function new(string name = "noc_master_driver", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        forever begin
            noc_transaction tx;
            
            // Get transaction from sequencer
            seq_item_port.get_next_item(tx);
            
            // Drive transaction
            drive_transaction(tx);
            
            // Signal completion
            seq_item_port.item_done();
        end
    endtask
    
    virtual task drive_transaction(noc_transaction tx);
        // Drive address phase
        @(posedge vif.clk);
        vif.awvalid <= 1;
        vif.awaddr <= tx.addr;
        vif.awlen <= tx.len;
        vif.awsize <= tx.size;
        vif.awburst <= tx.burst;
        vif.awid <= tx.id;
        vif.awqos <= tx.qos;
        
        // Wait for ready
        do @(posedge vif.clk);
        while (!vif.awready);
        
        // Drive data phase
        for (int i = 0; i <= tx.len; i++) begin
            @(posedge vif.clk);
            vif.wvalid <= 1;
            vif.wdata <= tx.data[i];
            vif.wstrb <= tx.strb[i];
            vif.wlast <= (i == tx.len);
            
            do @(posedge vif.clk);
            while (!vif.wready);
        end
        
        vif.awvalid <= 0;
        vif.wvalid <= 0;
    endtask
endclass
```

#### Master Monitor

**Purpose**: Observe NoC traffic and create transactions

**Key Responsibilities**:
1. Monitor interface signals
2. Reconstruct transactions from signals
3. Send transactions to analysis port

```systemverilog
// File: tb/agents/noc_master_monitor.sv (lines 50-150)
class noc_master_monitor extends uvm_monitor;
    `uvm_component_utils(noc_master_monitor)
    
    uvm_analysis_port #(noc_transaction) ap;
    virtual noc_if vif;
    
    function new(string name = "noc_master_monitor", uvm_component parent = null);
        super.new(name, parent);
        ap = new("ap", this);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        forever begin
            noc_transaction tx;
            
            // Monitor address phase
            @(posedge vif.clk);
            if (vif.awvalid && vif.awready) begin
                tx = noc_transaction::type_id::create("tx");
                tx.addr = vif.awaddr;
                tx.len = vif.awlen;
                tx.size = vif.awsize;
                tx.burst = vif.awburst;
                tx.id = vif.awid;
                tx.qos = vif.awqos;
                
                // Monitor data phase
                for (int i = 0; i <= tx.len; i++) begin
                    @(posedge vif.clk);
                    if (vif.wvalid && vif.wready) begin
                        tx.data[i] = vif.wdata;
                        tx.strb[i] = vif.wstrb;
                        if (vif.wlast) break;
                    end
                end
                
                // Send to analysis port
                ap.write(tx);
            end
        end
    endtask
endclass
```

### Slave Agents

Slave agents generate responses to incoming transactions.

#### Slave Agent Structure

Similar to master agent, but generates responses instead of requests.

```systemverilog
// File: tb/agents/noc_slave_agent.sv (lines 1-100)
class noc_slave_agent extends uvm_agent;
    `uvm_component_utils(noc_slave_agent)
    
    noc_slave_driver    driver;
    noc_slave_monitor   monitor;
    noc_slave_sequencer sequencer;
    
    // Similar structure to master agent
    // ...
endclass
```

#### Slave Driver

**Purpose**: Generate responses to incoming requests

```systemverilog
// File: tb/agents/noc_slave_driver.sv (lines 50-150)
class noc_slave_driver extends uvm_driver #(noc_response);
    `uvm_component_utils(noc_slave_driver)
    
    virtual task run_phase(uvm_phase phase);
        forever begin
            // Monitor for incoming requests
            @(posedge vif.clk);
            if (vif.awvalid) begin
                // Generate response
                noc_response resp;
                resp = generate_response(vif.awid);
                
                // Drive response
                drive_response(resp);
            end
        end
    endtask
endclass
```

### Scoreboard

**Purpose**: Verify correctness by comparing sent vs received transactions

#### Scoreboard Implementation

```systemverilog
// File: tb/scoreboards/noc_scoreboard.sv (lines 1-200)
class noc_scoreboard extends uvm_scoreboard;
    `uvm_component_utils(noc_scoreboard)
    
    // Analysis ports from monitors
    uvm_analysis_imp #(noc_transaction, noc_scoreboard) master_imp;
    uvm_analysis_imp #(noc_transaction, noc_scoreboard) slave_imp;
    
    // Transaction queues
    noc_transaction master_tx_queue[$];
    noc_transaction slave_tx_queue[$];
    
    // Statistics
    int tx_sent = 0;
    int tx_received = 0;
    int tx_mismatch = 0;
    
    function new(string name = "noc_scoreboard", uvm_component parent = null);
        super.new(name, parent);
        master_imp = new("master_imp", this);
        slave_imp = new("slave_imp", this);
    endfunction
    
    // Write from master monitor
    virtual function void write_master(noc_transaction tx);
        master_tx_queue.push_back(tx);
        tx_sent++;
        check_transactions();
    endfunction
    
    // Write from slave monitor
    virtual function void write_slave(noc_transaction tx);
        slave_tx_queue.push_back(tx);
        tx_received++;
        check_transactions();
    endfunction
    
    // Check for matching transactions
    function void check_transactions();
        noc_transaction master_tx, slave_tx;
        
        foreach (master_tx_queue[i]) begin
            foreach (slave_tx_queue[j]) begin
                if (master_tx_queue[i].id == slave_tx_queue[j].id) begin
                    master_tx = master_tx_queue[i];
                    slave_tx = slave_tx_queue[j];
                    
                    // Compare transactions
                    if (!master_tx.compare(slave_tx)) begin
                        `uvm_error("SCOREBOARD", $sformatf(
                            "Transaction mismatch: ID=%0d", master_tx.id
                        ));
                        tx_mismatch++;
                    end
                    
                    // Remove matched transactions
                    master_tx_queue.delete(i);
                    slave_tx_queue.delete(j);
                    break;
                end
            end
        end
    endfunction
    
    virtual function void report_phase(uvm_phase phase);
        `uvm_info("SCOREBOARD", $sformatf(
            "Transactions Sent: %0d, Received: %0d, Mismatches: %0d",
            tx_sent, tx_received, tx_mismatch
        ), UVM_MEDIUM);
    endfunction
endclass
```

### Coverage

**Purpose**: Measure verification completeness

#### Coverage Groups

```systemverilog
// File: tb/coverage/noc_coverage.sv (lines 1-200)
class noc_coverage extends uvm_subscriber #(noc_transaction);
    `uvm_component_utils(noc_coverage)
    
    noc_transaction tx;
    
    // Coverage groups
    covergroup protocol_cg;
        packet_type: coverpoint tx.packet_type {
            bins READ = {READ};
            bins WRITE = {WRITE};
            bins ATOMIC = {ATOMIC};
        }
        
        burst_type: coverpoint tx.burst_type {
            bins FIXED = {FIXED};
            bins INCR = {INCR};
            bins WRAP = {WRAP};
        }
        
        burst_length: coverpoint tx.len {
            bins SHORT = {[0:7]};
            bins MEDIUM = {[8:15]};
            bins LONG = {[16:255]};
        }
        
        qos_level: coverpoint tx.qos {
            bins LOW = {[0:3]};
            bins MEDIUM = {[4:11]};
            bins HIGH = {[12:15]};
        }
        
        // Cross coverage
        type_x_length: cross packet_type, burst_length;
        type_x_qos: cross packet_type, qos_level;
    endgroup
    
    function new(string name = "noc_coverage", uvm_component parent = null);
        super.new(name, parent);
        protocol_cg = new();
    endfunction
    
    virtual function void write(noc_transaction t);
        tx = t;
        protocol_cg.sample();
    endfunction
endclass
```

### Sequence Library

#### Base Sequence

```systemverilog
// File: tb/sequences/noc_base_sequence.sv (lines 1-100)
class noc_base_sequence extends uvm_sequence #(noc_transaction);
    `uvm_object_utils(noc_base_sequence)
    
    function new(string name = "noc_base_sequence");
        super.new(name);
    endfunction
    
    virtual task body();
        `uvm_fatal("SEQ", "Base sequence body() must be overridden")
    endtask
endclass
```

#### Basic Sequences

```systemverilog
// File: tb/sequences/noc_simple_seq.sv (lines 1-80)
class noc_simple_sequence extends noc_base_sequence;
    `uvm_object_utils(noc_simple_sequence)
    
    task body();
        noc_transaction tx;
        
        repeat(10) begin
            tx = noc_transaction::type_id::create("tx");
            start_item(tx);
            assert(tx.randomize() with {
                len == 0;  // Single transfer
            });
            finish_item(tx);
        end
    endtask
endclass
```

#### Advanced Sequences

```systemverilog
// File: tb/sequences/noc_advanced_seq.sv (lines 1-150)
class noc_advanced_sequence extends noc_base_sequence;
    `uvm_object_utils(noc_advanced_sequence)
    
    task body();
        // Burst transactions
        send_burst_transactions();
        
        // Out-of-order transactions
        send_oo_transactions();
        
        // QoS priority transactions
        send_qos_transactions();
    endtask
    
    task send_burst_transactions();
        // Implementation
    endtask
endclass
```

### Analysis Port Architecture

**Purpose**: Enable communication between components without direct references

**Architecture**:
```
Monitor → Analysis Port → Scoreboard
Monitor → Analysis Port → Coverage
Monitor → Analysis Port → Performance Monitor
```

**Benefits**:
1. **Decoupling**: Components don't need direct references
2. **Flexibility**: Easy to add/remove subscribers
3. **Reusability**: Components can be reused in different environments

---

## Deadlock Prevention in Verification

### Why Deadlock Matters

#### Deadlock Impact

**System Hang**: Deadlock causes complete system freeze

**Undetectable in Small Sims**: Deadlock may not occur in small simulations but appears in production

**Example**: 
```
Small simulation (4 nodes): No deadlock observed
Production system (512 nodes): Deadlock after 1 hour
```

#### Deadlock Scenarios

**1. Circular Dependency**
```
Router A waits for Router B
Router B waits for Router C
Router C waits for Router A
→ Deadlock
```

**2. Resource Exhaustion**
```
All buffers full
No packets can move
→ Deadlock
```

**3. Protocol Deadlock**
```
Request waiting for response
Response waiting for request
→ Deadlock
```

### XY Routing Proof: Why It's Deadlock-Free

#### Formal Proof

**Theorem**: XY routing is deadlock-free for mesh topologies.

**Proof**:

1. **Partial Ordering**: XY routing creates partial order
   - All packets route X dimension first
   - Then route Y dimension
   - Creates DAG (no cycles)

2. **No Circular Dependencies**: 
   - If packet P1 depends on P2, and P2 depends on P3
   - Then P1 depends on P3
   - But P3 cannot depend on P1 (would create cycle)
   - Therefore, no circular dependencies

3. **Formal Verification**: 
   ```systemverilog
   // File: verif/formal/deadlock_properties.sv (lines 1-50)
   property no_deadlock;
       @(posedge clk) disable iff (!rst_n)
       (packet_in_transit |-> ##[1:MAX_LATENCY] packet_completed);
   endproperty
   
   assert_no_deadlock: assert property (no_deadlock)
       else `uvm_error("FORMAL", "Deadlock detected");
   ```

### Virtual Channel Allocation

#### VC Allocation Strategy

**Purpose**: Prevent deadlock when using adaptive routing

**Strategy**: Separate VCs for different traffic types

```systemverilog
// File: rtl/router.sv (lines 500-550)
function vc_id_t allocate_vc(
    port_id_t output_port,
    traffic_type_t type
);
    case (type)
        REQUEST:  return allocate_vc_request(output_port);
        RESPONSE: return allocate_vc_response(output_port);
        COHERENCY: return allocate_vc_coherency(output_port);
        default:  return allocate_vc_default(output_port);
    endcase
endfunction
```

#### Deadlock Prevention Rules

1. **Separate VCs**: Requests and responses use different VCs
2. **Ordered Channels**: Maintain ordering within VC
3. **Credit Management**: Ensure credits available before sending

### Formal Verification of Deadlock Freedom

#### Property Specification

```systemverilog
// File: verif/formal/deadlock_properties.sv (lines 50-150)
// Property 1: No circular wait
property no_circular_wait;
    @(posedge clk) disable iff (!rst_n)
    !(router[0].waiting_for(1) &&
      router[1].waiting_for(2) &&
      router[2].waiting_for(0));
endproperty

// Property 2: Bounded latency
property bounded_latency;
    @(posedge clk) disable iff (!rst_n)
    (packet_injected |-> ##[1:MAX_LATENCY] packet_delivered);
endproperty

// Property 3: Progress guarantee
property progress_guarantee;
    @(posedge clk) disable iff (!rst_n)
    (buffer_not_empty |-> ##[1:10] buffer_decremented);
endproperty
```

#### Formal Tool Integration

```bash
# Run formal verification
make sim_formal FORMAL_TOOL=jaspergold

# Check deadlock properties
formal_tool -property deadlock_properties.sv
```

### Random Traffic Testing

#### Test Strategy

**Goal**: Run 10M+ cycles without deadlock

**Method**: Generate random traffic patterns

```systemverilog
// File: verif/test/deadlock_test.sv (lines 1-100)
class deadlock_test extends noc_base_test;
    `uvm_component_utils(deadlock_test)
    
    task run_phase(uvm_phase phase);
        // Run for 10M cycles
        phase.raise_objection(this);
        
        fork
            // Generate random traffic
            generate_random_traffic();
            
            // Monitor for deadlock
            monitor_deadlock();
        join_any
        
        phase.drop_objection(this);
    endtask
    
    task monitor_deadlock();
        forever begin
            @(posedge vif.clk);
            
            // Check if any packet stuck
            if (packet_latency > MAX_LATENCY) begin
                `uvm_error("DEADLOCK", "Potential deadlock detected")
            end
        end
    endtask
endclass
```

#### Deadlock Detection

**Indicators**:
1. **Packet Latency**: Exceeds maximum expected latency
2. **Buffer Full**: All buffers full, no movement
3. **No Progress**: No packets moving for extended period

**Detection Code**:
```systemverilog
// File: tb/monitors/deadlock_monitor.sv (lines 1-100)
class deadlock_monitor extends uvm_monitor;
    task check_deadlock();
        forever begin
            @(posedge vif.clk);
            
            // Check packet latencies
            foreach (packets[i]) begin
                if (packets[i].age > MAX_AGE) begin
                    `uvm_error("DEADLOCK", $sformatf(
                        "Packet %0d stuck for %0d cycles",
                        packets[i].id, packets[i].age
                    ));
                end
            end
            
            // Check buffer utilization
            if (all_buffers_full()) begin
                `uvm_warning("DEADLOCK", "All buffers full")
            end
        end
    endtask
endclass
```

---

## Performance Monitoring

### Latency Calculation

#### End-to-End Latency

**Definition**: Time from packet injection to packet delivery

**Measurement**:
```systemverilog
// File: tb/monitors/performance_monitor.sv (lines 1-100)
class performance_monitor extends uvm_monitor;
    // Latency tracking
    real latency_sum = 0;
    int latency_count = 0;
    real latency_min = 999999;
    real latency_max = 0;
    
    task measure_latency(noc_transaction tx);
        real start_time, end_time, latency;
        
        start_time = $realtime;
        
        // Wait for transaction completion
        wait_for_completion(tx);
        
        end_time = $realtime;
        latency = end_time - start_time;
        
        // Update statistics
        latency_sum += latency;
        latency_count++;
        if (latency < latency_min) latency_min = latency;
        if (latency > latency_max) latency_max = latency;
    endtask
    
    function real get_average_latency();
        return latency_sum / latency_count;
    endfunction
endclass
```

#### Hop-by-Hop Latency

**Definition**: Latency per router hop

**Measurement**: Track latency at each router

### Throughput Measurement

#### Flits per Cycle

**Definition**: Number of flits transferred per clock cycle

**Calculation**:
```systemverilog
// File: tb/monitors/performance_monitor.sv (lines 100-200)
class performance_monitor;
    int flits_sent = 0;
    int cycles_elapsed = 0;
    
    task measure_throughput();
        forever begin
            @(posedge vif.clk);
            cycles_elapsed++;
            
            if (vif.flit_valid && vif.flit_ready) begin
                flits_sent++;
            end
        end
    endtask
    
    function real get_flits_per_cycle();
        return real'(flits_sent) / real'(cycles_elapsed);
    endfunction
    
    function real get_bandwidth_gbps();
        real flits_per_cycle = get_flits_per_cycle();
        real flit_width_bits = 128;
        real clock_freq_ghz = 1.0;
        return flits_per_cycle * flit_width_bits * clock_freq_ghz / 8.0;
    endfunction
endclass
```

#### GB/s Calculation

**Formula**: `Throughput = (Flits/Cycle) × (Flit Width) × (Clock Frequency) / 8`

**Example**:
- Flits/Cycle: 0.8
- Flit Width: 128 bits
- Clock Frequency: 1 GHz
- Throughput: 0.8 × 128 × 1 / 8 = 12.8 GB/s

### Percentile Latencies

#### P50, P95, P99 Calculation

**Purpose**: Understand latency distribution

**Implementation**:
```systemverilog
// File: tb/monitors/performance_monitor.sv (lines 200-300)
class performance_monitor;
    int latency_samples[$];
    
    function void record_latency(real latency);
        latency_samples.push_back(latency);
    endfunction
    
    function real get_percentile(int percentile);
        int sorted_samples[$];
        int index;
        
        sorted_samples = latency_samples;
        sorted_samples.sort();
        
        index = (percentile * sorted_samples.size()) / 100;
        return sorted_samples[index];
    endfunction
    
    function void report_percentiles();
        `uvm_info("PERF", $sformatf(
            "P50: %0.2f ns, P95: %0.2f ns, P99: %0.2f ns",
            get_percentile(50),
            get_percentile(95),
            get_percentile(99)
        ), UVM_MEDIUM);
    endfunction
endclass
```

### Performance Counters and Histograms

#### Counter Implementation

```systemverilog
// File: tb/monitors/performance_monitor.sv (lines 300-400)
class performance_monitor;
    // Counters
    int packets_injected = 0;
    int packets_delivered = 0;
    int packets_dropped = 0;
    int buffer_overflows = 0;
    
    // Histogram
    int latency_histogram[real];
    
    function void update_counters();
        // Update based on observed events
    endfunction
    
    function void update_histogram(real latency);
        int bin = latency / 10.0;  // 10ns bins
        latency_histogram[bin]++;
    endfunction
endclass
```

### Interpreting Performance Curves

#### Latency vs Load

**Typical Curve**:
```
Latency
  ↑
  │     ┌───────
  │    ╱
  │   ╱
  │  ╱
  │ ╱
  │╱
  └────────────────→ Load
     Low        High
```

**Interpretation**:
- **Low Load**: Low latency, linear relationship
- **High Load**: Latency increases exponentially
- **Saturation**: System cannot handle more load

#### Throughput vs Load

**Typical Curve**:
```
Throughput
  ↑
  │     ────────
  │    ╱
  │   ╱
  │  ╱
  │ ╱
  └────────────────→ Load
     Low        High
```

**Interpretation**:
- **Low Load**: Throughput increases linearly
- **High Load**: Throughput saturates
- **Peak**: Maximum achievable throughput

---

## File Organization

### Directory Structure

```
noc-verification/
├── rtl/                          # RTL Design Files
│   ├── router.sv                 # Router implementation
│   ├── link.sv                   # Link implementation
│   ├── arbiter.sv                # Arbitration logic
│   ├── crossbar.sv               # Crossbar switch
│   └── noc_top.sv                # Top-level NoC
│
├── verif/                        # Verification Files
│   ├── tb/                       # Testbench Components
│   │   ├── agents/               # UVM Agents
│   │   │   ├── noc_master_agent.sv
│   │   │   ├── noc_slave_agent.sv
│   │   │   └── noc_driver.sv
│   │   ├── env/                  # Environment
│   │   │   ├── noc_env.sv
│   │   │   └── noc_config.sv
│   │   ├── scoreboards/          # Scoreboards
│   │   │   └── noc_scoreboard.sv
│   │   ├── monitors/             # Monitors
│   │   │   ├── noc_monitor.sv
│   │   │   └── performance_monitor.sv
│   │   └── top.sv                # Testbench top
│   │
│   ├── seq/                      # Sequences
│   │   ├── noc_base_sequence.sv
│   │   ├── noc_simple_seq.sv
│   │   ├── noc_random_seq.sv
│   │   └── noc_stress_seq.sv
│   │
│   ├── test/                     # Test Cases
│   │   ├── noc_base_test.sv
│   │   ├── simple_test.sv
│   │   ├── random_test.sv
│   │   └── stress_test.sv
│   │
│   ├── cov/                      # Coverage
│   │   ├── noc_coverage.sv
│   │   └── coverage_groups.sv
│   │
│   └── formal/                   # Formal Verification
│       ├── deadlock_properties.sv
│       └── protocol_properties.sv
│
├── pkg/                          # Packages
│   ├── noc_pkg.sv                # NoC package
│   ├── axi4_pkg.sv               # AXI4 package
│   └── ace_lite_pkg.sv           # ACE-Lite package
│
├── config/                       # Configuration Files
│   ├── noc_config.sv
│   └── test_config.sv
│
├── doc/                          # Documentation
│   ├── ARCHITECTURE.md           # This file
│   ├── README.md
│   └── CONTRIBUTING.md
│
├── sim/                          # Simulation Scripts
│   ├── compile.tcl
│   ├── run.tcl
│   └── results/                  # Simulation Results
│
├── scripts/                      # Utility Scripts
│   ├── coverage_analysis.py
│   └── performance_analysis.py
│
├── Makefile                      # Build System
├── setup.sh                      # Environment Setup
└── README.md                     # Project README
```

### RTL Directory (`rtl/`)

**Purpose**: Contains RTL design files (user implements, verification focuses on verifying)

**Files**:
- `router.sv`: Router implementation with XY routing
- `link.sv`: Physical link between routers
- `arbiter.sv`: Arbitration logic for crossbar
- `crossbar.sv`: Crossbar switch implementation
- `noc_top.sv`: Top-level NoC instantiation

**Note**: Verification framework verifies these files but doesn't implement them.

### Verification Testbench (`verif/tb/`)

**Purpose**: UVM testbench components

#### Agents (`verif/tb/agents/`)

- **Master Agents**: Generate stimulus
- **Slave Agents**: Generate responses
- **Drivers**: Drive transactions onto interface
- **Monitors**: Observe interface traffic

#### Environment (`verif/tb/env/`)

- **noc_env.sv**: Top-level UVM environment
- **noc_config.sv**: Configuration objects

#### Scoreboards (`verif/tb/scoreboards/`)

- **noc_scoreboard.sv**: Transaction-level checking

#### Monitors (`verif/tb/monitors/`)

- **noc_monitor.sv**: Protocol monitoring
- **performance_monitor.sv**: Performance metrics

### Sequences (`verif/seq/`)

**Purpose**: UVM sequences for stimulus generation

**Files**:
- `noc_base_sequence.sv`: Base sequence class
- `noc_simple_seq.sv`: Simple directed sequences
- `noc_random_seq.sv`: Constrained random sequences
- `noc_stress_seq.sv`: Stress test sequences

### Tests (`verif/test/`)

**Purpose**: UVM test cases

**Files**:
- `noc_base_test.sv`: Base test class
- `simple_test.sv`: Simple directed test
- `random_test.sv`: Random test
- `stress_test.sv`: Stress test

### Coverage (`verif/cov/`)

**Purpose**: Coverage models

**Files**:
- `noc_coverage.sv`: Coverage groups
- `coverage_groups.sv`: Additional coverage groups

### Formal Verification (`verif/formal/`)

**Purpose**: Formal verification properties

**Files**:
- `deadlock_properties.sv`: Deadlock prevention properties
- `protocol_properties.sv`: Protocol compliance properties

### Documentation (`doc/`)

**Purpose**: Project documentation

**Files**:
- `ARCHITECTURE.md`: This file
- `README.md`: Project overview
- `CONTRIBUTING.md`: Contribution guidelines

### Simulation Scripts (`sim/`)

**Purpose**: Simulation control scripts

**Files**:
- `compile.tcl`: Compilation script
- `run.tcl`: Simulation run script
- `results/`: Simulation results directory

### Packages (`pkg/`)

**Purpose**: SystemVerilog packages

**Files**:
- `noc_pkg.sv`: NoC-specific types and classes
- `axi4_pkg.sv`: AXI4 protocol definitions
- `ace_lite_pkg.sv`: ACE-Lite protocol definitions

---

## Conclusion

This architecture document provides a comprehensive overview of the GPU Interconnect NoC Verification Framework. The framework is designed to verify complex NoC designs used in modern GPUs, ensuring correctness, performance, and reliability.

**Key Takeaways**:

1. **NoC Fundamentals**: Understanding mesh topology, XY routing, and router architecture is essential
2. **Protocol Support**: AXI4 and ACE-Lite protocols enable high-performance, coherent communication
3. **UVM Architecture**: Layered testbench enables reuse and scalability
4. **Deadlock Prevention**: XY routing and virtual channels prevent deadlock
5. **Performance Monitoring**: Comprehensive metrics ensure design meets requirements
6. **File Organization**: Clear structure enables maintainability and collaboration

For questions or contributions, please refer to [CONTRIBUTING.md](./CONTRIBUTING.md).

---

**Last Updated**: January 2025  
**Version**: 1.0.0  
**Status**: Production Ready

