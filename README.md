# RV32IM Five-Stage Pipelined RISC-V Processor
Testing manual is in section 7


## 1. Features

- Full RV32I base instruction set
- RV32M extension with pipelined divider
- Classic five-stage pipeline architecture
- Full data forwarding (MX, WX, WD, WM)
- Load–use hazard detection and stalling
- Branch handling with pipeline flush
- Synthesizable on Xilinx ARTY-Z7 (Zynq-7000)

---

## 2. ISA Support

### 2.1 RV32I
- Arithmetic: `add`, `sub`, `addi`
- Logical: `and`, `or`, `xor`
- Shift: `sll`, `srl`, `sra`
- Comparison: `slt`, `sltu`
- Memory access: `lw`, `sw`, `sb`
- Control flow: `beq`, `bne`, `jal`, `jalr`, `lui`

### 2.2 RV32M
- Multiply: `mul`, `mulh`, `mulhu`
- Divide: `div`, `divu`
- Remainder: `rem`, `remu`

---

## 3. Overall Architecture

The processor follows the classic RISC pipeline organization:

| Stage | Name | Function |
|-----|------|---------|
| IF | Instruction Fetch | Instruction fetch and PC update |
| ID | Instruction Decode | Decode and register read |
| EX | Execute | ALU operation, branch decision |
| MEM | Memory | Load and store access |
| WB | Write Back | Register writeback |

---

## 4. Top-Level Modules

### 4.1 Processor
Top-level module for simulation.
- Instantiates the pipelined datapath and unified memory
- Exposes PC and instruction trace at the Writeback stage

### 4.2 DatapathPipelined
Implements the five-stage RV32IM pipeline:
- Register file
- Pipeline registers
- ALU with carry look-ahead adder
- Hazard detection and forwarding
- Sidecar pipelined divider for RV32M

### 4.3 Memory
- Unified instruction/data memory (can be seperated via simple configuring)
- 32-bit word-addressable

### 4.4 Supporting Modules
- `RegFile`: Register file with internal WD bypass
- `cla`: 32-bit carry look-ahead adder
- `DividerPipelined`: 8-stage pipelined divider

---

## 5. Forwarding and Hazard Handling

### 5.1 Forwarding Paths
To minimize stalls, the following forwarding paths are implemented:

| Path | Description |
|----|------------|
| MX | Memory stage to Execute stage |
| WX | Writeback stage to Execute stage |
| WD | Writeback stage to Decode stage |
| WM | Load data forwarded to Store data |

### 5.2 Load–Use Hazard
A load–use hazard is detected when:
- A load instruction is in the Execute stage
- The following instruction in Decode uses the loaded destination register

In this case, the pipeline stalls for one cycle and inserts a bubble into the Execute stage.

---

## 6. RV32IM Pipelined Divider Integration

### 6.1 Sidecar Divider Architecture
RV32IM divide and remainder instructions are handled by a dedicated 8-stage pipelined divider operating in parallel with the main pipeline. Divider instructions are removed from the main Writeback path, and their control information is tracked through an internal FIFO containing:
- Destination register index
- Write-enable signal
- Funct3 field
- Valid bit

At the Writeback stage, divider results take priority when valid.

### 6.2 Divider Hazard Handling
A barrier-stall mechanism is used to prevent writeback conflicts:
- Independent divide instructions may be pipelined
- Non-divide instructions stall while the divider pipeline is busy
- Data dependencies are checked against all active divider stages

This conservative approach guarantees correctness and simplifies forwarding logic.

---

## 7. Testing and Simulation

Simulation can be performed using both directed instruction sequences and waveform inspection:
- Simulation can be done by running the `ISA_runner.v`.
- The initial Instructions are stored in `mem.hex`
- The results in RAM and RegFile are stored in `mem_dump.txt` and  `reg_dump.txt`

Implementation can be done on Vivado or any other synthesis tools.
- Make sure to comment out the `$writememh()` and `$readmemh()` at the Memory and RegFile modules for synthesiability.

---

## 8. FPGA Implementation Results

### 8.1 Timing
- Target clock period: 25 ns (40 MHz)
- No failing timing endpoints
- Improved worst negative slack compared to single-cycle and multi-cycle designs

### 8.2 Resource Utilization
- 3400 LUTs and 2100 flip-flop (big improvement in area usage compared to other RV32IM single-cycle cores)
- Pipelined divider significantly reduces critical-path pressure

---

## 9. Conclusion

This project demonstrates a fully functional five-stage pipelined RV32IM processor with correct hazard handling, efficient forwarding, and clean integration of a multi-cycle arithmetic unit. The design is suitable for both academic study and further architectural exploration.

---

### Author: Pham Minh Nhat - HCMUT
