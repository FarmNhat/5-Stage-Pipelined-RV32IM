# RV32IM Five-Stage Pipelined RISC-V Processor

---

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

### 4.3 MemorySingleCycle
- Unified instruction/data memory
- 32-bit word-addressable
- Negative-edge access model

### 4.4 Supporting Modules
- `RegFile`: Register file with internal WD bypass
- `cla.v`: 32-bit carry look-ahead adder
- `DividerUnsignedPipelined.v`: 8-stage pipelined divider

---

## 5. Register File Design

The register file contains 32 general-purpose registers with:
- One synchronous write port
- Two asynchronous read ports
- Register x0 hard-wired to zero

An internal **WD bypass** is implemented: when a register is written in the same cycle it is read, the write data is forwarded directly to the read port. This ensures correct Decode-stage behavior and simplifies external hazard logic.

---

## 6. Pipeline Registers and Naming Convention

Pipeline stage signals follow a strict naming convention:
- Fetch stage: `f_`
- Decode stage: `id_`
- Execute stage: `ex_`
- Memory stage: `mem_`
- Writeback stage: `wb_`

Each stage includes a valid bit to support pipeline bubbles, stalls, and flushes.

---

## 7. Execute Stage and ALU

The Execute stage performs:
- Arithmetic and logical operations
- Branch condition evaluation and target calculation
- Effective address computation for memory instructions

The ALU is built around a 32-bit carry look-ahead adder, supporting addition and subtraction via operand inversion and carry-in control. For control-flow instructions, the link address (`PC + 4`) is generated and forwarded to Writeback.

---

## 8. Forwarding and Hazard Handling

### 8.1 Forwarding Paths
To minimize stalls, the following forwarding paths are implemented:

| Path | Description |
|----|------------|
| MX | Memory stage to Execute stage |
| WX | Writeback stage to Execute stage |
| WD | Writeback stage to Decode stage |
| WM | Load data forwarded to Store data |

### 8.2 Load–Use Hazard
A load–use hazard is detected when:
- A load instruction is in the Execute stage
- The following instruction in Decode uses the loaded destination register

In this case, the pipeline stalls for one cycle and inserts a bubble into the Execute stage.

---

## 9. RV32M Pipelined Divider Integration

### 9.1 Sidecar Divider Architecture
RV32M divide and remainder instructions are handled by a dedicated 8-stage pipelined divider operating in parallel with the main pipeline. Divider instructions are removed from the main Writeback path, and their control information is tracked through an internal FIFO containing:
- Destination register index
- Write-enable signal
- Funct3 field
- Valid bit

At the Writeback stage, divider results take priority when valid.

### 9.2 Divider Hazard Handling
A barrier-stall mechanism is used to prevent writeback conflicts:
- Independent divide instructions may be pipelined
- Non-divide instructions stall while the divider pipeline is busy
- Data dependencies are checked against all active divider stages

This conservative approach guarantees correctness and simplifies forwarding logic.

---

## 10. Testing and Simulation

Testing was performed using both directed instruction sequences and waveform inspection:
- Verification of all forwarding paths
- Branch taken and not-taken behavior
- Load–use hazard stalls
- Independent and dependent divide instruction behavior

Cycle-level traces were compared against expected results using the provided Python testbench.

---

## 11. FPGA Implementation Results

### 11.1 Timing
- Target clock period: 25 ns (40 MHz)
- No failing timing endpoints
- Improved worst negative slack compared to single-cycle and multi-cycle designs

### 11.2 Resource Utilization
- Low LUT and flip-flop usage
- Pipelined divider significantly reduces critical-path pressure

---

## 12. Conclusion

This project demonstrates a fully functional five-stage pipelined RV32IM processor with correct hazard handling, efficient forwarding, and clean integration of a multi-cycle arithmetic unit. The design is suitable for both academic study and further architectural exploration.

---

## 13. Future Work

- Instruction and data cache integration
- Branch prediction
- Superscalar issue support
- CSR and exception handling
- AXI-based memory interface

---

## 14. How to Run

1. Load `DatapathPipelined.v`
2. Initialize `mem_initial_contents.hex`
3. Run `runner.v` for simulation
4. Use the provided Python testbench for trace verification

---

## 15. Author

Phạm Minh Nhật  
Faculty of Computer Science and Engineering  
Ho Chi Minh City University of Technology  
December 2025
