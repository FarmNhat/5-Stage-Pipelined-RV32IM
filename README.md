# RV32IM Pipelined RISC-V Processor

## 1. Overview

This project implements a **32-bit RISC-V processor (RV32IM)** using a **pipelined architecture** written in **Verilog HDL**.  
The processor follows the official **RISC-V ISA specification** and supports both:

- **RV32I** (Base Integer Instruction Set)
- **RV32M** (Integer Multiply and Divide Extension)

The main goal of this project is to study and demonstrate:
- RISC-V datapath and control design
- Pipeline operation
- Hazard detection and forwarding
- Pipelined DIV instructions as a sidecar pipeline, which utilize CPI for M extension

---

## 2. Supported ISA

### 2.1 RV32I Instructions

- Arithmetic: `add`, `sub`, `addi`
- Logical: `and`, `or`, `xor`
- Shift: `sll`, `srl`, `sra`
- Comparison: `slt`, `sltu`
- Memory access: `lw`, `sw`
- Control flow: `beq`, `bne`, `jal`, `jalr`

### 2.2 RV32M Instructions

- Multiply: `mul`, `mulh`, `mulhu`
- Divide: `div`, `divu`
- Remainder: `rem`, `remu`

---

## 3. Processor Architecture

The processor is implemented using a **5-stage pipeline**:

| Stage | Name | Description |
|------|------|------------|
| IF | Instruction Fetch | Fetch instruction from instruction memory |
| ID | Instruction Decode | Decode instruction and read registers |
| EX | Execute | ALU operations, branch decision, mul/div |
| MEM | Memory Access | Load/store data memory |
| WB | Write Back | Write result back to register file |

---

## 4. Datapath

The datapath consists of the following main components:

- Program Counter (PC)
- Instruction Memory
- Register File (32 registers, x0 is hardwired to zero)
- ALU
- Multiply / Divide Unit (RV32M)
- Data Memory
- Pipeline Registers:
  - IF/ID
  - ID/EX
  - EX/MEM
  - MEM/WB

Main datapath implementation file:

