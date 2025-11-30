`timescale 1ns / 1ns
`include "DividerUnsignedPipelined.v"


// registers are 32 bits in RV32
`define REG_SIZE 31

// inst. are 32 bits in RV32IM
`define INST_SIZE 31

// RV opcodes are 7 bits
`define OPCODE_SIZE 6

`define DIVIDER_STAGES 8

// Don't forget your old codes
//`include "cla.v"
//`include "DividerUnsignedPipelined.v"

module RegFile (
  input      [        4:0] rd,
  input      [`REG_SIZE:0] rd_data,
  input      [        4:0] rs1,
  output reg [`REG_SIZE:0] rs1_data,
  input      [        4:0] rs2,
  output reg [`REG_SIZE:0] rs2_data,
  input                    clk,
  input                    we,
  input                    rst
);

  localparam NumRegs = 32;
reg [`REG_SIZE:0] regs[0:NumRegs-1];

// TODO: your code here
integer i;
always @(posedge clk) begin
  if(rst)begin
    for(i = 0; i < 32; i = i+1)begin 
      regs[i] <= 32'd0; 
    end
  end
  else begin 
    if(we) regs[rd] <= rd_data;
    //regs[0] <= 32'd0;
  end
end

always @(*) begin
  // Internal Forwarding cho RS1
  if (we && (rs1 == rd) && (rs1 != 0)) begin
      rs1_data = rd_data; // Lấy ngay giá trị đang được ghi
  end else begin
      rs1_data = regs[rs1]; // Lấy giá trị từ thanh ghi
  end

  // Internal Forwarding cho RS2
  if (we && (rs2 == rd) && (rs2 != 0)) begin
      rs2_data = rd_data; // Lấy ngay giá trị đang được ghi
  end else begin
      rs2_data = regs[rs2]; // Lấy giá trị từ thanh ghi
  end

  $writememh("reg_dump.txt", regs, 0, 10);
end

endmodule

module DatapathPipelined (
  input                     clk,
  input                     rst,
  output     [ `REG_SIZE:0] pc_to_imem,
  input      [`INST_SIZE:0] inst_from_imem,
  // dmem is read/write
  output reg [ `REG_SIZE:0] addr_to_dmem,
  input      [ `REG_SIZE:0] load_data_from_dmem,
  output reg [ `REG_SIZE:0] store_data_to_dmem,
  output reg [         3:0] store_we_to_dmem,
  output reg                halt,
  // The PC of the inst currently in Writeback. 0 if not a valid inst.
  output reg [ `REG_SIZE:0] trace_writeback_pc,
  // The bits of the inst currently in Writeback. 0 if not a valid inst.
  output reg [`INST_SIZE:0] trace_writeback_inst
);

  // opcodes - see section 19 of RiscV spec
  localparam [`OPCODE_SIZE:0] OpcodeLoad    = 7'b00_000_11;
  localparam [`OPCODE_SIZE:0] OpcodeStore   = 7'b01_000_11;
  localparam [`OPCODE_SIZE:0] OpcodeBranch  = 7'b11_000_11;
  localparam [`OPCODE_SIZE:0] OpcodeJalr    = 7'b11_001_11;
  localparam [`OPCODE_SIZE:0] OpcodeMiscMem = 7'b00_011_11;
  localparam [`OPCODE_SIZE:0] OpcodeJal     = 7'b11_011_11;

  localparam [`OPCODE_SIZE:0] OpcodeRegImm  = 7'b00_100_11;
  localparam [`OPCODE_SIZE:0] OpcodeRegReg  = 7'b01_100_11;
  localparam [`OPCODE_SIZE:0] OpcodeEnviron = 7'b11_100_11;

  localparam [`OPCODE_SIZE:0] OpcodeAuipc   = 7'b00_101_11;
  localparam [`OPCODE_SIZE:0] OpcodeLui     = 7'b01_101_11;

  // cycle counter, not really part of any stage but useful for orienting within GtkWave
  // do not rename this as the testbench uses this value
  reg [`REG_SIZE:0] cycles_current;
  always @(posedge clk) begin
    if (rst) begin
      cycles_current <= 0;
    end else begin
      cycles_current <= cycles_current + 1;
    end
  end

  


  // ==============================================================================
  // PIPELINE STAGE REGISTERS
  // ==============================================================================
  
  // --- IF/ID Pipeline Registers ---
  reg [`REG_SIZE:0] id_pc;
  reg [`INST_SIZE:0] id_inst;
  
  // --- ID/EX Pipeline Registers ---
  reg [`REG_SIZE:0] ex_pc;
  reg [`REG_SIZE:0] ex_rs1_data, ex_rs2_data;
  reg [`REG_SIZE:0] ex_imm;
  reg [4:0]         ex_rs1_addr, ex_rs2_addr, ex_rd_addr;
  reg [6:0]         ex_opcode;
  reg [2:0]         ex_funct3;
  reg [6:0]         ex_funct7;
  // Control Signals propagating to EX
  reg ex_reg_we, ex_mem_we, ex_mem_read, ex_branch, ex_jump, ex_halt;
  
  // --- EX/MEM Pipeline Registers ---
  reg [`REG_SIZE:0] mem_pc;
  reg [`REG_SIZE:0] mem_alu_result;
  reg [`REG_SIZE:0] mem_store_data;
  reg [4:0]         mem_rd_addr;
  reg [2:0]         mem_funct3; // NEW: Needed for Store size (SB/SH/SW)
  // Control Signals propagating to MEM
  reg mem_reg_we, mem_mem_we, mem_mem_read, mem_halt;
  
  // --- MEM/WB Pipeline Registers ---
  reg [`REG_SIZE:0] wb_pc;
  reg [`REG_SIZE:0] wb_alu_result;
  reg [`REG_SIZE:0] wb_mem_data;
  reg [4:0]         wb_rd_addr;
  reg [2:0]         wb_funct3; // NEW: Needed for Load extension (LB/LH/LBU...)
  // Control Signals propagating to WB
  reg wb_reg_we, wb_mem_read, wb_halt;

  // ==============================================================================
  // INTERNAL WIRES & HAZARD SIGNALS
  // ==============================================================================
  
  reg [`REG_SIZE:0] f_pc_current;
  wire [`REG_SIZE:0] f_pc_next, f_pc_plus_4;
  wire stall;
  wire flush;
  wire pc_stall;
  wire if_id_write;
  
  // Forwarding wires
  reg [`REG_SIZE:0] forwarded_rs1_data;
  reg [`REG_SIZE:0] forwarded_rs2_data;
  reg [1:0] forward_a, forward_b;

  // Branch Logic
  wire branch_taken;
  wire [`REG_SIZE:0] branch_target;

  wire div_busy;

  /***************/
  /* FETCH STAGE */
  /***************/

  assign pc_to_imem = f_pc_current;
  assign f_pc_plus_4 = f_pc_current + 4;

  // PC Mux (Next PC Logic)
  assign f_pc_next = (branch_taken) ? branch_target : f_pc_plus_4;

  always @(posedge clk) begin
    if (rst) begin
      f_pc_current <= 32'd0;
    end else if (div_busy) begin
      f_pc_current <= f_pc_current; // Hold PC stable during div
    end else if (!pc_stall) begin
      f_pc_current <= f_pc_next;
    end
  end // chèn stall ngắn lệnh tiếp theo

  // IF/ID Pipeline Register
  always @(posedge clk) begin
    if (rst || flush) begin // Flush on branch
      id_pc   <= 0;
      id_inst <= 0; // NOP (ADDI x0, x0, 0)
      //stall_mem <= 1'b1;
    end 
    else if (div_busy) begin
      id_pc   <= id_pc; // Hold values stable
      id_inst <= id_inst;
    end
    else if (if_id_write) begin
      id_pc   <= f_pc_current;
      id_inst <= inst_from_imem;
    end 
  end  // cập nhật giá trị cho state register

  // // send PC to imem
  // assign pc_to_imem = f_pc_current;
  // assign f_inst = inst_from_imem;




  /****************/
  /* DECODE STAGE */
  /****************/

  wire [6:0] id_opcode = id_inst[6:0];
  wire [4:0] id_rd     = id_inst[11:7];
  wire [2:0] id_funct3 = id_inst[14:12];
  wire [4:0] id_rs1    = id_inst[19:15];
  wire [4:0] id_rs2    = id_inst[24:20];
  wire [6:0] id_funct7 = id_inst[31:25];

  // Immediate Generation
  wire [`REG_SIZE:0] imm_i = {{20{id_inst[31]}}, id_inst[31:20]};
  wire [`REG_SIZE:0] imm_s = {{20{id_inst[31]}}, id_inst[31:25], id_inst[11:7]};
  wire [`REG_SIZE:0] imm_b = {{19{id_inst[31]}}, id_inst[31], id_inst[7], id_inst[30:25], id_inst[11:8], 1'b0};
  wire [`REG_SIZE:0] imm_u = {id_inst[31:12], 12'b0};
  wire [`REG_SIZE:0] imm_j = {{11{id_inst[31]}}, id_inst[31], id_inst[19:12], id_inst[20], id_inst[30:21], 1'b0};

  reg [`REG_SIZE:0] id_imm_selected;
  always @(*) begin
    case (id_opcode)
      7'b01_000_11: id_imm_selected = imm_s; // Store
      7'b11_000_11: id_imm_selected = imm_b; // Branch
      7'b01_101_11: id_imm_selected = imm_u; // LUI
      7'b00_101_11: id_imm_selected = imm_u; // AUIPC
      7'b11_011_11: id_imm_selected = imm_j; // JAL
      default:      id_imm_selected = imm_i; // RegImm, Load, JALR
    endcase
  end

  // Register File Instance
  wire [`REG_SIZE:0] rf_rs1_data, rf_rs2_data;
  // Writeback signals come from WB stage
  wire [`REG_SIZE:0] wb_final_data; 
  
  RegFile rf (
    .clk(clk), .rst(rst),
    .rs1(id_rs1), .rs1_data(rf_rs1_data),
    .rs2(id_rs2), .rs2_data(rf_rs2_data),
    .rd(wb_rd_addr), .rd_data(wb_final_data), 
    .we(wb_reg_we)
  );

  reg id_reg_we, id_mem_we, id_mem_read, id_branch, id_jump, id_halt;
  always @(*) begin
    id_reg_we   = 0;
    
    id_mem_we   = 0;
    id_mem_read = 0;
    id_branch   = 0;
    id_jump     = 0;
    id_halt     = 0;
    
    case (id_opcode)
      7'b01_100_11: id_reg_we = 1; // R-type
      7'b00_100_11: id_reg_we = 1; // I-type ALU
      7'b00_000_11: begin id_reg_we = 1; id_mem_read = 1; end // Load
      7'b01_000_11: id_mem_we = 1; // Store
      7'b11_000_11: id_branch = 1; // Branch
      7'b11_011_11: begin id_reg_we = 1; id_jump = 1; end // JAL
      7'b11_001_11: begin id_reg_we = 1; id_jump = 1; end // JALR
      7'b01_101_11: id_reg_we = 1; // LUI
      7'b00_101_11: id_reg_we = 1; // AUIPC
      7'b11_100_11: begin // System / ECALL
         if (id_funct3 == 0 && id_inst[20] == 0) id_halt = 1; 
      end
    endcase
  end

// Hazard Detection Unit (Load-Use Hazard)
  // If ID stage needs a register that EX stage is loading from memory -> STALL
    reg start_div;
    assign stall = (ex_mem_read && (ex_rd_addr != 0) && //ex mem read là lệnh load
                    ((ex_rd_addr == id_rs1) || (ex_rd_addr == id_rs2))); // nếu đang read thanh ghi thì stall
    
    assign pc_stall = stall;      // Freeze PC
    assign if_id_write = !stall;  // Freeze IF/ID
  // If stalling, we insert a bubble into ID/EX (control signals = 0)

  // ID/EX Pipeline Register
  always @(posedge clk) begin
    if (rst || stall || flush) begin
      ex_pc       <= 0;
      ex_rs1_data <= 0;
      ex_rs2_data <= 0;
      ex_imm      <= 0;
      ex_rs1_addr <= 0;
      ex_rs2_addr <= 0;
      ex_rd_addr  <= 0;
      ex_opcode   <= 0;
      ex_funct3   <= 0;
      ex_funct7   <= 0;
      // Control Bubbles
      ex_reg_we   <= 0;
      ex_mem_we   <= 0;
      ex_mem_read <= 0;
      ex_branch   <= 0;
      ex_jump     <= 0;
      ex_halt     <= 0;
      
    end 
    else if (div_busy) begin
      ex_pc       <= ex_pc; // Hold values stable
      ex_rs1_data <= ex_rs1_data;
      ex_rs2_data <= ex_rs2_data;
      ex_imm      <= ex_imm;
      ex_rs1_addr <= ex_rs1_addr;
      ex_rs2_addr <= ex_rs2_addr;
      ex_rd_addr  <= ex_rd_addr;
      ex_opcode   <= ex_opcode;
      ex_funct3   <= ex_funct3;
      ex_funct7   <= ex_funct7;
      // Control Hold
      ex_reg_we   <= ex_reg_we;
      ex_mem_we   <= ex_mem_we;
      ex_mem_read <= ex_mem_read;
      ex_branch   <= ex_branch;
      ex_jump     <= ex_jump;
      ex_halt     <= ex_halt;
    end
    else  begin
      ex_pc       <= id_pc;
      ex_rs1_data <= rf_rs1_data;
      ex_rs2_data <= rf_rs2_data;
      ex_imm      <= id_imm_selected;
      ex_rs1_addr <= id_rs1;
      ex_rs2_addr <= id_rs2;
      ex_rd_addr  <= id_rd;
      ex_opcode   <= id_opcode;
      ex_funct3   <= id_funct3;
      ex_funct7   <= id_funct7;
      // Control Pass-through
      ex_reg_we   <= id_reg_we;
      ex_mem_we   <= id_mem_we;
      ex_mem_read <= id_mem_read;
      ex_branch   <= id_branch;
      ex_jump     <= id_jump;
      ex_halt     <= id_halt;
    end
  end



  // ==============================================================================
  // STAGE 3: EXECUTE (EX)
  // ==============================================================================

  // ================== FORWARDING UNIT ==================

  // Forwarding Unit
  always @(*) begin
    // Forward A (RS1)
    if (mem_reg_we && (mem_rd_addr != 0) && (mem_rd_addr == ex_rs1_addr))
      forward_a = 2'b10; // Forward from MEM stage
    else if (wb_reg_we && (wb_rd_addr != 0) && (wb_rd_addr == ex_rs1_addr))
      forward_a = 2'b01; // Forward from WB stage
    else
      forward_a = 2'b00; // No forwarding

    // Forward B (RS2)
    if (mem_reg_we && (mem_rd_addr != 0) && (mem_rd_addr == ex_rs2_addr))
      forward_b = 2'b10;
    else if (wb_reg_we && (wb_rd_addr != 0) && (wb_rd_addr == ex_rs2_addr))
      forward_b = 2'b01;
    else
      forward_b = 2'b00;
  end

  // Muxes for Forwarding
  always @(*) begin
    case (forward_a)
      2'b00: forwarded_rs1_data = ex_rs1_data;
      2'b01: forwarded_rs1_data = wb_final_data;
      2'b10: forwarded_rs1_data = mem_alu_result; // Note: For Loads, this forwards ALU result (address), handled by load-use stall usually, but strictly simplified here
      default: forwarded_rs1_data = ex_rs1_data;
    endcase

    case (forward_b)
      2'b00: forwarded_rs2_data = ex_rs2_data;
      2'b01: forwarded_rs2_data = wb_final_data;
      2'b10: forwarded_rs2_data = mem_alu_result;
      default: forwarded_rs2_data = ex_rs2_data;
    endcase
  end

  // ALU Inputs
  wire [`REG_SIZE:0] alu_in_a = forwarded_rs1_data;
  wire [`REG_SIZE:0] alu_in_b = (ex_opcode == 7'b00_100_11 || ex_opcode == 7'b00_000_11 || ex_opcode == 7'b01_000_11) ? ex_imm : forwarded_rs2_data;
  // alu in b có thể reg, có thể là immediate cho lệnh I-type, load, store


  
// =============== DIVIDER INTEGRATION =================
  
  // 1. Identification
  // Opcode R-Type (0110011) AND M-Ext (funct7=0000001) AND funct3[2]=1 (DIV/REM, not MUL)
  wire is_div_op = (ex_opcode == 7'b01_100_11) && (ex_funct7 == 7'b0000001) && (ex_funct3[2] == 1'b1);
  wire is_signed_div = ~ex_funct3[0]; // Bit 0: 0=Signed, 1=Unsigned

  wire [`REG_SIZE:0] div_quotient;
  wire [`REG_SIZE:0] div_remainder;

  // 2. Instantiate Divider
  // The divider runs continuously. We just hold the inputs stable via the 'div_busy' stall mechanism.
  DividerPipelined divider_inst (
      .clk        (clk),
      .rst        (rst),
      .stall      (1'b0),          // Divider internal logic advances every cycle
      .i_signed   (is_signed_div),
      .i_dividend (alu_in_a),
      .i_divisor  (alu_in_b),
      .o_remainder(div_remainder),
      .o_quotient (div_quotient)
  );

  // 3. Stall Counter (Sequential Logic)
  reg [3:0] div_counter;
  
  
  always @(posedge clk) begin
      if (rst) begin
          div_counter <= 0;
          
      end else begin
          if (is_div_op && div_counter < 8) begin
              div_counter <= div_counter + 1;
              
          end else begin
              div_counter <= 0;
              
          end
      end
  end
  // 4. Generate Div Busy Signal
  // While is_div_op is true and we haven't reached 8 cycles, we are busy.
  assign div_busy = is_div_op && (div_counter < 8);



  // ==================== ALU ====================

  
  reg [`REG_SIZE:0] ex_alu_result_comb;
  always @(*) begin
    case (ex_opcode)
    7'b01_101_11: ex_alu_result_comb = ex_imm; // LUI
    //7'b00_101_11: ex_alu_result_comb = ex_pc + ex_imm; // AUIPC
    7'b11_011_11: ex_alu_result_comb = ex_pc + 4; // JAL (Link address)
    7'b11_001_11: ex_alu_result_comb = ex_pc + 4; // JALR (Link address)
    7'b11_000_11: ex_alu_result_comb = 0; // Branch (Comparison done separately below)
    7'h23: begin // Load
        ex_alu_result_comb = alu_in_b + alu_in_a; // Calculate address imm_s + rs1 còn rs đã đc bypass trong forwarding
    end
      default: begin // ALU Operations
          // ALU / MUL / DIV
        if (ex_opcode == 7'b01_100_11 && ex_funct7 == 7'b0000001) begin // M-Extension
              if (ex_funct3[2] == 1'b0) begin // MUL
                 case(ex_funct3)
                    3'b000: ex_alu_result_comb = alu_in_a * alu_in_b; // MUL
                    3'b001: ex_alu_result_comb = ($signed(alu_in_a) * $signed(alu_in_b)) >> 32; // MULH
                    3'b010: ex_alu_result_comb = ($signed(alu_in_a) * $signed({1'b0, alu_in_b})) >> 32; // MULHSU
                    3'b011: ex_alu_result_comb = (alu_in_a * alu_in_b) >> 32; // MULHU
                    default: ex_alu_result_comb = 0;
                 endcase
              end else begin // DIV/REM
                 // Select result based on funct3
                 if (ex_funct3[1] == 1'b0) // DIV, DIVU
                    ex_alu_result_comb = div_quotient;
                 else // REM, REMU
                    ex_alu_result_comb = div_remainder;

              end
          end 
        else begin 
          
          // Normal ALU
          case (ex_funct3)
          3'b000: begin // ADD/SUB/ADDI
             if (ex_opcode == 7'b01_100_11 && ex_funct7 == 7'b0100000)
                ex_alu_result_comb = alu_in_a - alu_in_b;
             else 
                ex_alu_result_comb = alu_in_a + alu_in_b;
          end
          3'b001: ex_alu_result_comb = alu_in_a << alu_in_b[4:0]; // SLL
          3'b010: ex_alu_result_comb = ($signed(alu_in_a) < $signed(alu_in_b)) ? 1 : 0; // SLT
          3'b011: ex_alu_result_comb = (alu_in_a < alu_in_b) ? 1 : 0; // SLTU
          3'b100: ex_alu_result_comb = alu_in_a ^ alu_in_b; // XOR
          3'b101: begin // SRL/SRA
             if (ex_funct7 == 7'b0100000) ex_alu_result_comb = $signed(alu_in_a) >>> alu_in_b[4:0];
             else ex_alu_result_comb = alu_in_a >> alu_in_b[4:0];
          end
          3'b110: ex_alu_result_comb = alu_in_a | alu_in_b; // OR
          3'b111: ex_alu_result_comb = alu_in_a & alu_in_b; // AND
        endcase    
      end
    end
    endcase
  end

  
  // Branch Decision Logic
  reg take_branch;
  always @(*) begin
    take_branch = 0;
    if (ex_branch) begin
      case (ex_funct3)
        3'b000: take_branch = (forwarded_rs1_data == forwarded_rs2_data); // BEQ
        3'b001: take_branch = (forwarded_rs1_data != forwarded_rs2_data); // BNE
        3'b100: take_branch = ($signed(forwarded_rs1_data) < $signed(forwarded_rs2_data)); // BLT
        3'b101: take_branch = ($signed(forwarded_rs1_data) >= $signed(forwarded_rs2_data)); // BGE
        3'b110: take_branch = (forwarded_rs1_data < forwarded_rs2_data); // BLTU
        3'b111: take_branch = (forwarded_rs1_data >= forwarded_rs2_data); // BGEU
      endcase
    end
  end

  assign branch_taken = take_branch || ex_jump;
  
  // Calculate Target
  // JAL: PC + imm (already in imm)
  // JALR: RS1 + imm
  // Branch: PC + imm
  assign branch_target = (ex_opcode == 7'b11_001_11) ? (forwarded_rs1_data + ex_imm) & ~1 : (ex_pc + ex_imm);
  //branch target đc thêm vào PC ở đầu (fetch stage)

  assign flush = branch_taken; // flush để các lệnh đã fetch bị loại bỏ


  // EX/MEM Pipeline Register
  always @(posedge clk) begin
    if (rst || div_busy) begin
      mem_pc         <= 0;
      mem_alu_result <= 0;
      mem_store_data <= 0;
      mem_rd_addr    <= 0;
      mem_funct3     <= 0; // Reset funct3
      mem_reg_we     <= 0;
      mem_mem_we     <= 0;
      mem_mem_read   <= 0;
      mem_halt       <= 0;
    end else begin
      mem_pc         <= ex_pc;
      mem_alu_result <= ex_alu_result_comb;
      mem_store_data <= forwarded_rs2_data;
      mem_rd_addr    <= ex_rd_addr;
      mem_funct3     <= ex_funct3; // Propagate funct3
      mem_reg_we     <= ex_reg_we;
      mem_mem_we     <= ex_mem_we;
      mem_mem_read   <= ex_mem_read;
      mem_halt       <= ex_halt;
    end
  end




  // ==============================================================================
  // STAGE 4: MEM
  // ==============================================================================

  always @(*) begin
    
    // Default values
    store_we_to_dmem   = 4'b0000;
    store_data_to_dmem = 32'd0;
    
    if (mem_mem_we) begin
        addr_to_dmem = mem_alu_result; // Address is the ALU result
        case (mem_funct3)
            3'b000: begin // SB (Store Byte)
                case (mem_alu_result[1:0])
                    2'b00: begin store_we_to_dmem = 4'b0001; store_data_to_dmem = {24'b0, mem_store_data[7:0]}; end
                    2'b01: begin store_we_to_dmem = 4'b0010; store_data_to_dmem = {16'b0, mem_store_data[7:0], 8'b0}; end
                    2'b10: begin store_we_to_dmem = 4'b0100; store_data_to_dmem = {8'b0, mem_store_data[7:0], 16'b0}; end
                    2'b11: begin store_we_to_dmem = 4'b1000; store_data_to_dmem = {mem_store_data[7:0], 24'b0}; end
                endcase
            end
            3'b001: begin // SH (Store Halfword)
                if (mem_alu_result[1] == 0) begin
                    store_we_to_dmem = 4'b0011; 
                    store_data_to_dmem = {16'b0, mem_store_data[15:0]};
                end else begin
                    store_we_to_dmem = 4'b1100;
                    store_data_to_dmem = {mem_store_data[15:0], 16'b0};
                end
            end
            3'b010: begin // SW (Store Word)
                store_we_to_dmem = 4'b1111;
                store_data_to_dmem = mem_store_data;
            end
            default: begin
               store_we_to_dmem = 4'b0000;
            end
        endcase
    end else if (mem_mem_read) begin
        addr_to_dmem = mem_alu_result; // Address is the ALU result
    end 
  end

  // MEM/WB Pipeline Register
  always @(posedge clk) begin
    if (rst) begin
      wb_pc         <= 0;
      wb_alu_result <= 0;
      wb_mem_data   <= 0;
      wb_rd_addr    <= 0;
      wb_reg_we     <= 0;
      wb_mem_read   <= 0;
      wb_halt       <= 0;
    end else begin
      wb_pc         <= mem_pc;
      wb_alu_result <= mem_alu_result;
      wb_mem_data   <= load_data_from_dmem;
      wb_rd_addr    <= mem_rd_addr;
      wb_reg_we     <= mem_reg_we;
      wb_mem_read   <= mem_mem_read;
      wb_halt       <= mem_halt;
    end
  end




  // ==============================================================================
  // STAGE 5: WRITEBACK (WB)
  // ==============================================================================

  reg [`REG_SIZE:0] wb_processed_load_data;
  reg [`REG_SIZE:0] wb_final;

  always @(*) begin
    wb_processed_load_data = wb_mem_data; // Default: Just pass the 32-bit word (for LW)


    if(wb_mem_read)begin
      //addr_to_dmem = wb_alu_result;
      case (wb_funct3)
          3'b000: begin // LB (Load Byte Signed)
              case (wb_alu_result[1:0])
                  2'b00: wb_processed_load_data = {{24{wb_mem_data[7]}},  wb_mem_data[7:0]};
                  2'b01: wb_processed_load_data = {{24{wb_mem_data[15]}}, wb_mem_data[15:8]};
                  2'b10: wb_processed_load_data = {{24{wb_mem_data[23]}}, wb_mem_data[23:16]};
                  2'b11: wb_processed_load_data = {{24{wb_mem_data[31]}}, wb_mem_data[31:24]};
              endcase
          end
          3'b001: begin // LH (Load Half Signed)
              case (wb_alu_result[1])
                  1'b0: wb_processed_load_data = {{16{wb_mem_data[15]}}, wb_mem_data[15:0]};
                  1'b1: wb_processed_load_data = {{16{wb_mem_data[31]}}, wb_mem_data[31:16]};
              endcase
          end
          3'b010: begin // LW (Load Word)
              wb_processed_load_data = wb_mem_data;
          end
          3'b100: begin // LBU (Load Byte Unsigned)
              case (wb_alu_result[1:0])
                  2'b00: wb_processed_load_data = {24'b0, wb_mem_data[7:0]};
                  2'b01: wb_processed_load_data = {24'b0, wb_mem_data[15:8]};
                  2'b10: wb_processed_load_data = {24'b0, wb_mem_data[23:16]};
                  2'b11: wb_processed_load_data = {24'b0, wb_mem_data[31:24]};
              endcase
          end
          3'b101: begin // LHU (Load Half Unsigned)
              case (wb_alu_result[1])
                  1'b0: wb_processed_load_data = {16'b0, wb_mem_data[15:0]};
                  1'b1: wb_processed_load_data = {16'b0, wb_mem_data[31:16]};
              endcase
          end
      endcase
      wb_final = wb_processed_load_data;
    end
    else begin
      wb_final = wb_alu_result;
    end
  end

  assign wb_final_data = wb_final;

  // Output Signals for Testbench/Trace
  always @(*) begin
    halt = wb_halt;
    trace_writeback_pc = wb_pc;
    trace_writeback_inst = 0; 
  end

  // TODO: your code here, though you will also need to modify some of the code above
  // TODO: the testbench requires that your register file instance is named `rf`

endmodule







module MemorySingleCycle #(
    parameter NUM_WORDS = 512
) (
    input                    rst,                 // rst for both imem and dmem
    input                    clk,                 // clock for both imem and dmem
	                                              // The memory reads/writes on @(negedge clk)
    input      [`REG_SIZE:0] pc_to_imem,          // must always be aligned to a 4B boundary
    output reg [`REG_SIZE:0] inst_from_imem,      // the value at memory location pc_to_imem
    input      [`REG_SIZE:0] addr_to_dmem,        // must always be aligned to a 4B boundary
    output reg [`REG_SIZE:0] load_data_from_dmem, // the value at memory location addr_to_dmem
    input      [`REG_SIZE:0] store_data_to_dmem,  // the value to be written to addr_to_dmem, controlled by store_we_to_dmem
    // Each bit determines whether to write the corresponding byte of store_data_to_dmem to memory location addr_to_dmem.
    // E.g., 4'b1111 will write 4 bytes. 4'b0001 will write only the least-significant byte.
    input      [        3:0] store_we_to_dmem
    
);

  // memory is arranged as an array of 4B words
  reg [`REG_SIZE:0] mem_array[0:NUM_WORDS-1];

  // preload instructions to mem_array
  initial begin
    $readmemh("mem.hex", mem_array);
  end

  localparam AddrMsb = $clog2(NUM_WORDS) + 1;
  localparam AddrLsb = 2;

  always @(negedge clk)begin
      inst_from_imem <= mem_array[{pc_to_imem[AddrMsb:AddrLsb]}]; //pc to imem là phản hồi điều khiển từ controller
  end

  always @(negedge clk) begin
    if (store_we_to_dmem[0]) begin
      mem_array[addr_to_dmem[AddrMsb:AddrLsb]][7:0] <= store_data_to_dmem[7:0];
    end
    if (store_we_to_dmem[1]) begin
      mem_array[addr_to_dmem[AddrMsb:AddrLsb]][15:8] <= store_data_to_dmem[15:8];
    end
    if (store_we_to_dmem[2]) begin
      mem_array[addr_to_dmem[AddrMsb:AddrLsb]][23:16] <= store_data_to_dmem[23:16];
    end
    if (store_we_to_dmem[3]) begin
      mem_array[addr_to_dmem[AddrMsb:AddrLsb]][31:24] <= store_data_to_dmem[31:24];
    end
    // dmem is "read-first": read returns value before the write
    load_data_from_dmem <= mem_array[{addr_to_dmem[AddrMsb:AddrLsb]}];
    $writememh("memory_dump.txt", mem_array, 0, 4);
  end
endmodule





/* This design has just one clock for both processor and memory. */
module Processor (
    input                 clk,
    input                 rst,
    output                halt,
    output [ `REG_SIZE:0] trace_writeback_pc,
    output [`INST_SIZE:0] trace_writeback_inst
);

  wire [`INST_SIZE:0] inst_from_imem;
  wire [ `REG_SIZE:0] pc_to_imem, mem_data_addr, mem_data_loaded_value, mem_data_to_write;
  wire [         3:0] mem_data_we;

  // This wire is set by cocotb to the name of the currently-running test, to make it easier
  // to see what is going on in the waveforms.
  wire [(8*32)-1:0] test_case;
  wire stall_mem;
  MemorySingleCycle #(
      .NUM_WORDS(8192)
  ) memory (
    .rst                 (rst),
    .clk                 (clk),
    // imem is read-only
    .pc_to_imem          (pc_to_imem),
    .inst_from_imem      (inst_from_imem),
    // dmem is read-write
    .addr_to_dmem        (mem_data_addr),
    .load_data_from_dmem (mem_data_loaded_value),
    .store_data_to_dmem  (mem_data_to_write),
    .store_we_to_dmem    (mem_data_we)
    //.stall_mem           (stall_mem)
  );

  DatapathPipelined datapath (
    .clk                  (clk),
    .rst                  (rst),
    .pc_to_imem           (pc_to_imem),
    .inst_from_imem       (inst_from_imem),
    .addr_to_dmem         (mem_data_addr),
    .store_data_to_dmem   (mem_data_to_write),
    .store_we_to_dmem     (mem_data_we),
    .load_data_from_dmem  (mem_data_loaded_value),
    .halt                 (halt),
    .trace_writeback_pc   (trace_writeback_pc),
    .trace_writeback_inst (trace_writeback_inst)
    //.stall_mem            (stall_mem)
  );

endmodule
