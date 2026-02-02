`timescale 1ns / 1ns

`include "cla.v"


`define REG_SIZE 31
`define INST_SIZE 31
`define OPCODE_SIZE 6

///////////////////// CLA MODULES //////////////////////

module gp1(input wire a, b,
output wire g, p);
assign g = a & b;
assign p = a | b;
endmodule


module gp4(input wire [3:0] gin, pin,
input wire cin,
output wire gout, pout,
output wire [2:0] cout);

assign cout[0] = gin[0] | (pin[0] & cin);
assign cout[1] = gin[1] | (pin[1] & gin[0]) | (pin[1] & pin[0] & cin);
assign cout[2] = gin[2] | (pin[2] & gin[1]) | (pin[2] & pin[1] & gin[0]) |  (pin[2] & pin[1] & pin[0] & cin);

assign pout = &pin; 
assign gout = gin[3] | (pin[3] & gin[2]) | 
              (pin[3] & pin[2] & gin[1]) | 
              (pin[3] & pin[2] & pin[1] & gin[0]);   
endmodule


module gp8(input wire [7:0] gin, pin,
input wire cin,
output wire gout, pout,
output wire [6:0] cout);


wire [1:0] g4, p4;
wire [2:0] c_low, c_high;
wire       carry4;

// Lower 4 bits
gp4 gp_low (
    .gin(gin[3:0]),
    .pin(pin[3:0]),
    .cin(cin),
    .gout(g4[0]),
    .pout(p4[0]),
    .cout(c_low));

assign carry4 = g4[0] | (p4[0] & cin);

 // Upper 4 bits
 gp4 gp_high (
    .gin(gin[7:4]),
    .pin(pin[7:4]),
    .cin(carry4),
    .gout(g4[1]),
    .pout(p4[1]),
    .cout(c_high)
);

assign cout = {c_high, carry4, c_low};
assign pout = p4[1] & p4[0];
assign gout = g4[1] | (p4[1] & g4[0]);
endmodule

module cla
(input wire [31:0]  a, b,
input wire         cin,
output wire [31:0] sum);

// TODO: your code here
wire [31:0] gin, pin;
wire [3:0]  g8, p8;
wire [30:0] c;
wire [2:0]  carry8;

genvar i;
generate
for (i = 0; i < 32; i = i + 1) begin : GP1
gp1 gp1_inst (.a(a[i]), .b(b[i]), .g(gin[i]), .p(pin[i]));
end
endgenerate

// 8-bit group blocks
gp8 gp8_0 (.gin(gin[7:0]),   .pin(pin[7:0]),   .cin(cin),        .gout(g8[0]), .pout(p8[0]), .cout(c[6:0]));
gp8 gp8_1 (.gin(gin[15:8]),  .pin(pin[15:8]),  .cin(carry8[0]),  .gout(g8[1]), .pout(p8[1]), .cout(c[14:8]));
gp8 gp8_2 (.gin(gin[23:16]), .pin(pin[23:16]), .cin(carry8[1]),  .gout(g8[2]), .pout(p8[2]), .cout(c[22:16]));
gp8 gp8_3 (.gin(gin[31:24]), .pin(pin[31:24]), .cin(carry8[2]),  .gout(g8[3]), .pout(p8[3]), .cout(c[30:24]));


assign carry8[0] = g8[0] | (p8[0] & cin);
assign carry8[1] = g8[1] | (p8[1] & carry8[0]);
assign carry8[2] = g8[2] | (p8[2] & carry8[1]);

assign c[7]  = carry8[0];
assign c[15] = carry8[1];
assign c[23] = carry8[2];

assign sum[0] = a[0] ^ b[0] ^ cin;
assign sum[31:1] = a[31:1] ^ b[31:1] ^ c[30:0];
endmodule




///////////////////////// DIVIDER MODULES //////////////////////



module DividerPipelined (
    input             clk, 
    input             rst, 
    input             stall,
    input             i_signed,   // 1 for signed (div/rem), 0 for unsigned (divu/remu)
    input      [31:0] i_dividend,
    input      [31:0] i_divisor,
    output reg [31:0] o_remainder,
    output reg [31:0] o_quotient
  );
  
    wire sign_dvd = i_signed & i_dividend[31];
    wire sign_dvr = i_signed & i_divisor[31];
    wire result_quo_sign = sign_dvd ^ sign_dvr;
    wire result_rem_sign = sign_dvd;
  
    wire [31:0] abs_dividend = sign_dvd ? -i_dividend : i_dividend;
    wire [31:0] abs_divisor  = sign_dvr ? -i_divisor  : i_divisor;
  
    
    reg [31:0] pipe_dvd [0:7]; // Remaining dividend bits
    reg [31:0] pipe_dvr [0:7]; // Divisor (constant throughout)
    reg [31:0] pipe_rem [0:7]; // Current remainder
    reg [31:0] pipe_quo [0:7]; // Current quotient
    reg        pipe_sq  [0:7]; // Sign of Quotient
    reg        pipe_sr  [0:7]; // Sign of Remainder
  
   
    genvar i, j;
    generate
        for (i = 0; i < 8; i = i + 1) begin : stage_gen
            
            // Wires to connect the 4 iterations within one stage
            wire [31:0] dvd_wires [0:4];
            wire [31:0] rem_wires [0:4];
            wire [31:0] quo_wires [0:4];
  
            
            if (i == 0) begin
                
                assign dvd_wires[0] = abs_dividend;
                assign rem_wires[0] = 32'b0;      // Initial remainder is 0
                assign quo_wires[0] = 32'b0;      // Initial quotient is 0
            end else begin
                
                assign dvd_wires[0] = pipe_dvd[i-1];
                assign rem_wires[0] = pipe_rem[i-1];
                assign quo_wires[0] = pipe_quo[i-1];
            end
  
            
            for (j = 0; j < 4; j = j + 1) begin : iter_gen
                divu_1iter iter_inst (
                    .i_dividend (dvd_wires[j]),
                    .i_divisor  (i == 0 ? abs_divisor : pipe_dvr[i-1]), 
                    .i_remainder(rem_wires[j]),
                    .i_quotient (quo_wires[j]),
                    .o_dividend (dvd_wires[j+1]),
                    .o_remainder(rem_wires[j+1]),
                    .o_quotient (quo_wires[j+1])
                );
            end
  
            
            always @(posedge clk) begin
                if (rst) begin
                    pipe_dvd[i] <= 0;
                    pipe_dvr[i] <= 0;
                    pipe_rem[i] <= 0;
                    pipe_quo[i] <= 32'hffff_ffff;
                    pipe_sq[i]  <= 0;
                    pipe_sr[i]  <= 0;
                end else if (!stall) begin
                    
                    pipe_dvd[i] <= dvd_wires[4];
                    pipe_rem[i] <= rem_wires[4];
                    pipe_quo[i] <= quo_wires[4];
                    
                    
                    if (i == 0) begin
                        pipe_dvr[i] <= abs_divisor;
                        pipe_sq[i]  <= result_quo_sign;
                        pipe_sr[i]  <= result_rem_sign;
                    end else begin
                        pipe_dvr[i] <= pipe_dvr[i-1];
                        pipe_sq[i]  <= pipe_sq[i-1];
                        pipe_sr[i]  <= pipe_sr[i-1];
                    end
                end
            end
        end
    endgenerate
  
    
    wire [31:0] raw_quotient  = pipe_quo[7];
    wire [31:0] raw_remainder = pipe_rem[7];
    wire        final_sq      = pipe_sq[7];
    wire        final_sr      = pipe_sr[7];
  
    always @(*) begin
        
        o_quotient  = final_sq ? -raw_quotient : raw_quotient;
        o_remainder = final_sr ? -raw_remainder : raw_remainder;
    end
  
  endmodule
  
  
  `timescale 1ns / 1ns
  
  module divu_1iter (
      input      [31:0] i_dividend,
      input      [31:0] i_divisor,
      input      [31:0] i_remainder,
      input      [31:0] i_quotient,
      output     [31:0] o_dividend,
      output     [31:0] o_remainder,
      output     [31:0] o_quotient
  );
  
      // 1. Shift Remainder left by 1, bringing in the MSB of the current dividend
      wire [31:0] partial_rem = {i_remainder[30:0], i_dividend[31]};
      wire [32:0] sub_res = {1'b0, partial_rem} - {1'b0, i_divisor};
      wire successful = ~sub_res[32];
  
      assign o_remainder = successful ? sub_res[31:0] : partial_rem;
      assign o_quotient  = {i_quotient[30:0], successful};
      assign o_dividend  = {i_dividend[30:0], 1'b0};
  
endmodule

  



/////////////////////////////////////////// REGFILE MODULE ////////////////////////////







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


// ============================================================================
// 4. DATAPATH PIPELINED
// ============================================================================
module DatapathPipelined (
    input                     clk,
    input                     rst,
    output     [ `REG_SIZE:0] pc_to_imem,
    input      [`INST_SIZE:0] inst_from_imem,
    output reg [ `REG_SIZE:0] addr_to_dmem,
    input      [ `REG_SIZE:0] load_data_from_dmem,
    output reg [ `REG_SIZE:0] store_data_to_dmem,
    output reg [         3:0] store_we_to_dmem,
    output reg                halt,
    output reg [ `REG_SIZE:0] trace_writeback_pc,
    output reg [`INST_SIZE:0] trace_writeback_inst
);

    // Opcodes
    localparam [`OPCODE_SIZE:0] OpcodeLoad    = 7'b00_000_11;
    localparam [`OPCODE_SIZE:0] OpcodeStore   = 7'b01_000_11;
    localparam [`OPCODE_SIZE:0] OpcodeBranch  = 7'b11_000_11;
    localparam [`OPCODE_SIZE:0] OpcodeJalr    = 7'b11_001_11;
    localparam [`OPCODE_SIZE:0] OpcodeJal     = 7'b11_011_11;
    localparam [`OPCODE_SIZE:0] OpcodeRegImm  = 7'b00_100_11;
    localparam [`OPCODE_SIZE:0] OpcodeRegReg  = 7'b01_100_11;
    localparam [`OPCODE_SIZE:0] OpcodeLui     = 7'b01_101_11;
    localparam [`OPCODE_SIZE:0] OpcodeAuipc   = 7'b00_101_11;
    localparam [`OPCODE_SIZE:0] OpcodeEnviron = 7'b11_100_11;

    // Cycle Counter
    reg [`REG_SIZE:0] cycles_current;
    always @(posedge clk) begin
        if (rst) cycles_current <= 0;
        else cycles_current <= cycles_current + 1;
    end

    
    reg [`REG_SIZE:0] id_pc;
    reg [`INST_SIZE:0] id_inst;
    
    reg [`REG_SIZE:0] ex_pc, ex_rs1_data, ex_rs2_data, ex_imm;
    reg [4:0]         ex_rs1_addr, ex_rs2_addr, ex_rd_addr;
    reg [6:0]         ex_opcode, ex_funct7;
    reg [2:0]         ex_funct3;
    reg ex_reg_we, ex_mem_we, ex_mem_read, ex_branch, ex_jump, ex_halt;
    
    reg [`REG_SIZE:0] mem_pc, mem_alu_result, mem_store_data;
    reg [4:0]         mem_rd_addr;
    reg [2:0]         mem_funct3;
    reg mem_reg_we, mem_mem_we, mem_mem_read, mem_halt;
    
    reg [`REG_SIZE:0] wb_pc, wb_alu_result, wb_mem_data;
    reg [4:0]         wb_rd_addr;
    reg [2:0]         wb_funct3;
    reg wb_reg_we, wb_mem_read, wb_halt;

    // Internal Signals
    reg  [`REG_SIZE:0] f_pc_current;
    wire [`REG_SIZE:0] f_pc_next, f_pc_plus_4;
    wire stall;
    wire flush;
    
    // Forwarding
    reg [`REG_SIZE:0] forwarded_rs1_data, forwarded_rs2_data;
    reg [1:0] forward_a, forward_b;
    
    // Branch
    wire branch_taken;
    wire [`REG_SIZE:0] branch_target;

    reg [4:0] pipe_div_rd     [0:7];
    reg       pipe_div_valid  [0:7];

    reg ex_is_ghost_div;

    //========================================================================
    //FETCH STAGE

    assign pc_to_imem = f_pc_current;
    assign f_pc_plus_4 = f_pc_current + 4;
    assign f_pc_next = (branch_taken) ? branch_target : f_pc_plus_4;

    always @(posedge clk) begin
        if (rst) f_pc_current <= 32'd0;
        else if (!stall) f_pc_current <= f_pc_next;
        else f_pc_current <= f_pc_current;
    end

    always @(posedge clk) begin
        if (rst || flush) begin
            id_pc <= 0; id_inst <= 0;
        end else if (!stall) begin
            id_pc <= f_pc_current; id_inst <= inst_from_imem;
        end else begin
            id_inst <= id_inst; // Hold instruction on stall
        end
    end

    //========================================================================
    //DECODE STAGE
    
    wire [6:0] id_opcode = id_inst[6:0];
    wire [4:0] id_rd     = id_inst[11:7];
    wire [2:0] id_funct3 = id_inst[14:12];
    wire [4:0] id_rs1    = id_inst[19:15];
    wire [4:0] id_rs2    = id_inst[24:20];
    wire [6:0] id_funct7 = id_inst[31:25];

    // Immediates
    wire [`REG_SIZE:0] imm_i = {{20{id_inst[31]}}, id_inst[31:20]};
    wire [`REG_SIZE:0] imm_s = {{20{id_inst[31]}}, id_inst[31:25], id_inst[11:7]};
    wire [`REG_SIZE:0] imm_b = {{19{id_inst[31]}}, id_inst[31], id_inst[7], id_inst[30:25], id_inst[11:8], 1'b0};
    wire [`REG_SIZE:0] imm_u = {id_inst[31:12], 12'b0};
    wire [`REG_SIZE:0] imm_j = {{11{id_inst[31]}}, id_inst[31], id_inst[19:12], id_inst[20], id_inst[30:21], 1'b0};

    reg [`REG_SIZE:0] id_imm_selected;
    always @(*) begin
        case (id_opcode)
            OpcodeStore:  id_imm_selected = imm_s;
            OpcodeBranch: id_imm_selected = imm_b;
            OpcodeLui:    id_imm_selected = imm_u;
            OpcodeAuipc:  id_imm_selected = imm_u;
            OpcodeJal:    id_imm_selected = imm_j;
            default:      id_imm_selected = imm_i;
        endcase
    end

    // Control Signals
    reg id_reg_we, id_mem_we, id_mem_read, id_branch, id_jump, id_halt;
    always @(*) begin
        id_reg_we = 0; id_mem_we = 0; id_mem_read = 0; id_branch = 0; id_jump = 0; id_halt = 0;
        case (id_opcode)
            OpcodeRegReg: id_reg_we = 1;
            OpcodeRegImm: id_reg_we = 1;
            OpcodeLoad:   begin id_reg_we = 1; id_mem_read = 1; end
            OpcodeStore:  id_mem_we = 1;
            OpcodeBranch: id_branch = 1;
            OpcodeJal:    begin id_reg_we = 1; id_jump = 1; end
            OpcodeJalr:   begin id_reg_we = 1; id_jump = 1; end
            OpcodeLui:    id_reg_we = 1;
            OpcodeAuipc:  id_reg_we = 1;
            OpcodeEnviron: if (id_funct3 == 0 && id_inst[20] == 0) id_halt = 1;
        endcase
    end

    // RegFile
    wire [`REG_SIZE:0] rf_rs1_data, rf_rs2_data;
    wire [`REG_SIZE:0] wb_final_data; 
    wire [4:0]         wb_final_rd;
    wire               wb_final_we;

    RegFile rf (
        .clk(clk), .rst(rst),
        .rs1(id_rs1), .rs1_data(rf_rs1_data),
        .rs2(id_rs2), .rs2_data(rf_rs2_data),
        .rd (wb_final_rd), .rd_data(wb_final_data), .we (wb_final_we)
    );

    // --- STALL LOGIC (BARRIER METHOD) - FIXED ---

   
    wire id_is_div = (id_opcode == OpcodeRegReg) && (id_funct7 == 7'b0000001) && (id_funct3[2] == 1'b1);

    wire ex_is_div = (ex_opcode == OpcodeRegReg) && (ex_funct7 == 7'b0000001) && (ex_funct3[2] == 1'b1);
    wire [7:0] pipe_div_valid_vector; 
    wire sidecar_is_busy = |pipe_div_valid_vector; 
    wire divider_system_busy = sidecar_is_busy 
    || ex_is_div
    ;
    wire stall_load_use = (ex_mem_read && (ex_rd_addr != 0) && ((ex_rd_addr == id_rs1) || (ex_rd_addr == id_rs2)));
    
    
    wire stall_div_barrier = divider_system_busy && !id_is_div; // divider_system_busy

    ////////////////////////////////////////////////////

    reg stall_div_data_dep;
    integer m;
    always @(*) begin
        stall_div_data_dep = 0;
        
        
        if (ex_is_div && (ex_rd_addr != 0)) begin
            if ((id_rs1 == ex_rd_addr) || (id_rs2 == ex_rd_addr)) begin
                stall_div_data_dep = 1; 
            end
        end

        
        for(m=0; m<6; m=m+1) begin
            if (pipe_div_valid[m] && (pipe_div_rd[m] != 0)) begin
                if ((id_rs1 == pipe_div_rd[m]) || (id_rs2 == pipe_div_rd[m])) begin
                    stall_div_data_dep = 1;
                end
            end
            
        end
    end

    /////////////////////////////////////////////////////

    assign stall = stall_load_use || 
                    stall_div_barrier ||
                    stall_div_data_dep;

    // ID/EX Pipeline Register
    always @(posedge clk) begin
        if (rst || flush || stall) begin
            ex_pc <= 0; ex_rs1_data <= 0; ex_rs2_data <= 0; ex_imm <= 0;
            ex_rs1_addr <= 0; ex_rs2_addr <= 0; ex_rd_addr <= 0;
            ex_opcode <= 0; ex_funct3 <= 0; ex_funct7 <= 0;
            ex_reg_we <= 0; ex_mem_we <= 0; ex_mem_read <= 0;
            ex_branch <= 0; ex_jump <= 0; ex_halt <= 0;
        end
        // else if (stall) begin 
        //     ex_pc <= ex_pc; ex_rs1_data <= ex_rs1_data; ex_rs2_data <= ex_rs2_data; ex_imm <= ex_imm;
        //     ex_rs1_addr <= ex_rs1_addr; ex_rs2_addr <= ex_rs2_addr; ex_rd_addr <= ex_rd_addr;
        //     ex_opcode <= ex_opcode; ex_funct3 <= ex_funct3; ex_funct7 <= ex_funct7;
        //     ex_reg_we <= ex_reg_we; ex_mem_we <= ex_mem_we; ex_mem_read <= ex_mem_read;
        //     ex_branch <= ex_branch; ex_jump <= ex_jump; ex_halt <= ex_halt;
        // end
        else begin
            ex_pc <= id_pc;
            ex_rs1_data <= rf_rs1_data; ex_rs2_data <= rf_rs2_data; ex_imm <= id_imm_selected;
            ex_rs1_addr <= id_rs1; ex_rs2_addr <= id_rs2; ex_rd_addr <= id_rd;
            ex_opcode <= id_opcode; ex_funct3 <= id_funct3; ex_funct7 <= id_funct7;
            ex_reg_we <= id_reg_we; ex_mem_we <= id_mem_we; ex_mem_read <= id_mem_read;
            ex_branch <= id_branch; ex_jump <= id_jump; ex_halt <= id_halt;
        end
    end

    //========================================================================
    //EXE STAGE
    
    // Forwarding
    always @(*) begin
        forward_a = 2'b00; forward_b = 2'b00;
        if (mem_reg_we && (mem_rd_addr != 0) && (mem_rd_addr == ex_rs1_addr)) forward_a = 2'b10;
        else if (wb_final_we && (wb_final_rd != 0) && (wb_final_rd == ex_rs1_addr)) forward_a = 2'b01;
        
        if (mem_reg_we && (mem_rd_addr != 0) && (mem_rd_addr == ex_rs2_addr)) forward_b = 2'b10;
        else if (wb_final_we && (wb_final_rd != 0) && (wb_final_rd == ex_rs2_addr)) forward_b = 2'b01;
    end

    always @(*) begin
        case (forward_a)
            2'b00: forwarded_rs1_data = ex_rs1_data;
            2'b01: forwarded_rs1_data = wb_final_data; 
            2'b10: forwarded_rs1_data = mem_alu_result;
            default: forwarded_rs1_data = ex_rs1_data;
        endcase
        case (forward_b)
            2'b00: forwarded_rs2_data = ex_rs2_data;
            2'b01: forwarded_rs2_data = wb_final_data;
            2'b10: forwarded_rs2_data = mem_alu_result;
            default: forwarded_rs2_data = ex_rs2_data;
        endcase
    end

    wire [`REG_SIZE:0] alu_in_a = forwarded_rs1_data;
    wire [`REG_SIZE:0] alu_in_b = (ex_opcode == OpcodeRegImm || ex_opcode == OpcodeLoad || ex_opcode == OpcodeStore) ? ex_imm : forwarded_rs2_data;

    // --- SIDECAR DIVIDER LOGIC ---
    wire is_div_op = (ex_opcode == OpcodeRegReg) && (ex_funct7 == 7'b0000001) && (ex_funct3[2] == 1'b1);
    wire is_signed_div = ~ex_funct3[0];
    wire [`REG_SIZE:0] div_quotient_out, div_remainder_out;

    DividerPipelined divider_inst (
        .clk(clk), .rst(rst), .stall(1'b0), 
        .i_signed(is_signed_div),
        .i_dividend(alu_in_a), .i_divisor(alu_in_b),
        .o_remainder(div_remainder_out), .o_quotient(div_quotient_out)
    );

    // Sidecar FIFO (Delay Line - 8 stages)
    
    reg       pipe_div_we     [0:7];
    reg [2:0] pipe_div_funct3 [0:7];
    integer k;

    // Assign vector for barrier stall check
    assign pipe_div_valid_vector = {
        pipe_div_valid[7], pipe_div_valid[6], pipe_div_valid[5], pipe_div_valid[4],
        pipe_div_valid[3], pipe_div_valid[2], pipe_div_valid[1], pipe_div_valid[0]
    };

    always @(posedge clk) begin
        if (rst) begin
            for(k=0; k<8; k=k+1) begin
                pipe_div_rd[k] <= 0; pipe_div_we[k] <= 0; pipe_div_valid[k] <= 0;
            end
        end else begin
            // Shift
            for(k=7; k>0; k=k-1) begin
                pipe_div_rd[k] <= pipe_div_rd[k-1];
                pipe_div_we[k] <= pipe_div_we[k-1];
                pipe_div_funct3[k] <= pipe_div_funct3[k-1];
                pipe_div_valid[k] <= pipe_div_valid[k-1];
            end
            // Insert at stage 0
            pipe_div_rd[0]     <= ex_rd_addr;
            pipe_div_we[0]     <= ex_reg_we && is_div_op;
            pipe_div_funct3[0] <= ex_funct3;
            pipe_div_valid[0]  <= is_div_op; 
        end
    end


   
    wire is_sub = (ex_opcode == OpcodeRegReg) && (ex_funct3 == 3'b000) && (ex_funct7 == 7'b0100000);

  
    wire [`REG_SIZE:0] cla_in_b = is_sub ? ~alu_in_b : alu_in_b;
    wire               cla_cin  = is_sub ? 1'b1 : 1'b0;
    wire [`REG_SIZE:0] cla_result;

    
        cla alu_adder (
            .a   (alu_in_a),    
            .b   (cla_in_b),
            .cin (cla_cin),
            .sum (cla_result)
        );
    // ========================================================================

    // Standard ALU Logic
    reg [`REG_SIZE:0] ex_alu_result_comb;
    always @(*) begin
        ex_alu_result_comb = 0;
        case (ex_opcode)
            OpcodeLui:    ex_alu_result_comb = ex_imm;
            OpcodeAuipc:  ex_alu_result_comb = ex_pc + ex_imm;
            OpcodeJal:    ex_alu_result_comb = ex_pc + 4;
            OpcodeJalr:   ex_alu_result_comb = ex_pc + 4;
            OpcodeBranch: ex_alu_result_comb = 0;
            default: begin
                if (ex_opcode == OpcodeRegReg && ex_funct7 == 7'b0000001 && ex_funct3[2] == 0) begin 
                    // MUL
                    ex_alu_result_comb = alu_in_a * alu_in_b; 
                end else begin
                    // ADD, SUB, etc.
                    case (ex_funct3)
                        3'b000: ex_alu_result_comb = cla_result;
                        3'b001: ex_alu_result_comb = alu_in_a << alu_in_b[4:0];
                        3'b010: ex_alu_result_comb = ($signed(alu_in_a) < $signed(alu_in_b)) ? 1 : 0;
                        3'b011: ex_alu_result_comb = (alu_in_a < alu_in_b) ? 1 : 0;
                        3'b100: ex_alu_result_comb = alu_in_a ^ alu_in_b;
                        3'b101: ex_alu_result_comb = (ex_funct7==7'b0100000) ? $signed(alu_in_a) >>> alu_in_b[4:0] : alu_in_a >> alu_in_b[4:0];
                        3'b110: ex_alu_result_comb = alu_in_a | alu_in_b;
                        3'b111: ex_alu_result_comb = alu_in_a & alu_in_b;
                    endcase
                end
            end
        endcase
    end

    // Branch Logic
    reg take_branch;
    always @(*) begin
        take_branch = 0;
        if (ex_branch) begin
            case (ex_funct3)
                3'b000: take_branch = (forwarded_rs1_data == forwarded_rs2_data);
                3'b001: take_branch = (forwarded_rs1_data != forwarded_rs2_data);
                3'b100: take_branch = ($signed(forwarded_rs1_data) < $signed(forwarded_rs2_data));
                3'b101: take_branch = ($signed(forwarded_rs1_data) >= $signed(forwarded_rs2_data));
                3'b110: take_branch = (forwarded_rs1_data < forwarded_rs2_data);
                3'b111: take_branch = (forwarded_rs1_data >= forwarded_rs2_data);
            endcase
        end
    end
    assign branch_taken = take_branch || ex_jump;
    assign branch_target = (ex_opcode == OpcodeJalr) ? (forwarded_rs1_data + ex_imm) & ~1 : (ex_pc + ex_imm);
    assign flush = branch_taken;

    // EX/MEM Register
    always @(posedge clk) begin
        if (rst || flush) begin
            mem_pc <= 0; mem_alu_result <= 0; mem_store_data <= 0; mem_rd_addr <= 0;
            mem_reg_we <= 0; mem_mem_we <= 0; mem_mem_read <= 0; mem_halt <= 0;
        end else begin
            mem_pc <= ex_pc;
            mem_alu_result <= ex_alu_result_comb;
            mem_store_data <= forwarded_rs2_data;
            mem_rd_addr <= ex_rd_addr;
            mem_funct3 <= ex_funct3;
            
            // Turn off write-enable in main pipeline if it's a DIV (it's handled by sidecar)
            if (is_div_op) mem_reg_we <= 1'b0; 
            else mem_reg_we <= ex_reg_we;
            
            mem_mem_we <= ex_mem_we;
            mem_mem_read <= ex_mem_read;
            mem_halt <= ex_halt;
        end
    end

    //========================================================================
    //MEM STAGE
    
    always @(*) begin
        addr_to_dmem = mem_alu_result; // Always assign address
        store_we_to_dmem = 4'b0000;
        store_data_to_dmem = 32'd0;
        
        if (mem_mem_we) begin
            case (mem_funct3)
                3'b000: begin // SB
                    case (mem_alu_result[1:0])
                        2'b00: begin store_we_to_dmem=4'b0001; store_data_to_dmem={24'b0, mem_store_data[7:0]}; end
                        2'b01: begin store_we_to_dmem=4'b0010; store_data_to_dmem={16'b0, mem_store_data[7:0], 8'b0}; end
                        2'b10: begin store_we_to_dmem=4'b0100; store_data_to_dmem={8'b0, mem_store_data[7:0], 16'b0}; end
                        2'b11: begin store_we_to_dmem=4'b1000; store_data_to_dmem={mem_store_data[7:0], 24'b0}; end
                    endcase
                end
                3'b001: begin // SH
                    if (mem_alu_result[1]==0) begin store_we_to_dmem=4'b0011; store_data_to_dmem={16'b0, mem_store_data[15:0]}; end
                    else begin store_we_to_dmem=4'b1100; store_data_to_dmem={mem_store_data[15:0], 16'b0}; end
                end
                3'b010: begin // SW
                    store_we_to_dmem = 4'b1111; store_data_to_dmem = mem_store_data;
                end
            endcase
        end
    end

    // MEM/WB Register
    always @(posedge clk) begin
        if (rst) begin
            wb_pc <= 0; wb_alu_result <= 0; wb_mem_data <= 0; wb_rd_addr <= 0;
            wb_reg_we <= 0; wb_mem_read <= 0; wb_halt <= 0; wb_funct3 <= 0;
        end else begin
            wb_pc <= mem_pc;
            wb_alu_result <= mem_alu_result;
            wb_mem_data <= load_data_from_dmem;
            wb_rd_addr <= mem_rd_addr;
            wb_reg_we <= mem_reg_we;
            wb_mem_read <= mem_mem_read;
            wb_halt <= mem_halt;
            wb_funct3 <= mem_funct3;
        end
    end

    // ========================================================================
    // 5. WRITEBACK STAGE
    // ========================================================================
    reg [`REG_SIZE:0] wb_processed_load_data;
    always @(*) begin
        wb_processed_load_data = wb_mem_data;
        if (wb_mem_read) begin
            case (wb_funct3)
                3'b000: begin // LB
                    case (wb_alu_result[1:0])
                        2'b00: wb_processed_load_data = {{24{wb_mem_data[7]}},  wb_mem_data[7:0]};
                        2'b01: wb_processed_load_data = {{24{wb_mem_data[15]}}, wb_mem_data[15:8]};
                        2'b10: wb_processed_load_data = {{24{wb_mem_data[23]}}, wb_mem_data[23:16]};
                        2'b11: wb_processed_load_data = {{24{wb_mem_data[31]}}, wb_mem_data[31:24]};
                    endcase
                end
                3'b001: begin // LH
                    case (wb_alu_result[1])
                        1'b0: wb_processed_load_data = {{16{wb_mem_data[15]}}, wb_mem_data[15:0]};
                        1'b1: wb_processed_load_data = {{16{wb_mem_data[31]}}, wb_mem_data[31:16]};
                    endcase
                end
                3'b010: wb_processed_load_data = wb_mem_data; // LW
                3'b100: begin // LBU
                    case (wb_alu_result[1:0])
                        2'b00: wb_processed_load_data = {24'b0, wb_mem_data[7:0]};
                        2'b01: wb_processed_load_data = {24'b0, wb_mem_data[15:8]};
                        2'b10: wb_processed_load_data = {24'b0, wb_mem_data[23:16]};
                        2'b11: wb_processed_load_data = {24'b0, wb_mem_data[31:24]};
                    endcase
                end
                3'b101: begin // LHU
                    case (wb_alu_result[1])
                        1'b0: wb_processed_load_data = {16'b0, wb_mem_data[15:0]};
                        1'b1: wb_processed_load_data = {16'b0, wb_mem_data[31:16]};
                    endcase
                end
            endcase
        end
    end

    
    wire wb_div_valid = pipe_div_valid[7];
    wire [4:0] wb_div_rd = pipe_div_rd[7];
    wire wb_div_we = pipe_div_we[7];
    wire [2:0] wb_div_funct3 = pipe_div_funct3[7];
    
    wire [`REG_SIZE:0] wb_div_result = (wb_div_funct3[1] == 0) ? div_quotient_out : div_remainder_out;

    
    assign wb_final_we = (wb_div_valid) ? wb_div_we : wb_reg_we;
    assign wb_final_rd = (wb_div_valid) ? wb_div_rd : wb_rd_addr;
    assign wb_final_data = (wb_div_valid) ? wb_div_result : 
                           (wb_mem_read ? wb_processed_load_data : wb_alu_result);

    // Trace
    always @(*) begin
        halt = wb_halt;
        trace_writeback_pc = wb_pc;
        trace_writeback_inst = 0; 
    end

endmodule


module MemorySingleCycle #(
    parameter NUM_WORDS = 8192
) (
    input                     rst,
    input                     clk,
    input      [`REG_SIZE:0] pc_to_imem,
    output reg [`REG_SIZE:0] inst_from_imem,
    input      [`REG_SIZE:0] addr_to_dmem,
    output reg [`REG_SIZE:0] load_data_from_dmem,
    input      [`REG_SIZE:0] store_data_to_dmem,
    input      [        3:0] store_we_to_dmem
);

    reg [`REG_SIZE:0] mem_array[0:NUM_WORDS-1];
    
    // Initial memory loading
    initial begin
        $readmemh("mem.hex", mem_array);
    end

    localparam AddrMsb = $clog2(NUM_WORDS) + 1;
    localparam AddrLsb = 2;

    // Instruction Memory Read
    always @(negedge clk) begin
        inst_from_imem <= mem_array[{pc_to_imem[AddrMsb:AddrLsb]}];
    end

    // Data Memory Read/Write
    always @(negedge clk) begin
        if (store_we_to_dmem[0]) mem_array[addr_to_dmem[AddrMsb:AddrLsb]][7:0]   <= store_data_to_dmem[7:0];
        if (store_we_to_dmem[1]) mem_array[addr_to_dmem[AddrMsb:AddrLsb]][15:8]  <= store_data_to_dmem[15:8];
        if (store_we_to_dmem[2]) mem_array[addr_to_dmem[AddrMsb:AddrLsb]][23:16] <= store_data_to_dmem[23:16];
        if (store_we_to_dmem[3]) mem_array[addr_to_dmem[AddrMsb:AddrLsb]][31:24] <= store_data_to_dmem[31:24];
        
        load_data_from_dmem <= mem_array[{addr_to_dmem[AddrMsb:AddrLsb]}];
        // $writememh("memory_dump.txt", mem_array, 0, 1024);
    end
endmodule


module Processor (
    input                     clk,
    input                     rst,
    output                    halt,
    output [ `REG_SIZE:0] trace_writeback_pc,
    output [`INST_SIZE:0] trace_writeback_inst
);
    wire [`INST_SIZE:0] inst_from_imem;
    wire [ `REG_SIZE:0] pc_to_imem, mem_data_addr, mem_data_loaded_value, mem_data_to_write;
    wire [         3:0] mem_data_we;

    MemorySingleCycle #(
        .NUM_WORDS(8192)
    ) memory (
        .rst                (rst),
        .clk                (clk),
        .pc_to_imem         (pc_to_imem),
        .inst_from_imem     (inst_from_imem),
        .addr_to_dmem       (mem_data_addr),
        .load_data_from_dmem(mem_data_loaded_value),
        .store_data_to_dmem (mem_data_to_write),
        .store_we_to_dmem   (mem_data_we)
    );

    DatapathPipelined datapath (
        .clk                 (clk),
        .rst                 (rst),
        .pc_to_imem          (pc_to_imem),
        .inst_from_imem      (inst_from_imem),
        .addr_to_dmem        (mem_data_addr),
        .store_data_to_dmem  (mem_data_to_write),
        .store_we_to_dmem    (mem_data_we),
        .load_data_from_dmem (mem_data_loaded_value),
        .halt                (halt),
        .trace_writeback_pc  (trace_writeback_pc),
        .trace_writeback_inst(trace_writeback_inst)
    );
endmodule