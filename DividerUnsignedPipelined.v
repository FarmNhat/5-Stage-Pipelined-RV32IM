

`timescale 1ns / 1ns

// quotient = dividend / divisor

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

  // ========================================================================
  // STAGE 0: Pre-processing (Sign Handling)
  // ========================================================================
  
  // Determine the sign of the results
  // Quotient is negative if signs are different. Remainder takes sign of dividend.
  wire sign_dvd = i_signed & i_dividend[31];
  wire sign_dvr = i_signed & i_divisor[31];
  wire result_quo_sign = sign_dvd ^ sign_dvr;
  wire result_rem_sign = sign_dvd;

  // Convert to absolute values for the core unsigned divider
  wire [31:0] abs_dividend = sign_dvd ? -i_dividend : i_dividend;
  wire [31:0] abs_divisor  = sign_dvr ? -i_divisor  : i_divisor;

  // Pipeline Registers Definitions
  // We need 8 stages. We store the data coming OUT of a stage to go INTO the next.
  // We must pipeline: Dividend, Divisor, Remainder, Quotient, and Sign info.
  reg [31:0] pipe_dvd [0:7]; // Remaining dividend bits
  reg [31:0] pipe_dvr [0:7]; // Divisor (constant throughout)
  reg [31:0] pipe_rem [0:7]; // Current remainder
  reg [31:0] pipe_quo [0:7]; // Current quotient
  reg        pipe_sq  [0:7]; // Sign of Quotient
  reg        pipe_sr  [0:7]; // Sign of Remainder

  // ========================================================================
  // PIPELINE GENERATION
  // ========================================================================
  genvar i, j;
  generate
      for (i = 0; i < 8; i = i + 1) begin : stage_gen
          
          // Wires to connect the 4 iterations within one stage
          wire [31:0] dvd_wires [0:4];
          wire [31:0] rem_wires [0:4];
          wire [31:0] quo_wires [0:4];

          // Setup the inputs for the first iteration of this stage
          if (i == 0) begin
              // Input to Stage 0 comes from Pre-processing
              assign dvd_wires[0] = abs_dividend;
              assign rem_wires[0] = 32'b0;      // Initial remainder is 0
              assign quo_wires[0] = 32'b0;      // Initial quotient is 0
          end else begin
              // Input to Stage N comes from Register of Stage N-1
              assign dvd_wires[0] = pipe_dvd[i-1];
              assign rem_wires[0] = pipe_rem[i-1];
              assign quo_wires[0] = pipe_quo[i-1];
          end

          // Generate 4 combinatorial iterations per stage
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

          // Register Logic (Flip-Flops)
          always @(posedge clk) begin
              if (rst) begin
                  pipe_dvd[i] <= 0;
                  pipe_dvr[i] <= 0;
                  pipe_rem[i] <= 0;
                  pipe_quo[i] <= 0;
                  pipe_sq[i]  <= 0;
                  pipe_sr[i]  <= 0;
              end else if (!stall) begin
                  // Latch the result of the 4th iteration
                  pipe_dvd[i] <= dvd_wires[4];
                  pipe_rem[i] <= rem_wires[4];
                  pipe_quo[i] <= quo_wires[4];
                  
                  // Pass along the divisor and sign bits
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

  // ========================================================================
  // POST-PROCESSING (Final Stage)
  // ========================================================================
  
  // The result is available after the 8th stage (index 7) registers
  wire [31:0] raw_quotient  = pipe_quo[7];
  wire [31:0] raw_remainder = pipe_rem[7];
  wire        final_sq      = pipe_sq[7];
  wire        final_sr      = pipe_sr[7];

  always @(*) begin
      // Apply 2's complement if the result sign should be negative
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
    
    // 2. Try to subtract the divisor
    // We extend to 33 bits to capture the borrow (sign bit)
    wire [32:0] sub_res = {1'b0, partial_rem} - {1'b0, i_divisor};
    
    // 3. Determine if the subtraction was successful (result >= 0)
    // If sub_res[32] is 1, the result was negative (borrow occurred)
    wire successful = ~sub_res[32];

    // 4. Update outputs
    // If successful, use the subtraction result and set quotient LSB to 1
    // If not, restore (keep) the partial remainder and set quotient LSB to 0
    assign o_remainder = successful ? sub_res[31:0] : partial_rem;
    assign o_quotient  = {i_quotient[30:0], successful};
    
    // Shift the dividend to prepare the next bit for the next iteration
    assign o_dividend  = {i_dividend[30:0], 1'b0};

endmodule
