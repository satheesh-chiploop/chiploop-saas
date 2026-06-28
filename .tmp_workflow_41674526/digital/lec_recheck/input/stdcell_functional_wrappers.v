// Auto-generated functional SKY130 cell wrappers for Yosys LEC.
// Generated from the synthesized netlist's referenced cell/pin set.
module sky130_fd_sc_hd__a2111o_2(A1, A2, B1, C1, D1, X);
  input A1;
  input A2;
  input B1;
  input C1;
  input D1;
  output X;
  assign X = ((A1 & A2) | (B1) | (C1) | (D1));
endmodule

module sky130_fd_sc_hd__a211o_2(A1, A2, B1, C1, X);
  input A1;
  input A2;
  input B1;
  input C1;
  output X;
  assign X = ((A1 & A2) | (B1) | (C1));
endmodule

module sky130_fd_sc_hd__a211oi_2(A1, A2, B1, C1, Y);
  input A1;
  input A2;
  input B1;
  input C1;
  output Y;
  assign Y = ~((A1 & A2) | (B1) | (C1));
endmodule

module sky130_fd_sc_hd__a21bo_2(A1, A2, B1_N, X);
  input A1;
  input A2;
  input B1_N;
  output X;
  assign X = ((A1 & A2) | (~B1_N));
endmodule

module sky130_fd_sc_hd__a21boi_2(A1, A2, B1_N, Y);
  input A1;
  input A2;
  input B1_N;
  output Y;
  assign Y = ~((A1 & A2) | (~B1_N));
endmodule

module sky130_fd_sc_hd__a21o_2(A1, A2, B1, X);
  input A1;
  input A2;
  input B1;
  output X;
  assign X = ((A1 & A2) | (B1));
endmodule

module sky130_fd_sc_hd__a21oi_2(A1, A2, B1, Y);
  input A1;
  input A2;
  input B1;
  output Y;
  assign Y = ~((A1 & A2) | (B1));
endmodule

module sky130_fd_sc_hd__a221o_2(A1, A2, B1, B2, C1, X);
  input A1;
  input A2;
  input B1;
  input B2;
  input C1;
  output X;
  assign X = ((A1 & A2) | (B1 & B2) | (C1));
endmodule

module sky130_fd_sc_hd__a22o_2(A1, A2, B1, B2, X);
  input A1;
  input A2;
  input B1;
  input B2;
  output X;
  assign X = ((A1 & A2) | (B1 & B2));
endmodule

module sky130_fd_sc_hd__a22oi_2(A1, A2, B1, B2, Y);
  input A1;
  input A2;
  input B1;
  input B2;
  output Y;
  assign Y = ~((A1 & A2) | (B1 & B2));
endmodule

module sky130_fd_sc_hd__a2bb2o_2(A1_N, A2_N, B1, B2, X);
  input A1_N;
  input A2_N;
  input B1;
  input B2;
  output X;
  assign X = ((~A1_N & ~A2_N) | (B1 & B2));
endmodule

module sky130_fd_sc_hd__a31o_2(A1, A2, A3, B1, X);
  input A1;
  input A2;
  input A3;
  input B1;
  output X;
  assign X = ((A1 & A2 & A3) | (B1));
endmodule

module sky130_fd_sc_hd__a31oi_2(A1, A2, A3, B1, Y);
  input A1;
  input A2;
  input A3;
  input B1;
  output Y;
  assign Y = ~((A1 & A2 & A3) | (B1));
endmodule

module sky130_fd_sc_hd__a32o_2(A1, A2, A3, B1, B2, X);
  input A1;
  input A2;
  input A3;
  input B1;
  input B2;
  output X;
  assign X = ((A1 & A2 & A3) | (B1 & B2));
endmodule

module sky130_fd_sc_hd__and2_2(A, B, X);
  input A;
  input B;
  output X;
  assign X = (A & B);
endmodule

module sky130_fd_sc_hd__and2b_2(A_N, B, X);
  input A_N;
  input B;
  output X;
  assign X = (~A_N & B);
endmodule

module sky130_fd_sc_hd__and3_2(A, B, C, X);
  input A;
  input B;
  input C;
  output X;
  assign X = (A & B & C);
endmodule

module sky130_fd_sc_hd__and3b_2(A_N, B, C, X);
  input A_N;
  input B;
  input C;
  output X;
  assign X = (~A_N & B & C);
endmodule

module sky130_fd_sc_hd__and4_2(A, B, C, D, X);
  input A;
  input B;
  input C;
  input D;
  output X;
  assign X = (A & B & C & D);
endmodule

module sky130_fd_sc_hd__and4b_2(A_N, B, C, D, X);
  input A_N;
  input B;
  input C;
  input D;
  output X;
  assign X = (~A_N & B & C & D);
endmodule

module sky130_fd_sc_hd__and4bb_2(A_N, B_N, C, D, X);
  input A_N;
  input B_N;
  input C;
  input D;
  output X;
  assign X = (~A_N & ~B_N & C & D);
endmodule

module sky130_fd_sc_hd__conb_1(LO);
  output LO;
  assign LO = 1'b0;
endmodule

module sky130_fd_sc_hd__dfrtp_2(CLK, D, RESET_B, Q);
  input CLK;
  input D;
  input RESET_B;
  output Q;
  reg q_reg;
  always @(posedge CLK or negedge RESET_B) begin
    if (!RESET_B) q_reg <= 1'b0;
    else q_reg <= D;
  end
  assign Q = q_reg;
endmodule

module sky130_fd_sc_hd__dfstp_2(CLK, D, SET_B, Q);
  input CLK;
  input D;
  input SET_B;
  output Q;
  reg q_reg;
  always @(posedge CLK or negedge SET_B) begin
    if (!SET_B) q_reg <= 1'b1;
    else q_reg <= D;
  end
  assign Q = q_reg;
endmodule

module sky130_fd_sc_hd__dfxtp_2(CLK, D, Q);
  input CLK;
  input D;
  output Q;
  reg q_reg;
  always @(posedge CLK) q_reg <= D;
  assign Q = q_reg;
endmodule

module sky130_fd_sc_hd__inv_2(A, Y);
  input A;
  output Y;
  assign Y = ~A;
endmodule

module sky130_fd_sc_hd__mux2_1(A0, A1, S, X);
  input A0;
  input A1;
  input S;
  output X;
  assign X = (S ? A1 : A0);
endmodule

module sky130_fd_sc_hd__nand2_2(A, B, Y);
  input A;
  input B;
  output Y;
  assign Y = ~(A & B);
endmodule

module sky130_fd_sc_hd__nand2b_2(A_N, B, Y);
  input A_N;
  input B;
  output Y;
  assign Y = ~(~A_N & B);
endmodule

module sky130_fd_sc_hd__nand3_2(A, B, C, Y);
  input A;
  input B;
  input C;
  output Y;
  assign Y = ~(A & B & C);
endmodule

module sky130_fd_sc_hd__nand3b_2(A_N, B, C, Y);
  input A_N;
  input B;
  input C;
  output Y;
  assign Y = ~(~A_N & B & C);
endmodule

module sky130_fd_sc_hd__nor2_2(A, B, Y);
  input A;
  input B;
  output Y;
  assign Y = ~(A | B);
endmodule

module sky130_fd_sc_hd__nor3_2(A, B, C, Y);
  input A;
  input B;
  input C;
  output Y;
  assign Y = ~(A | B | C);
endmodule

module sky130_fd_sc_hd__nor3b_2(A, B, C_N, Y);
  input A;
  input B;
  input C_N;
  output Y;
  assign Y = ~(A | B | ~C_N);
endmodule

module sky130_fd_sc_hd__nor4_2(A, B, C, D, Y);
  input A;
  input B;
  input C;
  input D;
  output Y;
  assign Y = ~(A | B | C | D);
endmodule

module sky130_fd_sc_hd__o211a_2(A1, A2, B1, C1, X);
  input A1;
  input A2;
  input B1;
  input C1;
  output X;
  assign X = ((A1 | A2) & (B1) & (C1));
endmodule

module sky130_fd_sc_hd__o21a_2(A1, A2, B1, X);
  input A1;
  input A2;
  input B1;
  output X;
  assign X = ((A1 | A2) & (B1));
endmodule

module sky130_fd_sc_hd__o21ai_2(A1, A2, B1, Y);
  input A1;
  input A2;
  input B1;
  output Y;
  assign Y = ~((A1 | A2) & (B1));
endmodule

module sky130_fd_sc_hd__o221a_2(A1, A2, B1, B2, C1, X);
  input A1;
  input A2;
  input B1;
  input B2;
  input C1;
  output X;
  assign X = ((A1 | A2) & (B1 | B2) & (C1));
endmodule

module sky130_fd_sc_hd__o22a_2(A1, A2, B1, B2, X);
  input A1;
  input A2;
  input B1;
  input B2;
  output X;
  assign X = ((A1 | A2) & (B1 | B2));
endmodule

module sky130_fd_sc_hd__o22ai_2(A1, A2, B1, B2, Y);
  input A1;
  input A2;
  input B1;
  input B2;
  output Y;
  assign Y = ~((A1 | A2) & (B1 | B2));
endmodule

module sky130_fd_sc_hd__o2bb2a_2(A1_N, A2_N, B1, B2, X);
  input A1_N;
  input A2_N;
  input B1;
  input B2;
  output X;
  assign X = ((~A1_N | ~A2_N) & (B1 | B2));
endmodule

module sky130_fd_sc_hd__o31a_2(A1, A2, A3, B1, X);
  input A1;
  input A2;
  input A3;
  input B1;
  output X;
  assign X = ((A1 | A2 | A3) & (B1));
endmodule

module sky130_fd_sc_hd__o31ai_2(A1, A2, A3, B1, Y);
  input A1;
  input A2;
  input A3;
  input B1;
  output Y;
  assign Y = ~((A1 | A2 | A3) & (B1));
endmodule

module sky130_fd_sc_hd__o32a_2(A1, A2, A3, B1, B2, X);
  input A1;
  input A2;
  input A3;
  input B1;
  input B2;
  output X;
  assign X = ((A1 | A2 | A3) & (B1 | B2));
endmodule

module sky130_fd_sc_hd__o41a_2(A1, A2, A3, A4, B1, X);
  input A1;
  input A2;
  input A3;
  input A4;
  input B1;
  output X;
  assign X = ((A1 | A2 | A3 | A4) & (B1));
endmodule

module sky130_fd_sc_hd__o41ai_2(A1, A2, A3, A4, B1, Y);
  input A1;
  input A2;
  input A3;
  input A4;
  input B1;
  output Y;
  assign Y = ~((A1 | A2 | A3 | A4) & (B1));
endmodule

module sky130_fd_sc_hd__or2_2(A, B, X);
  input A;
  input B;
  output X;
  assign X = (A | B);
endmodule

module sky130_fd_sc_hd__or3_2(A, B, C, X);
  input A;
  input B;
  input C;
  output X;
  assign X = (A | B | C);
endmodule

module sky130_fd_sc_hd__or3b_2(A, B, C_N, X);
  input A;
  input B;
  input C_N;
  output X;
  assign X = (A | B | ~C_N);
endmodule

module sky130_fd_sc_hd__or4_2(A, B, C, D, X);
  input A;
  input B;
  input C;
  input D;
  output X;
  assign X = (A | B | C | D);
endmodule

module sky130_fd_sc_hd__or4b_2(A, B, C, D_N, X);
  input A;
  input B;
  input C;
  input D_N;
  output X;
  assign X = (A | B | C | ~D_N);
endmodule

module sky130_fd_sc_hd__or4bb_2(A, B, C_N, D_N, X);
  input A;
  input B;
  input C_N;
  input D_N;
  output X;
  assign X = (A | B | ~C_N | ~D_N);
endmodule

module sky130_fd_sc_hd__xnor2_2(A, B, Y);
  input A;
  input B;
  output Y;
  assign Y = ~(A ^ B);
endmodule

module sky130_fd_sc_hd__xor2_2(A, B, X);
  input A;
  input B;
  output X;
  assign X = (A ^ B);
endmodule

