// Auto-generated functional SKY130 cell wrappers for Yosys LEC.
// Generated from the synthesized netlist's referenced cell/pin set.
module sky130_fd_sc_hd__a211o_1(A1, A2, B1, C1, VGND, VNB, VPB, VPWR, X);
  input A1;
  input A2;
  input B1;
  input C1;
  input VGND;
  input VNB;
  input VPB;
  input VPWR;
  output X;
  assign X = ((A1 & A2) | (B1) | (C1));
endmodule

module sky130_fd_sc_hd__a21boi_2(A1, A2, B1_N, VGND, VNB, VPB, VPWR, Y);
  input A1;
  input A2;
  input B1_N;
  input VGND;
  input VNB;
  input VPB;
  input VPWR;
  output Y;
  assign Y = ~((A1 & A2) | (~B1_N));
endmodule

module sky130_fd_sc_hd__a21o_1(A1, A2, B1, VGND, VNB, VPB, VPWR, X);
  input A1;
  input A2;
  input B1;
  input VGND;
  input VNB;
  input VPB;
  input VPWR;
  output X;
  assign X = ((A1 & A2) | (B1));
endmodule

module sky130_fd_sc_hd__a21oi_1(A1, A2, B1, VGND, VNB, VPB, VPWR, Y);
  input A1;
  input A2;
  input B1;
  input VGND;
  input VNB;
  input VPB;
  input VPWR;
  output Y;
  assign Y = ~((A1 & A2) | (B1));
endmodule

module sky130_fd_sc_hd__a21oi_2(A1, A2, B1, VGND, VNB, VPB, VPWR, Y);
  input A1;
  input A2;
  input B1;
  input VGND;
  input VNB;
  input VPB;
  input VPWR;
  output Y;
  assign Y = ~((A1 & A2) | (B1));
endmodule

module sky130_fd_sc_hd__a221o_1(A1, A2, B1, B2, C1, VGND, VNB, VPB, VPWR, X);
  input A1;
  input A2;
  input B1;
  input B2;
  input C1;
  input VGND;
  input VNB;
  input VPB;
  input VPWR;
  output X;
  assign X = ((A1 & A2) | (B1 & B2) | (C1));
endmodule

module sky130_fd_sc_hd__a22o_1(A1, A2, B1, B2, VGND, VNB, VPB, VPWR, X);
  input A1;
  input A2;
  input B1;
  input B2;
  input VGND;
  input VNB;
  input VPB;
  input VPWR;
  output X;
  assign X = ((A1 & A2) | (B1 & B2));
endmodule

module sky130_fd_sc_hd__a22oi_1(A1, A2, B1, B2, VGND, VNB, VPB, VPWR, Y);
  input A1;
  input A2;
  input B1;
  input B2;
  input VGND;
  input VNB;
  input VPB;
  input VPWR;
  output Y;
  assign Y = ~((A1 & A2) | (B1 & B2));
endmodule

module sky130_fd_sc_hd__a2bb2o_1(A1_N, A2_N, B1, B2, VGND, VNB, VPB, VPWR, X);
  input A1_N;
  input A2_N;
  input B1;
  input B2;
  input VGND;
  input VNB;
  input VPB;
  input VPWR;
  output X;
  assign X = ((~A1_N & ~A2_N) | (B1 & B2));
endmodule

module sky130_fd_sc_hd__a31o_1(A1, A2, A3, B1, VGND, VNB, VPB, VPWR, X);
  input A1;
  input A2;
  input A3;
  input B1;
  input VGND;
  input VNB;
  input VPB;
  input VPWR;
  output X;
  assign X = ((A1 & A2 & A3) | (B1));
endmodule

module sky130_fd_sc_hd__a32o_1(A1, A2, A3, B1, B2, VGND, VNB, VPB, VPWR, X);
  input A1;
  input A2;
  input A3;
  input B1;
  input B2;
  input VGND;
  input VNB;
  input VPB;
  input VPWR;
  output X;
  assign X = ((A1 & A2 & A3) | (B1 & B2));
endmodule

module sky130_fd_sc_hd__a41o_1(A1, A2, A3, A4, B1, VGND, VNB, VPB, VPWR, X);
  input A1;
  input A2;
  input A3;
  input A4;
  input B1;
  input VGND;
  input VNB;
  input VPB;
  input VPWR;
  output X;
  assign X = ((A1 & A2 & A3 & A4) | (B1));
endmodule

module sky130_fd_sc_hd__and2_1(A, B, VGND, VNB, VPB, VPWR, X);
  input A;
  input B;
  input VGND;
  input VNB;
  input VPB;
  input VPWR;
  output X;
  assign X = (A & B & VGND & VNB & VPB & VPWR);
endmodule

module sky130_fd_sc_hd__and2b_1(A_N, B, VGND, VNB, VPB, VPWR, X);
  input A_N;
  input B;
  input VGND;
  input VNB;
  input VPB;
  input VPWR;
  output X;
  assign X = (~A_N & B & VGND & VNB & VPB & VPWR);
endmodule

module sky130_fd_sc_hd__and3_1(A, B, C, VGND, VNB, VPB, VPWR, X);
  input A;
  input B;
  input C;
  input VGND;
  input VNB;
  input VPB;
  input VPWR;
  output X;
  assign X = (A & B & C & VGND & VNB & VPB & VPWR);
endmodule

module sky130_fd_sc_hd__and4b_1(A_N, B, C, D, VGND, VNB, VPB, VPWR, X);
  input A_N;
  input B;
  input C;
  input D;
  input VGND;
  input VNB;
  input VPB;
  input VPWR;
  output X;
  assign X = (~A_N & B & C & D & VGND & VNB & VPB & VPWR);
endmodule

module sky130_fd_sc_hd__buf_1(A, VGND, VNB, VPB, VPWR, X);
  input A;
  input VGND;
  input VNB;
  input VPB;
  input VPWR;
  output X;
  assign X = A;
endmodule

module sky130_fd_sc_hd__buf_12(A, VGND, VNB, VPB, VPWR, X);
  input A;
  input VGND;
  input VNB;
  input VPB;
  input VPWR;
  output X;
  assign X = A;
endmodule

module sky130_fd_sc_hd__buf_4(A, VGND, VNB, VPB, VPWR, X);
  input A;
  input VGND;
  input VNB;
  input VPB;
  input VPWR;
  output X;
  assign X = A;
endmodule

module sky130_fd_sc_hd__bufinv_16(A, VGND, VNB, VPB, VPWR);
  input A;
  input VGND;
  input VNB;
  input VPB;
  input VPWR;
endmodule

module sky130_fd_sc_hd__clkbuf_1(A, VGND, VNB, VPB, VPWR, X);
  input A;
  input VGND;
  input VNB;
  input VPB;
  input VPWR;
  output X;
  assign X = A;
endmodule

module sky130_fd_sc_hd__clkbuf_16(A, VGND, VNB, VPB, VPWR, X);
  input A;
  input VGND;
  input VNB;
  input VPB;
  input VPWR;
  output X;
  assign X = A;
endmodule

module sky130_fd_sc_hd__clkbuf_2(A, VGND, VNB, VPB, VPWR, X);
  input A;
  input VGND;
  input VNB;
  input VPB;
  input VPWR;
  output X;
  assign X = A;
endmodule

module sky130_fd_sc_hd__clkbuf_8(A, VGND, VNB, VPB, VPWR);
  input A;
  input VGND;
  input VNB;
  input VPB;
  input VPWR;
endmodule

module sky130_fd_sc_hd__clkinv_2(A, VGND, VNB, VPB, VPWR);
  input A;
  input VGND;
  input VNB;
  input VPB;
  input VPWR;
endmodule

module sky130_fd_sc_hd__clkinvlp_4(A, VGND, VNB, VPB, VPWR);
  input A;
  input VGND;
  input VNB;
  input VPB;
  input VPWR;
endmodule

module sky130_fd_sc_hd__decap_3(VGND, VNB, VPB, VPWR);
  input VGND;
  input VNB;
  input VPB;
  input VPWR;
endmodule

module sky130_fd_sc_hd__dfrtp_1(CLK, D, RESET_B, VGND, VNB, VPB, VPWR, Q);
  input CLK;
  input D;
  input RESET_B;
  input VGND;
  input VNB;
  input VPB;
  input VPWR;
  output Q;
  reg q_reg;
  always @(posedge CLK or negedge RESET_B) begin
    if (!RESET_B) q_reg <= 1'b0;
    else q_reg <= D;
  end
  assign Q = q_reg;
endmodule

module sky130_fd_sc_hd__dfrtp_4(CLK, D, RESET_B, VGND, VNB, VPB, VPWR, Q);
  input CLK;
  input D;
  input RESET_B;
  input VGND;
  input VNB;
  input VPB;
  input VPWR;
  output Q;
  reg q_reg;
  always @(posedge CLK or negedge RESET_B) begin
    if (!RESET_B) q_reg <= 1'b0;
    else q_reg <= D;
  end
  assign Q = q_reg;
endmodule

module sky130_fd_sc_hd__dlymetal6s2s_1(A, VGND, VNB, VPB, VPWR, X);
  input A;
  input VGND;
  input VNB;
  input VPB;
  input VPWR;
  output X;
  assign X = A;
endmodule

module sky130_fd_sc_hd__inv_2(A, VGND, VNB, VPB, VPWR, Y);
  input A;
  input VGND;
  input VNB;
  input VPB;
  input VPWR;
  output Y;
  assign Y = ~A;
endmodule

module sky130_fd_sc_hd__mux2_1(A0, A1, S, VGND, VNB, VPB, VPWR, X);
  input A0;
  input A1;
  input S;
  input VGND;
  input VNB;
  input VPB;
  input VPWR;
  output X;
  assign X = (S ? A1 : A0);
endmodule

module sky130_fd_sc_hd__mux2_2(A0, A1, S, VGND, VNB, VPB, VPWR, X);
  input A0;
  input A1;
  input S;
  input VGND;
  input VNB;
  input VPB;
  input VPWR;
  output X;
  assign X = (S ? A1 : A0);
endmodule

module sky130_fd_sc_hd__nand2_1(A, B, VGND, VNB, VPB, VPWR, Y);
  input A;
  input B;
  input VGND;
  input VNB;
  input VPB;
  input VPWR;
  output Y;
  assign Y = ~(A & B & VGND & VNB & VPB & VPWR);
endmodule

module sky130_fd_sc_hd__nand2b_1(A_N, B, VGND, VNB, VPB, VPWR, Y);
  input A_N;
  input B;
  input VGND;
  input VNB;
  input VPB;
  input VPWR;
  output Y;
  assign Y = ~(~A_N & B & VGND & VNB & VPB & VPWR);
endmodule

module sky130_fd_sc_hd__nand3_1(A, B, C, VGND, VNB, VPB, VPWR, Y);
  input A;
  input B;
  input C;
  input VGND;
  input VNB;
  input VPB;
  input VPWR;
  output Y;
  assign Y = ~(A & B & C & VGND & VNB & VPB & VPWR);
endmodule

module sky130_fd_sc_hd__nand4_1(A, B, C, D, VGND, VNB, VPB, VPWR, Y);
  input A;
  input B;
  input C;
  input D;
  input VGND;
  input VNB;
  input VPB;
  input VPWR;
  output Y;
  assign Y = ~(A & B & C & D & VGND & VNB & VPB & VPWR);
endmodule

module sky130_fd_sc_hd__nor2_1(A, B, VGND, VNB, VPB, VPWR, Y);
  input A;
  input B;
  input VGND;
  input VNB;
  input VPB;
  input VPWR;
  output Y;
  assign Y = ~(A | B | VGND | VNB | VPB | VPWR);
endmodule

module sky130_fd_sc_hd__nor2_4(A, B, VGND, VNB, VPB, VPWR, Y);
  input A;
  input B;
  input VGND;
  input VNB;
  input VPB;
  input VPWR;
  output Y;
  assign Y = ~(A | B | VGND | VNB | VPB | VPWR);
endmodule

module sky130_fd_sc_hd__nor2_8(A, B, VGND, VNB, VPB, VPWR, Y);
  input A;
  input B;
  input VGND;
  input VNB;
  input VPB;
  input VPWR;
  output Y;
  assign Y = ~(A | B | VGND | VNB | VPB | VPWR);
endmodule

module sky130_fd_sc_hd__nor3_1(A, B, C, VGND, VNB, VPB, VPWR, Y);
  input A;
  input B;
  input C;
  input VGND;
  input VNB;
  input VPB;
  input VPWR;
  output Y;
  assign Y = ~(A | B | C | VGND | VNB | VPB | VPWR);
endmodule

module sky130_fd_sc_hd__nor4_4(A, B, C, D, VGND, VNB, VPB, VPWR, Y);
  input A;
  input B;
  input C;
  input D;
  input VGND;
  input VNB;
  input VPB;
  input VPWR;
  output Y;
  assign Y = ~(A | B | C | D | VGND | VNB | VPB | VPWR);
endmodule

module sky130_fd_sc_hd__o2111ai_2(A1, A2, B1, C1, D1, VGND, VNB, VPB, VPWR, Y);
  input A1;
  input A2;
  input B1;
  input C1;
  input D1;
  input VGND;
  input VNB;
  input VPB;
  input VPWR;
  output Y;
  assign Y = ~((A1 | A2) & (B1) & (C1) & (D1));
endmodule

module sky130_fd_sc_hd__o211ai_1(A1, A2, B1, C1, VGND, VNB, VPB, VPWR, Y);
  input A1;
  input A2;
  input B1;
  input C1;
  input VGND;
  input VNB;
  input VPB;
  input VPWR;
  output Y;
  assign Y = ~((A1 | A2) & (B1) & (C1));
endmodule

module sky130_fd_sc_hd__o21a_1(A1, A2, B1, VGND, VNB, VPB, VPWR, X);
  input A1;
  input A2;
  input B1;
  input VGND;
  input VNB;
  input VPB;
  input VPWR;
  output X;
  assign X = ((A1 | A2) & (B1));
endmodule

module sky130_fd_sc_hd__o21ai_1(A1, A2, B1, VGND, VNB, VPB, VPWR, Y);
  input A1;
  input A2;
  input B1;
  input VGND;
  input VNB;
  input VPB;
  input VPWR;
  output Y;
  assign Y = ~((A1 | A2) & (B1));
endmodule

module sky130_fd_sc_hd__o21ba_1(A1, A2, B1_N, VGND, VNB, VPB, VPWR, X);
  input A1;
  input A2;
  input B1_N;
  input VGND;
  input VNB;
  input VPB;
  input VPWR;
  output X;
  assign X = ((A1 | A2) & (~B1_N));
endmodule

module sky130_fd_sc_hd__o221a_1(A1, A2, B1, B2, C1, VGND, VNB, VPB, VPWR, X);
  input A1;
  input A2;
  input B1;
  input B2;
  input C1;
  input VGND;
  input VNB;
  input VPB;
  input VPWR;
  output X;
  assign X = ((A1 | A2) & (B1 | B2) & (C1));
endmodule

module sky130_fd_sc_hd__o22a_1(A1, A2, B1, B2, VGND, VNB, VPB, VPWR, X);
  input A1;
  input A2;
  input B1;
  input B2;
  input VGND;
  input VNB;
  input VPB;
  input VPWR;
  output X;
  assign X = ((A1 | A2) & (B1 | B2));
endmodule

module sky130_fd_sc_hd__o2bb2a_1(A1_N, A2_N, B1, B2, VGND, VNB, VPB, VPWR, X);
  input A1_N;
  input A2_N;
  input B1;
  input B2;
  input VGND;
  input VNB;
  input VPB;
  input VPWR;
  output X;
  assign X = ((~A1_N | ~A2_N) & (B1 | B2));
endmodule

module sky130_fd_sc_hd__o311a_1(A1, A2, A3, B1, C1, VGND, VNB, VPB, VPWR, X);
  input A1;
  input A2;
  input A3;
  input B1;
  input C1;
  input VGND;
  input VNB;
  input VPB;
  input VPWR;
  output X;
  assign X = ((A1 | A2 | A3) & (B1) & (C1));
endmodule

module sky130_fd_sc_hd__o31a_1(A1, A2, A3, B1, VGND, VNB, VPB, VPWR, X);
  input A1;
  input A2;
  input A3;
  input B1;
  input VGND;
  input VNB;
  input VPB;
  input VPWR;
  output X;
  assign X = ((A1 | A2 | A3) & (B1));
endmodule

module sky130_fd_sc_hd__or2_1(A, B, VGND, VNB, VPB, VPWR, X);
  input A;
  input B;
  input VGND;
  input VNB;
  input VPB;
  input VPWR;
  output X;
  assign X = (A | B | VGND | VNB | VPB | VPWR);
endmodule

module sky130_fd_sc_hd__or2_2(A, B, VGND, VNB, VPB, VPWR, X);
  input A;
  input B;
  input VGND;
  input VNB;
  input VPB;
  input VPWR;
  output X;
  assign X = (A | B | VGND | VNB | VPB | VPWR);
endmodule

module sky130_fd_sc_hd__or3_1(A, B, C, VGND, VNB, VPB, VPWR, X);
  input A;
  input B;
  input C;
  input VGND;
  input VNB;
  input VPB;
  input VPWR;
  output X;
  assign X = (A | B | C | VGND | VNB | VPB | VPWR);
endmodule

module sky130_fd_sc_hd__or3_4(A, B, C, VGND, VNB, VPB, VPWR, X);
  input A;
  input B;
  input C;
  input VGND;
  input VNB;
  input VPB;
  input VPWR;
  output X;
  assign X = (A | B | C | VGND | VNB | VPB | VPWR);
endmodule

module sky130_fd_sc_hd__or3b_1(A, B, C_N, VGND, VNB, VPB, VPWR, X);
  input A;
  input B;
  input C_N;
  input VGND;
  input VNB;
  input VPB;
  input VPWR;
  output X;
  assign X = (A | B | ~C_N | VGND | VNB | VPB | VPWR);
endmodule

module sky130_fd_sc_hd__or4_1(A, B, C, D, VGND, VNB, VPB, VPWR, X);
  input A;
  input B;
  input C;
  input D;
  input VGND;
  input VNB;
  input VPB;
  input VPWR;
  output X;
  assign X = (A | B | C | D | VGND | VNB | VPB | VPWR);
endmodule

module sky130_fd_sc_hd__or4_4(A, B, C, D, VGND, VNB, VPB, VPWR, X);
  input A;
  input B;
  input C;
  input D;
  input VGND;
  input VNB;
  input VPB;
  input VPWR;
  output X;
  assign X = (A | B | C | D | VGND | VNB | VPB | VPWR);
endmodule

module sky130_fd_sc_hd__or4b_1(A, B, C, D_N, VGND, VNB, VPB, VPWR, X);
  input A;
  input B;
  input C;
  input D_N;
  input VGND;
  input VNB;
  input VPB;
  input VPWR;
  output X;
  assign X = (A | B | C | ~D_N | VGND | VNB | VPB | VPWR);
endmodule

module sky130_fd_sc_hd__or4b_4(A, B, C, D_N, VGND, VNB, VPB, VPWR, X);
  input A;
  input B;
  input C;
  input D_N;
  input VGND;
  input VNB;
  input VPB;
  input VPWR;
  output X;
  assign X = (A | B | C | ~D_N | VGND | VNB | VPB | VPWR);
endmodule

module sky130_fd_sc_hd__or4bb_1(A, B, C_N, D_N, VGND, VNB, VPB, VPWR, X);
  input A;
  input B;
  input C_N;
  input D_N;
  input VGND;
  input VNB;
  input VPB;
  input VPWR;
  output X;
  assign X = (A | B | ~C_N | ~D_N | VGND | VNB | VPB | VPWR);
endmodule

module sky130_fd_sc_hd__tapvpwrvgnd_1(VGND, VPWR);
  input VGND;
  input VPWR;
endmodule

module sky130_fd_sc_hd__xnor2_1(A, B, VGND, VNB, VPB, VPWR, Y);
  input A;
  input B;
  input VGND;
  input VNB;
  input VPB;
  input VPWR;
  output Y;
  assign Y = ~(A ^ B);
endmodule

module sky130_fd_sc_hd__xor2_1(A, B, VGND, VNB, VPB, VPWR, X);
  input A;
  input B;
  input VGND;
  input VNB;
  input VPB;
  input VPWR;
  output X;
  assign X = (A ^ B);
endmodule

// Unsupported cells intentionally left absent so Yosys reports unresolved models:
// - sky130_fd_sc_hd__clkinv_4
