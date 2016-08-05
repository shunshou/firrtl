circuit sram6t :
  module sram6t :
    input clk : Clock
    input reset : UInt<1>
    output io : {flip en : UInt<1>, flip wen : UInt<1>, flip waddr : UInt<8>, flip wdata : UInt<32>, flip raddr : UInt<8>, rdata : UInt<32>}
    io is invalid
    smem mem : UInt<32>[128]
    node T_0 = eq(io.wen, UInt<1>("h00"))
    node T_1 = and(io.en, T_0)
    wire T_2 : UInt
    T_2 is invalid
    when T_1 :
      T_2 <= io.raddr
    read mport T_3 = mem[T_2], clk
    io.rdata <= T_3
    node T_4 = and(io.en, io.wen)
    when T_4 :
      write mport T_5 = mem[io.waddr], clk
      T_5 <= io.wdata