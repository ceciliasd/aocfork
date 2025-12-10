module mem (
  input  logic        clk, we,
  input  logic [31:0] a, wd,
  output logic [31:0] rd,
  input  logic [31:0] va,
  output logic [31:0] vd,
  input               mem_rstrb,
  input  logic [3:0]  mem_wmask,
  input  logic        VGA_CLK // Não usado na leitura (usamos clk)
);

  // MUDANÇA MÁGICA: "Packed Array" ([3:0][7:0])
  // Isso define explicitamente 4 bytes por palavra.
  // O Quartus adora isso para inferir RAM M10K com Byte Enable.
  (* ramstyle = "M10K" *) logic [3:0][7:0] RAM [0:255];

  // Inicialização: Funciona porque o SystemVerilog sabe carregar
  // um hex de 32 bits para dentro de um array empacotado [3:0][7:0].
  initial begin
    $readmemh("riscv.hex", RAM);
  end

  // Endereçamento
  logic [7:0] word_addr_cpu;
  logic [7:0] word_addr_vga;
  assign word_addr_cpu = a[9:2]; 
  assign word_addr_vga = va[9:2];

  // --------------------------------------------------------
  // Porta A: CPU (Escrita com Byte Select Real)
  // --------------------------------------------------------
  always_ff @(posedge clk) begin
    if (we) begin
      // Agora acessamos cada byte individualmente pelo índice [0]..[3]
      // Isso mapeia DIRETO para o hardware da M10K.
      if (mem_wmask[0]) RAM[word_addr_cpu][0] <= wd[ 7: 0];
      if (mem_wmask[1]) RAM[word_addr_cpu][1] <= wd[15: 8];
      if (mem_wmask[2]) RAM[word_addr_cpu][2] <= wd[23:16];
      if (mem_wmask[3]) RAM[word_addr_cpu][3] <= wd[31:24];
    end
    
    // Leitura: O cast para 32 bits é automático
    rd <= RAM[word_addr_cpu];
  end

  // --------------------------------------------------------
  // Porta B: VGA (Leitura Rápida)
  // --------------------------------------------------------
  always_ff @(posedge clk) begin 
    vd <= RAM[word_addr_vga];
  end

endmodule
