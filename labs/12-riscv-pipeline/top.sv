module top(
    input  CLOCK_50,           // 50 MHz
    input  [9:0] SW,
    input  [3:0] KEY,           // KEY[3] = reset
    output reg [9:0] LEDR,
    output [6:0] HEX5, HEX4, HEX3, HEX2, HEX1, HEX0
);

    // Clock e Reset
    reg [31:0] counter = 0;

    always @(posedge CLOCK_50)
        counter <= counter + 1;

    wire clk   = counter[21];   // clock lento (~12 Hz)
    wire reset = ~KEY[3];        // reset ativo em nível baixo

    reg [31:0] cycle_counter;
    always @(posedge clk)
    if (!reset)
        cycle_counter <= cycle_counter + 1;  // contar ciclos para calculo de desempenho

    // Sinais do processador
    wire [31:0] pc, instr;
    wire [31:0] addr, writedata;
    wire [31:0] readdata;
    wire        memwrite;
    wire [3:0]  writemask;

    // CPU Pipeline
    riscvpipeline cpu (
        .clk(clk),
        .reset(reset),
        .pc(pc),
        .instr(instr),
        .addr(addr),
        .writedata(writedata),
        .memwrite(memwrite),
        .readdata(readdata),
        .writemask(writemask)
    );

    // Memória de Instruções (ROM)
    mem #("text.hex") instr_mem (
    .clk(clk),
    .we(1'b0),              // nunca escreve
    .a(pc),
    .wd(32'b0),
    .rd(instr),
    .mem_wmask(4'b0000)
);

    // Memória de Dados (RAM)
 wire [31:0] MEM_readdata;

mem #("data.hex") data_mem (
    .clk(clk),
    .we(memwrite & isRAM),
    .a(addr),
    .wd(writedata),
    .rd(MEM_readdata),
    .mem_wmask(writemask)
);

    // Memory-Mapped I/O
    localparam IO_LEDS_bit = 2;  // 0x00000104
    localparam IO_HEX_bit  = 3;  // 0x00000108
    localparam IO_KEY_bit  = 4;  // 0x00000110
    localparam IO_SW_bit   = 5;  // 0x00000120

    reg  [23:0] hex_digits;
    wire [31:0] IO_readdata;

    // Escrita em dispositivos
    always @(posedge clk) begin
        if (memwrite & isIO) begin
            if (addr[IO_LEDS_bit])
                LEDR <= writedata[9:0];

            if (addr[IO_HEX_bit])
                hex_digits <= writedata[23:0];
        end
    end

    // Leitura de dispositivos
    assign IO_readdata =
        addr[IO_KEY_bit] ? {28'b0, KEY} :
        addr[IO_SW_bit]  ? {22'b0, SW}  :
                           32'b0;

    // MUX final de leitura (RAM ou I/O)
    assign readdata = isIO ? IO_readdata : MEM_readdata;

    // Displays de 7 segmentos
    dec7seg hex0(hex_digits[ 3: 0], HEX0);
    dec7seg hex1(hex_digits[ 7: 4], HEX1);
    dec7seg hex2(hex_digits[11: 8], HEX2);
    dec7seg hex3(hex_digits[15:12], HEX3);
    dec7seg hex4(hex_digits[19:16], HEX4);
    dec7seg hex5(hex_digits[23:20], HEX5);

endmodule
