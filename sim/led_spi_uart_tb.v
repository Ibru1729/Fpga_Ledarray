//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 12/01/2021 08:39:12 PM
// Design Name: 
// Module Name: spi_tb
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////

`define assert(signal, value) \
	if (signal !== value) begin \
		$display("Assertion Failed in %m : signal != value), when signal = %b ", signal); \
	end

`timescale 1ns/1ps
module led_spi_uart_tb(

    );

	parameter CLK_FREQ = 100_000_000;
	parameter UART_BAUD_RATE = 115_200;
	parameter SPI_CLK_FREQ = 5_000_000;
    
    reg i_clk, i_rst;
	always
		# (1000_000_000 / CLK_FREQ / 2) i_clk = ~i_clk;
    reg i_wr;
    reg i_btn;
    wire o_spi_load, o_spi_data, o_spi_clk;
    wire [3:1] jd;
    assign {o_spi_data, o_spi_load, o_spi_clk} = jd[3:1];
    reg i_uart_rx;
    wire o_uart_tx;

	//////////////////////////////
	// Uart Transmitter
	/////////////////////////////
	
	/* verilator lint_off UNUSED */
	wire uart_ready;
	/* verilator lint_on UNUSED */
	reg uart_i_wr;
	reg [7:0] uart_tx_data;
	
	txuart #(.UART_COUNTER_MAX(CLK_FREQ / UART_BAUD_RATE)) txuart_i0 (
				.clk(i_clk),
				.uart_tx(o_uart_tx),
				.send(uart_i_wr),
				.ready(uart_ready),
				.rst(1'b1),
				.data(uart_tx_data)
			);


    led_spi_uart #(.DEBOUNCE_TIME_US(10), .CLK_FREQ(CLK_FREQ), .UART_BAUD_RATE(UART_BAUD_RATE), .SPI_CLK_FREQ(SPI_CLK_FREQ)) uut (
	    .i_clk(i_clk),
		.i_btn(i_btn),
		.i_uart_rx(o_uart_tx),
		.o_uart_tx(i_uart_rx),
		.jd(jd[3:1])
        );
	
	 
	////////////////////////////////////////////
	// UART Reciever
	////////////////////////////////////////////
	wire rx_stb;
	wire [7:0] rx_data;
	rxuart #(.UART_COUNTER_MAX(CLK_FREQ / UART_BAUD_RATE)) rxuart_i0 (
				.i_clk(i_clk),
				.i_uart_rx(i_uart_rx),
				.o_stb(rx_stb),
				.o_data(rx_data)
			);


   initial begin
      //  Wait for Global Reset to Complete
      // #100;
      // data_in = 8'h00;
      // #50 `assert(data_out, 8'h63);
      // data_in = 8'h70;
      // #50 `assert(data_out, 8'h52);
      // data_in = 8'hff;
      // #50 `assert(data_out, 8'h16);
      // $finish;
      $dumpfile ("led_spi_uart_tb.vcd");
      $dumpvars (0, led_spi_uart_tb);
	  i_clk = 1'b0;
      
   end
			
			
endmodule
