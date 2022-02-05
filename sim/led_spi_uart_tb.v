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

module led_spi_uart_tb(

    );
    
    reg i_clk, i_rst;
    reg i_wr;
    reg i_btn;
    wire o_spi_load, o_spi_data, o_spi_clk;
    wire [3:1] jd;
    assign {o_spi_data, o_spi_load, o_spi_clk} = jd[3:1];
    reg i_uart_rx;
    wire o_uart_tx;
    led_spi_uart #(.DEBOUNCE_TIME_US(10), .CLK_FREQ(100_000_000), .UART_BAUD_RATE(115_200), .SPI_CLK_FREQ(5_000_000)) uut (
	    .i_clk(i_clk),
		.i_btn(i_btn),
		.i_uart_rx(i_uart_rx),
		.o_uart_tx(o_uart_tx),
		.jd(jd[3:1])
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
      
   end
			
			
endmodule
