`default_nettype none


`ifndef MODULE_LED_SPI_UART
`define MODULE_LED_SPI_UART

module led_spi_uart (
	input wire i_clk,
	input wire i_btn,
	output wire [3:1] jd,
	input wire i_uart_rx,
	output wire o_uart_tx
);
	parameter CLK_FREQ = 100_000_000;
	parameter SPI_CLK_FREQ = 5_000_000;
	parameter DEBOUNCE_TIME_US = 100_000;
	parameter UART_BAUD_RATE = 115_200;

	/* verilator lint_off UNUSED*/
	wire spi_o_busy;
	/* verilator lint_on UNUSED*/
	reg spi_i_wr;
	reg [15:0] spi_i_data;
	/////////////////////////////////////////
	// debounce circuit
	/////////////////////////////////////////
	wire event_btn_sync;
	debounce #(.CLK_FREQ(CLK_FREQ), .DEBOUNCE_TIME_US(DEBOUNCE_TIME_US)) debounce_i0 (
			.i_clk(i_clk),
			.i_btn(i_btn),
			.o_btn_sync(event_btn_sync)
		);
	
	reg last_event_btn_sync;
	initial
		last_event_btn_sync = 0;
	always @(posedge i_clk)
		last_event_btn_sync <= event_btn_sync;


	wire i_event;
	assign i_event = event_btn_sync && !last_event_btn_sync;

	////////////////////////////////////////////
	// UART Reciever
	////////////////////////////////////////////
	reg [7:0] uart_rx_data [1:0];
	wire rx_stb;
	wire [7:0] rx_data;
	rxuart #(.UART_COUNTER_MAX(CLK_FREQ / UART_BAUD_RATE)) rxuart_i0 (
				.i_clk(i_clk),
				.i_uart_rx(i_uart_rx),
				.o_stb(rx_stb),
				.o_data(rx_data)
			);

	always @(posedge i_clk) begin
		if (rx_stb) begin
			uart_rx_data[0] <= rx_data;
			uart_rx_data[1] <= uart_rx_data[0];
		end
	end
	
	
	////////////////////////////
	// SPI Master
	////////////////////////////

	wire o_spi_load;
	wire o_spi_clk;
	wire o_spi_data;
	assign jd = {o_spi_data, o_spi_load, o_spi_clk};
	always @(*) begin
		spi_i_data = {uart_rx_data[1], uart_rx_data[0]};
		spi_i_wr = (rx_stb && (rx_data == ">")) || i_event;
	end
	spi #(.DATA_WIDTH(16), .CLK_DIV(CLK_FREQ / SPI_CLK_FREQ)) max_spi (
		.i_clk(i_clk),
		.i_rst(1'b0),
		.i_data(spi_i_data),
		.i_wr(spi_i_wr),
		.o_busy(spi_o_busy),
		.o_spi_load(o_spi_load),
		.o_spi_clk(o_spi_clk),
		.o_spi_data(o_spi_data)
	);



	//////////////////////////////
	// Uart Transmitter
	/////////////////////////////
	
	/* verilator lint_off UNUSED */
	wire uart_ready;
	/* verilator lint_on UNUSED */
	wire uart_i_wr;
	assign uart_i_wr = spi_i_wr;
	wire [7:0] uart_tx_data;
	//assign uart_tx_data = {spi_o_busy, 3'b111, spi_i_data[11:8]};
	
	// Used as debug output
	assign uart_tx_data = spi_i_data[15:8];

		txuart #(.UART_COUNTER_MAX(CLK_FREQ / UART_BAUD_RATE)) txuart_i0 (
				.clk(i_clk),
				.uart_tx(o_uart_tx),
				.send(uart_i_wr),
				.ready(uart_ready),
				.rst(1'b1),
				.data(uart_tx_data)
			);




	`ifdef FORMAL_SPI_UART
		always @(*) begin
			// send data back to UART only when spi is enabled
			assert(uart_i_wr == spi_i_wr);
			// send data if current rx_data is arrow
			if (rx_data == ">" && rx_stb)
				assert (uart_i_wr == 1'b1);
		end

	`endif
	
endmodule
`endif
