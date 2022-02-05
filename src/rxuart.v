`default_nettype none

`ifndef MODULE_RXUART
`define MODULE_RXUART


`ifdef FORMAL_RXUART
`define FORMAL_TXUART
`include "txuart.v"
`endif

module rxuart (
	input wire i_clk,
	input wire i_uart_rx,
	output reg o_stb,
	output reg [7:0] o_data
);
	parameter UART_COUNTER_MAX = 217;
	
	reg [3:0] rxuart_state;

	reg uart_rx_sync1, uart_rx;
	initial 
		{uart_rx_sync1, uart_rx} = 2'b11;
	always @(posedge i_clk)
		{uart_rx_sync1, uart_rx} <= {i_uart_rx, uart_rx_sync1};

	wire baud_stb;
	initial
		rxuart_state = 0;
	always @(posedge i_clk) begin
		if (rxuart_state == 4'b0) begin
			if (!uart_rx)
				rxuart_state <= 4'b1;
		end
		else if (rxuart_state < 4'd9) begin
			if (baud_stb == 1'b1)
				rxuart_state <= rxuart_state + 1;
		end
		else if (rxuart_state == 4'd9) begin
			if (baud_stb == 1'b1)
				rxuart_state <= 4'd0;
		end
		else
			rxuart_state <= 4'h0;
	end

	/*verilator lint_off WIDTH */
	reg [15:0] baud_counter;

	assign baud_stb = (baud_counter == 0);
	initial
		baud_counter = 0;

	always @(posedge i_clk) begin
		if (rxuart_state == 0) begin // idle state
			baud_counter <= 0;
			if (!uart_rx)
				baud_counter <= UART_COUNTER_MAX + UART_COUNTER_MAX / 2 - 1;
		end
		else if (rxuart_state < 4'd9) begin
			baud_counter <= baud_counter - 1;
			if (baud_stb == 1'b1)
				baud_counter <= UART_COUNTER_MAX - 1;
		end
		else if (rxuart_state == 4'd9) begin
			baud_counter <= baud_counter - 1;
			if (baud_stb == 1'b1)
				baud_counter <= 0;
		end
		else
			baud_counter <= 0;
	end

	always @(posedge i_clk) begin
		if ((rxuart_state > 4'h0) && (rxuart_state < 4'd9)) 
			if (baud_stb)
				o_data <= {uart_rx, o_data[7:1]};
	end

	// basically o_stb is when rxuart_state is 4'd9 (stop bit)
	initial
		o_stb = 0;
	always @(posedge i_clk) begin
		o_stb <= baud_stb && (rxuart_state == 4'd9);
	end
		
	`ifdef FORMAL_RXUART
	
		always @(*) begin
			assert (rxuart_state <= 4'd9);
			if (rxuart_state == 0)
				assert (baud_counter == 0);
		end
		// 
		always @(posedge i_clk) begin
			if (rxuart_state == 4'd0)
				assert (baud_counter == 0);
			else if (rxuart_state == 4'd1)
				assert (baud_counter < UART_COUNTER_MAX + UART_COUNTER_MAX / 2);
			else if (rxuart_state <= 4'd9)
				assert (baud_counter < UART_COUNTER_MAX);
		end

		// Assume a transmitter	

		(* anyseq *) reg f_tx_wr;
		(* anyseq *) reg [7:0] f_tx_idata;
		wire f_tx_uart, f_tx_not_busy;
		wire [19:0] f_tx_counter;
		wire [7:0] f_tx_data;
	
		txuart #(.UART_COUNTER_MAX(UART_COUNTER_MAX)) txuart_i0 (
				.clk(i_clk),
				.send(f_tx_wr),
				.data(f_tx_idata),
				.ready(f_tx_not_busy),
				.f_counter(f_tx_counter),
				.f_data_reg(f_tx_data),
				.uart_tx(f_tx_uart),
				.rst(1'b1)
			);

		always @(*)
			assume (i_uart_rx == f_tx_uart);
	
		
		always @(posedge i_clk) begin
			case (rxuart_state)
				4'h2 : assert (f_tx_data[0] == o_data[7]);
				4'h3 : assert (f_tx_data[1:0] == o_data[7:6]);
				4'h4 : assert (f_tx_data[2:0] == o_data[7:5]);
				4'h5 : assert (f_tx_data[3:0] == o_data[7:4]);
				4'h6 : assert (f_tx_data[4:0] == o_data[7:3]);
				4'h7 : assert (f_tx_data[5:0] == o_data[7:2]);
				4'h8 : assert (f_tx_data[6:0] == o_data[7:1]);
				4'h9 : assert (f_tx_data[7:0] == o_data[7:0]);
			endcase
			if (o_stb)
				assert (f_tx_data == o_data);
		end
		
		always @(posedge i_clk) begin
			case (rxuart_state)
				4'h0 : if (f_tx_uart)
						assert ((f_tx_counter == baud_counter) || ((f_tx_counter < 10 * UART_COUNTER_MAX) && (f_tx_counter > (9 * UART_COUNTER_MAX + 2 + UART_COUNTER_MAX / 2))));
					else begin
						assert (baud_counter == 0);
						assert (f_tx_counter < 4); // 1 cycle delay (in 4'd1 state) + 2 cycle delay in sync
					end
				4'h1 : assert (f_tx_counter == 1 * UART_COUNTER_MAX - baud_counter + 1 + 2 + UART_COUNTER_MAX / 2);
				4'h2 : assert (f_tx_counter == 2 * UART_COUNTER_MAX - baud_counter + 1 + 2 + UART_COUNTER_MAX / 2);
				4'h3 : assert (f_tx_counter == 3 * UART_COUNTER_MAX - baud_counter + 1 + 2 + UART_COUNTER_MAX / 2);
				4'h4 : assert (f_tx_counter == 4 * UART_COUNTER_MAX - baud_counter + 1 + 2 + UART_COUNTER_MAX / 2);
				4'h5 : assert (f_tx_counter == 5 * UART_COUNTER_MAX - baud_counter + 1 + 2 + UART_COUNTER_MAX / 2);
				4'h6 : assert (f_tx_counter == 6 * UART_COUNTER_MAX - baud_counter + 1 + 2 + UART_COUNTER_MAX / 2);
				4'h7 : assert (f_tx_counter == 7 * UART_COUNTER_MAX - baud_counter + 1 + 2 + UART_COUNTER_MAX / 2);
				4'h8 : assert (f_tx_counter == 8 * UART_COUNTER_MAX - baud_counter + 1 + 2 + UART_COUNTER_MAX / 2);
				4'h9 : assert (f_tx_counter == 9 * UART_COUNTER_MAX - baud_counter + 1 + 2 + UART_COUNTER_MAX / 2);
			endcase
		end


		reg f_first_hit;
		initial
			f_first_hit = 0;
		always @(posedge i_clk) begin
			if (o_stb)
				f_first_hit <= 1;
			cover (f_first_hit && o_stb);
		end



	`endif


endmodule

`endif
