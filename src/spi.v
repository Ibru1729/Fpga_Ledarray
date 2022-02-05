// This module produces works on simple wishbone protocol
// This module gives the output apropriate to max7219/7221
// outer modules can use FORMAL_SPI_INPUT macro to check the stability of the input in event of busy


`default_nettype none

`ifndef MODULE_SPI
`define MODULE_SPI

module spi #(
	parameter DATA_WIDTH = 16,
	/* verilator lint_off WIDTH */
	parameter [19:0] CLK_DIV = 10
	/* verilator lint_on WIDTH */
	)(
	input wire i_clk,
	input wire i_rst,
	input wire [DATA_WIDTH-1:0] i_data,
	input wire i_wr,
	output reg o_busy,
	output wire o_spi_clk,
	output wire o_spi_data,
	output wire o_spi_load
);
	
	localparam DELAY = 5; // to keep o_spi_load high

	reg [DATA_WIDTH - 1:0] data_reg;
	reg [5:0] bit_count = DATA_WIDTH;
	reg tx_status = 1;

	wire wr_req = i_wr && !o_busy;
	wire spi_clk_negedge;
	// tx_status zero indicates active (feed to spi_load)

	// bit_count = DATA_WIDTH is idle state
	// to track nos of bits transmitted
	initial begin
		bit_count = DATA_WIDTH;
		o_busy = 1;
	end
	always @(posedge i_clk) begin
		if (i_rst) begin // reset
			bit_count <= DATA_WIDTH;
			tx_status <= 1;
			o_busy <= 1;
		end
		else if (bit_count >= DATA_WIDTH + DELAY) begin // idle stage
			tx_status <= 1;
			o_busy <= 0;
			bit_count <= DATA_WIDTH + DELAY;
			if (wr_req) begin
				bit_count <= 0;
				tx_status <= 0;
				o_busy <= 1;
			end
		end
		else if (bit_count >= DATA_WIDTH) begin // delay stages
			tx_status <= 1;
			o_busy <= 1;
			bit_count <= bit_count + 1;
		end
		else if (spi_clk_negedge) begin
			tx_status <= 0;	
			bit_count <= bit_count + 1;
		end
	end

	// loading and changing data in data_reg
	initial
		data_reg = 0;
	always @(posedge i_clk) begin
		if (wr_req == 1'b1)
			data_reg <= i_data;
		else if (spi_clk_negedge)
			data_reg <= {data_reg[DATA_WIDTH - 2:0], 1'b0};
	end


	// spi clock generation with default value as 1 when not transmitting
	reg div_clk = 0;
	reg [19:0] clk_counter;
	always @(posedge i_clk) begin
		if (tx_status == 1 || i_rst)
			div_clk <= 0;
		else if (clk_counter >= CLK_DIV / 2 - 1)
			div_clk <= ~div_clk;
	end

	initial
		clk_counter = 0;
	always @(posedge i_clk) begin
		if ((clk_counter >= CLK_DIV/2 - 1) || (tx_status == 1'b1))
			clk_counter <= 0;
		else
			clk_counter <= clk_counter + 1;
	end

	assign spi_clk_negedge = div_clk && (clk_counter >= CLK_DIV/2 - 1) && !tx_status;

	assign o_spi_clk = div_clk;
	assign o_spi_data = data_reg[DATA_WIDTH - 1];
	assign o_spi_load = tx_status;
	
	`ifdef FORMAL
		reg f_past_valid;
		initial begin
			f_past_valid = 0;
		end
		always @(posedge i_clk) begin
			f_past_valid <= 1;
			assume (i_data == 16'hf00f);
		end

	    `ifdef FORMAL_SPI_INPUT
	    // checks if input to spi is maintained if busy is high
	    always @(posedge i_clk) begin
	            if (f_past_valid && $past(i_wr) && $past(o_busy)) begin
	        	    assert(i_wr == $past(i_wr));
	        	    assert(i_data == $past(i_data));
	            end
	    end
	    `endif


		`ifdef FORMAL_SPI
		// clock divider properties
		reg [2:0] f_once_toggled = 0;
		always @(posedge i_clk) begin
			// effect of clk_counter only works when i_rst is not
			// active
			if (f_past_valid && ($rose(div_clk) || $fell(div_clk))) begin
				assert ($past(i_rst || tx_status || (clk_counter >= CLK_DIV / 2 - 1)));
			end

			assert (clk_counter <= CLK_DIV/2 - 1);
		end

		// spi  state properties
		always @(*) begin
			// state range
			assert (bit_count <= DATA_WIDTH + DELAY);

			// tx_status active states
			if (!tx_status)
				assert (bit_count <= DATA_WIDTH);

			// non busy states
			if (o_busy == 0)
				assert (bit_count >= DATA_WIDTH + DELAY);
		end

		// FORMAL CONTRACT
		reg [DATA_WIDTH-1:0] f_data = 0;
		always @(posedge i_clk) begin
			if (wr_req)
				f_data <= i_data;
		end

		always @(*) begin
			if (bit_count == 0)
				assert (f_data == data_reg);
			if (bit_count < DATA_WIDTH) begin
				assert (o_spi_data == f_data[DATA_WIDTH - 1 - bit_count]);
			end
			for (int i = 0; i < DATA_WIDTH ; i++) begin
				if (i >= {26'b0, bit_count})
					assert (data_reg[i] == f_data[i - {26'b0, bit_count}]);
			end
		end

		always @(posedge i_clk) begin
			if ($fell(tx_status))
				f_once_toggled <= {f_once_toggled[1:0], 1'b1};
			cover (f_once_toggled == 3'b111);
		end

		`endif
	`endif

endmodule
`endif
