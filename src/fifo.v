`default_nettype none


module fifo #(
	parameter FIFO_WIDTH = 8,
	parameter LOG_FIFO_DEPTH = 4)
	
	(
	input wire i_clk,
	input wire i_wr,
	input wire i_rd,
	input wire [FIFO_WIDTH - 1:0] i_data,
	output wire o_full,
	output wire o_empty,
	output reg [LOG_FIFO_DEPTH:0] o_entries,
	output reg [FIFO_WIDTH - 1:0] o_data
);

	reg [LOG_FIFO_DEPTH:0] rd_addr, wr_addr;
	wire rd_req, wr_req;

	assign rd_req = i_rd && (!o_empty);
	assign wr_req = i_wr && (!o_full);

	initial
		rd_addr = 0;
	always @(posedge i_clk) begin
		if (rd_req)
			rd_addr <= rd_addr + 1;
	end

	initial
		wr_addr = 0;
	always @(posedge i_clk) begin
		if (wr_req)
			wr_addr <= wr_addr + 1;
	end

	// MEMORY SECTION
	reg [FIFO_WIDTH - 1:0] fifo_mem [(1 << LOG_FIFO_DEPTH) - 1 :0];
	always @(posedge i_clk)
		if (wr_req)
			fifo_mem[wr_addr[LOG_FIFO_DEPTH - 1:0]] <= i_data;

	always @(*)
		o_data = fifo_mem[rd_addr[LOG_FIFO_DEPTH - 1:0]];

	wire [LOG_FIFO_DEPTH:0] entries;
	assign entries = wr_addr - rd_addr;

	always @(*)
		o_entries = entries;

	assign o_full = (entries >= {1'b1, {(LOG_FIFO_DEPTH){1'b0}}});
	assign o_empty = (entries == 0);

	`ifdef FORMAL
		reg f_past_valid;
		initial
			f_past_valid = 0;
		always @(posedge i_clk)
			f_past_valid <= 1'b1;

		always @(*)
			assert (entries <= (1 << LOG_FIFO_DEPTH));

		reg [FIFO_WIDTH - 1:0] past_memdata;
		always @(posedge i_clk) begin
			past_memdata <= fifo_mem[(wr_addr[LOG_FIFO_DEPTH - 1:0])];
			if (f_past_valid && $past(o_full)) begin
				assert (past_memdata == fifo_mem[(wr_addr[LOG_FIFO_DEPTH - 1:0])]);
			end

			if (f_past_valid && $past(o_empty))
				assert($stable(rd_addr));
			
			if (f_past_valid && $past(o_full))
				assert($stable(wr_addr));
		end

		//Formal Contract
		// Write two values, read back again in order
		
		(* anyconst *) reg [LOG_FIFO_DEPTH:0] f_first_data_addr;
		reg [LOG_FIFO_DEPTH:0] f_second_data_addr;
		(* anyconst *) reg [LOG_FIFO_DEPTH-1:0] f_diff_addr;
		(* anyconst *) reg [FIFO_WIDTH - 1:0] f_first_data, f_second_data;

		// check addr is inside the fifo
		reg f_first_data_addr_inside_fifo;
		reg f_second_data_addr_inside_fifo;
		always @(*) begin
			assume (f_diff_addr > 0); // has to be neither 0 or contract test is invalid
			f_first_data_addr_inside_fifo = ((entries != 0) && ((f_first_data_addr - rd_addr) < entries));
			f_second_data_addr_inside_fifo = ((entries != 0) && ((f_second_data_addr - rd_addr) < entries));
			f_second_data_addr = f_first_data_addr + {1'b0, f_diff_addr}; // has to be less than 2 ^ LOG_FIFO_DEPTH because it is impossible to write second after first without reading first in between
		end

		reg [1:0] f_contract_state;
		reg f_finish;
		initial begin
			f_contract_state = 0;
			f_finish = 0;
		end

		always @(posedge i_clk) begin
			case (f_contract_state)
				2'h00: begin
					// first data written
					if ((wr_req == 1'b1) && (wr_addr == f_first_data_addr) && (i_data == f_first_data))
						f_contract_state <= 2'd1;
				end
				2'h01: begin
					// if first data read before the
					// second data written
					if ((rd_req == 1'b1) && (rd_addr == f_first_data_addr)) begin
						assert(o_data == f_first_data);
						f_contract_state <= 2'd0;
					end
					// second data is written
					else if ((wr_req == 1'b1) && (wr_addr == f_second_data_addr) && (i_data == f_second_data)) begin
						f_contract_state <= 2'd2;
					end
				end
				2'h02: begin
					// first data read
					if ((rd_req == 1'b1) && (rd_addr == f_first_data_addr)) begin
						assert (o_data == f_first_data);
						f_contract_state <= 2'd3;
					end
				end
				2'h03: begin
					if (!f_finish && (rd_req == 1'b1) && (rd_addr == f_second_data_addr)) begin
						assert (o_data == f_second_data);
						f_finish <= 1'b1;
					end
				end

			endcase
		end

		always @(*) begin
			case (f_contract_state)
				2'h1: begin
					assert (f_first_data_addr_inside_fifo);
					assert (fifo_mem[f_first_data_addr[LOG_FIFO_DEPTH-1:0]] == f_first_data);
				end
				2'h2 : begin
					assert (f_first_data_addr_inside_fifo);
					assert (fifo_mem[f_first_data_addr[LOG_FIFO_DEPTH-1:0]] == f_first_data);
					assert (f_second_data_addr_inside_fifo);
					assert (fifo_mem[f_second_data_addr[LOG_FIFO_DEPTH-1:0]] == f_second_data);
				end
				2'h3 : begin
					if (f_finish == 1'b0) begin
						assert (f_second_data_addr_inside_fifo);
						assert (fifo_mem[f_second_data_addr[LOG_FIFO_DEPTH-1:0]] == f_second_data);
					end
				end
			endcase
		end

		reg f_was_full;
		initial
			f_was_full = 0; 
		always @(posedge i_clk)
			if (o_full)
				f_was_full <= 1'b1;
		always @(posedge i_clk)
			cover (f_finish);
		always @(posedge i_clk)
			cover (f_past_valid && $fell(o_full));
		always @(posedge i_clk)
			cover (f_past_valid && f_was_full && $fell(o_empty));
	`endif

endmodule
