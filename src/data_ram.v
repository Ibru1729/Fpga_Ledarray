`default_nettype none

`ifndef MODULE_DATA_RAM
`define MODULE_DATA_RAM

module data_ram #(
	parameter MEMFILE_NAME = "memfile.hex",
	parameter DATA_WIDTH = 32,
	parameter ADDR_WIDTH = 6
	)(
	input wire i_clk,
	input wire i_mem_en,
	input wire i_mem_wr_en,
	input wire [ADDR_WIDTH - 1:0] i_mem_addr,
	input wire [DATA_WIDTH - 1:0] i_mem_data,
	output reg [DATA_WIDTH - 1:0] o_mem_data
);
	
	reg [DATA_WIDTH - 1:0] mem [0:1<<ADDR_WIDTH-1];

	initial
		$readmemh(MEMFILE_NAME, mem);

	always @(posedge i_clk)
		if (i_mem_en)
			o_mem_data <= mem[i_mem_addr];

	always @(posedge i_clk)
		if (i_mem_en && i_mem_wr_en)
			mem[i_mem_addr] <= i_mem_data;

	`ifdef FORMAL_DATA_RAM
	
	`ifdef FORMAL_DATA_RAM_INPUT
		`define ASSUME assert
	`else
		`define ASSUME assume
	`endif
	reg f_past_valid;
	initial
		f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid <= 1;
	always @(posedge i_clk) begin
		if (f_past_valid) begin
			for (int i = 0; (i < 1<<ADDR_WIDTH) ; i++) begin
				if (i != $past(i_mem_addr))
					`ASSUME ($stable(mem[i]));
				else begin
					if ($past(i_mem_wr_en && i_mem_en))
						`ASSUME (mem[i] == $past(i_mem_data));
					else
						`ASSUME ($stable(mem[i]));
				end
			end

		end
	end
	`endif

endmodule

`endif
