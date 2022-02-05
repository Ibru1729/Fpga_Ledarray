`default_nettype none

`ifndef MODULE_DEBOUNCE
`define MODULE_DEBOUNCE

module debounce (
	input wire i_clk,
	input wire i_btn,
	output reg o_btn_sync
);
	
	parameter CLK_FREQ = 100_000_000;
	parameter DEBOUNCE_TIME_US = 100_000; // in debounce us

	parameter DEBOUNCE_CYCLES = (CLK_FREQ / 1_000_000) * DEBOUNCE_TIME_US;

	reg button_sync_stage1, button_state, last_button_state;
	// 2ff synchronizer
	initial begin
		button_sync_stage1 = 0;
		button_state = 0;
		last_button_state = 0;
	end
	always @(posedge i_clk) begin
		{button_state , button_sync_stage1} <= {button_sync_stage1, i_btn};
		last_button_state <= button_state;
	end

	reg [28:0] debounce_counter;
	initial
		debounce_counter = 0;
	// debouncer
	always @(posedge i_clk) begin
		if (last_button_state != button_state)
			/* verilator lint_off WIDTH */
			debounce_counter <= DEBOUNCE_CYCLES - 1;
			/* verilator lint_on WIDTH */
		else if (debounce_counter != 0)
			debounce_counter <= debounce_counter - 1;
	end

	initial
		o_btn_sync = 0;
	always @(posedge i_clk) begin
		if (debounce_counter == 0)
			o_btn_sync <= last_button_state;
	end


	`ifdef FORMAL
		
		reg f_past_valid;
		initial
			f_past_valid = 0;
		always @(posedge i_clk) begin
			f_past_valid = 1;
		end

		always @(posedge i_clk)
			if (f_past_valid && ($past(last_button_state != button_state))) begin
				assert (debounce_counter == DEBOUNCE_CYCLES - 1);
			end

		always @(posedge i_clk)
			if (f_past_valid && ($past(debounce_counter == 0)))
				assert ($past(last_button_state) == o_btn_sync);

	
	`endif
		


endmodule
`endif
