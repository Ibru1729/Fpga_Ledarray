// `timescale 1ns / 1ps
`default_nettype none

`ifndef MODULE_TXUART
`define MODULE_TXUART

module txuart(
    `ifdef FORMAL_TXUART
    output reg [19:0] f_counter,
    output wire [7:0] f_data_reg,
    `endif
    output wire uart_tx,
    input wire [7:0] data,
    input wire send,
    output wire ready,
    input wire clk,
    input wire rst
    );
	parameter UART_IDLE = 10;
	parameter UART_COUNTER_MAX = 217;
	// wire [15:0] UART_COUNTER_MAX = 10416;
	// wire [15:0] UART_COUNTER_MAX = 868;
	wire [15:0] uart_count_max = UART_COUNTER_MAX[15:0];
	reg [3:0] uart_state;
	reg tx_wire;
	
	reg [9:0] data_reg;
	reg [15:0] uart_counter;
	
    
    	wire bitDone;
	assign bitDone = (uart_counter >= (uart_count_max - 1));

	initial
		uart_state = UART_IDLE;
	always @(posedge clk) begin
		if(rst == 1'b0)
			uart_state <= UART_IDLE;
		else begin
			if (uart_state == UART_IDLE) begin
				if (send == 1'b1)
					uart_state <= 4'd0; // start bit
			end
			else if (uart_state < UART_IDLE) begin
				if (bitDone == 1'b1)
					uart_state <= uart_state + 1;
			end
			else
				uart_state <= UART_IDLE;
		end
	end
			     
	initial
		data_reg = 10'h3ff;
	always @(posedge clk) begin
		case (uart_state)
			UART_IDLE: begin
				if (send == 1'b1)
					data_reg <= {1'b1, data, 1'b0};
			end
		endcase
	end

	initial
		tx_wire = 1'b1;
	always @(posedge clk) begin
		if (uart_state == UART_IDLE)
			tx_wire <= 1'b1;
		else if (uart_state < UART_IDLE)
			tx_wire <= data_reg[uart_state];
		else
			tx_wire <= 1'b1;
	end
	  	
	
	initial
	       uart_counter = 0;	
	  
	always @(posedge clk) begin
		if (uart_state == UART_IDLE)
			uart_counter <= 0;
		else begin
			uart_counter <= uart_counter + 1;
			if (bitDone == 1'b1)
				uart_counter <= 0;
		end
	end
	 
	assign ready = (uart_state == UART_IDLE);
	assign uart_tx = tx_wire;

    `ifdef FORMAL_TXUART
	    // formal past validity
	    reg f_past_valid;
	    initial
		    f_past_valid = 0;
	    always @(posedge clk) begin
		    f_past_valid <= 1;
	    end

	    // formal acts differently when proving f_txuart (assume)module and
	    // helloworld wrapper (assert)
	    `ifdef FORMAL_TXUART
		    `define ASSUME assume
	    `else
		    `define ASSUME assert
	    `endif

	    // always @(posedge clk) begin
	    //         if (f_past_valid && $past(send) && $past(!ready)) begin
	    //     	    `ASSUME(send == $past(send));
	    //     	    `ASSUME(data == $past(data));
	    //         end
	    // end

	    always @(posedge clk) begin
		    assert (uart_counter < UART_COUNTER_MAX);
		    assert (uart_state <= UART_IDLE);
	    end

	    always @(posedge clk) begin
		    if (f_past_valid && ($past(uart_counter == UART_COUNTER_MAX - 1))) begin
			    assert ($past(uart_state + 1) == uart_state);
		    end
		    if (f_past_valid && ($past(uart_counter) != UART_COUNTER_MAX - 1) && (uart_state == $past(uart_state)) && ($past(uart_state) != UART_IDLE))
			    assert ($past(uart_counter + 1)  == uart_counter);
		    if (uart_state == UART_IDLE) begin
			    assert (uart_counter == 0);
		    end
	    end

	    
	    //Formal Contract
	    always @(posedge clk)
		    assume (rst);
	    reg [7:0] fv_data;
	    initial begin
		    fv_data = 8'hff;
		    f_counter = 0;
	    end
	    always @(posedge clk) begin
		    if (send && ready) begin
			    fv_data <= data;
		    end
		    if (uart_state == UART_IDLE)
			    f_counter <= 0;
		    else if ((uart_state == 4'd9) && bitDone == 1'h1)
			    f_counter <= 0;
		    else
			    f_counter <= f_counter + 1;
	    end

	    assign f_data_reg = data_reg[8:1];
	    always @(posedge clk) begin
		    assert (fv_data == data_reg[8:1]);
	    end

	    always @(posedge clk) begin
		    // if (f_past_valid && $rose(ready))
		    case (uart_state)
			    4'd10 : 	assert (f_counter == 0);
			    4'd0  : 	assert (f_counter == uart_counter);
			    4'd1  : 	assert (f_counter == UART_COUNTER_MAX + uart_counter);
			    4'd2  : 	assert (f_counter == 2 * UART_COUNTER_MAX + uart_counter);
			    4'd3  : 	assert (f_counter == 3 * UART_COUNTER_MAX + uart_counter);
			    4'd4  : 	assert (f_counter == 4 * UART_COUNTER_MAX + uart_counter);
			    4'd5  : 	assert (f_counter == 5 * UART_COUNTER_MAX + uart_counter);
			    4'd6  : 	assert (f_counter == 6 * UART_COUNTER_MAX + uart_counter);
			    4'd7  : 	assert (f_counter == 7 * UART_COUNTER_MAX + uart_counter);
			    4'd8  : 	assert (f_counter == 8 * UART_COUNTER_MAX + uart_counter);
			    4'd9  : 	assert (f_counter == 9 * UART_COUNTER_MAX + uart_counter);
		    endcase
	    end
	    always @(posedge clk) begin
		if (f_past_valid) begin
		    case ($past(uart_state))
			    4'h0 : assert (uart_tx == 1'h0);
			    4'h1 : assert (uart_tx == fv_data[0]);
			    4'h2 : assert (uart_tx == fv_data[1]);
			    4'h3 : assert (uart_tx == fv_data[2]);
			    4'h4 : assert (uart_tx == fv_data[3]);
			    4'h5 : assert (uart_tx == fv_data[4]);
			    4'h6 : assert (uart_tx == fv_data[5]);
			    4'h7 : assert (uart_tx == fv_data[6]);
			    4'h8 : assert (uart_tx == fv_data[7]);
			    4'h9 : assert (uart_tx == 1'h1);
			    4'd10 : assert (uart_tx == 1'h1);
			    default : assert (uart_tx == 1'h1);
		    endcase
	    	end
	end



    `endif
    
endmodule

`endif
