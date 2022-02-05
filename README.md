# Fpga_Ledarray
Design and Testbench files for Fpga to interface with MAX7219 based Led Array


src folder includes all the verilog files
led_spi_uart.sv is Top level module file.
Each file include formal verification script to verify respective modules inside the file.

sim folder includes Python cocotb testbench files to verify the top level.

Tools needed:
icarus verilog
Python-cocotb
Symbiyosys
verilator (linting purpose)
