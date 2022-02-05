# Fpga_Ledarray
Design and Testbench files for Fpga to interface with MAX7219 based Led Array


src folder includes all the verilog files

led_spi_uart.sv is Top level module file.

Each files includes code to formally verify the respective modules.

sim folder includes Python cocotb testbench files to verify the top level.

Tools needed:

icarus verilog

Python-cocotb

Symbiyosys

verilator (linting purpose)
