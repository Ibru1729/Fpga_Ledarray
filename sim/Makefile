#file: Makefile
CWD=$(shell pwd)

TOPLEVEL_LANG ?=verilog
SIM ?= icarus

#Paths to HDL source files
ifeq ($(TOPLEVEL_LANG),verilog)
  VERILOG_SOURCES +=$(CWD)/../src/spi.v
  VERILOG_SOURCES +=$(CWD)/../src/debounce.v
  VERILOG_SOURCES +=$(CWD)/../src/txuart.v
  VERILOG_SOURCES +=$(CWD)/../src/rxuart.v
  VERILOG_SOURCES +=$(CWD)/../src/led_spi_uart.sv
  VERILOG_SOURCES +=$(CWD)/led_spi_uart_tb.v
else
  $(error "A valid value (verilog) was not provided for TOPLEVEL_LANG=$(TOPLEVEL_LANG)")
endif

DUT      = led_spi_uart_tb         #module under test
TOPLEVEL = $(DUT)             #top module
MODULE := led_spi_uart_test   #python testbench file

CUSTOM_SIM_DEPS=$(CWD)/Makefile

ifeq ($(SIM),questa)
    SIM_ARGS=-t 1ps
endif



include $(shell cocotb-config --makefiles)/Makefile.sim

