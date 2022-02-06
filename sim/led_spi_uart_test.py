# to import refernce check
import max7219_driver as spi
import uart_driver as uart

# necessary for cocotb routine
import cocotb
import random
from cocotb.triggers import Timer, FallingEdge
from cocotb.clock import Clock

# clock period
clock_period = 10
baud_counter = 868;
max_driver = spi.max7219_driver(clock_period); # calling after each clock edge
uart_driver1 = uart.uart_driver(baud_counter);

uart_tx_send = 1
uart_tx_data_array = [0x0b, 0x07, ord(">"), 0x09, 0x00, ord(">"), 0x0c, 0x01, ord(">"), 0x0c, 0x01, ord(">"), 0x01, 0x00, ord(">"), 0x02, 0x76, ord(">"), 0x03, 0x89, ord(">"), 0x04, 0x89, ord(">"), 0x05, 0x89, ord(">"), 0x06, 0x89, ord(">"), 0x07, 0x76, ord(">"), 0x08, 0x00, ord(">"), 0xff, 0x01, ord(">"), 0x10, 0xdd, ord(">")];
uart_tx_data = 0;

hw_debug_output = []


################################################################################

async def update_maxdriver_input(dut, SimEvent_End):
    while (not SimEvent_End.is_set()):
        await FallingEdge(dut.i_clk)
        max_driver.rx(bool(dut.o_spi_load.value), bool(dut.o_spi_clk.value), bool(dut.o_spi_data.value))

async def update_uartdriver_input(dut, SimEvent_Data, SimEvent_End):
    while (not SimEvent_End.is_set()):
        await FallingEdge(dut.i_clk)
        dut.i_uart_rx.value = int(uart_driver1.rx_tx(bool(dut.o_uart_tx.value), SimEvent_Data.is_set(), SimEvent_Data.data));
        if (SimEvent_Data.is_set()):
            SimEvent_Data.clear()

async def reset_dut(dut):
    await FallingEdge(dut.i_clk)
    dut.i_btn.value = 0;
    await Timer(5 * clock_period, units="ns")
    dut.i_btn.value = 1;
    await Timer(1000 * clock_period, units="ns")
    dut.i_btn.value = 0;
    
async def send_test_data(dut, SimEvent_Data, SimEvent_End):
    for i in range(len(uart_tx_data_array)):
        SimEvent_Data.set(data = uart_tx_data_array[i]);
        await Timer(random.randint(9000 * clock_period, 9500 * clock_period), 'ns');
    SimEvent_End.set();


@cocotb.test()
async def spi_test_batman(dut):
    SimEvent_End = cocotb.triggers.Event()
    SimEvent_Data = cocotb.triggers.Event()
    #start clock generator for infinite cycles
    await cocotb.start(Clock(dut.i_clk,period=clock_period,units='ns').start(start_high=False))
    #asynchronously start input data feeding function
    cocotb.start_soon(update_maxdriver_input(dut ,SimEvent_End))
    cocotb.start_soon(update_uartdriver_input(dut,SimEvent_Data, SimEvent_End))
    await reset_dut(dut)
    await send_test_data(dut,SimEvent_Data, SimEvent_End) 
