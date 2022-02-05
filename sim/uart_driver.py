import numpy as np

class uart_tx:
    baud_counter = 9600;
    clk_counter = 0;
    bit_counter = 0;
    UART_TX_STATE = 0;
    data_reg = np.full(10, True);
    sw_tx = 1;
    def __init__(self, baud_counter):
        self.baud_counter = baud_counter;
        self.UART_TX_STATE = 0;
        self.clk_counter = 0;
        self.sw_tx = 1;
    def process(self, send, data):
        if (self.UART_TX_STATE == 0):
            self.sw_tx = 1
            if (send == 1):
                self.UART_TX_STATE = 1;
                self.clk_counter = self.baud_counter - 1
                self.bit_counter = 0
                for i in range(8):
                    self.data_reg[8 - i] = np.unpackbits(np.array([data], dtype=np.uint8))[i]
                self.data_reg[9] = 1;
                self.data_reg[0] = 0;
        else:
            self.sw_tx = self.data_reg[self.bit_counter]
            if (self.clk_counter == 0):
                self.bit_counter = self.bit_counter + 1
                if (self.bit_counter >= 10):
                    self.UART_TX_STATE = 0;
                    self.bit_counter = 0; 
                    self.status();
                elif (self.bit_counter == 9):
                    self.clk_counter = self.baud_counter // 2 -1
                else:
                    self.clk_counter = self.baud_counter - 1;
            else:
                self.clk_counter = self.clk_counter - 1;
            
        return self.sw_tx
    
    def status(self):
        print ("To UART_RX --- Transmitted : ", self.data_reg[8:0:-1] * 1);






class uart_rx:
    baud_counter = 9600;
    clk_counter = 0;
    bit_counter = 0;
    UART_RX_STATE = 0;
    data_reg = np.full(8, False);
    def __init__(self, baud_counter):
        self.baud_counter = baud_counter;
        self.UART_RX_STATE = 0;
        self.clk_counter = 0;
    def process(self, sw_rx):
        if (self.UART_RX_STATE == 0):
            if (sw_rx == 0):
                self.UART_RX_STATE = 1;
                self.clk_counter = self.baud_counter + (self.baud_counter // 2) - 1
                self.bit_counter = 0
        else:
            if (self.clk_counter == 0):
                self.clk_counter = self.baud_counter - 1;
                if (self.bit_counter >= 8):
                    self.UART_RX_STATE = 0;
                    self.bit_counter = 0; 
                    self.clk_counter = 0;
                    self.status();
                else:
                    self.data_reg[self.bit_counter] = sw_rx
                    self.bit_counter = self.bit_counter + 1
                    
            else:
                self.clk_counter = self.clk_counter - 1;
    
    def status(self):
        print ("from UART_TX --- Recieved : ", self.data_reg[::-1] * 1);




class uart_driver:
    def __init__(self, baud_counter):
        self.uart_rx1 = uart_rx(baud_counter);
        self.uart_tx1 = uart_tx(baud_counter);

    def rx_tx(self, sw_rx, send, data):
        self.uart_rx1.process(sw_rx);
        return self.uart_tx1.process(send, data);

