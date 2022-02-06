import numpy as np
import cocotb
import pyglet
from pyglet import shapes
from pyglet.event import EventDispatcher

class LEDEvent(EventDispatcher):
    def update_state(self,state):
        self.dispatch_event('state_update',state)

LEDEvent.register_event_type('state_update')

sizex = 900
sizey = 900
window = pyglet.window.Window(sizex,sizey)

def transform_axes(x,y):
    return x,sizey-y

batch = pyglet.graphics.Batch()
circles = []
radius = 10.0
columns = 8
rows = 8
color = (255,255,255)
for i in range(rows):
    circle_row = []
    y = (2*i+1)*radius
    for j in range(columns):
        x = (2*j+1)* radius
        pyglet_x,pyglet_y = transform_axes(x,y)
        circle_row.append(shapes.Circle(pyglet_x,pyglet_y,radius,color=color,batch=batch))

    circles.append(circle_row)

@window.event
def on_draw():
    window.clear()
    batch.draw()

led_event_inst = LEDEvent()
@led_event_inst.event('state_update')
def update_led(state):
    for i in range(rows):
        for j in range(columns):
            if state[i][j] == True:
                circles[i][j].color = (0,255,0)
            else:
                circles[i][j].color = (255,255,255)


#####################################################################
class max7219_state:
    shift_reg = np.full(16, False);
    addr_reg = np.full(4, False);
    data_reg = np.full(8, False);
    data_ram = np.empty(shape=(8,8));
    clk = False
    load = True
    din = False

    def __init__(self):
        self.data_ram.fill(False)
        return
    def update_led_display(self):
        pyglet.clock.tick()

        for window in pyglet.app.windows:
            window.switch_to()
            window.dispatch_events()
            window.dispatch_event('on_draw')
            window.flip()
    
    def process(self, load, clk, din):
        clk_posedge = (not self.clk) and clk
        load_posedge = (not self.load) and load
        if (load_posedge):
            for i in range(8, 12):
                self.addr_reg[i-8] = self.shift_reg[i]
            addr = self.addr_reg.dot(1 << np.arange(self.addr_reg.size))
            for j in range(0, 8):
                self.data_reg[j] = self.shift_reg[j]
            data = self.data_reg.dot(1 << np.arange(self.data_reg.size))
            #print (addr, self.addr_reg)
            if ((addr < 9) and (addr > 0)):
                print ("SPI -- Digit :", addr, " :-  Data: ", self.data_reg[::-1]*1);
                self.data_ram[addr - 1] = self.data_reg
                led_event_inst.update_state(self.data_ram)
                print("LED display function about to be called")
                self.update_led_display()
                print("LED display function called")

            elif (addr == 9):
                print ("SPI -- Decode mode :-", "Data: ", self.data_reg[::-1]*1)
            elif (addr == 10):
                print ("SPI -- Intensity :-", "Data: ", self.data_reg[::-1]*1)
            elif (addr == 11):
                print ("SPI -- Scan limit :-", "Data: ", self.data_reg[::-1]*1)
            elif (addr == 12):
                print ("SPI -- Shutdown :-", "Data: ", self.data_reg[::-1]*1)
            elif (addr == 15):
                print ("SPI -- Display test :- ", "Data: ", self.data_reg[::-1]*1)
            elif (addr == 0):
                print ("SPI -- NOP")
            # self.status()

        if (clk_posedge):
            for i in range(15, 0, -1):
                self.shift_reg[i] = self.shift_reg[i-1]
            self.shift_reg[0] = din
        self.clk = clk
        self.load = load
        self.din = din

    def status(self):
        print (self.shift_reg[::-1] * 1, self.addr_reg[::-1] * 1, self.data_ram[::-1] * 1)


class max7219_timing:
    # min values
    T_CP = 100; # clock period
    T_CH = 50; # clock pulse width high
    T_CL = 50; # clock pulse width low
    T_CSS = 25; # time between load fall and clk rise
    T_CSH = 0; # time between clk rise to load rise
    T_DS = 25; # setup time for DIN
    T_DH = 0; # hold time for DIN
    T_DO = 25;
    T_LDCLK = 50; # time between load rising to clk rising
    T_CSW = 50; # minimum load pulse width
    time_per_call = 10;
    clk_last_posedge = 0;
    clk_last_negedge = 0;
    load_last_posedge = 0;
    load_last_negedge = 0;
    din_last_change = 0;
    clk = False
    load = True
    def __init__(self, time_per_call):
        self.time_per_call = time_per_call;
    def time_increment(self):
        self.clk_last_posedge += self.time_per_call;
        self.clk_last_negedge += self.time_per_call;
        self.load_last_posedge += self.time_per_call;
        self.load_last_negedge += self.time_per_call;
        self.din_last_change += self.time_per_call;

    def time_update(self, max_state, load, clk, din):
        if (din != max_state.din):
            self.din_last_change = 0;
        if (clk != max_state.clk):
            if (clk):
                self.clk_last_posedge = 0
            else:
                self.clk_last_negedge = 0
        if (load != max_state.load):
            if (not load):
                self.load_last_negedge = 0
            else:
                self.load_last_posedge = 0


    async def check_timing(self, max_state, load, clk, din):
        self.time_increment()
        if (clk and (not max_state.clk)):
            assert (self.clk_last_posedge >= self.T_CP), "Error: SPI CLK TIME PERIOD is less than 100 ns"
            assert (self.clk_last_negedge >= self.T_CL), "Error: SPI T_CL violation"
            assert (self.load_last_negedge >= self.T_CSS), "SPI T_CSS violation"
            assert (self.load_last_posedge >= self.T_LDCLK), "SPI T_LDCLK violation"
            assert (self.din_last_change >= self.T_DS), "SPI T_DS violation"

        if ((not load) and (max_state.load)):
            assert (self.load_last_posedge > self.T_CSW), "SPI T_CSW violation"

        self.time_update(max_state, load, clk, din)
        return


class max7219_driver:

    def __init__(self, time):
        self.max_timer = max7219_timing(time);
        self.max_state = max7219_state();

    def rx (self, load, clk, din):
        cocotb.start_soon(self.max_timer.check_timing(self.max_state, load, clk, din))
        self.max_state.process(load, clk, din);

    def status (self):
        self.max_state.status();
