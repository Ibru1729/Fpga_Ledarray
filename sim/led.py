#!/usr/bin/env python
import pyglet
from pyglet import shapes
from led import LEDEvent

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
debug_circle_x, debug_circle_y = transform_axes((2*columns + 1)*radius,(2*rows + 1)*radius) 
debug_circle = shapes.Circle(debug_circle_x,debug_circle_y,radius,color=color,batch=batch)
for i in range(rows):
    circle_row = []
    y = (2*i+1)*radius
    for j in range(columns):
        x = (2*j+1)* radius
        pyglet_x,pyglet_y = transform_axes(x,y)
        circle_row.append(shapes.Circle(pyglet_x,pyglet_y,radius,color=color,batch=batch))

    circles.append(circle_row)

@window.event
def on_key_press(symbol,modifiers):
    if symbol == pyglet.window.key.R:
        debug_circle.color = (255,0,0)
    if symbol == pyglet.window.key.G:
        debug_circle.color = (0,255,0)
    if symbol == pyglet.window.key.B:
        debug_circle.color = (0,0,255)
@window.event
def on_draw():
    window.clear()
    batch.draw()
    #label.draw()


class LEDDisplay:
    def __init__(self
led_event_inst = LEDEvent()
@led_event_inst.event('state_update')
def update_led(state):
    for i in range(rows):
        for j in range(columns):
            if state[i][j] == True:
                circles[i][j].color = (0,255,0)
            else:
                circles[i][j].color = (255,255,255)


pyglet.app.run()
