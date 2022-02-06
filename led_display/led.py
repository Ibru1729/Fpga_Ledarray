#!/usr/bin/env python
import pyglet
import asyncio
from pyglet import shapes

sizex = 900
sizey = 900
window = pyglet.window.Window(sizex,sizey)

def transform_axes(x,y):
    return x,sizey-y

batch = pyglet.graphics.Batch()
circles = []
radius = 60.0
columns = 3
rows = 3
color = (255,255,255)
for i in range(rows):
    circle_row = []
    y = (2*i+1)*radius
    for j in range(columns):
        x = (2*j+1)* radius
        pyglet_x,pyglet_y = transform_axes(x,y)
        circle_row.append(shapes.Circle(pyglet_x,pyglet_y,radius,color=color,batch=batch))

    circles.append(circle_row)

label = pyglet.text.Label('Hello World',
        font_name='Times New Roman',
        font_size=36,
        x=window.width//2, y=window.height//2,
        anchor_x='center', anchor_y='center')
@window.event
def on_key_press(symbol,modifiers):
    if symbol == pyglet.window.key.R:
        circles[1][1].color = (255,0,0)
    if symbol == pyglet.window.key.G:
        circles[1][1].color = (0,255,0)
    if symbol == pyglet.window.key.B:
        circles[1][1].color = (0,0,255)

@window.event
def on_mouse_press(x,y,button,modifiers):
    if button == pyglet.window.mouse.LEFT:
        print(f'The left mouse button was pressed at ({x},{y})')
@window.event
def on_draw():
    window.clear()
    batch.draw()
    #label.draw()

async def run_late(delay):
    await asyncio.sleep(delay)
    circles[1][1].color = (255,0,0)

asyncio.run(run_late(10))
#run_late(10)
#pyglet.app.run()
