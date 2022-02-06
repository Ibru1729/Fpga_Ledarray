#!/usr/bin/env python
import asyncio

async def run_late(delay):
    await asyncio.sleep(delay)
    print("yay")

#asyncio.run(run_late(3))
run_late(4)
