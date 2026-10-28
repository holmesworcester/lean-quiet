#!/usr/bin/env python3
"""Walks the emulator's virtual-scene camera (gRPC EmulatorController) to
the wall poster, which hangs where the scene's kitchen print is: about
(-0.8, 0.3, 5.3) in Toren1BD (emulator/resources/Toren1BD.posters), facing
-z turned by -150 degrees. The camera starts near the origin facing -z
(the television), with the poster behind a wall; rotations and velocities
are in the camera's own frame (+y rotation turns left, -z is forward).

The path: turn 142.6 degrees, walk 3.6 m to beside the dining table, turn
to face the poster, step back 1.5 m, then left and up: the poster fills
most of the frame, the dining table and a chair in front of its lower
corner (Lean corrects what they hide).

usage: scene.py GRPC_PORT STUBS_DIR
STUBS_DIR holds emulator_controller_pb2*.py (made by e2e.sh with grpc_tools).
"""
import sys
import time

sys.path.insert(0, sys.argv[2])
import grpc  # noqa: E402
import emulator_controller_pb2 as pb  # noqa: E402
import emulator_controller_pb2_grpc as rpc  # noqa: E402

stub = rpc.EmulatorControllerStub(grpc.insecure_channel(f'localhost:{sys.argv[1]}'))


def turn(rad):
    stub.rotateVirtualSceneCamera(pb.RotationRadian(x=0, y=rad, z=0))
    time.sleep(1)


def move(x, y, z, seconds):
    stub.setVirtualSceneCameraVelocity(pb.Velocity(x=x, y=y, z=z))
    time.sleep(seconds)
    stub.setVirtualSceneCameraVelocity(pb.Velocity(x=0, y=0, z=0))
    time.sleep(0.5)


turn(2.489)
move(0, 0, -0.5, 7.24)
turn(1.176)
move(0, 0, 0.5, 3.0)
move(-0.3, 0.3, 0, 1.0)
move(0, 0.3, 0, 1.0)
print('camera at the poster')
