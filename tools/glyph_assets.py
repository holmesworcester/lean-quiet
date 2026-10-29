#!/usr/bin/env python3
"""Build native glyph coverage from the pinned SVG geometry (librsvg + Cairo).

No runtime SVG parser or platform font dependency. Every integer size from
8 through 96 is rendered at its final resolution, including density scales.
"""
import ctypes as C
import hashlib
from pathlib import Path
import struct

ROOT = Path(__file__).resolve().parents[1]
SOURCES = sorted((ROOT / 'ui/glyphs').glob('*.svg'))
OUT = ROOT / 'assets/ui-glyphs.bin'


class Rectangle(C.Structure):
    _fields_ = [(n, C.c_double) for n in ['x', 'y', 'width', 'height']]


def bind(lib, name, args, result):
    f = getattr(lib, name)
    f.argtypes, f.restype = args, result
    return f


def build():
    if not SOURCES:
        raise RuntimeError('no glyph source files')
    digest = hashlib.sha256(Path(__file__).read_bytes() + b''.join(p.read_bytes() for p in SOURCES)).hexdigest()
    stamp = OUT.with_suffix('.sha256')
    if OUT.exists() and stamp.exists() and stamp.read_text() == digest:
        return
    rsvg, cairo, obj = (C.CDLL(n) for n in ['librsvg-2.so.2', 'libcairo.so.2', 'libgobject-2.0.so.0'])
    load = bind(rsvg, 'rsvg_handle_new_from_data', [C.c_char_p, C.c_size_t, C.c_void_p], C.c_void_p)
    render = bind(rsvg, 'rsvg_handle_render_document', [C.c_void_p, C.c_void_p, C.POINTER(Rectangle), C.c_void_p], C.c_int)
    unref = bind(obj, 'g_object_unref', [C.c_void_p], None)
    surface_new = bind(cairo, 'cairo_image_surface_create', [C.c_int, C.c_int, C.c_int], C.c_void_p)
    surface_drop = bind(cairo, 'cairo_surface_destroy', [C.c_void_p], None)
    flush = bind(cairo, 'cairo_surface_flush', [C.c_void_p], None)
    stride = bind(cairo, 'cairo_image_surface_get_stride', [C.c_void_p], C.c_int)
    data = bind(cairo, 'cairo_image_surface_get_data', [C.c_void_p], C.c_void_p)
    context_new = bind(cairo, 'cairo_create', [C.c_void_p], C.c_void_p)
    context_drop = bind(cairo, 'cairo_destroy', [C.c_void_p], None)
    out = bytearray(b'QICO' + struct.pack('<I', len(SOURCES) * 89))
    for path in SOURCES:
        raw = path.read_bytes().replace(b'currentColor', b'#ffffff')
        handle = load(raw, len(raw), None)
        if not handle:
            raise RuntimeError(f'invalid SVG: {path}')
        try:
            for size in range(8, 97):
                surface = surface_new(0, size, size)  # CAIRO_FORMAT_ARGB32
                context = context_new(surface)
                try:
                    if not render(handle, context, C.byref(Rectangle(0, 0, size, size)), None):
                        raise RuntimeError(f'could not render {path} at {size}')
                    flush(surface)
                    pixels = C.string_at(data(surface), stride(surface) * size)
                    alpha = bytes(pixels[y * stride(surface) + x * 4 + 3]
                                  for y in range(size) for x in range(size))
                    if not any(alpha):
                        raise RuntimeError(f'empty glyph {path}')
                    name = path.stem.encode()
                    out += bytes([len(name)]) + name + bytes([size]) + alpha
                finally:
                    context_drop(context)
                    surface_drop(surface)
        finally:
            unref(handle)
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_bytes(out)
    stamp.write_text(digest)
    print(f'glyphs: {len(SOURCES)} source paths, {len(out)} bytes of coverage')


if __name__ == '__main__':
    build()
