"""Actual M4RI rank backend; no third-party binary or source is bundled.

The caller supplies a compiled wrapper library from benchmarks/m4ri/build.py.
This adapter is a benchmark component, not a complete Sage installation.
"""
from __future__ import annotations
import ctypes
from pathlib import Path

class M4RIRank:
    def __init__(self, library):
        self.library_path=Path(library)
        self._dll=ctypes.CDLL(str(self.library_path.resolve()))
        self._rank=self._dll.db_m4ri_rank
        self._rank.argtypes=[ctypes.c_int,ctypes.c_int,ctypes.c_void_p,ctypes.c_int]
        self._rank.restype=ctypes.c_int

    def rank(self, values, width=None):
        values=list(values)
        if any(type(x) is not int or x<0 for x in values):
            raise ValueError('M4RI vectors must be nonnegative Python integers.')
        width=max(values,default=0).bit_length() if width is None else width
        if width<0 or any(x.bit_length()>width for x in values):
            raise ValueError('Declared matrix width is too small.')
        if not values or not width:return 0
        stride=(width+7)//8
        raw=b''.join(value.to_bytes(stride,'little') for value in values)
        buffer=ctypes.create_string_buffer(raw)
        result=self._rank(len(values),width,buffer,stride)
        if result<0:raise ValueError('M4RI rejected the input dimensions.')
        return result

    def __call__(self, values, expected_rank):
        return self.rank(values)==expected_rank
