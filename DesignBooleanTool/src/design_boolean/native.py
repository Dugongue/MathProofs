"""Optional C++ recognition backend; all outputs use the public certificate schema.

Building is explicit. Recognition never downloads code or invokes a compiler.
"""
from __future__ import annotations
import ctypes
import os
from operator import index
from pathlib import Path
import shutil
import subprocess
import sys
from time import perf_counter
from .core import IncidenceMatrix, RecognitionResult, _hash, _parameters

class NativeUnavailable(RuntimeError):
    pass

class NativeExecutionError(RuntimeError):
    pass

_LIBRARY=None
_LIBRARY_PATH=None
_BINARY_VALIDATION_TABLE=bytes(0 if i<2 else 1 for i in range(256))

def _filename():
    return 'design_boolean_native.dll' if sys.platform=='win32' else 'libdesign_boolean_native.so'

def _candidates():
    package=Path(__file__).resolve().parent
    if os.environ.get('DESIGN_BOOLEAN_NATIVE_LIBRARY'):
        yield Path(os.environ['DESIGN_BOOLEAN_NATIVE_LIBRARY'])
    if _LIBRARY_PATH:
        yield Path(_LIBRARY_PATH)
    yield package/'_native'/_filename()
    yield package.parents[1]/'build'/_filename()

def _library():
    global _LIBRARY,_LIBRARY_PATH
    if _LIBRARY is not None:return _LIBRARY
    errors=[]
    for path in _candidates():
        if not path.is_file():continue
        try:
            lib=ctypes.CDLL(str(path))
            lib.db_abi_version.restype=ctypes.c_int
            if lib.db_abi_version()!=2:raise NativeUnavailable('Unsupported native ABI version.')
            lib.db_recognize.argtypes=[ctypes.POINTER(ctypes.c_ubyte),ctypes.c_size_t,ctypes.c_uint32,ctypes.c_uint32,ctypes.c_int,ctypes.c_int,
                ctypes.POINTER(ctypes.c_uint32),ctypes.c_size_t,ctypes.POINTER(ctypes.c_ubyte),ctypes.c_size_t,
                ctypes.POINTER(ctypes.c_uint32),ctypes.c_char_p,ctypes.c_size_t]
            lib.db_recognize.restype=ctypes.c_int
            _LIBRARY=lib;_LIBRARY_PATH=path
            return lib
        except (OSError,AttributeError,NativeUnavailable) as exc:errors.append(str(exc))
    raise NativeUnavailable('Optional native library is unavailable. Run build-native explicitly.'+(' '+ '; '.join(errors) if errors else ''))

def available():
    try:_library();return True
    except NativeUnavailable:return False

def build_native(*, output=None, compiler=None):
    """Compile for this host using a C++17 compiler and return the library path."""
    global _LIBRARY_PATH
    package=Path(__file__).resolve().parent
    source=package.parents[1]/'native/design_boolean.cpp'
    if not source.is_file():source=package/'_native_src/recognizer.cpp'
    if not source.is_file():raise NativeUnavailable('Native source is not present in this distribution.')
    compiler=compiler or os.environ.get('CXX') or shutil.which('g++') or shutil.which('clang++')
    if not compiler:raise NativeUnavailable('A C++17 compiler (g++ or clang++) is required to build the optional backend.')
    destination=Path(output) if output is not None else package/'_native'/_filename()
    destination.parent.mkdir(parents=True,exist_ok=True)
    command=[compiler,'-O3','-std=c++17','-shared',str(source),'-o',str(destination)]
    if os.environ.get('DESIGN_BOOLEAN_NATIVE_TUNE')=='native':command.append('-march=native')
    command += ['-static','-static-libgcc','-static-libstdc++'] if sys.platform=='win32' else ['-fPIC']
    done=subprocess.run(command,capture_output=True,text=True)
    if done.returncode:raise NativeUnavailable('Native compilation failed: '+done.stderr[-4000:])
    _LIBRARY_PATH=destination
    return destination

def _dense_input(incidence):
    rows=[];width=None
    for row_number,row in enumerate(incidence):
        if isinstance(row,(str,bytes)):
            if isinstance(row,bytes):row=row.decode('ascii')
            if any(c not in '01' for c in row):raise ValueError(f'Row {row_number} must contain only 0 and 1.')
            raw=bytes(ord(c)-48 for c in row)
        else:
            if isinstance(row,int):raise ValueError(f'Row {row_number} must be an iterable of bits.')
            raw=bytes(row) if isinstance(row,(list,tuple)) else bytes(index(x) for x in row)
        if width is None:width=len(raw)
        elif len(raw)!=width:raise ValueError('Incidence rows must have equal lengths.')
        rows.append(raw)
    if not rows or not width:raise ValueError('An incidence matrix must have at least one point and block.')
    return b''.join(rows),len(rows),width,False

def recognize_native(incidence,*,point_labels=None,block_labels=None,validation='certificate'):
    """Same recognition contract as the Python implementation, with native exact checks."""
    started=perf_counter();timings={};params={};diagnostics={'backend':'native','timings_seconds':timings,'validation_method':'walsh_certificate' if validation=='certificate' else 'explicit_pair_counts'}
    def finish(status,reason,cert=None):
        timings['total']=perf_counter()-started
        return RecognitionResult(status,reason,params,cert,diagnostics)
    try:
        if validation not in ('certificate','explicit'):raise ValueError('validation must be certificate or explicit.')
        if isinstance(incidence,IncidenceMatrix):
            v=len(incidence.rows);b=index(incidence.num_blocks)
            if not v or b<=0:raise ValueError('An incidence matrix must have at least one point and block.')
            width=(b+7)//8
            row_values=tuple(index(x) for x in incidence.rows)
            if any(x<0 or x.bit_length()>b for x in row_values):raise ValueError('A packed incidence row exceeds the declared block count.')
            data=b''.join(x.to_bytes(width,'little') for x in row_values);packed=True
        else:
            data,v,b,packed=_dense_input(incidence)
            if data.translate(_BINARY_VALIDATION_TABLE).count(1):
                raise ValueError('Incidence entries must be bits.')
        if point_labels is not None and len(point_labels)!=v:raise ValueError('point_labels length must match the number of rows.')
        if block_labels is not None and len(block_labels)!=b:raise ValueError('block_labels length must match the number of columns.')
        params=_parameters(IncidenceMatrix((0,)*v,b)) or {}
        if not params:return finish('unsupported','Supported shapes require v=2^n, even n>=4, and b=2^m with m>=n.')
        # Dense input is not yet semantically validated; C++ checks every byte.
        m=params['m']
        if m>20 or v*b>(1<<28):return finish('unsupported','Matrix exceeds the native resource bound; use backend=python for a larger trusted input.')
        timings['input']=perf_counter()-started
    except (TypeError,ValueError,OverflowError,UnicodeError) as exc:
        return finish('invalid_input',str(exc))
    lib=_library()
    source=(ctypes.c_ubyte*len(data)).from_buffer_copy(data)
    outputs=(ctypes.c_uint32*(2*b+2*v+m))()
    row_bytes=(b+7)//8
    packed_rows=(ctypes.c_ubyte*(v*row_bytes))()
    rank=ctypes.c_uint32();reason=ctypes.create_string_buffer(1024)
    native_started=perf_counter()
    code=lib.db_recognize(source,len(data),v,b,int(packed),int(validation=='certificate'),outputs,len(outputs),packed_rows,len(packed_rows),ctypes.byref(rank),reason,len(reason))
    timings['native_validation_reconstruction_check']=perf_counter()-native_started
    text=reason.value.decode('utf-8','replace')
    diagnostics['normalized_rank']=rank.value
    if rank.value:
        if validation=='explicit':diagnostics['design_validated']=True
        diagnostics['bordered_rank']=rank.value+2
    if code:
        diagnostics['reason_code']='native.rejected'
        if code==4:raise NativeExecutionError(text)
        return finish({1:'not_recognized',2:'invalid_input',3:'unsupported'}.get(code,'invalid_input'),text)
    serialization_started=perf_counter()
    packed_data=bytes(packed_rows)
    matrix=IncidenceMatrix(tuple(int.from_bytes(packed_data[p*row_bytes:(p+1)*row_bytes],'little') for p in range(v)),b)
    cert={'schema':'design-boolean/1','parameters':params.copy(),'input_hash':_hash(matrix),
        'truth_table':list(outputs[:b]),'block_coordinates':list(outputs[b:2*b]),
        'point_frequencies':list(outputs[2*b:2*b+v]),'point_offsets':list(outputs[2*b+v:2*b+2*v]),
        'amplitude':params['amplitude'],'basis_block_indices':list(outputs[2*b+2*v:]),'anchor_point':0,'anchor_block':0}
    if point_labels is not None:cert['point_labels']=list(point_labels)
    if block_labels is not None:cert['block_labels']=list(block_labels)
    diagnostics.update(design_validated=True,bordered_rank=rank.value+2,reason_code='native.recognized',
        certificate_checks={'walsh_spectrum':True,'walsh_support_size':v,'incidence_identity':True,'walsh_support_affine_rank':m,'no_nonzero_linear_structures':True,'block_coordinate_bijection':True})
    timings['certificate_serialization']=perf_counter()-serialization_started
    return finish('recognized',text,cert)
