"""Explicit offline build; no compiler runs during recognition."""
from pathlib import Path
import argparse
import os
import platform
import shutil
import subprocess
import sys

def build(output=None, compiler=None):
    root=Path(__file__).resolve().parents[1]
    source=Path(__file__).with_name('design_boolean.cpp')
    destination=Path(output) if output else root/'build'/('design_boolean_native.dll' if sys.platform=='win32' else 'libdesign_boolean_native.so')
    destination.parent.mkdir(parents=True,exist_ok=True)
    compiler=compiler or os.environ.get('CXX') or shutil.which('g++') or shutil.which('clang++')
    if not compiler:raise RuntimeError('A C++17 compiler (g++ or clang++) is required for the optional native backend.')
    command=[compiler,'-O3','-std=c++17','-shared',str(source),'-o',str(destination)]
    if os.environ.get('DESIGN_BOOLEAN_NATIVE_TUNE')=='native':command.append('-march=native')
    if sys.platform=='win32':command += ['-static','-static-libgcc','-static-libstdc++']
    else:command += ['-fPIC']
    subprocess.run(command,check=True,capture_output=True,text=True)
    return destination

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path);p.add_argument('--compiler');a=p.parse_args()
    print(build(a.output,a.compiler))
