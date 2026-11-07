"""Launch the Sage comparator in an existing extracted Windows Cygwin runtime."""
import argparse
from pathlib import Path
import shlex
import subprocess


def cygpath(path):
    p=Path(path).resolve()
    if not p.drive:raise ValueError('A Windows absolute path is required.')
    return '/cygdrive/'+p.drive[0].lower()+p.as_posix()[2:]


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--runtime',type=Path,required=True,help='Cygwin root containing bin/bash.exe and opt/sagemath-9.3')
    p.add_argument('--corpus',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--repeats',type=int,default=5)
    p.add_argument('--validation',choices=['spectral','incidence','gram'],default='spectral')
    args=p.parse_args()
    command=['/opt/sagemath-9.3/sage','-python',cygpath(Path(__file__).with_name('sage_m4ri_sage.py')),
      '--corpus',cygpath(args.corpus),'--output',cygpath(args.output),'--repeats',str(args.repeats),'--validation',args.validation]
    shell='export PATH=/usr/bin:/bin; exec '+' '.join(shlex.quote(x) for x in command)
    subprocess.run([str(args.runtime/'bin/bash.exe'),'--noprofile','--norc','-c',shell],check=True)

if __name__=='__main__':main()
