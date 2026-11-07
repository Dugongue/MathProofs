"""Build a pinned upstream M4RI rank wrapper outside the product source tree.

Requires git and a C compiler (MinGW GCC on Windows). Downloads M4RI under its
GPL-2.0-or-later license. No upstream source or binary is bundled in this project.
"""
import argparse
import hashlib
import json
from pathlib import Path
import platform
import subprocess

COMMIT='397a70fcffeb17b0c25c0aa40231145fc392317f'
REPOSITORY='https://github.com/malb/m4ri.git'

def run(args,cwd=None):
    subprocess.run([str(x) for x in args],cwd=cwd,check=True)

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--work',type=Path,required=True,help='External build/cache directory')
    p.add_argument('--cc',default='gcc')
    p.add_argument('--source',type=Path,help='Use an existing checkout at the pinned commit')
    args=p.parse_args();work=args.work.resolve();work.mkdir(parents=True,exist_ok=True)
    source=args.source.resolve() if args.source else work/'m4ri'
    if not source.exists():
        git=['git']+(['-c','http.sslBackend=openssl'] if platform.system()=='Windows' else [])
        run(git+['clone',REPOSITORY,source]);run(['git','checkout','--detach',COMMIT],source)
    actual=subprocess.check_output(['git','rev-parse','HEAD'],cwd=source,text=True).strip()
    if actual!=COMMIT:raise SystemExit('Existing M4RI checkout does not match pinned commit')
    x86=platform.machine().lower() in ('amd64','x86_64','x86','i386','i686')
    flags=['-O3','-march=native']+(['-msse2'] if x86 else [])
    values={'M4RI_HAVE_MM_MALLOC':str(int(x86)),'M4RI_HAVE_POSIX_MEMALIGN':'0','M4RI_SSE2_ENABLED':str(int(x86)),
      'M4RI_HAVE_OPENMP':'0','M4RI_CPU_L1_CACHE':'32768','M4RI_CPU_L2_CACHE':'262144','M4RI_CPU_L3_CACHE':'8388608',
      'M4RI_DEBUG_DUMP':'0','M4RI_DEBUG_MZD':'0','M4RI_HAVE_LIBPNG':'0','CC':args.cc,'OPENMP_CFLAGS':'','CFLAGS':' '.join(flags),
      'M4RI_ENABLE_MZD_CACHE':'1','M4RI_ENABLE_MMC':'1'}
    config=(source/'m4ri/m4ri_config.h.in').read_text()
    for key,value in values.items():config=config.replace('@'+key+'@',value)
    if '@' in config:raise SystemExit('Unexpected upstream configure variable')
    (source/'m4ri/m4ri_config.h').write_text(config,encoding='utf-8',newline='\n')
    target=work/('m4ri_rank.dll' if platform.system()=='Windows' else 'm4ri_rank.so')
    sources=sorted((source/'m4ri').glob('*.c'))
    cmd=[args.cc,*flags,'-Wno-error=implicit-function-declaration','-shared','-static-libgcc','-I',source,'-I',source/'m4ri',*sources,
         Path(__file__).with_name('rank_wrapper.c'),'-o',target]
    if platform.system()!='Windows':cmd.extend(['-fPIC','-lm'])
    run(cmd)
    metadata={'upstream':REPOSITORY,'commit':actual,'version':'20260122','compiler_flags':flags,
              'sse2':x86,'openmp':False,'cache_bytes':{'L1':32768,'L2':262144,'L3':8388608},
              'configuration':'Explicit portable build configuration, cache values not auto-detected',
              'license':'GPL-2.0-or-later; upstream COPYING retained in external checkout',
              'binary_sha256':hashlib.sha256(target.read_bytes()).hexdigest()}
    (work/'m4ri-build.json').write_text(json.dumps(metadata,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(target.name)

if __name__=='__main__':main()
