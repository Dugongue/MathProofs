
from pathlib import Path
import subprocess,sys,json,hashlib,statistics,time
b=Path(__file__).resolve().parent;u=b/'.deps/upstream/ref';c=b/'.deps/candidate'
import os,shutil
gcc=os.environ.get('MEDS_CC') or shutil.which('gcc')
nm=os.environ.get('MEDS_NM') or shutil.which('nm')
if not gcc or not nm: raise SystemExit('Install GCC/binutils and add them to PATH, or set MEDS_CC and MEDS_NM')
level=int(sys.argv[1]);reps=int(sys.argv[2]) if len(sys.argv)>2 else 3;label=sys.argv[3] if len(sys.argv)>3 else 'build'
d=b/label/('level'+str(level));d.mkdir(parents=True,exist_ok=True)
srcs=['util','matrixmod','corankone','kernel','contract','algo3','key_gen','sign','verify']
flags=['-O3','-march=native','-fno-plt','-funroll-loops','-DLEVEL='+str(level),'-DUSE_FORWARD_DIFF_SCAN']
# Namespace both entire implementations, sharing only SHAKE and resettable RNG.
symbols=[]
for s in srcs:
 obj=d/(s+'-raw.o');subprocess.run([gcc,'-O0','-DLEVEL='+str(level),'-c',str(u/(s+'.c')),'-o',str(obj)],check=True)
 for line in subprocess.check_output([nm,'--extern-only','--defined-only',str(obj)],text=True).splitlines():
  if len(line.split())>=3 and line.split()[-1].isidentifier():symbols.append(line.split()[-1])
objects=[];hashes={}
for prefix,root in [('base',u),('fast',c)]:
 defs=['-D'+s+'='+prefix+'_'+s for s in sorted(set(symbols))]
 for s in srcs:
  path=root/(s+'.c');obj=d/(prefix+'-'+s+'.o')
  subprocess.run([gcc,*flags,'-flto',*defs,'-c',str(path),'-o',str(obj)],check=True);objects.append(str(obj))
 hashes[prefix]={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(root.iterdir()) if p.suffix in ['.h','.c']}
 print('compiled',prefix,'level',level,flush=True)
for s in ['rng','fips202']:
 obj=d/(s+'.o');subprocess.run([gcc,*flags,'-flto','-c',str(u/(s+'.c')),'-o',str(obj)],check=True);objects.append(str(obj))
exe=d/'bench.exe';subprocess.run([gcc,*flags,'-flto','-I'+str(u),'-I'+str(c),str(b/'bench.c'),*objects,'-Wl,--stack,33554432','-o',str(exe)],check=True)
meta={'level':level,'reps':reps,'flags':flags+['-flto'],'compiler':subprocess.check_output([gcc,'--version'],text=True).splitlines()[0],'hashes':hashes,'harness_sha256':hashlib.sha256((b/'bench.c').read_bytes()).hexdigest()}
(d/'build.json').write_text(json.dumps(meta,indent=2));print('running',exe,flush=True)
with (d/'results.jsonl').open('w') as out,(d/'stderr.log').open('w') as err:
 p=subprocess.run([str(exe),str(reps)],stdout=out,stderr=err,timeout=900)
if p.returncode:print((d/'stderr.log').read_text());print((d/'results.jsonl').read_text()[-3000:]);sys.exit(p.returncode)
rows=[json.loads(l) for l in (d/'results.jsonl').read_text().splitlines() if l.startswith('{')]
summary={'level':level,'reps':reps,'passed':True,'checks':[r for r in rows if r['kind']!='timing']}
for op,name in enumerate(['keygen','sign','verify']):
 r=[x for x in rows if x['kind']=='timing' and x['op']==op and x['trial']>=0]
 summary[name]={}
 for unit in ['ms','cycles']:
  x=statistics.median(v['base_'+unit] for v in r);y=statistics.median(v['fast_'+unit] for v in r)
  summary[name][unit]={'base':x,'fast':y,'speedup':x/y,'paired_speedup':statistics.median(v['base_'+unit]/v['fast_'+unit] for v in r)}
(d/'summary.json').write_text(json.dumps(summary,indent=2));print(json.dumps(summary),flush=True)

