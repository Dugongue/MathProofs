
from pathlib import Path
import sys,subprocess,json,statistics,hashlib
b=Path(__file__).resolve().parent;u=b/'baseline';c=b/(sys.argv[4] if len(sys.argv)>4 else 'hybrid')
import os,shutil
gcc=os.environ.get('MEDS_CC') or shutil.which('gcc')
nm=os.environ.get('MEDS_NM') or shutil.which('nm')
if not gcc or not nm: raise SystemExit('Install GCC/binutils and add them to PATH, or set MEDS_CC and MEDS_NM')
param=sys.argv[1];reps=int(sys.argv[2]) if len(sys.argv)>2 else 7
label=sys.argv[3] if len(sys.argv)>3 else 'build';d=b/label/param;d.mkdir(parents=True,exist_ok=True)
(d/'api.h').write_bytes(subprocess.check_output([sys.executable,str(u/'params.py'),'-a',param]))
flags=['-O3','-mavx2','-D'+param,'-I'+str(d)]
symbols=[];objects=[];srcs=['matrixmod','util','meds']
for s in srcs:
 obj=d/(s+'-raw.o');subprocess.run([gcc,*flags,'-c',str(u/(s+'.c')),'-o',str(obj)],check=True)
 for line in subprocess.check_output([nm,'--defined-only','--extern-only',str(obj)],text=True).splitlines():
  if len(line.split())>=3 and line.split()[-1].isidentifier():symbols.append(line.split()[-1])
hashes={}
for prefix,root in [('base',u),('fast',c)]:
 defs=['-D'+s+'='+prefix+'_'+s for s in sorted(set(symbols))]
 for s in srcs:
  obj=d/(prefix+'-'+s+'.o');subprocess.run([gcc,*flags,*defs,'-c',str(root/(s+'.c')),'-o',str(obj)],check=True);objects.append(str(obj))
 hashes[prefix]={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in root.iterdir() if p.suffix in ['.h','.c']}
for s in ['fips202','bitstream','seed']:
 obj=d/(s+'.o');subprocess.run([gcc,*flags,'-c',str(u/(s+'.c')),'-o',str(obj)],check=True);objects.append(str(obj))
exe=d/'bench.exe';subprocess.run([gcc,*flags,'-I'+str(u),str(b/'bench.c'),*objects,'-Wl,--stack,33554432','-o',str(exe)],check=True)
meta={'parameter':param,'trials':reps,'flags':flags,'hashes':hashes,'harness_sha256':hashlib.sha256((b/'bench.c').read_bytes()).hexdigest(),'compiler':subprocess.check_output([gcc,'--version'],text=True).splitlines()[0]};(d/'build.json').write_text(json.dumps(meta,indent=2))
print('Running',param,flush=True)
with (d/'results.jsonl').open('w') as out,(d/'stderr.log').open('w') as err:p=subprocess.run([str(exe),str(reps)],stdout=out,stderr=err,timeout=900)
if p.returncode:print((d/'stderr.log').read_text()[-2000:]);sys.exit(p.returncode)
rows=[json.loads(l) for l in (d/'results.jsonl').read_text().splitlines() if l.startswith('{')]
summary={'parameter':param,'trials':reps,'checks':[r for r in rows if r['kind']!='timing']}
for op,name in enumerate(['keygen','sign','verify']):
 tim=[r for r in rows if r['kind']=='timing' and r['trial']>=0 and r['op']==op];summary[name]={}
 for unit in ['ms','cycles']:
  x={tag:statistics.median(r[tag+'_'+unit] for r in tim) for tag in ['scalar','published','ours']};x['published_over_ours']=x['published']/x['ours'];x['scalar_over_ours']=x['scalar']/x['ours'];x['paired_ratio']=statistics.median(r['published_'+unit]/r['ours_'+unit] for r in tim);summary[name][unit]=x
(d/'summary.json').write_text(json.dumps(summary,indent=2));print(json.dumps({k:v for k,v in summary.items() if k!='checks'}),flush=True)
