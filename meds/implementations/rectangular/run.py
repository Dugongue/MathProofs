from pathlib import Path
import subprocess,sys,json,statistics,hashlib
b=Path(__file__).resolve().parent;o=b;u=o/'upstream/ref'
import os,shutil
gcc=os.environ.get('MEDS_CC') or shutil.which('gcc')
nm=os.environ.get('MEDS_NM') or shutil.which('nm')
if not gcc or not nm: raise SystemExit('Install GCC/binutils and add them to PATH, or set MEDS_CC and MEDS_NM')
param=sys.argv[1];variant=sys.argv[2];trials=int(sys.argv[3]) if len(sys.argv)>3 else 3
run=sys.argv[4] if len(sys.argv)>4 else 'build'
d=b/run/(param+'-'+variant);d.mkdir(parents=True,exist_ok=True)
for arg,f in [('-p','params.h'),('-a','api.h')]: (d/f).write_bytes(subprocess.check_output([sys.executable,str(u/'params.py'),arg,param]))
flags=['-O3','-march=native','-std=c11','-I'+str(d),'-I'+str(o),'-I'+str(u/'include'),'-Wno-unused-function']
objects=[];source_hashes={}
for src in ['fips202','bitstream','seed']:
 obj=d/(src+'.o');subprocess.run([gcc,*flags,'-c',str(u/'src'/(src+'.c')),'-o',str(obj)],check=True);objects.append(str(obj))
# Build reference objects to discover and namespace every external symbol.
raw=[];symbols=[]
for src in ['matrixmod','util','meds']:
 path=u/'src'/(src+'.c') if src!='meds' else o/'meds-original.c';obj=d/(src+'-raw.o')
 subprocess.run([gcc,*flags,'-c',str(path),'-o',str(obj)],check=True)
 names=subprocess.check_output([nm,'--defined-only','--extern-only',str(obj)],text=True)
 symbols.extend(line.split()[-1] for line in names.splitlines() if len(line.split())>=3 and line.split()[-1].isidentifier())
for prefix in ['base','fast']:
 defs=['-D'+sym+'='+prefix+'_'+sym for sym in symbols]
 for src in ['matrixmod','util','meds']:
  path=u/'src'/(src+'.c') if src!='meds' else o/'meds-original.c'
  if prefix=='fast':
   if src=='matrixmod' and variant in ['native','native-no-cancel']:path=b/'matrixmod-native.c'
   if src=='meds':path=(b/'meds-native.c' if variant=='native' else o/'meds-cancelled.c' if variant=='cancel' else o/'meds-original.c')
  if variant=='ablation':
   if src=='matrixmod':path=b/'matrixmod-native.c'
   if src=='meds':path=b/'meds-native.c' if prefix=='fast' else o/'meds-original.c'
  if variant=='competitor':
   if src=='matrixmod':path=b/('matrixmod-native.c' if prefix=='fast' else 'matrixmod-ported-avx2.c')
   if src=='meds':path=b/'meds-native.c'
  source_hashes[prefix+'-'+src]={'path':str(path),'sha256':hashlib.sha256(path.read_bytes()).hexdigest()}
  obj=d/(prefix+'-'+src+'.o');subprocess.run([gcc,*flags,*defs,'-c',str(path),'-o',str(obj)],check=True);objects.append(str(obj))
# Harness uses reference matrix/solver helpers, separate implementations for API.
defs=['-D'+sym+'=base_'+sym for sym in symbols if not sym.startswith('crypto_')]
for p in ['base','fast']:
 for short,long in [('keypair','crypto_sign_keypair'),('sign','crypto_sign'),('open','crypto_sign_open')]:defs.append('-D'+p+'_'+short+'='+p+'_'+long)
exe=d/'bench.exe';subprocess.run([gcc,*flags,*defs,str(b/'bench.c'),*objects,'-Wl,--stack,33554432','-o',str(exe)],check=True)
meta={'parameter':param,'variant':variant,'trials':trials,'source_hashes':source_hashes,'harness_sha256':hashlib.sha256((b/'bench.c').read_bytes()).hexdigest(),'flags':flags,'compiler':subprocess.check_output([gcc,'--version'],text=True).splitlines()[0]}
(d/'build.json').write_text(json.dumps(meta,indent=2))
with (d/'results.jsonl').open('w') as out,(d/'stderr.log').open('w') as err:p=subprocess.run([str(exe),str(trials)],stdout=out,stderr=err,timeout=480)
if p.returncode:print((d/'stderr.log').read_text()[-2500:]);sys.exit(p.returncode)
rows=[json.loads(s) for s in (d/'results.jsonl').read_text().splitlines() if s.startswith('{')];tim=[r for r in rows if r['kind']=='timing'];cyc=[r for r in rows if r['kind']=='cycles']
for f in ['sign','verify']:
 for unit,data,tail in [('ms',tim,'_ms'),('cycles',cyc,'')]:
  x=statistics.median(r['base_'+f+tail] for r in data);y=statistics.median(r['fast_'+f+tail] for r in data)
  meta[f+'_'+unit]={'base':x,'fast':y,'ratio':x/y,'paired_ratio_median':statistics.median(r['base_'+f+tail]/r['fast_'+f+tail] for r in data)}
kt=[r for r in rows if r['kind']=='keygen']
meta['keygen']={unit:{'base':statistics.median(r['base_'+unit] for r in kt),'fast':statistics.median(r['fast_'+unit] for r in kt),'paired_ratio_median':statistics.median(r['base_'+unit]/r['fast_'+unit] for r in kt)} for unit in ['ms','cycles']}
meta['checks']=[r for r in rows if r['kind'] not in ['cycles','timing','keygen']]
(d/'summary.json').write_text(json.dumps(meta,indent=2));print(json.dumps(meta),flush=True)
