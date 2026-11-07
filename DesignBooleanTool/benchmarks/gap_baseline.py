"""Actual GAP DESIGN/GF(2) full-pipeline benchmark, with explicit runtime path.

GAP and DESIGN remain external dependencies; this adapter does not emulate them.
Input-script parsing and GAP process startup are outside GAP's inner timers and
are separately reported. Every timed call validates, reconstructs and checks.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import statistics
import subprocess
import sys
import tempfile
import time

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'examples'))
sys.path.insert(0,str(Path(__file__).resolve().parent))
from generate import make_fixture
from reference import verify


def gap_string(value):
    return json.dumps(str(value).replace('\\','/'))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--gap-root',type=Path,required=True,help='Directory containing gap.exe and pkg/design')
    parser.add_argument('--runtime-bin',type=Path,help='Cygwin runtime bin directory, if required')
    parser.add_argument('--repeats',type=int,default=5)
    parser.add_argument('--max-m',type=int,default=10)
    parser.add_argument('--output',type=Path,default=Path(__file__).with_name('gap-results.json'))
    parser.add_argument('--timeout',type=float,default=300)
    args=parser.parse_args()
    if args.repeats<1 or not 7<=args.max_m<=10:parser.error('repeats>=1; max-m in7..10')
    exe=args.gap_root/'gap.exe'
    if not exe.is_file():parser.error('gap-root does not contain gap.exe')
    manifest=json.loads((ROOT/'examples/manifest.json').read_text(encoding='utf-8'))
    fixtures=[json.loads((ROOT/'examples'/entry['file']).read_text(encoding='utf-8')) for entry in manifest['fixtures']]
    for m in range(8,args.max_m+1):
        f=make_fixture('quadratic-family' if m%2==0 else 'plateaued-stabilization',m)
        f['id']='stress-'+f['id'];fixtures.append(f)
    setup='''if LoadPackage("design")<>true then Error("DESIGN package unavailable");fi;
SizeScreen([1000000,1000000]);
'''
    setup+='Read('+gap_string(Path(__file__).with_name('gap_pipeline.g').resolve())+');\n'
    setup+='Inputs := '+json.dumps([f['incidence'] for f in fixtures],separators=(',',':'))+';;\n'
    setup+='Ids := '+json.dumps([f['id'] for f in fixtures])+';;\n'
    setup+='''Print("DB_BEGIN\\n{\\"gap_version\\":\\"",GAPInfo.Version,"\\",\\"design_version\\":\\"",PackageInfo("design")[1].Version,"\\",\\"cases\\":[");
for idx in [1..Length(Inputs)] do
 if idx>1 then Print(",");fi;
 warm := DBPipeline(Inputs[idx]);;
 samples := [];;
'''
    setup+=' for iteration in [1..'+str(args.repeats)+'] do\n'
    setup+='''  started := NanosecondsSinceEpoch();;
  outcome := DBPipeline(Inputs[idx]);;
  Add(samples,NanosecondsSinceEpoch()-started);
 od;
 Print("{\\"id\\":\\"",Ids[idx],"\\",\\"samples_ns\\":",samples,",\\"result\\":");
 DBPrintJSON(outcome);
 Print("}");
od;
Print("]}\\nDB_END\\n");
QUIT;
'''
    env=os.environ.copy()
    if args.runtime_bin:env['PATH']=str(args.runtime_bin)+os.pathsep+env.get('PATH','')
    with tempfile.TemporaryDirectory(prefix='design-gap-') as folder:
        script=Path(folder)/'run.g';script.write_text(setup,encoding='utf-8',newline='\n')
        start=time.perf_counter()
        completed=subprocess.run([str(exe),'-l',str(args.gap_root),'-A','-T','-q','-b','-r',str(script)],env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True,timeout=args.timeout)
        wall=time.perf_counter()-start
    if 'DB_BEGIN\n' not in completed.stdout or '\nDB_END' not in completed.stdout:
        print(completed.stdout[-4000:],file=sys.stderr);print(completed.stderr[-4000:],file=sys.stderr)
        raise RuntimeError('GAP did not produce a complete benchmark; no successful timing is asserted')
    report=json.loads(completed.stdout.split('DB_BEGIN\n',1)[1].split('\nDB_END',1)[0])
    output=[]
    for fixture,case in zip(fixtures,report['cases']):
        result=case['result'];expected=fixture['expected']['recognized']
        assert (result['status']=='recognized')==expected,(case['id'],result['status'])
        if expected:assert verify(fixture['incidence'],result['certificate']),case['id']
        samples=[n/1e6 for n in case['samples_ns']]
        record={'id':case['id'],'points':len(fixture['incidence']),'blocks':len(fixture['incidence'][0]),'status':result['status'],'median_ms':statistics.median(samples),'samples_ms':samples,'independent_certificate_verified':bool(expected)}
        output.append(record);print(f"{record['id']}: {record['median_ms']:.3f} ms {record['status']}",flush=True)
    document={'backend':{'gap':report['gap_version'],'design':report['design_version']},'methodology':{'repeats':args.repeats,'warmup':1,'clock':'GAP NanosecondsSinceEpoch','scope':'Preparsed native GAP integer incidence -> actual DESIGN validation -> compressed GF(2) rank/coordinates -> reconstruction -> exact Walsh/incidence/support checks','startup_and_script_parsing':'Excluded from case timers; separately reported process wall time','process_wall_seconds':wall,'reconstruction':'Original adapter code; not a claimed built-in DESIGN reconstructor','library_calls':['BlockDesign','IsBinaryBlockDesign','IsSimpleBlockDesign','PairwiseBalancedLambda','SemiEchelonMat','RankMat']},'cases':output,'source_hashes':{name:hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest() for name in ['gap_baseline.py','gap_pipeline.g']}}
    args.output.write_text(json.dumps(document,indent=2)+'\n',encoding='utf-8',newline='\n')

if __name__=='__main__':main()
