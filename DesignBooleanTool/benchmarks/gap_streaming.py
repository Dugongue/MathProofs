"""Checkpointing actual GAP DESIGN benchmark; preserves completed cases on timeout.

This is a transport/checkpoint wrapper around the unchanged gap_pipeline.g.
It writes per-case JSON from GAP using closed streams and independently checks
positive certificates before incorporating them into the public timing report.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import statistics
import subprocess
import sys
import time

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'examples'))
sys.path.insert(0,str(Path(__file__).resolve().parent))
from generate import make_fixture
from reference import verify


def quoted(value):
    return json.dumps(str(value).replace('\\','/'))


def safe_json(path):
    try:
        return json.loads(path.read_text(encoding='utf-8'))
    except (OSError,ValueError):
        return None


def write_json(path,value):
    temporary=path.with_suffix(path.suffix+'.tmp')
    temporary.write_text(json.dumps(value,indent=2)+'\n',encoding='utf-8',newline='\n')
    temporary.replace(path)


def fixtures_for(max_m,case_ids):
    manifest=json.loads((ROOT/'examples/manifest.json').read_text(encoding='utf-8'))
    result=[json.loads((ROOT/'examples'/entry['file']).read_text(encoding='utf-8')) for entry in manifest['fixtures']]
    for m in range(8,max_m+1):
        family='quadratic-family' if m%2==0 else 'plateaued-stabilization'
        if case_ids and f'stress-{family}-m{m}' not in case_ids:continue
        fixture=make_fixture(family,m)
        fixture['id']='stress-'+fixture['id'];result.append(fixture)
    if case_ids:
        available={f['id'] for f in result}
        if set(case_ids)-available:
            raise ValueError('Unknown case IDs: '+', '.join(sorted(set(case_ids)-available)))
        wanted=set(case_ids)
        result=[f for f in result if f['id'] in wanted]
    return result


def case_record(fixture,case,repeats):
    result=case['result']
    expected=fixture['expected']['recognized']
    if (result['status']=='recognized')!=expected:
        raise ValueError('GAP classification disagrees on '+fixture['id'])
    samples=case['samples_ns']
    if len(samples)!=repeats or any(type(x)is not int or x<0 for x in samples):
        raise ValueError('Wrong timing sample count or type on '+fixture['id'])
    if expected and not verify(fixture['incidence'],result['certificate']):
        raise ValueError('Independent certificate verification failed on '+fixture['id'])
    milliseconds=[x/1e6 for x in samples]
    return {'id':fixture['id'],'points':len(fixture['incidence']),'blocks':len(fixture['incidence'][0]),
            'status':result['status'],'median_ms':statistics.median(milliseconds),'samples_ms':milliseconds,
            'independent_certificate_verified':bool(expected)}


def script_for(fixtures,indices,folder,repeats):
    pipeline=Path(__file__).with_name('gap_pipeline.g').resolve()
    text='if LoadPackage("design")<>true then Error("DESIGN unavailable");fi;\nSizeScreen([1000000,1000000]);\n'
    text+='Read('+quoted(pipeline)+');\n'
    text+='''DBCheckpointResult := function(path,id,samples,outcome)
 local stream;
 stream:=OutputTextFile(path,false);
 SetPrintFormattingStatus(stream,false);
 PrintTo(stream,"{\\"id\\":\\"",id,"\\",\\"samples_ns\\":",samples,",\\"result\\":{\\"status\\":\\"",outcome.status,"\\"");
 if outcome.status="recognized" then
  PrintTo(stream,",\\"certificate\\":{\\"truth_table\\":",outcome.truth_table,
   ",\\"block_coordinates\\":",outcome.block_coordinates,",\\"point_frequencies\\":",outcome.point_frequencies,
   ",\\"point_offsets\\":",outcome.point_offsets,",\\"amplitude\\":",outcome.amplitude,"}");
 fi;
 PrintTo(stream,"}}\\n");CloseStream(stream);
end;
'''
    text+='PrintTo('+quoted(folder/'backend.json')+',"{\\"gap\\":\\"",GAPInfo.Version,"\\",\\"design\\":\\"",PackageInfo("design")[1].Version,"\\"}\\n");\n'
    # Each complete case gets a closed standalone file. Thus a later timeout
    # cannot discard earlier certificates/timings buffered in process stdout.
    for i in indices:
        fixture=fixtures[i]
        text+='M := '+json.dumps(fixture['incidence'],separators=(',',':'))+';;\n'
        text+='PrintTo('+quoted(folder/'progress.json')+',"{\\"case_index\\":'+str(i)+',\\"phase\\":\\"warmup\\"}\\n");\n'
        text+='warm := DBPipeline(M);;samples := [];;\n'
        text+='for iteration in [1..'+str(repeats)+'] do\n'
        text+=' PrintTo('+quoted(folder/'progress.json')+',"{\\"case_index\\":'+str(i)+',\\"phase\\":\\"timed\\",\\"iteration\\":",iteration,"}\\n");\n'
        text+=' started := NanosecondsSinceEpoch();;outcome := DBPipeline(M);;elapsed := NanosecondsSinceEpoch()-started;;Add(samples,elapsed);\n'
        # Partial samples remain explicitly unverified until the full case and
        # independent certificate check complete. They are progress, not proof.
        text+=' PrintTo(Concatenation('+quoted(folder)+',"/sample-'+str(i)+'-",String(iteration),".json"),"{\\"sample_ns\\":",elapsed,"}\\n");\n'
        text+='od;\nDBCheckpointResult('+quoted(folder/f'case-{i:03d}.json')+','+quoted(fixture['id'])+',samples,outcome);\n'
        text+='M := fail;;warm := fail;;outcome := fail;;\n'
    return text+'QUIT;\n'


def main(argv=None):
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--gap-root',type=Path,required=True)
    parser.add_argument('--runtime-bin',type=Path)
    parser.add_argument('--repeats',type=int,default=5)
    parser.add_argument('--max-m',type=int,default=10)
    parser.add_argument('--cases',help='Comma-separated exact fixture IDs; all selected cases otherwise')
    parser.add_argument('--timeout',type=float,default=600,help='Overall process budget in seconds')
    parser.add_argument('--output',type=Path,default=Path(__file__).with_name('gap-streaming-results.json'))
    parser.add_argument('--checkpoint-dir',type=Path)
    parser.add_argument('--resume',action='store_true',help='Reuse independently validated completed cases with identical contract')
    parser.add_argument('--prepare-only',action='store_true',help='Write the GAP script and contract without launching any process')
    args=parser.parse_args(argv)
    if args.repeats<1 or not 7<=args.max_m<=10 or args.timeout<=0:
        parser.error('Require repeats>=1, max-m in7..10, timeout>0')
    try:fixtures=fixtures_for(args.max_m,[x.strip() for x in args.cases.split(',') if x.strip()] if args.cases else None)
    except ValueError as exc:parser.error(str(exc))
    folder=(args.checkpoint_dir or args.output.with_suffix('.checkpoints')).resolve()
    source_hashes={name:hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest() for name in ['gap_streaming.py','gap_pipeline.g']}
    contract={'repeats':args.repeats,'source_hashes':source_hashes,'fixture_hashes':{f['id']:hashlib.sha256(json.dumps(f['incidence'],separators=(',',':')).encode()).hexdigest() for f in fixtures}}
    if folder.exists() and any(folder.iterdir()):
        if not args.resume:parser.error('Checkpoint directory is nonempty; choose a new one or use --resume')
        if safe_json(folder/'contract.json')!=contract:parser.error('Checkpoint contract differs; preserve it and choose a new directory')
    folder.mkdir(parents=True,exist_ok=True);write_json(folder/'contract.json',contract)
    completed={}
    def collect():
        for i,fixture in enumerate(fixtures):
            if i in completed:continue
            case=safe_json(folder/f'case-{i:03d}.json')
            if case is not None:
                if case.get('id')!=fixture['id']:raise ValueError('Checkpoint fixture ID mismatch')
                completed[i]=case_record(fixture,case,args.repeats)
                print(f"COMPLETE {fixture['id']}: {completed[i]['median_ms']:.3f} ms {completed[i]['status']}",flush=True)
    collect()
    indices=[i for i in range(len(fixtures)) if i not in completed]
    script=folder/'run.g';script.write_text(script_for(fixtures,indices,folder,args.repeats),encoding='utf-8',newline='\n')
    if args.prepare_only:
        print(f'PREPARED {len(indices)} pending cases; no GAP process launched',flush=True);return 0
    exe=args.gap_root/'gap.exe'
    if not exe.is_file():parser.error('gap-root does not contain gap.exe')
    environment=os.environ.copy()
    if args.runtime_bin:environment['PATH']=str(args.runtime_bin)+os.pathsep+environment.get('PATH','')
    start=time.perf_counter();timed_out=False;last_progress=None
    process=None
    def report(status):
        partial={}
        for i,f in enumerate(fixtures):
            if i not in completed:
                values=[]
                for j in range(1,args.repeats+1):
                    sample=safe_json(folder/f'sample-{i}-{j}.json')
                    if sample is not None:values.append(sample['sample_ns']/1e6)
                if values:partial[f['id']]=values
        document={'status':status,'backend':safe_json(folder/'backend.json'),
          'methodology':{'repeats':args.repeats,'warmup':1,'clock':'GAP NanosecondsSinceEpoch','scope':'Preparsed GAP integer incidence -> actual DESIGN validation -> GF(2) coordinates -> reconstruction -> full exact certificate checks',
           'process_wall_seconds':time.perf_counter()-start,'timeout_seconds':args.timeout,'reconstruction':'Original adapter; not a claimed DESIGN built-in','checkpointing':'Closed per-case files preserve completed results on timeout; resume requires identical source/fixture contract'},
          'requested_cases':[f['id'] for f in fixtures],'cases':[completed[i] for i in sorted(completed)],
          'pending_cases':[f['id'] for i,f in enumerate(fixtures) if i not in completed],
          'partial_samples_unverified_ms':partial,'source_hashes':source_hashes}
        args.output.parent.mkdir(parents=True,exist_ok=True);write_json(args.output,document)
    try:
        with (folder/'stdout.log').open('w',encoding='utf-8') as stdout,(folder/'stderr.log').open('w',encoding='utf-8') as stderr:
            if indices:
                process=subprocess.Popen([str(exe),'-l',str(args.gap_root),'-A','-T','-q','-b','-r',str(script)],env=environment,stdout=stdout,stderr=stderr)
                while process.poll() is None:
                    collect()
                    progress=safe_json(folder/'progress.json')
                    if progress is not None and progress!=last_progress:
                        last_progress=progress
                        index=progress['case_index'];phase=progress['phase'];iteration=progress.get('iteration')
                        print(f"RUNNING {fixtures[index]['id']} {phase}"+(f' {iteration}/{args.repeats}' if iteration is not None else ''),flush=True)
                    report('RUNNING')
                    if time.perf_counter()-start>=args.timeout:
                        timed_out=True;process.terminate()
                        try:process.wait(timeout=5)
                        except subprocess.TimeoutExpired:process.kill();process.wait()
                        break
                    time.sleep(.25)
        collect()
        status='COMPLETE' if len(completed)==len(fixtures) else ('TIMEOUT' if timed_out else 'FAILED')
        report(status)
        print(f'{status}: {len(completed)}/{len(fixtures)} cases saved',flush=True)
        return 0 if status=='COMPLETE' else (124 if timed_out else 1)
    except BaseException:
        if process is not None and process.poll() is None:
            process.terminate()
            try:process.wait(timeout=5)
            except subprocess.TimeoutExpired:process.kill();process.wait()
        report('FAILED');raise

if __name__=='__main__':raise SystemExit(main())
