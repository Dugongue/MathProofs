"""Same-input full-pipeline comparisons against actual available backends.

External Sage and GAP reports use native in-process timers; process startup and
input parsing are excluded for every primary measurement. Paths are not recorded.
"""
import argparse
import gc
import hashlib
import json
from pathlib import Path
import platform
import statistics
import sys
import time
ROOT=Path(__file__).resolve().parents[1]
sys.path[:0]=[str(ROOT/'src'),str(ROOT/'examples'),str(Path(__file__).resolve().parent)]
from design_boolean import recognize
from design_boolean import native
from generate import make_fixture
from reference import recognize as reference_recognize, verify

def corpus():
    manifest=json.loads((ROOT/'examples/manifest.json').read_text())
    out=[]
    for entry in manifest['fixtures']:
        data=json.loads((ROOT/'examples'/entry['file']).read_text())
        out.append({'id':data['id'],'incidence':data['incidence'],'expected_status':'recognized' if entry['expected']['recognized'] else 'not_recognized','provenance':data['provenance']['kind']})
    for m in range(8,11):
        data=make_fixture('quadratic-family' if m%2==0 else 'plateaued-stabilization',m)
        out.append({'id':'stress-'+data['id'],'incidence':data['incidence'],'expected_status':'recognized','provenance':data['provenance']['kind']})
    return {'schema':1,'cases':out}

def samples(fn,repeats):
    fn()
    times=[]
    for _ in range(repeats):
        gc.collect();started=time.perf_counter_ns();result=fn();times.append((time.perf_counter_ns()-started)/1e6)
    return {'median_ms':statistics.median(times),'minimum_ms':min(times),'samples_ms':times},result

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--corpus-only',type=Path)
    p.add_argument('--repeats',type=int,default=5)
    p.add_argument('--m4ri-library',type=Path)
    p.add_argument('--output',type=Path,default=Path(__file__).with_name('comparison-results.json'))
    a=p.parse_args()
    if a.repeats<1:p.error('repeats must be positive')
    data=corpus()
    if a.corpus_only:
        a.corpus_only.write_text(json.dumps(data,separators=(',',':'))+'\n',encoding='utf-8',newline='\n');print('Wrote',len(data['cases']),'cases.');return
    if not native.available():raise RuntimeError('Explicitly build the native library before performance comparisons.')
    methods={'native_certificate':lambda mat:recognize(mat,backend='native'),
             'native_explicit':lambda mat:native.recognize_native(mat,validation='explicit'),
             'python_explicit':lambda mat:recognize(mat,backend='python')}
    if a.m4ri_library:
        from m4ri_baseline import M4RIRank
        rank=M4RIRank(a.m4ri_library)
        methods['m4ri_reference']=lambda mat:reference_recognize(mat,decision=rank)
    records=[]
    for case in data['cases']:
        matrix=case['incidence'];measurements={}
        for name,method in methods.items():
            measured,result=samples(lambda:method(matrix),a.repeats)
            status=result['status'] if isinstance(result,dict) else result.status
            certificate=result.get('certificate') if isinstance(result,dict) else result.certificate
            assert status==case['expected_status'],(case['id'],name,status)
            if status=='recognized':assert verify(matrix,certificate),(case['id'],name)
            measurements[name]=measured
        item={k:v for k,v in case.items() if k!='incidence'}
        item.update(points=len(matrix),blocks=len(matrix[0]),incidence_sha256=hashlib.sha256(json.dumps(matrix,separators=(',',':')).encode()).hexdigest(),measurements=measurements)
        records.append(item)
        print(case['id'],{k:round(v['median_ms'],4) for k,v in measurements.items()},flush=True)
    sources=['src/design_boolean/core.py','src/design_boolean/native.py','native/design_boolean.cpp','benchmarks/reference.py','benchmarks/compare_backends.py']
    report={'schema':1,'environment':{'python':platform.python_version(),'system':platform.system(),'machine':platform.machine()},
            'methodology':{'repeats':a.repeats,'warmups':1,'input':'Same preparsed dense integer incidence lists','scope':'Validation, coordinate recovery, full truth table and exact realization checks; all conversion and certificate construction included; JSON parsing and startup excluded','native_validation':'certificate-first proof or explicit block/pair counts, respectively','m4ri_reference':'Actual supplied M4RI DLL rank with independent Python full-pipeline adapter; not a complete Sage runtime','scheduling':'Run serialized with external backends after runtime extraction finishes','limitations':'Single host; fixed generated and published corpus; no universal speed claim'},'source_hashes':{s:hashlib.sha256((ROOT/s).read_bytes()).hexdigest() for s in sources},'cases':records}
    a.output.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
if __name__=='__main__':main()
