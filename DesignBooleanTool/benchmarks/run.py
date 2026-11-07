"""Reproducible full-pipeline comparison; fixture parsing is outside timings."""
import argparse
import gc
import json
import os
from pathlib import Path
import platform
import statistics
import sys
import time

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'src'))
sys.path.insert(0,str(Path(__file__).resolve().parent))
sys.path.insert(0,str(ROOT/'examples'))
from design_boolean.core import _recognize_python as fast_recognize
from generate import make_fixture
from reference import recognize as reference_recognize, normalized_columns, closure_decision, rank_decision, verify


def timed(fn,repeats):
    samples=[];result=None
    fn() # untimed warmup
    for _ in range(repeats):
        gc.collect()
        start=time.perf_counter_ns();result=fn();samples.append((time.perf_counter_ns()-start)/1e6)
    return {'median_ms':statistics.median(samples),'minimum_ms':min(samples),'samples_ms':samples},result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repeats',type=int,default=5)
    parser.add_argument('--max-m',type=int,default=9,help='generated stress cases through this variable count (4..10)')
    parser.add_argument('--sympy-path',type=Path,help='optional existing dependency directory containing SymPy; not recorded in results')
    parser.add_argument('--output',type=Path,default=Path(__file__).with_name('results.json'))
    args=parser.parse_args()
    if args.repeats<1 or not 4<=args.max_m<=10:parser.error('repeats>=1 and 4<=max-m<=10 required')
    manifest=json.loads((ROOT/'examples/manifest.json').read_text(encoding='utf-8'))
    fixtures=[json.loads((ROOT/'examples'/entry['file']).read_text(encoding='utf-8')) for entry in manifest['fixtures']]
    for m in range(8,args.max_m+1):
        name='quadratic-family' if m%2==0 else 'plateaued-stabilization'
        fixture=make_fixture(name,m)
        fixture['id']='stress-'+fixture['id'];fixtures.append(fixture)
    if args.sympy_path:
        sys.path.insert(0,str(args.sympy_path))
    try:
        import sympy
        from sympy.polys.matrices import DomainMatrix
        from sympy import GF
        def sympy_decision(values,m):
            # Dimension must come from the current packed vectors, retaining
            # zero trailing rows is immaterial for rank.
            rows=[[(value>>i)&1 for value in values] for i in range(max(values,default=0).bit_length())]
            return DomainMatrix.from_list(rows,GF(2)).rank()==m
        sympy_version=sympy.__version__
    except ImportError:
        sympy_decision=None;sympy_version=None
    records=[]
    for fixture in fixtures:
        matrix=fixture['incidence'];v=len(matrix);b=len(matrix[0]);m=b.bit_length()-1
        ours,result=timed(lambda:fast_recognize(matrix),args.repeats)
        baseline,reference=timed(lambda:reference_recognize(matrix),args.repeats)
        rank_baseline,rank_reference=timed(lambda:reference_recognize(matrix,decision='rank'),args.repeats)
        sympy_baseline=sympy_reference=None
        if sympy_decision:
            sympy_baseline,sympy_reference=timed(lambda:reference_recognize(matrix,decision=sympy_decision),args.repeats)
        status=result.status
        if status!=reference['status'] or status!=rank_reference['status'] or (sympy_reference is not None and status!=sympy_reference['status']):raise AssertionError((fixture['id'],status,reference['status']))
        if status=='recognized':
            if not verify(matrix,result.certificate) or not verify(matrix,reference['certificate']):raise AssertionError('independent certificate verification failed')
        values=normalized_columns(matrix)
        rank_phase,rank_result=timed(lambda:rank_decision(values,m),args.repeats)
        closure_phase,closure_result=timed(lambda:closure_decision(values),args.repeats)
        if rank_result!=closure_result and len(set(values))==b:raise AssertionError('decision disagreement')
        rec={'id':fixture['id'],'points':v,'blocks':b,'status':status,'provenance':fixture['provenance']['kind'],
             'optimized_end_to_end':ours,'normalized_tsdp_reference_end_to_end':baseline,
             'same_pipeline_rank_ablation_end_to_end':rank_baseline,
             'sympy_gf2_rank_reference_end_to_end':sympy_baseline,
             'closure_over_rank_ablation_speed_ratio':baseline['median_ms']/rank_baseline['median_ms'],
             'end_to_end_speed_ratio_reference_over_optimized':baseline['median_ms']/ours['median_ms'],
             'rank_decision_only':rank_phase,'closure_decision_only':closure_phase}
        records.append(rec)
        print(f"{fixture['id']}: {v}x{b} {status}; ours {ours['median_ms']:.3f} ms, TSDP {baseline['median_ms']:.3f} ms, rankablation {rank_baseline['median_ms']:.3f} ms; TSDP/ours {rec['end_to_end_speed_ratio_reference_over_optimized']:.2f}, TSDP/rank {rec['closure_over_rank_ablation_speed_ratio']:.2f}",flush=True)
    out={'schema':1,'environment':{'python':platform.python_version(),'implementation':platform.python_implementation(),'platform':platform.system(),'machine':platform.machine(),'processor':platform.processor(),'logical_cpus':os.cpu_count(),'sympy_version':sympy_version},
         'methodology':{'repeats':args.repeats,'timer':'perf_counter_ns','summary':'median after one untimed warmup; gc.collect before each sample','timed_scope':'parsed dense incidence through exact design validation, decision, reconstruction, and certificate check; no input JSON loading',
                        'baseline':'independent standard-library normalized TSDP pair-closure implementation with full reconstruction and exact Walsh/incidence verification; not Sage timing',
                        'rank_ablation':'identical reference pipeline changing only closure decision to packed GF2 rank saturation; isolates decision-rule benefit from other implementation differences',
                        'sympy_baseline':'if available, identical reference pipeline using actual SymPy DomainMatrix GF(2) rank, including conversion cost; no Sage timing claimed',
                        'phase_scope':'normalized columns precomputed for both decision-only phases; no validation/reconstruction included',
                        'limits':'single-machine in-process benchmark; generated stress instances are not individually published examples'},'cases':records}
    args.output.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8',newline='\n')


if __name__=='__main__':main()
