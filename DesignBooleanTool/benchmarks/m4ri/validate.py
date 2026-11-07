"""Exact rectangular and word-boundary checks for the actual M4RI wrapper."""
import argparse
import importlib.util
import json
from pathlib import Path
import random


def reference_rank(values):
    pivots={}
    for value in values:
        while value:
            lead=value.bit_length()-1
            if lead in pivots:value^=pivots[lead]
            else:pivots[lead]=value;break
    return len(pivots)


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--library',type=Path,required=True)
    p.add_argument('--output',type=Path)
    args=p.parse_args()
    source=Path(__file__).parents[1]/'m4ri_baseline.py'
    spec=importlib.util.spec_from_file_location('m4ri_benchmark_adapter',source)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    backend=module.M4RIRank(args.library);rng=random.Random(20261106);cases=0
    for rows in [0,1,2,7,8,16,31,64,65,127]:
        for cols in [0,1,2,7,8,16,31,63,64,65,129]:
            values=[rng.getrandbits(cols) for _ in range(rows)]
            assert backend.rank(values,cols)==reference_rank(values),(rows,cols)
            cases+=1
    result={'status':'PASS','cases':cases,'seed':20261106,'scope':'Exact rank comparisons including zero dimensions, rectangles and 64-bit boundaries'}
    text=json.dumps(result,indent=2)+'\n'
    if args.output:args.output.write_text(text,encoding='utf-8')
    print(text,end='')

if __name__=='__main__':main()
