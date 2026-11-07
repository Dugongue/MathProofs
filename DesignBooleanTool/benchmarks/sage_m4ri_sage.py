"""Run complete recognition/reconstruction using actual SageMath native matrices.

Run with `sage -python benchmarks/sage_m4ri_sage.py --corpus CORPUS.json`.
Python 3.7-compatible for the archived native Windows SageMath 9.3 runtime.
No design_boolean implementation is imported in this comparator.
"""
import argparse
import gc
import json
from pathlib import Path
import platform
import statistics
import time
from sage.all import GF, ZZ, matrix, IncidenceStructure, version
from sage.crypto.boolean_function import BooleanFunction

F2=GF(2)
NONBINARY_TABLE=bytes([0,0]+[1]*254)

def recognize(rows, validation='spectral'):
    if not rows or not rows[0]:return {'status':'invalid_input'}
    v,b=len(rows),len(rows[0])
    if any(len(row)!=b for row in rows):return {'status':'invalid_input'}
    try:
        raw=b''.join(bytes(row) for row in rows)
    except (TypeError,ValueError,OverflowError):return {'status':'invalid_input'}
    if raw.translate(NONBINARY_TABLE).count(b'\x01'):
        return {'status':'invalid_input'}
    if v&(v-1) or b&(b-1):return {'status':'unsupported'}
    n,m=v.bit_length()-1,b.bit_length()-1
    if n<4 or n%2 or m<n:return {'status':'unsupported'}
    q=1<<(n//2-1);k=q*(2*q-1);lam=(1<<(m-n))*q*(q-1);amplitude=1<<(m-n//2)
    if validation=='incidence':
        blocks=[[i for i in range(v) if rows[i][j]] for j in range(b)]
        if len(set(map(tuple,blocks)))!=b:return {'status':'not_recognized'}
        design=IncidenceStructure(v,blocks)
        if not design.is_t_design(2,v,k,lam):return {'status':'not_recognized'}
    M=matrix(F2,v,b,raw)
    if validation=='gram':
        ints=matrix(ZZ,rows)
        if any(sum(ints.column(j))!=k for j in range(b)):return {'status':'not_recognized'}
        if len(set(tuple(row) for row in M.transpose().rows()))!=b:return {'status':'not_recognized'}
        gram=ints*ints.transpose()
        if any(gram[i,j]!=lam for i in range(v) for j in range(i)):return {'status':'not_recognized'}
    onesv=matrix(F2,v,1,[1]*v);onesb=matrix(F2,1,b,[1]*b)
    N=M+M.matrix_from_columns([0])*onesb+onesv*M.matrix_from_rows([0])+M[0,0]*(onesv*onesb)
    # Sage dense GF(2) matrices use their actual M4RI implementation.
    pivots=N.pivots()
    if len(pivots)!=m:return {'status':'not_recognized'}
    B=N.matrix_from_columns(pivots)
    rowpivots=B.transpose().pivots()
    X=B.matrix_from_rows(rowpivots).solve_right(N.matrix_from_rows(rowpivots))
    beta=[sum(int(X[i,j])<<i for i in range(m)) for j in range(b)]
    if set(beta)!=set(range(b)):return {'status':'not_recognized'}
    phi=[sum(int(B[p,i])<<i for i in range(m)) for p in range(v)]
    if len(set(phi))!=v:return {'status':'not_recognized'}
    truth=[0]*b
    for j,x in enumerate(beta):truth[x]=rows[0][j]
    offsets=[rows[p][0]^rows[0][0] for p in range(v)]
    walsh=[int(x) for x in BooleanFunction(truth).walsh_hadamard_transform()]
    if any(x not in (0,amplitude,-amplitude) for x in walsh):return {'status':'not_recognized'}
    if {u for u,x in enumerate(walsh) if x}!=set(phi):return {'status':'not_recognized'}
    if any(walsh[u]!=amplitude*(1-2*g) for u,g in zip(phi,offsets)):return {'status':'not_recognized'}
    function_row=matrix(F2,1,b,[truth[x] for x in beta])
    if B*X+onesv*function_row+matrix(F2,v,1,offsets)*onesb!=M:return {'status':'not_recognized'}
    affine=B+onesv*B.matrix_from_rows([0])
    if affine.rank()!=m:return {'status':'not_recognized'}
    cert={'truth_table':truth,'block_coordinates':beta,'point_frequencies':phi,'point_offsets':offsets,'amplitude':amplitude}
    return {'status':'recognized','certificate':cert}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--corpus',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--repeats',type=int,default=5)
    p.add_argument('--validation',choices=['spectral','incidence','gram'],default='spectral')
    args=p.parse_args()
    corpus=json.loads(args.corpus.read_text(encoding='utf-8'))
    results=[]
    for case in corpus['cases']:
        rows=case['incidence'];recognize(rows,args.validation);samples=[];answer=None
        for _ in range(args.repeats):
            gc.collect();start=time.perf_counter_ns();answer=recognize(rows,args.validation)
            samples.append((time.perf_counter_ns()-start)/1e6)
        if answer['status']!=case['expected_status']:
            raise AssertionError((case['id'],answer['status'],case['expected_status']))
        rec={'id':case['id'],'points':len(rows),'blocks':len(rows[0]),'status':answer['status'],
             'median_ms':statistics.median(samples),'samples_ms':samples,'certificate':answer.get('certificate')}
        results.append(rec)
        print(case['id'],answer['status'],round(rec['median_ms'],4),'ms',flush=True)
    output={'backend':'Actual SageMath native dense GF(2)/M4RI and BooleanFunction','sage_version':version(),
       'python':platform.python_version(),'platform':platform.system(),'machine':platform.machine(),
       'validation':args.validation,'repeats':args.repeats,'cases':results,
       'methodology':'Full dense-input parsing validation, optional design validation, native GF2 basis/coordinates, Sage Walsh transform, full incidence and affine-support check. Corpus JSON loading and interpreter startup excluded.',
       'scope':'spectral mode proves the design axioms from the full spectral-incidence certificate; incidence mode additionally calls IncidenceStructure.is_t_design; gram mode additionally checks exact integer incidence Gram matrix.'}
    args.output.write_bytes((json.dumps(output,indent=2)+'\n').encode('utf-8'))

if __name__=='__main__':main()
