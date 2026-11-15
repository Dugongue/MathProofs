"""Normalize the publisher's MatTen elasticity tensors and check crossed coverage.

This reads the actual decimal literals as rationals. The binary variants are
explicit reductions of a primitive integer representative. No value-threshold
or tolerance is part of either coverage test.
"""
from argparse import ArgumentParser
from collections import Counter, defaultdict
from decimal import Decimal
from hashlib import md5, sha256
from itertools import product
from math import gcd
from pathlib import Path
import json
from time import perf_counter

DOI = 'https://doi.org/10.5281/zenodo.8190849'
PUBLISHER_MD5 = '337c77550fbdb2b6c6d07b6f4e769920'
INDICES = tuple(product(range(3), repeat=4))
POINTS = tuple(product(range(3), repeat=2))


def primitive_integers(entries):
    scale = min((int(x.as_tuple().exponent) for x in entries), default=0)
    ints = [int(x.scaleb(-scale)) for x in entries]
    content = gcd(*ints)
    return [x // content for x in ints] if content else ints


def adj_and_factor(matrix):
    """Return p and p A^-1 by exact fraction-free Gauss–Jordan, or None."""
    n = len(matrix)
    a = [row[:] + [int(i == j) for j in range(n)] for i, row in enumerate(matrix)]
    old = 1
    for k in range(n):
        j = next((j for j in range(k, n) if a[j][k]), None)
        if j is None:
            return None
        a[j], a[k] = a[k], a[j]
        pivot = a[k][k]
        for i in range(n):
            if i == k:
                continue
            multiplier = a[i][k]
            a[i] = [0 if j == k else (pivot * a[i][j] - multiplier * a[k][j]) // old
                    for j in range(2*n)]
        old = pivot
    return old, [row[n:] for row in a]


def matmul(a, b):
    columns = list(zip(*b))
    return [[sum(u*v for u,v in zip(row,col)) for col in columns] for row in a]


def rank(a):
    a = [row[:] for row in a]
    lead = 0
    for j in range(len(a[0])):
        k = next((k for k in range(lead, len(a)) if a[k][j]), None)
        if k is None:
            continue
        a[lead], a[k] = a[k], a[lead]
        for i in range(lead+1, len(a)):
            if not a[i][j]:
                continue
            c,d = a[lead][j],a[i][j]
            divisor = gcd(c,d)
            a[i] = [(c//divisor)*u - (d//divisor)*v for u,v in zip(a[i],a[lead])]
            content = gcd(*a[i])
            if content > 1:
                a[i] = [v//content for v in a[i]]
        lead += 1
        if lead == 8:
            # Scalar matrices are always in the commutant. Eight is maximum.
            break
    return lead


def gamma(a):
    return [[a[3*i+l][3*k+j] for k,l in POINTS] for i,j in POINTS]


def trace_out(a, mode):
    if mode == 0:
        return [[sum(a[3*i+j][3*k+j] for j in range(3)) for k in range(3)] for i in range(3)]
    return [[sum(a[3*j+i][3*j+k] for j in range(3)) for k in range(3)] for i in range(3)]


def commute_equations(pair):
    return [[(a[b][j] if aidx==i else 0) - (a[i][aidx] if b==j else 0)
             for aidx,b in POINTS] for a in pair for i,j in POINTS]


def coverage_q(values):
    f = [values[9*i:9*i+9] for i in range(9)]
    if adj_and_factor(f) is None:
        return 'first-cut-singular'
    crossed = adj_and_factor(gamma(f))
    if crossed is None:
        return 'second-cut-singular'
    scale,crossed_adj = crossed
    jf = matmul(f,gamma(crossed_adj))
    for i in range(9):
        jf[i][i] -= scale
    jf2 = matmul(jf,jf)
    jf3 = matmul(jf2,jf)
    for mode in range(2):
        if rank(commute_equations([trace_out(jf2,mode),trace_out(jf3,mode)])) != 8:
            return 'non-scalar-commutant'
    return 'covered'


def xor_product(a, b):
    result = []
    for row in a:
        accum = 0
        while row:
            low = row & -row
            accum ^= b[low.bit_length()-1]
            row ^= low
        result.append(accum)
    return result


def bit_rows(a):
    return [sum((x&1)<<j for j,x in enumerate(row)) for row in a]


def invert_binary(f):
    a = [row | (1<<(9+i)) for i,row in enumerate(f)]
    for j in range(9):
        k = next((k for k in range(j,9) if a[k]>>j&1),None)
        if k is None:
            return None
        a[j],a[k] = a[k],a[j]
        for i in range(9):
            if i != j and a[i]>>j&1:
                a[i] ^= a[j]
    return [x>>9 for x in a]


def binary_rank(a):
    pivots = {}
    for row in a:
        while row:
            pivot = row.bit_length()-1
            if pivot not in pivots:
                pivots[pivot] = row
                break
            row ^= pivots[pivot]
    return len(pivots)


def square_rows(a):
    return [[row>>j&1 for j in range(9)] for row in a]


def coverage_2(values):
    f = bit_rows([values[9*i:9*i+9] for i in range(9)])
    if invert_binary(f) is None:
        return 'first-cut-singular'
    crossed = invert_binary(bit_rows(gamma(square_rows(f))))
    if crossed is None:
        return 'second-cut-singular'
    h = bit_rows(gamma(square_rows(crossed)))
    jf = [row^(1<<i) for i,row in enumerate(xor_product(f,h))]
    jf2 = xor_product(jf,jf)
    jf3 = xor_product(jf2,jf)
    for mode in range(2):
        equations = commute_equations([trace_out(square_rows(jf2),mode),
                                       trace_out(square_rows(jf3),mode)])
        if binary_rank(bit_rows(equations)) != 8:
            return 'non-scalar-commutant'
    return 'covered'


def emit_variant(dataset, ids, family, field, regrouped, out, scan):
    counts = defaultdict(Counter)
    input_count = 0
    scan_time = 0.0
    for key in ids:
        c = dataset['elastic_tensor'][key]
        symmetry = dataset['crystal_system'][key]
        native = [c[i][j][k][l] for i,j,k,l in INDICES]
        native = [x if isinstance(x,Decimal) else Decimal(x) for x in native]
        coefficients = [c[i][k][j][l] for i,j,k,l in INDICES] if regrouped else native
        coefficients = [x if isinstance(x,Decimal) else Decimal(x) for x in coefficients]
        ints = primitive_integers(coefficients)
        if scan:
            tick = perf_counter()
            state = (coverage_2 if field == 2 else coverage_q)(ints)
            scan_time += perf_counter()-tick
            counts[symmetry][state] += 1
        item = {'id': f'wen-elasticity-{key}', 'source': DOI, 'family': family,
                'field': field, 'dims': [3,3,3,3], 'crystal_system': symmetry,
                'publisher_row': key, 'axis_order': [0,2,1,3] if regrouped else [0,1,2,3]}
        if field == 2:
            item['ones'] = [point for point,x in zip(INDICES,ints) if x&1]
        else:
            item['entries'] = [str(x) for x in coefficients]
        out.write(json.dumps(item,separators=(',',':'))+'\n')
        input_count += 1
    totals = Counter()
    for c in counts.values():
        totals.update(c)
    return {'inputs': input_count, 'outcomes': dict(sorted(totals.items())),
            'by_crystal_system': {k:dict(sorted(v.items())) for k,v in sorted(counts.items())},
            'independent_coverage_seconds_excluding_load_and_serialization': scan_time}


def run():
    p = ArgumentParser(description=__doc__)
    p.add_argument('downloaded_json', type=Path)
    p.add_argument('output_dir', type=Path)
    p.add_argument('--limit', type=int, help='Use the first records in publisher order')
    p.add_argument('--no-scan', action='store_true')
    args = p.parse_args()
    raw = args.downloaded_json.read_bytes()
    if md5(raw).hexdigest() != PUBLISHER_MD5:
        raise SystemExit('Publisher MD5 mismatch')
    dataset = json.loads(raw,parse_float=Decimal)
    ids = sorted(dataset['elastic_tensor'], key=int)[:args.limit]
    assert len(dataset['elastic_tensor']) == 10276
    args.output_dir.mkdir(parents=True,exist_ok=True)
    result = {'source': DOI, 'license': 'CC BY 4.0', 'publisher_md5': PUBLISHER_MD5,
              'source_sha256': sha256(raw).hexdigest(), 'total_publisher_records': 10276,
              'variants': {}}
    for regrouped in [False,True]:
        for field in ['Q',2]:
            tag = ('regrouped' if regrouped else 'native') + ('-f2' if field==2 else '-q')
            family = 'wen-elasticity-'+tag
            path = args.output_dir/('data_elasticity_'+tag+'.jsonl')
            with path.open('w',encoding='utf-8',newline='\n') as f:
                result['variants'][tag] = emit_variant(dataset, ids, family, field, regrouped, f, not args.no_scan)
            result['variants'][tag]['normalized_sha256'] = sha256(path.read_bytes()).hexdigest()
            print(tag, result['variants'][tag]['outcomes'], flush=True)
    (args.output_dir/'data_elasticity_coverage.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')


if __name__ == '__main__':
    run()
