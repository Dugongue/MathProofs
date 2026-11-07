"""Reproducible design fixtures from cited Boolean functions.

Coordinates x1,...,xm use integer bits 0,...,m-1.  Matrices always
have point rows and block columns.  No third-party implementation is copied.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import random

PAPER = 'https://arxiv.org/html/2605.24355v1'


def parity(x: int) -> int:
    return x.bit_count() & 1


def walsh_transform(truth_table: list[int]) -> list[int]:
    """Integer Walsh transform in bit order, via the standard butterfly."""
    n = len(truth_table)
    if n < 1 or n & (n - 1) or any(x not in (0, 1) for x in truth_table):
        raise ValueError('truth_table must be a nonempty power-of-two bit list')
    out = [1 - 2*x for x in truth_table]
    step = 1
    while step < n:
        for base in range(0, n, 2*step):
            for j in range(base, base+step):
                u, v = out[j], out[j+step]
                out[j], out[j+step] = u+v, u-v
        step *= 2
    return out


def addition_design(truth_table: list[int]) -> dict:
    """Construct the paper's Walsh-support addition design from a plateaued f."""
    m = len(truth_table).bit_length()-1
    w = walsh_transform(truth_table)
    support = [i for i, value in enumerate(w) if value]
    amplitudes = {abs(w[i]) for i in support}
    if len(amplitudes) != 1:
        raise ValueError('function is not plateaued')
    amp = next(iter(amplitudes))
    if amp & (amp-1):
        raise ValueError('plateaued amplitude must be a power of two')
    r = 2*(amp.bit_length()-1)-m
    n = m-r
    if n < 4 or n % 2 or r < 0:
        raise ValueError('fixture constructor requires m-r even and at least four')
    piv = {}
    for a in support:
        value = a ^ support[0]
        while value:
            k = value.bit_length()-1
            if k in piv:
                value ^= piv[k]
            else:
                piv[k] = value
                break
    if len(piv) != m:
        raise ValueError('function has a nonzero linear structure; addition design is not simple')
    incidence = [[truth_table[b] ^ int(w[a] < 0) ^ parity(a & b)
                  for b in range(1 << m)] for a in support]
    n = m-r
    expected = {'recognized': True, 'm': m, 'r': r, 'points': len(support),
                'blocks': 1 << m, 'block_size': (1 << (n-1))-(1 << ((n-2)//2)),
                'lambda': (1 << (m-2))-(1 << ((m+r-2)//2)),
                'bordered_rank': m+2}
    return {'incidence': incidence, 'point_labels': support,
            'block_labels': list(range(1 << m)), 'expected': expected,
            'source_function': {'variables': m, 'truth_table': truth_table,
                                'walsh_support': support,
                                'walsh_amplitude': amp}}


def quadratic_bent(m: int) -> list[int]:
    if m < 4 or m % 2:
        raise ValueError('quadratic_bent requires even m >= 4')
    half = m//2
    return [parity((z & ((1 << half)-1)) & (z >> half)) for z in range(1 << m)]


def cubic_mm_bent(m: int) -> list[int]:
    """f(x,y)=dot(x,y)+y1*y2*y3; a cited M-M family instantiation."""
    if m < 6 or m % 2:
        raise ValueError('cubic_mm_bent requires even m >= 6')
    half = m//2
    return [parity((z & ((1 << half)-1)) & (z >> half)) ^
            int(((z >> half) & 7) == 7) for z in range(1 << m)]


def example2_plateaued(m: int = 5) -> list[int]:
    """Published Example 2 at m=5; at m>5 add disjoint quadratic pairs."""
    if m < 5 or m % 2 == 0:
        raise ValueError('example2_plateaued requires odd m >= 5')
    table = []
    for z in range(1 << m):
        b = [(z >> i) & 1 for i in range(m)]
        value = b[0]*b[2] ^ b[1]*b[3] ^ b[0]*b[1]*b[4]
        for i in range(5, m, 2):
            value ^= b[i]*b[i+1]
        table.append(value)
    return table


def permuted(fixture: dict, seed: int = 20261106) -> dict:
    """Relabel a fixture, preserving its exact design and source provenance."""
    rng = random.Random(seed)
    rows = list(range(len(fixture['incidence'])))
    cols = list(range(len(fixture['incidence'][0])))
    rng.shuffle(rows); rng.shuffle(cols)
    out = dict(fixture)
    out['incidence'] = [[fixture['incidence'][i][j] for j in cols] for i in rows]
    out['point_labels'] = [fixture['point_labels'][i] for i in rows]
    out['block_labels'] = [fixture['block_labels'][j] for j in cols]
    out['transformation'] = {'kind': 'point-and-block permutation', 'seed': seed,
                             'row_order': rows, 'column_order': cols}
    return out


def negative_sum_free() -> dict:
    """The proof's own simple 2-(64,28,24) rank-nine non-TSDP design."""
    pi = [1, 2, 4, 8, 15, 17, 18, 20]
    def xcoord(j0: int, j1: int) -> int:
        u = [(j1 >> i) & 1 for i in range(4)]
        rows = [[0,u[0],u[1],u[2],u[3]],
                [u[0],0,u[1],u[2],u[3]],
                [u[0],u[1],0,u[2],u[3]],
                [u[0],u[1],u[2],0,u[3]],
                [u[0]^u[1]^u[2],u[0],u[1],u[2],u[3]],
                [u[3],u[0],u[1],u[2],u[3]],
                [u[0],u[3],u[1],u[2],u[3]],
                [u[0],u[1],u[3],u[2],u[3]]]
        return sum(v << i for i,v in enumerate(rows[j0]))
    points = [(a,b) for a in range(8) for b in range(8)]
    blocks = [(a,b) for a in range(8) for b in range(16)]
    incidence = [[parity(pi[a] & xcoord(c,d)) ^ parity(b & (a ^ c))
                  for c,d in blocks] for a,b in points]
    return {'id': 'proof-counterexample-64x128', 'incidence': incidence,
            'point_labels': [list(p) for p in points],
            'block_labels': [list(b) for b in blocks],
            'expected': {'recognized': False, 'points': 64, 'blocks': 128,
                         'block_size': 28, 'lambda': 24, 'binary_rank': 9,
                         'm': 7, 'r': 1},
            'provenance': {'kind': 'project-proof-counterexample',
                'source': 'PlateauedAdditionDesigns_BorderedRankCharacterization.lean',
                'declarations': ['SumFreeCounterexample.counterexample',
                                 'SumFreeCounterexample.not_plateaued_addition_design'],
                'published_instance': False,
                'description': 'Own proof fixture; not attributed to the paper.'}}



def published_example4() -> dict:
    """Hyun et al. Example 4: a published non-addition design of rank 30."""
    def mul(a,b):
        ans=0
        while b:
            if b&1: ans^=a
            b>>=1; a<<=1
            if a&16: a^=0b10011
        return ans
    def power(a,n):
        ans=1
        while n:
            if n&1: ans=mul(ans,a)
            a=mul(a,a); n>>=1
        return ans
    def trace(a):
        ans=0; x=a
        for _ in range(4): ans^=x; x=mul(x,x)
        assert ans in (0,1)
        return ans
    g=[trace(mul(z&15,power(z>>4,14))) for z in range(256)]
    h=[trace(mul(2,mul(z&15,power(z>>4,14)))) for z in range(256)]
    matrix=[[g[b]^h[x^b]^g[x]^h[x] for b in range(256)] for x in range(256)]
    return {'id':'published-example-4-negative', 'incidence':matrix,
            'point_labels':list(range(256)), 'block_labels':list(range(256)),
            'expected':{'recognized':False,'m':8,'r':0,'points':256,'blocks':256,
                        'block_size':120,'lambda':56,'binary_rank':30},
            'provenance':{'kind':'exact-published-design-construction','paper':PAPER,
              'location':'Section VIII, Example 4 and Theorem 10',
              'formula':'g(x,y)=Tr(x*y^14); h(x,y)=Tr(alpha*x*y^14); M[x,b]=g(b)+h(x+b)+g(x)+h(x)',
              'field':'GF(16), alpha^4+alpha+1=0, alpha encoded by integer 2',
              'published_instance':True,
              'description':'Regenerated from the published finite-field formula; rank 30 is independently checked.'}}


def make_fixture(name: str, m: int | None = None) -> dict:
    if name == 'published-example-4':
        return published_example4()
    if name == 'published-example-1':
        out = addition_design(quadratic_bent(6))
        origin = {'kind': 'exact-published-function', 'paper': PAPER,
                  'location': 'Section IV-A, Example 1',
                  'formula': 'f(x1,x2,x3,y1,y2,y3)=x1*y1+x2*y2+x3*y3',
                  'published_instance': True,
                  'description': 'The incidence matrix is regenerated from the exact published function; its entries are not transcribed from a printed matrix.'}
    elif name == 'published-example-2':
        out = addition_design(example2_plateaued(5))
        origin = {'kind': 'exact-published-function', 'paper': PAPER,
                  'location': 'Section VI-A, Example 2',
                  'formula': 'f(x1,x2,x3,x4,x5)=x1*x3+x2*x4+x1*x2*x5',
                  'published_instance': True,
                  'description': 'The paper explicitly identifies this simple 2-(16,6,4) addition design. It cites Hodzic-Pasalic-Wei-Zhang (2019), Example 4.1 for the function.'}
    elif name == 'quadratic-family':
        m = 4 if m is None else m
        out = addition_design(quadratic_bent(m))
        origin = {'kind': 'published-family-instantiation', 'paper': PAPER,
                  'location': 'Section II-B, Maiorana-McFarland construction',
                  'formula': 'f(x,y)=dot(x,y)', 'published_instance': False,
                  'description': 'Generated family instance, not asserted to be an individually printed example.'}
    elif name == 'cubic-mm-family':
        m = 6 if m is None else m
        out = addition_design(cubic_mm_bent(m))
        origin = {'kind': 'published-family-instantiation', 'paper': PAPER,
                  'location': 'Section II-B, Maiorana-McFarland construction',
                  'formula': 'f(x,y)=dot(x,y)+y1*y2*y3', 'published_instance': False,
                  'description': 'Generated family instance, not asserted to be an individually printed example.'}
    elif name == 'plateaued-stabilization':
        m = 7 if m is None else m
        out = addition_design(example2_plateaued(m))
        origin = {'kind': 'derived-family-instantiation', 'paper': PAPER,
                  'location': 'Example 2 plus disjoint quadratic stabilization',
                  'formula': 'Example2(x1,...,x5)+x6*x7+x8*x9+...',
                  'published_instance': False,
                  'description': 'Our larger test instance obtained from the published five-variable example; not a claimed printed example.'}
    elif name == 'proof-counterexample':
        return negative_sum_free()
    else:
        raise ValueError('unknown fixture: '+name)
    out['id'] = name + (('-m'+str(m)) if m is not None else '')
    out['provenance'] = origin
    return out


def write_fixture(path: Path, fixture: dict) -> str:
    path.write_text(json.dumps(fixture,indent=2)+'\n',encoding='utf-8',newline='\n')
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir',type=Path,default=Path(__file__).resolve().parent)
    parser.add_argument('--include-large',action='store_true',help='also materialize m=8,9 test designs')
    args = parser.parse_args()
    args.output_dir.mkdir(parents=True,exist_ok=True)
    specs = [('published-example-1',None),('published-example-2',None),
             ('quadratic-family',4),('cubic-mm-family',6),
             ('plateaued-stabilization',7),('proof-counterexample',None),
             ('published-example-4',None)]
    if args.include_large:
        specs += [('quadratic-family',8),('cubic-mm-family',8),('plateaued-stabilization',9)]
    records = []
    for name,m in specs:
        fixture = make_fixture(name,m)
        filename = fixture['id']+'.json'
        sha = write_fixture(args.output_dir/filename,fixture)
        records.append({'file':filename,'sha256':sha,'expected':fixture['expected'],
                        'provenance':fixture['provenance']})
        if name == 'published-example-2':
            shuffled = permuted(fixture)
            shuffled['id'] += '-permuted'
            filename = shuffled['id']+'.json'
            sha = write_fixture(args.output_dir/filename,shuffled)
            records.append({'file':filename,'sha256':sha,'expected':shuffled['expected'],
                            'provenance':shuffled['provenance']})
    (args.output_dir/'manifest.json').write_text(json.dumps({'schema':1,'fixtures':records},indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({'fixtures':len(records),'files':[r['file'] for r in records]}))

if __name__ == '__main__':
    main()
