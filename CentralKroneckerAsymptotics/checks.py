"""Exact coefficient diagnostics; not a universal asymptotic proof."""
from collections import Counter
from itertools import combinations
from pathlib import Path
import hashlib
import json
import math
import time

ROOT = Path(__file__).resolve().parent
OUT = ROOT


def central_coefficients(m):
    r = m*m//2
    values = [1]+[0]*r
    for j in range(1, m+1):
        for k in range(j, r+1):
            values[k] += values[k-j]
        shift = m+j
        for k in range(r, shift-1, -1):
            values[k] -= values[k-shift]
    return values


def main():
    start = time.monotonic()
    small = []
    for m in range(1, 9):
        exact = central_coefficients(m)
        counts = Counter(sum(subset)-m*(m+1)//2 for subset in combinations(range(1,2*m+1),m))
        assert all(counts[k] == value for k,value in enumerate(exact))
        small.append({'m':m, 'subset_count':sum(counts.values()), 'checked_coefficients':len(exact)})
    rows = []
    for m in [2,3,4,5,10,11,20,21,40,41,80,81,160,161,240,241]:
        values = central_coefficients(m)
        g = values[-1]-values[-2]
        assert g >= 0
        leading = (3*math.sqrt(3)/math.pi)*(1+(m%2))*4.0**m/m**5
        rows.append({'m':m, 'g':str(g), 'leading_term':leading, 'ratio':g/leading})
    # The global tail estimate uses (24/23) sin(1) < 9/10.
    assert 24*math.sin(1)/23 < .9
    # Deterministic grid controls for the centered sine-square bounds.
    tested = 0
    for m in [4,5,8,16,32]:
        for ia in range(41):
            a = -math.pi+2*math.pi*ia/40
            for it in range(81):
                t = -math.pi+2*math.pi*it/80
                total = sum(math.sin((a+(j-(2*m+1)/2)*t)/2)**2 for j in range(1,2*m+1))
                if abs(t) <= 1/m:
                    lower = m**3*t*t/(2*math.pi**2)+2*m*math.cos(1)*a*a/math.pi**2
                else:
                    lower = m/10
                assert total+1e-10 >= lower, (m,a,t,total,lower)
                tested += 1
    result = {'kind':'EXACT_FINITE_CONTROLS_NOT_UNIVERSAL_PROOF', 'status':'PASS',
              'subset_bijection':small, 'asymptotic_diagnostics':rows,
              'tail_bound_grid_checks':tested, 'seconds':round(time.monotonic()-start,3),
              'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    (OUT/'CHECKS.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'status':'PASS','seconds':result['seconds'],'last_ratios':rows[-4:],'tail_checks':tested}))


if __name__ == '__main__':
    main()
