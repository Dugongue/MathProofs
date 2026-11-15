"""Fraction-free version of the rational crossed-flattening pipeline."""

import argparse
from dataclasses import dataclass
from fractions import Fraction
import json
from math import gcd, lcm, prod
from pathlib import Path
from time import perf_counter

import crossed
from data_elasticity import adj_and_factor
from baseline_external import rational_reconstruct


def integer_forward(equations, width):
    def primitive(row):
        content = gcd(*row)
        return [x // content for x in row] if content > 1 else row
    a = [primitive(row[:]) for row in equations]
    pivots = []
    for j in range(width):
        i = len(pivots)
        k = next((k for k in range(i,len(a)) if a[k][j]),None)
        if k is None:
            continue
        a[i],a[k] = a[k],a[i]
        pivots.append(j)
        for k in range(i+1,len(a)):
            if not a[k][j]:
                continue
            h = gcd(a[i][j],a[k][j])
            c,d = a[i][j]//h, a[k][j]//h
            a[k] = primitive([c*x-d*y for x,y in zip(a[k],a[i])])
        if i+1 == len(a):
            break
    return a, pivots


def integer_nullspace(equations, width):
    a, pivots = integer_forward(equations,width)
    basis = []
    for free in (j for j in range(width) if j not in pivots):
        v = [0]*width
        v[free] = 1
        for i,pivot in reversed(list(enumerate(pivots))):
            v[pivot] = Fraction(-sum(a[i][k]*v[k] for k in range(pivot+1,width)), a[i][pivot])
        basis.append(v)
    return basis


def common_integers(xs):
    den = lcm(*(x.denominator for x in xs))
    ys = [int(x * den) for x in xs]
    content = gcd(*ys)
    return ([x//content for x in ys], Fraction(content,den)) if content else (ys, Fraction(1))


def certified_rank(equations, width, maximal):
    """A modular maximal minor certifies the rational rank."""
    prime = 65521
    _, pivots = crossed.reduce_rows([[x % prime for x in row] for row in equations], width, prime)
    if len(pivots) == maximal:
        return maximal
    return len(integer_forward(equations, width)[1])


def certified_nullspace(equations, width):
    """Use small modular images, validating every reconstructed coordinate."""
    for prime in (65521, 65519, 65497):
        form, pivots = crossed.reduce_rows(
            [[x % prime for x in row] for row in equations], width, prime)
        if len(pivots) == width:
            return []
        if len(pivots) != width-1:
            continue
        free = next(i for i in range(width) if i not in pivots)
        v = [None]*width
        v[free] = Fraction(1)
        for i, p in enumerate(pivots):
            v[p] = rational_reconstruct(-form[i][free] % prime, prime)
        if any(x is None for x in v):
            continue
        if all(sum(x*y for x,y in zip(row,v)) == 0 for row in equations):
            return [v]
    return integer_nullspace(equations, width)

@dataclass
class Profile:
    ranks: tuple
    commutants: tuple | None = None
    covariants: tuple | None = None
    denominator: int | None = None
    inverse: tuple | None = None

    @property
    def supported(self):
        return self.commutants == (1,1)


def profile(data, sizes):
    side = prod(sizes)
    values, global_scale = common_integers(data)
    a = crossed.rows(values,side)
    gamma = crossed.crossing(a,*sizes)
    ia, ig = adj_and_factor(a), adj_and_factor(gamma)
    ranks = tuple(side if det else len(integer_forward(entries,side)[1])
                  for det, entries in ((ia,a),(ig,gamma)))
    if ia is None or ig is None:
        return Profile(ranks)
    d, invgamma = ig
    v = crossed.matmul(a,crossed.crossing(invgamma,*sizes),None)
    for i in range(side):
        v[i][i] -= d
    content = gcd(d,*crossed.flatten(v))
    if content > 1:
        d //= content
        v = [[x//content for x in row] for row in v]
    square = crossed.matmul(v,v,None)
    cube = crossed.matmul(square,v,None)
    covars = tuple(zip(crossed.partial_traces(square,*sizes,None),
                       crossed.partial_traces(cube,*sizes,None)))
    comm = tuple(n*n-certified_rank(crossed.intertwiner_system(pair,pair,None),
                                     n*n,n*n-1)
                 for pair,n in zip(covars,sizes))
    inv = ia[1], 1/(ia[0]*global_scale)
    return Profile(ranks,comm,covars,d,inv)


def cross_system(a,b,n,da,db):
    equations = []
    for r,left,right in zip((2,3),a,b):
        src = db ** r
        dst = da ** r
        h = gcd(src,dst)
        left = [[[x*(src//h) for x in row] for row in left]]
        right = [[[x*(dst//h) for x in row] for row in right]]
        equations.extend(crossed.intertwiner_system(left,right,None))
    return equations


def integer_matrix(a):
    flat, scale = common_integers(crossed.flatten(a))
    return crossed.rows(flat,len(a[0])), scale


def verify_integer(source, target, sizes, witness):
    src, source_scale = common_integers(source)
    dst, target_scale = common_integers(target)
    maps = []
    for matrix in witness:
        a, scale = integer_matrix(matrix)
        if adj_and_factor(a) is None:
            return False
        maps.append(a)
        source_scale *= scale
    values = crossed.apply(src,sizes,maps,None)
    ratio = source_scale / target_scale
    return all(x*ratio.numerator == y*ratio.denominator for x,y in zip(values,dst))

def solve(pair):
    sizes = tuple(pair["dims"][:2])
    if pair["field"]!="Q":
        return crossed.solve(pair)
    if len(pair["dims"]) != 4 or tuple(pair["dims"][2:]) != sizes or min(sizes)<2:
        return {"status":"unknown","reason":"unsupported format"}
    source,target = (crossed.parse("Q",pair[key]) for key in ("src","dst"))
    a,b = profile(source,sizes),profile(target,sizes)
    out = dict(ranks=[a.ranks,b.ranks],commutants=[a.commutants,b.commutants])
    if a.ranks!=b.ranks or a.commutants!=b.commutants:
        return dict(out,status="no",reason="invariant mismatch")
    if not (a.supported and b.supported):
        return dict(out,status="unknown",reason="outside scalar-commutant class")
    factors = []
    for left,right,n in zip(a.covariants,b.covariants,sizes):
        equations = cross_system(left,right,n,a.denominator,b.denominator)
        basis = certified_nullspace(equations,n*n)
        if len(basis) != 1:
            return dict(out,status="no",reason="local intertwiners")
        g = crossed.rows(basis[0],n)
        ig = crossed.inverse_and_rank(g,None)[0]
        if ig is None:
            return dict(out,status="no",reason="singular local intertwiner")
        factors.append((g,ig))
    g0,g1 = [g for g,_ in factors]
    (u,su),(v,sv) = [integer_matrix(ig) for _,ig in factors]
    inv01 = crossed.kronecker(u,v,None)
    dst, sd = common_integers(target)
    inverse_src, si = a.inverse
    right = crossed.transpose(crossed.matmul(
        crossed.matmul(inverse_src,inv01,None),crossed.rows(dst,prod(sizes)),None))
    tail = crossed.factor_kronecker(right,sizes,None)
    if tail is None:
        return dict(out,status="no",reason="right Kronecker test")
    scale = si*su*sv*sd
    witness = [g0,g1,tail[0],[[scale*x for x in row] for row in tail[1]]]
    if not verify_integer(source,target,sizes,witness):
        raise ArithmeticError("fraction-free witness did not verify")
    return dict(out,status="yes",reason="verified",witness=witness)


if __name__=="__main__":
    cli=argparse.ArgumentParser(description=__doc__)
    cli.add_argument("pair",type=Path)
    args=cli.parse_args()
    begin=perf_counter()
    pair=json.loads(args.pair.read_text(encoding="utf-8-sig"))
    report=solve(pair)
    print(json.dumps(dict(report,elapsed_seconds=perf_counter()-begin),default=str))
