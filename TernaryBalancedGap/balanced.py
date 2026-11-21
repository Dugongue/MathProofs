"""Signed comparison of concise balanced cores over the ternary field."""
from itertools import product


def orbit_rows(m, n, rows, left, ops):
    eliminate, matrices, multiply = ops
    slices = [[row[i:i+n] for i in range(0, m*n, n)] for row in rows]
    for g, bit in matrices(m if left else n):
        transformed = [sum(multiply(g, t) if left else multiply(t, g), [])
                       for t in slices]
        basis, _, minor = eliminate(transformed)
        yield tuple(bytes(row) for row in basis), bit, minor


def meet_profile(m, n, source, target, ops):
    # Equal transformed row spaces share their pivot columns.
    table = {}
    for key, p, minor in orbit_rows(m, n, source, True, ops):
        table.setdefault(key, set()).add((p, minor))
    found = set()
    for key, q, minor in orbit_rows(m, n, target, False, ops):
        for p, other in table.get(key, ()):
            found.add((p, q, other ^ minor))
        if len(found) == 8:
            break
    return found


def transpose(a):
    return [list(row) for row in zip(*a)]


def identity(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]


def matrix(v, n):
    return [v[i:i+n] for i in range(0, n*n, n)]


def centroid(shape, data, nullspace):
    # Equality of the three single-mode actions on tensor entries.
    strides = (shape[1]*shape[2], shape[2], 1)
    offsets = (0, shape[0]**2, shape[0]**2 + shape[1]**2)
    width = sum(n*n for n in shape)
    equations = []
    for idx, coord in enumerate(product(*(range(n) for n in shape))):
        for axis in (1, 2):
            row = [0]*width
            for mode, sign in ((0,1),(axis,-1)):
                n, i = shape[mode], coord[mode]
                for j in range(n):
                    row[offsets[mode] + n*i + j] = sign*data[idx+(j-i)*strides[mode]] % 3
            if any(row):
                equations.append(row)
    return [[matrix(v[start:start+n*n], n) for start, n in zip(offsets, shape)]
            for v in nullspace(equations, width)]


def eigenspaces(n, operators, multiply, nullspace):
    spaces = {(): identity(n)}
    for op in operators:
        refined = {}
        for key, basis in spaces.items():
            moved = multiply(basis, op)
            for lam in range(3):
                diff = [[(a-lam*b)%3 for a,b in zip(u,v)] for u,v in zip(moved,basis)]
                coeff = nullspace(transpose(diff), len(basis))
                if coeff:
                    refined[key+(lam,)] = multiply(coeff,basis)
        spaces = refined
    return spaces


def act(shape, data, axis, rows):
    stride = (shape[1]*shape[2],shape[2],1)[axis]
    out = []
    for pos in range(len(data)):
        i = pos // stride % shape[axis]
        out.append(sum(c*data[pos+(j-i)*stride] for j,c in enumerate(rows[i]))%3)
    return out


def factors(shape, data, eliminate, kernel, multiply):
    def nullspace(rows, n):
        return kernel(eliminate(rows), n) if rows else identity(n)

    basis = centroid(shape, data, nullspace)
    trivial = ([(tuple(shape), data)], (0,0,0), None)
    if len(basis) == 1:
        return trivial
    # Frobenius is linear in the commutative centroid. Mode 0 acts faithfully.
    diffs = []
    for triple in basis:
        a = triple[0]
        cube = multiply(multiply(a,a),a)
        diffs.append([(x-y)%3 for u,v in zip(cube,a) for x,y in zip(u,v)])
    fixed = nullspace(transpose(diffs),len(basis))
    if len(fixed) == 1:
        if shape[0] == shape[1] == shape[2] == len(basis):
            calibration = chain_frame(shape, data, basis, eliminate, multiply)
            return trivial[:2] + (calibration,)
        return trivial
    frames = []
    signs = []
    keys = None
    for axis,n in enumerate(shape):
        coordinates = [sum(t[axis],[]) for t in basis]
        operators = [matrix(v,n) for v in multiply(fixed,coordinates)]
        frame = eigenspaces(n,operators,multiply,nullspace)
        if keys is None:
            keys = sorted(frame)
        if set(keys) != set(frame):
            raise ArithmeticError("inconsistent centroid eigenspaces")
        rows = [v for label in keys for v in frame[label]]
        _, pivots, sign = eliminate(rows)
        if len(pivots) != n:
            raise ArithmeticError("singular centroid frame")
        data = act(shape,data,axis,rows)
        signs.append(sign)
        frames.append(frame)
    result = []
    starts = [0]*3
    for label in keys:
        dims = tuple(len(f[label]) for f in frames)
        ranges = [range(s,s+n) for s,n in zip(starts,dims)]
        part = [data[(i*shape[1]+j)*shape[2]+k] for i,j,k in product(*ranges)]
        result.append((dims,part))
        starts = [s+n for s,n in zip(starts,dims)]
    return result, tuple(signs), None


def add(a,b):
    return tuple(x^y for x,y in zip(a,b))


def merge(left, right, solve):
    parts, ls, _ = left
    targets, rs, _ = right
    if len(parts) != len(targets):
        return set()
    signs = {add(ls,rs)}
    used = []
    for shape,t in parts:
        repeat = False
        chosen = None
        for j,(dims,u) in enumerate(targets):
            if dims != shape:
                continue
            profile = solve(shape,t,u)
            if not profile:
                continue
            if j in used:
                repeat = True
            elif chosen is None:
                chosen, edge = j,profile
            if chosen is not None and repeat:
                break
        if chosen is None:
            return set()
        signs = {add(a,b) for a in signs for b in edge}
        if repeat:
            swap = tuple(n%2 for n in shape)
            signs |= {add(a,swap) for a in signs}
        # Stable block coordinates acquire a sign on every inverted block pair.
        inversion = tuple(sum(targets[j][0][k]*shape[k] for j in used if j>chosen)%2
                          for k in range(3))
        signs = {add(a,inversion) for a in signs}
        used.append(chosen)
    return signs


def chain_frame(shape, data, basis, eliminate, multiply):
    """Calibrate a tensor with centroid F3[t]/(t^d) to its standard frame."""
    d = shape[0]
    eye = identity(d)
    for triple in basis:
        for scalar in range(3):
            frames = []
            for op in triple:
                nil = [[(x-scalar*y)%3 for x,y in zip(a,b)] for a,b in zip(op,eye)]
                power = eye
                for _ in range(d-1):
                    power = multiply(power,nil)
                    if not any(map(any,power)):
                        break
                if not any(map(any,power)) or any(map(any,multiply(power,nil))):
                    break
                j = next(i for i,col in enumerate(zip(*power)) if any(col))
                v = [row[j] for row in eye]
                vectors = [v]
                for _ in range(d-1):
                    v = [sum(x*y for x,y in zip(row,v))%3 for row in nil]
                    vectors.append(v)
                frames.append(transpose(vectors))
            if len(frames) != 3:
                continue
            coords = data
            bits = []
            for axis, frame in enumerate(frames):
                augmented = [a+b for a,b in zip(frame,eye)]
                reduced, _, bit = eliminate(augmented)
                coords = act(shape,coords,axis,[row[d:] for row in reduced])
                bits.append(bit)
            constant = coords[d*d-1]  # entry (0,d-1,d-1)
            if not constant:
                raise ArithmeticError("nonconcise truncated-polynomial form")
            bits[0] ^= (d%2)*int(constant==2)
            return tuple(bits)
    return None


def chain_profile(d, left, right):
    calibration = add(left, right)
    result = set()
    for b,c,a in product(range(2),repeat=3):
        substitution_bit = (d*(d-1)//2 * a)%2
        units = tuple((d*i)%2 ^ substitution_bit for i in (b,c,b^c))
        result.add(add(calibration,units))
    return result
