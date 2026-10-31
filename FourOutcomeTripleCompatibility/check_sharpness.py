"""Independent exact Gaussian-integer audit of the dimension-8 sharpness witness.

All stored matrices represent four times their physical operator. No numerical
linear algebra, symbolic algebra package, floating-point test, or Lean is used.
"""
if not __debug__:raise RuntimeError("Do not use Python optimization flags.")
import hashlib
import json
from pathlib import Path
from datetime import datetime, timezone

Z = (0, 0)
O = (1, 0)

def gadd(a, b):
    return (a[0] + b[0], a[1] + b[1])

def gmul(a, b):
    return (a[0]*b[0] - a[1]*b[1], a[0]*b[1] + a[1]*b[0])

def gconj(a):
    return (a[0], -a[1])

def zero(n):
    return tuple(tuple(Z for _ in range(n)) for _ in range(n))

def ident(n):
    return tuple(tuple(O if i == j else Z for j in range(n)) for i in range(n))

def add(A, B):
    return tuple(tuple(gadd(a, b) for a, b in zip(ra, rb)) for ra, rb in zip(A, B))

def scale(k, A):
    return tuple(tuple((k*a[0], k*a[1]) for a in row) for row in A)

def adj(A):
    return tuple(tuple(gconj(A[j][i]) for j in range(len(A))) for i in range(len(A)))

def mul(A, B):
    n = len(A)
    C = [[Z for _ in range(n)] for _ in range(n)]
    for i in range(n):
        for k in range(n):
            a = A[i][k]
            if a == Z:
                continue
            for j in range(n):
                b = B[k][j]
                if b != Z:
                    C[i][j] = gadd(C[i][j], gmul(a, b))
    return tuple(tuple(row) for row in C)

def trace(A):
    re = sum(A[i][i][0] for i in range(len(A)))
    im = sum(A[i][i][1] for i in range(len(A)))
    assert im == 0
    return re

def sum_matrices(mats):
    out = zero(len(mats[0]))
    for A in mats:
        out = add(out, A)
    return out

def block_matrix(block):
    return tuple(tuple(block(i//2, j//2)[i%2][j%2] for j in range(8)) for i in range(8))

H = ((1,1,1,1), (1,-1,1,-1), (1,1,-1,-1), (1,-1,-1,1))
assert all(sum(H[a][b]*H[c][b] for b in range(4)) == 4*(a == c) for a in range(4) for c in range(4))
I2 = ident(2)
E = (I2, (((0,0),(0,1)),((0,1),(0,0))), (((0,0),(-1,0)),((1,0),(0,0))), (((0,1),(0,0)),((0,0),(0,-1))))
assert all(mul(e, adj(e)) == I2 and mul(adj(e), e) == I2 for e in E)
P = tuple(block_matrix(lambda a, b, j=j: scale(4, I2) if a == b == j else zero(2)) for j in range(4))
Q = tuple(block_matrix(lambda a, b, j=j: scale(H[a][j]*H[b][j], I2)) for j in range(4))
R = tuple(block_matrix(lambda a, b, j=j: scale(H[a][j]*H[b][j], mul(E[a], adj(E[b])))) for j in range(4))
I8 = ident(8)
Z8 = zero(8)
checks = {"hadamard_row_inner_products": 16, "unitary_two_sided_checks": 8, "self_adjoint": 0, "projectivity": 0, "orthogonality_ordered": 0, "completeness": 0, "rank_two_trace": 0, "selected_sum_polynomial": 0, "selected_sum_characteristic_polynomial": 0}
for family in (P, Q, R):
    for i, A in enumerate(family):
        assert adj(A) == A
        checks["self_adjoint"] += 1
        assert mul(A, A) == scale(4, A)
        checks["projectivity"] += 1
        assert trace(A) == 8
        checks["rank_two_trace"] += 1
        for j, B in enumerate(family):
            if i != j:
                assert mul(A, B) == Z8
                checks["orthogonality_ordered"] += 1
    assert sum_matrices(family) == scale(4, I8)
    checks["completeness"] += 1

expected_char = [1, -24, 216, -912, 1872, -1728, 576, 0, 0]
for a in range(4):
    for b in range(4):
        for c in range(4):
            T = add(add(P[a], Q[b]), R[c])
            assert adj(T) == T
            powers = [I8]
            for _ in range(8):
                powers.append(mul(powers[-1], T))
            # T=4S: T^4 - 12T^3 + 36T^2 - 24T = 0.
            residual = add(add(powers[4], scale(-12, powers[3])), add(scale(36, powers[2]), scale(-24, powers[1])))
            assert residual == Z8, (a,b,c)
            checks["selected_sum_polynomial"] += 1
            # Exact Newton identities independently verify det(tI-T).
            traces = [None] + [trace(powers[k]) for k in range(1,9)]
            coeffs = [1]
            for k in range(1,9):
                numerator = -sum(coeffs[k-i]*traces[i] for i in range(1,k+1))
                assert numerator % k == 0
                coeffs.append(numerator//k)
            assert coeffs == expected_char, (a,b,c,coeffs)
            checks["selected_sum_characteristic_polynomial"] += 1

source = Path(__file__).resolve()
receipt = {
    "status": "PASS",
    "date_utc": datetime.now(timezone.utc).isoformat(),
    "checker": source.name,
    "checker_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
    "arithmetic": "Exact Python integers representing Gaussian integers; all operators scaled by 4",
    "dimension": 8,
    "outcomes_per_measurement": 4,
    "measurement_count": 3,
    "projection_rank": 2,
    "hadamard": H,
    "unitaries": ["I", "i sigma_x", "-i sigma_y", "i sigma_z"],
    "pvm_identity_checks": checks,
    "selected_sum_identity": "S*(S^3 - 3*S^2 + (9/4)*S - (3/8)*I) = 0",
    "scaled_characteristic_coefficients": expected_char,
    "selected_sum_characteristic_polynomial": "t^2*(t^3-3*t^2+(9/4)*t-3/8)^2",
    "spectral_argument": "Self-adjoint S has eigenvalues among 0, 1+cos(pi/9), 1+cos(5*pi/9), 1+cos(7*pi/9). Characteristic identity gives multiplicity 2 for each. Therefore S <= (1+cos(pi/9))*I for every tuple.",
    "dual_witness": "Y_(a|x)=P_(a|x)/24, X=(1+cos(pi/9))*I/24. The normalization sum Tr(PY)=1 and all 64 inequalities X>=sum Y hold, so eta_g <= Tr X=(1+cos(pi/9))/3.",
    "proof_scope": "Independent exact finite matrix audit plus elementary symbolic spectral/SDP reasoning; no Lean kernel certificate."
}
receipt_path = source.with_name('sharpness-receipt.json')
if receipt_path.exists():
    previous = json.loads(receipt_path.read_text(encoding='utf-8'))
    for key, value in json.loads(json.dumps(receipt)).items():
        if key != 'date_utc':
            assert previous[key] == value, ('existing_receipt_mismatch', key)
else:
    receipt_path.write_text(json.dumps(receipt, indent=2) + '\n', encoding='utf-8')
print(json.dumps({"status": "PASS", "receipt": str(receipt_path), "checks": checks}, indent=2))
