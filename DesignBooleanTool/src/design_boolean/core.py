"""Exact design-to-Boolean recognition using the bordered-rank characterization.

Incidence orientation is points (rows) by blocks (columns). All arithmetic is
integer or over F2. This executable implementation is not itself Lean verified.
"""
from __future__ import annotations

from dataclasses import asdict, dataclass, field
from hashlib import sha256
from operator import index
from time import perf_counter
from typing import Any, Iterable, Sequence


@dataclass(frozen=True)
class IncidenceMatrix:
    """Packed binary rows; bit j records membership in block j."""

    rows: tuple[int, ...]
    num_blocks: int

    @property
    def num_points(self) -> int:
        return len(self.rows)

    @classmethod
    def from_rows(cls, rows: Iterable[Iterable[int]]) -> IncidenceMatrix:
        packed: list[int] = []
        width: int | None = None
        for row_no, row in enumerate(rows):
            if isinstance(row, (str, bytes)):
                values = list(row.decode() if isinstance(row, bytes) else row)
                if any(x not in ('0', '1') for x in values):
                    raise ValueError(f'Row {row_no} must contain only 0 and 1.')
                values = [int(x) for x in values]
            else:
                try:
                    values = [index(x) for x in row]
                except (TypeError, ValueError) as exc:
                    raise ValueError(f'Row {row_no} must contain binary integers.') from exc
                if any(x not in (0, 1) for x in values):
                    raise ValueError(f'Row {row_no} must contain only 0 and 1.')
            if width is None:
                width = len(values)
            elif len(values) != width:
                raise ValueError('Incidence rows must have equal lengths.')
            data = bytearray((len(values)+7)//8)
            for j, value in enumerate(values):
                if value:
                    data[j//8] |= 1 << (j%8)
            packed.append(int.from_bytes(data, 'little'))
        if not packed or not width:
            raise ValueError('An incidence matrix must have at least one point and block.')
        return cls(tuple(packed), width)

    @classmethod
    def from_blocks(cls, num_points: int, blocks: Iterable[Iterable[int]]) -> IncidenceMatrix:
        num_points = index(num_points)
        if num_points <= 0:
            raise ValueError('num_points must be positive.')
        rows = [0] * num_points
        count = 0
        for j, block in enumerate(blocks):
            seen: set[int] = set()
            for point in block:
                p = index(point)
                if p < 0 or p >= num_points:
                    raise ValueError(f'Block {j} contains an out-of-range point.')
                if p in seen:
                    raise ValueError(f'Block {j} repeats a point.')
                seen.add(p)
                rows[p] |= 1 << j
            count += 1
        if not count:
            raise ValueError('There must be at least one block.')
        return cls(tuple(rows), count)

    def to_rows(self) -> list[list[int]]:
        return [[(row >> j) & 1 for j in range(self.num_blocks)] for row in self.rows]


def _matrix(incidence: IncidenceMatrix | Iterable[Iterable[int]]) -> IncidenceMatrix:
    matrix = incidence if isinstance(incidence, IncidenceMatrix) else IncidenceMatrix.from_rows(incidence)
    try:
        width = index(matrix.num_blocks)
        rows = tuple(index(x) for x in matrix.rows)
    except (ValueError, TypeError) as exc:
        raise ValueError('Packed incidence requires integer rows and block count.') from exc
    if width <= 0 or not rows:
        raise ValueError('An incidence matrix must have at least one point and block.')
    if any(row < 0 or row.bit_length() > width for row in rows):
        raise ValueError('A packed incidence row exceeds the declared block count.')
    return IncidenceMatrix(rows, width)


def fwht(values: Iterable[int]) -> list[int]:
    """Return the unnormalized exact Walsh-Hadamard transform; do not mutate input."""
    out = [index(value) for value in values]
    n = len(out)
    if n == 0 or n & (n - 1):
        raise ValueError('Walsh transform length must be a positive power of two.')
    half = 1
    while half < n:
        for start in range(0, n, 2 * half):
            for j in range(start, start + half):
                a, b = out[j], out[j + half]
                out[j], out[j + half] = a + b, a - b
        half *= 2
    return out


def gf2_rank(vectors: Iterable[int]) -> int:
    """Binary rank of nonnegative packed vectors."""
    pivots: dict[int, int] = {}
    for raw in vectors:
        value = index(raw)
        if value < 0:
            raise ValueError('GF(2) packed vectors must be nonnegative.')
        while value:
            lead = value.bit_length() - 1
            if lead in pivots:
                value ^= pivots[lead]
            else:
                pivots[lead] = value
                break
    return len(pivots)


def _columns(matrix: IncidenceMatrix) -> list[int]:
    result = [0] * matrix.num_blocks
    width_bytes = (matrix.num_blocks+7)//8
    for p, row in enumerate(matrix.rows):
        point = 1 << p
        for byte_index, byte in enumerate(row.to_bytes(width_bytes, 'little')):
            while byte:
                low = byte & -byte
                result[8*byte_index+low.bit_length()-1] |= point
                byte ^= low
    return result


def _hash(matrix: IncidenceMatrix) -> str:
    h = sha256(f'design-boolean/incidence/1:{matrix.num_points}:{matrix.num_blocks}\n'.encode('ascii'))
    for row in matrix.rows:
        h.update(f'{row:x}\n'.encode('ascii'))
    return h.hexdigest()


def _parameters(matrix: IncidenceMatrix) -> dict[str, int] | None:
    v, b = matrix.num_points, matrix.num_blocks
    if v & (v - 1) or b & (b - 1):
        return None
    n, m = v.bit_length() - 1, b.bit_length() - 1
    if n < 4 or n % 2 or m < n:
        return None
    r = m - n
    q = 1 << (n // 2 - 1)
    return dict(v=v, b=b, n=n, m=m, r=r, k=q * (2*q-1),
                lambda_=(1 << r)*q*(q-1), amplitude=1 << (m - n//2),
                expected_normalized_rank=m, expected_bordered_rank=m+2,
                replication=b*(q*(2*q-1))//v)


@dataclass
class RecognitionResult:
    status: str
    reason: str
    parameters: dict[str, int] = field(default_factory=dict)
    certificate: dict[str, Any] | None = None
    diagnostics: dict[str, Any] = field(default_factory=dict)

    @property
    def recognized(self) -> bool:
        return self.status == 'recognized'

    @property
    def truth_table(self) -> list[int] | None:
        return None if self.certificate is None else self.certificate['truth_table']

    @property
    def function(self):
        if not self.recognized or self.certificate is None:
            return None
        from .boolean import BooleanFunction
        return BooleanFunction(tuple(self.certificate['truth_table']))

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


@dataclass
class CertificateVerification:
    valid: bool
    reason: str
    checks: dict[str, Any] = field(default_factory=dict)

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


def _coordinates(columns: Sequence[int]) -> tuple[list[int], list[int]]:
    """Return independent original column indices and coordinates in that basis."""
    pivots: dict[int, tuple[int, int]] = {}
    selected: list[int] = []
    coordinates: list[int] = []
    for j, original in enumerate(columns):
        value, coordinate = original, 0
        while value:
            lead = value.bit_length() - 1
            if lead in pivots:
                pivot, mask = pivots[lead]
                value ^= pivot
                coordinate ^= mask
            else:
                new = 1 << len(selected)
                pivots[lead] = (value, coordinate ^ new)
                selected.append(j)
                coordinate = new
                break
        coordinates.append(coordinate)
    return selected, coordinates


def verify_certificate(incidence: IncidenceMatrix | Iterable[Iterable[int]],
                       certificate: dict[str, Any]) -> CertificateVerification:
    """Check an explicit realization directly, without relying on the rank theorem.

    Verifies the complete Walsh spectrum, its signed support, the full incidence
    identity, a bijective block labeling, and absence of linear structures.
    """
    checks: dict[str, Any] = {}
    try:
        matrix = _matrix(incidence)
        parameters = _parameters(matrix)
        if parameters is None:
            return CertificateVerification(False, 'Input shape is outside the supported parameter range.')
        if not isinstance(certificate, dict) or certificate.get('schema') != 'design-boolean/1':
            return CertificateVerification(False, 'Unknown or missing certificate schema.')
        if certificate.get('input_hash') != _hash(matrix):
            return CertificateVerification(False, 'Certificate input hash does not match this matrix.')
        if certificate.get('parameters') != parameters:
            return CertificateVerification(False, 'Certificate parameters do not match the incidence shape.')
        b, v, m, amplitude = parameters['b'], parameters['v'], parameters['m'], parameters['amplitude']
        truth = [index(x) for x in certificate['truth_table']]
        beta = [index(x) for x in certificate['block_coordinates']]
        phi = [index(x) for x in certificate['point_frequencies']]
        offsets = [index(x) for x in certificate['point_offsets']]
        if len(truth) != b or any(x not in (0, 1) for x in truth):
            return CertificateVerification(False, 'Truth table is not a binary table of length 2^m.')
        if len(beta) != b or set(beta) != set(range(b)):
            return CertificateVerification(False, 'Block coordinates are not a bijection onto the binary cube.')
        if len(phi) != v or any(x < 0 or x >= b for x in phi) or len(set(phi)) != v:
            return CertificateVerification(False, 'Point frequencies are not distinct cube elements.')
        if len(offsets) != v or any(x not in (0, 1) for x in offsets):
            return CertificateVerification(False, 'Point offsets must be binary and match the number of points.')
        if certificate.get('amplitude') != amplitude:
            return CertificateVerification(False, 'Walsh amplitude is inconsistent with the parameters.')
        walsh = fwht(1 - 2*x for x in truth)
        if any(x not in (0, amplitude, -amplitude) for x in walsh):
            return CertificateVerification(False, 'The reconstructed function has the wrong Walsh spectrum.')
        support = {i for i, value in enumerate(walsh) if value}
        if support != set(phi):
            return CertificateVerification(False, 'Point frequencies do not equal the complete Walsh support.')
        if any(walsh[freq] != amplitude*(1-2*offset) for freq, offset in zip(phi, offsets)):
            return CertificateVerification(False, 'Point signs do not match the Walsh coefficients.')
        checks['walsh_spectrum'] = True
        checks['walsh_support_size'] = len(support)
        # Fast exact evaluation of the incidence identity in its original column order.
        coordinate_bytes = [bytearray((b+7)//8) for _ in range(m)]
        function_bytes = bytearray((b+7)//8)
        for j, x in enumerate(beta):
            byte_index, bit = j//8, 1 << (j%8)
            if truth[x]:
                function_bytes[byte_index] |= bit
            value = x
            while value:
                low = value & -value
                coordinate_bytes[low.bit_length()-1][byte_index] |= bit
                value ^= low
        coordinate_rows = [int.from_bytes(data, 'little') for data in coordinate_bytes]
        function_row = int.from_bytes(function_bytes, 'little')
        mask = (1 << b)-1
        for p, (frequency, offset) in enumerate(zip(phi, offsets)):
            expected = function_row ^ (mask if offset else 0)
            value = frequency
            while value:
                low = value & -value
                expected ^= coordinate_rows[low.bit_length()-1]
                value ^= low
            if expected != matrix.rows[p]:
                return CertificateVerification(False, f'Incidence identity fails at point index {p}.', checks)
        checks['incidence_identity'] = True
        # Linear structure (a,c) exists iff support is contained in {u:u.a=c}.
        affine_rank = gf2_rank(freq ^ phi[0] for freq in phi)
        checks['walsh_support_affine_rank'] = affine_rank
        if affine_rank != m:
            return CertificateVerification(False, 'The function has a nonzero linear structure.', checks)
        checks['no_nonzero_linear_structures'] = True
        checks['block_coordinate_bijection'] = True
        return CertificateVerification(True, 'Exact Walsh spectrum, incidence, and linear-structure checks passed.', checks)
    except (KeyError, TypeError, ValueError, OverflowError) as exc:
        return CertificateVerification(False, f'Malformed input or certificate: {exc}', checks)


def _recognize_python(incidence: IncidenceMatrix | Iterable[Iterable[int]], *,
              point_labels: Sequence[Any] | None = None,
              block_labels: Sequence[Any] | None = None) -> RecognitionResult:
    """Recognize and reconstruct the complete supported simple 2-design family.

    The supported nondegenerate family has v=2^n points (even n>=4), b=2^m
    blocks (m>=n), k=2^(n-1)-2^(n/2-1), and lambda=2^(m-n)*q*(q-1),
    q=2^(n/2-1). Both bent (r=0) and plateaued (r=m-n>=1) cases are included.
    Design axioms and simplicity are checked, never assumed.
    """
    started = perf_counter()
    timings: dict[str, float] = {}
    diagnostics: dict[str, Any] = {'timings_seconds': timings}
    parameters: dict[str, int] = {}
    def finish(status: str, reason: str, certificate: dict[str, Any] | None = None) -> RecognitionResult:
        if status == 'invalid_input':
            diagnostics['reason_code'] = 'MALFORMED_INPUT'
        elif status == 'unsupported':
            diagnostics['reason_code'] = 'UNSUPPORTED_PARAMETERS'
        elif status == 'recognized':
            diagnostics['reason_code'] = 'CERTIFIED_REALIZATION'
        else:
            diagnostics.setdefault('reason_code', 'REJECTED_CANDIDATE')
        timings['total'] = perf_counter()-started
        return RecognitionResult(status, reason, parameters, certificate, diagnostics)
    try:
        matrix = _matrix(incidence)
        if point_labels is not None and len(point_labels) != matrix.num_points:
            return finish('invalid_input', 'point_labels length must match the number of rows.')
        if block_labels is not None and len(block_labels) != matrix.num_blocks:
            return finish('invalid_input', 'block_labels length must match the number of columns.')
    except (TypeError, ValueError, OverflowError) as exc:
        return finish('invalid_input', str(exc))
    timings['input'] = perf_counter()-started
    diagnostics['num_points'] = matrix.num_points
    diagnostics['num_blocks'] = matrix.num_blocks
    parameters = _parameters(matrix) or {}
    if not parameters:
        return finish('unsupported', 'Supported shapes require v=2^n, even n>=4, and b=2^m with m>=n.')
    v, b, m = parameters['v'], parameters['b'], parameters['m']
    design_started = perf_counter()
    columns = _columns(matrix)
    for j, column in enumerate(columns):
        size = column.bit_count()
        if size != parameters['k']:
            diagnostics['reason_code'] = 'BLOCK_SIZE_MISMATCH'
            diagnostics['failed_block'] = j
            diagnostics['actual_block_size'] = size
            timings['design_validation'] = perf_counter()-design_started
            return finish('not_recognized', 'A block has the wrong size for the supported design family.')
    if len(set(columns)) != b:
        diagnostics['reason_code'] = 'DUPLICATE_BLOCKS'
        timings['design_validation'] = perf_counter()-design_started
        return finish('not_recognized', 'The incidence matrix has repeated blocks; the theorem requires a simple design.')
    for p in range(v):
        for q in range(p):
            pair_count = (matrix.rows[p] & matrix.rows[q]).bit_count()
            if pair_count != parameters['lambda_']:
                diagnostics['reason_code'] = 'PAIR_MULTIPLICITY_MISMATCH'
                diagnostics['failed_point_pair'] = [q, p]
                diagnostics['actual_pair_count'] = pair_count
                timings['design_validation'] = perf_counter()-design_started
                return finish('not_recognized', 'Point-pair multiplicities do not match the required 2-design.')
    timings['design_validation'] = perf_counter()-design_started
    diagnostics['design_validated'] = True
    rank_started = perf_counter()
    all_points = (1 << v)-1
    first = columns[0]
    normalized = [column ^ first ^ (all_points if ((column ^ first) & 1) else 0) for column in columns]
    selected, beta = _coordinates(normalized)
    rank = len(selected)
    diagnostics['normalized_rank'] = rank
    diagnostics['bordered_rank'] = rank+2
    timings['rank'] = perf_counter()-rank_started
    if rank != m:
        diagnostics['reason_code'] = 'BORDERED_RANK_MISMATCH'
        return finish('not_recognized', f'Bordered binary rank is {rank+2}; the characterization requires {m+2}.')
    if set(beta) != set(range(b)):
        diagnostics['reason_code'] = 'COORDINATE_BIJECTION_FAILURE'
        # Checked explicitly rather than trusting rank saturation or separation.
        return finish('not_recognized', 'Normalized columns do not bijectively cover the recovered cube.')
    reconstruction_started = perf_counter()
    truth = [0]*b
    for j, coordinate in enumerate(beta):
        truth[coordinate] = (matrix.rows[0] >> j) & 1
    phi = [sum(((normalized[j] >> p) & 1) << i for i, j in enumerate(selected)) for p in range(v)]
    g = [((row & 1) ^ (matrix.rows[0] & 1)) for row in matrix.rows]
    certificate: dict[str, Any] = dict(schema='design-boolean/1', parameters=parameters.copy(),
        input_hash=_hash(matrix), truth_table=truth, block_coordinates=beta,
        point_frequencies=phi, point_offsets=g, amplitude=parameters['amplitude'],
        basis_block_indices=selected, anchor_point=0, anchor_block=0)
    if point_labels is not None:
        certificate['point_labels'] = list(point_labels)
    if block_labels is not None:
        certificate['block_labels'] = list(block_labels)
    timings['reconstruction'] = perf_counter()-reconstruction_started
    verification_started = perf_counter()
    verified = verify_certificate(matrix, certificate)
    timings['certificate_verification'] = perf_counter()-verification_started
    diagnostics['certificate_checks'] = verified.checks
    if not verified.valid:
        diagnostics['reason_code'] = 'CERTIFICATE_FAILURE'
        return finish('not_recognized', 'Direct reconstruction check failed: '+verified.reason)
    return finish('recognized', 'Recognized the supported plateaued addition design and verified an explicit Boolean-function realization.', certificate)


def recognize(incidence: IncidenceMatrix | Iterable[Iterable[int]], *,
              point_labels: Sequence[Any] | None = None,
              block_labels: Sequence[Any] | None = None,
              backend: str = "auto") -> RecognitionResult:
    """Validate, reconstruct and check the supported design family.

    backend='auto' uses an explicitly built native library when available,
    otherwise the dependency-free Python implementation. 'native' requires
    that library; 'python' always selects the reference implementation.
    No compiler or installer is started by a recognition call.
    """
    if backend not in ("auto", "python", "native"):
        raise ValueError("backend must be auto, python or native")
    if backend != "python":
        from . import native
        if backend == "native" or native.available():
            result = native.recognize_native(incidence, point_labels=point_labels,
                                             block_labels=block_labels)
            result.diagnostics["backend"] = "native"
            return result
    result = _recognize_python(incidence, point_labels=point_labels,
                                block_labels=block_labels)
    result.diagnostics["backend"] = "python"
    return result
