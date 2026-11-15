"""Run the balanced TI compiler and an exact backend aware of the compiler's blocks."""

from dataclasses import dataclass
from math import prod
from pathlib import Path
import json
import subprocess
import time

import numpy as np

from encoder import compile_published, compile_tensor


def verify_witness(source, target, words):
    """Check invertibility and apply every returned factor to the original tensor."""
    if len(words) != source.ndim:
        return False
    current = source
    for axis, (side, word) in enumerate(zip(source.shape, words)):
        if not 0 <= word < 1 << (side * side):
            return False
        rows = tuple((word >> (side * i)) & ((1 << side) - 1) for i in range(side))
        span = {0}
        for row in rows:
            span |= {point ^ row for point in span}
        if len(span) != 1 << side:
            return False
        matrix = np.array(
            [[(row >> j) & 1 for j in range(side)] for row in rows], dtype=np.uint8
        )
        # Each dot product sums at most three terms on supported inputs.
        current = np.moveaxis(np.tensordot(matrix, current, axes=(1, axis)) & 1, 0, axis)
    return np.array_equal(current, target)


def validate_pair(source, target):
    source = np.asarray(source)
    target = np.asarray(target)
    if source.shape != target.shape or not 3 <= source.ndim <= 20:
        raise ValueError("The pair must have matching shape and order in 3..20")
    if any(not 1 <= dim <= 3 for dim in source.shape) or source.size > 1 << 20:
        raise ValueError("Use local dimensions in 1..3 and at most 2^20 coefficients")
    for tensor in (source, target):
        if np.any((tensor != 0) & (tensor != 1)):
            raise ValueError("Coefficients must be in GF(2)")
    return source.astype(np.uint8, copy=False), target.astype(np.uint8, copy=False)


def write_input(shape, source, target):
    """Backend wire format, also accepted by the independent reference adapters."""
    def serialize(array):
        flat = np.ascontiguousarray(array, dtype=np.uint8).ravel()
        values = np.empty(flat.size * 2, dtype=np.uint8)
        values[::2] = flat + ord("0")
        values[1::2] = 32
        return values.tobytes()
    header = f"{len(shape)} 2\n{' '.join(map(str, shape))}\n".encode("ascii")
    return header + serialize(source) + b"\n" + serialize(target) + b"\n"


@dataclass(frozen=True)
class CompiledPayload:
    original_shape: tuple[int, ...]
    grouped_shape: tuple[int, int, int]
    ordinary_shape: tuple[int, int, int]
    tensor: np.ndarray
    marker_runs: int


def take_payload(compiled):
    """Read the grouped block of a tensor just produced by the standard compiler."""
    if len(compiled.blocks) != 1:
        raise RuntimeError("The balanced reduction should have exactly one payload block")
    shape = compiled.system.grouped_shape
    # The three erasures operate with two cyclic rotations from the initial layout.
    grouped = compiled.blocks[0].data if not compiled.runs else compiled.blocks[0].data.transpose(1, 2, 0)
    if grouped.shape != shape:
        raise RuntimeError("The compiler's payload orientation is inconsistent")
    return CompiledPayload(
        compiled.system.input_shape, shape, compiled.shape, grouped, len(compiled.runs)
    )


class NativeSolver:
    def __init__(self, executable: Path, *, direct=False, budget_ms=2000, grouping=None):
        args = [str(executable.resolve()), "--budget", str(budget_ms)]
        if direct:
            args.append("--direct")
        if grouping:
            args.extend(["--grouped", grouping])
        self.process = subprocess.Popen(args, stdin=subprocess.PIPE, stdout=subprocess.PIPE)

    def __enter__(self):
        return self

    def __exit__(self, *exc):
        self.process.stdin.close()
        self.process.stdout.close()
        self.process.wait(timeout=5)

    def solve(self, request):
        self.process.stdin.write(request)
        self.process.stdin.flush()
        line = self.process.stdout.readline()
        if not line:
            raise RuntimeError("Native solver exited without a verdict")
        return json.loads(line)


def solve_pair(solver, source, target, compiler="balanced"):
    """Exact yes/no, or a timeout on the native search. Only compile trusted inputs."""
    start = time.perf_counter_ns()
    source, target = validate_pair(source, target)
    metadata = {}
    if compiler in ("balanced", "half", "balanced-runs", "half-runs", "balanced-geometric"):
        partition = compiler.split("-")[0]
        layer = "mixed" if compiler in ("balanced", "half") else "ordinary"
        tag_policy = "geometric" if compiler == "balanced-geometric" else "compact"
        a = take_payload(compile_tensor(source, partition, layer=layer, tag_policy=tag_policy))
        b = take_payload(compile_tensor(target, partition, layer=layer, tag_policy=tag_policy))
        if a.grouped_shape != b.grouped_shape or a.ordinary_shape != b.ordinary_shape:
            raise RuntimeError("Compiled formats differ")
        metadata.update(
            grouped_shape=a.grouped_shape, stored_shape=a.ordinary_shape,
            marker_runs=a.marker_runs,
        )
        payload_a, payload_b = a.tensor, b.tensor
    elif compiler == "published-runs":
        a = compile_published(source)
        b = compile_published(target)
        if not a.blocks or not b.blocks or a.shape != b.shape:
            raise RuntimeError("Published output does not expose a compatible payload")
        # Every displayed full-arm relation block contains one reshape of the input.
        payload_a, payload_b = a.blocks[0].data, b.blocks[0].data
        metadata.update(stored_shape=a.shape, marker_runs=len(a.runs))
    elif compiler == "direct":
        payload_a, payload_b = source, target
    else:
        raise ValueError("Unknown compiler")
    packed = time.perf_counter_ns()
    request = write_input(source.shape, payload_a, payload_b)
    encoded = time.perf_counter_ns()
    answer = solver.solve(request)
    solved = time.perf_counter_ns()
    if answer["result"] == "yes" and not verify_witness(source, target, answer["witness"]):
        raise RuntimeError("Returned isomorphism failed independent verification")
    checked = time.perf_counter_ns()
    return {
        **answer, **metadata, "compiler_ms": (packed - start) / 1e6,
        "wire_ms": (encoded - packed) / 1e6, "backend_wall_ms": (solved - encoded) / 1e6,
        "verify_ms": (checked - solved) / 1e6, "total_ms": (checked - start) / 1e6,
    }


def read_case(path):
    ints = list(map(int, path.read_bytes().split()))
    order, prime = ints[:2]
    if prime != 2:
        raise ValueError("Only binary cases are supported")
    shape = tuple(ints[2:2 + order])
    size = prod(shape)
    if len(ints) != 2 + order + 2 * size:
        raise ValueError("Input size does not match its shape")
    array = np.array(ints[2 + order:], dtype=np.int64).reshape(2, *shape)
    return array[0], array[1]


def main():
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("pair", type=Path)
    parser.add_argument("--exe", type=Path, default=Path(__file__).with_name("native_ti.exe"))
    parser.add_argument("--budget-ms", type=int, default=2000)
    parser.add_argument("--compiler", choices=("balanced", "half", "balanced-runs", "half-runs", "balanced-geometric", "published-runs", "direct"), default="balanced")
    parser.add_argument("--direct-search", action="store_true")
    args = parser.parse_args()
    source, target = read_case(args.pair)
    with NativeSolver(args.exe, direct=args.direct_search, budget_ms=args.budget_ms) as solver:
        print(json.dumps(solve_pair(solver, source, target, args.compiler)))


if __name__ == "__main__":
    main()
