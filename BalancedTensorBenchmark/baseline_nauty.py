"""Exact all-sides-two GF(2) tensor isomorphism via Nauty or Traces.

The colored graph has three vertices per tensor mode, one for each nonzero
covector, plus one vertex for each pure evaluation with value one. Incidence
records the covector in every mode. Full canonical graph comparison decides
isomorphism, and a positive graph match yields a checked tensor witness.
"""
import argparse
import json
import os
from pathlib import Path
import re
from queue import Empty, Queue
import subprocess
from threading import Thread
import time

from baseline_io import read_pair


def expand_evaluations(coefficients, order):
    """Change every {e1,e2} index to {e1,e2,e1+e2}, last axis first."""
    values = list(coefficients)
    stride = 1
    for _ in range(order):
        next_values = []
        for start in range(0, len(values), 2 * stride):
            a = values[start:start + stride]
            b = values[start + stride:start + 2 * stride]
            next_values.extend(a)
            next_values.extend(b)
            next_values.extend(x ^ y for x, y in zip(a, b))
        values = next_values
        stride *= 3
    return values


def incidence_graph(coefficients, order):
    values = expand_evaluations(coefficients, order)
    adjacency = [[] for _ in range(3 * order)]
    support_count = 0
    for index, value in enumerate(values):
        if not value:
            continue
        vertex = 3 * order + support_count
        support_count += 1
        for mode in range(order - 1, -1, -1):
            index, digit = divmod(index, 3)
            adjacency[3 * mode + digit].append(vertex)
    return adjacency, support_count


def graph_script(graph, order):
    adjacency, support = graph
    n = 3 * order + support
    incidence = "".join(f"{i}: " + " ".join(map(str, neighbors)) + ";\n"
                        for i, neighbors in enumerate(adjacency) if neighbors)
    partition = "|".join(f"{3 * i}:{3 * i + 2}" for i in range(order))
    if support:
        partition += f"|{3 * order}:{n - 1}"
    return f"n={n}\ng\n{incidence}.\nf=[{partition}]\nc\n-a -m\nx\n"


def parse_witness(output, order):
    """For each mode decode covector bijection as inverse transpose."""
    mapping_mark = output.index("h and h' are identical.")
    mapping = {int(a): int(b) for a, b in re.findall(r"(\d+)-(\d+)", output[mapping_mark:])}
    covectors = [(1, 0), (0, 1), (1, 1)]
    result = []
    for mode in range(order):
        offset = 3 * mode
        unit_images = [mapping[offset + i] - offset for i in range(2)]
        if any(not 0 <= k < 3 for k in unit_images) or unit_images[0] == unit_images[1]:
            raise ValueError("invalid mode permutation in graph witness")
        (a, c), (b, d) = (covectors[k] for k in unit_images)
        result.append((d, c, b, a))
    return result


def apply_maps(source, maps):
    values = list(source)
    for mode, (a, b, c, d) in enumerate(maps):
        stride = 1 << (len(maps) - mode - 1)
        updated = [0] * len(values)
        for start in range(0, len(values), 2 * stride):
            for i in range(start, start + stride):
                x, y = values[i], values[i + stride]
                updated[i], updated[i + stride] = (a & x) ^ (b & y), (c & x) ^ (d & y)
        values = updated
    return values


def dreadnaut_argv(command, runtime):
    if command is not None:
        return [str(command)], None
    bindir = runtime / "opt" / "sagemath-9.3" / "local" / "bin"
    env = dict(os.environ)
    env["PATH"] = os.pathsep.join(map(str, (runtime / "bin", bindir))) + os.pathsep + env["PATH"]
    return [str(bindir / "dreadnaut.exe")], env


class DreadnautSession:
    """Keep the external solver warm, matching the native baseline's worker."""
    def __init__(self, command, runtime):
        args, env = dreadnaut_argv(command, runtime)
        self.proc = subprocess.Popen(args, env=env, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                     stderr=subprocess.STDOUT, text=True, bufsize=1)
        self.output = Queue()
        self.reader = Thread(target=self._read_lines, daemon=True)
        self.reader.start()
        self._call("B\n", 10)

    def _read_lines(self):
        for line in self.proc.stdout:
            self.output.put(line)
        self.output.put(None)

    def _call(self, script, timeout):
        deadline = time.perf_counter() + timeout
        self.proc.stdin.write(script + '"BASELINE_END\\n"\n')
        self.proc.stdin.flush()
        lines = []
        while True:
            left = deadline - time.perf_counter()
            if left <= 0:
                self.proc.kill()
                raise subprocess.TimeoutExpired("dreadnaut", timeout)
            try:
                line = self.output.get(timeout=left)
            except Empty as exc:
                self.proc.kill()
                raise subprocess.TimeoutExpired("dreadnaut", timeout) from exc
            if line is None:
                raise RuntimeError("dreadnaut exited before finishing the case")
            if line.strip() == "BASELINE_END":
                return "".join(lines)
            lines.append(line)

    def solve(self, script, timeout):
        return self._call(script, timeout)

    def close(self):
        if self.proc.poll() is None:
            self.proc.stdin.write("q\n")
            self.proc.stdin.flush()
        self.proc.wait(timeout=5)
        self.proc.stdin.close()
        self.proc.stdout.close()


def solve_file(path, command, runtime, timeout, algorithm, session=None):
    total_start = time.perf_counter()
    prime, sizes, source, target = read_pair(path)
    if prime != 2 or set(sizes) != {2}:
        raise ValueError("this encoding requires GF(2) and every tensor side exactly 2")
    order = len(sizes)
    read_s = time.perf_counter() - total_start
    build_start = time.perf_counter()
    graph_a = incidence_graph(source, order)
    graph_b = incidence_graph(target, order)
    a_size, b_size = graph_a[1], graph_b[1]
    script = ""
    if a_size == b_size:
        script = f"A{algorithm}\n" + graph_script(graph_a, order) + "@\n" + graph_script(graph_b, order) + "##\n"
    result = {"case": path.name, "order": order, "read_s": read_s,
              "build_s": time.perf_counter() - build_start,
              "graph_vertices": [3 * order + a_size, 3 * order + b_size],
              "solver_input_bytes": len(script), "algorithm": algorithm}
    if not script:
        result.update(status="decided", isomorphic=False, method="evaluation support cardinality")
    else:
        solve_start = time.perf_counter()
        returncode, error = 0, ""
        try:
            if session is None:
                args, env = dreadnaut_argv(command, runtime)
                run = subprocess.run(args, input=script + "q\n", env=env, text=True,
                                     capture_output=True, check=False, timeout=timeout)
                solved, returncode, error = run.stdout, run.returncode, run.stderr
            else:
                solved = session.solve(script, timeout)
            result["solver_s"] = time.perf_counter() - solve_start
            result["solver_startup_included"] = session is None
        except subprocess.TimeoutExpired:
            result.update(status="timeout", total_s=time.perf_counter() - total_start)
            return result
        times = [float(x) for x in re.findall(r"cpu time =\s*([0-9.]+)\s*seconds", solved)]
        result["reported_cpu_s"] = times
        if returncode != 0 or error.strip():
            result.update(status="error", returncode=returncode, diagnostic=(solved + error)[-500:])
        elif "h and h' are identical." in solved:
            verify_start = time.perf_counter()
            witness = parse_witness(solved, order)
            okay = apply_maps(source, witness) == target
            if not okay:
                # Older dreadnaut variants have used the opposite saved-label
                # print direction. Try the inverse and verify the result.
                witness = [(d, b, c, a) for a, b, c, d in witness]
                okay = apply_maps(source, witness) == target
            if not okay:
                raise ValueError("graph witness did not verify in the original tensor")
            result.update(status="decided", isomorphic=True, witness=witness,
                          verify_s=time.perf_counter() - verify_start, method="canonical graph comparison")
        elif "h and h' are different." in solved:
            result.update(status="decided", isomorphic=False, method="canonical graph comparison")
        else:
            result.update(status="error", diagnostic=solved[-500:])
    result["total_s"] = time.perf_counter() - total_start
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    backend = parser.add_mutually_exclusive_group(required=True)
    backend.add_argument("--dreadnaut", type=Path)
    backend.add_argument("--runtime", type=Path, help="extracted Sage 9.3 Cygwin runtime")
    parser.add_argument("--timeout", type=float, default=15)
    parser.add_argument("--algorithm", choices=["s", "t"], default="t", help="s=Nauty sparse, t=Traces")
    parser.add_argument("--persistent", action="store_true")
    parser.add_argument("cases", type=Path, nargs="+")
    args = parser.parse_args()
    session = DreadnautSession(args.dreadnaut, args.runtime) if args.persistent else None
    try:
        for case in args.cases:
            result = solve_file(case, args.dreadnaut, args.runtime, args.timeout, args.algorithm, session)
            print(json.dumps(result), flush=True)
    finally:
        if session is not None:
            session.close()


if __name__ == "__main__":
    main()
