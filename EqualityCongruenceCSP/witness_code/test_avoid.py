#!/usr/bin/env python3
"""Deterministic black-box tests with prescribed answers, using Python integers.

This file does not implement the candidate search. The expected first candidate
and output point are specified independently for each case. A second checker
then substitutes successful outputs into the input equations and affine forms.
"""

from dataclasses import dataclass
from pathlib import Path
import subprocess
import sys


ROOT = Path(__file__).resolve().parent
TESTS = ROOT / "tests"


@dataclass(frozen=True)
class Data:
    n: int
    d: int
    m: int
    u: list[int]
    B: list[list[int]]
    rho: list[int]
    forms: list[list[int]]  # Each row is [constant, coefficient_0, ...].

    def render(self) -> str:
        lines = [f"{self.n} {self.d} {len(self.forms)}", str(self.m)]
        lines.append(" ".join(map(str, self.u)))
        lines.extend(" ".join(map(str, row)) for row in self.B)
        lines.append(" ".join(map(str, self.rho)))
        lines.extend(" ".join(map(str, form)) for form in self.forms)
        return "\n".join(lines) + "\n"


@dataclass(frozen=True)
class Case:
    name: str
    data: Data
    code: int
    stdout: str
    stderr: str = ""


def vector_line(name: str, values: list[int]) -> str:
    suffix = "" if not values else " " + " ".join(map(str, values))
    return f"{name} {len(values)}{suffix}\n"


def ok(T: int, bound: int, z: list[int], parameters: list[int],
       x: list[int], values: list[int]) -> str:
    return (f"OK\nT {T}\nBOUND {bound}\n"
            + vector_line("Z", z)
            + vector_line("PARAMETERS", parameters)
            + vector_line("X", x)
            + vector_line("VALUES", values)
            + "VERIFIED exact_coset_and_nonzero_forms\n")


def zero(index: int, directions: list[int]) -> str:
    return (f"IDENTICALLY_ZERO {index}\nBASE_VALUE 0\n"
            + vector_line("DIRECTION_VALUES", directions))


def cases() -> list[Case]:
    K = 10**100
    return [
        Case("01_dimension_zero",
             Data(2, 0, 7, [3, -2], [[], []], [],
                  [[-2, 1, 0], [5, 0, 1]]),
             0, ok(0, 0, [], [], [3, -2], [1, 3])),
        Case("02_no_forms",
             Data(2, 2, 5, [1, -2], [[2, 1], [-1, 3]], [4, -2], []),
             0, ok(0, 0, [0, 0], [4, -2], [7, -12], [])),
        Case("03_nonzero_constant",
             Data(1, 1, 3, [2], [[4]], [5], [[9, 0]]),
             0, ok(0, 1, [0], [5], [22], [9])),
        Case("04_identically_zero_restriction",
             Data(2, 1, 4, [1, 2], [[1], [2]], [3],
                  [[0, 2, -1], [1, 1, 0]]),
             2, zero(0, [0])),
        Case("05_all_initial_roots",
             Data(1, 1, 1, [0], [[1]], [0],
                  [[0, 1], [-1, 1], [-2, 1], [-3, 1]]),
             0, ok(4, 4, [4], [4], [4], [4, 3, 2, 1])),
        Case("06_exponents_start_at_one",
             Data(2, 2, 1, [0, 0], [[1, 0], [0, 1]], [0, 0],
                  [[-1, 1, 0], [0, 0, 1]]),
             0, ok(2, 4, [2, 4], [2, 4], [2, 4], [1, 4])),
        Case("07_hundred_digit_integers",
             Data(2, 1, K + 7, [K, -K], [[K], [-K - 1]], [0],
                  [[0, K, K]]),
             0, ok(1, 1, [1], [K + 7],
                   [K*K + 8*K, -K*K - 9*K - 7], [-K*K - 7*K])),
        Case("08_cancellation_example_cell",
             Data(2, 2, 5, [0, 0], [[1, 0], [0, 1]], [0, 0],
                  [[0, 1, -1], [0, 1, 0], [-1, 1, 0]]),
             0, ok(2, 6, [2, 4], [10, 20], [10, 20], [-10, 10, 9])),
        Case("09_zero_dimension_zero_form",
             Data(1, 0, 1, [3], [[]], [], [[-3, 1]]),
             2, zero(0, [])),
        Case("10_empty_ambient_space",
             Data(0, 0, 1, [], [], [], []),
             0, ok(0, 0, [], [], [], [])),
        Case("11_invalid_zero_modulus",
             Data(1, 1, 0, [0], [[1]], [0], []),
             64, "", "INPUT_ERROR m must be positive\n"),
    ]


def output_vector(lines: dict[str, list[str]], key: str) -> list[int]:
    values = lines[key]
    length = int(values[0])
    result = list(map(int, values[1:]))
    assert len(result) == length, (key, length, result)
    return result


def check_equations(data: Data, output: str) -> None:
    """Direct substitution only; there is no candidate enumeration here."""
    rows = [line.split() for line in output.splitlines()]
    fields = {row[0]: row[1:] for row in rows}
    z = output_vector(fields, "Z")
    parameters = output_vector(fields, "PARAMETERS")
    point = output_vector(fields, "X")
    values = output_vector(fields, "VALUES")
    candidate = int(fields["T"][0])
    assert len(z) == len(parameters) == data.d
    assert len(point) == data.n
    assert len(values) == len(data.forms)
    assert int(fields["BOUND"][0]) == len(data.forms) * data.d
    assert 0 <= candidate <= len(data.forms) * data.d
    for j in range(data.d):
        assert z[j] == candidate ** (j + 1)
        assert parameters[j] - data.rho[j] == data.m * z[j]
    for i in range(data.n):
        assert point[i] == data.u[i] + sum(
            data.B[i][j] * parameters[j] for j in range(data.d))
    for form, reported_value in zip(data.forms, values):
        actual_value = form[0] + sum(
            form[i + 1] * point[i] for i in range(data.n))
        assert actual_value == reported_value
        assert actual_value != 0


def check_zero_certificate(data: Data, output: str) -> None:
    rows = [line.split() for line in output.splitlines()]
    fields = {row[0]: row[1:] for row in rows}
    index = int(fields["IDENTICALLY_ZERO"][0])
    form = data.forms[index]
    base = [data.u[i] + sum(data.B[i][j] * data.rho[j]
                           for j in range(data.d)) for i in range(data.n)]
    assert form[0] + sum(form[i + 1] * base[i] for i in range(data.n)) == 0
    directions = output_vector(fields, "DIRECTION_VALUES")
    assert directions == [0] * data.d
    for j in range(data.d):
        assert data.m * sum(form[i + 1] * data.B[i][j]
                            for i in range(data.n)) == 0


def main() -> int:
    executable = (Path(sys.argv[1]).resolve() if len(sys.argv) > 1
                  else ROOT / "avoid")
    TESTS.mkdir(exist_ok=True)
    passed = 0
    log: list[str] = []
    for case in cases():
        input_text = case.data.render()
        (TESTS / f"{case.name}.in").write_text(input_text)
        (TESTS / f"{case.name}.expected").write_text(case.stdout)
        result = subprocess.run([str(executable)], input=input_text,
                                text=True, capture_output=True, check=False)
        (TESTS / f"{case.name}.actual").write_text(result.stdout)
        (TESTS / f"{case.name}.stderr.actual").write_text(result.stderr)
        assert result.returncode == case.code, (
            case.name, "exit code", result.returncode, case.code, result.stderr)
        assert result.stdout == case.stdout, (
            case.name, "stdout mismatch", result.stdout, case.stdout)
        assert result.stderr == case.stderr, (
            case.name, "stderr mismatch", result.stderr, case.stderr)
        if case.code == 0:
            check_equations(case.data, result.stdout)
        elif case.code == 2:
            check_zero_certificate(case.data, result.stdout)
        passed += 1
        status = f"PASS {case.name} (exit {result.returncode})"
        print(status)
        log.extend([status, "stdout:", result.stdout.rstrip("\n") or "<empty>",
                    "stderr:", result.stderr.rstrip("\n") or "<empty>", ""])
    summary = (f"RESULT {passed}/{len(cases())} deterministic cases passed; "
               "all returned points and zero certificates checked exactly.")
    print(summary)
    log.append(summary)
    (ROOT / "captured_test_output.txt").write_text("\n".join(log) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
