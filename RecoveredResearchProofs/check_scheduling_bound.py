"""Exact six-job assignment-game lower bounds, with two durations per type."""

from fractions import Fraction
from functools import cache


@cache
def optimum(durations):
    total = sum(durations)
    subset_sums = [0]
    for duration in durations:
        subset_sums += [left + duration for left in subset_sums]
    return min(max(left, total - left) for left in subset_sums)


def game(choices):
    @cache
    def value(remaining, loads, assigned):
        if sum(remaining) == 0:
            return Fraction(max(loads), optimum(assigned))

        moves = []
        for job_type, count in enumerate(remaining):
            if count == 0:
                continue
            for machine in range(1 if loads[0] == loads[1] else 2):
                moves.append(max(
                    successor(remaining, loads, assigned, job_type, machine, duration)
                    for duration in choices[job_type]
                ))
        return min(moves)

    def successor(remaining, loads, assigned, job_type, machine, duration):
        counts = list(remaining)
        counts[job_type] -= 1
        new_loads = list(loads)
        new_loads[machine] += duration
        return value(tuple(counts), tuple(sorted(new_loads)),
                     tuple(sorted((*assigned, duration))))

    opening = tuple(tuple(
        successor((3, 3), (0, 0), (), job_type, 0, duration)
        for duration in choices[job_type]
    ) for job_type in range(2))
    return value((3, 3), (0, 0), ()), opening


def main():
    expected = (
        (Fraction(30707, 29600), Fraction(31527, 29600)),
        (Fraction(31527, 29600), Fraction(1521, 1480)),
    )
    result, opening = game(((8000, 8820), (10800, 11907)))
    assert opening == expected, opening
    assert result == Fraction(31527, 29600), result
    assert result - Fraction(841, 800) == Fraction(41, 2960)
    control, _ = game(((800, 882), (1200, 1323)))
    assert control == Fraction(681, 640), control
    print("Exact assignment-game values:", result, "and", control)


if __name__ == "__main__":
    main()
