"""Decide partial modular Hom profiles over an arbitrary finite field."""
import argparse
import json
from functools import lru_cache
from math import lcm
from profiles import threshold

threshold_cached = lru_cache(maxsize=None)(threshold)


def witness(observations):
    positive = [m for m, sign in observations if sign]
    negative = [m for m, sign in observations if not sign]
    even = lcm(2, *positive)
    if all(even % m != 0 for m in negative):
        return {"kind": "even integer template for a prime field", "divisor": even}
    if any(m % 2 == 0 for m in positive):
        return None
    exponent = lcm(1, *(threshold_cached(m)[1] for m in positive))
    if all(pow(2, exponent, m) != 1 % m for m in negative):
        return {"kind": "binary field", "divisor": "2^exponent - 1", "exponent": exponent}
    return None


def explain(observations):
    observations = list(dict.fromkeys(observations))
    if any(m < 1 for m, _ in observations):
        raise ValueError("Moduli must be positive")
    example = witness(observations)
    if example is not None:
        return {"realizable": True, "witness": example}
    core = observations.copy()
    for item in observations:
        remaining = [x for x in core if x != item]
        if witness(remaining) is None:
            core = remaining
    return {
        "realizable": False,
        "inclusion_minimal_core": [
            {"modulus": m, "agree": sign,
             "witness_after_deleting": witness([x for x in core if x != (m, sign)])}
            for m, sign in core
        ],
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--agree", nargs="*", type=int, default=[])
    parser.add_argument("--disagree", nargs="*", type=int, default=[])
    args = parser.parse_args()
    assumptions = [(m, True) for m in args.agree] + [(m, False) for m in args.disagree]
    print(json.dumps(explain(assumptions), indent=2))
