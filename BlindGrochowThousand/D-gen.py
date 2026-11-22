"""Search binary projection panels, then emit exact Lean survival spectra."""
import argparse
from itertools import combinations
from pathlib import Path
import random


LEAN = r"""import Lean

namespace ShotD

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- Binary vectors of at most eight coordinates, encoded as natural numbers. -/
def parity8 (x : Nat) : Bool :=
  let a := x ^^^ (x >>> 4)
  let b := a ^^^ (a >>> 2)
  (b ^^^ (b >>> 1)).testBit 0

/-- A seed represents two scalar probes. The result encodes its two-bit image. -/
def project (seed : Nat × Nat) (v : Nat) : Nat :=
  (if parity8 (seed.1 &&& v) then 1 else 0) +
    (if parity8 (seed.2 &&& v) then 2 else 0)

/-- There is one record per plane, with its nonzero vectors x < y < x XOR y. -/
def planes (n : Nat) : List (Nat × Nat) :=
  let vectors := List.range (2 ^ n)
  vectors.flatMap fun x =>
    (vectors.filter fun y => 0 < x && x < y && y < (x ^^^ y)).map fun y => (x, y)

/-- Two nonzero distinct images are independent in the binary codomain. -/
def preserves (seed : Nat × Nat) (plane : Nat × Nat) : Bool :=
  let x := project seed plane.1
  let y := project seed plane.2
  x != 0 && y != 0 && x != y

/-- A row of binary survival indicators in plane order. -/
def hits (n : Nat) (seed : Nat × Nat) : List Nat :=
  (planes n).map fun plane => if preserves seed plane then 1 else 0

/-- Entry t counts planes on which exactly t of the supplied rows have a hit. -/
def histogram (size : Nat) (rows : List (List Nat)) : List Nat :=
  let counts := rows.foldl (List.zipWith (· + ·)) (List.replicate size 0)
  (List.range (rows.length + 1)).map fun t => counts.count t

def spectrum (n : Nat) (seeds : List (Nat × Nat)) : List Nat :=
  histogram (planes n).length (seeds.map (hits n))
"""


def plane_pairs(n):
    return [(x, y) for x, y in combinations(range(1, 2**n), 2) if y < x ^ y]


def project(seed, v):
    a, b = seed
    return ((a & v).bit_count() % 2) + 2 * ((b & v).bit_count() % 2)


def survival(seed, plane):
    a, b = map(lambda x: project(seed, x), plane)
    return a != 0 and b != 0 and a != b


def search(n, good_quota, miss_quota, rng):
    planes = plane_pairs(n)
    seeds = plane_pairs(n)
    masks = [sum(1 << i for i, plane in enumerate(planes) if survival(seed, plane)) for seed in seeds]
    limit = len(planes)
    seen = set()
    accepted = [0, 0]
    for _ in range(20000):
        size = rng.randrange(4, 11) if n == 4 else rng.randrange(5, 15)
        chosen = sorted(rng.sample(range(len(seeds)), size))
        spectrum = [0] * (size + 1)
        for i in range(limit):
            hits = sum((masks[seed] >> i) & 1 for seed in chosen)
            spectrum[hits] += 1
        covered = int(spectrum[0] == 0)
        if (not covered and spectrum[0] > 3) or accepted[covered] >= (miss_quota, good_quota)[covered]:
            continue
        key = tuple(spectrum)
        if key in seen:
            continue
        seen.add(key)
        accepted[covered] += 1
        yield [seeds[seed] for seed in chosen], spectrum
        if accepted == [miss_quota, good_quota]:
            return
    raise RuntimeError((n, accepted))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path)
    args = parser.parse_args()
    rng = random.Random(51387)
    outputs, names = [LEAN], []
    full_by_dim, twice = {}, 0
    for n, good, near in ((4, 63, 62), (5, 62, 63)):
        full_by_dim[n] = []
        panels = list(search(n, good, near, rng))
        planes = plane_pairs(n)
        used = sorted({seed for panel, _ in panels for seed in panel})
        outputs.append(f"private theorem layout{n} : planes {n} = {planes} := by decide")
        outputs.append(f"private theorem count{n} : (planes {n}).length = {len(planes)} := by rw [layout{n}] <;> decide")
        for seed in used:
            row = [int(survival(seed, plane)) for plane in planes]
            name = f"row{n}_{seed[0]}_{seed[1]}"
            outputs.append(f"private theorem {name} : hits {n} {seed} = {row} := by rw [hits, layout{n}] <;> decide")
        for index, (seeds, values) in enumerate(panels, 1):
            name = f"n{n}_{index:03}"
            names.append("ShotD." + name)
            components = ", ".join(f"hits {n} {seed}" for seed in seeds)
            rows = ", ".join(f"row{n}_{a}_{b}" for a, b in seeds)
            outputs.append(
                f"theorem {name} : spectrum {n} {seeds} = {values} := by\n"
                f"  change histogram (planes {n}).length [{components}] = {values}\n"
                f"  rw [count{n}, {rows}] <;> decide\n"
            )
            if values[0] == 0:
                full_by_dim[n].append(index)
                twice += values[1] == 0
    outputs.append("end ShotD\n")
    (args.directory / "D.lean").write_text("\n".join(outputs), encoding="utf-8", newline="\n")
    (args.directory / "D.targets").write_text("\n".join(names) + "\n", encoding="utf-8", newline="\n")
    print(f"{len(names)} spectra; {sum(map(len, full_by_dim.values()))} strict covers; "
          f"{twice} remain covers after one seed is lost")
    print(f"First complete panels: { {n: indices[:3] for n, indices in full_by_dim.items()} }")


if __name__ == "__main__":
    main()
