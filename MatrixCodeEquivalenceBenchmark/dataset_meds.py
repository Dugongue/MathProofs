"""Published MEDS example and reference KAT decoding for ordered matrix codes."""
import argparse
import hashlib
import json
from pathlib import Path


OXFORD_SOURCE = "https://www.maths.ox.ac.uk/system/files/inline-files/meds.pdf"
OXFORD_PARAMETERS = 13, 4, 6, 5
OXFORD_C = (
    (2,8,10,4,5,7, 1,11,7,9,6,12, 3,0,13,5,4,8, 9,6,3,2,10,11),
    (12,0,4,11,9,3, 5,6,8,13,2,1, 10,7,3,9,4,6, 2,5,11,8,1,10),
    (5,2,9,11,4,8, 3,7,1,10,12,0, 6,9,2,13,11,8, 1,5,6,3,10,7),
    (9,4,6,1,13,2, 8,0,5,12,6,11, 3,7,10,9,4,5, 2,8,11,3,7,1),
    (7,10,4,6,8,3, 1,5,2,11,9,0, 13,7,6,4,12,2, 8,3,1,9,5,10),
)
OXFORD_D = (
    (4,12,9,9,12,12, 6,3,2,2,5,7, 5,7,12,12,0,6, 12,3,7,12,2,7),
    (0,1,12,9,1,9, 11,2,0,11,5,6, 5,9,4,12,2,12, 9,6,9,10,11,0),
    (1,1,3,9,3,7, 9,5,12,9,1,1, 4,3,7,12,10,7, 7,4,9,3,2,4),
    (2,12,2,3,4,5, 12,9,10,6,12,1, 3,3,11,11,11,2, 9,6,0,12,11,7),
    (10,2,12,8,9,9, 2,10,2,11,1,11, 9,2,9,10,3,6, 9,11,7,10,11,6),
)
OXFORD_LEFT = (
    (0,0,5,7),
    (5,1,2,7),
    (0,4,4,0),
    (4,3,7,7),
)
OXFORD_RIGHT = (
    (9,0,8,11,2,3),
    (2,7,4,7,4,9),
    (3,3,10,10,12,12),
    (10,6,8,3,5,10),
    (0,7,5,1,5,7),
    (0,0,1,1,8,12),
)


def rref(rows, p):
    work = [[element % p for element in row] for row in rows]
    if not work:
        return ()
    pivot = 0
    for col in range(len(work[0])):
        choice = next((j for j in range(pivot, len(work)) if work[j][col]), None)
        if choice is None:
            continue
        work[pivot], work[choice] = work[choice], work[pivot]
        inverse = pow(work[pivot][col], -1, p)
        work[pivot] = [(x * inverse) % p for x in work[pivot]]
        lead = work[pivot]
        for j, row in enumerate(work):
            scale = row[col]
            if j != pivot and scale:
                work[j] = [(x - scale * y) % p for x, y in zip(row, lead)]
        pivot += 1
        if pivot == len(work):
            break
    return tuple(tuple(row) for row in work[:pivot])


def product(a, b, p):
    cols = tuple(zip(*b))
    return tuple(tuple(sum(x * y for x, y in zip(row, col)) % p for col in cols) for row in a)


def transform(code, left, right, p, n):
    for row in code:
        mat = tuple(tuple(row[j:j+n]) for j in range(0, len(row), n))
        yield tuple(x for y in product(product(left, mat, p), right, p) for x in y)


def verify_pair(parameters, source, target, left, right):
    p, m, n, k = parameters
    return (
        len(rref(left, p)) == m and len(rref(right, p)) == n
        and len(rref(source, p)) == k
        and rref(transform(source, left, right, p, n), p) == rref(target, p)
    )


def write_pair(path, parameters, source, target):
    p, m, n, k = parameters
    source = tuple(tuple(x % p for x in row) for row in source)
    target = tuple(tuple(x % p for x in row) for row in target)
    if len(source) != k or len(target) != k or any(len(row) != m*n for row in (*source, *target)):
        raise ValueError("incorrect matrix stack dimensions")
    with path.open("w", encoding="ascii", newline="\n") as handle:
        handle.write(" ".join(map(str, parameters)) + "\n")
        for row in (*source, *target):
            handle.write(" ".join(map(str,row)) + "\n")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def oxford(out):
    if not verify_pair(OXFORD_PARAMETERS, OXFORD_C, OXFORD_D, OXFORD_LEFT, OXFORD_RIGHT):
        raise ValueError("published witness doesn't verify after transcription")
    sha256 = write_pair(out, OXFORD_PARAMETERS, OXFORD_C, OXFORD_D)
    return {"source": OXFORD_SOURCE, "file": out.name, "parameters": OXFORD_PARAMETERS,
            "label": "equivalent", "verified_published_witness": True, "sha256": sha256}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    opts = parser.parse_args()
    print(json.dumps(oxford(opts.output), indent=2))


if __name__ == "__main__":
    main()
