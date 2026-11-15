"""UCI Semeion binary images as four-way tensors in two fixed layouts.

Source DOI 10.24432/C5SC8V, CC BY 4.0. Pixel values are unchanged.
"""
import argparse
from hashlib import sha256
from itertools import product
import json
from pathlib import Path
from zipfile import ZipFile

ARCHIVE_HASH = "6fb091394714cddda5751d4e1c2781ab094e7cf15de07917fb40e581f19efc75"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("archive", type=Path)
    parser.add_argument("output_dir", type=Path)
    args = parser.parse_args()
    if sha256(args.archive.read_bytes()).hexdigest() != ARCHIVE_HASH:
        raise ValueError("Unexpected source archive bytes.")
    with ZipFile(args.archive) as archive:
        lines = archive.read("semeion.data").decode("ascii").splitlines()
    if len(lines) != 1593:
        raise ValueError("Unexpected number of records.")
    args.output_dir.mkdir(parents=True, exist_ok=True)
    with (args.output_dir / "semeion-native.jsonl").open("w", encoding="utf-8") as native, \
            (args.output_dir / "semeion-regrouped.jsonl").open("w", encoding="utf-8") as regrouped:
        for i, line in enumerate(lines):
            tokens = line.split()
            values = tokens[:256]
            if len(tokens) != 266 or any(x not in ("0.0000", "1.0000") for x in values):
                raise ValueError("Unexpected binary pixel layout.")
            pixels = [int(x[0]) for x in values]
            source = {"id": f"semeion-{i+1:04}", "source": "https://doi.org/10.24432/C5SC8V",
                      "field": 2, "dims": [4] * 4}
            a = dict(source, family="semeion-native", entries=pixels)
            other = [pixels[((r * 4 + s) * 4 + c) * 4 + t]
                     for r, c, s, t in product(range(4), repeat=4)]
            b = dict(source, family="semeion-regrouped", entries=other)
            native.write(json.dumps(a, separators=(",", ":")) + "\n")
            regrouped.write(json.dumps(b, separators=(",", ":")) + "\n")


if __name__ == "__main__":
    main()
