"""Decode public matrix-code pairs from the MEDS v1.1 official KAT archive."""
import argparse
import hashlib
import json
import tarfile
from pathlib import Path

from dataset_meds import rref, write_pair

SOURCE = "https://www.meds-pqc.org/KAT/MEDS-KAT-2023-07-26.tgz"
ARCHIVE_SHA256 = "4045fbde6d2c6a4ccce1df5c46230e227ad5961047a4d172cf502622b3250760"
PARAMETERS = {
    "toy": (8191, 10, 10, 10, 4),
    "MEDS9923": (4093, 14, 14, 14, 4),
    "MEDS13220": (4093, 14, 14, 14, 5),
    "MEDS41711": (4093, 22, 22, 22, 4),
    "MEDS55604": (4093, 22, 22, 22, 5),
    "MEDS134180": (2039, 30, 30, 30, 5),
    "MEDS167717": (2039, 30, 30, 30, 6),
}
PUBLIC_SEED_BYTES = 32


def records(lines, count):
    index = None
    emitted = 0
    for raw in lines:
        if raw.startswith(b"count = "):
            index = int(raw[len(b"count = "):])
        if index is not None and raw.startswith(b"pk = "):
            yield index, bytes.fromhex(raw[len(b"pk = "):].decode("ascii"))
            emitted += 1
            if emitted == count:
                return
            index = None


def packed_values(data, p, count):
    width = (p - 1).bit_length()
    mask = (1 << width) - 1
    if len(data) != (count * width + 7) // 8:
        raise ValueError("invalid packed field vector length")
    result = []
    buffer = bits = 0
    for byte in data:
        buffer |= byte << bits
        bits += 8
        while bits >= width and len(result) < count:
            result.append(buffer & mask)
            bits -= width
            buffer >>= width
    if buffer or len(result) != count or any(x >= p for x in result):
        raise ValueError("noncanonical packed field vector")
    return result


def shake_values(seed, p, count):
    width = (p - 1).bit_length()
    item_bytes = (width + 7) // 8
    mask = (1 << width) - 1
    shake = hashlib.shake_256(seed)
    result = []
    position = 0
    while len(result) < count:
        stream = shake.digest(max(2 * position, count * item_bytes + 64))
        while position + item_bytes <= len(stream) and len(result) < count:
            value = int.from_bytes(stream[position:position + item_bytes], "little") & mask
            position += item_bytes
            if value < p:
                result.append(value)
    return result


def systematic_code(tail, k, columns):
    width = columns - k
    return [[int(i == j) for j in range(k)] + tail[i * width:(i + 1) * width]
            for i in range(k)]


def decode(pk, params, target_index):
    p, m, n, k, s = params
    if not 1 <= target_index < s:
        raise ValueError(f"expected public code index in 1..{s - 1}")
    if m != n or m != k:
        raise ValueError("only the published square KAT parameters are supported")

    width = (p - 1).bit_length()
    public_count = n + (k - 2) * (m * n - k)
    public_bytes = (public_count * width + 7) // 8
    if len(pk) != PUBLIC_SEED_BYTES + (s - 1) * public_bytes:
        raise ValueError("invalid KAT public-key length")

    seed = pk[:PUBLIC_SEED_BYTES]
    g0 = systematic_code(shake_values(seed, p, k * (m * n - k)), k, m * n)
    start = PUBLIC_SEED_BYTES + (target_index - 1) * public_bytes
    data = packed_values(pk[start:start + public_bytes], p, public_count)
    gi = systematic_code([0] * (k * (m * n - k)), k, m * n)
    for i in range(1, m):
        gi[0][i * (n + 1)] = 1
    for i in range(1, m - 1):
        gi[1][i * (n + 1) + 1] = 1
    gi[1][m * n - n:] = data[:n]
    for i in range(2, k):
        start = n + (i - 2) * (m * n - k)
        gi[i][k:] = data[start:start + m * n - k]
    return g0, gi


def extract(archive, out, count, target, options):
    with archive.open("rb") as handle:
        observed = hashlib.file_digest(handle, "sha256").hexdigest()
    if ARCHIVE_SHA256 != observed:
        raise ValueError("unexpected KAT archive SHA-256")
    found = set()
    manifests = []
    requested = set(options or PARAMETERS)
    out.mkdir(parents=True, exist_ok=True)
    with tarfile.open(archive, "r|gz") as data:
        for info in data:
            file = Path(info.name).name
            if not info.isfile() or not file.startswith("PQCsignKAT_") or not file.endswith(".rsp"):
                continue
            name = file[len("PQCsignKAT_"):-len(".rsp")]
            if name not in requested:
                continue
            if name in found:
                raise ValueError("duplicate parameter entry in KAT archive")
            found.add(name)
            key = PARAMETERS[name]
            parameters = key[:4]
            with data.extractfile(info) as stream:
                selected = tuple(records(stream, count))
            if len(selected) != count:
                raise ValueError("fewer complete KAT records than requested")
            for index, pk in selected:
                source, dest = decode(pk, key, target)
                if len(rref(source, key[0])) != key[3] or len(rref(dest, key[0])) != key[3]:
                    raise ValueError("a decoded code did not have the published dimension")
                path = out / f"kat-{name.lower()}-{index:03d}-g0-to-g{target}.txt"
                digest = write_pair(path, parameters, source, dest)
                manifests.append({"source": SOURCE, "archive_sha256": ARCHIVE_SHA256,
                                  "member": file, "count": index, "code_index": target,
                                  "file": path.name, "parameters": parameters,
                                  "label": "equivalent-by-official-key-generation",
                                  "sha256": digest})
    if found != requested:
        raise ValueError(f"missing KAT parameter entries {sorted(requested - found)}")
    return sorted(manifests, key=lambda m: m["file"])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("archive", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--records", type=int, default=1)
    parser.add_argument("--target", type=int, default=1)
    parser.add_argument("--parameter", choices=tuple(PARAMETERS), action="append")
    opts = parser.parse_args()
    if opts.records < 1:
        parser.error("--records must be positive")
    manifest = extract(opts.archive, opts.output, opts.records, opts.target, opts.parameter)
    print(json.dumps(manifest, indent=2))


if __name__ == "__main__":
    main()
