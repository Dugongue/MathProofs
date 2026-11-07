"""Bounded JSON/CSV input and explicit point-row/block-column orientation."""
import csv
import gzip
import json
from pathlib import Path
from .core import IncidenceMatrix

DEFAULT_MAX_CELLS = 16_000_000
DEFAULT_MAX_BYTES = 128_000_000

def read_text(path, max_bytes=DEFAULT_MAX_BYTES):
    path = Path(path)
    opener = gzip.open if path.suffix.lower() == ".gz" else open
    with opener(path, "rb") as handle:
        raw = handle.read(max_bytes+1)
    if len(raw)>max_bytes:
        raise ValueError("Input exceeds the byte limit; increase --max-bytes for trusted larger inputs.")
    return raw.decode("utf-8-sig")

def load_incidence(path, *, max_cells=DEFAULT_MAX_CELLS, max_bytes=DEFAULT_MAX_BYTES, packed=True):
    text = read_text(path,max_bytes)
    suffixes = [s.lower() for s in Path(path).suffixes]
    if ".csv" in suffixes:
        rows = [[int(cell.strip()) for cell in row] for row in csv.reader(text.splitlines()) if row]
        data = {"incidence":rows}
    else:
        data = json.loads(text)
        if isinstance(data,list):
            data = {"incidence":data}
    if not isinstance(data,dict):
        raise ValueError("Expected a JSON incidence array or an object with incidence/blocks.")
    if "incidence" in data and "blocks" in data:
        raise ValueError("Specify exactly one of incidence and blocks.")
    labels = {k:data[k] for k in ("point_labels","block_labels") if k in data}
    if "incidence" in data:
        rows = data["incidence"]
        if not isinstance(rows,list) or not rows or not isinstance(rows[0],list):
            raise ValueError("incidence must be a nonempty list of point rows.")
        if len(rows)*len(rows[0])>max_cells:
            raise ValueError("Incidence exceeds --max-cells.")
        matrix = IncidenceMatrix.from_rows(rows) if packed else rows
    elif "blocks" in data:
        n = data.get("point_count")
        blocks = data["blocks"]
        if isinstance(n,bool) or not isinstance(n,int) or n<1 or not isinstance(blocks,list):
            raise ValueError("Block input requires positive integer point_count and a list of blocks.")
        if n*len(blocks)>max_cells:
            raise ValueError("Incidence exceeds --max-cells.")
        matrix = IncidenceMatrix.from_blocks(n,blocks)
    else:
        raise ValueError("JSON object requires incidence or point_count plus blocks.")
    return matrix,labels

def write_json(value,path=None):
    text = json.dumps(value,ensure_ascii=(path is None),indent=2,allow_nan=False)+"\n"
    if path is None:
        print(text,end="")
    else:
        Path(path).write_text(text,encoding="utf-8",newline="\n")
