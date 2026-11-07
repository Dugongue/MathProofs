"""Exhaust all 65,536 four-variable truth tables as rank-pass candidate designs.

This is a finite stress check, not a universal software proof. Independent Walsh
coefficients are calculated by packed truth-table Hamming distances, not FWHT.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import sys
import time
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/"src"))
from design_boolean import IncidenceMatrix, recognize, verify_certificate
from design_boolean.native import recognize_native

def main():
    p=argparse.ArgumentParser();p.add_argument("--output",type=Path,default=Path(__file__).with_name("exhaustive-results.json"));a=p.parse_args()
    chars=[sum(((u&x).bit_count()&1)<<x for x in range(16)) for u in range(16)]
    counts=Counter();start=time.perf_counter()
    for f in range(1<<16):
        w=[16-2*(f^c).bit_count() for c in chars]
        expected=all(abs(v)==4 for v in w)
        rows=tuple(f^c^(65535 if v<0 else 0) for c,v in zip(chars,w))
        matrix=IncidenceMatrix(rows,16)
        native=recognize_native(matrix)
        explicit=recognize_native(matrix,validation="explicit")
        py=recognize(matrix,backend="python")
        if not (native.recognized==explicit.recognized==py.recognized==expected):
            raise AssertionError((f,native.status,explicit.status,py.status,expected))
        if expected:
            assert native.certificate==py.certificate==explicit.certificate
            assert verify_certificate(matrix,native.certificate).valid
        counts["recognized" if expected else "rejected"]+=1
    result={"status":"PASS","truth_tables":1<<16,"counts":dict(counts),"scope":"Every four-variable truth table converted to a normalized-rank-pass candidate; not every binary incidence matrix", "methods":["native-certificate","native-explicit","python-explicit"],"independent_expectation":"Walsh coefficients from truth-mask Hamming distances","wall_seconds":time.perf_counter()-start}
    a.output.write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8",newline="\n")
    print(json.dumps(result))
if __name__=="__main__":main()
