"""Build this pure-Python wheel offline using the standard library only."""
import base64
import csv
import hashlib
import io
from pathlib import Path
import zipfile

ROOT=Path(__file__).resolve().parents[1]
VERSION="0.2.0"
DIST=f"design_boolean-{VERSION}.dist-info"

def main():
    files={}
    for source in sorted((ROOT/"src/design_boolean").glob("*.py")):
        files["design_boolean/"+source.name]=source.read_bytes()
    files["design_boolean/_native_src/recognizer.cpp"]=(ROOT/"native/design_boolean.cpp").read_bytes()
    files[DIST+"/METADATA"]=(f"Metadata-Version: 2.1\nName: design-boolean\nVersion: {VERSION}\nSummary: Recognize and reconstruct plateaued Boolean functions from incidence designs\nRequires-Python: >=3.10\nLicense: Apache-2.0\nAuthor: MathProofs contributors\n\nExact arithmetic, a Python API, a CLI, and directly checkable reconstruction certificates.\n").encode()
    files[DIST+"/WHEEL"]=b"Wheel-Version: 1.0\nGenerator: design-boolean-stdlib-builder\nRoot-Is-Purelib: true\nTag: py3-none-any\n"
    files[DIST+"/entry_points.txt"]=b"[console_scripts]\ndesign-boolean = design_boolean.cli:main\n"
    for name in ("LICENSE","NOTICE"):
        files[DIST+"/licenses/"+name]=(ROOT/name).read_bytes()
    record=io.StringIO(newline="")
    writer=csv.writer(record,lineterminator="\n")
    for name,raw in sorted(files.items()):
        digest=base64.urlsafe_b64encode(hashlib.sha256(raw).digest()).decode().rstrip("=")
        writer.writerow([name,"sha256="+digest,len(raw)])
    writer.writerow([DIST+"/RECORD","",""])
    files[DIST+"/RECORD"]=record.getvalue().encode()
    destination=ROOT/"dist"/f"design_boolean-{VERSION}-py3-none-any.whl"
    destination.parent.mkdir(exist_ok=True)
    with zipfile.ZipFile(destination,"w",compression=zipfile.ZIP_DEFLATED) as wheel:
        for name,raw in sorted(files.items()):
            info=zipfile.ZipInfo(name,date_time=(2020,1,1,0,0,0))
            info.create_system=3
            info.external_attr=0o100644 << 16
            info.compress_type=zipfile.ZIP_DEFLATED
            wheel.writestr(info,raw)
    print(destination.name)

if __name__=="__main__":main()
