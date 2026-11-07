"""Refresh the generated source-package mirror; edit native/design_boolean.cpp."""
from pathlib import Path
import shutil
root=Path(__file__).resolve().parents[1]
target=root/"src/design_boolean/_native_src/recognizer.cpp"
target.parent.mkdir(exist_ok=True)
shutil.copyfile(root/"native/design_boolean.cpp",target)
print("Native source-package mirror refreshed.")
