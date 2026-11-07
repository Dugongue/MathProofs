"""Backend selection and the native CLI dense-input route."""
import contextlib
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/"src"))
from design_boolean import recognize
from design_boolean import native
from design_boolean.cli import main

class DispatchTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.matrix=json.loads((ROOT/"examples/published-example-2.json").read_text())["incidence"]

    def test_explicit_python_never_probes_native(self):
        with mock.patch.object(native,"available",side_effect=AssertionError("native probe")):
            self.assertEqual(recognize(self.matrix,backend="python").diagnostics["backend"],"python")

    def test_auto_falls_back_when_library_unavailable(self):
        with mock.patch.object(native,"available",return_value=False):
            result=recognize(self.matrix)
            self.assertTrue(result.recognized)
            self.assertEqual(result.diagnostics["backend"],"python")

    def test_unknown_backend_is_not_a_design_rejection(self):
        with self.assertRaises(ValueError):recognize(self.matrix,backend="unknown")

    def test_unavailable_backend_has_distinct_cli_exit(self):
        with tempfile.TemporaryDirectory() as folder:
            path=Path(folder)/"matrix.json";path.write_text(json.dumps(self.matrix))
            error=io.StringIO()
            with mock.patch.object(native,"_library",side_effect=native.NativeUnavailable("build the backend")),contextlib.redirect_stderr(error):
                self.assertEqual(main(["recognize",str(path),"--backend","native"]),4)
            self.assertEqual(json.loads(error.getvalue())["status"],"backend_error")

    def test_unicode_labels_round_trip_through_cli_json(self):
        with tempfile.TemporaryDirectory() as folder:
            path=Path(folder)/"matrix.json"
            labels=["α"+str(i) for i in range(len(self.matrix))]
            path.write_text(json.dumps({"incidence":self.matrix,"point_labels":labels}),encoding="utf-8")
            output=io.StringIO()
            with contextlib.redirect_stdout(output):
                self.assertEqual(main(["recognize",str(path)]),0)
            output.getvalue().encode("ascii")
            self.assertEqual(json.loads(output.getvalue())["certificate"]["point_labels"],labels)

    @unittest.skipUnless(native.available(),"Native library not built")
    def test_native_cli_does_not_pack_dense_input_in_python(self):
        with tempfile.TemporaryDirectory() as folder:
            path=Path(folder)/"matrix.json";out=Path(folder)/"out.json";path.write_text(json.dumps(self.matrix))
            with mock.patch("design_boolean.io.IncidenceMatrix.from_rows",side_effect=AssertionError("unnecessary dense packing")):
                self.assertEqual(main(["recognize",str(path),"--backend","native","-o",str(out)]),0)
            self.assertEqual(json.loads(out.read_text())["diagnostics"]["backend"],"native")

if __name__=="__main__":unittest.main()
