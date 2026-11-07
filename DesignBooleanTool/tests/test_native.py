"""Native backend differentials and direct ABI bounds tests."""
import copy
from array import array
import ctypes
import json
from pathlib import Path
import random
import sys
import unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'src'))
sys.path.insert(0,str(ROOT/'examples'))
from design_boolean.core import recognize,verify_certificate,IncidenceMatrix
from design_boolean import native
from generate import make_fixture,permuted

@unittest.skipUnless(native.available(),'Optional native library has not been built.')
class NativeTests(unittest.TestCase):
    def test_all_published_and_control_fixtures(self):
        manifest=json.loads((ROOT/'examples/manifest.json').read_text(encoding='utf-8'))
        for entry in manifest['fixtures']:
            with self.subTest(fixture=entry['file']):
                data=json.loads((ROOT/'examples'/entry['file']).read_text(encoding='utf-8'))
                x=native.recognize_native(data['incidence'])
                y=recognize(data['incidence'],backend='python')
                self.assertEqual(x.status,y.status)
                self.assertEqual(x.certificate,y.certificate)
                if x.recognized:self.assertTrue(verify_certificate(data['incidence'],x.certificate).valid)

    def test_dense_packed_and_labels(self):
        data=make_fixture('plateaued-stabilization',7)['incidence']
        packed=IncidenceMatrix.from_rows(data)
        labels={'point_labels':list(range(len(data))),'block_labels':list(range(len(data[0])))}
        a=native.recognize_native(data,**labels)
        b=native.recognize_native(packed,**labels)
        c=recognize(data,backend='python',**labels)
        self.assertEqual(a.certificate,b.certificate)
        self.assertEqual(a.certificate,c.certificate)

    def test_typed_buffer_and_generic_iterable_rows(self):
        data=make_fixture('quadratic-family',4)['incidence']
        expected=recognize(data,backend='python').certificate
        for rows in [[array('I',row) for row in data], [memoryview(array('I',row)) for row in data], [tuple(row) for row in data], (iter(row) for row in data)]:
            result=native.recognize_native(rows)
            self.assertTrue(result.recognized)
            self.assertEqual(result.certificate,expected)

    def test_random_permutations(self):
        data=make_fixture('quadratic-family',6)['incidence']
        rng=random.Random(20261106)
        for _ in range(12):
            rows=list(range(len(data)));cols=list(range(len(data[0])))
            rng.shuffle(rows);rng.shuffle(cols)
            changed=[[data[i][j] for j in cols] for i in rows]
            a=native.recognize_native(changed);b=recognize(changed,backend='python')
            self.assertEqual(a.certificate,b.certificate)
            self.assertTrue(verify_certificate(changed,a.certificate).valid)

    def test_malformed_and_unsupported(self):
        for data in [[],[[0,1],[1]],[[0,2],[1,0]],[[0,1.0],[1,0]],[[0,-1],[1,0]],[[0,'1'],[1,0]],[[0,256],[1,0]],[[0,float('nan')],[1,0]],[[0,1],[1,0]]]:
            with self.subTest(data=repr(data)):
                self.assertEqual(native.recognize_native(data).status,recognize(data,backend='python').status)
        fixture=make_fixture('quadratic-family',4)['incidence']
        self.assertEqual(native.recognize_native(fixture,point_labels=['bad']).status,'invalid_input')
        self.assertEqual(native.recognize_native(IncidenceMatrix((-1,),16)).status,'invalid_input')

    def test_mutations_are_rejected(self):
        data=make_fixture('quadratic-family',6)['incidence'];rng=random.Random(731)
        for _ in range(30):
            changed=[row[:] for row in data]
            changed[rng.randrange(len(data))][rng.randrange(len(data[0]))]^=1
            self.assertEqual(native.recognize_native(changed).status,'not_recognized')

    def test_generated_larger(self):
        data=make_fixture('quadratic-family',8)['incidence']
        a=native.recognize_native(data)
        self.assertTrue(a.recognized)
        self.assertTrue(verify_certificate(data,a.certificate).valid)
        self.assertEqual(a.certificate,recognize(data,backend='python').certificate)

    def test_certificate_and_explicit_validation_agree(self):
        manifest=json.loads((ROOT/'examples/manifest.json').read_text(encoding='utf-8'))
        for item in manifest['fixtures']:
            data=json.loads((ROOT/'examples'/item['file']).read_text())['incidence']
            certificate=native.recognize_native(data,validation='certificate')
            explicit=native.recognize_native(data,validation='explicit')
            self.assertEqual(certificate.status,explicit.status)
            self.assertEqual(certificate.certificate,explicit.certificate)
        self.assertEqual(native.recognize_native(data,validation='bad').status,'invalid_input')

    def test_direct_abi_bounds(self):
        lib=native._library()
        source=(ctypes.c_ubyte*1)(0);out=(ctypes.c_uint32*1)();packed=(ctypes.c_ubyte*1)();rank=ctypes.c_uint32();message=ctypes.create_string_buffer(128)
        for v,b,mode in [(0,16,0),(16,16,2),(16,16,0),(2**31,2**31,0)]:
            with self.subTest(v=v,b=b,mode=mode):
                code=lib.db_recognize(source,1,v,b,mode,1,out,1,packed,1,ctypes.byref(rank),message,len(message))
                self.assertIn(code,(2,3))
        self.assertEqual(lib.db_recognize(None,1,16,16,0,1,out,1,packed,1,ctypes.byref(rank),message,len(message)),2)

if __name__=='__main__':unittest.main()
