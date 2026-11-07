import csv
import gzip
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from design_boolean.io import load_incidence, read_text
from independent import support_design, quadratic_truth

ROOT = Path(__file__).resolve().parents[1]


class InterfaceTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.folder = Path(self.temp.name)
        self.matrix = support_design(quadratic_truth(4))
        self.input = self.folder/'design.json'
        self.input.write_text(json.dumps({'incidence':self.matrix}),encoding='utf-8')

    def tearDown(self):
        self.temp.cleanup()

    def command(self,*args):
        env=dict(os.environ)
        env['PYTHONPATH']=str(ROOT/'src')
        return subprocess.run([sys.executable,'-m','design_boolean',*map(str,args)],
                              cwd=self.folder,env=env,capture_output=True,text=True)

    def test_cli_roundtrip(self):
        cert=self.folder/'certificate.json'
        function=self.folder/'function.json'
        result=self.command('recognize',self.input,'--certificate-out',cert,'--function-out',function)
        self.assertEqual(result.returncode,0,result.stderr)
        response=json.loads(result.stdout)
        self.assertEqual(response['status'],'recognized')
        self.assertEqual(len(json.loads(function.read_text(encoding='utf-8'))['truth_table']),16)
        verified=self.command('verify',self.input,cert)
        self.assertEqual(verified.returncode,0,verified.stderr)
        self.assertTrue(json.loads(verified.stdout)['valid'])

    def test_cli_certificate_tamper(self):
        result=json.loads(self.command('recognize',self.input).stdout)
        result['certificate']['truth_table'][0]^=1
        cert=self.folder/'bad.json'
        cert.write_text(json.dumps(result),encoding='utf-8')
        checked=self.command('verify',self.input,cert)
        self.assertEqual(checked.returncode,1)
        self.assertFalse(json.loads(checked.stdout)['valid'])

    def test_csv_and_gzip(self):
        csv_path=self.folder/'design.csv'
        with csv_path.open('w',newline='',encoding='utf-8') as handle:
            csv.writer(handle).writerows(self.matrix)
        for path in (csv_path,self.folder/'design.json.gz'):
            if path.suffix=='.gz':
                with gzip.open(path,'wt',encoding='utf-8') as handle:
                    json.dump(self.matrix,handle)
            result=self.command('recognize',path)
            self.assertEqual(result.returncode,0,result.stderr)
            self.assertEqual(json.loads(result.stdout)['status'],'recognized')

    def test_block_list_input(self):
        blocks=[[p for p,row in enumerate(self.matrix) if row[b]] for b in range(16)]
        path=self.folder/'blocks.json'
        path.write_text(json.dumps({'point_count':16,'blocks':blocks}),encoding='utf-8')
        result=self.command('recognize',path)
        self.assertEqual(result.returncode,0,result.stderr)

    def test_bounds(self):
        for args in [('--max-cells','8'),('--max-bytes','8'),('--max-cells','0')]:
            result=self.command('recognize',self.input,*args)
            self.assertEqual(result.returncode,2,result.stdout)
        # Byte limit applies to decompressed size too.
        path=self.folder/'large.json.gz'
        with gzip.open(path,'wt',encoding='utf-8') as handle:
            handle.write(' '*10000)
        with self.assertRaises(ValueError):
            read_text(path,50)

    def test_bad_payloads(self):
        payloads=[{'incidence':[[0,1],[1]]}, {'incidence':[[0,2]]},
                  {'incidence':[[0,1.0]]}, {'incidence':[[0,float('nan')]]},
                  {'incidence':[[0,'1']]}, {'incidence':self.matrix,'point_labels':['x']},
                  {'point_count':16,'blocks':[[0,0]]},
                  {'incidence':self.matrix,'blocks':[]}]
        for payload in payloads:
            with self.subTest(payload=str(payload)[:30]):
                self.input.write_text(json.dumps(payload),encoding='utf-8')
                result=self.command('recognize',self.input)
                self.assertEqual(result.returncode,2,result.stdout)


if __name__=='__main__':
    unittest.main()
