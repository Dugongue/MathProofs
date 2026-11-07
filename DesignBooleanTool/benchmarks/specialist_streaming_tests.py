"""Checkpoint transport tests using a fake process, never launching GAP."""
import contextlib
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import gap_streaming as adapter
from reference import recognize


class StreamingTests(unittest.TestCase):
    def test_timeout_preserves_complete_case_and_resume(self):
        with tempfile.TemporaryDirectory(prefix='gap-transport-test-') as td:
            root=Path(td);runtime=root/'runtime';runtime.mkdir();(runtime/'gap.exe').write_bytes(b'not launched')
            output=root/'report.json';checkpoints=root/'checkpoints'
            fixtures=adapter.fixtures_for(7,['published-example-1','published-example-2'])
            result=recognize(fixtures[0]['incidence'])
            self.assertEqual(result['status'],'recognized')
            class FakeProcess:
                def __init__(self,*a,**kw):
                    self.stopped=False
                    adapter.write_json(checkpoints/'backend.json',{'gap':'fake-transport-test','design':'fake-transport-test'})
                    adapter.write_json(checkpoints/'case-000.json',{'id':fixtures[0]['id'],'samples_ns':[123456],'result':result})
                def poll(self):return 0 if self.stopped else None
                def terminate(self):self.stopped=True
                def kill(self):self.stopped=True
                def wait(self,timeout=None):self.stopped=True;return 0
            args=['--gap-root',str(runtime),'--cases','published-example-1,published-example-2','--repeats','1','--max-m','7',
                  '--timeout','.01','--output',str(output),'--checkpoint-dir',str(checkpoints)]
            with patch.object(adapter.subprocess,'Popen',FakeProcess),contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(adapter.main(args),124)
            report=json.loads(output.read_text())
            self.assertEqual(report['status'],'TIMEOUT')
            self.assertEqual([x['id'] for x in report['cases']],['published-example-1'])
            self.assertEqual(report['pending_cases'],['published-example-2'])
            self.assertTrue(report['cases'][0]['independent_certificate_verified'])
            with contextlib.redirect_stdout(io.StringIO()) as captured:
                self.assertEqual(adapter.main(args+['--resume','--prepare-only']),0)
            self.assertIn('PREPARED 1 pending',captured.getvalue())

    def test_resume_rejects_changed_contract(self):
        with tempfile.TemporaryDirectory(prefix='gap-transport-test-') as td:
            root=Path(td);output=root/'out.json';cp=root/'cp'
            args=['--gap-root',str(root),'--cases','published-example-2','--repeats','1','--max-m','7','--output',str(output),'--checkpoint-dir',str(cp),'--prepare-only']
            with contextlib.redirect_stdout(io.StringIO()):self.assertEqual(adapter.main(args),0)
            changed=list(args);changed[changed.index('--repeats')+1]='2'
            with contextlib.redirect_stderr(io.StringIO()),self.assertRaises(SystemExit):adapter.main(changed+['--resume'])

    def test_unknown_case_rejected(self):
        with self.assertRaises(ValueError):adapter.fixtures_for(7,['not-a-fixture'])

if __name__=='__main__':unittest.main()
