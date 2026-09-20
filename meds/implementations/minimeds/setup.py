
"""Fetch the pinned miniMEDS dependency locally, verify it, and apply our edits.
The downloaded/generated dependency is gitignored and is not part of the release.
Do not redistribute it without resolving its upstream license terms.
"""
from pathlib import Path
import argparse,hashlib,io,json,re,shutil,urllib.request,zipfile
b=Path(__file__).resolve().parent
lock=json.loads((b/'source-lock.json').read_text(encoding='utf-8'));edits=json.loads((b/'replacements.json').read_text(encoding='utf-8'))
def span(s,name):
 m=re.search(r'(?m)^(?:static\s+)?(?:inline\s+)?(?:void|GFq_t|int)\s+'+re.escape(name)+r'\s*\(',s)
 if not m:raise ValueError('Missing function '+name)
 a=s.index('{',m.end());i=a+1;depth=1
 while depth:depth+=(s[i]=='{')-(s[i]=='}');i+=1
 return m.start(),a,i
parser=argparse.ArgumentParser();parser.add_argument('--local-source',type=Path,help='Existing pinned ref directory instead of network download');args=parser.parse_args()
u=b/'.deps/upstream/ref';c=b/'.deps/candidate';u.mkdir(parents=True,exist_ok=True)
if args.local_source:
 for name in lock['upstream_sha256']:shutil.copyfile(args.local_source/name,u/name)
else:
 url='https://codeload.github.com/'+lock['repository']+'/zip/'+lock['commit']
 with urllib.request.urlopen(url,timeout=60) as response:archive=zipfile.ZipFile(io.BytesIO(response.read()))
 for name in lock['upstream_sha256']:
  matches=[p for p in archive.namelist() if p.endswith('/ref/'+name)]
  if len(matches)!=1:raise ValueError('Ambiguous/missing archive member '+name)
  (u/name).write_bytes(archive.read(matches[0]))
for name,h in lock['upstream_sha256'].items():
 if hashlib.sha256((u/name).read_bytes()).hexdigest()!=h:raise ValueError('Upstream hash mismatch: '+name)
shutil.copytree(u,c,dirs_exist_ok=True);shutil.copyfile(b/'fast_dot.h',c/'fast_dot.h')
for filename in ['GFq.h','matrixmod.c','contract.c']:
 s=(c/filename).read_text(encoding='utf-8')
 for name,body in edits[filename].items():
  _,a,z=span(s,name);s=s[:a]+body+s[z:]
 if filename=='GFq.h':s=s.replace('#include "config.h"','#include "config.h"\n#include "fast_dot.h"',1)
 if filename=='matrixmod.c':
  pos=s.index('void TT_NNN(');s=s[:pos]+edits['tensor_helper']+'\n'+s[pos:]
  a,_,z=span(s,'pmod_mat_syst_ct');s=s[:a]+s[a:z].replace('uint64_t','uint32_t').replace('int64_t','int32_t')+s[z:]
 (c/filename).write_text(s,encoding='utf-8')
p=c/'kernel.c';s=p.read_text(encoding='utf-8');a,_,z=span(s,'right_kernel_corank1_ct_fixed_piv');s=s[:a]+s[a:z].replace('uint64_t','uint32_t').replace('int64_t','int32_t')+s[z:];p.write_text(s,encoding='utf-8')
# The inserted helper has different whitespace/comments from the historical
# integrated file. Save hashes of this precisely reproducible generated tree.
receipt={'commit':lock['commit'],'upstream_verified':True,'generated_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in c.iterdir() if p.suffix in ['.c','.h']}}
(b/'.deps/setup-receipt.json').write_text(json.dumps(receipt,indent=2),encoding='utf-8')
print('Pinned dependency verified; generated candidate in',c)
