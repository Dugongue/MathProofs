"""Read first-four-factor contingency tensors from the Sloane OA catalogue."""
from argparse import ArgumentParser
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from hashlib import sha256
from itertools import combinations, product
from pathlib import Path
from time import sleep
import json
import re
import ssl
from urllib.error import URLError
from urllib.request import urlopen

INDEX = 'https://neilsloane.com/oadir/index.html'
ORIGIN = 'https://neilsloane.com/oadir/'


def read_http(url):
    context = ssl.SSLContext(ssl.PROTOCOL_TLS_CLIENT)
    context.load_default_certs()
    error = None
    for attempt in range(3):
        try:
            with urlopen(url,timeout=15,context=context) as response:
                return response.read()
        except (URLError,TimeoutError) as exc:
            error = exc
            sleep(0.25*(attempt+1))
    raise OSError(str(error)) from error


def names_in_catalog(index):
    names = set(re.findall(r'href="(oa\.\d+\.\d+\.\d+\.\d+(?:\.[a-z]+)?\.txt)"', index))
    for name in sorted(names):
        n,k,q,t = map(int,name.split('.')[1:5])
        if n<=256 and k>=4 and 3<=q<=9 and t>=2:
            yield name


def parse_array(name,payload):
    n,k,q,t = map(int,name.split('.')[1:5])
    lines = payload.decode('ascii').splitlines()
    digit_rows = [s.strip() for s in lines[:n]]
    if len(digit_rows) != n or any(len(row)!=k or not re.fullmatch(r'[0-9]+',row)
                                   for row in digit_rows):
        raise ValueError('Wrong pure-level catalogue row format')
    full = [tuple(map(int,row)) for row in digit_rows]
    if not all(0<=a<q for row in full for a in row):
        raise ValueError('Published symbol outside range')
    left = [row[:4] for row in full]
    for a,b in combinations(range(4),2):
        counts = Counter((row[a],row[b]) for row in left)
        if len(counts) != q*q or set(counts.values()) != {n//(q*q)}:
            raise ValueError('First four columns fail declared pair balance')
    weights = Counter(left)
    support = sorted(p for p,k in weights.items() if k&1)
    return {'id':name.removesuffix('.txt'), 'source':ORIGIN+name,
            'family':'sloane-oa-first-four-f2' if k>4 else 'sloane-oa-four-f2',
            'field':2, 'dims':[q]*4, 'ones':support, 'runs':n, 'source_width':k,
            'strength':t, 'axis_order':[0,1,2,3], 'source_sha256':sha256(payload).hexdigest()}


def get_record(name):
    try:
        return name,parse_array(name,read_http(ORIGIN+name)),None
    except (OSError,ValueError) as err:
        return name,None, type(err).__name__+': '+str(err)


def run():
    parser=ArgumentParser(description=__doc__)
    parser.add_argument('outdir', type=Path)
    args=parser.parse_args()
    index=read_http(INDEX)
    paths=list(names_in_catalog(index.decode('utf-8')))
    with ThreadPoolExecutor(max_workers=8) as pool:
        records=list(pool.map(get_record,paths))
    failures={name:err for name,row,err in records if err}
    rows=[row for name,row,err in records if row]
    args.outdir.mkdir(parents=True,exist_ok=True)
    target=args.outdir/'data_sloane_oa.jsonl'
    with target.open('w',encoding='utf-8',newline='\n') as f:
        for row in rows:
            f.write(json.dumps(row,separators=(',',':'))+'\n')
    d = {'source_catalogue':INDEX, 'matching_links':len(paths), 'normalized':len(rows),
         'selection':'Pure-level linked text entries with 3 to 9 levels, at least four columns, at most 256 runs and strength at least two.',
         'conversion':'Use the first four listed factors; count row multiplicities modulo two.',
         'license_note':'No explicit redistribution license found for the Sloane catalogue. Fetch original data from source URLs. Generated JSONL was used locally.',
         'download_failures':failures, 'normalized_sha256':sha256(target.read_bytes()).hexdigest(),
         'sources':[{k:row[k] for k in ['id','source','source_sha256','runs','source_width','strength']} for row in rows]}
    (args.outdir/'data_sloane_oa_manifest.json').write_text(json.dumps(d,indent=2)+'\n',encoding='utf-8')
    print(f'{len(rows)}/{len(paths)} sources normalized; {len(failures)} unavailable')
    for name,err in failures.items():
        print(name,err)


if __name__=='__main__':
    run()
