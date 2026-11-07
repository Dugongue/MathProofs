"""Independent fixture integrity checks, separate from the recognizer."""
from __future__ import annotations
import json
from pathlib import Path
from collections import Counter


def gf2_rank(rows):
    piv = {}
    for row in rows:
        value = int(row)
        while value:
            k = value.bit_length()-1
            if k in piv:
                value ^= piv[k]
            else:
                piv[k] = value
                break
    return len(piv)


def inspect(incidence):
    v,b = len(incidence),len(incidence[0])
    assert all(len(row)==b and all(x in (0,1) for x in row) for row in incidence)
    columns = [sum(incidence[i][j]<<i for i in range(v)) for j in range(b)]
    rows = [sum(row[j]<<j for j in range(b)) for row in incidence]
    ks = Counter(c.bit_count() for c in columns)
    reps = Counter(r.bit_count() for r in rows)
    pairs = Counter((rows[i]&rows[j]).bit_count() for i in range(v) for j in range(i+1,v))
    return {'points':v,'blocks':b,'simple':len(set(columns))==b,
            'block_sizes':dict(ks),'replication_numbers':dict(reps),
            'pair_counts':dict(pairs),'binary_rank':gf2_rank(rows),
            'bordered_rank':gf2_rank([r|(1<<b) for r in rows]+[(1<<b)-1])}


def main():
    here = Path(__file__).resolve().parent
    records=[]
    for item in json.loads((here/'manifest.json').read_text())['fixtures']:
        fixture=json.loads((here/item['file']).read_text())
        out=inspect(fixture['incidence']); expected=fixture['expected']
        assert out['points']==expected['points'] and out['blocks']==expected['blocks']
        assert out['simple']
        assert list(out['block_sizes'])==[expected['block_size']]
        assert list(out['pair_counts'])==[expected['lambda']]
        if expected['recognized']:
            assert out['bordered_rank']==expected['bordered_rank']
        else:
            assert out['binary_rank']==expected['binary_rank']
            assert out['bordered_rank']!=expected['m']+2
        records.append({'file':item['file'],**out})
    result={'status':'PASS','scope':'exact fixture integrity, not recognizer output','fixtures':records}
    (here/'validation.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
