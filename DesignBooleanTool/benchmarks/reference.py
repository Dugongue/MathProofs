"""Independent normalized-TSDP baseline with full reconstruction.

The closure test implements the triple-symmetric-difference characterization
using a normalized family containing zero. It checks every unordered pair;
it is not the deliberately slower literal triple enumeration. No core helper
is used in its arithmetic, parameter validation or reconstruction.
"""


def parity(x):
    return x.bit_count() & 1


def rank(values):
    pivots={}
    for v in values:
        while v:
            lead=v.bit_length()-1
            if lead in pivots:v^=pivots[lead]
            else:pivots[lead]=v;break
    return len(pivots)


def transform(truth):
    a=[1-2*b for b in truth]
    stride=1
    while stride<len(a):
        for start in range(0,len(a),2*stride):
            for j in range(start,start+stride):
                x,y=a[j],a[j+stride];a[j],a[j+stride]=x+y,x-y
        stride*=2
    return a


def verify(matrix,cert):
    truth=cert['truth_table'];coords=cert['block_coordinates']
    freqs=cert['point_frequencies'];offsets=cert['point_offsets'];amp=cert['amplitude']
    m=len(truth).bit_length()-1
    if sorted(coords)!=list(range(len(truth))) or len(freqs)!=len(matrix):return False
    w=transform(truth)
    if set(freqs)!={i for i,x in enumerate(w) if x} or len(set(freqs))!=len(freqs):return False
    if not set(w)<={0,amp,-amp}:return False
    for row,u,g in zip(matrix,freqs,offsets):
        if w[u]!=amp*(1-2*g):return False
        if any(value != parity(u&x)^truth[x]^g for value,x in zip(row,coords)):return False
    return rank([u^freqs[0] for u in freqs])==m


def normalized_columns(matrix):
    v=len(matrix);b=len(matrix[0]);mask=(1<<v)-1
    cols=[sum(matrix[p][j]<<p for p in range(v)) for j in range(b)]
    return [c^cols[0]^((mask if matrix[0][j]^matrix[0][0] else 0)) for j,c in enumerate(cols)]


def closure_decision(values):
    candidates=set(values)
    for i,a in enumerate(values):
        for b in values[i+1:]:
            if a^b not in candidates:return False
    return True


def rank_decision(values,m):
    return rank(values)==m


def recognize(matrix, decision="closure"):
    if not isinstance(matrix,list) or not matrix or not isinstance(matrix[0],list):return {'status':'invalid_input'}
    v=len(matrix);b=len(matrix[0])
    if not b or any(len(row)!=b or any(type(x)is not int or x not in (0,1) for x in row) for row in matrix):return {'status':'invalid_input'}
    if v&(v-1) or b&(b-1):return {'status':'unsupported'}
    n=v.bit_length()-1;m=b.bit_length()-1;r=m-n
    if n<4 or n%2 or r<0:return {'status':'unsupported'}
    k=(1<<(n-1))-(1<<(n//2-1));lam=(1<<r)*(1<<(n//2-1))*((1<<(n//2-1))-1)
    cols=[sum(matrix[p][j]<<p for p in range(v)) for j in range(b)]
    if len(set(cols))!=b or any(c.bit_count()!=k for c in cols):return {'status':'not_recognized'}
    rows=[sum(x<<j for j,x in enumerate(row)) for row in matrix]
    if any((a&rows[j]).bit_count()!=lam for i,a in enumerate(rows) for j in range(i)):return {'status':'not_recognized'}
    mask=(1<<v)-1
    values=[c^cols[0]^((mask if matrix[0][j]^matrix[0][0] else 0)) for j,c in enumerate(cols)]
    if len(set(values))!=b:return {'status':'not_recognized'}
    if callable(decision):accepted=decision(values,m)
    elif decision=='closure':accepted=closure_decision(values)
    elif decision=='rank':accepted=rank_decision(values,m)
    else:raise ValueError('unknown decision method')
    if not accepted:return {'status':'not_recognized'}
    # Echelon reduction tracks coordinates in the selected original columns.
    basis=[];pivots={}
    for original in values:
        value=original;coordinate=0
        while value:
            lead=value.bit_length()-1
            if lead in pivots:
                old,word=pivots[lead];value^=old;coordinate^=word
            else:
                coordinate^=1<<len(basis)
                basis.append(original);pivots[lead]=(value,coordinate);break
    if len(basis)!=m:return {'status':'not_recognized'}
    coords=[]
    for value in values:
        coordinate=0
        while value:
            lead=value.bit_length()-1
            old,word=pivots[lead];value^=old;coordinate^=word
        coords.append(coordinate)
    truth=[0]*b
    for j,x in enumerate(coords):truth[x]=matrix[0][j]
    freqs=[sum(((a>>p)&1)<<i for i,a in enumerate(basis)) for p in range(v)]
    offsets=[matrix[p][0]^matrix[0][0] for p in range(v)]
    cert={'truth_table':truth,'block_coordinates':coords,'point_frequencies':freqs,'point_offsets':offsets,'amplitude':1<<(m-n//2)}
    if not verify(matrix,cert):return {'status':'not_recognized'}
    return {'status':'recognized','certificate':cert}
