# Full recognition/reconstruction reference using actual GAP DESIGN and GF(2).
# This wrapper is original; DESIGN/GAP implementations are external dependencies.
DBBitsToInt := function(bits)
 local value,i;
 value:=0;
 for i in Reversed([1..Length(bits)]) do value:=2*value+IntFFE(bits[i]); od;
 return value;
end;
DBWalsh := function(truth)
 local w,h,start,j,a,b,n;
 w:=List(truth,x->1-2*x); n:=Length(w); h:=1;
 while h<n do
  for start in [1,1+2*h..n-2*h+1] do
   for j in [start..start+h-1] do
    a:=w[j]; b:=w[j+h]; w[j]:=a+b; w[j+h]:=a-b;
   od;
  od;
  h:=2*h;
 od;
 return w;
end;
DBPipeline := function(input)
 local v,b,n,m,r,q,k,lambda,amplitude,one,zero,M,columns,blocks,D,normalized,ones,
       echelon,basis,heads,betaBits,betaIntegers,j,i,value,coordinate,truth,phi,
       phiIntegers,offsets,walsh,support,coordinateRows,functionRow,expected;
 if not IsList(input) or IsEmpty(input) or not IsList(input[1]) or IsEmpty(input[1]) then
  return rec(status:="invalid_input");
 fi;
 v:=Length(input); b:=Length(input[1]);
 if not ForAll(input,row->IsList(row) and Length(row)=b and ForAll(row,x->x=0 or x=1)) then return rec(status:="invalid_input"); fi;
 n:=LogInt(v,2); m:=LogInt(b,2);
 if 2^n<>v or 2^m<>b or n<4 or n mod 2<>0 or m<n then return rec(status:="unsupported"); fi;
 r:=m-n; q:=2^(n/2-1); k:=q*(2*q-1); lambda:=2^r*q*(q-1); amplitude:=2^(m-n/2);
 one:=One(GF(2));zero:=Zero(GF(2));
 M:=List(input,row->List(row,x->x*one));ConvertToMatrixRep(M,2);
 columns:=TransposedMat(M);ConvertToMatrixRep(columns,2);
 blocks:=List(columns,col->PositionsProperty(col,x->x=one));
 D:=BlockDesign(v,blocks);
 if not IsBinaryBlockDesign(D) or not IsSimpleBlockDesign(D) or not ForAll(D.blocks,x->Length(x)=k) or PairwiseBalancedLambda(D)<>lambda then
  return rec(status:="not_recognized");
 fi;
 ones:=List([1..v],x->one);ConvertToVectorRep(ones,2);
 normalized:=List([1..b],j->columns[j]+columns[1]+(M[1][j]+M[1][1])*ones);
 ConvertToMatrixRep(normalized,2);
 echelon:=SemiEchelonMat(normalized);basis:=echelon.vectors;
 if Length(basis)<>m then return rec(status:="not_recognized");fi;
 heads:=List(basis,row->Position(row,one));
 betaBits:=[];
 for j in [1..b] do
  value:=ShallowCopy(normalized[j]);coordinate:=[];
  for i in [1..m] do
   Add(coordinate,value[heads[i]]);
   value:=value+coordinate[i]*basis[i];
  od;
  if not IsZero(value) then Error("Coordinate reconstruction failed");fi;
  ConvertToVectorRep(coordinate,2);Add(betaBits,coordinate);
 od;
 betaIntegers:=List(betaBits,DBBitsToInt);
 if Set(betaIntegers)<>[0..b-1] then return rec(status:="not_recognized");fi;
 truth:=List([1..b],x->0);
 for j in [1..b] do truth[betaIntegers[j]+1]:=input[1][j];od;
 phi:=TransposedMat(basis);ConvertToMatrixRep(phi,2);phiIntegers:=List(phi,DBBitsToInt);
 offsets:=List([1..v],i->IntFFE(M[i][1]+M[1][1]));
 walsh:=DBWalsh(truth);
 if not ForAll(walsh,x->x=0 or x=amplitude or x=-amplitude) then return rec(status:="not_recognized");fi;
 support:=Filtered([0..b-1],i->walsh[i+1]<>0);
 if Set(phiIntegers)<>support or Length(Set(phiIntegers))<>v then return rec(status:="not_recognized");fi;
 if not ForAll([1..v],i->walsh[phiIntegers[i]+1]=amplitude*(1-2*offsets[i])) then return rec(status:="not_recognized");fi;
 coordinateRows:=TransposedMat(betaBits);ConvertToMatrixRep(coordinateRows,2);
 functionRow:=List([1..b],j->truth[betaIntegers[j]+1]*one);ConvertToVectorRep(functionRow,2);
 ones:=List([1..b],x->one);ConvertToVectorRep(ones,2);
 for i in [1..v] do
  expected:=functionRow+offsets[i]*ones;
  for j in [1..m] do expected:=expected+phi[i][j]*coordinateRows[j];od;
  if expected<>M[i] then return rec(status:="not_recognized");fi;
 od;
 if RankMat(List(phi,row->row+phi[1]))<>m then return rec(status:="not_recognized");fi;
 return rec(status:="recognized",truth_table:=truth,block_coordinates:=betaIntegers,
   point_frequencies:=phiIntegers,point_offsets:=offsets,amplitude:=amplitude);
end;
DBPrintJSON := function(record)
 Print("{\"status\":\"",record.status,"\"");
 if record.status="recognized" then
  Print(",\"certificate\":{\"truth_table\":",record.truth_table,
  ",\"block_coordinates\":",record.block_coordinates,",\"point_frequencies\":",record.point_frequencies,
  ",\"point_offsets\":",record.point_offsets,",\"amplitude\":",record.amplitude,"}");
 fi;
 Print("}");
end;
