// Original Design Boolean native implementation. Apache-2.0.
#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <exception>
#include <limits>
#include <string>
#include <vector>
#if defined(_WIN32)
#define DB_EXPORT extern "C" __declspec(dllexport)
#else
#define DB_EXPORT extern "C"
#endif
using U=std::uint64_t;
using V=std::vector<U>;
static unsigned pc(U x){return __builtin_popcountll(x);}
static unsigned lead(U x){return 63-__builtin_clzll(x);}
static int leading(const V &a){for(std::size_t i=a.size();i-->0;)if(a[i])return int(i*64+lead(a[i]));return -1;}
static void xorr(V &a,const V&b){for(std::size_t i=0;i<a.size();++i)a[i]^=b[i];}
static unsigned rank_small(std::vector<std::uint32_t> a){std::uint32_t p[32]={};unsigned rank=0;for(auto x:a)while(x){unsigned k=31-__builtin_clz(x);if(p[k])x^=p[k];else{p[k]=x;++rank;break;}}return rank;}
static unsigned log2exact(std::uint32_t x){return 31-__builtin_clz(x);}
DB_EXPORT int db_abi_version(){return 2;}
DB_EXPORT int db_recognize(const unsigned char *data,std::size_t size,
 std::uint32_t v,std::uint32_t b,int is_packed,int strategy,
 std::uint32_t *out,std::size_t out_len,unsigned char *packed_out,std::size_t packed_len,
 std::uint32_t *rank_out,char *reason,std::size_t reason_len){
 auto fail=[&](int code,const char* text){if(reason&&reason_len)std::snprintf(reason,reason_len,"%s",text);return code;};
 try{
  if(!data||!out||!packed_out||!rank_out||!reason||!reason_len||!v||!b)return fail(2,"Invalid null pointer or empty dimensions.");
  *rank_out=0;
  if(strategy!=0&&strategy!=1)return fail(2,"Unknown validation strategy.");
  if((v&(v-1))||(b&(b-1)))return fail(3,"Supported dimensions must be powers of two.");
  unsigned n=log2exact(v),m=log2exact(b);
  if(n<4||(n&1)||m<n)return fail(3,"Supported shapes require even n>=4 and m>=n.");
  // Bound shifts, output indices and allocations before any dimension product.
  if(m>20||std::uint64_t(v)*b>(std::uint64_t(1)<<28))return fail(3,"Matrix exceeds the native resource bound.");
  std::size_t bytes=(std::size_t(b)+7)/8;
  if(is_packed!=0&&is_packed!=1)return fail(2,"Unknown input packing.");
  std::size_t needed=std::size_t(v)*(is_packed?bytes:b);
  if(size!=needed||out_len<std::size_t(2)*b+std::size_t(2)*v+m||packed_len<std::size_t(v)*bytes)return fail(2,"Input or output buffer length mismatch.");
  std::size_t rw=(std::size_t(b)+63)/64,cw=(std::size_t(v)+63)/64;
  std::vector<V> rows(v,V(rw)),cols(b,V(cw));
  if(is_packed){
   for(std::uint32_t p=0;p<v;++p){
    if(b%8&&(data[std::size_t(p)*bytes+bytes-1]>>(b%8)))return fail(2,"Packed row has nonzero padding bits.");
    for(std::uint32_t j=0;j<b;++j){unsigned z=(data[std::size_t(p)*bytes+j/8]>>(j%8))&1;rows[p][j/64]|=U(z)<<(j%64);cols[j][p/64]|=U(z)<<(p%64);}
   }
  }else{
   for(std::uint32_t p=0;p<v;++p){
    for(std::uint32_t j=0;j<b;++j){unsigned z=data[std::size_t(p)*b+j];if(z>1)return fail(2,"Incidence entries must be bits.");rows[p][j/64]|=U(z)<<(j%64);cols[j][p/64]|=U(z)<<(p%64);}
   }
  }
  std::memset(packed_out,0,std::size_t(v)*bytes);
  for(std::uint32_t p=0;p<v;++p)for(std::size_t k=0;k<bytes;++k)packed_out[std::size_t(p)*bytes+k]=(rows[p][k/8]>>(8*(k%8)))&255;
  U q=U(1)<<(n/2-1),expected_k=q*(2*q-1),lambda=(U(1)<<(m-n))*q*(q-1);
  if(strategy==0){
  for(const auto& col:cols){U k=0;for(auto word:col)k+=pc(word);if(k!=expected_k)return fail(1,"A block has the wrong size for the supported design family.");}
  std::vector<std::uint32_t> order(b);for(std::uint32_t j=0;j<b;++j)order[j]=j;
  std::sort(order.begin(),order.end(),[&](auto a,auto c){return cols[a]<cols[c];});
  for(std::uint32_t j=1;j<b;++j)if(cols[order[j-1]]==cols[order[j]])return fail(1,"Repeated blocks violate simplicity.");
  for(std::uint32_t p=0;p<v;++p)for(std::uint32_t r=0;r<p;++r){U count=0;for(std::size_t w=0;w<rw;++w)count+=pc(rows[p][w]&rows[r][w]);if(count!=lambda)return fail(1,"Point-pair multiplicities do not match the required 2-design.");}
  }
  std::vector<V> norm=cols;
  for(std::uint32_t j=0;j<b;++j){bool flip=((cols[j][0]^cols[0][0])&1)!=0;for(std::size_t k=0;k<cw;++k)norm[j][k]^=cols[0][k]^(flip?~U(0):U(0));if(v%64)norm[j].back()&=(U(1)<<(v%64))-1;}
  std::vector<V> piv(v);std::vector<std::uint32_t> masks(v),basis,beta(b);
  for(std::uint32_t j=0;j<b;++j){V value=norm[j];std::uint32_t coordinate=0;while(true){int k=leading(value);if(k<0)break;if(!piv[k].empty()){xorr(value,piv[k]);coordinate^=masks[k];}else{std::uint32_t unit=basis.size()<31?(std::uint32_t(1)<<basis.size()):0;piv[k]=std::move(value);masks[k]=coordinate^unit;basis.push_back(j);coordinate=unit;break;}}beta[j]=coordinate;}
  *rank_out=std::uint32_t(basis.size());
  if(basis.size()!=m)return fail(1,"Bordered binary rank does not match the characterization.");
  std::vector<unsigned char> seen(b),truth(b),offset(v);std::vector<std::uint32_t> phi(v);
  for(std::uint32_t j=0;j<b;++j){if(beta[j]>=b||seen[beta[j]])return fail(1,"Normalized coordinates do not cover the cube bijectively.");seen[beta[j]]=1;truth[beta[j]]=(rows[0][j/64]>>(j%64))&1;}
  for(std::uint32_t p=0;p<v;++p){for(unsigned i=0;i<m;++i)phi[p]|=std::uint32_t((norm[basis[i]][p/64]>>(p%64))&1)<<i;offset[p]=(rows[p][0]^rows[0][0])&1;}
  // Independent direct realization verifier, after the construction.
  std::vector<std::int64_t> spectrum(b);for(std::uint32_t x=0;x<b;++x)spectrum[x]=1-2*int(truth[x]);
  for(std::uint32_t step=1;step<b;step*=2)for(std::uint32_t start=0;start<b;start+=2*step)for(std::uint32_t j=start;j<start+step;++j){auto a=spectrum[j],c=spectrum[j+step];spectrum[j]=a+c;spectrum[j+step]=a-c;}
  std::int64_t amplitude=std::int64_t(1)<<(m-n/2);std::fill(seen.begin(),seen.end(),0);unsigned support=0;
  for(auto value:spectrum){if(value&&value!=amplitude&&value!=-amplitude)return fail(1,"Direct Walsh spectrum verification failed.");support+=value!=0;}
  if(support!=v)return fail(1,"Walsh support cardinality verification failed.");
  for(std::uint32_t p=0;p<v;++p){if(phi[p]>=b||seen[phi[p]]||spectrum[phi[p]]!=amplitude*(1-2*int(offset[p])))return fail(1,"Walsh support or sign verification failed.");seen[phi[p]]=1;}
  // Evaluate every incidence bit through packed coordinate rows, not sampling.
  std::vector<V> coordinate_rows(m,V(rw));V function_row(rw);
  for(std::uint32_t j=0;j<b;++j){if(truth[beta[j]])function_row[j/64]|=U(1)<<(j%64);auto value=beta[j];while(value){unsigned bit=__builtin_ctz(value);coordinate_rows[bit][j/64]|=U(1)<<(j%64);value&=value-1;}}
  for(std::uint32_t p=0;p<v;++p){V predicted=function_row;if(offset[p])for(auto&word:predicted)word=~word;auto frequency=phi[p];while(frequency){unsigned bit=__builtin_ctz(frequency);xorr(predicted,coordinate_rows[bit]);frequency&=frequency-1;}if(b%64)predicted.back()&=(U(1)<<(b%64))-1;if(predicted!=rows[p])return fail(1,"Direct incidence identity verification failed.");}
  std::vector<std::uint32_t> affine(v);for(std::uint32_t p=0;p<v;++p)affine[p]=phi[p]^phi[0];if(rank_small(affine)!=m)return fail(1,"Reconstruction has a nonzero linear structure.");
  for(std::uint32_t j=0;j<b;++j){out[j]=truth[j];out[b+j]=beta[j];}for(std::uint32_t p=0;p<v;++p){out[2*b+p]=phi[p];out[2*b+v+p]=offset[p];}for(unsigned i=0;i<m;++i)out[2*b+2*v+i]=basis[i];
  return fail(0,"Recognized and directly verified the complete Boolean-function realization.");
 }catch(const std::exception& e){return fail(4,e.what());}catch(...){return fail(4,"Unknown native exception.");}
}
