
#include <windows.h>
#include <x86intrin.h>
long long cpucycles(void){return (long long)__rdtsc();}
/* Upstream diagnostic conversion only; actual measurements use QPC/thread cycles. */
double osfreq(void){return 2900000000.0;}
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "api.h"
#include "matrixmod.h"
#include "fips202.h"
#define DECL(p) \
int p##crypto_sign_keypair(unsigned char*,unsigned char*); \
int p##crypto_sign_keypair_simd(unsigned char*,unsigned char*); \
int p##crypto_sign(unsigned char*,unsigned long long*,const unsigned char*,unsigned long long,const unsigned char*); \
int p##crypto_sign_simd(unsigned char*,unsigned long long*,const unsigned char*,unsigned long long,const unsigned char*); \
int p##crypto_sign_open(unsigned char*,unsigned long long*,const unsigned char*,unsigned long long,const unsigned char*); \
int p##crypto_sign_open_simd(unsigned char*,unsigned long long*,const unsigned char*,unsigned long long,const unsigned char*); \
void p##pmod_mat_mul(GFq_t*,int,int,GFq_t*,int,int,GFq_t*,int,int); \
void p##pmod_mat_mul_simd(GFq_t*,int,int,GFq_t*,int,int,GFq_t*,int,int);
#define MORE(p) \
int p##pmod_mat_syst_ct(GFq_t*,int,int); \
int p##pmod_mat_syst_ct_simd(GFq_t*,int,int);
MORE(base_)
MORE(fast_)
DECL(base_)
DECL(fast_)
static void ck(int a,const char*s){if(!a){fprintf(stderr,"FAIL %s\n",s);exit(2);}}
static keccak_state rng;
int randombytes(unsigned char*x,unsigned long long n){shake256_squeeze(x,n,&rng);return 0;}
static void seed(uint64_t x){shake256_absorb_once(&rng,(uint8_t*)&x,8);}
static double now(void){LARGE_INTEGER x,f;QueryPerformanceCounter(&x);QueryPerformanceFrequency(&f);return 1000.0*x.QuadPart/f.QuadPart;}
static uint64_t cyc(void){ULONG64 x;ck(QueryThreadCycleTime(GetCurrentThread(),&x),"cycles");return x;}
static void kernels(void){
 enum{D=35};GFq_t a[D*D],b[D*D+8],x[D*D],y[D*D],z[D*D],al[D*D];seed(23456);
 for(int t=0;t<200;t++){
  int n=t%32+1,w=(t*7)%35+1;randombytes((void*)a,sizeof a);randombytes((void*)b,sizeof b);
  for(int i=0;i<D*D;i++){a[i]%=MEDS_p;b[i]%=MEDS_p;}
  base_pmod_mat_mul(x,n,w,a,n,n,b,n,w);base_pmod_mat_mul_simd(y,n,w,a,n,n,b,n,w);fast_pmod_mat_mul_simd(z,n,w,a,n,n,b,n,w);
  ck(!memcmp(x,y,n*w*sizeof *x),"published SIMD vs scalar");ck(!memcmp(x,z,n*w*sizeof *x),"packed vs scalar");
  memcpy(al,b,sizeof al);fast_pmod_mat_mul_simd(al,n,w,a,n,n,al,n,w);ck(!memcmp(x,al,n*w*sizeof*x),"alias B");
  if(w<=n){memcpy(al,a,sizeof al);fast_pmod_mat_mul_simd(al,n,w,al,n,n,b,n,w);ck(!memcmp(x,al,n*w*sizeof*x),"alias A");}
 }

 /* Block systemization must agree on full-rank inputs and reject singular
    left blocks without reading a nonexistent inverse. Exercise rectangular
    widths that triggered the upstream identity-buffer overflow. */
 for(int trial=0;trial<200;trial++){
  int n=2+trial%16,w=n+1+trial%16;
  GFq_t original[32*40],p[32*40],q[32*40],r[32*40];
  for(int i=0;i<n;i++)for(int j=0;j<w;j++)original[i*w+j]=j<n?(i==j):((i*7+j*11+trial)%MEDS_p);
  if(trial%3==0)for(int j=0;j<n;j++)original[(n-1)*w+j]=0;
  memcpy(p,original,n*w*sizeof *p);memcpy(q,p,n*w*sizeof *q);memcpy(r,p,n*w*sizeof *r);
  int rp=base_pmod_mat_syst_ct(p,n,w),rq=base_pmod_mat_syst_ct_simd(q,n,w),rr=fast_pmod_mat_syst_ct_simd(r,n,w);
  ck(rp==rq&&rp==rr,"block systemizer status");if(rp==0)ck(!memcmp(p,q,n*w*sizeof*p)&&!memcmp(p,r,n*w*sizeof*p),"block systemizer result");
 }
 puts("{\"kind\":\"systemizer_checks\",\"cases\":200,\"passed\":true}");
 puts("{\"kind\":\"kernels\",\"cases\":200,\"passed\":true}");
}
int main(int argc,char**argv){
 setvbuf(stdout,NULL,_IONBF,0);ck(SetThreadAffinityMask(GetCurrentThread(),64)!=0,"affinity");kernels();
 int trials=argc>1?atoi(argv[1]):7;unsigned char *pk[3],*sk[3],*sm[3],out[1024],mut[MEDS_SIG_BYTES+1024],msg[1024],tape[3][32];unsigned long long len[3],ol;
 for(int i=0;i<1024;i++)msg[i]=(unsigned char)(i*31);for(int j=0;j<3;j++){pk[j]=malloc(MEDS_PK_BYTES);sk[j]=malloc(MEDS_SK_BYTES);sm[j]=malloc(MEDS_SIG_BYTES+1024);ck(pk[j]&&sk[j]&&sm[j],"alloc");}
 int sizes[]={0,1,32,135,136,137,1024};
 for(int r=-1;r<trials;r++){
  int n=sizes[(r+1)%7];
  for(int op=0;op<3;op++){
   double ms[3];uint64_t cycles[3];
   for(int ord=0;ord<3;ord++){
    int j=(ord+r+1)%3;seed(700001+(r+1)*197+op);double t=now();uint64_t c=cyc();int v;
    if(op==0)v=j==0?base_crypto_sign_keypair(pk[j],sk[j]):j==1?base_crypto_sign_keypair_simd(pk[j],sk[j]):fast_crypto_sign_keypair_simd(pk[j],sk[j]);
    else if(op==1)v=j==0?base_crypto_sign(sm[j],&len[j],msg,n,sk[j]):j==1?base_crypto_sign_simd(sm[j],&len[j],msg,n,sk[j]):fast_crypto_sign_simd(sm[j],&len[j],msg,n,sk[j]);
    else {int other=(j+1)%3;v=j==0?base_crypto_sign_open(out,&ol,sm[other],len[other],pk[other]):j==1?base_crypto_sign_open_simd(out,&ol,sm[other],len[other],pk[other]):fast_crypto_sign_open_simd(out,&ol,sm[other],len[other],pk[other]);}
    cycles[j]=cyc()-c;ms[j]=now()-t;ck(v==0,"API");if(op==2)ck(ol==n&&!memcmp(msg,out,n),"message");randombytes(tape[j],32);
   }
   for(int j=1;j<3;j++){
    ck(!memcmp(tape[0],tape[j],32),"RNG consumption");
    if(op==0)ck(!memcmp(pk[0],pk[j],MEDS_PK_BYTES)&&!memcmp(sk[0],sk[j],MEDS_SK_BYTES),"key bytes");
    if(op==1)ck(len[0]==len[j]&&!memcmp(sm[0],sm[j],len[0]),"signature bytes");
   }
   printf("{\"kind\":\"timing\",\"trial\":%d,\"op\":%d,\"msg_bytes\":%d,\"scalar_ms\":%.6f,\"published_ms\":%.6f,\"ours_ms\":%.6f,\"scalar_cycles\":%llu,\"published_cycles\":%llu,\"ours_cycles\":%llu}\n",r,op,n,ms[0],ms[1],ms[2],(unsigned long long)cycles[0],(unsigned long long)cycles[1],(unsigned long long)cycles[2]);
  }
  if(r>=0){memcpy(mut,sm[0],len[0]);mut[MEDS_SIG_BYTES-1]^=1;
   ck(base_crypto_sign_open(out,&ol,mut,len[0],pk[0])!=0,"scalar reject");
   ck(base_crypto_sign_open_simd(out,&ol,mut,len[0],pk[0])!=0,"SIMD reject");
   ck(fast_crypto_sign_open_simd(out,&ol,mut,len[0],pk[0])!=0,"packed reject");
  }
  printf("{\"kind\":\"check\",\"trial\":%d,\"three_way_equal\":true,\"signature_bytes\":%d}\n",r,MEDS_SIG_BYTES);
 }
 for(int j=0;j<3;j++){free(pk[j]);free(sk[j]);free(sm[j]);}return 0;
}
