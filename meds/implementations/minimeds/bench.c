
#include <windows.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include "key_gen.h"
#include "sign.h"
#include "verify.h"
#include "rng.h"
#include "fast_dot.h"
#define API(p) \
int p##keygen(public_key_t*,secret_key_t*); \
int p##sign_sk(signature_t*,const secret_key_t*,const public_key_t*,const uint8_t*,size_t); \
int p##verify_pk(const public_key_t*,const uint8_t*,size_t,const signature_t*); \
void p##TT_NNN(GFq_t*,const GFq_t*,const GFq_t*,const GFq_t*,const GFq_t*); \
void p##TT_MMM(GFq_t*,const GFq_t*,const GFq_t*,const GFq_t*,const GFq_t*); \
void p##pmod_mat_mul(GFq_t*,int,int,const GFq_t*,int,int,const GFq_t*,int,int); \
void p##contract_mode1_u_bca_fast(const GFq_t*,int,const GFq_t*,GFq_t*); \
void p##contract_mode2_v_acb_fast(const GFq_t*,int,const GFq_t*,GFq_t*); \
void p##contract_mode3_w_fast(const GFq_t*,int,const GFq_t*,GFq_t*);
#define EXTRA(p) \
int p##right_kernel_corank1_ct_fixed_piv(GFq_t*,GFq_t*); \
int p##pmod_mat_syst_ct(GFq_t*,int,int);
EXTRA(base_)
EXTRA(fast_)
API(base_)
API(fast_)
static void ck(int v,const char*s){if(!v){fprintf(stderr,"FAIL %s\n",s);exit(2);}}
static uint32_t state=12345;
static uint32_t rnd(void){state^=state<<13;state^=state>>17;state^=state<<5;return state;}
static void fill(GFq_t*x,int n,int mode){for(int i=0;i<n;i++)x[i]=mode==1?4092:mode==2?0:rnd()%4093;}
static void seed(int r,int phase){unsigned char v[48];for(int i=0;i<48;i++)v[i]=(unsigned char)(i*7+r*31+phase*97);randombytes_init(v,48);}
static double now(void){LARGE_INTEGER t,f;QueryPerformanceCounter(&t);QueryPerformanceFrequency(&f);return 1000.0*(double)t.QuadPart/f.QuadPart;}
static uint64_t cycles(void){ULONG64 c;ck(QueryThreadCycleTime(GetCurrentThread(),&c),"cycles");return c;}
static void kernels(void){
 GFq_t a[257],b[257];
 for(int t=0;t<100000;t++){
  uint32_t x=rnd();ck(fast_reduce4093(x)==x%4093,"reduce");
  if(t<3000){int n=t%257;uint64_t s=0;
   for(int i=0;i<n;i++){a[i]=(t%3)?rnd()%4093:(GFq_t)rnd();b[i]=(t%3)?rnd()%4093:(GFq_t)rnd();s+=(uint64_t)a[i]*b[i];}
   ck(fast_dot(a,b,n)==s%4093,"dot");
  }
 }
 GFq_t *t=malloc(N*N*N*2),*x=malloc(N*N*2),*y=malloc(N*N*2),*z=malloc(N*N*2),*p=malloc(N*N*N*2),*q=malloc(N*N*N*2);
 ck(t&&x&&y&&z&&p&&q,"allocation");
 for(int r=0;r<20;r++){
  fill(t,N*N*N,r<2?r+1:0);fill(x,N*N,r<2?r+1:0);fill(y,N*N,0);fill(z,N*N,0);
  base_TT_NNN(p,t,x,y,z);fast_TT_NNN(q,t,x,y,z);ck(!memcmp(p,q,N*N*N*2),"TT_NNN");
  base_TT_MMM(p,t,x,y,z);fast_TT_MMM(q,t,x,y,z);ck(!memcmp(p,q,MM*MM*MM*2),"TT_MMM");
  base_pmod_mat_mul(p,N,N,x,N,N,y,N,N);fast_pmod_mat_mul(q,N,N,x,N,N,y,N,N);ck(!memcmp(p,q,N*N*2),"matmul");
  base_contract_mode1_u_bca_fast(t,N,x,p);fast_contract_mode1_u_bca_fast(t,N,x,q);ck(!memcmp(p,q,N*N*2),"contract1");
  base_contract_mode2_v_acb_fast(t,N,x,p);fast_contract_mode2_v_acb_fast(t,N,x,q);ck(!memcmp(p,q,N*N*2),"contract2");
  base_contract_mode3_w_fast(t,N,x,p);fast_contract_mode3_w_fast(t,N,x,q);ck(!memcmp(p,q,N*N*2),"contract3");
 }

 for(int r=0;r<200;r++){
  fill(t,N*N,0);if(r%2==0)memset(t+(N-1)*N,0,N*2);if(r%20==0)memset(t,0,N*N*2);
  memcpy(p,t,N*N*2);memcpy(q,t,N*N*2);memset(x,0,N*2);memset(y,0,N*2);
  int a=base_right_kernel_corank1_ct_fixed_piv(p,x),b=fast_right_kernel_corank1_ct_fixed_piv(q,y);
  ck(a==b,"kernel return");ck(!memcmp(p,q,N*N*2),"kernel elimination");if(a)ck(!memcmp(x,y,N*2),"kernel vector");
  int cols=r%2?N:2*N;fill(t,N*cols,0);if(r%3==0)memset(t+(N-1)*cols,0,cols*2);
  memcpy(p,t,N*cols*2);memcpy(q,t,N*cols*2);
  a=base_pmod_mat_syst_ct(p,N,cols);b=fast_pmod_mat_syst_ct(q,N,cols);
  ck(a==b,"systemizer return");ck(!memcmp(p,q,N*cols*2),"systemizer matrix");
 }
 free(t);free(x);free(y);free(z);free(p);free(q);
 printf("{\"kind\":\"kernels\",\"reduce_cases\":100000,\"dot_cases\":3000,\"tensor_cases\":40,\"systemizer_cases\":200,\"kernel_cases\":200,\"matrix_cases\":20,\"contraction_cases\":60,\"passed\":true}\n");
}
int main(int argc,char**argv){
 setvbuf(stdout,NULL,_IONBF,0);ck(SetThreadAffinityMask(GetCurrentThread(),(DWORD_PTR)64)!=0,"affinity");
 int reps=argc>1?atoi(argv[1]):3;kernels();
 public_key_t *pk[2]={calloc(1,sizeof(public_key_t)),calloc(1,sizeof(public_key_t))};
 secret_key_t sk[2];signature_t sig[2],bad;uint8_t tape[2][32];
 const uint8_t msg[]={0,1,255,9,4,0,6,7,88,99};
 for(int r=-1;r<reps;r++){
  double ms[3][2];uint64_t cs[3][2];
  for(int op=0;op<3;op++){
   for(int order=0;order<2;order++){
    int p=order^((r+1)&1);seed(r+17,op);if(op==1)memset(&sig[p],0,sizeof(signature_t));
    uint64_t c0=cycles();double t0=now();int ok;
    if(op==0)ok=p?fast_keygen(pk[p],&sk[p]):base_keygen(pk[p],&sk[p]);
    else if(op==1)ok=p?fast_sign_sk(&sig[p],&sk[p],pk[p],msg,sizeof(msg)):base_sign_sk(&sig[p],&sk[p],pk[p],msg,sizeof(msg));
    else ok=p?fast_verify_pk(pk[0],msg,sizeof(msg),&sig[0]):base_verify_pk(pk[1],msg,sizeof(msg),&sig[1]);
    ms[op][p]=now()-t0;cs[op][p]=cycles()-c0;ck(ok,"API result");randombytes(tape[p],32);
   }
   ck(!memcmp(tape[0],tape[1],32),"random tape consumption");
   if(op==0){ck(!memcmp(pk[0],pk[1],sizeof(public_key_t)),"public keys");ck(!memcmp(sk,sk+1,sizeof(secret_key_t)),"secret keys");}
   if(op==1)ck(!memcmp(sig,sig+1,sizeof(signature_t)),"signature bytes");
   printf("{\"kind\":\"timing\",\"level\":%d,\"trial\":%d,\"op\":%d,\"base_ms\":%.6f,\"fast_ms\":%.6f,\"base_cycles\":%llu,\"fast_cycles\":%llu}\n",LEVEL,r,op,ms[op][0],ms[op][1],(unsigned long long)cs[op][0],(unsigned long long)cs[op][1]);
  }
  if(r>=0){
   for(int which=0;which<3;which++){
    bad=sig[0];uint8_t altered[sizeof(msg)];memcpy(altered,msg,sizeof(msg));
    if(which==0)bad.h_packed[0]^=1;else if(which==1)bad.mu[0]=(bad.mu[0]+1)%4093;else altered[0]^=1;
    ck(!base_verify_pk(pk[0],altered,sizeof(msg),&bad),"base mutant rejection");
    ck(!fast_verify_pk(pk[0],altered,sizeof(msg),&bad),"fast mutant rejection");
   }
  }
  printf("{\"kind\":\"checks\",\"trial\":%d,\"key_bytes_identical\":true,\"signature_bytes_identical\":true,\"cross_verify\":true,\"mutants\":%d,\"signature_struct_bytes\":%llu}\n",r,r>=0?3:0,(unsigned long long)sizeof(signature_t));
 }
 free(pk[0]);free(pk[1]);return 0;
}
