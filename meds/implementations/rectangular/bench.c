/* Differential experiment only. Deterministic RNG is NOT for production. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <windows.h>
#include "api.h"
#include "matrixmod.h"
#include "util.h"
#include "fips202.h"
int solve_opt(pmod_mat_t*, pmod_mat_t*, pmod_mat_t*);
int base_keypair(unsigned char*,unsigned char*);
int fast_keypair(unsigned char*,unsigned char*);
int base_sign(unsigned char*,unsigned long long*,const unsigned char*,unsigned long long,const unsigned char*);
int fast_sign(unsigned char*,unsigned long long*,const unsigned char*,unsigned long long,const unsigned char*);
int base_open(unsigned char*,unsigned long long*,const unsigned char*,unsigned long long,const unsigned char*);
int fast_open(unsigned char*,unsigned long long*,const unsigned char*,unsigned long long,const unsigned char*);
static keccak_state test_rng;
static void reset_rng(uint64_t seed) { shake256_absorb_once(&test_rng,(uint8_t*)&seed,sizeof seed); }
int randombytes(unsigned char *x, unsigned long long len) { shake256_squeeze(x,(size_t)len,&test_rng); return 0; }
static double now(void) { LARGE_INTEGER t,f; QueryPerformanceCounter(&t); QueryPerformanceFrequency(&f); return (double)t.QuadPart/f.QuadPart; }
static void require(int ok,const char*where) { if(!ok) { fprintf(stderr,"FAIL %s\n",where); exit(2); } }
static int solver_checks(int count) {
 GFq_t C[2*MEDS_m*MEDS_n],A[MEDS_m*MEDS_m],R[MEDS_n*MEDS_n],B[MEDS_n*MEDS_n],AI[MEDS_m*MEDS_m];
 GFq_t prod[MEDS_m*MEDS_n],candidate[MEDS_m*MEDS_n]; int accepted=0, solved=0;
 reset_rng(9001);
 for(int t=0;t<count;t++) {
   for(int i=0;i<2*MEDS_m*MEDS_n;i++) C[i]=rnd_GF(&test_rng);
   if(t%10==0) memset(C,0,sizeof C);
   if(t%10==1) memcpy(C+MEDS_m*MEDS_n,C,MEDS_m*MEDS_n*sizeof(GFq_t));
   if(t%10==2) memset(C,0,MEDS_m*MEDS_n*sizeof(GFq_t));
   if(t%10==3) for(int j=0;j<MEDS_n;j++) { C[(MEDS_m-1)*MEDS_n+j]=0; C[MEDS_m*MEDS_n+(MEDS_m-1)*MEDS_n+j]=0; }
   if(solve_opt(A,R,C)<0) continue;
   solved++;
   for(int s=0;s<2;s++) {
     pmod_mat_mul(prod,MEDS_m,MEDS_n,A,MEDS_m,MEDS_m,C+s*MEDS_m*MEDS_n,MEDS_m,MEDS_n);
     for(int i=0;i<MEDS_m;i++) for(int j=0;j<MEDS_n;j++) require(prod[i*MEDS_n+j]==R[(i+s)*MEDS_n+j],"solver equation");
   }
   if(pmod_mat_inv(B,R,MEDS_n,MEDS_n)<0) continue;
   accepted++; require(pmod_mat_inv(AI,A,MEDS_m,MEDS_m)==0,"implied invertibility");
   pmod_mat_mul(candidate,MEDS_m,MEDS_n,C,MEDS_m,MEDS_n,B,MEDS_n,MEDS_n);
   for(int i=0;i<MEDS_m;i++) for(int j=0;j<MEDS_m;j++) require(candidate[i*MEDS_n+j]==AI[i*MEDS_m+j],"inverse formula");
 }
 printf("{\"kind\":\"solver_checks\",\"parameter\":\"%s\",\"cases\":%d,\"solved\":%d,\"right_invertible\":%d,\"failures\":0}\n",MEDS_name,count,solved,accepted); fflush(stdout); return 0;
}
static unsigned long long cycles(void) { ULONG64 x=0; require(QueryThreadCycleTime(GetCurrentThread(),&x),"thread cycle clock"); return x; }
int main(int argc,char**argv) {
 DWORD_PTR allowed,system; require(GetProcessAffinityMask(GetCurrentProcess(),&allowed,&system),"affinity read");
 DWORD_PTR chosen=(allowed & 64)?64:(allowed & (~allowed+1));
 require(SetThreadAffinityMask(GetCurrentThread(),chosen)!=0,"affinity set");
 printf("{\"kind\":\"environment\",\"affinity_mask\":%llu}\n",(unsigned long long)chosen);
 int trials=argc>1?atoi(argv[1]):7; solver_checks(1000);
 unsigned char *pk=malloc(MEDS_PK_BYTES),*sk=malloc(MEDS_SK_BYTES),*pk2=malloc(MEDS_PK_BYTES),*sk2=malloc(MEDS_SK_BYTES);
 unsigned char msg[32]={1,2,3,4},*sm=malloc(MEDS_SIG_BYTES+32),*sf=malloc(MEDS_SIG_BYTES+32),*out=malloc(32),*mut=malloc(MEDS_SIG_BYTES+32);
 unsigned long long sl,fl,ol;
 for(int t=0;t<9;++t) {
   double kb=0,kf=0,z; unsigned long long cb=0,cf=0,zc;
   for(int j=0;j<2;++j) {
     int fast=(j+t)%2; reset_rng(17+t);z=now();zc=cycles();
     if(fast){require(fast_keypair(pk2,sk2)==0,"fast keygen");cf=cycles()-zc;kf=now()-z;}
     else{require(base_keypair(pk,sk)==0,"base keygen");cb=cycles()-zc;kb=now()-z;}
   }
   require(!memcmp(pk,pk2,MEDS_PK_BYTES)&&!memcmp(sk,sk2,MEDS_SK_BYTES),"identical keys");
   if(t>0)printf("{\"kind\":\"keygen\",\"trial\":%d,\"base_ms\":%.6f,\"fast_ms\":%.6f,\"base_cycles\":%llu,\"fast_cycles\":%llu}\n",t,kb*1000,kf*1000,cb,cf);
 }
 for(int t=0;t<trials+1;t++) {
   double bs=0,fs=0,bv=0,fv=0,z; unsigned long long bc=0,fc=0,bvc=0,fvc=0,zc;
   for(int j=0;j<2;j++) {
     int fast=(j+(t%2))%2; reset_rng(1000+t); z=now(); zc=cycles();
     if(fast) { require(fast_sign(sf,&fl,msg,32,sk)==0,"fast sign"); fc=cycles()-zc; fs=now()-z; }
     else { require(base_sign(sm,&sl,msg,32,sk)==0,"base sign"); bc=cycles()-zc; bs=now()-z; }
   }
   require(sl==fl&&!memcmp(sm,sf,(size_t)sl),"byte-identical signature");
   for(int j=0;j<2;j++) {
     int fast=(j+(t%2))%2; z=now(); zc=cycles();
     int r=fast?fast_open(out,&ol,sm,sl,pk):base_open(out,&ol,sf,fl,pk);
     unsigned long long dc=cycles()-zc; double dt=now()-z; require(r==0&&ol==32&&!memcmp(msg,out,32),"cross verification"); if(fast){fv=dt;fvc=dc;} else {bv=dt;bvc=dc;}
   }
   if(t>0)printf("{\"kind\":\"timing\",\"parameter\":\"%s\",\"trial\":%d,\"base_sign_ms\":%.6f,\"fast_sign_ms\":%.6f,\"base_verify_ms\":%.6f,\"fast_verify_ms\":%.6f}\n",MEDS_name,t,1000*bs,1000*fs,1000*bv,1000*fv);
   if(t>0)printf("{\"kind\":\"cycles\",\"trial\":%d,\"base_sign\":%llu,\"fast_sign\":%llu,\"base_verify\":%llu,\"fast_verify\":%llu}\n",t,bc,fc,bvc,fvc);
   fflush(stdout);
 }
 for(int t=0;t<12;t++) {
   memcpy(mut,sm,(size_t)sl); size_t pos=t<6?(t*13)%MEDS_SIG_BYTES:MEDS_SIG_BYTES+(t%32); mut[pos]^=(unsigned char)(1u<<(t%8));
   int a=base_open(out,&ol,mut,sl,pk),c=fast_open(out,&ol,mut,sl,pk); require((a==0)==(c==0),"mutant agreement"); require(a!=0,"mutant rejection");
 }
 printf("{\"kind\":\"differential\",\"parameter\":\"%s\",\"identical_signatures\":%d,\"mutant_rejections\":12,\"failures\":0}\n",MEDS_name,trials+1);
 return 0;
}
