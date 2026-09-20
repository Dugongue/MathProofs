#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include "matrixmod.h"
void base_pmod_mat_mul(GFq_t*,int,int,GFq_t*,int,int,GFq_t*,int,int);
void fast_pmod_mat_mul(GFq_t*,int,int,GFq_t*,int,int,GFq_t*,int,int);
int base_pmod_mat_syst_ct_partial_swap_backsub(GFq_t*,int,int,int,int,int);
int fast_pmod_mat_syst_ct_partial_swap_backsub(GFq_t*,int,int,int,int,int);
static uint32_t seed=0x579ef138u;
static uint32_t rnd(void){seed^=seed<<13;seed^=seed>>17;seed^=seed<<5;return seed;}
static void check(int c,const char* msg,int i){if(!c){fprintf(stderr,"FAIL %s case %d\n",msg,i);exit(2);}}
static uint32_t fold(uint32_t x){x=(x&4095u)+3u*(x>>12);x=(x&4095u)+3u*(x>>12);return x-4093u*(x>=4093u);}
int main(void){
 for(uint32_t t=0;t<1000000;++t){uint32_t x=rnd();check(fold(x)==x%4093u,"mod reduction",t);}
 uint32_t boundary[]={0,1,4092,4093,4094,4095,4096,16744464u,4292870400u,0xffffffffu};
 for(int i=0;i<10;++i)check(fold(boundary[i])==boundary[i]%4093u,"mod boundary",i);
 for(int t=0;t<1200;++t){
  int nr=1+rnd()%45,nk=1+rnd()%46,nc=1+rnd()%91;
  if(t%10==0){nk=256+(t%3);nr=1+rnd()%5;}
  if(t%10==1)nc=650;
  int stride=nc+(t%4);size_t an=nr*nk,bn=nk*stride,cn=nr*nc;
  size_t cap=an>bn?an:bn;if(cap<cn)cap=cn;
  GFq_t *a=calloc(cap,sizeof *a),*bb=calloc(cap,sizeof *bb),*c=calloc(cn,sizeof *c),*d=calloc(cn,sizeof *d),*alias=calloc(cap,sizeof *alias);
  check(a&&bb&&c&&d&&alias,"alloc",t);
  for(size_t i=0;i<an;++i)a[i]=t%4==0?65535:t%4==1?rnd()%4093:t%4==2?rnd()%4096:rnd();
  for(size_t i=0;i<bn;++i)bb[i]=t%4==0?65535:t%4==1?rnd()%4093:t%4==2?rnd()%4096:rnd();
  base_pmod_mat_mul(c,nr,nc,a,nr,nk,bb,nk,stride);
  fast_pmod_mat_mul(d,nr,nc,a,nr,nk,bb,nk,stride);
  check(!memcmp(c,d,cn*sizeof *c),"multiply",t);
  memcpy(alias,a,an*sizeof *a);fast_pmod_mat_mul(alias,nr,nc,alias,nr,nk,bb,nk,stride);check(!memcmp(c,alias,cn*sizeof *c),"alias A",t);
  memcpy(alias,bb,bn*sizeof *bb);fast_pmod_mat_mul(alias,nr,nc,a,nr,nk,alias,nk,stride);check(!memcmp(c,alias,cn*sizeof *c),"alias B",t);
  free(a);free(bb);free(c);free(d);free(alias);
 }
 for(int t=0;t<600;++t){
  int nr=1+rnd()%45,nc=nr+rnd()%46,mr=1+rnd()%nr,swap=t%2,back=(t/2)%2;
  GFq_t *a=malloc(nr*nc*sizeof *a),*b=malloc(nr*nc*sizeof *b);check(a&&b,"alloc",t);
  for(int i=0;i<nr*nc;++i)a[i]=t%5==0?0:t%5==1?rnd()%4093:t%5==2?rnd()%4096:t%5==3?rnd():65535;
  memcpy(b,a,nr*nc*sizeof *a);
  int ra=base_pmod_mat_syst_ct_partial_swap_backsub(a,nr,nc,mr,swap,back);
  int rb=fast_pmod_mat_syst_ct_partial_swap_backsub(b,nr,nc,mr,swap,back);
  check(ra==rb&&!memcmp(a,b,nr*nc*sizeof *a),"row systemization",t);
  free(a);free(b);
 }
 puts("{\"status\":\"PASS\",\"modular_random\":1000000,\"modular_boundaries\":10,\"matrix_cases\":1200,\"matrix_alias_cases\":2400,\"systemization_cases\":600}");
 return 0;
}
