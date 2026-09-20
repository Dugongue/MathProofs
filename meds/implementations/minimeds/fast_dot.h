#ifndef MINIMEDS_FAST_DOT_H
#define MINIMEDS_FAST_DOT_H
#include <stdint.h>
#include <immintrin.h>
_Static_assert(MINI_MEDS_P == 4093, "This backend requires q=4093");
/* Exact for all uint32_t inputs: 4096 == 3 modulo 4093. */
static inline uint16_t fast_reduce4093(uint32_t x) {
 x=(x&4095u)+3u*(x>>12);
 x=(x&4095u)+3u*(x>>12);
 return (uint16_t)(x-4093u*(x>=4093u));
}
/* Fast for <=256 12-bit entries; exact uint64 fallback otherwise.
   Canonical field elements always take the same fast branch. */
static inline uint16_t fast_dot(const uint16_t *a,const uint16_t *b,int n) {
 __m256i v=_mm256_setzero_si256(),bits=v; uint32_t tail=0,mask=0;int i=0;
 for(;i+16<=n;i+=16){
  __m256i x=_mm256_loadu_si256((const __m256i*)(a+i));
  __m256i y=_mm256_loadu_si256((const __m256i*)(b+i));
  bits=_mm256_or_si256(bits,_mm256_or_si256(x,y));
  v=_mm256_add_epi32(v,_mm256_madd_epi16(x,y));
 }
 if(i+8<=n){
  __m128i x=_mm_loadu_si128((const __m128i*)(a+i));
  __m128i y=_mm_loadu_si128((const __m128i*)(b+i));
  bits=_mm256_or_si256(bits,_mm256_inserti128_si256(_mm256_setzero_si256(),_mm_or_si128(x,y),0));
  v=_mm256_add_epi32(v,_mm256_inserti128_si256(_mm256_setzero_si256(),_mm_madd_epi16(x,y),0));
  i+=8;
 }
 for(;i<n;i++){mask|=a[i]|b[i];tail+=(uint32_t)a[i]*b[i];}
 if(n<=256 && !(mask>>12) && _mm256_testz_si256(bits,_mm256_set1_epi16((short)0xf000))){
  __m128i s=_mm_add_epi32(_mm256_castsi256_si128(v),_mm256_extracti128_si256(v,1));
  s=_mm_hadd_epi32(s,s);s=_mm_hadd_epi32(s,s);
  return fast_reduce4093(tail+(uint32_t)_mm_cvtsi128_si32(s));
 }
 uint64_t z=0;for(i=0;i<n;i++)z+=(uint64_t)a[i]*b[i];
 return (uint16_t)(z%4093u);
}
#endif
