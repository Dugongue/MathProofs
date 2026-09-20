#ifndef MATRIXMOD_H
#define MATRIXMOD_H

#include <stdio.h>
#include <stdint.h>

#include "params.h"


static inline
uint64_t eq(uint64_t a, uint64_t b)
{
	uint64_t q = a ^ b;
	return ~(q | -q) >> 63;
}

static inline
GFq_t GFq_eq0(GFq_t x)
{
	uint64_t q = (uint64_t)x;
	return ~(q | -q) >> 63;
}

static inline
void GFq_cswap(GFq_t *a, GFq_t *b, int cond)
{
   GFq_t diff = (*a ^ *b) * cond;

   *a ^= diff;
   *b ^= diff;
}

static inline
void GFq_cmov(GFq_t *a, const GFq_t b, int cond)
{
   GFq_t diff = (*a ^ b) * cond;

   *a ^= diff;
}


#define pmod_mat_entry(M, M_r, M_c, r, c) M[(M_c)*(r)+(c)]

#define pmod_mat_set_entry(M, M_r, M_c, r, c, v) (M[(M_c)*(r)+(c)] = v)

#define pmod_mat_t GFq_t

void pmod_mat_print(pmod_mat_t *M, int M_r, int M_c);
void pmod_mat_fprint(FILE *stream, pmod_mat_t *M, int M_r, int M_c);

void pmod_mat_mul(pmod_mat_t *C, int C_r, int C_c, pmod_mat_t *A, int A_r, int A_c, pmod_mat_t *B, int B_r, int B_c);


int pmod_mat_syst_ct_partial_swap_backsub(pmod_mat_t *M, int M_r, int M_c, int max_r, int swap, int backsub);

int pmod_mat_syst_ct(pmod_mat_t *M, int M_r, int M_c);
int pmod_mat_syst_ct_partial(pmod_mat_t *M, int M_r, int M_c, int max_r);

int pmod_mat_rref(pmod_mat_t *M, int M_r, int M_c);

int pmod_mat_inv(pmod_mat_t *B, pmod_mat_t *A, int A_r, int A_c);

GFq_t GF_inv(GFq_t val);

#endif

