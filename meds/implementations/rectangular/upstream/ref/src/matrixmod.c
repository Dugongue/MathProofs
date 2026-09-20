#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "log.h"
#include "profiler.h"
#include "params.h"
#include "matrixmod.h"

void pmod_mat_print(pmod_mat_t *M, int M_r, int M_c)
{
  pmod_mat_fprint(stdout, M, M_r, M_c);
}

void pmod_mat_fprint(FILE *stream, pmod_mat_t *M, int M_r, int M_c)
{
  GFq_t max = 0;

  for (int i = 0; i < M_r*M_c; i++)
    if (M[i] > max)
      max = M[i];

  char tmp[32];

  snprintf(tmp, sizeof(tmp), "%u", max);

  int len = strlen(tmp);

  char fmt0[32] = {"%"};
  char fmt1[32] = {"%"};

  snprintf(fmt0+1, 31, "%iu ", len);
  snprintf(fmt1+1, 31, "%iu", len);

  for (int r = 0; r < M_r; r++)
  {
    fprintf(stream, "[");
    for (int c = 0; c < M_c-1; c++)
      fprintf(stream, fmt0, pmod_mat_entry(M, M_r, M_c, r, c));
    fprintf(stream, fmt1, pmod_mat_entry(M, M_r, M_c, r, M_c-1));
    fprintf(stream, "]\n");
  }
}

void pmod_mat_mul(pmod_mat_t *C, int C_r, int C_c, pmod_mat_t *A, int A_r, int A_c, pmod_mat_t *B, int B_r, int B_c)
{
  PROFILER_START("pmod_mat_mul");
  GFq_t tmp[C_r*C_c];

  for (int c = 0; c < C_c; c++)
    for (int r = 0; r < C_r; r++)
    {
      uint64_t val = 0;

      for (int i = 0; i < A_c; i++)
        val = (val + (uint64_t)pmod_mat_entry(A, A_r, A_c, r, i) * (uint64_t)pmod_mat_entry(B, B_r, B_c, i, c));

      tmp[r*C_c + c] = val % MEDS_p;
    }

  for (int c = 0; c < C_c; c++)
    for (int r = 0; r < C_r; r++)
      pmod_mat_set_entry(C, C_r, C_c, r, c, tmp[r*C_c + c]);
  PROFILER_STOP("pmod_mat_mul");
}

int pmod_mat_syst_ct(pmod_mat_t *M, int M_r, int M_c)
{
  PROFILER_START("pmod_mat_syst_ct");
  int result = pmod_mat_syst_ct_partial_swap_backsub(M, M_r, M_c, M_r, 0, 1);
  PROFILER_STOP("pmod_mat_syst_ct");
  return result;
}

int pmod_mat_syst_ct_partial(pmod_mat_t *M, int M_r, int M_c, int max_r)
{
  PROFILER_START("pmod_mat_syst_ct_partial");
  int result = pmod_mat_syst_ct_partial_swap_backsub(M, M_r, M_c, max_r, 0, 1);
  PROFILER_STOP("pmod_mat_syst_ct_partial");
  return result;
}

int pmod_mat_rref(pmod_mat_t *M, int M_r, int M_c)
{
  PROFILER_START("pmod_mat_rref");
  int result = pmod_mat_syst_ct_partial_swap_backsub(M, M_r, M_c, M_r, 1, 1);
  PROFILER_STOP("pmod_mat_rref");
  return result;
}

int pmod_mat_syst_ct_partial_swap_backsub(pmod_mat_t *M, int M_r, int M_c, int max_r, int swap, int backsub)
{
  PROFILER_START("pmod_mat_syst_ct_partial_swap_backsub");
  int ret = M_r * swap;

  for (int r = 0; r < max_r; r++)
  {
    if (swap)
    {
      GFq_t z = 0;

      // compute condition for swap
      for (int r2 = r; r2 < M_r; r2++)
        z |= pmod_mat_entry(M, M_r, M_c, r2, r);

      int do_swap = GFq_eq0(z);

      // conditional swap
      {
        ret = r*do_swap + ret*(1-do_swap);

#if DEBUG
        if (do_swap)
        {
          LOG("swapping %i", r);

          LOG_MAT(M, M_r, M_c);
        }
#endif

        for (int i = 0; i < M_r; i++)
          GFq_cswap(&pmod_mat_entry(M, M_r, M_c, i, r),
                    &pmod_mat_entry(M, M_r, M_c, i, M_c-1),
                    do_swap);

#if DEBUG
        if (do_swap)
          LOG_MAT(M, M_r, M_c);
#endif
      }
    }

    for (int r2 = r+1; r2 < M_r; r2++)
    {
      uint64_t Mrr = pmod_mat_entry(M, M_r, M_c, r, r);

      for (int c = r; c < M_c; c++)
      {
        uint64_t val = pmod_mat_entry(M, M_r, M_c, r2, c);

        uint64_t Mrc = pmod_mat_entry(M, M_r, M_c, r, c);

        pmod_mat_set_entry(M, M_r, M_c, r, c, (Mrc + val * GFq_eq0(Mrr)) % MEDS_p);
      }
    }

    uint64_t val = pmod_mat_entry(M, M_r, M_c, r, r);

    if (val == 0)
    {
      PROFILER_STOP("pmod_mat_syst_ct_partial_swap_backsub");
      return -1;
    }

    val = GF_inv(val);

    // normalize
    for (int c = r; c < M_c; c++)
    {
      uint64_t tmp = ((uint64_t)pmod_mat_entry(M, M_r, M_c, r, c) * val) % MEDS_p;
      pmod_mat_set_entry(M, M_r, M_c, r, c, tmp);
    }

    // eliminate
    for (int r2 = r+1; r2 < M_r; r2++)
    {
      uint64_t factor = pmod_mat_entry(M, M_r, M_c, r2, r);

      for (int c = r; c < M_c; c++)
      {
        uint64_t tmp0 = pmod_mat_entry(M, M_r, M_c, r, c);
        uint64_t tmp1 = pmod_mat_entry(M, M_r, M_c, r2, c);

        uint64_t val = (tmp0 * factor) % MEDS_p;

        val = (MEDS_p + tmp1 - val) % MEDS_p;

        pmod_mat_set_entry(M, M_r, M_c,  r2, c, val);
      }
    }
  }

  if (!backsub)
  {
    PROFILER_STOP("pmod_mat_syst_ct_partial_swap_backsub");
    return ret;
  }

  // back substitution
  for (int r = max_r - 1; r >= 0; r--)
    for (int r2 = 0; r2 < r; r2++)
    {
      uint64_t factor = pmod_mat_entry(M, M_r, M_c, r2, r);

      uint64_t tmp0 = pmod_mat_entry(M, M_r, M_c, r, r);
      uint64_t tmp1 = pmod_mat_entry(M, M_r, M_c, r2, r);

      uint64_t val = (tmp0 * factor) % MEDS_p;

      val = (MEDS_p + tmp1 - val) % MEDS_p;

      pmod_mat_set_entry(M, M_r, M_c,  r2, r, val);

      for (int c = max_r; c < M_c; c++)
      {
        uint64_t tmp0 = pmod_mat_entry(M, M_r, M_c, r, c);
        uint64_t tmp1 = pmod_mat_entry(M, M_r, M_c, r2, c);

        uint64_t val = (tmp0 * factor) % MEDS_p;

        val = (MEDS_p + tmp1 - val) % MEDS_p;

        pmod_mat_set_entry(M, M_r, M_c,  r2, c, val);
      }
    }

  PROFILER_STOP("pmod_mat_syst_ct_partial_swap_backsub");
  return ret;
}

GFq_t GF_inv(GFq_t val)
{
  // PROFILER_START("GF_inv");
//  if (MEDS_p == 8191)
//  {
//    // Use an optimal addition chain...
//    uint64_t tmp_0  = val;                          //  0                1
//    uint64_t tmp_1  = (tmp_0 * tmp_0) % MEDS_p;     //  1( 0)            2
//    uint64_t tmp_2  = (tmp_1 * tmp_0) % MEDS_p;     //  2( 1, 0)         3
//    uint64_t tmp_3  = (tmp_2 * tmp_1) % MEDS_p;     //  3( 2, 1)         5
//    uint64_t tmp_4  = (tmp_3 * tmp_3) % MEDS_p;     //  4( 3)           10
//    uint64_t tmp_5  = (tmp_4 * tmp_3) % MEDS_p;     //  5( 4, 3)        15
//    uint64_t tmp_6  = (tmp_5 * tmp_5) % MEDS_p;     //  6( 5)           30
//    uint64_t tmp_7  = (tmp_6 * tmp_6) % MEDS_p;     //  7( 6)           60
//    uint64_t tmp_8  = (tmp_7 * tmp_7) % MEDS_p;     //  8( 7)          120
//    uint64_t tmp_9  = (tmp_8 * tmp_8) % MEDS_p;     //  9( 8)          240
//    uint64_t tmp_10 = (tmp_9 * tmp_5) % MEDS_p;     // 10( 9, 5)       255
//    uint64_t tmp_11 = (tmp_10 * tmp_10) % MEDS_p;   // 11(10)          510
//    uint64_t tmp_12 = (tmp_11 * tmp_11) % MEDS_p;   // 12(11)         1020
//    uint64_t tmp_13 = (tmp_12 * tmp_2) % MEDS_p;    // 13(12, 2)      1023
//    uint64_t tmp_14 = (tmp_13 * tmp_13) % MEDS_p;   // 14(13)         2046
//    uint64_t tmp_15 = (tmp_14 * tmp_14) % MEDS_p;   // 15(14)         4092
//    uint64_t tmp_16 = (tmp_15 * tmp_15) % MEDS_p;   // 16(15)         8184
//    uint64_t tmp_17 = (tmp_16 * tmp_3) % MEDS_p;    // 17(16, 3)      8189
//
//    return tmp_17;
//  }
//  else if (MEDS_p == 4093)
//  {
//    // Use an optimal addition chain...
//   uint64_t tmp_0  = val;                          //  0                1
//   uint64_t tmp_1  = (tmp_0 * tmp_0) % MEDS_p;     //  1( 0)            2
//   uint64_t tmp_2  = (tmp_1 * tmp_1) % MEDS_p;     //  2( 1)            4
//   uint64_t tmp_3  = (tmp_2 * tmp_0) % MEDS_p;     //  3( 2, 0)         5
//   uint64_t tmp_4  = (tmp_3 * tmp_3) % MEDS_p;     //  4( 3)           10
//   uint64_t tmp_5  = (tmp_4 * tmp_3) % MEDS_p;     //  5( 4, 3)        15
//   uint64_t tmp_6  = (tmp_5 * tmp_5) % MEDS_p;     //  6( 5)           30
//   uint64_t tmp_7  = (tmp_6 * tmp_6) % MEDS_p;     //  7( 6)           60
//   uint64_t tmp_8  = (tmp_7 * tmp_7) % MEDS_p;     //  8( 7)          120
//   uint64_t tmp_9  = (tmp_8 * tmp_8) % MEDS_p;     //  9( 8)          240
//   uint64_t tmp_10 = (tmp_9 * tmp_5) % MEDS_p;     // 10( 9, 5)       255
//   uint64_t tmp_11 = (tmp_10 * tmp_10) % MEDS_p;   // 11(10)          510
//   uint64_t tmp_12 = (tmp_11 * tmp_11) % MEDS_p;   // 12(11)         1020
//   uint64_t tmp_13 = (tmp_12 * tmp_12) % MEDS_p;   // 13(12)         2040
//   uint64_t tmp_14 = (tmp_13 * tmp_3) % MEDS_p;    // 14(13, 3)      2045
//   uint64_t tmp_15 = (tmp_14 * tmp_14) % MEDS_p;   // 15(14)         4090
//   uint64_t tmp_16 = (tmp_15 * tmp_0) % MEDS_p;    // 16(15, 0)      4091
//
//   return tmp_16;
//  }
//  else
  {
    uint64_t exponent = MEDS_p - 2;
    uint64_t t = 1;

    while (exponent > 0)
    {
      if ((exponent & 1) != 0)
        t = (t*(uint64_t)val) % MEDS_p;

      val = ((uint64_t)val*(uint64_t)val) % MEDS_p;

      exponent >>= 1;
    }

    // PROFILER_STOP("GF_inv");
    return t;
  }
}

int pmod_mat_inv(pmod_mat_t *B, pmod_mat_t *A, int A_r, int A_c)
{
  PROFILER_START("pmod_mat_inv");
  pmod_mat_t M[A_r * A_c*2];

  for (int r = 0; r < A_r; r++)
  {
    memcpy(&M[r * A_c*2], &A[r * A_c], A_c * sizeof(GFq_t));

    for (int c = 0; c < A_c; c++)
      pmod_mat_set_entry(M, A_r, A_c*2, r, A_c + c, r==c ? 1 : 0);
  }

  int ret = pmod_mat_syst_ct(M, A_r, A_c*2);

  if ((ret == 0) && B)
    for (int r = 0; r < A_r; r++)
      memcpy(&B[r * A_c], &M[r * A_c*2 + A_c], A_c * sizeof(GFq_t));

  PROFILER_STOP("pmod_mat_inv");
  return ret;
}

