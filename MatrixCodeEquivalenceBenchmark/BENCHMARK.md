# End-to-end matrix-code equivalence results

## Published representatives

The prime-field prototype correctly decided all 89 pairs induced by Morrison’s published representatives across five repeats each. The labels were independently checked under unrestricted left–right GL equivalence. There were 2 positive and 87 negative pairs. Thirteen negatives matched on the full codeword-rank histogram. Morrison’s original classification uses the subgroup preserving self-duality, so its class numbers alone cannot label this benchmark. [Morrison, Tables 1–2](https://arxiv.org/abs/1505.07363) · [Dataset details](DATASETS.md)

| Field | Matrix size | Generators | Verdict | Prototype | CaDiCaL adapter | Exact two-row reference |
| --- | --- | --- | --- | ---: | ---: | ---: |
| F₂ | 2 × 3 | 02, 05 | No | 1.565 ms | 21.322 ms | 1.045 ms |
| F₂ | 2 × 3 | 01, 02 | No | 0.282 ms | 20.099 ms | 1.220 ms |
| F₃ | 2 × 4 | 01, 03 | No | 4.788 ms | 1,204.634 ms | 17.919 ms |
| F₃ | 2 × 4 | 08, 11 | No | 0.316 ms | 503.419 ms | 343.492 ms |
| F₃ | 2 × 4 | 01, 06 | Yes | 2.450 ms | 102.653 ms | 2.838 ms |
| F₃ | 2 × 4 | 05, 10 | Yes | 1.801 ms | 187.778 ms | 1.333 ms |

The median of the six paired speedups over the exact CaDiCaL adapter was 87.7×. That adapter includes CNF construction and solver-process launch. Against the more direct exact two-row reference, the prototype won four and lost two. In table order the approximate ratios were 0.67×, 4.32×, 3.74×, 1,086×, 1.16×, and 0.74×. These six matched pairs include both positives. Times are per-instance medians with five prototype repeats, three CaDiCaL repeats, and nine two-row repeats. Timing starts before reading the input and includes positive-witness verification. Interpreter startup is outside the timed interval. [Reference implementations and commands](ref_notes.md) · [Prototype raw results](morrison-results-final.json) · [Reference raw results](ref_results.json)

## Larger cases

| Case | Field | Matrix size | Code dimension | Prototype median |
| --- | --- | --- | ---: | ---: |
| Oxford MEDS teaching example | F₁₃ | 4 × 6 | 5 | 41.91 ms |
| Independently rebased Oxford | F₁₃ | 4 × 6 | 5 | 44.84 ms |
| Oxford amplified by 2 | F₁₃ | 8 × 12 | 5 | 78.27 ms |
| Oxford amplified by 3 | F₁₃ | 12 × 18 | 5 | 167.34 ms |
| Oxford amplified by 4 | F₁₃ | 16 × 24 | 5 | 374.96 ms |
| Trace dual of the last amplification | F₁₃ | 16 × 24 | 379 | 1.04 s |

Every Oxford result included a checked witness. The amplifications and dual are constructed examples sharing the published seed. The dual solver exploits codimension 5, so dimension 379 here measures recovery in a high-dimensional output space. The same two Oxford 4 × 6 inputs took 247.48 ms and 236.25 ms on the NumPy-only path, giving 5.90× and 5.27× against the same algorithm without native kernels. The comparisons above are medians over seven trials, or five for the dual. [Oxford example](https://www.maths.ox.ac.uk/system/files/inline-files/meds.pdf) · [Raw Oxford and KAT runs](mce-results-final.json) · [Dual timings](dual-results.json)

CaDiCaL reached its reference time or construction caps on the Oxford inputs. The bounded Highway to Hull adaptation also returned unknown on them. Its positive control succeeded, and the published Magma implementation was unavailable. All four distinct official MEDS v1.1 KAT pairs exceeded the prototype’s projective search cap. These are coverage results on public generator data. [Reference details](ref_notes.md) · [Official MEDS test data](https://www.meds-pqc.org/KAT/MEDS-KAT-2023-07-26.tgz)

## What the binary transfer changed

On four synthetic 16 × 18 positives of code dimension 8, the same packed solver went from 115.00 ms with single-word ranks to 6.23 ms with richer rank profiles, an 18.5× end-to-end gain. When single-word ranks were uniform, the richer solver decided all 16 synthetic rectangular cases of sizes 16 × 32 and 32 × 64, with cohort medians from 5.44 to 24.18 ms. The rank-only ablation hit its two-second search cap on all 16. On four planted 128 × 128 positives of code dimension 12, the richer version verified answers in a median 464.10 ms, compared with 445.97 ms for rank-only. At that size rank computation dominated and the extra invariants cost about 4%. [Binary method and controls](mce_backend.md) · [Raw results](mce_backend_results.json)

Measurements used Windows, an Intel Core i7-10700F, GCC 15.2.0, Python 3.13.5 and NumPy 2.5.4. The prime-field kernel and lift passed 1,747 exact controls. The binary decision outputs matched 630 independently enumerated binary pairs and all 72 generated larger inputs. Results are specific to these cohorts, machines, and budget settings. The projective-space enumeration still grows with field size and coefficient dimension.
