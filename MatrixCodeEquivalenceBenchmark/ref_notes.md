# Reference solvers for the matrix-code benchmark

The decision problem here is left–right equivalence of matrix subspaces over a prime field. Each solver receives both ordered bases without a matching, an isomorphism, or a secret key. A positive answer includes invertible matrices $L,R,S$ satisfying $LA_iR=\sum_j S_{ij}B_j$ for every generator. The same independent Python verifier checks these equations and the three ranks on the original inputs.

## Implementations

- `ref_cadical.py` encodes the original bilinear equations and three matrix inverse equations as CNF with exact modular arithmetic. CaDiCaL 2.1.2 supplies SAT or UNSAT. The elapsed time covers reading the input, constructing and writing the CNF, launching the solver, reading its answer, and verifying a positive witness. The six Morrison verdicts also agree with the independent exhaustive linear-algebra decider in the dataset generator. [CaDiCaL](https://github.com/arminbiere/cadical)
- `ref_small_gl2.py` runs that exact two-row decider on the raw input and includes recovery and verification of the basis map. It enumerates projective left maps, then enumerates the kernel of the resulting right-map system. Its six cases give a direct linear-algebra comparison that avoids CNF construction and process startup.
- `ref_hull.py` is a bounded NumPy adaptation of the trace-hull collision and linearized conjugacy strategy of Couvreur and Levrat. It samples selectors, normalizes fingerprints under field scaling, and checks collision-derived witnesses. It searches a subset of the branches and may return unknown. A fixed-seed 3 × 3 positive control over `F5` exercised successful recovery. [Highway to Hull](https://arxiv.org/html/2504.01230)
- `ref_anchor_cadical.py` encodes the map between minimum-rank projective points as a SAT problem, and tries to lift each possible coefficient map via a linear system. Its timing is an ablation of the rank-anchor strategy. It returns unknown when a cap stops either stage.

Trimoska, Reijnders, and Samardjiska provide Magma implementations. Magma was unavailable in the test environment. The Magma timings in Narayanan, Qiao, and Tang concern different inputs, so the benchmark makes no runtime comparison to them. [Magma reference code](https://github.com/mtrimoska/matrix-code-equivalence) · [Algorithms for Matrix Code and Alternating Trilinear Form Equivalences, §4.6](https://eprint.iacr.org/2024/368)

## Completed comparisons

The medians below are over three direct SAT runs and nine two-row runs of each of six fixed Morrison pairs on the benchmark host. Selection includes both published-source positives and three negatives whose rank histograms agree. The input numbering follows the corresponding table in Morrison.

| Prime | Matrix dimensions | Generator numbers | Verdict | CaDiCaL median wall time | Exact two-row median wall time |
| --- | --- | --- | --- | ---: | ---: |
| 2 | 2 × 3 | 02, 05 | No | 21.322 ms | 1.045 ms |
| 2 | 2 × 3 | 01, 02 | No | 20.099 ms | 1.220 ms |
| 3 | 2 × 4 | 01, 03 | No | 1,204.634 ms | 17.919 ms |
| 3 | 2 × 4 | 08, 11 | No | 503.419 ms | 343.492 ms |
| 3 | 2 × 4 | 01, 06 | Yes | 102.653 ms | 2.838 ms |
| 3 | 2 × 4 | 05, 10 | Yes | 187.778 ms | 1.333 ms |

The raw and independently rebased Oxford instances each reached a five-second search cap in the direct CaDiCaL model, after emitting roughly 1.15 million clauses. The three amplified instances reached the three-million-clause construction cap. The seven MEDS KAT parameter labels represent four distinct record-zero pairs. All four reached the 500,000-clause construction cap on direct SAT. The rank-anchor SAT ablation reached its 12-second total cap on both raw and rebased Oxford inputs. The Hull adaptation returned unknown for all tested Oxford, Morrison, and KAT inputs. Budget outcomes report coverage and elapsed time up to the cap. Relative runtime ratios require both methods to return a verdict.

The raw timings, verdicts, and recovered witnesses are in [ref_results.json](ref_results.json).

## Reproduction

Place a `cadical` executable on disk and install NumPy for the two optional adapters. The direct SAT script needs only Python and CaDiCaL. See [DATASETS.md](DATASETS.md) for input provenance and reproduction.

```text
python ref_cadical.py --cadical PATH_TO_CADICAL --timeout 5 dataset/morrison/morrison-f3-2x4-g01-g06.txt
python ref_small_gl2.py --repeats 9 dataset/morrison/morrison-f3-2x4-g01-g06.txt
python ref_cadical.py --cadical PATH_TO_CADICAL --timeout 5 --clause-limit 3000000 dataset/oxford-meds-13-4-6-5.txt dataset/oxford-rebased.txt
python ref_anchor_cadical.py --cadical PATH_TO_CADICAL --timeout 12 dataset/oxford-meds-13-4-6-5.txt
python ref_hull.py --samples 8192 --timeout 5 dataset/oxford-meds-13-4-6-5.txt
```
