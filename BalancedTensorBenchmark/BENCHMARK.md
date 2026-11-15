# Benchmark results

The implicit balanced pipeline decided all 106 test pairs. The clearest direct effect of the layout was in the controlled grouped-rank experiment. With the same backend and 250 ms native budget, balanced group sizes finished 105 of 106 cases and the half split finished 74. In the production pipeline, packing the tensor as a named product system avoids the need to allocate the ordinary rank-marker coordinates.

## Main comparison

Experiments ran on Windows on an Intel Core i7-10700F, using GCC 15.2.0 with C++20 and native optimization, CPython 3.13, and NumPy 2.5.4. Timings include the warm file read, encoder or reference input construction, transfer to the backend, decision, and positive-witness verification. The first process launch is excluded for the two persistent backends. The native run used seven samples per case, with one attempt on a timeout. Traces used three samples per case. The table gives the median of the case medians and a separate median of paired per-case speed ratios.

| Order, all original sides 2 | Pairs | Implicit balanced | Warm Traces 2.7r1.p1 | Median paired ratio |
|---|---:|---:|---:|---:|
| 3 | 4 | 0.427 ms | 0.705 ms | 1.6× |
| 4 | 12 | 0.419 ms | 0.869 ms | 1.9× |
| 6 | 19 | 0.563 ms | 4.418 ms | 5.6× |
| 8 | 15 | 0.855 ms | 47.332 ms | 51× |
| 10 | 15 | 1.914 ms | 588.776 ms | 306× |
| 12 | 12 | 5.717 ms | 7,397.672 ms | 1,204× |

Traces decides the same binary isomorphism relation via a colored incidence graph. Over $\mathbf F_2$ the action of $\mathrm{GL}_2$ on the three nonzero covectors is the full symmetric group. Evaluating a tensor at all pure covector tuples and using its support as a colored hypergraph therefore preserves and reflects the decision. This reference uses cheap projective-count rejection before full graph canonization. All 231 reference samples were decided correctly, including the independently checked positive witnesses. The warm startup was 18.5 ms. The ratios include graph construction and text transfer of graphs containing up to order $3^d$ vertices, so these are full pipeline ratios for the tested adapters. [nauty and Traces](https://pallini.di.uniroma1.it/).

The CaDiCaL 2.1.2 reference used staged CNF equations of the original tensor action with inverse constraints on each factor. It measured 28 selected cases with three repeats when successful. Of these, 21 decided on all repeats, six reached the two-second solver timeout without deciding, and one decided on a repeat before a later timeout. Among the 22 cases with a completed reference verdict, the median paired ratio was 60×, with reference process launch included. Timeouts are excluded from that ratio and retained in the raw results. [CaDiCaL](https://github.com/arminbiere/cadical).

## What balance changed

Fix the grouped-rank backend and change only the forest shape. The balanced forest cuts the leaf list into three near-equal parts. The half control cuts off $\lfloor d/2\rfloor$ leaves and ends with a singleton. Each test contracts one whole root against pure covectors and takes the rank across the two remaining roots. The balanced layout more often gives near-square matrices, whose rank profiles distinguished local actions much more strongly in these data.

| Input | Cases | Balanced grouped ranks | Half grouped ranks |
|---|---:|---:|---:|
| Order 6, all sides 2 | 20 | 20, 0.553 ms | 20, 0.577 ms |
| Order 8, all sides 2 | 16 | 16, 0.842 ms | 16, 2.790 ms |
| Order 10, all sides 2 | 16 | 16, 2.147 ms | 2 |
| Order 12, all sides 2 | 13 | 12, 5.417 ms | 1 |
| All formats | 106 | 105 | 74 |

Cells show completions and, where informative, the median time among completions. In the order-8 set, the median native search node count fell from 5,726 to 13.5. The production backend uses pair-contraction ranks, which resolved the adversarial order-12 negative that timed out under grouped ranks.

A second, independently implemented backend retains the whole grouped-mode rank table and checks compatible tuples of leaf maps within each group. With persistent workers, randomized interleaving, the same direct-rank fallback, and compact ordinary descriptors constructed on every run, the 12 shared order-12 cases took **9.61 ms balanced versus 11.77 ms half split**, a 1.22× median-to-median end-to-end gain. Backend times were 0.82 versus 2.84 ms. All cases completed under both layouts. Balanced required no fallback on this cohort and half required fallback on all 12 cases. This comparison measures the advantage of grouping while holding the search and compilation policy fixed.

In the main 106-case run, the pair-rank backend took 0.786 ms median with the implicit balanced compiler and 0.713 ms directly on the original tensor. With the same backend, building compact balanced run descriptors took 6.310 ms median end to end, compact half run descriptors took 5.889 ms, and the published path-algebra descriptors took 0.857 ms. The direct exhaustive control completed 58 cases. These comparisons isolate the benefit of the implicit representation and the search from the extra work of constructing the ordinary encodings. The separate covector-count experiment compares with a stronger meet-in-the-middle control. [Covector backend benchmark](SOLVER-TRANSFER.md).

For a six-way input with side 2, the original geometric compiler gives about $1.74\cdot10^{46}$ dense entries. The revised binary spectral compiler and schedule cut that to $9.62\cdot10^{13}$, or 366,490 nonzero entries for the all-one sample. The published path-algebra comparator is still much smaller at $50^3=125{,}000$ dense entries and 334 nonzero entries. The implicit balanced payload itself has shape $4\times4\times4$, with the product-tree equations stored separately. The literal ordinary outputs were evaluated for size, and the tests called structured solvers on run descriptors or named systems. These measurements establish practical speedups for the stated binary workload. They leave open how an unmodified ordinary three-tensor solver would scale on the explicit reduction outputs.

## Correctness controls

The native rank backend agreed with an independently computed orbit partition on all 32,896 unordered pairs, including equal pairs, of binary $2\times2\times2$ tensors. There were eight orbits. Positives in the larger benchmark were built by applying invertible maps. Negatives had exact cut-rank witnesses or came from the adversarial seed whose orbit was exhausted independently. The encoder was cross-checked over $\mathbf F_2,\mathbf F_3,\mathbf F_5$ on small coordinate expansions. The separate encoding controls checked 1,125 path-algebra associativity triples, 196 spectral contamination cases, and explicit lifted binary transporters. There is no dependence on running Lean for these benchmark replays. The original Lean equivalence is cited in the package, while the executable code and the smaller tag policies were reviewed informally.
