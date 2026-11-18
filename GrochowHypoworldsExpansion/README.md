# Grochow Hypoworlds expansion

This packet extends the original 82-question ledger with related propositions in finite-field isometry, group epimorphism counting, geometric solvability, cellular automata, arithmetic circuits, and proof complexity. The proof notes are informal. The Python replay checks logical consequences of the entered rules, with a separate profile that omits informal premises.

## Proofs and reductions

- [Field transfer and involutive norms](FIELDS.md). Ordered bilinear, alternating, and quadratic tuple isometry over fixed finite characteristic-two fields have the same polynomial-time status as norm membership in arbitrary finite-dimensional binary algebras with involution. The construction gives polynomial-time radical congruence, an explicit example where quotient norm roots cannot all lift, and a conditional exact counting algorithm for certain group epimorphisms. A separate effective modular transfer applies to geometric solvability over algebraic closures.
- [Group pebble games](GAMES.md). Two-colored elementary abelian groups separate bounded-width play at the second and third levels of Hella's hierarchy. The proof preserves the whole marked subgroup.
- [Cellular-automaton coarse-graining](AUTOMATA.md). At block size two a fixed eight-symbol target gives NP-completeness with a variable fine alphabet and explicit rules. The reduction gives an exact count in terms of graph colorings. A separate result extends the all-size obstruction to finite abelian targets.
- [Rational oracles and ideal degrees](ARITHMETIC.md). High-power oracle elimination survives rational division, with a multi-index version. There are continuum many incomparable minimal degrees in a polynomial-degree two-generated prime ideal. A separate general polynomial-system IPS construction gives linear versus logarithmic certificate size at two degree cutoffs.

In the full ledger, binary tuple isometry in P and arbitrary binary involutive norm membership outside P are incompatible. A polynomial-time algorithm for the explicit variable-alphabet coarse-graining tables without (P=NP) is incompatible. The truth of the published binary tuple-isometry question, ordinary uncolored group comparison, and the ordinary CNF interpretation of the IPS tradeoff require separate evidence.

## Replay results

| Profile | Propositions | Rules | Forced true | Forced false | Pair-only contradictions | Minimal three-premise contradictions |
|---|---:|---:|---:|---:|---:|---:|
| Previous full ledger | 186 | 211 | 25 | 28 | 225 | — |
| [Expanded, published premises](published-summary.json) | 211 | 181 | 11 | 0 | 267 | 172 |
| [Expanded, with informal premises](local-summary.json) | 211 | 244 | 37 | 32 | 316 | 181 |

One three-way conflict assumes a polynomial reduction from binary TI to rational TI and from rational TI to ternary TI, while denying a reduction from binary to ternary TI. Each pair of assumptions is consistent with the ledger. The three together contradict composition. See the [published](published-triples.csv) and [expanded](local-triples.csv) lists for the full scan. Counts include inherited propositions and their logical consequences.

## Reproduce

Run the following from this directory with Python 3. No third-party packages are required.

```sh
python worlds.py --profile local --triples --output local-replay
python worlds.py --profile published --triples --output published-replay
python worlds.py --assume T10_F2 '!StarNorm_F2_P'
python worlds.py --assume T4_2_Q T4_Q_3 '!T3_2_3'
```

A minimal three-premise conflict has satisfiable proper subassignments and no satisfying complete assignment. The replay counts complete Boolean assignments exactly. Its scope is the finite ledger, including each rule's stated hypotheses. A satisfying assignment only indicates consistency with the entered rules.

The file [claims.txt](claims.txt) gives the proposition meanings. [rules.txt](rules.txt) records their sources, proof explanations, and evidence profile. Contradictions inferred from informal statements inherit that status.
