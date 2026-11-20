# Underused methods for tensors and group isomorphism problems

Four written proofs using matroid degenerations, Brauer classes, p-adic Lie coordinates, and extension-class orbits. The notes credit the closest established results and state the hypotheses needed for the new applications. Publication priority, human review, and Lean formalization remain pending.

| Method | Result |
|---|---|
| [Matroids and diagonal tensors](TENSORS.md) | Directional degeneration is NP-complete on an explicitly presented concise family whose two endpoints have both ordinary and border rank equal to their largest side. A fixed labelling has a polynomial-time test and Laurent certificates. A separate \(6\times6\times4\) example has more than one geometric branch at an encoded degeneration point of minimum rank. |
| [Brauer classes and generic representatives](GEOMETRY.md) | Computes exact indices and periods of all partition classes for the generic torsor of an effectively generically free tensor format. A rational section exists precisely for pairwise coprime mode dimensions. For the indicated pure complex tensor formats, the obstruction gives explicit divisibility of descent degrees. |
| [p-adic logarithms and Smith coordinates](PADIC.md) | Gives exact local search, decision, and counting modulo \(p^r\), with a sharp precision-loss bound for repair. The algorithm is local to a prescribed congruence coset. Its number of residue-coset tests for global comparison is independent of the final precision. |
| [Extension-class orbits and group epimorphisms](GROUPS.md) | Gives polynomial Cayley-table time for deciding, constructing, and exactly counting epimorphisms in the stated abelian-Hall families, including nonsplit bounded-support action-kernel extensions and a nonabelian complement case with bounded central-kernel generator number and bounded central index. |

The Python controls supplement the written proofs. The p-adic replay exhausts two small congruence groups and checks 64 additional uneven-precision targets. The matroid and group controls test their respective finite examples. The Brauer argument uses explicit cyclic division algebras and a versal specialization argument.
