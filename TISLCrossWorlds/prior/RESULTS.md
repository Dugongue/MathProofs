# Direct progress on the square-zero sign comparison over F3

Let \(H\) denote deterministic polynomial-time many-one reduction from determinant-one to ordinary three-tensor isomorphism over \(\mathbb F_3\). The input is the square-zero operator carrier
\[
{\cal S}(A)=\{(u,v,w)\mapsto (0,0,au+bv):a,b\in A\},\qquad
A=\mathbb F_3 1\oplus X\oplus Z,
\]
where \(J=X\oplus Z\) is the radical, \(J^2=\operatorname{Ann}_J(J)=Z\), \(X\) has even dimension, and \(Z\) has odd dimension. The older proof identifies the determinant of every conjugator with \(\det g_X\det h_Z\) on the two grades of the associated symmetric radical bimap \(\beta\). The unrestricted sign comparison in this carrier remains open. [Previous exact equivalence](earlier/SquareZeroClosure.md) · [Chen, Grochow, Qiao, Tang and Zhang, Open Question 1.9](https://arxiv.org/html/2306.03135v2#S1.SS5)

## Strongest assembly theorem

Compute the primitive centroid factors of \(\beta\) and their canonical residue fields \(E_i\). There is a single deterministic ordinary TI output for the full square-zero comparison if **each factor has odd \(\dim_{E_i}X_i\), or the kernel of \(\operatorname{Sym}_{E_i}^2 X_i\to Z_i\) has dimension \(O(\log L)\) over \(E_i\)**, where \(L\) is the explicit coefficient input length. The two original role dimensions, field degrees, number of factors and repetitions of each factor type may grow without this bound.

For odd relative input rank, an \(E_i\)-scalar of norm \(-1\), together with its square on \(Z_i\), supplies a real odd correction. For even relative input rank, the symmetric-square determinant identity cancels the large input determinant. Only the determinant on the small relation space and the explicit sign of a finite-field Frobenius action remain.

The assembly theorem is more general than this subclass. It applies whenever each required local positive and negative sign test has a uniform ordinary compiler. An odd local automorphism, or two ordinarily isomorphic odd-dimensional blocks, supplies an odd correction and is tested by a positive ordinary disjunction. Otherwise the matching of odd blocks is unique under the ordinary guard. The allowed edges in each of its rows are complementary one-hot tests, so the atlas determinant compiler gives the permutation sign. Local edge signs on rigid factors factor through a reference object within each type; odd row and column incidences give the exact total sign by one linear switch system. Actual perfect matching is used in the proof of reflection and lift, and does not have to be found during construction. All cases combine into one ordinary TI instance. [Proof](PrimitiveAssembly.md)

## Other complete one-query regimes

- **Cyclic scalar slices.** If the scalar slice space is \(B C\) for a nonsingular symmetric slice \(B\) and some local factor of its right idealizer \(C\) is Frobenius and odd-dimensional, a constructible orthogonal reflection fixes every scalar slice and reverses the sign. Ordinary comparison is then sufficient. The input need not supply \(B\), or be free over \(C\). For non-Frobenius \(C\), the regular-plus-dual model still carries the full degree question, even though all slice ratios commute and every scalar slice is split on its nonsingular quotient. [Proof](CyclicSlices.md)
- **Probe and relation compilers.** Two scalar probes with a nonsingular first probe suffice when the output is logarithmic and the relevant primary multiplicities are logarithmic. The multiplicity condition is needed only at odd lengths and odd-degree primary fields; even-degree blocks can be arbitrarily large. There is also an independent compiler using an explicitly small Koszul homology space. The original algebra frames can be recovered in polynomial time from raw conjugate matrix-space presentations on the carrier promise. [Proofs](PrimaryAndKoszul.md)
- **Recoverable polarizations.** A hyperbolic bimap with an intrinsically recoverable pair of polarizations and a small balanced relation space has a one-query compiler, including sign-rigid examples with large original grades and large unbalanced symmetric relation space. A different criterion uses alternating trace-commutator forms when probes can be enumerated and the indicated radicals are small. [Proofs](PolarizedAndProbe.md)

## The narrower unresolved case

The square-zero missing lemma remains equivalent to \(H\) even with the additional promises that **the radical bimap's centroid is exactly \(\mathbb F_3\)** and that the scalar slices include a split nonsingular form. No isomorphism has to preserve a supplied choice of nonsingular form. The modified determinant-character construction gives every auxiliary output coordinate a cross-role generator. Any remaining centroid operator after removing its scalar part would have to act through a dual marker, and such an operator vanishes on all cross-role generators. Therefore the centroid is precisely the scalars, while every original determinant sign is preserved.

These exact carriers already have just one primitive factor. Their normalized scalar commutators have zero pairwise products, so the trace-commutator probe pairing is identically zero on the output dual. The factor and probe reductions therefore leave the single-factor scalar-centroid promise unresolved. A one-query ordinary compiler for that promise would settle \(H\). [Exact restricted lower and upper reductions](ScalarCentroid.md)

The reductions are written proofs. The independent Lean check covers the weighted incidence identity used in the assembly theorem. [Verification](Verification.json)
