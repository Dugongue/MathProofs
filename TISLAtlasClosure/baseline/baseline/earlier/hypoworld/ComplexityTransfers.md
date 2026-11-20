# Computational consequences of fixed-field TI equality

Let $F=\mathbf F_3$. Inputs are two dense three-tensors in ordered bases. Let $\mathrm{TI}$ use arbitrary invertible maps in the three modes and $\mathrm{TI}_{\rm SL}$ use determinant-one maps. Write $\mathcal H$ for the hypothetical deterministic polynomial-time same-field many-one reduction $\mathrm{TI}_{\rm SL}\le_m\mathrm{TI}$. The reverse reduction is unconditional by adding a one-dimensional null summand to each mode. An ordinary map lifts by the reciprocal determinant on that line, and a padded transporter restricts to the contraction supports, from which its maps extend to the original spaces. The null-line construction applies to deficient supports as well. [Chen, Grochow, Qiao, Tang and Zhang, Open Question 1.9](https://arxiv.org/html/2306.03135v2#S1.SS5).

The statements below distinguish $\mathcal H$ from an independently available subquadratic-exponent algorithm for the signed problem. Write $n$ for maximum side length and $L$ for the dense bit input length.

## The entire determinant pattern and the orbit index

Let $G=\prod_i\operatorname{GL}(V_i)$, let $D=\{\pm1\}^3$, and let $\chi:G\to D$ be the modewise determinant. Its kernel is $K=\prod_i\operatorname{SL}(V_i)$. Assume positive mode dimensions. Zero-dimensional formats can be handled directly. For $d\in D$, choose a public modewise diagonal reflection $r_d$ of determinant tuple $d$, using the first coordinate in each relevant mode. For tensors $A,B$, define
$$
 {\cal C}(A,B)=\{\chi(g):gA=B\},\qquad
 H_A=\chi(\operatorname{Stab}_G(A)).
$$
For every $d$ there is a bijection
$$
 \{g:gA=B,\ \chi(g)=d\}
   \longleftrightarrow \operatorname{Iso}_K(A,r_d^{-1}B),
 \qquad g\longmapsto r_d^{-1}g.
$$
Thus eight nonadaptive signed decision calls compute the whole set ${\cal C}(A,B)$, and under $\mathcal H$ eight nonadaptive ordinary TI calls suffice. If an ordinary transporter $g_0$ exists, the transporter set is $g_0\operatorname{Stab}_G(A)$. This proves that ${\cal C}(A,B)=\chi(g_0)H_A$ and that each of its nonempty determinant fibers has the same cardinality.

Consequently the following quantities can all be computed with a fixed number of ordinary decision calls under $\mathcal H$.

- The affine determinant coset and its linear span data over $\mathbf F_2$, treating an empty transporter separately.
- The dimension of $H_A$ and the exact index $[\operatorname{Stab}_G(A):\operatorname{Stab}_K(A)]=|H_A|$.
- The number $8/|H_A|$ of determinant-one orbits inside $G A$. Indeed $K$ is normal, and the induced action of $D$ on those orbits is transitive with stabilizer $H_A$.
- The probability $1/|H_A|$ for any attainable determinant tuple in a uniformly random ordinary transporter, and zero for every unattainable tuple.
- The exact ratio $|G A|/|K A|=8/|H_A|$. Equivalently the difference of the two log-base-two orbit entropies is $3-\log_2|H_A|$.
- Whether any fixed determinant character is constant on all transporters and its constant value if applicable. On a nonempty transporter set it is constant precisely when it is trivial on $H_A$.

The number of calls is independent of $n$ and $L$. The same statements hold over any separately fixed finite field if the analogous hypothesis holds there, with $|D|=(q-1)^3$. The call bound grows as $(q-1)^3$ if the field varies.

## One ordinary instance for arbitrary allowed signs

Let $\Omega\subseteq D$ be specified and ask for a transporter with determinant tuple in $\Omega$. Under $\mathcal H$ this reduces to a single ordinary TI instance. To justify the single-instance assertion, ordinary TI has a uniform disjunction construction in addition to the usual conjunction construction.

View a tensor $T$ as a bilinear map $X\times Y\to Z$. Encode it as a finite-dimensional unital triangular algebra with three diagonal scalar idempotents, with nonzero corners $01=X$, $12=Y$, and $02=Z$, and with the only nonzero radical multiplication given by $T$. The radical is the sum of the off-diagonal corners. Different original formats stay distinguishable by the dimensions of these corners. An algebra isomorphism permutes the three primitive classes in the semisimple quotient. Their directed nonzero-corner graph has a unique topological order, forcing the classes to be preserved in order. To see this directly in the algebra, align their lifted idempotents by conjugation by a unit congruent to $1$ modulo the radical. If $(e_i)$ and $(f_i)$ are complete orthogonal idempotent families with the same quotient classes, then $u=\sum_i f_i e_i$ is such a unit and satisfies $u e_i=f_i u$. After alignment the induced maps on the corners satisfy exactly the original equation for a tensor transporter. Conversely every transporter defines the blockwise algebra isomorphism. Before using this encoding, any test with a zero-dimensional mode or unequal input formats can be decided directly and replaced with a fixed nonzero-format affirmative or negative test.

For an ordered pair of tensors, use two such triples of vertices with a nonzero one-dimensional bridge from the last vertex of the first triple to the first vertex of the second. All additional radical products are zero. This is associative because all triple radical products vanish. Its directed corner graph has a unique topological order and is connected. Thus it represents an ordered pair up to independent tensor equivalence. The algebra is centrally indecomposable. A central idempotent commutes with every vertex idempotent and hence is diagonal. Commuting with each nonzero corner forces all its diagonal coordinates to agree. The same construction with more bridges represents a tuple if desired.

For two ordinary TI tests $(x,y)$ and $(u,v)$, use the two products of centrally indecomposable ordered-pair algebras representing the multisets
$$
 \{(x,u),(y,v)\},\qquad \{(x,v),(y,u)\}.
$$
Algebra isomorphism preserves primitive central idempotents, so these products are isomorphic precisely when the multisets match componentwise, allowing the two components to be exchanged. The direct matching exists precisely when $u$ and $v$ are tensor-isomorphic. The exchanged matching exists precisely when $x$ and $y$ are tensor-isomorphic. Turn the product algebras into ordinary TI instances by taking their multiplication tensors. For a unital associative algebra, a multiplication isotopy $R(ab)=P(a)Q(b)$ is equivalent to an algebra isomorphism after normalizing by $P(1)$ and $Q(1)$. Surjectivity makes these two elements units, and $P(1)^{-1}R(a)Q(1)^{-1}$ is the normalized algebra isomorphism by substitution. This proves disjunction, even when the two tests have different formats. The construction has linear growth in the sum of the nonzero tensor side lengths at each gate. Fixed disjunctions, fixed conjunctions, and balanced positive formulas therefore stay polynomial. [Grochow and Qiao, tensor-to-algebra methods](https://arxiv.org/html/1907.00309).

Apply the hypothetical reduction to the reflected pair corresponding to each $d\in\Omega$, and combine those at most eight ordinary instances by disjunction. The converse implication is exact by selecting $\Omega=\{(1,1,1)\}$. Thus the same-field many-one collapse is equivalent to a one-instance reduction for arbitrary prescribed allowed sets of determinant patterns. This includes parity constraints given by any linear equations in the three sign bits. The same construction combines any fixed positive Boolean formula of independent signed comparisons. Shared unknown transporters across the tests require separate compatibility constraints.

## Exact counts and their decision reductions

Write $N_G(A,B)$ and $N_K(A,B)$ for the exact number of ordinary and determinant-one transporters, respectively. Reflection gives the unconditional formula
$$
 N_G(A,B)=\sum_{d\in D}N_K(A,r_d^{-1}B).
$$
If the identity determinant tuple belongs to ${\cal C}(A,B)$, then
$$
 N_K(A,B)=\frac{N_G(A,B)}{|{\cal C}(A,B)|}.
$$
Otherwise $N_K(A,B)=0$. Thus under $\mathcal H$, signed exact counting has a deterministic nonadaptive reduction using at most nine ordinary exact-count calls. Use one to obtain $N_G(A,B)$, and replace the eight signed decision calls for ${\cal C}(A,B)$ by the hypothetical reductions followed by testing ordinary counts for positivity. The unconditional reverse reduction uses eight nonadaptive signed count calls and addition. This proves a functional Turing equivalence, with constant query budgets, under $\mathcal H$. It also computes the complete eight-entry transporter count table from one ordinary count and eight ordinary decision calls.

Under $\mathcal H$ the following two statements are equivalent as polynomial-time Turing reductions in the dense model.

- Ordinary exact counting reduces to ordinary decision.
- Signed exact counting reduces to signed decision.

For either direction use the functional equivalence above and replace the decision oracle by that of the other language by the two many-one reductions. The conclusion is an equivalence of counting-to-decision claims. It does not assume either claim is currently known in the dense model. Grochow and Qiao's polynomial-time counting-to-decision theorem for class-two exponent-$p$ groups takes their full Cayley tables as input, a different size bound. [Grochow and Qiao, Part IV, Theorem 1.8 in the STOC version](https://opus.lib.uts.edu.au/bitstream/10453/189643/2/3717823.3718282.pdf).

Two variants follow from the same formulas.

- For an odd modulus $M$, a signed count modulo $M$ is obtained from one ordinary count modulo $M$ and the exact determinant feasibility pattern. The denominator is a power of two and invertible modulo $M$. For arbitrary positive $M$, it suffices to ask for the ordinary count modulo $8M$, divide its representative by the known divisor of eight when the signed fiber exists, and reduce modulo $M$. The reverse uses the eight signed counts modulo $M$. These claims use a separate ordinary decision oracle to compute the pattern under $\mathcal H$.
- Under $\mathcal H$ an estimate of the ordinary count with relative error $\epsilon$ yields a signed estimate with the same relative error on a nonempty sign fiber. Use the ordinary decision pattern to handle empty fibers. If only an ordinary approximation scheme is supplied, estimate with relative error less than one and use positivity, with amplified success probability, to implement the ordinary decision calls. In the other direction approximate each of the eight signed counts and sum. On the event that all approximations are correct, the total has the same relative error. Amplifying each call before taking the union bound proves that a fully polynomial randomized approximation scheme exists for one counting problem if and only if it exists for the other, under $\mathcal H$.
## Search, complete cosets, and sampling

Use the coset-search convention of returning one witness and generators of the source stabilizer, or an explicit empty result. With an ordinary coset output, list the image $H_A$ by breadth-first search on the eight-element sign group, retaining one stabilizer word per image element. The signed fiber is nonempty if and only if the inverse sign of the returned witness occurs. Multiply the witness by a stored inverse-sign word to obtain a signed witness. The standard coset rewriting gives generators for the kernel of $\chi$ on $\operatorname{Stab}_G(A)$ using at most $|H_A|$ times the number of ordinary generators. Explicitly, for every representative $t_d$ of sign $d$ and generator $s$, use $t_d s t_{d\chi(s)}^{-1}$, allowing inverses in the original list. Every kernel word rewrites to a product of these by inserting sign representatives at its prefixes. This gives $K$-coset search from a $G$-coset output in polynomial additional time, unconditionally.

Conversely ask signed coset search on the eight reflected comparisons. If any succeeds, undo the reflection to obtain an ordinary witness. The signed stabilizer generators returned by that call generate the kernel for the source. For each nonempty sign fiber, undo its reflection and multiply on the left by the inverse of the chosen ordinary witness to obtain a source stabilizer representative of the corresponding relative sign. These representatives, together with the kernel, generate the ordinary stabilizer. This proves unconditional equivalence of the two full-coset functions by constant-query Turing reductions.

Under $\mathcal H$, polynomial-time reduction of either full-coset function to its own decision oracle is therefore equivalent to the analogous claim for the other. A search algorithm that supplies only one ordinary witness can leave the whole sign image unknown. A many-one decision reduction $\mathcal H$ also need not return a rule lifting witnesses from its target instances. The full-coset inference uses the explicit generators.

If an exact uniform sampler for ordinary transporters is already supplied, under $\mathcal H$ one can test whether any prescribed sign fiber is empty and, when it is nonempty, sample it exactly by rejection. The acceptance probability is $1/|H_A|\ge1/8$, so the expected number of samples is at most eight. Without a uniform ordinary sampler this is a conditional transfer of sampling, even after the decision reduction is assumed.

## Canonical representatives

A canonical representative procedure returns some tensor in the input orbit with identical output on identical orbits. It need not return the lexicographically smallest tensor in the orbit.

Given such a procedure for ordinary TI, compute $C=\operatorname{Can}_G(T)$. Form the eight tensors $r_d C$ and select the lexicographically first one that is $K$-isomorphic to $T$. At least one succeeds, and the candidate list depends only on the ordinary orbit. Equivalent signed inputs select the same candidate, and the selected output is a representative of the signed orbit. Under $\mathcal H$, the eight tests reduce to ordinary TI and can therefore be implemented by the same ordinary representative procedure, evaluating its result on the two members of each comparison. Thus ordinary representative canonization gives signed representative canonization with a fixed number of calls of polynomially bounded size under $\mathcal H$.

Conversely, from signed representative canonization compute the eight signed representatives of $r_d T$ and take their lexicographic minimum. The signed orbits of the eight twists exhaust the signed orbits inside the ordinary orbit of $T$, by normality and surjectivity of $\chi$. Their resulting multiset is the same for any ordinary-isomorphic input. Thus this direction needs no hypothesis. Combining directions gives equality of the two deterministic representative-canonization degrees under polynomial-time Turing reductions under $\mathcal H$, and equivalence of polynomial-time representative canonization. Comparison of canonical codes that are allowed to lie outside the original orbit is a different functional task.

## A worst-case algorithm already available without the hypothesis

There is an unconditional bound
$$
 3^{\widetilde O(n^{3/2})}
$$
for determinant-one decision, full coset search, and exact counting for dense $F$-tensors of maximum side length $n$. This follows from the ordinary coset algorithm and the finite-index computation above, with an additional group-order routine for counting.

Ivanyos, Mendoza, Qiao, Sun and Zhang give the ordinary matrix-space left-right equivalence algorithm, and in Section IV-E show how it returns a coset representative and stabilizer generators within the same $q^{\widetilde O(n^{3/2})}$ bound. Section IV-D reduces tensor isomorphism to these matrix spaces by restricting to the concise supports and taking the largest mode as the slice index, padding the rectangular matrices to the same square width. On a concise tensor the slices form a basis of the matrix space. The third-mode map is recovered uniquely from a left-right equivalence by expressing the transformed basis of slices in the target basis. This is a polynomial-time lift of the whole matrix-space transporter coset. If square padding was used, the common image and row-support spaces are intrinsic, so the computed generators and witness restrict to them. Their restrictions give exactly the original matrix-space action because all original equivalences extend over padding. For the original nonconcise tensor, compare the three support dimensions and restrict to all three contraction supports. Once the support-level maps are found, the unused complement maps are arbitrary invertible maps with arbitrary shears into the support. Block-diagonal lifts of the support generators together with these elementary complement generators give the full original stabilizer. This handles the original raw determinants on deficient inputs rather than silently replacing them by support determinants. The fixed-characteristic tuple-isometry and generator routines at the bottom are deterministic at characteristic three. [Ivanyos, Mendoza, Qiao, Sun and Zhang, Sections IV-D and IV-E](https://chuanqizhang.com/assets/pdf/pdf/focs24.pdf), [Ivanyos and Qiao, Theorem 7](https://arxiv.org/html/1708.03495), [Brooksbank and Wilson, Theorem 1.2 and Remark 2.1](https://doi.org/10.1090/S0002-9947-2011-05388-2).

To compute an exact order from the resulting matrix-tuple generators, use their faithful permutation action on the disjoint union of the three whole vector spaces. Its degree is $\sum_i 3^{\dim V_i}\le 3^{O(n)}$. Convert each generator to a permutation by enumerating these vectors and use the deterministic polynomial-time permutation group order algorithm in that degree and generator-list length. The additional group-order computation stays within $3^{\widetilde O(n^{3/2})}$. Apply the exact cardinality and parity formulas to count either transporter fiber. This argument needs no general polynomial-time order algorithm for matrix groups in the dense representation. [Furst, Hopcroft and Luks, *Polynomial-time algorithms for permutation groups*](https://doi.org/10.1109/SFCS.1980.34).

The same bound yields $N^{\widetilde O(\sqrt{\log N})}$-time even-isomorphism, full-coset and exact-count algorithms for special exponent-three groups of order $N$ in the Cayley-table model, with compact bracket dimension $O(\log N)$. Use the coset-compatible linear-length reduction from alternating matrix space isometry to ordinary TI, recover the bracket coset, and filter by the determinant of the domain times the central determinant. The remaining central shear is an elementary abelian group, contributes its explicitly computable order to the number of isomorphisms, and has determinant $1$. The parity convention for an arbitrary written table order is calibrated by the permutations from those labels to coordinate order, obtainable by enumeration in polynomial time in $N$. [Grochow and Qiao, Part IV, Theorem 1.10 and Remark 1.12](https://arxiv.org/html/2306.16317v2).

## What the hypothetical reduction changes

The new implication of $\mathcal H$ is a polynomial-time decision equivalence, with the count, full-coset, and representative consequences above. A polynomial-time many-one reduction whose output side length is $r(n)$ transfers an ordinary side-length bound $T$ to at most polynomial overhead and $T(r(n))$. Linear or polylogarithmically near-linear output length preserves the $3^{\widetilde O(n^{3/2})}$ exponent in that formula. A bare input-polynomial bound on the reduction gives no such side-length guarantee.

Further one-way or equivalent consequences under $\mathcal H$ include the following.

1. The two languages have identical membership in any class closed under deterministic polynomial-time many-one preimages. In particular $\mathrm P$, $\mathrm{RP}$, $\mathrm{ZPP}$, $\mathrm{BPP}$, $\mathrm{BQP}$, $\mathrm{P/poly}$, and quasipolynomial time transfer in both directions. This states equivalence of membership claims, as distinct from asserting membership in all these classes.
2. If there is a polynomial-time many-one reduction from ordinary TI to GI, then so is determinant-one TI, and the converse follows by padding. Either conjecture, combined with $\mathcal H$, makes the three problems many-one equivalent and gives quasipolynomial-time tensor algorithms from Babai. Graph Isomorphism hardness of each tensor problem already follows from the ordinary graph-to-tensor reduction and padding. [Grochow and Qiao, Section 3.2](https://arxiv.org/html/1907.00309#S3.SS2), [Babai, *Graph Isomorphism in Quasipolynomial Time*](https://arxiv.org/abs/1512.03547).
3. Under $\mathcal H$, polynomial-time oracle computations can substitute either tensor decision oracle for the other, with only polynomial overhead. This gives equality of the deterministic and randomized polynomial-time oracle classes for the two oracles, and also of the quantum decision oracle classes using reversible computation of the classical maps.
4. A deterministic many-one reduction to any external target, including a meta-complexity language such as MCSP or MKTP, transfers in both directions under $\mathcal H$. The known statistical-zero-knowledge and orbit-sampling theorems supply randomized oracle upper bounds via MCSP or MKTP, with their own hypotheses and error models. [Allender and Das, Zero Knowledge and Circuit Minimization](https://www.cs.rutgers.edu/~allender/papers/szk.mcsp.pdf), [Allender, Grochow, van Melkebeek, Moore and Morgan, Theorem 5.7](https://pages.cs.wisc.edu/~dieter/Papers/gi-mktp-sicomp.pdf).
5. For any efficiently samplable distribution of signed input pairs, a reduction under $\mathcal H$ transfers accuracy on that distribution to accuracy of an ordinary solver on its pushed-forward distribution, with equality of error probabilities. Uniform-tensor and other specified average-case ensembles can change under this map. Results for a particular ordinary ensemble transfer to a specified signed ensemble only if the output distribution meets the ordinary solver's assumption. [*On the average-case complexity landscape for Tensor-Isomorphism-complete problems over finite fields*](https://arxiv.org/abs/2604.00591).

These proofs concern raw fixed-field decision instances and explicitly specified functional reductions. They give conditional consequences of the proposed equivalence and unconditional finite-index postprocessing results. The proofs are informal. Finite checks covered all 15 equivalence partitions of the four objects in the disjunction construction, 2,432 determinant count tables and 48,640 modular count cases. The comparison in Open Question 1.9 is still a hypothesis in this chapter.
