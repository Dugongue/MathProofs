# Eliminating inversion steps with low symbolic defect rank

**Theorem.** Work over any field $F$. Let a Polynomial Calculus with Inversion step use $r$-by-$r$ polynomial matrices $A,B$ to derive a selected entry of $BA-I$ from the entries of $AB-I$. Put $d=\deg(A)+\deg(B)$, taking each matrix degree to be the maximum of zero and its entry degrees. If $k=\operatorname{rank}_{F(x)}(AB-I)$, the step has an ordinary Polynomial Calculus derivation of degree at most $(k+1)d$ from its premises. The bound depends on the symbolic rank of the defect and does not depend on the matrix side $r$. In a full proof, if every step has $k\le k_0$ and $d\le d_0$, the ordinary Polynomial Calculus simulation has degree at most the maximum of the original proof-line degree and $(k_0+1)d_0$. For fixed $k_0,d_0$, the simulation has polynomial overhead in sparse proof size when the matrix annotations and premise references are charged to the original size. [Original inversion rule and published degree measure](https://arxiv.org/html/2305.19320#S2.SS3)

## Polynomial identity and degree

Set $E=AB-I$, $J=BA-I$, $C=I+E$. The algebraic identity
$$
 B\operatorname{adj}(C)A=\det(C)I
$$
holds universally. It holds for independent generic $A,B$ over their rational function field by multiplying by the inverse of $C$. The generic identity is between integer polynomials and thus specializes to any field. Since $E$ commutes with $\operatorname{adj}(C)$, the adjugate identity gives
$$
 B E\operatorname{adj}(C) A=\det(C)J.
$$
Expand
$$
 \det(I+tE)=\sum_{j\geq0}c_jt^j,\qquad
 \operatorname{adj}(I+tE)=\sum_{j\geq0}M_jt^j.
$$
Here $c_j$ is the sum of the principal $j$-minors of $E$. Every entry of $M_j$ is a signed sum of $j$-minors of $E$, obtained by expanding its defining cofactor, choosing the identity entries first. Both kinds of coefficients vanish for $j>k$. Comparing coefficients of $t^{k+1}$ in $(I+tE)\operatorname{adj}(I+tE)=\det(I+tE)I$ gives $EM_k=0$. Thus for $k\ge1$,
$$
 J=B E\left(\sum_{j=0}^{k-1}M_j\right)A-J\left(\sum_{j=1}^kc_j\right).
$$
For $k=0$ the defect is zero, and $J=0$ by the basic adjugate identity.

The right side of the displayed formula expresses each selected conclusion as a linear combination of premise entries $E_{uv}$ with polynomial multipliers. In the first summand the displayed $E$ contributes the premise. In the second, expand every principal minor by its determinant sum and choose one entry of $E$ as the premise in each term. Every product on the right has at most $k$ factors from $E$, plus one entry from each of $A,B$ or one entry from $J$. Since $E,J$ have degree at most $d$, all these products have degree at most $(k+1)d$.

Use ordinary variable multiplication to multiply each premise by the monomials of its multiplier, and combine the results linearly. Intermediate terms have the same degree bound. If $k_0,d_0$ are fixed, at most polynomially many minors and permutation terms occur. The number of distinct monomials of bounded degree in the original variables is polynomial as well. The multipliers can therefore be expanded at polynomial sparse cost. Repeat this argument at each inversion line, retaining the preceding proof lines. If annotations are supplied by circuits, the argument gives an algebraic proof-size bound and does not rely on a deterministic general identity-testing procedure.

## Application to tensor isomorphism

Apply the simulation to the explicit sparse lower-bound examples in *MathProofs*, or to the full-support semisimple multiplication tensors in the accompanying [concise separation](concise-separation.md) in positive characteristic. For each fixed characteristic and for constants $k_0,d_0$, the corresponding family has exponential sparse-size lower bounds for Polynomial Calculus with Inversion when every substitution satisfies the two caps. This permits arbitrary matrix sides and does not impose a degree restriction on the other proof lines. Indeed the simulation has polynomial sparse overhead even if those other lines have large degree. If all the displayed lines also have sublinear degree, the ordinary degree lower bound forces some permitted step to have $(k+1)d=\Omega(n)$ on these inputs. [Sparse proof lower bounds in positive characteristic](https://github.com/Dugongue/MathProofs/blob/main/TensorSparsePCBounds/Proof.md) · [Characteristic zero](https://github.com/Dugongue/MathProofs/blob/main/TensorSparsePCBounds/CharacteristicZero.md)

The proof-line-only collapse is consistent with this restriction. Its block matrices have rank-one defect, but they carry Nullstellensatz coefficients in the annotations and those coefficients can have large degree. [Original block construction](https://github.com/Dugongue/MathProofs/blob/main/IsomorphismProofCrossovers/circuits.md)

## Ordered branching program annotations

There is also a direct size statement without bounding the annotation degree. Consider a one-inversion refutation whose premises each refer directly to an input axiom or to zero, and whose selected conclusion is a nonzero scalar. Suppose all annotations are given by read-once oblivious algebraic branching programs in one common variable order, and fix $k_0\ge1$. If the defect rank is at most $k_0$, the identity above translates the proof into a Hilbert-like IPS certificate with coefficients represented by branching programs in that order, at polynomial size overhead. The operations in each summand of a multiplier consist of at most $2k_0+2$ factors of annotation entries or scalar polynomials, and a polynomial number of summands for fixed $k_0$. Take tensor products of programs for products and direct sums for sums. Group the multipliers by the input axiom they reference and finally normalize the output scalar.

Conversely, if each input axiom $f_i$ and each coefficient $g_i$ in a Hilbert-like certificate $\sum_i f_i g_i=1$ is presented by a branching program in that order, the block matrices
$$
 A=\begin{pmatrix}1&0\\-g&I\end{pmatrix}, \qquad
 B=\begin{pmatrix}1&f\\g&I+gf\end{pmatrix}
$$
give such a proof with rank-one defect and polynomial overhead. Sparse input axioms convert to branching programs in any variable order with polynomial overhead in their sparse encoding. This gives a two-way polynomial comparison for the direct one-inversion fragment and the stated fixed-order coefficient model. It is independent of the earlier comparison using unrestricted circuit annotations. [Circuit-annotation comparison](https://github.com/Dugongue/MathProofs/blob/main/IsomorphismProofCrossovers/circuit-ips.md)

For fixed $k_0$ this ordered fragment has a deterministic verifier using only polynomially many field operations. Compare each computed premise and conclusion with its claimed polynomial, and test all $(k_0+1)$-minors of the defect for zero. If $k_0\ge r$ this last test is vacuous. Every comparison uses a polynomial-size branching program in the supplied common order. To test identity, start with the row vector at the input and propagate the span of its coefficient vectors through each univariate matrix layer using linear algebra. The scalar outputs of the final span vanish exactly when every coefficient is zero. Each basis remains of size at most the program width. This also gives deterministic polynomial binary time over any fixed finite field with the usual coefficient encoding. [Ordered branching program identity testing](https://arxiv.org/abs/1002.1496)

## Attribution

The upper bound uses classical adjugate identities and cofactor expansion. Galesi, Grochow, Pitassi and She gave a degree bound depending on the matrix side for unrestricted inversion instances. The proposed extension here is the dependence on the actual symbolic rank of $AB-I$, together with the resulting constant-rank simulation and applications. The argument was independently checked informally. Publication priority remains unestablished. [Galesi–Grochow–Pitassi–She, §3.2](https://arxiv.org/html/2305.19320#S3.SS2)
