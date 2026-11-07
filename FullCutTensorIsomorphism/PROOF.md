# Full-cut-rank Four-Tensor Isomorphism Contains Arbitrary Four-Tensor Isomorphism

This is an informal proof with a small exact marker certificate. Let $F$ have characteristic 5. For a four-tensor of side $n$, define ordinary isomorphism using four independent invertible changes of basis, with modes ordered. A pair flattening groups two modes on each side.

**Theorem.** There is a deterministic affine-linear objectwise map $\Phi$ over $F$, with output side $11(10n+1)$, such that
$$
 X\cong Y \quad\Longleftrightarrow\quad \Phi(X)\cong\Phi(Y).
$$
Every output has three invertible pair flattenings and scalar centroid. Its stabilizer contains a fixed diagonal copy of $\mathrm{GL}_n(F)$ acting faithfully in each mode. In particular, for $n\geq2$ no cyclic mode endomorphism can be assigned equivariantly on a class containing any of the outputs. For fixed finite $F$, every nonempty equivariantly assigned list of split line frames in an output mode has at least $|F|^{n^2-O(n\log n)}$ members, even if the lines are defined over an extension. For decompositions into $o(n)$-dimensional summands the bound is $|F|^{n^2-o(n^2)}$.

Thus, over $\mathbb F_5$ in particular, a polynomial-time reduction of the counting-exponent dimension $O(m^{4/3})$ on this full-cut-rank promise would give an $O(n^{4/3})$ reduction for unrestricted four-tensors. Conversely an unrestricted reduction applies to the promise. The construction also shows that the simultaneous failure of the rank, centroid, cyclic, and short intrinsic frame routes can contain a linearly padded copy of every four-tensor isomorphism instance. This is an equivalence of reduction tasks at order four, and supplies no algorithm for the remaining compression.

## 1. An open contraction and a fixed marker

On a tensor with an invertible $12\mid34$ flattening, let $S(T)$ be its inverse matrix relabelled as a tensor with four dual slots. It transforms under the contragredient actions. Take four copies of $T$ and four copies of $S(T)$ indexed by $x\in\mathbb Z/4$ on each side. In color $j$, join positive $x$ to negative $x+s_j$, using $(s_1,s_2,s_3,s_4)=(0,1,3,2)$, by contracting the indicated mode. For $A_i(T)$ remove just the edge of color $i$ at positive $0$. The two open slots make an endomorphism in mode $i$. Every internal pairing is invariant, so $A_i$ is conjugation-covariant. This is the open inverse-flattening contraction from our weighted orthogonal-array work.

Take the marker $M$ of side 11. Its nonzero coefficients occur at
$$
 (a,b,a+b,a+2b),\qquad a,b\in\mathbb Z/11,
$$
with nonzero weights $w_{ab}\in\mathbb F_5$. Every pair of the four linear forms determines $(a,b)$, so all pair flattenings are weighted permutation matrices. The inverse tensor has the same support and reciprocal weights.

For this support the other three full color matchings restore the removed equality. Summing each full color's equations shows that its linear form agrees on the two sums of the row vectors. Any two of the three linear forms determine a row, so the row sums agree. The three present edges of the remaining color then force its missing equality. Hence all four $A_i(M)$ are diagonal. The nonzero contributions to their diagonal entries can be indexed by full matchings. To enumerate those, first use color 1 to write a common first coordinate $X_x$ for positive and negative vertices at position $x$. Color 2 makes the positive second coordinate $B_{x+1}$ and the negative second coordinate $B_x$. The other two conditions are
$$
 X_x+B_{x+1}=X_{x+3}+B_{x+3},
 \qquad
 X_x+2B_{x+1}=X_{x+2}+2B_{x+2}.
$$
Adding the second equation at $x$ and $x+2$ gives $B_x+B_{x+2}=B_{x+1}+B_{x+3}$. Thus $B_x=b+t_x$ with $t=(u,v,-u,-v)$. The second equation then gives $X_x=a_{x\bmod2}-t_x-t_{x+1}$ and the first equates the two parity constants. Conversely these formulas solve all the equations. There are exactly $11^4$ assignments indexed by $(a,b,u,v)$.

Use the following fixed weights. Start a 32-bit integer state at 20261107 and iterate $s\gets(1664525s+1013904223)\bmod 2^{32}$. Discard the first 121 iterates. In lexicographic order of $(a,b)$, use the next 121 iterates to set $w_{ab}=2^{(\lfloor s/2^{16}\rfloor\bmod4)}$ in $\mathbb F_5$. The [exact certificate](verify_marker.py) enumerates the $11^4$ full matchings with their weight products and verifies that at
$$
 \tau=(0,8,4,0)
$$
the selected eigenvalues of $A_i(M)$, in mode order, are $(0,0,0,1)$, each of multiplicity one in its own mode. The table in the certificate records every diagonal entry. The selected tuple is outside the support of $M$.

The marker admits a two-dimensional finite grading. Over an extension containing a primitive eleventh root of unity, assign grade $a(-1,-1)$ to mode 1's label $a$, $b(-1,-2)$ to mode 2's label $b$, $c(1,0)$ to mode 3's label $c$, and $d(0,1)$ to mode 4's label $d$. Grades lie in $(\mathbb Z/11)^2$ and determine characters of an order-$121$ diagonal torus. Every marker support coefficient has total grade zero. The selected tuple has grade
$$
 \delta=(4-8,0-16)=(7,6)\pmod {11}.
$$
It is on none of the four lines generated by the mode grade directions. The same is true of $k\delta$ for $1\leq k\leq8$. The extension is used only to prove identities by the grading. The reduction and its data are over $F$.

## 2. A full-rank carrier with free data actions

Take one vector space $W$ containing four mutually orthogonal hyperbolic pairs $U_i\oplus U_i^*$, each $U_i$ of dimension $n$. Add another hyperbolic pair $H\oplus H^*$ with $\dim H=n$, and one extra line of norm 1. The symmetric inverse-pairing tensor $B$ on $W$ has matrix equal to its inverse, with hyperbolic swap matrices and the last $1$. The dimension $D=10n+1$ equals 1 as an element of $F$. Define
$$
 C=B_{13}B_{24}+2B_{14}B_{23}\ \in W^{\otimes4},
$$
where products mean the indicated pairings occupying distinct slots. A simultaneous isometry of $B$ on all four copies of $W$ stabilizes $C$.

For any pair flattening, identify the input dual spaces with $W$ using $B$. The flattened operator is $\beta I+\gamma P+\alpha Q$, where $P$ swaps the factors, $Q$ contracts the pair and reinserts $B$, and $(\alpha,\beta,\gamma)$ is a permutation of $(0,1,2)$. We have $P^2=I$, $PQ=QP=Q$, and $Q^2=DQ$. Its inverse is
$$
 \frac{\beta I-\gamma P}{\beta^2-\gamma^2}
 -\frac{\alpha Q}{(\beta+\gamma)(\beta+\gamma+\alpha D)}.
$$
The denominators are nonzero in characteristic 5 since $D=1$ in the field and $0,1,2$ are distinct up to sign. Thus every flattening is invertible. Relabelling the inverse in the $12\mid34$ cut, $S(C)$ is a linear combination of the three dual pairing patterns, with coefficients depending only on $D$ as a field element.

We will also use $A_i(C)=I_W$. To see this, expand the contractions of four copies of $C$ and four copies of its inverse into pairing patterns. Each term consists of closed strands and one open strand joining a primal to a dual endpoint. The tensors are pairings and inverse pairings, so every closed strand gives $D$ and the open strand gives the identity. The resulting scalar depends only on $D$ as a field element, including in the inverse coefficients just displayed. At dimension 1, $C$ is the scalar 3, the inverse is $1/3$, and the product of four of each is 1. Our $D$ has the same value in the coefficient field, proving the claim.

## 3. Insert arbitrary data without changing the visible markers

Use $F^{11}\otimes W$ as each output mode. Let $T_0=M\otimes C$, with the four corresponding mode factors grouped. Identify the $i$-th source factor with $U_i$ inside $W$. Write $E(X)$ for the tensor supported just in the marker block $\tau$ with $W$-coefficient the image of $X$ in $U_1\otimes U_2\otimes U_3\otimes U_4$. Set $\Phi(X)=T_0+E(X)$.

Fix any pair cut, with baseline matrix $F_0$. It is a permutation matrix on the marker blocks, with each nonzero block an invertible multiple of the corresponding carrier flattening. Since $\tau$ is outside the marker support, the flattened perturbation lies in a single block off that permutation. The product $F_0^{-1}E(X)$ in that cut is supported in one off-diagonal block. Its square is zero, for any coefficient matrix in the block. Consequently the flattened matrix remains invertible for every $X$, and its inverse as a function of $T_0+tE(X)$ is affine in $t$.

The baseline contraction factors along the marker and carrier, giving $A_i(T_0)=A_i(M)\otimes I_W$. We claim that $A_i$ is exactly unchanged after insertion of any $X$. The defining expression on $T_0+tE(X)$ has degree at most 8 in $t$, since it uses four copies of the tensor and four of the affine inverse. Under the marker torus the baseline is fixed and $tE(X)$ scales by the character of grade $\delta$. By covariance, the coefficient of $t^k$ in $A_i$ has grade $k\delta$ in the conjugation action on endomorphisms of the output mode. This follows by comparing formal polynomial coefficients in $t$ after scalar extension. Every weight of that endomorphism action is a difference of two grades in a single mode, and hence lies on the line of that mode. For $1\leq k\leq8$ the requisite grade does not occur, so the coefficient is zero. Therefore
$$
 A_i(\Phi(X))=A_i(M)\otimes I_W
$$
for every input. In particular the eigenspace for the selected unique marker eigenvalue in mode $i$ is exactly the copy of $W$ at label $\tau_i$. This recovers the data block from the raw output using only the four covariants.

## 4. Exact preservation and reflection of isomorphism

Given a source isomorphism with maps $g_i$ on $U_i$, form the isometry of $W$ acting by $g_i$ and $g_i^{-\mathsf T}$ on the corresponding hyperbolic pair, and by the identity on the remaining summands. Acting by it in every output mode, with identity on all marker indices, preserves $T_0$ and carries $E(X)$ to $E(Y)$. Thus $\Phi$ preserves isomorphism.

Conversely suppose $\Phi(X)$ and $\Phi(Y)$ are isomorphic. Covariance of the four $A_i$ forces the four changes of basis to preserve each selected eigenspace. It also forces them to preserve its complement, the sum of the other eigenspaces, since the contractions are split diagonal and the selected eigenvalue occurs in no other block. Projecting the isomorphism to the tensor product of the selected eigenspaces now gives an isomorphism between the $W$-embedded copies of $X$ and $Y$. There is no baseline in that block. The isomorphism restricts to the intrinsic singleton supports. Their restrictions extend to the original equal-dimensional $U_i$, proving $X\cong Y$.

The map is affine-linear and the output dense array has only a constant-factor increase in side and therefore polynomial bit cost over a fixed finite field. It is defined without solving any source isomorphism problem. In particular ordinary 3TI also reduces to the promise by first appending a fixed nonzero vector in a fourth mode. The existing balanced reduction supplies a polynomial-time reduction in the other direction.

## 5. Simultaneous limits of the earlier routes

The centroid is scalar. Indeed, in an invertible cut, equality of the actions of the two same-side modes implies $A\otimes I=I\otimes A'$ on the full pair space, so both endomorphisms are the same scalar. All modes are concise, so the remaining actions are that scalar as well.

On the spectator pair $H\oplus H^*$ every map $h\oplus h^{-\mathsf T}$ for $h\in\mathrm{GL}_n(F)$ extends to a simultaneous isometry of $C$, and it is the identity on the data. It acts with the identity marker map and hence stabilizes every $\Phi(X)$. Its image in each mode is faithful and noncommutative for $n\geq2$. If a conjugation-covariant endomorphism were cyclic at such an input, its centralizer would be the commutative algebra of its polynomials. That follows by taking the image of a cyclic vector, which determines a commuting endomorphism. The stabilizer subgroup acts inside that centralizer, a contradiction.

For the frame bound, let $m=11(10n+1)$ and suppose the coefficient field has fixed size $q$. For any unordered decomposition into nonzero subspaces of dimension at most $w$, a stabilizer of the decomposition in the spectator group acts on the summands by at most $m!$ permutations. The kernel preserves each summand. The space of matrices preserving all summands has dimension at most $\sum_j w_j^2\leq mw$. This remains an upper bound on the dimension of base-field matrices satisfying these constraints if the decomposition is defined over an extension, since independent base-field matrices remain independent over the extension. Thus the orbit of the decomposition has size at least
$$
 \frac{|\mathrm{GL}_n(\mathbb F_q)|}{m!\,q^{mw}}.
$$
For lines this is $q^{n^2-O(n\log n)}$, and for $w=o(n)$ it is $q^{n^2-o(n^2)}$. Any nonempty equivariantly assigned list must contain the entire orbit of a member. In particular the frame route cannot cover this promise with polynomially many fine frames.

The same construction works in characteristic zero using the integers $1,2,3,4$ as the representatives of the marker weights. All selected marker eigenvalue differences are nonzero by reduction modulo 5. The rational carrier contraction scalar for $D=10n+1$ is congruent to 1 modulo 5, so is nonzero, and it is constant across that mode's marker labels. The multiplicity-one argument is therefore unchanged. The finite-field frame count above is stated only in finite characteristic.

## References and scope

- The open contraction and affine-array parameterization reuse our earlier weighted-array construction. Related closed contraction invariants appear in [Rather et al.](https://arxiv.org/abs/2212.06737) and [Ramadas and Lakshminarayan](https://arxiv.org/abs/2411.04096). The present theorem uses a fixed open contraction, an inverse flattening, and a grading to retain the marker under arbitrary perturbations.
- The dimension-preserving question is [Grochow–Qiao Question 7.8](https://epubs.siam.org/eprint/VA7M2DT6DFQMVDVWIBBN/full). The ordinary upper reduction is the MathProofs [balanced reduction](../BalancedOrdinaryReduction.lean). For the related generic-input context, see [Li, Li, Qiao, Tao, and Wang, Section 4](https://arxiv.org/html/2604.00591v1).
- The marker table is an exact finite calculation. The reduction, reflection proof, and asymptotic consequences are informal. No publication-priority claim is made.
