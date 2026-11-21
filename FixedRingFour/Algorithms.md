# Tensor isomorphism at arbitrary prime-power precision

Let $R=\mathbb Z/p^e\mathbb Z$, with the modulus and coefficients represented in binary. Let $T,S\in M_1\otimes_R M_2\otimes_R M_3$ be explicitly presented tensors. The $M_i$ may be nonfree. Write $n_i$ for their numbers of nonzero cyclic factors and put $b=\sum_i n_i^2$. If source and target modules have different cyclic types, reject. Otherwise transport them into common cyclic frames.

**Theorem.** Set $k=1$ at odd primes and $k=2$ at $p=2$. For each $i$ put $E_i=\operatorname{End}_R(M_i)$. Given a class of units in $\prod_i(E_i/p^k E_i)^\times$, it is possible in deterministic polynomial bit time to decide whether it lifts to a tensor transporter, produce a lift, and count its lifts. The full decision, search, and counting problems take
$$
 p^{k b}\operatorname{poly}(\text{explicit input length},e,\log p)
 \tag{1}
$$
time. All dependence on the precision exponent $e$ is polynomial. The algorithm also provides a deterministic polynomial-time canonical form for each orbit of $\prod_i(1+p^k E_i)$. For free modes the same bound applies to literal determinant-one tensor isomorphism.

The shallow quotient in the theorem means reduction in the *endomorphism ring*. In nonfree modes it can contain more information than the induced action on $M_i/p^kM_i$.

## 1. Exponential coordinates on the correct congruence subgroup

Write $M=\bigoplus_j\mathbb Z/p^{a_j}\mathbb Z$ and choose $V=\mathbb Z_p^n$, $L=\bigoplus_j p^{a_j}\mathbb Z_p e_j$, so $M=V/L$. Set
$$
 O=\{X\in\operatorname{End}_{\mathbb Z_p}(V):XL\subseteq L\},
 \qquad J=\{X\in O:XV\subseteq L\}.
$$
Then $E=\operatorname{End}_R(M)=O/J$. In coordinates, $X_{ij}$ is divisible by $p^{\max(a_i-a_j,0)}$, and its image in $E$ is taken modulo $p^{a_i}$. These are exactly the conditions for homomorphisms between the cyclic factors. In particular the additive coordinate length in $E$ is $\min(a_i,a_j)$.

The ideal $p^kE$ is nilpotent. Every unit of $E/p^kE$ lifts to a unit of $E$: a chosen lift of an inverse gives products congruent to $1$ modulo this ideal, and those products are invertible by finite geometric sums. Equivalently an endomorphism of $M$ is invertible precisely when its action on $M/pM$ is invertible, by Nakayama and finiteness. Enumerate the shallow classes by taking each scaled coordinate modulo $p^{\min(k,a_i,a_j)}$, taking its least nonnegative representative, and testing the resulting endomorphism for invertibility. Different choices represent different classes. The group $1+p^k E$ is the kernel of this quotient map. For example, on $M=\mathbb Z/p\oplus\mathbb Z/p^2$, the map sending the short generator to $p$ times the long one vanishes on $M/pM$ but is nonzero modulo $pE$.

The series $\exp,\log$ are inverse bijections between $p^k O$ and $1+p^k O$. This follows from the convergent single-variable series identities. They also give inverse bijections
$$
 p^kE\ \longleftrightarrow\ 1+p^kE.
 \tag{2}
$$
For descent, changing an argument by $X-Y\in J$ changes its $m$-th power by a sum of terms in $p^{k(m-1)}J$, using a telescoping expansion and the fact that $J$ is a two-sided ideal. Division by $m!$ or by $m$ stays in $J$. Indeed $v_p(m!)\le(m-1)/(p-1)$, and $k(m-1)$ exceeds this bound for large $m$. Taking the series limits proves compatibility with both quotients. The construction excludes depth one at $p=2$, where $1+2O$ can already contain the element $-1$ with logarithm zero. [Lazard, *Groupes analytiques $p$-adiques*, Section III.3.2](https://pmihes.centre-mersenne.org/articles/10.1007/BF02684303/)

Everything in (2) can be computed with integers of polynomial bit length. For $\exp(X)$ lift the scaled coordinates of $X$ to integer matrices in $p^k O$. This is possible by the explicit cyclic-coordinate parametrization of $p^kE$. To compute $X^m/m!$ modulo $p^e$ work modulo $p^{e+v_p(m!)}$, remove the known power of $p$, and invert the remaining unit. The valuation of the term in $O$ is at least $km-v_p(m!)\ge m/2$, so $O(e)$ terms suffice. These modular precisions have $O(e\log p)$ bits. The logarithm is computed the same way with denominator $m$. Reduction of the resulting matrices to the cyclic-coordinate endomorphism ring is lawful by (2).

## 2. One congruence condition for an entire lift step

Put $\mathcal C=M_1\otimes_R M_2\otimes_R M_3$. In the cyclic frames its coordinates have lengths $\min(a_{1i},a_{2j},a_{3k})$. For $X=(X_1,X_2,X_3)$ define
$$
 \mathcal D_T(X)=X_1 T+X_2 T+X_3 T,
$$
where each $X_i$ acts only in its own leg. This is an additive map on $\bigoplus_iE_i$. On the tensor product of the three free $\mathbb Z_p$-lifts in Section 1, the induced operators on the three different legs commute. If $X_i\in p^k E_i$ and $h=(\exp X_i)_i$, put $A=X_1+X_2+X_3$ in this lifted tensor representation. The product of the three exponentials equals $\exp A$. Consequently on $\mathcal C$ one has
$$
 hT-T=B(A)\mathcal D_T(X),\qquad
 B(A)=I+\sum_{m\ge1}\frac{A^m}{(m+1)!}.
 \tag{3}
$$
To use this equality, it is enough to take any lifted $X$. All the displayed operators before reduction preserve the tensor relation lattice. More precisely $A$ is $p^k$ times an integral endomorphism preserving that lattice, since each summand acts in a single leg. For $m\ge1$ each higher term of $B(A)$ is divisible by $p$ in that ring: $km-v_p((m+1)!)\ge1$ by $v_p((m+1)!)\le m/(p-1)$. So $B(A)$ induces an invertible endomorphism on $\mathcal C$ and acts as $1$ on $p^j\mathcal C/p^{j+1}\mathcal C$ for every $j$. Its inverse preserves all the $p^j\mathcal C$ as well.

There are two consequences. First $hT=T$ exactly when $\mathcal D_T(X)=0$. The same statement is true modulo $p^j\mathcal C$ at all $j$. Second, for any $d\in p^j\mathcal C$,
$$
  hT-T\equiv d\bmod p^{j+1}\mathcal C
  \quad\Longleftrightarrow\quad
  \mathcal D_T(X)\equiv d\bmod p^{j+1}\mathcal C.
 \tag{4}
$$
For either direction, the displacement on the corresponding side is first seen to lie in $p^j\mathcal C$, using invertibility of $B$, and then $B$ is the identity on the next quotient. This is the step that allows the correction $X$ to range over the *whole* shallow congruence kernel. Restricting to new matrix digits one level at a time would overlook lower digits that stabilize the current tensor and can help at the next level.

## 3. Decision, witnesses, counts and canonical forms

Lift the supplied shallow unit class to $g_0$, and set $Y=g_0 T$. All possible images in this class form the orbit of $Y$ under $U=\prod_i(1+p^k E_i)$. Check $Y=S\bmod p^{\min(k,e)}\mathcal C$. If it holds, maintain this equality modulo $p^j$ and solve
$$
 \mathcal D_Y(X)=S-Y\bmod p^{j+1}\mathcal C,\qquad X_i\in p^k E_i .
 \tag{5}
$$
This is a system of linear congruences. A coordinate of tensor length $a$ is tested modulo $p^{\min(a,j+1)}$. To put every equation over $\mathbb Z/p^{j+1}\mathbb Z$, multiply its row by $p^{j+1-\min(a,j+1)}$. Parametrize each unknown by its scaled endomorphism entry with the extra $p^k$ factor, and solve by Smith elimination. Allowing unrestricted representatives for the unknown parameters is valid because their redundant higher digits act trivially on the cyclic group in question.

If (5) fails, there is no match at that precision within the class, by (4). If it succeeds, replace $Y$ by $(\exp X)Y$ and update the accumulated transporter. Any successful choice is safe: it stays in the same $U$-orbit, so every eventual solution remains related by some element of $U$. Iterate for at most $e$ steps. All row operations, exponential evaluations, and tensor multiplications take polynomial bit time on the explicit arrays. The same argument handles $e\le k$ with a trivial kernel. The relevant numerical precision is $e$; the standard modulus representation has $\Theta(e\log p)$ bits.

For counting, a successful class contains exactly
$$
 \left|\ker\!\left(\mathcal D_T\colon\bigoplus_i p^k E_i\longrightarrow\mathcal C\right)\right|
 \tag{6}
$$
transporters. In fact the set of all lifts in the class is a coset of the stabilizer in $U$, whose size follows from (2) and (3). Compute (6) by Smith elimination for finite abelian $p$-groups, or divide the known domain order by the image order computed from the generated tensor-coordinate submodule. In the free case, if the Smith valuations of $\mathcal D_T$ on the entire matrix variable space are $s_i$, setting $s_i=e$ for zero columns, the count is $p^{\sum_i\min(s_i,\max(e-k,0))}$. Enumerating all shallow classes and multiplying their number of successes by (6) proves (1). Nothing requires enumeration of group elements within a shallow class.

For local canonical forms, keep the initial digits modulo $p^{\min(k,e)}$. At stage $j$, the attainable next digits on the current orbit element $Y$, with all previous digits fixed, are precisely a translate of
$$
 \left(\operatorname{im}(\mathcal D_Y|_{\oplus_i p^k E_i})
                \cap p^j\mathcal C\right)\bmod p^{j+1}\mathcal C .
$$
This is a subspace of the next $\mathbb F_p$-layer. Compute it by linear congruences and normalize the translate by row-echelon reduction in fixed cyclic coordinates. Realize the chosen next digits using (5). Inductively the set of attainable next digits depends only on the orbit with its previously chosen digits, so the final representative is canonical for the $U$-orbit. This also gives a transporter to the representative.

For free modules and determinant-one transport, enumerate determinant-one shallow classes. Choose determinant-one lifts by scaling one row in each factor by the inverse of its determinant, a scalar congruent to $1$ at shallow precision. The identity $\det\exp X_i=\exp(\operatorname{tr}X_i)$ follows by triangularizing over an algebraic closure or from the formal exponential identity. Thus the exact additional constraint for (5) is $\operatorname{tr} X_i=0\bmod p^e$ in every leg, by (2) on scalars. These constraints are linear and are imposed on every correction, even when solving a lower layer. For the count in (6) append the same traces to the map. This gives (1) for determinant-one isomorphism without making any claim of a reduction to ordinary TI in unbounded dimensions.

## 4. Transfer of fast field search on a promise class

Take free modes of positive ranks and odd $p$. Let $l=\sum_i n_i$, and let $h$ be the number of field transporters between the reductions of the tensors, modulo the central scalar subgroup
$$
 Z=\{(aI,bI,(ab)^{-1}I):a,b\in\mathbb F_p^\times\}.
$$
Each element of $Z$ lifts to an exact stabilizer at every precision. Lift the first two scalars and use the inverse product in the third leg. Thus each class modulo $Z$ needs one application of (5). With a representative and generators of the residue stabilizer, enumerate the quotient stabilizer by breadth-first search. Normalize a class key by scaling the first nonzero entries of the first two matrices to $1$ and compensating on the third factor. A deterministic search tree deduplicates the keys with polynomial bit work per insertion, since $\log h\le b\log p$ when $h\ge 1$. The overall transporter count equals $h_{\rm good}(p-1)^2$ times (6), with $h_{\rm good}$ successful classes.

Here is a linear-length reduction from ordered projective-line pins to field decision. Work in bases putting the independent pinned lines in the first $r$ axes in the relevant mode of each tensor. For $r\ge18$, take a rigid simple graph $G$ with $r$ edges and minimum degree at least two. Construct it by subdividing one fixed edge of the rigid cubic Frucht graph $r-18$ times. The degree-three vertices and paths between them recover the Frucht graph, so every automorphism fixes the original vertices and then each subdivided vertex. Put the tensor
$$
 \sum_{x\in f}u_f\otimes v_x\otimes w_{f,x}
$$
in the entire original mode (with $u_f$ assigned to the $r$ pinned axes) and in two private auxiliary modes indexed by vertices and incidences. The notation sums over all incidences. The other axes of the original mode are unused by the pin tensor, and the same full-mode map acts on the input tensor and the pin tensor. In particular a valid map may have arbitrary complementary images consistent with invertibility.

To check the pin, its two-mode slice space is $\operatorname{span}\{u_f\otimes v_x:x\in f\}$. A preserving pair of maps must preserve the span of the $u_f$ by contraction. On this span and on the vertex space, select nonzero determinant terms with support permutations $\pi,\sigma$. Then every incidence $(f,x)$ maps to an incidence $(\pi(f),\sigma(x))$, by applying the maps to the corresponding pure tensor in the slice space. The permutations preserve the finite incidence set and thereby induce a graph automorphism. Rigidity gives $\pi=\sigma=1$, so both matrices have nonzero diagonal entries. An off-diagonal entry in the edge matrix would force one edge's two endpoints to lie in another edge. An off-diagonal entry in the vertex matrix would force one vertex's set of incident edges to be contained in another's, impossible for minimum degree two in a simple graph. Thus the restricted edge map is diagonal, and any diagonal can be offset in the private third mode. For $r<18$, use separately partitioned rank-one tensors with one private pair of axes per pin.

For each of the three original modes add its pin tensor using that **same full original mode** as a partition block and taking the other two modes as private blocks. This makes an ordinary partitioned TI instance with constantly many parts and side lengths $O(l)$. Grochow–Qiao IV, Theorem 5.1 removes the partitions with linear length. [Frucht, cubic rigid graph](https://doi.org/10.4153/CJM-1949-033-6) · [Grochow–Qiao IV, Theorem 5.1](https://arxiv.org/html/2306.16317#S5)

Greedily choose images for an ordered projective basis in each leg using those decisions, then check $(p-1)^l$ scalar choices once all line images are fixed. The analogous projective stabilizer chain on the target gives transversal witnesses by enumerating each next-line orbit and applying the same search. These transversals and the final diagonal group give generators in $p^{O(l)}$ queries and work besides the decision oracle. Compress the generators by representing the group faithfully as permutations on the disjoint union of the mode vector spaces and testing membership sequentially. Each accepted generator at least doubles the generated group, so $O(b\log p)$ remain. This compression also takes $p^{O(l)}$ time.

For the decision oracle, Grochow–Qiao IV, Theorem 2.1 sends an $n\times m\times s$ tensor to an alternating matrix space of dimension at most $s+1$ and matrix size at most $3n+2m+2$. Ivanyos, Mendoza, Qiao, Sun and Zhang, Theorem I.4, gives $q^{\widetilde O((N+d)^{3/2})}$ time for two congruence instances given by bases of $d$-dimensional spaces of alternating $N\times N$ matrices over $\mathbb F_q$. Here $q=p$ is an odd prime and $N+d=O(l)$. Combined with the search construction and (5) this gives
$$
 \bigl(p^{\widetilde O(l^{3/2})}+h\bigr)
 \operatorname{poly}(\text{explicit input length},e,\log p).
$$
If the field stabilizer is just $Z$, the fast field decision and search bound transfers at arbitrary input precision. The promise concerns only the residue stabilizer. [Grochow–Qiao IV, Theorem 2.1](https://arxiv.org/html/2306.16317#S2) · [Ivanyos et al., Theorem I.4](https://chuanqizhang.com/assets/pdf/pdf/focs24.pdf) · [Furst–Hopcroft–Luks, permutation-group membership](https://hdl.handle.net/1813/6282)

## 5. Explicit finite commutative rings of prime-power characteristic

The local argument works over any finite commutative unital ring of additive exponent $p^e$, for modules specified by additive cyclic bases and multiplication/action tables. It uses the additive generator count $b'=\sum_i\dim_{\mathbb F_p}(E_i/pE_i)$ in place of $b$, where $E_i=\operatorname{End}_R(M_i)$. Here source and target are presented in common mode modules.

For any finite associative endomorphism ring $E$ annihilated by $p^e$, write $X=p^kY$. Define the exponential and logarithm by evaluating their one-variable series in $Y$ with coefficients $p^{km}/m!$ and $(-1)^{m+1}p^{km}/m$, respectively. These coefficients are integral $p$-adically and belong to $p^k\mathbb Z_p$ for $m\ge1$. Their valuations grow at least linearly. If two choices of $Y$ represent the same $X$, all differences of powers are annihilated by $p^k$, using telescoping as in Section 1. Thus the evaluations are well-defined. The inverse identities follow by composition of the one-variable series over $\mathbb Z_p$. In particular the inner series can be divided by $p^k$ before substituting it for $Y$, with integral coefficients. On the tensor product the $Y_i$ on separate factors commute. The coefficient of $(\sum_iY_i)^m$ in $B$ is $p^{km}/(m+1)!$, which belongs to $p\mathbb Z_p$ for $m\ge1$. This proves (3) and (4) directly for the torsion ring, with no lifting order required.

Compute each $E_i$ as the kernel of additive linear congruences requiring an additive endomorphism to commute with the supplied ring generators. Build the balanced tensor product over $R$ by starting with the tensor product over $\mathbb Z$ of the additive groups and taking the quotient by the balancing relations between adjacent factors. It suffices to generate these relations on triples of additive cyclic generators and on a ring basis. The coefficient modules and all maps used in (5) are thus computed by polynomial-size Smith elimination. The shallow units lift through the nilpotent ideal $p^k E_i$, and one tests the chosen lift on $M_i/pM_i$ as an additive group. This gives the local algorithm and the total bound $p^{k b'}$ times polynomial bit work in the explicit tables. The tables must expose the additive structure and operations used here.

## Exact finite controls

Run `python Algorithms.py`. The script exhaustively compares the exponential and derivative formulas with the actual principal-unit actions for four free or mixed cyclic families at $p=2,3$, with two scalar modes. It checks 189,435 congruence layers and directly matches counts of stabilizer elements with sizes of linear kernels. It also checks that the enumerated matrix exponentials are exactly the raw principal congruence matrices.

## Relation to prior work

The earlier prime-power tensor reduction uses bounded-degree group-algebra jets and turns the fixed-ring problem into a prime-field decision problem, with cutoff $p^{e-1}$. The algorithm here permits variable $e$ and works directly with the original modules after the first one or two endomorphism-ring digits. The linear systems still read the full input precision. For instance the rank-one tensors $0$ and $p^k$ agree modulo $p^k$ when $e>k$ and are inequivalent. [PrimePowerTensorIsomorphism](https://github.com/Dugongue/MathProofs/tree/main/PrimePowerTensorIsomorphism)

The prior dyadic prescribed-residue theorem treats free modules with simultaneous literal quadratic or bilinear data, including degenerate forms, at the full residue depth $1$. Its proof uses a central series with order-two quotients and compressed generating sets. The present method gives direct linear congruences on the entire kernel at depth $2$ in the dyadic case and depth $1$ at odd primes. It also computes a linear-kernel counting formula and allows nonfree modes. [DyadicPrescribedResidueTransport, GP-0102](https://github.com/Dugongue/MathProofs/blob/cb95f7fe15deb558cb5014ca2227736554246543/GrochowCatalogueProofsVII/DyadicPrescribedResidueTransport.md)

Grochow, Qiao, Stange and Sun, Part V, establish equivalence between tensor actions over prime-power rings. For alternating matrix space isometry their Theorem 5.9 gives $p^{O(\mu^{17/9}(\log p)^{8/9})}$ times the cost of a matrix-tuple isometry test, where $\mu$ measures the total logarithmic group size in their setting. Theorem 5.22 and Proposition 5.29 use an involutive-algebra radical and square-root correction for tuple isometry at odd $p$. The algorithm here has quadratic dependence on the mode ranks and separates out the full precision. It applies to the alternating action by tying the first two group factors and the first two logarithm variables, giving $p^{k(n^2+m^2)}$ times polynomial work for $n\times n\times m$ free arrays with that action. Their subquadratic dependence on $\mu$ can be sharper at low precision. The exact linear correction (4) is the source of the high-precision bound here. Priority for this algorithm has not been established. [Grochow–Qiao–Stange–Sun, Part V, Theorems 1.6, 5.9 and 5.22 and Proposition 5.29](https://arxiv.org/html/2611.00735v1)
