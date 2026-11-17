# Single-instance orientation tests from a short pencil anchor

Work over a fixed finite field $F$, in particular $\mathbb F_3$. The tensors are explicit square matrix pencils $M_X:U_X\longrightarrow\operatorname{Hom}(V_X,W_X)$, where $X$ is $T$ or $S$, $\dim U_X=k$, and $\dim V_X=\dim W_X=n$. A transporter is a triple $(f,g,h)$ with
$$
M_S(fx)=hM_T(x)g^{-1}\qquad(x\in U_T).
$$
This convention possibly inverts some original determinant entries. A prescription of determinant one is unchanged by inversion.

Fix $r\ge1$ independent of the input. Suppose $k=O(\log N)$, where $N$ is the dense input length. On the source, require a tuple $a,b_1,\ldots,b_r\in U_T$ with $A=M_T(a)$ invertible. Write
$$
C_i=A^{-1}M_T(b_i),\qquad
D(x)=A^{-1}M_T(x).
$$
Let $C=\operatorname{End}_{(C_i)_i}(V_T)$ be the simultaneous centralizer algebra of the short tuple. Let $E=\operatorname{End}_{(D(x))_{x\in U_T}}(V_T)$ be the simultaneous centralizer algebra of the whole normalized pencil, obtained using a basis of $U_T$. The condition is
$$
\det(C^\times)=\det(E^\times)\subseteq F^\times. \tag{1}
$$
The condition and anchors are recoverable deterministically from the raw tensors in polynomial time. No corresponding condition is required on a separately chosen anchor on the target.

Under this hypothesis, ordinary, one-sign, two-sign and full special-linear comparison all reduce to one ordinary TI instance. In fact the construction can prescribe any subset of the three determinant values over the fixed field. Its time and output size are polynomial in $N+|F|^{(r+1)k}+2^k$. Constructing the instance uses no TI oracle.

## 1. Determine the anchor determinant fiber

Enumerate all candidate destination tuples $a',b'_1,\ldots,b'_r$ in $U_S$. Discard a tuple when $A'=M_S(a')$ is singular. If a transporter matches the anchors, then
$$
h=A'gA^{-1},\qquad gC_i=(A'^{-1}M_S(b_i'))g.
$$
For each tuple obtain an invertible simultaneous conjugator $g_0$, or prove none exists, by the constructive fixed-field module isomorphism algorithm. Use the two tuples as modules over the free associative algebra on $r$ generators. Every possible anchor-only column map is $g_0u$ with $u\in C^\times$. Thus its determinant set is
$$
\det(g_0)\det(C^\times),
$$
and the row determinant is always $\det(A')\det(A)^{-1}\det(g_0u)$. Discard the tuple if this set, together with that row relation, misses the prescribed matrix-mode determinants.

For completeness, $\det(B^\times)$ for an explicit unital subalgebra $B\le\operatorname{End}_F(V_T)$ is computable in deterministic polynomial time at fixed $F$. Compute its Jacobson radical $J$ and the explicit simple factors of $B/J$ using finite-field algebra decomposition. In the radical filtration of the module $V_T$, a simple factor $M_d(K)$ acts on $m$ copies of $K^d$, where $m$ sums the multiplicities through all grades. Its determinant is the norm of its $K$-determinant to the power $m$. Radical units have determinant one and every quotient unit lifts. Since each finite-field norm is surjective, the formula determines the subgroup by integer arithmetic on exponents modulo $|F^\times|$. The multiplicities are dimensions of the images of a primitive diagonal idempotent on the corresponding grades divided by $[K:F]$. This computes both sides of (1) and the anchor coset. [Brooksbank–Luks, module isomorphism](https://ix.cs.uoregon.edu/~luks/ModIso.pdf) · [Ivanyos–Qiao, Theorem 18](https://arxiv.org/abs/1708.03495).

## 2. Retain the original tensor and label map

For each retained target tuple, construct an ordinary typed tensor system comparing the original pencils with the specified paired labels. Pin the labels by linear maps from a fixed scalar sort. If a label determinant is prescribed, attach the exterior algebra on each $U_X$, its unit, and the degree-one inclusion. These force the auxiliary isomorphism to be the one induced by $f$. Compare the source top wedge with the target top wedge multiplied by the prescribed determinant in the input bases. This costs $2^k$ dimensions before compilation. The number of tensor sorts and relation types in each branch is fixed for fixed $r$.

If such a branch is isomorphic, let $(f,g,h)$ be its actual original transporter. Its matrix-mode determinants are related by the anchor equation and its column determinant lies in the computed anchor coset. By (1), any other desired column determinant in this coset differs from $\det g$ by the determinant of some $u\in E^\times$. The triple
$$
(1,u,A u A^{-1})
$$
stabilizes the entire source pencil: commuting with $D(x)$ gives $AuA^{-1}M_T(x)u^{-1}=M_T(x)$. It fixes every label and its row and column determinants both equal $\det u$. Composing the actual transporter on the source with this triple corrects its matrix-mode determinants simultaneously and preserves the label map. This proves soundness. A genuinely prescribed transporter selects one enumerated branch and satisfies all its marks, proving completeness.

Compile the fixed-signature branches to ordinary TI. A polynomial number of ordinary TI queries joined by OR compiles to one ordinary TI query by the existing balanced unordered-pair construction. At a binary OR, compare the unordered pairs $\{(P,R),(Q,S)\}$ and $\{(P,S),(Q,R)\}$ of ordered pairs of isomorphism types. A balanced tree has logarithmic depth, so its unfolding has polynomial size. A fixed-signature tensor-system compiler represents the whole colored tree and its tensor leaves. [Chen–Grochow–Qiao–Tang–Zhang, Theorem 4.1](https://arxiv.org/html/2306.03135v2#S4).

## 3. Explicit scope

When $r=1$, the decomposition of $V_T$ into primary cyclic modules for $C_1$ shows that $\det(C^\times)$ is generated by norm values raised to the individual elementary-divisor exponents. Indeed, on the primary summands $F[x]/(p^e)$ of a given length $e$, a quotient unit acts on each of the $e$ power grades by the same matrix over $F[x]/(p)$. Off-diagonal maps between distinct lengths are in the radical of the endomorphism algebra, along with the maps divisible by $p$ within a fixed length. Thus over $\mathbb F_3$, all elementary-divisor exponents even imply $\det(C^\times)=\{1\}$, and (1) follows from containment. A regular Jordan nilpotent of even dimension is a simple example: its centralizer consists of polynomial functions of the shift, and each unit has all diagonal entries equal in the Jordan basis.

For a raw family with unbounded mode widths, take even $n$, $k=2+\lfloor\log_3 n\rfloor$, and any $k$-dimensional slice space containing $I_n$ and a regular nilpotent shift $J_n$. The extra slices can be arbitrary independent matrices outside $\langle I_n,J_n\rangle$. Arbitrary simultaneous rebasings of all three modes preserve the existence of the anchor, because the ratio at the transported labels is similar to $J_n$. The raw algorithm finds a suitable anchor by enumerating at most $|F|^{(r+1)k}$ tuples. The same proof applies when some anchor centralizer has nontrivial determinant image, provided the full ordered-pencil stabilizer realizes that image as in (1).

This family includes genuinely constrained matrix-mode signs. Take $4\mid n$ and the slices $I,J,\ldots,J^{k-1}$. A stabilizer with column map $g$ takes $I$ to an invertible polynomial $u\in\mathbb F_3[J]$ and $J$ to a slice $M(fb)$, so $gJg^{-1}=u^{-1}M(fb)\in\mathbb F_3[J]$. Similarity forces this polynomial to have zero constant coefficient and nonzero linear coefficient $\alpha$, since it is nilpotent of index $n$. For a cyclic vector $v$, the basis $v,P(J)v,\ldots,P(J)^{n-1}v$ for $P(J)=gJg^{-1}$ has transition determinant $\alpha^{n(n-1)/2}$ from the corresponding $J$-basis. The map between the bases is a conjugator of determinant one since $4\mid n$. All others differ by a unit centralizing $J$, which also has determinant one. Hence $g$ has determinant one. The row map is $ug$ and $\det u=1$ because the nonzero constant coefficient is repeated an even number of times. Rebasing only the column mode by a map of determinant minus one gives an ordinary-equivalent pair with no determinant-one column transporter.

The sufficient condition combines constructive module isomorphism, the determinant image of a unit group, and the earlier ordinary TI conjunction and disjunction constructions. Equality of the two computable determinant images makes sign correction exact after any full-tensor extension. The scope is square pencils with a logarithmic label dimension and a fixed-length anchor satisfying (1). The proof is informal and publication priority is unverified.
