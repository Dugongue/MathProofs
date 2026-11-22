# Parametric polymatroid recovery and ordinary tensor transport for split arrangements

Let $V$ have dimension $d$ over a field $k$, and let $U_1,\ldots,U_m\subseteq V$, $m\ge1$, be a family given by bases. Call it split if a single basis of $V$ spans each $U_i$ by a subset. Equivalently, there are subspaces $E_A$ indexed by $A\subseteq[m]$ with
$$
V=\bigoplus_A E_A,\qquad U_i=\bigoplus_{A\ni i}E_A .
$$
Write $a_A=\dim E_A$ and retain the supports of positive multiplicity, including the empty support when present.

**Theorem.** The slopes of two-level one-parameter objectives on an integer representable polymatroid recover the weighted hypergraph $(A,a_A)$ of any split arrangement, using
$$
O\left(1+b+\sum_{a_A>0,\ A\ne\varnothing}|A|\log(2m/|A|)\right)
\tag{1}
$$
slope queries, where $b$ is the number of positive supports. A deterministic polynomial-time certificate over the field recognizes split arrangements from their explicit linear data and constructs the decomposition. A label permutation lifts to an arrangement transporter exactly when it transports the recovered weighted hypergraph. Over a finite field the formula below counts all lifts.

There is also a polynomial-size construction of **ordinary, unmarked** three-tensors for which equivalence is exactly weighted hypergraph isomorphism. From an arbitrary coordinate presentation of one of these tensors, the hypergraph can be recovered in deterministic polynomial time over each fixed finite field. The transporter counts of the ordinary tensors are explicit. Over other fields the equivalence and the count formula when applicable follow from the same proof, while the arbitrary-coordinate reconstruction below uses access to the common eigenspaces of a split commutative matrix algebra.

## 1. The slopes and their sparse inverse

Set $r(J)=\dim\sum_{i\in J}U_i$. The dimension formula and the inclusion of the sum over $J\cap J'$ in the intersection of the two sums show submodularity. Append one dummy subspace $U_0=V$ and extend $r$ accordingly. Use the integer base set
$$
\mathcal B=\{x\in\mathbb Z_{\ge0}^{m+1}:x(J)\le r(J)\text{ for every }J\subseteq\{0,\ldots,m\},\ x(\{0,\ldots,m\})=d\}.
$$
It is the integer base set of an integral polymatroid. These are the domains of linear optimization in the basic M-convex setting. We only need its following explicit one-parameter restriction. For $S\subseteq[m]$ and $0\le t\le1$, give the indices outside $S$ weight $1$, the dummy weight $t$, and those in $S$ weight $0$. The maximum is
$$
H_S(t)=r([m]\setminus S)+t\bigl(d-r([m]\setminus S)\bigr).
\tag{2}
$$
Indeed, writing $J=[m]\setminus S$, any feasible value is $x(J)+t x_0\le t d+(1-t)x(J)\le td+(1-t)r(J)$. To attain it take a basis of $\sum_{i\in J}U_i$ extracted from the union of bases of those $U_i$, and label each vector by its summand. Complete the resulting independent list to a basis of $V$ with dummy labels. Its label counts fulfill all base inequalities. In particular, one slope query may be implemented by a single matrix rank. [Murota, Discrete convex analysis](https://doi.org/10.1007/BF02680565) · [Edmonds, Submodular functions, matroids, and certain polyhedra](https://ndlsearch.ndl.go.jp/books/R100000136-I1571417125743436416)

In the split case the slope $g(S)=d-r([m]\setminus S)$ equals $\sum_{A\subseteq S}a_A$. This follows because a basis vector contributes to the sum outside $S$ exactly when its membership pattern meets the complement. The transform determines $a_A$ uniquely by Möbius inversion. The following inverse avoids enumerating the Boolean lattice.

Read $a_\varnothing=g(\varnothing)$. At each later step subtract all already recovered supports with their weights from the slope oracle. Let $h(S)=g(S)-\sum_{A\subseteq S,\ \mathrm{recovered}}a_A$. If $h([m])=0$ all supports are known. Otherwise there is a remaining support. The predicate $h(S)>0$ is upward closed, because the unrecovered weights are nonnegative. Start from $C=[m]$ and use a balanced binary partition tree of the labels. To test a block $B$, query $h(C\setminus B)$. If positive, delete the whole block. If zero and $B$ has at least two labels, recursively test its two children. If zero at a leaf, retain that label. At the end the remaining $C$ is inclusion-minimal positive. In fact each retained label was tested for deletion from a candidate containing the final one, so deleting it from the final candidate also gives zero. A minimal positive set is a single remaining support and its value $h(C)$ is exactly its multiplicity.

Every failed block intersects the final support $A$, since otherwise monotonicity would force the final $h(A)$ to vanish. At depth $j$ at most $\min(2^j,|A|)$ blocks can fail. Every tested nonroot block has a failed parent. Summing over depths up to $\lceil\log_2 m\rceil$ and counting the query of each recovered weight gives (1). The only essential data for this reconstruction are the slopes. In the general coverage-function setting Chakrabarty and Huang reconstruct a true coverage function in $O(mb)$ queries when there are $b$ atoms. Related adaptive sparse Möbius-transform bounds use group testing in a broader real-coefficient model. The positive residual argument here uses the realized support sizes in the count. For a single nonempty atom with weight one and size $s$, each slope is a bit, so an adaptive slope procedure needs at least $\log_2\binom ms$ bits in the worst case. Thus (1) has the correct order in that case for $1\le s\le m/2$. [Chakrabarty–Huang, Recognizing coverage functions](https://www.cs.dartmouth.edu/~deepc/PUBS/CH-SIDMA.pdf) · [Erginbas, Adaptive Sparse Möbius Transforms](https://www2.eecs.berkeley.edu/Pubs/TechRpts/2026/EECS-2026-19.pdf)

## 2. Certifying the split representation

For arbitrary input, run the proposed sparse inverse, treating every nonpositive block response as a failed deletion, with a budget of $d$ positive supports, reject on a nonpositive proposed weight or on total multiplicity exceeding $d$, and stop the search when the total reaches $d=g([m])$. There are $O((d+1)m)$ rank queries in any such run. Insist on the dimension equations $\sum_{A\ni i}a_A=\dim U_i$, and for each proposed $A$ compute $W_A=\bigcap_{i\in A}U_i$ with $W_\varnothing=V$. Test whether there are $a_A$ independent representatives from each $W_A$, all jointly independent. This is linear matroid intersection with a partition matroid. The ground set contains a separately labelled basis of each $W_A$, and the capacity in that label class is $a_A$. It suffices to reach size $d$. Indeed, if independent representatives exist anywhere in the $W_A$, multilinearity of the determinant expands their nonzero determinant in terms of the listed bases. At least one term is nonzero and gives a selection on the ground set. The converse is immediate from the interpretation of a selection. Matroid intersection is deterministic polynomial time using the linear independence oracle. [Rado, A theorem on independence relations](https://doi.org/10.1093/qmath/os-13.1.83) · [Edmonds, Matroid intersection](https://www.sciencedirect.com/science/article/pii/S0167506008708173)

The selected vectors give $E_A$ by span. They form a basis of $V$, and for each $i$ the selected vectors with $i\in A$ lie in $U_i$ and have exactly its dimension. Thus a passed certificate implies splitting even if the residual predicate behaved irregularly during the search. A split arrangement always passes by the sparse inverse and its actual decomposition.

Recognition needs this final linear certificate. For example, three distinct coordinate planes in $k^3$ have the same sum ranks as any three distinct planes sharing a common line, whenever such planes exist. Every singleton has rank $2$ and every set of at least two planes has rank $3$. The triple intersections have dimensions zero and one, respectively. The first arrangement is split and the second is not.

## 3. Exact arrangement transporters

A transporter with prescribed $\sigma\in S_m$ carries $U_i$ onto $U'_{\sigma(i)}$. It preserves the slope function after relabelling, so it preserves $a_A$ by uniqueness of the transform. Conversely such weights give a transporter by choosing any linear isomorphism $E_A\to E'_{\sigma(A)}$ and taking their direct sum.

Fix a valid permutation and these identifications. Every lift differs from the chosen one by an automorphism preserving each $U_i$. Its block from $E_A$ to $E_B$ vanishes unless $A\subseteq B$, since $\bigcap_{i\in A}U_i=\bigoplus_{B\supseteq A}E_B$. Every matrix obeying that block rule preserves the subspaces by inclusion, and if invertible the inclusions are equalities by dimension. A linear extension of inclusion makes the blocks triangular. Invertibility is precisely invertibility on each diagonal block. Hence over $k=\mathbb F_q$ the lift count for each valid permutation is
$$
F_q(a)=q^{\sum_{A\subsetneq B}a_Aa_B}\prod_{a_A>0}|\operatorname{GL}_{a_A}(\mathbb F_q)|.
\tag{3}
$$

## 4. Removing the slice marks and recovering them computationally

Let $N=d+1$. Add private $N$-spaces $P_i$ and define
$$
\widetilde V=V\oplus\textstyle\bigoplus_i P_i,\qquad
\widetilde U_i=U_i\oplus P_i,\qquad
W=\textstyle\bigoplus_i W_i,
$$
where $W_i$ is a copy of $\widetilde U_i$ and $j_i:W_i\to\widetilde V$ is its inclusion. The ordinary tensor is the bilinear map
$$
T:k^m\times W\longrightarrow\widetilde V,\qquad T(x,w)=\sum_i x_i j_i(w_i).
\tag{4}
$$
Use independent general linear maps on all three modes. A slice $T(x,-)$ whose coefficient support has size $s$ has rank at least $sN$ by its private outputs. For $s=1$ its rank is at most $N+d<2N$. Thus every ordinary transporter permutes exactly the $m$ slice lines, characterized by nonzero rank below $2N$. Equal tensor shapes determine the same $m,d,N$, since $\dim\widetilde V=(m+1)d+m$.

Write the transporter as $T'(f x,g w)=hT(x,w)$. With $f(e_i)=\lambda_i e'_{\sigma(i)}$, the individual slice equations give $h(\widetilde U_i)=\widetilde U'_{\sigma(i)}$. For $w\in W_j$ and $j\ne i$, the same equations force the $W'_{\sigma(i)}$-component of $g(w)$ to vanish, by injectivity of $j'_{\sigma(i)}$. Hence for a given $h,\sigma,\lambda_i$ the map $g$ is forced on each block:
$$
g|_{W_i}=\lambda_i^{-1}(j'_{\sigma(i)})^{-1}h\,j_i .
$$
Conversely these maps give a transporter for any such $h$ and nonzero scalars. The padded arrangement is split with weights $a^+$ given by adding $N$ to every singleton. Those additions commute with relabelling. Consequently ordinary tensor equivalence of (4) is precisely weighted hypergraph isomorphism of the original split arrangements, and each valid permutation gives exactly $(q-1)^m F_q(a^+)$ ordinary tensor transporters. From any such tensor transporter one can recover the permutation and build a corresponding original arrangement transporter by Section 3. In the opposite direction any weighted hypergraph is realized by coordinate subspaces with the supplied atom dimensions. For weights of arbitrary bit length, this last realization has size polynomial in the sum of the weights, not necessarily in its logarithm. Unweighted hypergraph isomorphism therefore embeds with polynomial size.

The rank description also has an effective coordinate-independent complement. For any presented tensor of the promised form, solve the linear adjoint equations
$$
T(Ax,w)=T(x,Bw)
\tag{5}
$$
for endomorphisms $A,B$, and project this solution space to the first mode. In the displayed coordinates the first-mode solution space is exactly the diagonal algebra. To see this, take $x=e_i$, $w\in W_j$ with $j\ne i$. If $A_{ji}\ne0$, the left side spans $\widetilde U_j$ as $w$ varies, while the right lies in $\widetilde U_i$. Containment is impossible because $P_j$ is private. Thus $A_{ji}=0$; the remaining equations give $B=\bigoplus_i A_{ii}I_{W_i}$. Conversely all diagonal $A$ with that $B$ satisfy (5). After arbitrary basis changes the projected algebra is conjugate to the diagonal algebra. Over fixed $\mathbb F_q$, intersect eigenspaces by processing a linear basis of the algebra and testing all $q$ possible eigenvalues on each current block. Distinct coordinate lines are separated by some basis element because the full diagonal algebra separates them. The final common eigenspaces are exactly the slice lines. Compute their images, run the slope inverse, and subtract the known singleton padding. This recovers the hypergraph up to relabelling from the ordinary tensor, using only polynomially many field operations for fixed $q$. [Grochow–Qiao, Tensor Isomorphism-Completeness](https://arxiv.org/abs/1907.00309) · [Grochow–Qiao, linear-length reductions](https://arxiv.org/abs/2306.16317)

## Finite controls

The sparse inverse recovered all 256 unit-weight families on three labels and 400 seeded weighted examples on up to 30 labels. Direct enumeration of binary general linear groups agreed with (3) in 552 prescribed-permutation cases on at most three ambient coordinates. Linear elimination verified the expected adjoint kernel dimension in 50 padded binary tensors, half presented in a randomly changed first-mode basis. The finite experiments and the independently checked minimality lemma address individual steps of the written proof.

The equivalence, reconstruction and counts concern the explicit family (4). Coverage reconstruction, matroid intersection and rank marking are established ingredients. The combination gives a succinct route from parametric slopes to full ordinary tensor transport data on this family. Publication priority for the combination and the support-sensitive bound remains unconfirmed. Only the auxiliary minimality step is separately formalized.
