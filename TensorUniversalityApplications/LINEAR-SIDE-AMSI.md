# Linear-order search-to-decision for alternating matrix spaces

**Theorem.** Let $\mathcal A,\mathcal B$ be spaces of $n$ by $n$ alternating matrices over a presented finite field $\mathbb F_q$. There is a deterministic algorithm that finds $P\in\mathrm{GL}_n(\mathbb F_q)$ with $P\mathcal A P^{\mathsf T}=\mathcal B$, or determines that none exists, using at most $1+nq^n$ queries to ordinary alternating matrix space isometry. Each query has matrix order at most $48n+6$, independent of $\dim \mathcal A$ and $\dim \mathcal B$. The work outside the decision oracle is $q^n\operatorname{poly}(n,\log q)$ bit operations in a standard explicit finite-field presentation. The same query and time bounds give exact automorphism group orders and exact isometry counts. The theorem includes characteristic two and arbitrary common radicals.

This meets the two quantitative requirements of Grochow and Qiao's Open Question 10.5 in the preprint of Part I. Part IV gives linear-length search for ordinary 3-tensors and sketches a direct diagonal-restriction method for counting alternating-space isometries, using their graph-based diagonal gadget and block compiler. The construction below gives a deterministic direct prefix test with its matrix order bounded solely in terms of $n$. It uses the named-summand and evaluation mechanism from the solution of Open Question 7.4. Here contraction extracts the labeled lines from a binary relation, and symplectic rank tags make the summands recoverable after forgetting the labels. The original alternating space remains on an $n$-dimensional carrier throughout this encoding. [Part I, preprint Open Question 10.5](https://arxiv.org/html/1907.00309#S10.SS2) · [Part IV, Theorem 2.5 and Sections 4.5 and 7.3–7.4](https://arxiv.org/html/2306.16317)

## 1. A space that recognizes an ordered partial frame

Work first over any field $K$. Let $u=(u_1,\dots,u_k)$ be an independent list in an $n$-dimensional space $V$, where $1\le k\le n$, and set $L_i=Ku_i$. When $k\ge2$ also set $L_*=K(u_1+\cdots+u_k)$. It is distinct from every $L_i$ by independence. Form the following list of nonzero subspaces $U_1,\dots,U_t$ of $V$, with repetitions allowed.

- If $k=1$, include only $L_1$.
- If $2\le k\le6$, include $i$ copies of $L_i$ for every $i$, and $k+1$ copies of $L_*$.
- If $k\ge7$, include each $L_i$ once and $L_*$ twice. On the label set $\{1,\ldots,k\}$ use the tree with center 1 and three arms $2$, $3,4$, and $5,6,\ldots,k$, in that order away from the center. Include $L_i+L_j$ once for each edge $\{i,j\}$ of the tree.

In every case $t\le5k$. Take $W=K^t$ with basis $w_1,\dots,w_t$ and let
$$
C_u=\bigoplus_{j=1}^t U_j\otimes K w_j\subseteq V\otimes W.
$$
For $\alpha\in W^*$ define $C_u(\alpha)=(\mathrm{id}_V\otimes\alpha)(C_u)$. It is exactly $\sum_{\alpha(w_j)\ne0}U_j$. For any subspace $D\subseteq V$, define $E_u(D)=\{\alpha\in W^*:C_u(\alpha)\subseteq D\}$. This is the coordinate subspace whose permitted nonzero coordinates are exactly the $j$ with $U_j\subseteq D$. In particular,
$$
\dim E_u(D)=\#\{j\mid U_j\subseteq D\}.
$$
If $(P,Q)\in\mathrm{GL}(V)\times\mathrm{GL}(W)$ sends $C_u$ to $C_v$ for another independent list $v$, then $C_v(\alpha)=P C_u(Q^*\alpha)$. Here $Q^*\alpha=\alpha\circ Q$. Therefore $P$ takes the lines occurring as nonzero one-dimensional contraction images to the corresponding lines for $v$, preserving the function $D\mapsto\dim E_u(D)$.

For $k=1$ this recognizes the only marked line. For $2\le k\le6$, the possible lines are exactly $L_i$ and $L_*$, with pairwise distinct values of $\dim E_u$. For $k\ge7$, the line $L_*$ is recognized by the value 2 and the $L_i$ have value 1. For distinct $i,j$, independence and $k\ge3$ imply that $L_*\not\subseteq L_i+L_j$ and that no third frame line lies in this plane. The only two-dimensional subspace in the list that can lie in that plane is the same plane. Thus
$$
\dim E_u(L_i+L_j)=2+\mathbf 1_{\{i,j\}\text{ is an edge}}.
$$
It follows that a transporter induces a permutation preserving the labeled tree. Its only degree-three vertex is the center. The branches have different lengths $1,2,k-4$, so each branch and each distance along it is fixed. Therefore the permutation is the identity. This recovers every ordered line as well as the sum line.

In all cases a transporter satisfies $P u_i=\lambda_i v_i$ with nonzero scalars $\lambda_i$. For $k\ge2$ preservation of the sum line implies all $\lambda_i$ equal, by independence of the $v_i$. For $k=1$ the common-scalar condition has just one entry. Conversely, if $P u_i=\lambda v_i$ for all $i$ and some $\lambda\ne0$, then $P$ sends every subspace in the list for $u$ to its counterpart for $v$. The map $P\otimes 1_W$ therefore takes $C_u$ to $C_v$. No hypothesis on the characteristic has been used.

## 2. Encoding the frame in ordinary alternating matrix space isometry

Identify alternating matrices on a coordinate space $H$ with bivectors in $\bigwedge^2 H$, so that $x\wedge y$ denotes $xy^{\mathsf T}-yx^{\mathsf T}$. This realizes exactly the alternating matrices, including zero diagonal in characteristic two. A matrix acts by contraction from $H^*$ to $H$. Congruence by $T$ carries the image of every matrix to its image under $T$, since the right-hand map $T^{\mathsf T}$ is invertible.

On $V\oplus W$ build the subspace
$$
S_{\mathcal A,u}=\mathcal A\oplus\{\text{cross-block bivectors from }C_u\},
$$
where $\mathcal A$ lies in $\bigwedge^2 V$ and a basis vector $x\otimes w_j$ of a cross-block summand becomes $x\wedge w_j$. This cross-block embedding is injective, because projection to the block from $W^*$ to $V$ recovers the rectangular matrix. A basis is obtained from a basis of $\mathcal A$ and the listed one- or two-vector bases for the $U_j$, paired with their separate $w_j$. With block-diagonal maps, the $V$-only and cross parts are invariant summands, so simultaneous transport is precisely transport of the two records.

We now produce an ordinary unmarked instance whose isometries recover such block maps. Put $b=n+t$ and adjoin fresh copies $V'$ and $W'$ of the two coordinate spaces. Adjoin disjoint spaces $H_1,H_2$ of dimensions $2(b+1)$ and $4(b+1)$, each with a standard invertible alternating matrix $J_1,J_2$ on its own coordinates. Such matrices are direct sums of $\begin{pmatrix}0&1\\-1&0\end{pmatrix}$ over every field. Add two bivectors
$$
F_V=\sum_{i=1}^n e_i\wedge e_i'+J_1,
\qquad
F_W=\sum_{j=1}^t w_j\wedge w_j'+J_2,
$$
where the $e_i$ are the standard coordinates of $V$ and primes denote the corresponding copies. Define the ordinary query space $S^+_{\mathcal A,u}=S_{\mathcal A,u}+K F_V+K F_W$. Its carrier order is $8b+6\le48n+6$. It has a basis given by the earlier basis and the two new slices, because the two heavy blocks are disjoint and absent in the earlier basis. Its dimension is $\dim\mathcal A+\sum_j\dim U_j+2\le\dim\mathcal A+5k+2$. The sum is at most $5k$ for $k\le6$ by the size of the list, and equals $3k$ for $k\ge7$.

For $M\in S_{\mathcal A,u}$, the rank of $M+\alpha F_V+\beta F_W$ belongs to
$$
[2(b+1)h,\ 2(b+1)h+2b],
\qquad h=\mathbf 1_{\alpha\ne0}+2\mathbf 1_{\beta\ne0}.
$$
The heavy block ranks give the left endpoint, and the remaining carrier has dimension $2b$. The four intervals are disjoint, so an arbitrary isometry $T$ from $S^+_{\mathcal A,u}$ to $S^+_{\mathcal B,v}$ maps $S_{\mathcal A,u}$ onto $S_{\mathcal B,v}$ and takes $F_V,F_W$ into their respective nonzero scalar cosets modulo the target $S_{\mathcal B,v}$.

Let $Z_{\mathcal A,u}$ denote the sum of the images of the matrices in $S_{\mathcal A,u}$. It is intrinsic to that matrix space. In the chosen decomposition it is $V_0\oplus W$, where $V_0=\sum_{A\in\mathcal A}\mathrm{im}(A)+\langle u_1,\ldots,u_k\rangle$. Indeed, contraction of a cross slice $x\wedge w_j$ spans $Kx+K w_j$ for $x\ne0$, and each $U_j$ is nonzero. The target has $Z_{\mathcal B,v}=\widetilde V_0\oplus W$ with the analogous formula, and $T Z_{\mathcal A,u}=Z_{\mathcal B,v}$.

First, $\operatorname{im}(F_V)\cap Z_{\mathcal A,u}=V_0$. For any $M\in S_{\mathcal B,v}$ and $\sigma\ne0$, a column combination of $\sigma F_V+M$ with zero output in $V'$ has zero dual input in the $V$ coordinates, because the $V$-to-$V'$ pairing is invertible. The remaining inputs produce only $V$ inside $V\oplus W$, since $M$ has zero $W$-by-$W$ block. Conversely all of $V$ is obtained from dual inputs in $V'$. Therefore $\operatorname{im}(\sigma F_V+M)\cap Z_{\mathcal B,v}=\widetilde V_0$, and $T V_0=\widetilde V_0$.

Second, $\operatorname{im}(F_W)\cap Z_{\mathcal A,u}=W$. In the target $\operatorname{im}(\sigma F_W+M)\cap Z_{\mathcal B,v}=\operatorname{im}(M_{VV})\oplus W$. To see this, a column combination with zero output in $W'$ has zero dual input in $W$. The possible $V$-coordinate outputs are exactly the image of $M_{VV}$ on the dual of $V$. These lie in $\widetilde V_0$. Independently, dual input in $W'$ can produce any $W$ component. The heavy blocks and the other copied coordinates give no additional columns in the intersection. Because $T$ preserves intersection dimensions, the target intersection has dimension $t$, which forces $\operatorname{im}(M_{VV})=0$. Thus $T W=W$.

The map on $Z$ now has two blocks. Extend $T|_{V_0}$ to an arbitrary invertible linear map $P$ on the full $V$, by choosing and mapping complementary bases. Every original data or cross matrix is supported as a bivector in $V_0\oplus W$. In a basis extending one for this subspace, all rows outside it vanish because the image lies in it, and all columns outside it vanish by alternation. Consequently $P\mathcal A P^{\mathsf T}=\mathcal B$, and $(P,T|_W)$ takes $C_u$ to $C_v$. This argument includes zero matrix spaces and degenerate data. In the other direction any block map $(P,Q)$ transporting the data and cross space lifts to the ordinary query by using inverse transposes on $V',W'$ and identity maps on the heavy blocks. Those maps preserve each marker and transport the old space as required.

Finally multiply $P$ by $\lambda^{-1}$ if its action on the ordered prefix has common factor $\lambda$. Congruence by this scalar rescales the whole matrix space by a nonzero scalar, so it preserves the isometry condition. We have proved both directions of a same-field, polynomial-time reduction from exact prefix feasibility to an ordinary alternating matrix space isometry query. The empty prefix uses the original query directly.

## 3. Searching and counting

Ask the oracle whether the original spaces are isometric. For a yes-instance choose the images of the standard basis $e_1,\ldots,e_n$ consecutively. Once images $v_1,\ldots,v_{i-1}$ have been found that admit a completion, enumerate the at most $q^n$ possibilities for $v_i$. Discard linearly dependent prefixes. For each remaining candidate use the compiled query with source prefix $(e_1,\ldots,e_i)$ and target prefix $(v_1,\ldots,v_i)$. The equivalence proved above makes the first yes-candidate a valid extension. There is always one because the current prefix admits a completion. At the end the selected columns give the desired isometry, verifiable by matrix operations. Query construction and other work per candidate are polynomial in $n,\log q$ under a standard finite-field representation with element arithmetic and enumeration in polynomial time per element.

For counting, let $G_0=\operatorname{Aut}(\mathcal A)$ and $G_i$ be the subgroup fixing $e_1,\ldots,e_i$ pointwise. For each $i$, the index $[G_{i-1}:G_i]$ is the orbit size of $e_i$ under $G_{i-1}$. Enumerate and count all feasible vectors $v_i$ using target prefix $(e_1,\ldots,e_{i-1},v_i)$ in the same exact prefix query with $\mathcal B=\mathcal A$. Because $G_n=1$, the product of the indices is $|G_0|$. For arbitrary $\mathcal B$, a yes-instance has an isometry coset of the same size and a no-instance has count zero. The count has $O(n^2\log q)$ bits.

## 4. The group version over odd prime fields

For odd $p$, the class-two exponent-$p$ group in commutator coordinates is specified by $V=G/[G,G]$, $B=[G,G]$, and the alternating bilinear map $\beta:V\times V\longrightarrow B$ whose values span $B$. The ordinary multiplication on $V\oplus B$ is
$$
(v,b)(v',b')=(v+v',b+b'+\tfrac12\beta(v,v')).
$$
These are the class-two coordinates of the Baer correspondence. With $n=\dim V$ and $m=\dim B$, the dual of the induced surjection $\bigwedge^2 V\to B$ embeds $B^*$ as an alternating matrix space on the $n$-dimensional coordinate space $V^*$. An isometry of those spaces gives the quotient map $g$ by inverse transpose. It uniquely determines the invertible commutator map $h$ because the two surjections have matching kernels after applying $\bigwedge^2 g$. Equivalently, $\beta'(gv,gv')=h\beta(v,v')$ for every pair. The group isomorphism is $(v,b)\mapsto(gv,hb)$ in these coordinates. Any isomorphism inducing the same maps has the form $(v,b)\mapsto(gv,hb+a(v))$ with $a:V\to B'$ linear. The multiplication formula proves additivity of $a$ and verifies every such shear. Consequently exact group isomorphism counts are $p^{nm}$ times the AMSI counts when the respective dimensions agree.

A group decision oracle in the same coordinate model can answer each query by using the query's independent slices as commutator coordinates. The resulting group has logarithmic order at most $m+53n+8$ in base $p$. The algorithm uses at most $1+np^n$ queries and $p^n\operatorname{poly}(n,m,\log p)$ work outside them, and outputs a map on coordinate generators. The bound covers central elementary abelian factors because $V$ is the quotient by the derived subgroup. Part IV already addresses polynomial-time search and counting in the Cayley-table representation. [Part II, Sections 3 and 4](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CCC.2021.16) · [Part IV, Theorem 1.5](https://arxiv.org/html/2306.16317#S1.SS2)

## Verification

The Lean companion checks the contraction-support criterion, the common-scale deduction, and disjointness of the rank windows. The independent audit binds the source bytes and records the transitive axioms, including a separate check of the frozen rank-window statement. The exact arithmetic replay passed 3,470 frame checks and 174 rank and image-intersection checks in prime fields. The full reduction and group interpretation are proved in the written argument above.
