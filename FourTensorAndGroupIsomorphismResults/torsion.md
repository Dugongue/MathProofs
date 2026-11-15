# Subquadratic-exponent isomorphism of tensors in arbitrary modules over finite principal ideal rings

**Theorem.** Fix a finite commutative principal ideal ring $R$. Given two tensors in triple tensor products of explicitly presented $R$-modules, their isomorphism under the product of three module automorphism groups can be decided in time

$$
2^{O_R(n^{7/4}\log(n+2))}\operatorname{poly}(L),
$$

where $L$ is the explicit input length and $n$ bounds the number of presented generators in each mode. If $R$ has odd characteristic the bound is $2^{O_R(n^{3/2}\log^2(n+2))}\operatorname{poly}(L)$. The same holds when the input gives different presentations for corresponding source and target modules and asks for isomorphisms between them. This is an informal proof. It covers the general-module tensor action, including tensors whose modes have mixed cyclic lengths.

## 1. Contractions over varying coefficient quotients

First let $R$ be local, with maximal ideal $(\pi)$ and length $e$ such that $\pi^e=0$. Write $R_a=R/(\pi^a)$ for $1\le a\le e$. Every finitely presented $R$-module decomposes as a finite sum of cyclic modules $R_b$. Compute such decompositions and the coordinate maps by Smith operations, which over this fixed ring use the least valuation pivot and unit arithmetic.

Let $T\in M_1\otimes_R M_2\otimes_R M_3$. For each $a$ form

$$
E_{1,a}=\operatorname{Hom}_R(M_1,R_a),\qquad E_{2,a}=\operatorname{Hom}_R(M_2,R_a),\qquad N_a=M_3/\pi^aM_3.
$$

The bilinear map $B_{T,a}:E_{1,a}\times E_{2,a}\to N_a$ is given by applying both functionals to $T$. On $x\otimes y\otimes z$ its value is $f(x)g(y)[z]$. The product is defined in the $R_a$-module $N_a$. Each derived module uses $O_R(n)$ cyclic coordinates. Tensor coefficients and all the evaluation tables are computable in polynomial time from the supplied presentations and the tensor coefficients in the generators.

**Separation.** The family of all $B_{T,a}$ determines $T$. In cyclic bases, the $(i,j,k)$ coordinate of $T$ is an element of $R_b$, where $b$ is the minimum of the three coordinate lengths. Take $a=b$. A functional on either of the first two modes can send the selected cyclic generator to $1$ in $R_b$ and all the others to zero, since its chosen coordinate length is at least $b$. Apply those two functionals, then examine the $k$-th coordinate of $N_b$, which is exactly $R_b$. The result is the desired coefficient.

## 2. Enforce one action on every occurrence of each module

Keep the three original modules, all the $E_{i,a},N_a$, and rigid copies of each $R_a$. Keep the bilinear evaluation maps $E_{i,a}\times M_i\to R_a$ for $i=1,2$, the quotient maps $M_3\to N_a$, and the bilinear $B_{T,a}$. Mark $1$ in each $R_a$ so its $R$-linear action is the identity. If the original actions are $g_1,g_2,g_3$, preservation of the evaluation pairing forces the actions on the $E_{i,a}$ to be precomposition by $g_i^{-1}$. Surjectivity of the quotient maps forces the actions on the $N_a$ to be induced by $g_3$. Conversely those actions preserve the evaluations and quotient maps. By functoriality of contraction and separation from Section 1, preservation of all remaining maps is equivalent to $(g_1\otimes g_2\otimes g_3)T=T'$. The diagram therefore preserves and reflects tensor isomorphism.

The use of all levels is important. For example, over $\mathbb Z/4$ a functional to the full ring sends an element of order two to an even element. Applying two such functionals to a pure tensor can erase the tensor because the two even values multiply to zero. Evaluation in the quotient of the correct length distinguishes that coefficient.

## 3. Linear-size implementation on free modules over the prime-power integer ring

The characteristic of the fixed local ring is $p^f$. Set $S=\mathbb Z/p^f\mathbb Z$. For each diagram sort $M$, choose an additive cyclic decomposition and form its minimal free $S$-module cover $q_M:F_M\to M$ and a standard embedding $i_M:M\to J_M$ into a free $S$-module of the same rank. In a cyclic coordinate of order $p^b$, the cover reduces modulo $p^b$ and the embedding maps $x$ to $p^{f-b}x$. Each of these free ranks is $O_R(n)$. The additive decompositions are computable by expanding the $R$ relations using the fixed additive generators of $R$ and diagonalizing over $S$.

Keep the linear maps $i_Mq_M$ and $i_M(r\,{-})q_M$ for every $r\in R$ and every sort. The first maps induce common additive isomorphisms on the original modules under any invertible actions on the covers and embedding spaces. Keeping the other maps forces those induced isomorphisms to commute with every scalar in $R$. For a linear map $A:M\to N$ record $i_NAq_M$. For a bilinear map $B:M\times N\to P$ record $i_P B(q_M{-},q_N{-})$. Record a distinguished element using its image under $i_M$. Injectivity and surjectivity of the embeddings and covers give reflection of all the requested equations.

For completeness, every original additive isomorphism lifts to invertible actions on both spaces. For the cover, choose preimages of the transformed generators. The resulting matrix is invertible modulo $p$, since a minimal generating list is a basis modulo $pM$. For the embedding, take ordered cyclic bases of equal lengths on the two sides. If an isomorphism is given by $u_{ij}$ modulo $p^{b_i}$, choose entries $P_{ij}$ solving

$$
P_{ij}p^{f-b_j}=p^{f-b_i}u_{ij}.
$$

When $b_i>b_j$, existence follows from the divisibility of $u_{ij}$ by $p^{b_i-b_j}$. When $b_i\le b_j$, use $P_{ij}=p^{b_j-b_i}u_{ij}$. Ordered by cyclic length, $P$ modulo $p$ is block triangular, and its diagonal blocks are those of the induced invertible map on $M/pM$. Thus it is invertible. Independent choices of both lifts satisfy every marked equation because their induced maps on the original module agree.

To use a single alternating map, take one free input space consisting of separate copies of the two input sorts of each recorded bilinear map, with injections tying those copies to the genuine sort actions. Take an output direct sum of separate copies of the outputs, tied in the same way. Mark the injections for both sums. On each pair of input copies insert the alternating extension $B(x,y')-B(x',y)$ into its output component. This construction works even if a bilinear map repeats a module sort, because its two input copies are different. Keeping the injections forces the input and output actions to be direct sums of the prescribed actions. There are only a constant number of maps and sorts for fixed $R$.

The algorithm of [the short-probe proof](ALGORITHM.md) applies to this single alternating bilinear map on free modules over $S$: use Sections 2–5 and their prime-power version. Carry every additional linear map and named point as an extra entry of the final ordered alternating tuple, using the free-sort markers in Section 5. This leaves the probe enumeration unchanged, and the tuple matrix dimension stays $O_R(n)$. The proof of that algorithm applies to alternating maps with arbitrary radicals. It yields the stated even- and odd-characteristic bounds, using the published ordered tuple solvers. [Sun, Theorem A.1](https://arxiv.org/html/2611.05920#A), [Grochow–Qiao–Stange–Sun, Theorem 5.22](https://arxiv.org/html/2611.00735v1#S5.SS3)

## 4. Product rings and scope

A fixed finite commutative principal ideal ring is a product of finite local principal ideal rings. The central idempotents split every module and tensor product. Products of tensors from different factors vanish by the balancing relation, and module isomorphisms act factor by factor. Apply Sections 1–3 on each factor. The mode-generator bounds grow only by fixed constants.

The proof combines the prior prime-power short-probe algorithm with coefficient-level contractions and a dimension-controlled diagram for torsion. Grochow–Qiao–Stange–Sun distinguish free and arbitrary-module tensor isomorphism and develop reductions for the latter. The specific quantitative bound here tracks the original generator counts and handles the actual tensor product across mixed cyclic lengths. The argument gives an informal all-input theorem under the stated fixed-ring assumption. Priority for this bound remains unestablished. [Grochow–Qiao–Stange–Sun, definitions and finite principal ideal rings](https://arxiv.org/abs/2611.00735)

For fixed tensor order $d\geq3$, group the original modes into three sets of size at most $b=\lceil d/3\rceil$. At each node of a binary tree within a group, retain the genuine tensor-product module and the corresponding bilinear pure tensor map. These maps force the induced actions at all internal nodes because pure tensors generate every tensor product additively. Apply Sections 1–3 to the three roots and keep the tree maps in the same bilinear diagram. Each node uses at most $n^b$ generators, and the total number of nodes is fixed. This gives the same bounds with $n$ replaced by $n^b$, for arbitrary presented modules over the fixed principal ideal ring. This is a runtime bound for those inputs. The [same-ring balanced order reduction](order.md) separately produces an ordinary three-tensor instance for free inputs.
