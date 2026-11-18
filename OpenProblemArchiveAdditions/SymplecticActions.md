# Symplectic tensor isomorphism for five actions and fixed arity

**Theorem.** Over the same field, all five symplectic three-tensor actions corresponding to Definition 1.2 of Chen, Grochow, Qiao, Tang and Zhang are polynomial-time many-one equivalent to ordinary three-tensor isomorphism. For each fixed $d\ge 3$, plain symplectic $d$-tensor isomorphism also reduces in polynomial time to plain symplectic three-tensor isomorphism. These are reductions in the exact field-arithmetic model, and in polynomial bit time over a fixed finite field. The informal proof extends the plain action already proved in [TIEqTISp.lean](../TIEqTISp.lean). [Classical-group isomorphism paper](https://arxiv.org/html/2306.03135v2)

## A simultaneous extension on primal and dual supports

Suppose $P\subset V$ and $Q\subset V^*$, with counterpart subspaces $P'\subset V'$ and $Q'\subset V'^*$, where $\dim V=\dim V'$. Let $f\colon P\to P'$ and $h\colon Q\to Q'$ be isomorphisms satisfying
$$
(h\alpha)(fp)=\alpha(p)\qquad(p\in P,\ \alpha\in Q).
$$
Write $E=\operatorname{Ann}(Q)$ and $E'=\operatorname{Ann}(Q')$. Dualizing $h^{-1}$ via the evaluation identifications gives an isomorphism $\bar g\colon V/E\to V'/E'$. The pairing identity implies $\bar g([p])=[fp]$ for $p\in P$ and $f(P\cap E)=P'\cap E'$. Extend the restriction on $P\cap E$ to an isomorphism $E\to E'$. Pick a basis of $V/E$ beginning with a basis of the image of $P$. For this first part use representatives in $P$ and send them by $f$. For each remaining representative choose any lift of its image under $\bar g$. Together with the map on $E$ this defines an invertible $g\colon V\to V'$ that extends $f$ and induces $\bar g$. The quotient identity gives $(h\alpha)(gv)=\alpha(v)$ for all $v\in V$, so the inverse-dual action of $g$ agrees with $h$ on $Q$.

## Hyperbolic doubling reflects mixed tensor isomorphism

For each named mode space $V$, put $W=V\oplus V^*$ with alternating form
$$
\omega((v,\alpha),(w,\beta))=\beta(v)-\alpha(w).
$$
Embed a primal slot by $v\mapsto(v,0)$. Embed a dual slot by sending $\alpha$ to the functional $(v,\beta)\mapsto\alpha(v)$ on $W$. Apply these inclusions to the tensor in every slot to obtain a zero-padded tensor $\widehat T$. A change $g\in\mathrm{GL}(V)$ on a name lifts to $g\oplus(g^{-1})^*\in\mathrm{Sp}(W)$, with the required action on every embedded slot. The alternating form and lift work in characteristic two.

Conversely, suppose that a tuple of symplectic maps takes $\widehat T$ to $\widehat S$. A slot support is the image of the flattening into that slot. Under a product of invertible linear maps, the slot support transforms by the map in that slot. For each name take the sum $P$ of its primal slot supports and the sum $Q$ of its dual slot supports. The symplectic tuple restricts to isomorphisms between the padded $P,Q$ for $T$ and those for $S$. Its action on the ambient space and dual preserves their evaluation pairing, so the restricted maps satisfy the identity in the extension lemma. Replace each symplectic map on these supports by the general-linear map supplied by that lemma. Each input tensor belongs to the product of its slot supports, as seen by completing bases in each slot. The replacement therefore sends the original $T$ to $S$. This argument also applies to zero tensors and to tensors with deficient mode supports.

The five signatures are $U\otimes V\otimes W$, $U\otimes U\otimes V$, $U\otimes U^*\otimes V$, $U\otimes U\otimes U^*$ and $U\otimes U\otimes U$. One map acts on all occurrences of a given name, using its inverse dual on dual occurrences. The published general-linear equivalences for those signatures, recalled in Section 5 of Chen et al., followed by doubling establish the reductions from ordinary TI. In the reverse direction apply their Theorem 1.4 with the standard alternating forms, then the general-linear equivalences. This gives the symplectic counterpart to their Theorem 1.6. [Classical-group isomorphism paper](https://arxiv.org/html/2306.03135v2)

## Fixed higher arity

For $T\in V_1\otimes\cdots\otimes V_d$, introduce named spaces $W_i=V_i\otimes\cdots\otimes V_d$ for $3\le i<d$, and write $W_d=V_d$. Include the canonical isomorphisms $\mu_i\colon V_i\otimes W_{i+1}\to W_i$ as labeled three-tensors for $3\le i<d$. Store $T$ as a three-tensor on $V_1,V_2,W_3$, and include the alternating forms on each $V_j$ as labeled bilinear tensors. Two such systems are isomorphic exactly when the original tensors are symplectically isomorphic. The labeled forms impose the symplectic action on the original modes, and the $\mu_i$ force the auxiliary actions to be their iterated tensor products. Conversely those products give the required extension. There are at most $2d$ labeled tensors of order at most three, and their written dimensions are polynomial in the original dense input size for fixed $d$. The tensor-system compiler in Chen et al., Theorem 4.1, gives ordinary three-tensors. Apply plain hyperbolic doubling to obtain the symplectic three-tensors. This gives the symplectic counterpart to their Theorem 1.7. [Tensor-system compiler and higher-arity comparison](https://arxiv.org/html/2306.03135v2)
