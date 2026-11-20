# Tensor isomorphism over finite fields of the same characteristic

**Theorem.** Fix a prime $p$. For all positive integers $a,b$, ordinary 3-tensor isomorphism over $\mathbb F_{p^a}$ and over $\mathbb F_{p^b}$ are equivalent under deterministic polynomial-time many-one reductions. The reductions are uniform in $a,b$ when the fields are supplied by irreducible polynomials over $\mathbb F_p$. More generally, for any field extension $L/\mathbb F_{p^a}$ with the coefficient embedding supplied, the upward construction tests $\mathbb F_{p^a}$-isomorphism by ordinary 3-tensor isomorphism over $L$. Its equality of isomorphism conditions holds over every such $L$, including infinite extensions. The algorithmic assertion over $L$ uses its field arithmetic and the supplied coefficient map.

This answers the same-characteristic finite-field part of Grochow and Qiao’s Open Question 7.6. The question also asks about different characteristics and $\mathbb Q$. [Published article](https://epubs.siam.org/eprint/VA7M2DT6DFQMVDVWIBBN/full) · [Preprint Open Question 10.6](https://arxiv.org/html/1907.00309#S10.SS2)

Write a tensor $T\in U\otimes V\otimes W$ as the bilinear map $U^*\times V^*\to W$ given by contraction. If the maps on the tensor factors are $P,Q,R$, the corresponding maps on the three bilinear-map spaces are $P^{-\mathsf T}, Q^{-\mathsf T}, R$. These conversions are inverse and commute with extension and restriction of coefficients. Below the three named spaces will be the two input spaces and the output space of this bilinear map.

## From an extension to its prime field

Let $K=\mathbb F_{p^a}=\mathbb F_p[\theta]$. Regard the three input spaces as $\mathbb F_p$-spaces in the displayed field basis. Record multiplication by $\theta$ as a named linear endomorphism on each space. Record the original bilinear map as an $\mathbb F_p$-bilinear map using the multiplication table of $K$ in that basis. For earlier use of that coordinate construction see [Schrock, §2.4.4](https://math.colorado.edu/~tysc3584/Tyler_Schrock-PhD_Thesis.pdf).

An $\mathbb F_p$-linear map commutes with multiplication by $\theta$ exactly when it is $K$-linear, since multiplication by each field element is a polynomial in that endomorphism. Preservation of the named bilinear map then means exactly the original tensor equation. A $K$-linear isomorphism conversely preserves all named records, so restriction gives a bijection on isomorphisms at this marked stage. This argument also works down any finite simple field extension with its presentation supplied. The mixed system reduces to ordinary 3-tensor isomorphism over the smaller field by the low-arity compiler described below.

## From a finite field to an extension

Let $K=\mathbb F_{p^a}\subseteq L$. Apply the following construction to each of the three bilinear-map spaces of dimension $n$, with its input basis. Use $a$ copies $E_i=L^n$, where $i$ is taken modulo $a$. On each copy take the degree-$r$ homogeneous polynomials on its basis symbols, written as $S_{r,i}=\operatorname{Sym}^r E_i$ for $1\le r\le p$. In particular $S_{1,i}=E_i$. At each degree use one aggregate space $S_r=\bigoplus_i S_{r,i}$ with its standard monomial bases. Mark the different levels by one named endomorphism $D_r$ of each $S_r$, acting as multiplication by $\lambda_i$ on $S_{r,i}$. Choose the $a$ distinct $\lambda_i$ from $K$, which has at least $a$ elements. For fields represented by polynomials, the first $a$ base-$p$ digit vectors in the given basis supply them explicitly.

For $2\le r\le p$ include the named bilinear homogeneous multiplication $S_1\times S_{r-1}\to S_r$. It is standard multiplication within each level and zero between different levels. Include one more named **linear** map $I:S_1\to S_p$ by
$$
I(e_{i+1,j})=e_{i,j}^{p},
$$
on the basis symbols $e_{i,j}$, extending $L$-linearly. The cyclic index is essential. Finally, use the original bilinear map with scalars extended to $L$ on the three level-zero degree-one blocks, and extend it by zero on the other pairs of levels.

### Recovery of the coefficient field

A marked isomorphism commutes with each $D_r$, so it preserves every level. Write $g_i$ for its matrix at degree one and level $i$. Preservation of multiplication forces its degree-$r$ map at level $i$ to be $\operatorname{Sym}^r(g_i)$. This follows by induction, since homogeneous degree-$r$ monomials are products of one basis symbol and a degree-$(r-1)$ monomial. The induced symmetric power maps are invertible and preserve all the multiplication records.

Writing $g_i^{[p]}$ for entrywise $p$-th powers, the characteristic-$p$ identity
$$
\left(\sum_k (g_i)_{kj} e_{i,k}\right)^p
=\sum_k (g_i)_{kj}^p e_{i,k}^p
$$
shows that preservation of $I$ means exactly $g_{i+1}=g_i^{[p]}$. This follows in both directions by comparing coefficients of the linearly independent degree-$p$ monomials $e_{i,k}^p$. Going around the cycle gives $g_0^{[p^a]}=g_0$. The subfield $K$ consists of all the roots of $X^{p^a}-X$ in $L$, since its own $p^a$ elements are roots and a polynomial of that degree has no more roots in a field. Thus $g_0$ has entries in $K$, and its nonzero determinant is already nonzero over $K$.

Conversely any $g_0\in\mathrm{GL}_n(K)$ extends uniquely through all levels by entrywise powers and symmetric powers. These are invertible, since entrywise Frobenius on matrices takes a matrix and its inverse to inverse matrices. All structural maps are preserved by construction. Across two tensor inputs, the only data-dependent record is the extended bilinear map. Its restriction to level zero is preserved precisely when the three recovered $K$-linear maps preserve the original map. Consequently extension and restriction give inverse bijections on isomorphism sets at the marked stage, and both respect composition.

### Compilation and cost

For either direction put the named spaces in a direct sum. Mark them by separate unary subspace relations and extend the records by zero on their other input summands. The technique from the proof of Open Question 7.4 is to recover the auxiliary maps from the multiplication records on spanning pure products, here using commutative products and an additional cyclic link. The finite-field construction already has the arity needed for the Futorny–Grochow–Sergeichuk compiler. Apply its mixed-system reduction as stated in [Grochow–Qiao, Theorem 7.3](https://epubs.siam.org/eprint/VA7M2DT6DFQMVDVWIBBN/full) to obtain an ordinary tensor over the target field. See also [Wildness for tensors](https://arxiv.org/abs/1810.09219) and the [arity reduction](https://github.com/Dugongue/MathProofs/blob/main/GrochowProofTransfersIII/UNIVERSAL-TENSOR-ISOMORPHISM.md).

There are only $3p$ aggregate degree spaces and a number of named records bounded by a function of the fixed prime $p$. Thus the application of the fixed-signature compiler is uniform in $a$. For maximum input side $n\ge1$, the upward intermediate dimension is $O_p(a n^p)$, since there are $\binom{n+r-1}{r}$ monomials at degree $r$. In the downward construction the intermediate dimension is the sum of the three dimensions multiplied by $a$. The linear-length fixed-type compiler in [the companion ring proof, §3](PRESENTED-MODULE-TENSOR-ISOMORPHISM.md#3-erase-the-marks-over-the-original-ring) achieves the same order bounds on the sides of the final ordinary tensors. Apply it directly to the named spaces and their linear or bilinear records. In particular even dense tables have polynomial size in the dimensions and extension degrees at fixed $p$. None of the field operations need the enumeration of a whole extension field. Fixed input formats can be compared first, and a zero-dimensional mode needs only a format comparison. The final compilation gives decision reductions. Exact recovery and extension were proved for the marked intermediate systems.

To compare finite fields of degrees $a$ and $b$ with no divisibility hypothesis, reduce first to the prime field using the downward construction. Use the upward construction with source the prime field and target the field of degree $b$. The embedding of the prime field uses constants directly. Reverse the roles for the opposite reduction. The polynomial dependence here is at fixed prime $p$.

## Verification

The written proof gives both many-one reductions using the published low-arity compiler. The accompanying Lean file checks the pure-power identity, the composition of the local Frobenius links, and the fixed-field identity under any field embedding. The finite script independently checks actual substitutions in degrees $2$ and $3$, the cyclic matrix constraint over extension fields, and the scalar-action argument under restriction. Those checks cover the indicated identities and finite cases. Historical priority remains open.
