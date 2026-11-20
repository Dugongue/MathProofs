# Square-zero counterexamples to the tangency-flattening conjecture

The algebra $R=\mathbb C[x,y,z]/(x,y,z)^2$ refutes the equality for the multiplication-output factor $C=R$, the superscript appearing in Doležálek and Michałek’s February 2026 formulation of Conjecture 6.1. Its flattening rank is $20$ and its Hilbert tangent dimension is $18$, so the proposed identity on that factor predicts rank $18$. The proof extends to every square-zero algebra of embedding dimension at least three. It is an informal proof. [February formulation, §§3, 4.1 and 6.1](https://arxiv.org/html/2602.12762v1#S6.SS1)

Doležálek, Jagiełła, Oszer, Seynnaeve and Stastny’s October 2026 proof applies to the flattening that wedges a multiplication-input factor $R^*$. Their identity gives rank $18$ on that factor for the same example. Both ranks can be checked directly. The factor distinction matters here because the examples are non-Gorenstein and the two input factors have a different role from the output. [October definition and Theorem 1.1](https://arxiv.org/html/2610.17875v1#S3) · [October specialization to the input factor](https://arxiv.org/html/2610.17875v1#S5)

## Statement

Let $d\geq 3$, $P=\mathbb C[x_1,\ldots,x_d]$, $\mathfrak m=(x_1,\ldots,x_d)$ and $R=P/\mathfrak m^2$. Put $n=\dim_{\mathbb C}R=d+1$ and let $T\in R^*\otimes R^*\otimes R$ be its multiplication tensor. Then
$$
 \dim T_{[R]}\operatorname{Hilb}_n(\mathbb A^d)=d\binom{d+1}{2},
 \qquad
 \operatorname{rank}\Phi_{\mathrm T}^{C}(T)=\binom{d+3}{3}.
$$
Here $C=R$ is the multiplication-output factor of $T$. The target predicted rank is
$$
 n(n-1)(n-2)+dn-\dim T_{[R]}\operatorname{Hilb}_n(\mathbb A^d)
 =\frac{d^2(d+1)}2.
$$
Equality with the computed rank would require $2d^2-5d-6=0$, which has no integer roots because its discriminant is $73$.

## Hilbert tangent dimension

Write $V=\mathfrak m/\mathfrak m^2$. Thus $R=\mathbb C1\oplus V$ and $V^2=0$. The Hilbert tangent space is $\operatorname{Hom}_P(\mathfrak m^2,R)$. The ideal $\mathfrak m^2$ has $\binom{d+1}{2}$ minimal generators $x_ix_j$ for $i\le j$. For $i\ne j$ the relation
$$
 x_j\cdot x_i^2-x_i\cdot(x_ix_j)=0
$$
forces the constant terms of both images to vanish, by linear independence of $\bar x_i,\bar x_j$ in $R$. These relations cover all generators because $d\geq 2$. Conversely, each assignment of images in $V$ is valid. Every syzygy has all coefficients in $\mathfrak m$, since taking its degree-two part gives a linear relation among distinct monomials. Its image thus vanishes by $V^2=0$. The choices of images are independent and give the stated dimension.

## Tangency flattening rank

Let $E=R^*$, $\epsilon\in E$ be the projection onto the coefficient of $1$, and $U=V^*\subseteq E$ be the covectors vanishing at $1$. Write $L_a:R\to R$ for multiplication by $a$ and $L_a^*:E\to E$ for its dual. As $V^2=0$, we have
$$
 L_1^*=\operatorname{id}_E,\qquad
 L_a^*(\lambda)=\lambda(a)\epsilon \quad(a\in V).
$$

For the factor $C=R$, the tangency flattening is a map from $\bigwedge^3 E\otimes R\otimes R$ to $E^{\otimes3}$. In the convention where the untouched covector occupies the first output slot, its formula is
$$
 (\alpha\wedge\beta\wedge\gamma)\otimes a\otimes b
 \longmapsto
 \sum_{\mathrm{cyc}}\alpha\otimes
 \bigl(L_a^*\beta\otimes L_b^*\gamma-L_a^*\gamma\otimes L_b^*\beta\bigr).
$$
Indeed, alternate the three covectors and contract two slots of the alternating tensor against the two copies of $T$ with $a,b$ in the respective other factors. This is the tangency flattening of §3, up to the normalization of exterior alternation. [Tangency flattening construction, §3](https://arxiv.org/html/2602.12762v1#S3)

The formula preserves the decomposition of the image into subspaces with a specified number of $U$ factors. To see this, split the inputs into pure types $\bigwedge^3 U$ and $\epsilon\wedge\bigwedge^2 U$, and take each of $a,b$ in $\mathbb C1$ or in $V$. Any nonzero term has the same number of $U$ factors, since a contraction with a vector in $V$ must replace a covector in $U$ by a multiple of $\epsilon$. The four image dimensions are as follows.

- **Three $U$ factors.** Only the inputs $\bigwedge^3U$ with $a=b=1$ contribute. The image is the alternating copy of $\bigwedge^3U$ in $U^{\otimes3}$, of dimension $\binom d3$.
- **Two $U$ factors.** In each of the three placements of $\epsilon$, every output is alternating in the two $U$ slots. The corresponding three spaces are independent and each has dimension $\binom d2$. Taking an input from $\bigwedge^3U$ and contracting with one vector of $V$ gives all of the alternating space with $\epsilon$ fixed in the second or third slot, according to the contraction slot. In fact, for any two distinct basis covectors, use a third basis covector and contract with its dual basis vector to get the prescribed pair. Finally, the alternating tensors from $\epsilon\wedge\bigwedge^2U$ with $a=b=1$ project onto the full first-slot space. These images together have dimension $3\binom d2$.
- **One $U$ factor.** The output space has dimension $3d$. Contracting two vectors of $V$ against an input from $\bigwedge^3U$ gives every element of $U$ in the first slot, with the last two slots occupied by $\epsilon$. For an input covector in a basis of $U$, choose two other basis covectors and contract with their dual vectors. Contracting one vector against $\epsilon\wedge\bigwedge^2U$ with the other vector equal to $1$ gives the alternating difference of copies in the first and the other uncontracted slot. For instance, contract a basis covector distinct from the desired one. With the first-slot space already present these differences generate the full second- and third-slot spaces. Thus the rank contribution is $3d$.
- **No $U$ factors.** Contracting two vectors dual to distinct basis covectors $u,v\in U$ against $\epsilon\wedge u\wedge v$ produces $\epsilon^{\otimes3}$. The contribution is $1$.

The rank is therefore
$$
 \binom d3+3\binom d2+3d+1=\binom{d+3}{3}.
$$
In particular, when $d=3$ the conjectural equality would read $20-24=12-18$, so the two sides are $-4$ and $-6$. The quotient in this proof has socle dimension $d$. The Gorenstein minor-flattening conjecture in the same source has a different hypothesis and concerns a different map.
