# Fixed Characteristic Field Independence for Tensor Isomorphism

**Status:** Informal mathematical proof, 31 October 2026. Prepared in the MathProofs project with AI assistance. The proof has received internal adversarial review; it is not Lean verified or externally peer reviewed. Publication priority is unestablished.

## Abstract

For each fixed prime $p$, ordinary three-tensor isomorphism over any two finite fields of characteristic $p$ is equivalent under deterministic polynomial-time many-one reductions. The reductions work on every tensor, including zero and nonconcise tensors, and do not require either field to embed in the other. The construction first expresses the source field through prime-field multiplication matrices, then forces every target-field transporter matrix to have prime-field entries. The latter condition is encoded by multiplication in the symmetric algebra, a linear pure-$p$-power inclusion, and an identity map. A published theorem of Futorny, Grochow and Sergeichuk converts the resulting fixed-signature system into one ordinary three-tensor instance.

This answers the finite same-characteristic clause of Grochow and Qiao's published Open Question 7.6. It does not answer the different-characteristic or rational-versus-finite-field clauses. All polynomial bounds below fix $p$; no uniform polynomial dependence on $\log p$ is asserted.

## 1. Statement and relation to the open question

Write $\mathbf{3TI}(F)$ for the following decision problem. Its input is a pair of dense arrays

$$
T,S\in F^{a\times b\times c},
$$

and its question is whether there are invertible matrices $U,V,W$ over $F$ with

$$
S=(U\otimes V\otimes W)T.
\tag{1}
$$

The three modes are ordered. No permutation of the modes or automorphism of the coefficient field is part of this equivalence relation.

**Theorem.** Fix a prime $p$. Let $F=\mathbb F_{p^s}$ and $K=\mathbb F_{p^t}$, where $s,t\geq 1$. There is a deterministic polynomial-time many-one reduction

$$
\mathbf{3TI}(F)\leq_m^P\mathbf{3TI}(K).
\tag{2}
$$

The construction is uniform in $s,t$ when the fields are supplied in standard polynomial presentations. Every coefficient in the constructed $K$-tensor belongs to $\mathbb F_p$. Exchanging $s$ and $t$ gives the reverse reduction.

For field presentations we use

$$
F=\mathbb F_p[\theta]/(f(\theta)),\qquad
K=\mathbb F_p[\xi]/(g(\xi)),
$$

where $f,g$ are supplied monic irreducible polynomials of degrees $s,t$. Field construction is not an uncharged preprocessing task: the presentations are given. Polynomial running time includes their description lengths and the explicit output coefficients in $K$. For each fixed pair of fields these descriptions are constants.

Grochow and Qiao define the TI classes through polynomial-time Turing reductions to fixed-order tensor isomorphism. Their fixed-order-to-three-tensor reduction, together with (2), implies

$$
\mathsf{TI}_{\mathbb F_{p^s}}
 =\mathsf{TI}_{\mathbb F_{p^t}}.
\tag{3}
$$

Their journal version explicitly asks about $\mathbb F_p$ versus $\mathbb F_{p^e}$ in Open Question 7.6, Section 7.2 [GQ]. The longer arXiv version numbers this field-comparison question 10.6. Equation (3) answers that clause. The other clauses remain separate.

## 2. The published compilation theorem used here

We use the following consequence of [FGS, Theorem 1.1 and Remark 1.1], also stated in linear-model language in [GQ, Theorem 7.3].

**Fixed-signature compilation theorem.** Fix finitely many vector-space sorts and finitely many specified tensor slots of orders at most three, permitting repeated sorts and primal or dual occurrences. Isomorphism of such explicitly based systems reduces to ordinary three-tensor isomorphism over the same field in polynomial time. The field may be arbitrary. The size polynomial may depend on the fixed signature.

Thus a specified linear map $A\to B$ is a tensor in $A^*\otimes B$, and a specified bilinear map $A\times B\to C$ is a tensor in $A^*\otimes B^*\otimes C$. Their isomorphism equations use the same unknown matrix whenever a sort occurs more than once. In particular, an endomorphism requires conjugacy, and a bilinear map with two copies of one input space uses one common input matrix.

The number of sorts and slots constructed below depends only on $p$. Consequently the published compiler suffices. We do not invoke a separate theorem for a growing number of components, and we do not need to re-prove the compiler.

## 3. Replace the source tensor by a bilinear map

For $T=(T_{ijk})$, define

$$
\beta_T:F^a\times F^b\longrightarrow F^c,
\qquad
\beta_T(x,y)_k=\sum_{i,j}T_{ijk}x_i y_j.
$$

Equation (1) is equivalent to the existence of invertible $F$-linear maps $P,Q,R$ with

$$
R\beta_T(x,y)=\beta_S(Px,Qy)
\quad\text{for every }x,y.
\tag{4}
$$

Indeed, if (1) holds, then

$$
\beta_S(x,y)=W\beta_T(U^{\mathsf T}x,V^{\mathsf T}y),
$$

so take $P=U^{-\mathsf T}$, $Q=V^{-\mathsf T}$ and $R=W$. The same substitutions reversed prove the converse. This reparameterization is performed over $F$, before restricting scalars.

Use the power basis $1,\theta,\ldots,\theta^{s-1}$ to write the three source spaces as prime-field spaces of dimensions

$$
D_1=sa,\qquad D_2=sb,\qquad D_3=sc.
$$

Expanding the field products in this basis gives a bilinear map

$$
\widetilde\beta_T:
\mathbb F_p^{D_1}\times\mathbb F_p^{D_2}
\longrightarrow\mathbb F_p^{D_3}.
$$

For each mode let $M_i$ be the prime-field matrix of multiplication by $\theta$. Regard the expanded map and these three matrices as tensors over $K$, using the canonical inclusion $\mathbb F_p\hookrightarrow K$.

The source field $F$ itself need not embed in $K$. At this stage we have only expanded its arithmetic into prime-field coordinate matrices.

**Centralizer lemma.** A prime-field-linear map $G:\mathbb F_p^{D_i}\to\mathbb F_p^{D_i}$ commutes with $M_i$ if and only if it is $F$-linear on the original source space.

**Proof.** Commutation with $M_i$ implies commutation with every polynomial in $M_i$. Every element of $F$ is a polynomial in $\theta$, so $G$ commutes with multiplication by every source scalar. This is precisely $F$-linearity. The converse follows directly from $F$-linearity. $\square$

It is essential that $G$ in this lemma is prime-field-linear. An arbitrary $K$-matrix centralizing $M_i$ could admit extra transformations. The next construction forces exactly the needed entry condition.

## 4. Force transporter entries into the prime field

We describe a fixed collection of tensors associated with one based $K$-space $X=K^D$. An isomorphism preserving this collection will have an arbitrary matrix $G\in\mathrm{GL}_D(K)$ on $X$ initially.

### 4.1 Symmetric multiplication determines the auxiliary actions

Let

$$
S_r(X)=\operatorname{Sym}^r(X),\qquad 1\leq r\leq p,
$$

with its usual monomial basis, and identify $S_1(X)=X$. These are homogeneous pieces of the commutative symmetric algebra. Their dimensions are

$$
\dim S_r(X)=\binom{D+r-1}{r}.
$$

Include the bilinear multiplication maps

$$
\mu_r:X\times S_r(X)\longrightarrow S_{r+1}(X),
\qquad (v,m)\longmapsto vm,
\quad 1\leq r<p.
\tag{5}
$$

All their monomial-basis structure constants are zero or one.

Let $H_r$ be the unknown isomorphism matrix on $S_r(X)$, with $H_1=G$. Preservation of (5) says

$$
H_{r+1}(vm)=G(v)H_r(m).
\tag{6}
$$

Inductively, this forces

$$
H_r=\operatorname{Sym}^r(G).
\tag{7}
$$

To see uniqueness, every degree-$(r+1)$ basis monomial is a product of a basis vector and a degree-$r$ monomial. Equation (6) determines its image, and the induced symmetric-algebra map satisfies that equation. This argument uses neither polarization nor division by a factorial, so it remains valid in characteristic $p$.

When $r=1$, the two inputs of $\mu_1$ are the same sort $X$, so both use the same matrix $G$. This repeated occurrence is permitted by the compilation theorem.

### 4.2 A linear inclusion records Frobenius on matrices

Introduce a separate based space $X'=K^D$, with basis $e'_1,\ldots,e'_D$. Include the $K$-linear map

$$
\iota:X'\longrightarrow S_p(X),\qquad
\iota(e'_j)=e_j^p.
\tag{8}
$$

This is a linear map specified on a basis. Its definition does not assert that the function $v\mapsto v^p$ is $K$-linear.

Write $G'$ for the unknown matrix on $X'$. From (7), preservation of (8) requires

$$
\operatorname{Sym}^p(G)\,\iota=\iota G'.
$$

The pure-power inclusion is the classical Frobenius construction; see [BMT, Section 3.2.2]. In characteristic $p$,

$$
\operatorname{Sym}^p(G)(e_j^p)
 =\left(\sum_iG_{ij}e_i\right)^p
 =\sum_iG_{ij}^{\,p}e_i^p.
$$

Since the monomials $e_i^p$ are independent, this equation is equivalent to

$$
G'=G^{[p]},
\tag{9}
$$

where the brackets denote entrywise $p$-th powers.

### 4.3 An identity link enforces prime-field entries

Also include the linear map

$$
\eta:X'\longrightarrow X,\qquad \eta(e'_j)=e_j.
\tag{10}
$$

Its preservation requires $G\eta=\eta G'$, hence $G=G'$. Together with (9), this gives

$$
G^{[p]}=G.
\tag{11}
$$

The roots of $z^p-z$ in any characteristic-$p$ field are exactly the $p$ elements of its prime field: these already give $p$ distinct roots of a degree-$p$ polynomial. Therefore (11) says every entry of $G$ lies in $\mathbb F_p$. Since its determinant is nonzero in $K$, it is nonzero in $\mathbb F_p$, and

$$
G\in\mathrm{GL}_D(\mathbb F_p).
$$

Conversely every such matrix extends through the collection: take $H_r=\operatorname{Sym}^r(G)$ and $G'=G$. These matrices are invertible, preserve all multiplication maps, and satisfy both (8) and (10).

We have proved an exact characterization: the matrices permitted on $X$ by this tensor collection are precisely $\mathrm{GL}_D(\mathbb F_p)$.

## 5. The complete system and both correctness directions

For the input tensor $T$, form a tensor system $\mathcal E(T)$ over $K$ consisting of:

1. The expanded source map $\widetilde\beta_T$.
2. The three multiplication endomorphisms $M_1,M_2,M_3$.
3. For each of its three mode spaces, all maps (5), (8) and (10).

Everything except $\widetilde\beta_T$ is fixed by the source presentation, the ordered dimensions and $p$.

**Soundness.** Suppose $\mathcal E(T)$ and $\mathcal E(S)$ are isomorphic over $K$. Section 4 forces their three base-mode matrices to have entries in $\mathbb F_p$. Preservation of $M_i$ forces them to commute with source multiplication by $\theta$. By the centralizer lemma, they are exactly invertible $F$-linear maps on the original source spaces.

Preservation of the expanded bilinear map is then (4), expressed in prime-field coordinates. Its entries lie in $\mathbb F_p$, so equality over $K$ is equality over the prime field and hence equality of the original $F$-bilinear maps. Section 3 converts this into (1). Thus no new isomorphism of the original tensors is introduced.

**Completeness.** Suppose (1) holds over $F$. Obtain $P,Q,R$ from Section 3 and write their restrictions as prime-field matrices. They commute with the corresponding $M_i$ and preserve the expanded bilinear map. Every prime-field matrix is fixed by entrywise $p$-Frobenius. Extend it to each symmetric power and to its companion space as in Section 4. All fixed maps are preserved, so these matrices give an isomorphism $\mathcal E(T)\cong\mathcal E(S)$ over $K$.

Consequently

$$
T\cong_F S
\quad\Longleftrightarrow\quad
\mathcal E(T)\cong_K\mathcal E(S).
\tag{12}
$$

No conciseness, nonzero-rank, connected-stabilizer or genericity assumption occurred in this proof.

## 6. Compilation and polynomial complexity

For each base mode there are $p$ symmetric-power sorts, including its base space, and one companion sort. The full signature therefore has

$$
3p+3\ \text{space sorts}.
$$

Its tensor count is one expanded bilinear map, three source multiplication operators, and $p-1$ multiplication maps plus two links per mode:

$$
1+3+3((p-1)+2)=3p+7.
$$

Every slot has tensor order at most three. For fixed $p$ this is one fixed signature, independent of $s,t,a,b,c$. Apply the published compilation theorem to $\mathcal E(T)$ and $\mathcal E(S)$. It outputs ordinary three-tensors $\widehat T,\widehat S$ over $K$ satisfying

$$
\widehat T\cong_K\widehat S
\quad\Longleftrightarrow\quad
T\cong_F S.
$$

For a mode of dimension $D$, its supporting dimension, including the companion, is

$$
\sum_{r=1}^p\binom{D+r-1}{r}+D
 =\binom{D+p}{p}-1+D.
$$

Put

$$
B=\sum_{i=1}^3\left(\binom{D_i+p}{p}-1+D_i\right).
$$

The explicitly written system has at most $O_p(B^3)$ scalar positions. In particular the source expansion has $D_1D_2D_3=s^3abc$ coefficients, the source operators are explicit matrices, and all symmetric multiplication and link entries are computed directly from monomial exponents. These computations are deterministic polynomial work in their written size.

The FGS construction has a possible exponential dependence on the number of partition parts [FGS, Remark 1.1]. Here those counts depend only on the fixed signature and therefore only on $p$. They do not grow with the source field degree or the mode dimensions. Thus compilation has a polynomial bound depending on $p$.

At fixed $p$, each $\binom{D+p}{p}$ is polynomial in $D$. Writing prime-field coefficients as elements of the supplied target field adds polynomial cost in $t$. The total construction time and output length are therefore polynomial in the original dense input and the supplied field presentations, uniformly in $s,t$ for that fixed $p$.

This proves (2). No search oracle or target-TI decision call is used by the reduction itself: it writes one target instance pair.

**Formats and empty modes.** Different ordered source formats give a fixed NO pair, such as the one-dimensional tensors $(0)$ and $(1)$. If matching formats have any zero mode, every tensor of that format is zero, so output a fixed YES pair before allocating auxiliary spaces. This also handles large unused dimensions written compactly. Otherwise all mode dimensions are positive and are bounded by the dense input size. Zero tensors in positive formats and arbitrary nonconcise tensors are already covered by (12).

## 7. Why naive scalar extension is insufficient

Over $\mathbb F_2$, compare the multiplication maps of $\mathbb F_4$ and $\mathbb F_2\times\mathbb F_2$. With $\omega^2+\omega+1=0$, the two output-coordinate slices of the first map are

$$
A_0=\begin{pmatrix}1&0\\0&1\end{pmatrix},\qquad
A_1=\begin{pmatrix}0&1\\1&1\end{pmatrix}.
$$

Every nonzero prime-field combination of $A_0,A_1$ has rank two. The product-algebra map has coordinate slices $E_{11},E_{22}$, including rank-one slices. Invertible input changes preserve matrix ranks, and an invertible output change preserves the slice space, so these tensors are not isomorphic over $\mathbb F_2$.

Over $\mathbb F_4$, the invertible evaluation matrix

$$
C=\begin{pmatrix}1&\omega\\1&\omega^2\end{pmatrix}
$$

identifies the two multiplication maps:

$$
C\beta_{\mathbb F_4}(x,y)
 =\beta_{\mathbb F_2\times\mathbb F_2}(Cx,Cy).
$$

For each row this follows by evaluating the polynomial representative at one of the two roots of $z^2+z+1$. Its determinant is $\omega^2-\omega=1$. Thus extending the original tensors can merge source orbits.

Our reduction extends a larger, different tensor system. Its extra maps force every base-mode matrix back into the prime field, excluding this spurious extension transporter.

## 8. Scope and attribution

The conclusion concerns equality of polynomial-time TI classes for fixed characteristic. It does not supply a polynomial-time algorithm for those problems. It does not establish reductions across different characteristics or between finite fields and $\mathbb Q$. The symmetric powers and compilation constants also do not give a uniform polynomial bound in $\log p$ when $p$ varies.

The proof separates two ingredients. Restriction of scalars with multiplication markers already gives a direct route from a finite extension to its prime field using the published compiler. The reverse comparison is supplied by the prime-field-entry construction in Section 4; one can also apply that construction after the restriction-of-scalars reduction. The combined form above makes its size and all transporter constraints explicit.

The symmetric-algebra Frobenius identity, scalar-centralizer argument, and compilation theorem are established mathematics. Possible novelty lies in the explicit field-comparison assembly and its complexity accounting. A bounded literature search did not establish publication priority; the note makes no claim to be the first discovery. Its relationship to the named open question follows from its precise theorem, independently of that priority question.

The exposition is authored for the MathProofs project with AI assistance. It invokes published mathematical results and redistributes no upstream software or Lean source. The compiler and the classical ingredients are credited below.

## References

**[GQ]** Joshua A. Grochow and Youming Qiao. *On the Complexity of Isomorphism Problems for Tensors, Groups, and Polynomials I: Tensor Isomorphism-Completeness*. SIAM Journal on Computing 52(2), 568–617 (2023). Theorem 7.3 and Open Question 7.6. [Published article](https://doi.org/10.1137/21M1441110); [full journal text](https://epubs.siam.org/eprint/VA7M2DT6DFQMVDVWIBBN/full). The [arXiv full version](https://arxiv.org/abs/1907.00309) numbers the field-comparison question 10.6.

**[FGS]** Vyacheslav Futorny, Joshua A. Grochow and Vladimir V. Sergeichuk. *Wildness for tensors*. Linear Algebra and its Applications 566, 212–244 (2019). Theorem 1.1, Remark 1.1, and the mixed-variance tensor-system definitions. [DOI](https://doi.org/10.1016/j.laa.2018.12.022); [arXiv version](https://arxiv.org/abs/1810.09219).

**[BMT]** Lawrence Breen, Roman Mikhailov and Antoine Touzé. *Derived functors of the divided power functors*. Geometry & Topology 20, 257–352 (2016). Section 3.2.2, pp. 267–268, discusses the pure-power Frobenius inclusion into a symmetric power. [DOI](https://doi.org/10.2140/gt.2016.20.257); [publisher PDF](https://msp.org/gt/2016/20-1/gt-v20-n1-p04-p.pdf).
