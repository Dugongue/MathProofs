# Multiplication and Frobenius tensor transport

The Lean source contains 50 universal statements. They cover weighted binary multiplications, linear-functional radicals, arbitrary multilinear order, shared and separate tensor transports, and prescribed determinant data. The theorem names record the scope of each result. [Lean source](C.lean)

## Determinant constraints for multiplication tensors

Let $A,B$ be finite-dimensional unital associative algebras over a field, and choose a reference linear equivalence $F:A\to B$. Measure the determinant of $T:A\to B$ relative to $F$. If $Z(xy)=X(x)Y(y)$, an algebra equivalence $\sigma$ and units $a,b\in B^\times$ give
$$
X(x)=a\sigma(x),\qquad Y(x)=\sigma(x)b,\qquad Z(x)=a\sigma(x)b .
$$
The relative determinant triple is exactly $(N_L(a)d,N_R(b)d,N_L(a)N_R(b)d)$, where $N_L,N_R$ are determinants of multiplication on the two sides and $d=\det_F(\sigma)$. In particular, $d=\det_F(X)\det_F(Y)/\det_F(Z)$. All three transports can have determinant one exactly when an algebra equivalence of relative determinant one exists. This concerns multiplication tensors of unital associative algebras.

The same unit recovery yields a normal form for three independent inputs of the ordered product $xyz$. The middle two unit factors cancel. When two input maps coincide for the binary product, the common unit multiplier must centralize the transported algebra. The weighted product $xay$ has an identity exactly when $a$ is a unit. Its two radicals and principal slice images transport under independent changes of basis.

## Reconstructing a Frobenius algebra across degrees

For a commutative algebra over a commutative ring, let $\phi$ be a linear functional whose multiplication pairing separates points. A common-basis transport preserving the $r$-linear product form $\phi(x_1\cdots x_r)$ for any $r\ge 3$ has the form $T=u\sigma$, with a unit $u$ and a unital algebra equivalence $\sigma$. The transported functional carries the multiplier $u^r$. The proof first fills $r-3$ inputs with the unit and uses separation on the source to show that the resulting target pairing still separates. This avoids an invertibility assumption on the target's reference contraction.

Once the same $T$ transports the forms in degree $r$, it transports the forms in degree $r+k$ exactly when $T(1)^k=1$. Two consecutive degrees force the transport itself to preserve the algebra and both functionals. Over a field, the separate three-leg theorem permits different linear changes of basis for the three copies. When both multiplication pairings separate points and the codomain is finite-dimensional, all three transports recover a single algebra equivalence. Each differs from it by multiplication by a unit, and the product of those three units specifies the functional change.

## Radicals and partial observations

For each functional $\phi$, the elements $a$ with $\phi(ax)=0$ for every $x$ form the largest ideal on which $\phi$ vanishes. This ideal controls perturbations, quotient nilpotence, and the transport of individual input radicals. Multiplying the observable weight by $a$ pulls the radical back under multiplication by $a$. If several weights generate the unit ideal, the intersection of the radicals of their observations recovers the original radical. Coincidence of trilinear probes taken over a prescribed ideal is characterized by one ideal-containment condition. With two prescribed leg transports, the third leg is determined modulo the radical. When this radical vanishes the third leg is unique.

The unital binary isotopy normalization is classical, as is the field-level analysis of higher-degree trace forms. Other antecedents concern tensor isomorphism and multilinear centres. These references motivate the scope distinctions above. [Albert](https://doi.org/10.2307/1968960) · [Harrison–Pareigis](https://epub.ub.uni-muenchen.de/7099/1/7099.pdf) · [Grochow–Qiao](https://arxiv.org/abs/1907.00309) · [Huang–Lu–Ye–Zhang](https://arxiv.org/abs/2110.07915)

The frozen third queue nominated numeric matches before any names were read. Positions 5 and 12 included the determinant-rank producer 13892, positions 17 and 71 included quotient rank and kernel producers 252477 and 363773, position 54 included scalar cancellation producer 35002, and positions 6 and 164 included root-power handles 79498 and 235231. These motifs suggested the determinant correction, radical tests and period equations. The mathematical statements were chosen and proved after the reveal. [Frozen queue](queues/worker-3.json)
