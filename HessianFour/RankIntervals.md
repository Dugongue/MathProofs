# Rank intervals inside one fixed-Hessian fiber

Let $k$ be algebraically closed of characteristic different from $2,3$, let $d\ge1$, and set $N=2d+2$ and $M=\binom{d+2}{3}$. Consider the affine family of cubics on the same $N$ coordinates
$$
 f_C(r,u,v,z)=3r^2z+6r\sum_{i=1}^d u_i v_i+C(u),\qquad
 C\in\operatorname{Sym}^3((k^d)^*).
$$
Use the symmetric polarization to view each cubic as an ordinary three-tensor as well. Write $R,\underline R$ for ordinary tensor rank and border rank, and $R_s,\underline R_s$ for Waring rank and border Waring rank. The family has one Hessian determinant and a common determinant-one normal form for every invertible slice. This holds coefficientwise throughout the affine family.

**Theorem.** Each of the four ranks takes every integer in the indicated interval in this single family. The four parameters can use different members of the family.
$$
\begin{array}{c|c}
\text{rank} & \text{guaranteed interval}\\ \hline
\underline R & [N,\max(N,\lceil M/(3d-2)\rceil)]\\
\underline R_s & [N,\max(N,\lceil M/d\rceil)]\\
R & [2N-1,\max(2N-1,\lceil M/(3d-2)\rceil)]\\
R_s & [2N-1,\max(2N-1,\lceil M/d\rceil)] .
\end{array}
$$
In each row the left endpoint is the exact minimum. In particular the intervals have quadratic width as $N$ grows. The proof also gives a rank comparison on the linearly sized tensor-isomorphism-complete tagged subfamily and a rank interval with a fixed lower-precision tensor over finite local rings of odd residue characteristic different from $3$.

## 1. Common slice data for arbitrary cubic perturbations

The construction uses the Frobenius carrier from the fixed-Hessian theorem. Let $B$ have the underlying space $k1\oplus V\oplus V^*\oplus kz$, with $V=k^d$. If $c$ is the symmetric trilinear polarization of $C$, use the products $u u'=c(u,u',-)\in V^*$, $u\ell=\ell(u)z$, and their transposes. Let other products in the nonunit part be zero. The product is associative because the only potentially nonzero triple product there occurs on three arguments in $V$, and both bracketings equal $c(u,u',u'')z$. The functional $\lambda$ reads the coefficient of $z$. Expanding $\lambda(x^3)$ gives exactly $f_C$. The fixed perfect pairing $G(x,y)=\lambda(xy)$ pairs $1,z$ and the two dual summands. Under this pairing the normalized slice at $x$ is $L_x$, left multiplication by $x$.

For $x=r1+u+v+a z$, in the displayed order $L_x$ is triangular with diagonal $r$. Hence the slice determinant is $\det(G)r^N$, and the Hessian determinant of $f_C$ is $6^N\det(G)r^N$. In the polynomial ring localized at $r$, remove the extra symmetric $V$-by-$V$ block $D$ of the slice by adding to each vector in $V$ its image under the shear $-D/(2r):V\to V^*$. The pairing between $V$ and $V^*$ is $r$ times evaluation and the pairing on $V^*$ vanishes. The two cross terms cancel $D$. Next subtract from each middle vector its pairing with $1$ times $r^{-1}z$. These two determinant-one shears fix $1,z$. They produce $r$ times the middle hyperbolic pairing and a block $\left(\begin{smallmatrix}a&r\\r&0\end{smallmatrix}\right)$ on $1,z$. This is the same normal form for the entire family. It is defined by polynomials in the original coordinates and $r^{-1}$, and commutes with any scalar extension. The factor $1/2$ permits arbitrary symmetric $D$ here. The starting paper's zero-diagonal shears are needed when $2$ is not invertible. [Fixed-Hessian construction](https://github.com/Dugongue/MathProofs/blob/main/SymmetricFinalFour/Tensor.md)

Every normalized slice other than the unit basis slice is strictly triangular. Thus all matrix substitutions in the normalized pencil also have the same determinant polynomial: after arranging the tensor-product basis in carrier blocks, a substitution $\sum_i Y_i\otimes L_{e_i}$ has $N$ diagonal blocks $Y_0$, with $e_0=1$. Its determinant is $\det(Y_0)^N$. The matrices $Y_i$ may be noncommuting. These identities also persist along the single-cube steps used below.

## 2. The exact minima

Every member has border rank at least $N$, since its unit slice has matrix rank $N$ and matrix rank at most $b$ is a closed condition on each slice of a border-rank-$b$ tensor.

The ordinary rank has the stronger lower bound $2N-1$ for every member. Suppose the tensor is a sum of $b$ pure tensors. Their first-slot covectors span the dual of the first mode, since the perfect unit pairing makes the first flattening injective. Choose a basis among these covectors. The augmentation $r$ is a nonzero linear combination of that basis, so some basis-dual vector $x$ has $r(x)\ne0$. At $x$, at least $N-1$ chosen summands vanish. Its slice is invertible by Section 1, so $b-(N-1)\ge N$. This is the substitution argument specialized to the common invertible-slice chart. Waring rank is at least ordinary rank. [Gharahi–Lysikov on the substitution bound for persistent tensors](https://doi.org/10.22331/q-2024-01-31-1238)

At $C=0$, diagonalize the middle quadratic $2\sum_i u_i v_i$, which is nondegenerate. Write it as $\sum_{j=1}^{m} x_j^2$, where $m=N-2$. Each $3r x_j^2$ is $((r+x_j)^3+(r-x_j)^3)/2-r^3$. Collecting the last terms leaves $3r^2(z-(m/3)r)$, which is a sum of three weighted cubes by
$$
 3r^2 w=\tfrac12\big((w+r)^3+(w-r)^3-2w^3\big).
$$
Thus $R(f_0)=R_s(f_0)=2m+3=2N-1$. We give a degeneration for the two border minima as well, to make the exact value independent of any smoothability characterization. Choose $a_0\ne0,-m$ and use $m+1$ linear forms $\ell_i$ with weights $\lambda_i$ given initially by $\ell_j=x_j,\lambda_j=1$ for $j\le m$ and $\ell_{m+1}=-a_0^{-1}\sum_j x_j,\lambda_{m+1}=a_0$. Their first weighted moment vanishes and their second is nondegenerate, since $I+a_0^{-1}\boldsymbol 1\boldsymbol 1^{\mathsf T}$ has determinant $1+m/a_0\ne0$. After a change of middle coordinates the second moment is $\sum x_j^2$. Put $c_0=m+a_0\ne0$. The expression
$$
 h(\varepsilon)=\varepsilon^{-2}
 \left(\sum_{i=1}^{m+1}\lambda_i(r+\varepsilon\ell_i)^3
       -c_0(r-\varepsilon^2 z/c_0)^3\right)
$$
is regular at zero by the constant and first moment cancellations. The special value is $3r\sum x_j^2+3r^2z=f_0$. At nonzero $\varepsilon$ it is a sum of at most $m+2=N$ weighted cubes. Scalars can be absorbed by cube roots over $k$. Thus $\underline R(f_0)=\underline R_s(f_0)=N$. The base point is the classical big Coppersmith–Winograd cubic in split coordinates. [Bläser–Lysikov on the associated algebra and its smoothability](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.MFCS.2016.19) · [Carlini–Guo–Ventura on ranks of reducible cubics](https://arxiv.org/abs/1512.04905)

## 3. Quadratic upper endpoints and rank intervals

Restriction to $r=v=z=0$ gives $C(u)$. Ordinary and symmetric border ranks do not increase under this restriction, since restriction is a linear map and sends a rank-one summand to a rank-one summand or zero. On $d$ coordinates, the variety of ordinary tensors of border rank at most $b$ has dimension at most $b(3d-2)$. Indeed the cone of pure tensors has dimension $3d-2$, and take the closure of the image of the sum map from $b$ copies. For the symmetric version the cone of cubes has dimension $d$, giving dimension at most $bd$. The whole space of symmetric cubics has dimension $M$. Therefore a generic $C$ has ordinary border rank at least $\lceil M/(3d-2)\rceil$ and border Waring rank at least $\lceil M/d\rceil$. These lower bounds carry to $f_C$, including for exact ranks. The two dimension bounds concern closures of secants and require no assertion about generic identifiability or an equality of ordinary and symmetric ranks.

Cubes span the space of cubics because $2,3$ are invertible, by the polarization identity. Choose a decomposition of one such high-rank $C$ as a sum of scalar multiples of cubes and take its partial sums starting at zero. Every step changes $f_C$ by a rank-one tensor or its negative. Subadditivity for all four ranks, used in both directions, gives a change of at most one. For the border variants subadditivity follows by applying the sum map to the closures of the two rank loci. Each integer between the starting value and an attained higher value therefore occurs. This proves the four intervals. The proof produces existence, with a path from any chosen high-rank cubic; it does not require a deterministic procedure to find a generic high-rank point.

There is also a uniform upper bound of order $N^2$ for the family. Write $C=\sum_i u_i Q_i$ with quadratic forms $Q_i$, diagonalize each $Q_i$ into at most $d$ squares, and express each linear-times-square monomial as at most three weighted cubes by the binary calculation above. Thus $R_s(f_C)\le 2N-1+3d^2$, which bounds all four ranks.

## 4. Quantitative rank transfer on the marked TI family

Now take $C=C_t$ with the three ordered roles and hyperbolic marker blocks of the fully symmetric TI reduction. Let $d=\dim L$ there, and use its field case with $N=2d+2$. In the symmetric polarization of $f_{C_t}$, restrict the three slots to the three respective source role subspaces. The result is exactly the ordinary tensor $t$, so
$$
 \underline R(t)\le \underline R(f_{C_t}),\qquad R(t)\le R(f_{C_t}).
$$
For the upper bounds, each simple summand of $t$ contributes a scalar multiple of the product of three linear forms in the cubic $C_t$, which is a sum of four weighted cubes by polarization. For example $24xyz$ equals
$$
 (x+y+z)^3+(x-y-z)^3+(-x+y-z)^3+(-x-y+z)^3 .
$$
The same transfer is valid for border rank by applying the linear symmetrization map to the secant closure. The marker terms are sums of one such product for each split pair, of which there are $(d-3)/2$ in total. They cost at most $2(d-3)=N-8$ cubes. Add the base-point bounds from Section 2 to obtain
$$
 \underline R_s(f_{C_t})\le 4\underline R(t)+2N-8,\qquad
 R_s(f_{C_t})\le 4R(t)+3N-9.
$$
Taking $t=0$ or a generic balanced tensor gives linear ranks or quadratic ranks, respectively, within the actual TI-hard marked subfamily, in a common format. The generic ordinary border-rank lower bound for $t$ follows from its full tensor-space dimension by the same cone calculation as above. The individual intervals in the theorem concern the whole perturbation family, whose paths of one cube need not keep the role markings fixed. [Starting symmetric tagged reduction](https://github.com/Dugongue/MathProofs/blob/main/FinalDigitFour/Tensor.md)

## 5. Exact rank intervals at fixed lower precision

Let $R_0$ be a fixed finite commutative local ring with nonzero maximal ideal, residue field $k_0$ of cardinality $q$ and characteristic different from $2,3$, and let $s\ne0$ annihilate the maximal ideal. Use the same carrier, place every polarized coefficient of $C$ in $sR_0\simeq k_0$, and allow all $C$ on $d$ variables over $k_0$. There are $q^M$ arrays, because restriction to the $V$ input blocks recovers the socle-valued coefficients. They all reduce to the same array modulo $sR_0$. For a free tensor over $R_0$ use the ordinary rank defined by exact sums of pure tensors.

Every such rank is at least $2N-1$ by reducing to the residue field and applying the proof of Section 2. The unperturbed array attains $2N-1$ over $R_0$. For the upper bound at that point, express each split pair as a difference of squares using $(x+y)^2-(x-y)^2=4xy$; retain the scalar weights in the cube identities. Weighted cubes are pure tensors after absorbing the weight into one factor, so no cube-root operation is needed. There are at most $|R_0|^{3Nb}$ arrays of rank at most $b$, by counting ordered decompositions of length $b$ with zeros allowed. Hence some array has rank at least
$$
 B_{R_0}=\left\lceil\frac{M\log q}{3N\log|R_0|}\right\rceil .
$$
A cube path over the residue field changes an array by $s\lambda\,w^{\otimes3}$ for a lifted covector $w$ and a scalar lift of $\lambda$. This difference is pure. The same unit-step argument shows that **every** integer from $2N-1$ through $\max(2N-1,B_{R_0})$ occurs in one final-digit class, with the common slice normal forms intact. The width is quadratic for each fixed $R_0$.

The zero perturbation and the usual persistent-tensor lower bound have classical precedents. The additional results are the quantitative rank intervals under fixed Hessian and unit-slice data, the rank comparison for the marked isomorphism reduction, and the exact finite-ring interval in a single reduction class. This is a written proof. Publication priority for the exact package remains unconfirmed.

[RankIntervals.py](RankIntervals.py) checks the constant, linear and quadratic coefficients of the border decomposition in 17,408 instances over the fields of orders $5,7$ and the rings $\mathbb Z/25\mathbb Z,\mathbb Z/49\mathbb Z$. [WeightedCube.lean](WeightedCube.lean) independently checks the supporting weighted-cube expansion.
