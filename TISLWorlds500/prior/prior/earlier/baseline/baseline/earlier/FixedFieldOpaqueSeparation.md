# A fixed-field opaque-query separation with an explicit-input algorithm

Ordinary TI and determinant-one TI here both use $\mathbb F_3$. There are fixed-field tensor families for which an opaque ordinary-isomorphism oracle needs exponentially many queries to recover the determinant-one answer, even though the same promised family is decidable in polynomial time from the coefficients. Thus this kind of separation is compatible with a positive explicit-input algorithm on the very same tensors.

## Oracle and theorem

The oracle receives opaque handles for two tensors with mode dimensions $(2m,12m,12m)$ over $\mathbb F_3$. It gives ordinary isomorphism decisions, exact transporter counts, and an unpinned ordinary witness that may be any valid witness. It also answers ordinary existence and exact counts under any list of exact full-vector pins in the first mode, membership of a fully specified ordinary transporter, and the rank of an individual single-mode contraction. It permits self-comparisons, reversing a comparison, and comparison after specified invertible maps on the handles. The algorithm is given a relative ordinary witness as well. It does not read hidden coefficients or make tensor constructions depending on them. In particular the oracle does not return witnesses for pinned comparisons.

Take $m$ an arbitrarily large odd multiple of three. There is a promise family in this model with deterministic exact and bounded-error randomized query complexity
$$
\Omega\!\left(\frac{3^{m/2}}m\right)
$$
for deciding whether an $\mathbb F_3$ determinant-one transporter exists in all three modes. The field, dimensions, unpinned ordinary transporter count, and public witness are the same for the two promise answers. In the explicit-input version the family is polynomial-time decidable by a cross-ratio square test.

## Building the two pencils and restricting scalars

Put $E=\mathbb F_{3^m}$, $K=\mathbb F_{27}\subset E$, and $q=|E|$. Fix a public tower representation and a public $b\in K\setminus\mathbb F_3$. Choose $c\in K^\times$ so the following three root pairs have no overlaps within either list:
$$
\begin{array}{c|ccc}
+ & \{1,-1\}&\{b,-b\}&\{c,-c\}\\
- & \{1,-1\}&\{b,-1/b\}&\{c,-1/c\}.
\end{array}
$$
The exclusions on $c$ affect fewer than a dozen elements of $K$. Each pair gets rank-drop multiplicity $1,2,3$ in the displayed order, so each line is a scalar block of that dimension in a diagonal $12$ by $12$ pencil. Positive pairs are swapped by $z\mapsto-z$ and negative pairs by $z\mapsto-1/z$. The corresponding representatives over $K$ are
$$
S_+^0=\operatorname{diag}(1,-1),\qquad S_-^0=\begin{pmatrix}0&-1\\1&0\end{pmatrix}.
$$
Since $m$ is odd, $-1$ is a nonsquare in both $K$ and $E$.

The ordered cross-ratios of the first two colored pairs, taken with the displayed representatives, are
$$
\chi_+=\left(\frac{1-b}{1+b}\right)^2,\qquad
\chi_-=-\left(\frac{1-b}{1+b}\right)^2.
$$
They are nonzero and belong to $K\setminus\mathbb F_3$. In fact the square expression can equal neither $-1$ nor $1$, the latter because $b\ne0$ and the characteristic is not two. Both cross-ratios therefore differ from their inverses. A projective map preserving the two colored pairs cannot swap just one, since that would invert the cross-ratio. Fixing both pairs pointwise forces the identity. Swapping both is determined by three point images and is realized by the corresponding displayed involution. It also preserves the third pair. Thus the projective label group over $E$ has precisely these two elements in each case.

Choose a public $\alpha\in K$ outside the union of all the roots and the fixed points of both involutions. The lists and fixed points exclude at most fourteen rational elements. The map $Q:z\mapsto1/(z-\alpha)$ sends $\alpha$ to infinity. Apply it to the roots and normalize the $x$-coefficient of each scalar block to one by invertible block scalings. The resulting pencils $A^0_+,A^0_-$ have coefficients in $K$, $x$-coefficient $I_{12}$, and six distinct finite roots. Their nonidentity projective labels $S_\pm=QS_\pm^0Q^{-1}$ have a nonzero lower-left entry since neither fixes infinity.

For the hidden parameter $a\in E$ let $U_a=\left(\begin{smallmatrix}1&a\\0&1\end{smallmatrix}\right)$ and define
$$
A_{\pm,a}(w)=A^0_\pm(U_{-a}w),\qquad
B_{\pm,a}(w)=A_{\pm,a}(W^{-1}w),\quad W=\operatorname{diag}(1,-1).
$$
View the bimap $A(w)v$ as an $\mathbb F_3$-bilinear map $E^2\times E^{12}\to E^{12}$ in the public coordinate bases. The same applies to $B$. Transporters satisfy $B(Pw)G=HA(w)$ as $\mathbb F_3$-linear maps in the three roles. The public transporter is $(W,I,I)$.

## All underlying $\mathbb F_3$ transporters are accounted for

For these pencils the centroid as an $\mathbb F_3$-bimap consists exactly of the simultaneous scalar action of $E$. To see this, let $(L,R,C)$ act in its three roles and satisfy $A(Lw)v=A(w)R(v)=C(A(w)v)$. At $w=e_1$ the last equality gives $R=C$, and at $w=se_1$ it shows these maps commute with every multiplication by $s\in E$. The first equality and conciseness of the pencil then show $L$ is $E$-linear. Write $L$ as a $2$ by $2$ matrix. If the block roots are $r_i$, substituting $e_1$ gives $R$ equal to the block-scalar map with values $L_{11}-r_i L_{21}$. Substituting $e_2$ gives
$$
L_{12}-r_iL_{22}=-r_i(L_{11}-r_iL_{21}).
$$
A quadratic polynomial vanishing at all six distinct roots is zero, so $L$ is scalar and so are the other two maps. The label-twisted pencil has the same centroid by conjugation.

Each ordinary $\mathbb F_3$ transporter must therefore be semilinear over one common Frobenius automorphism $\sigma$ of $E$ in its three modes. A semilinear label stabilizing a colored root configuration requires $\sigma(\chi_\pm)\in\{\chi_\pm,\chi_\pm^{-1}\}$. Since the restriction to $K$ has order dividing three and $\chi_\pm\notin\mathbb F_3$, this is possible exactly when $\sigma$ fixes $K$. Indeed an order-three action that maps a nonzero element to its inverse would fix it after squaring the action and hence would fix it already. For a $\sigma$ fixing $K$, coordinatewise $\sigma$ is an automorphism of $A_\pm^0$ and its $\mathbb F_3$-linear determinant is one in each mode. Its order divides odd $m$.

At $A_\pm^0$, the $E$-linear elements over the identity projective class form the same subgroup for both signs:
$$
D=\{(\lambda I,X,\lambda X):\lambda\in E^\times,\
 X\in\textstyle\prod_{i=1}^6\mathrm{GL}_{m_i}(E)\},\quad
 (m_i)=(1,1,2,2,3,3).
$$
This follows from the identity $x$-slice and the six distinct diagonal scalars of the $y$-slice. The other projective class is one coset of $D$. A label preserving the marked root pairs lifts by the block permutation and scalar rescalings of the linear factors. For the original positive involution $S_+^0$, a simultaneous pair swap $R$ gives $(S_+^0,R,R)$, with $\det_E R=(-1)^{1+2+3}=1$. Conjugating to the normalized pencil and then by $U_a$ leaves the determinants unchanged.

Consequently all labels of $A_{\pm,a}$ are of the form
$$
\lambda U_a S U_{-a^\sigma}\sigma,\qquad
 S\in\{I,S_\pm\},\quad \sigma\in\operatorname{Gal}(E/K),\quad \lambda\ne0.
\tag{1}
$$
For $S=I$ the two other modes are $X\sigma$ and $\lambda X\sigma$ with $X$ as in $D$. For every label representative their number is the same block-group order, also when $S=S_\pm$. The full ordinary count for $(A,B)$ is $2|\operatorname{Gal}(E/K)||D|$ for both signs. In the positive case the involution's lift has $\mathbb F_3$ determinants $(-1,1,1)$, since $\operatorname{Nm}_{E/\mathbb F_3}(-1)=-1$. It repairs the public transporter. In the negative case each label determinant on the source, including every semilinear component, has positive $\mathbb F_3$ sign: the $E$-linear label determinants are squares and the coordinatewise Frobenius has positive determinant. The public label $W$ therefore makes every relative label negative. This verifies the two promise outcomes.

## Exceptional hidden shifts per query

Pull reversed, self, or explicitly transformed handle queries back to $A_{\pm,a}$ using the known maps. Conjugating handles transports any vector pin to an exact vector pin. It also preserves the rank of a contraction after pulling back its contracting covector. Unpinned answers agree and the adversarial witness can always be the public one after conversion.

For a nonzero pin on an $E$-projective line, consider the corresponding projective image condition in (1). For $S=I$ and $\sigma=\mathrm{id}$, the answer comes from $D$ and is independent of the shift. For $S=I$ and $\sigma\ne\mathrm{id}$, on a finite source direction $z$ the image is $z^\sigma+a-a^\sigma$. A finite target direction fixes one value of the linearized map $a-a^\sigma$. Every fiber has size at most $3^{\gcd(s,m)}\le\sqrt q$ for $\sigma:x\mapsto x^{3^s}$ nonidentity. An infinite target is impossible in this case. For pins with all nonzero inputs and outputs in the infinity line, every affine label sends $(x,0)$ to $(\lambda x^\sigma,0)$ independent of $a$. Thus the exact count from the affine labels is common to both signs and every shift on these queries. The nonaffine labels never map infinity to itself.

For $S=S_\pm$, if the source and target directions $z,w$ are finite, their image condition becomes
$$
w-a=S\big((z-a)^\sigma\big).
$$
With $x=z-a$ this is $x^\sigma=M(x)$ for a projective linear fractional function $M$, obtained by composing $S^{-1}$ with a translation. Its lower-left entry is nonzero. For $\sigma=\mathrm{id}$ this gives a nonzero quadratic equation. For other $\sigma$, clearing the denominator gives a nonzero polynomial equation of degree at most $3^s+1$. Applying $\sigma^{-1}$ to the original equation and applying the resulting inverse fractional map gives instead a nonzero polynomial equation of degree at most $3^{m-s}+1$. Both fractional maps are nonaffine. The exceptional shifts therefore number at most $3^{\min(s,m-s)}+1\le\sqrt q+1$. If just one direction is infinity, the equation fixes one value of $a$ or of $a^\sigma$, so there is at most one shift. If both are infinity there are none. These are necessary image conditions, so adding exact scalar constraints on pins cannot increase the exceptions.

For a pin list with at least one finite input or mismatched infinity condition, use only $D$ in the reference answer. The actual count or existence can differ from this answer on at most
$$
b_m=2m(\sqrt q+1)+6
$$
shifts for each sign, by the preceding bounds and the at most $m$ automorphisms $\sigma$. If every nonzero pin is infinity-to-infinity, use the common affine answer. Pins with incompatible zero constraints are immediately rejected. Fully specified membership calls can use only $D$ for the reference. Outside it, imposing the tested matrix's action on a single nonzero finite vector gives the same exceptional bound, since any other actual label must lie in one of the hidden affine or nonaffine classes.

An $\mathbb F_3$ slice rank on the label mode is its $E$ rank multiplied by $m$. The generic answer can differ only on at most six shifts, one per translated root. For the $\mathbb F_3$ contraction rank on either of the other modes, a fixed vector's nonzero block supports determine whether it has rank $0,m,$ or $2m$. In the output mode, express the contracting functional as an $E$ row followed by the trace to $\mathbb F_3$. The trace pairing is nondegenerate, so the same block-support count gives the rank. In the input-column mode it follows directly from the rank of the $E$-linear map on $E^2$. Distinct roots in distinct blocks make these answers independent of the sign and shift.

For deterministic algorithms, simulate the reference transcript. A length-$T$ path rules out at most $b_m T$ shifts for each sign. If $b_m T<q$, both an affirmative and a negative instance follow the path. For randomized algorithms condition on the algorithm's coins, and sample each sign's shift uniformly. Each real answer distribution can differ from the common transcript with probability at most $b_m T/q$. The difference in acceptance probabilities is at most $2b_m T/q$. Worst-case error $\epsilon<1/2$ would require a gap at least $1-2\epsilon$, so $T\ge(1-2\epsilon)q/(2b_m)$. Both bounds are exponential in $m$.

## The explicit-input comparison and scope

With the written coefficient table, read the $y$-slice on the first coordinate of each of the four blocks of sizes $1,1,2,2$. The public field basis identifies their translated roots in $E$. Compute their cross-ratio and test its square class by one powering. Taking a different order within a pair inverts the cross-ratio, which preserves its square class. The positive cross-ratio is a square and the negative one a nonsquare. This determines the answer in polynomial bit time on the promised written instances.

The theorem is about a specified restricted oracle. It shows an exponential separation over the fixed ground field, together with a polynomial algorithm on exactly the same promise family once the coefficients are accessible. It gives no lower bound against an explicit-input many-one reduction, and no contradiction with positive algorithms that build new comparison instances from the data. The unrestricted question remains [Chen, Grochow, Qiao, Tang and Zhang, Open Question 1.9](https://arxiv.org/html/2306.03135v2#S1.SS5). The proof uses no computational complexity conjecture.
