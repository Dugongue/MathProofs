# A complete projective relation space removes all three signs

Work over $\mathbb F_3$. Use the raw pencil convention and unique invertible alternating multiplier line in [the finite harmonic readout](PfaffianHarmonicReadout.md). The determinant problem has a single ordinary TI reduction on the following raw Pfaffian family. This is a sufficient case of the authors' determinant-one tensor problem. [Chen–Grochow–Qiao–Tang–Zhang, Open Question 1.9](https://arxiv.org/html/2306.03135v2#S1.SS5)

## Theorem

Suppose the source has a nonzero split Pfaffian $p_X=c_X\prod_{i=1}^N\ell_i^{e_i}$ of even degree, with distinct normalized projective factors. Make the following three assumptions.

- The factors span the full label dual $W_X^*$.
- The coordinate functionals $q_i:R_X\to\mathbb F_3$ on the relation space $R_X=\ker(e_i\mapsto\ell_i)$ are nonzero and their projective lines are exactly all the projective lines of $R_X^*$, each once.
- All factor multiplicities $e_i$ have the same parity.

Then the full three-sign comparison $P_3$ reduces in deterministic polynomial time to one ordinary tensor isomorphism instance. Only this source promise is required. The map computes both alternating multipliers, factors, and their relation data before compilation. Shapes and conditions not inherited by the target may cause early rejection.

The exact transfer is to use the Navier–Stokes phase projection to pass from the large primal label coordinates to the dual frequency relation space. On a complete projective frequency set, the two permutation signs of the full finite frequency set and its projective quotient determine the induced sign on the label space. This allows all three signs to be enforced on the small relation space, rather than constructing the exterior algebra of the original axes. [Alpöge–Buckmaster, finite analogue of the vanishing character mean](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorusMeanFacts.lean#L126-L151)

## 1. Two permutation signs on a complete frequency set

For $G\in \operatorname{GL}_t(\mathbb F_3)$, the permutation of all nonzero vectors has sign $\det G$, and its permutation of all projective lines has sign $(\det G)^{t-1}$. Both are characters of the linear group. The elementary transvections have order three, so both signs are one on them. Elementary elimination generates the special linear subgroup by these transvections. Thus it suffices to take $G=\operatorname{diag}(-1,1,\ldots,1)$, also covering dimension one. It exchanges $3^{t-1}$ unordered pairs of nonzero vectors by negating a nonzero first coordinate. On projective lines it fixes the hyperplane of zero first coordinate and the first coordinate line. Each other line has a unique representative $(1,v)$ for $0\ne v\in\mathbb F_3^{t-1}$, and the action is $v\mapsto-v$. Hence the projective action exchanges $(3^{t-1}-1)/2$ pairs, with parity $t-1$ modulo two.

Using the normalized representative of each projective line, write $G$ on those representatives as a permutation followed by line scales. The action on all nonzero vectors permutes blocks of size two, and every block permutation has even sign. A negative scale flips its block. Therefore the product of the line scales is also $\det G$.

## 2. Calibrate both raw sign observables

For each endpoint choose a basis of its relation space $R$ and a consistent deterministic ordering of its factors. In these coordinates let $\eta_i\in\{1,-1\}$ be the scalar expressing the coefficient functional $q_i$ as $\eta_i$ times the normalized representative of its projective line. Define $E=\prod_i\eta_i$. Also let $\pi\in\{1,-1\}$ be the sign of the permutation from the chosen factor order to the lexicographic order of normalized projective representatives in the chosen relation basis.

Let $A:Z=\mathbb F_3^I\to W^*$ send $e_i$ to $\ell_i$. Because the factors span, form an adapted basis $\mathcal B$ of $Z$ starting with the chosen relation basis, followed by lifts under $A$ of the given coordinate basis of $W^*$. Its determinant in the fixed factor order is denoted $\Delta$. All endpoint quantities $E,\pi,\Delta$ are computed by linear algebra and sorting, with no relative isomorphism needed.

Consider any actual raw transporter $(P,Q,C)$. The normalized multiplier equations and even Pfaffian degree give
$$ p_Y(Cz)=\det P\,p_X(z),\qquad
 \det P=(\det B_Y/\det B_X)\det Q . $$
The factor matching $\sigma$ and scales $\lambda_i$ satisfy $\ell_{Y,\sigma(i)}C=\lambda_i\ell_{X,i}$. Define $L:Z_X\to Z_Y$ by $L(e_i)=\lambda_i^{-1}e_{\sigma(i)}$. Its restriction $H:L|_{R_X}$ maps $R_X$ isomorphically to $R_Y$, and $A_Y L=C^{-\mathsf T} A_X$. Let $h=\det H$ in the chosen relation bases.

The corresponding action on the relation duals is $H^{-\mathsf T}q_{X,i}=\lambda_i q_{Y,\sigma(i)}$. Its determinant in the chosen dual coordinates is $h$ because signs over $\mathbb F_3$ are self-inverse. The complete projective condition and Section 1 therefore give
$$
 \prod_i\lambda_i = (E_X/E_Y)h,\qquad
 \operatorname{sgn}(\sigma)=\pi_X\pi_Y h^{t-1}.
$$
The first identity compares the chosen endpoint line vectors with normalized representatives before taking the product. The second compares the chosen factor orders with the standard projective order at both endpoints.

Write $\alpha\in\{0,1\}$ for the common parity of the exponents. Pfaffian covariance now yields the first formula below. The determinant of the monomial map $L$ in factor bases is $\operatorname{sgn}(\sigma)\prod_i\lambda_i$. In the adapted bases its matrix is block triangular with diagonal maps $H$ and $C^{-\mathsf T}$. Dividing by the adapted basis ratio and $h$ gives the second formula:
$$
 \det P=(c_Y/c_X)(E_X/E_Y)^\alpha h^\alpha,\qquad
 \det C=(\Delta_X/\Delta_Y)\pi_X\pi_Y(E_X/E_Y)h^{t-1}.
$$
This computes all three requested raw signs from one bit on the actual relation map.

## 3. Compile one ordinary comparison

Find the normalized multiplier and the split factors by the linear equations and deterministic factor recovery in the accompanying proof. Compute all $q_i$ in a chosen relation basis. The projective hypothesis is checked by normalizing each nonzero $q_i$, testing distinctness, and testing $N=(3^t-1)/2$. Check the common parity and full span from the factor list. The endpoint quantities in Section 2 are then explicit. Every source promise and all needed dimensions persist under an ordinary transporter.

Try both signs $h$ in the displayed formulas to determine which are compatible with $\det P=\det Q=\det C=1$. If neither passes return one fixed ordinary NO instance. If both pass the ordinary raw comparison suffices. Otherwise let $h_0$ be the unique permitted sign.

Use the ordinary system with the raw tensor, factor coordinate algebra $A_0=\mathbb F_3^I$, its natural coordinate module $Z$, and the evaluation pairing $Z\times W\to\mathbb F_3$ of [the colored relation tuple proof](PfaffianRelationColors.md). This forces exactly the actual factor permutation and scales. Keep the relation space as a role with its inclusion $R\hookrightarrow Z$. This inclusion forces the map on that role to be $H$. Adjoin its full exterior algebra $\Lambda R$ with multiplication, include the injection of $R$ as the degree-one part, and mark a top wedge of the source relation basis against $h_0$ times the top wedge of the target basis. The product and the included generators force the extension of $H$ as an exterior map. The top mark consequently imposes exactly $\det H=h_0$. Every actual raw transporter of the required sign extends by its forced maps. Any simultaneous system isomorphism supplies a common raw transporter and its calibrated signs.

Since $N=(3^t-1)/2$, the full exterior algebra of $R$ has dimension $2^t\le2N+1$. Its multiplication table and all other tables therefore have polynomial size. The exterior role is marked through ordinary tensors of order at most three. The ordinary tensor-system compiler produces one ordinary tensor comparison. The conclusion concerns all three signs on the same raw witness. [Ordinary tensor-system compiler](https://arxiv.org/html/2306.03135v2#S4)

## 4. Explicit scalar-multiplier examples with no unused labels

Take any even $t\ge4$ and enumerate the $N=(3^t-1)/2$ normalized projective vectors in $\mathbb F_3^t$ as columns of a matrix. Let $R$ be its row space, $W=R^\perp\subseteq\mathbb F_3^N$, and take $\ell_i$ to be the coordinate restrictions to $W$. The coordinate functionals on the relation space are exactly the chosen projective column vectors. A nonzero element of $R$ has support of size $3^{t-1}$, by counting projective directions outside its annihilator hyperplane. Thus there is no relation supported on one or two coordinates. The $\ell_i$ are nonzero and projectively distinct, and they span $W^*$ because $W$ is a subspace of the coefficient space.

Take $D(z)=\operatorname{diag}(\ell_1(z),\ldots,\ell_N(z))$ and
$$ M(z)=\begin{pmatrix}0&D(z)\\-D(z)&B(z)\end{pmatrix} .$$
There are no auxiliary label coordinates. For each adjacent pair $i,i+1$ choose some $\ell_{k(i)}$ outside $\operatorname{span}(\ell_i,\ell_{i+1})$, possible since the factor span has dimension $N-t\ge3$. Set $B_{i,i+1}=\ell_{k(i)}$, reflect with a minus sign, and use zero elsewhere. The Pfaffian is $\pm\prod_i\ell_i$, regardless of $B$. Its degree $N$ is even because $t$ is even. Conciseness of the label mode follows from the span of the factors. The common kernel in a matrix mode is zero since the top block $D(z)$ kills no common nonzero vector and the same then holds for the lower left block. The other mode follows by alternation.

To see that the alternating multiplier line is scalar, let $L=(P,Q;R',S)$ in blocks. The top-left block $D(z)R'$ must be alternating. The independence of each pair of factor lines forces $R'=0$, using its off-diagonal equations and zero diagonal. The comparison of off-diagonal blocks then gives $D(z)P=S^\mathsf T D(z)$, so $P$ and $S$ are diagonal with common entries $s_i$. Alternation of the bottom-right block on an adjacent pair gives
$$
 -\ell_i Q_{i,i+1}-\ell_{i+1}Q_{i+1,i}
   +(s_{i+1}-s_i)B_{i,i+1}=0.
$$
Independence of the three displayed factors forces $s_i=s_{i+1}$ on every adjacent pair. Hence all the $s_i$ agree. The remaining equations then say $D(z)Q$ is alternating, which forces $Q=0$ by the same earlier pairwise argument. Thus every right alternating multiplier is scalar. Arbitrary changes of raw bases preserve the hypotheses by the covariance calculations.

All these examples have relation spaces of growing dimension and none satisfies a fixed bound on the number of relation vectors whose union support covers all factors. Indeed a span of dimension less than $t$ has a nonzero dual annihilator, whose projective direction occurs among the factors. Hence the complete projective argument gives a distinct ordinary sign compiler. The unrestricted four-class collapse remains open.
