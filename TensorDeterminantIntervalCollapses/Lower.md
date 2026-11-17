# Exact comparisons among the lower interval algebra languages

Work over $F=\mathbb F_3$. Write $O$ for ordinary dense three-tensor isomorphism and $A$ for determinant-one isomorphism in only the first mode. Use the lower interval definitions from the preceding catalogue. In L3 the first determinant is tested when both raw tensors are ordinarily isomorphic to multiplication tensors of commutative unital associative algebras. L4 adds that the algebras are local with scalar residue. L5 adds one-dimensional socle. L7 further requires the tangent dimension $e\ge2$ and radical nilpotence index $3e+1$. Each language uses ordinary TI on its default branch. Conditions are recognized from raw coordinates by recovering the fixed-label adjoint algebra and explicit regular-module frames. In particular the algebras, their radicals, the tangent dimensions, and their powers can all be recovered in deterministic polynomial time. The earlier catalogue gives $O\le_m^p \mathrm{L7}\le_m^p \mathrm{L5}\le_m^p \mathrm{L4}\le_m^p \mathrm{L3}\le_m^p A$.

The additional results here are
$$
\mathrm{L3}\equiv_m^p\mathrm{L4}\equiv_m^p A,
\qquad
\mathrm{L5}\equiv_m^p\mathrm{L7}.
$$
The degree of L5 and L7 relative to either endpoint remains unresolved here. The two constructions use actual multiplication tensors and track all ordinary transporter determinants on their active branches.

## 1. Commutative local multiplication tensors retain one arbitrary sign

For an $A$ comparison, first reject incompatible formats or support dimensions. If the first mode is odd-dimensional or has unused support, its sign is freely correctable by a scalar gauge or a reflection on the unused complement. Use the ordinary-branch reduction in this case. Otherwise let the even first dimension be $a$ and let this dimension have full support.

Pad the two other dimensions to positive odd numbers $b,c$, adding at least one unused coordinate in each, and arrange $(b-1)c>a+2$. This is a polynomial amount of padding. Use calibrated castling in the first mode, replacing the image of the full first flattening by its annihilator in the dual of the $b$ by $c$ product space. A determinant-one ordered completion of the image coordinates supplies the calibration. The new tensor is concise in all three modes. For the unchanged padded modes this follows because the annihilator contains each entire strip associated with a newly unused coordinate in the other mode. Its three dimensions are odd. Write them as $u=bc-a,v=b,w=c$, so $u>w+2$. If an old transporter has determinant triple $(d_1,d_2,d_3)$, the new first determinant is $d_1d_2^cd_3^b=d_1d_2d_3$ and the other determinants are $d_2,d_3$. Thus its total sign is exactly $d_1$. The double-annihilator inverse reflects every castled transporter, preserving that character. This uses the preceding catalogue's determinant-calibrated castling calculation. For the ordinary castling correspondence see [Derksen, Makam, and Walter](https://arxiv.org/abs/2011.03849).

Write either new tensor as a concise bilinear map $\mu:U\times V\to W$. Fix a common two-dimensional auxiliary space $Z$. Define a commutative unital algebra $R_\mu=F1\oplus X\oplus Y$, with
$$
X=U\oplus V\oplus Z,\qquad
Y=W\oplus (U\otimes Z).
$$
Its only nonzero products within the radical, up to switching factors, are
$$
uv=\mu(u,v),\qquad uz=u\otimes z .
$$
All products of $Y$ with the radical vanish. This makes associativity immediate because both parenthesizations of every triple radical product vanish. It is scalar-residue local, with $J=X\oplus Y$, $J^2=Y$ by conciseness, and dimension $3+3u+v+w$, which is even.

Recover the original tensor intrinsically from the induced product $\beta:(J/J^2)^2\to J^2$. The subspace $X_0=U\oplus V$ is exactly the set of $x$ with $\operatorname{rank}\beta(x,-)\le w+2$. If $x\in X_0$, its image lies in $W$ plus at most a two-dimensional subspace from its product with $Z$. If $x$ has nonzero $Z$ component, its product on $U$, projected to $U\otimes Z$, already has rank $u>w+2$. The integer $w$ is known and the same in the two tensors produced from the comparison. Next $W=\operatorname{span}\beta(X_0,X_0)$. Reducing products modulo $W$ gives a well-defined map
$$
X_0\times(X/X_0)\longrightarrow Y/W.
$$
Its left kernel is $V$. The product $(X_0/V)\times V\to W$ is therefore the recovered $\mu$, since products within $V$ vanish. The second displayed product also identifies $Y/W$ with $(X_0/V)\otimes(X/X_0)$.

Every algebra isomorphism therefore induces an original transporter $g_U,g_V,g_W$ and an invertible map $g_Z$ on the marker quotient. Conversely every original transporter extends by identity on $Z$ and the tensor-product action on $U\otimes Z$. If $d_U,d_V,d_W,d_Z$ are the corresponding determinants, determinant multiplication on the preserved flags gives
$$
\begin{aligned}
\det(\phi|_X)&=d_Ud_Vd_Z,\\
\det(\phi|_Y)&=d_W d_U^2 d_Z^u=d_Wd_Z,\\
\det\phi&=d_Ud_Vd_W.
\end{aligned}
$$
Here the first line uses $X=J/J^2$ and its filtration, so off-diagonal shears do not affect it. The second line uses the $Y/W$ tensor-product action and $u$ odd.

An ordinary transporter of multiplication tensors of unital algebras is an algebra isomorphism with left and right unit factors. Specifically $p(x)q(y)=r(xy)$ implies $r(x)=p(x)v=u q(x)$ with units $u=p(1),v=q(1)$ by invertibility, and $\phi=u^{-1}p=qv^{-1}$ is a unital algebra isomorphism. The first determinant is $\det(L_u)\det\phi$. In a scalar-residue local algebra of even dimension, $\det L_u=1$ because $L_u$ acts on each radical grade by the scalar residue of $u$, whose even power is one. Thus the first-mode determinant of every new transporter reads the total sign of one recovered transporter of $\mu$. Conversely all old transporters lift with exactly this readout. This gives $A\le_m^p\mathrm{L4}$, using a polynomial enlargement of each source tensor. Its outputs also meet L3. Together with the known upper inclusions it proves the first two equalities.

## 2. Padding Frobenius algebras to the L7 nilpotence index

For an active L5 comparison recover the two commutative scalar-residue local algebras $R,R'$ using the catalogue recognizer. Each has one-dimensional socle. Compare the common dimension $n$, tangent dimension $e=\dim J_R/J_R^2$, and largest $d$ with $J_R^d\ne0$. Mismatches reject by invariance. If $n$ is odd, multiplication by a unit of negative scalar residue corrects the first determinant, so use the ordinary branch. On the remaining branch $n$ is even and $J_R\ne0$. For both algebras the last nonzero power is exactly the one-dimensional socle, so fix nonzero socle vectors $s,s'$.

Choose an integer $e'>e$ satisfying $e'\equiv3\bmod4$, $e'\ge2$, and $3e'-1>d$. Take the least such integer, put $k=e'-e$ and $r=3e'$. In particular $r\equiv1\bmod4$ and $r\ge9$. For each algebra adjoin $k$ marker strings with the same unit, with the positive part of each string annihilating the old radical and every other string. The powers of a given string are
$$
z_i,z_i^2,\ldots,z_i^{r-1},\qquad z_i^r=s,\qquad z_i^{r+1}=0 .
$$
Formally this is the fiber product over $F$ with the $k$ truncated univariate algebras, then quotient by the span of the differences between their socle generators and the old socle generator. Those differences generate an ideal because all positive factors annihilate every shared socle generator. Denote the output by $\widehat R$. It has basis consisting of a basis of $R$ and the indicated pre-top powers of the new tags. It is scalar-residue local, and its socle is still $Fs$. Indeed a socle element is in the radical. Multiplying it by each $z_i$ forces every coefficient in that tag to vanish, since all resulting powers up to and including $z_i^r=s$ are nonzero and independent for this single-tag test. The remaining old part is in $\operatorname{Soc}(R)$. The converse is immediate. The tangent dimension is $e+k=e'$ and the nilpotence index is $r+1=3e'+1$. These are L7 algebras. The output dimension $n+k(r-1)$ is even and polynomial in $n$.

Let $\Phi:\widehat R\to\widehat R'$ be an algebra isomorphism. Its action on the old tangent subspace $J_R/J_R^2$ inside the full tangent is intrinsic. That is precisely the set of tangent vectors whose $(r-1)$-st power is zero in $J_{\widehat R}^{r-1}/J_{\widehat R}^r$. This power is well-defined on tangent classes, since changing a lift by $J_{\widehat R}^2$ changes its $(r-1)$-st power by an element of $J_{\widehat R}^r$. It kills all old tangent coordinates by $r-1>d$. Conversely a nonzero tag tangent coefficient gives a nonzero corresponding marker power in the quotient, where the $z_i^{r-1}$ remain independent. In the resulting quotient by the old tangent the map on the tag directions is monomial. Indeed the images of distinct $z_i,z_j$ have zero product by the source relation. The coordinate of their product on each target tag's degree-two term is the product of their two tangent coefficients at that tag and hence is zero. No other term can cancel that degree-two coordinate. In the invertible tag map, this forces the columns to have nonempty disjoint supports, hence exactly one nonzero per column and per row. Write this as the permutation $\pi$ with leading scales $\nu_i\in F^\times$.

For $x\in J_R$ one has $\Phi(x)\Phi(z_i)=0$. In the $\pi(i)$-th target tag, $\Phi(z_i)$ has a nonzero degree-one coefficient. If the pre-top component of $\Phi(x)$ there has lowest exponent $t<r-1$, their product has a nonzero coefficient of $z_{\pi(i)}^{t+1}$, a pre-top term that neither the old algebra nor any other tag can cancel. Consequently all possible tag contamination of $\Phi(J_R)$ is in the degree-$(r-1)$ marker span. Its products with itself vanish. Projecting $\Phi|_R$ to $R'$ along all the marker powers therefore gives a unital algebra homomorphism $g:R\to R'$. This uses both that radical tag contamination has product zero and that $\Phi(1)=1$. It is injective. If its kernel contained $x$, then $x$ has zero scalar residue and $\Phi(x)$ would consist only of degree-$(r-1)$ markers. Multiplication by each matching $\Phi(z_i)$ gives that coefficient times $\nu_i s'$, so $\Phi(x)=0$. Thus $g$ is an isomorphism. It has the same action on the socle as $\Phi$, since the output socle is intrinsic.

The extra tags contribute determinant one despite possible shears. In the fixed splitting $\widehat R=R\oplus P$, with $P$ the sum of all pre-top marker powers, write the isomorphism matrix as
$$
\begin{pmatrix}g&B\\D&H\end{pmatrix}.
$$
The map $D$ lands in the highest marker grade $P_{r-1}$, and vanishes on the socle. Also $B(P_{r-1})\subseteq Fs'$ because $\Phi$ preserves $J^{r-1}$, whose old part is only the shared socle. Hence $Dg^{-1}B$ vanishes on $P_{r-1}$ and has image in it, so this Schur correction does not change the diagonal blocks of the power filtration of $H$. On marker grade $t$ the leading block of $H$ is the same permutation $\pi$ with scales $\nu_i^t$. The product of their determinants is
$$
\operatorname{sgn}(\pi)^{r-1}
 \Bigl(\prod_i\nu_i\Bigr)^{r(r-1)/2}=1
$$
by $r\equiv1\bmod4$. Thus $\det\Phi=\det g$ in the stated split bases. Conversely every algebra isomorphism $g$ extends. If $g(s)=\lambda s'$, extend by $z_i\mapsto\lambda z'_i$. Since $r$ is odd, $\lambda^r=\lambda$ and all relations are preserved. This extension likewise has determinant $\det g$.

It remains to relate determinants to the raw first-mode coordinates. The recognized raw multiplication frames are computed independently on the two inputs. Their determinant ratio calibrates the desired determinant of $g$ in the chosen $R,R'$ bases. Unit factors are neutral in dimension $n$ and in dimension $n+k(r-1)$. Therefore rebasing the target first mode of the output by a fixed reflection if the calibration bit is negative makes the physical first determinant condition exactly the original one. The rebase does not affect L7 eligibility. On a default L5 branch or an odd active dimension use the ordinary-branch nonsquare padding. This proves $\mathrm{L5}\le_m^p\mathrm{L7}$. The reverse uses the inclusion of activation conditions and the same ordinary padding.

These proofs are informal and do not resolve whether ordinary TI equals one-sign TI. They do show that unconstrained commutativity and scalar-locality cannot restrict the one-sign degree, and that the particular L7 radical-length constraint leaves the Frobenius degree unchanged.
