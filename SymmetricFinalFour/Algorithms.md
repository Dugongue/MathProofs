# Determinant profiles and exact counts for symmetric final-digit tensors

Fix the symmetric final-digit construction, with a finite commutative local ring $R$, nonzero maximal ideal $\mathfrak m$, residue field $k$ of order $q$ and characteristic $p$, and $0\ne s\in\operatorname{Ann}_R(\mathfrak m)$. Denote the lifted algebra by $A_t$, its Frobenius functional by $\lambda_t$, and its symmetric tensor by $F_t(x,y,z)=\lambda_t(xyz)$. Write $l$ for the dimension of its marked field form $C_t$, $\epsilon\in\{0,1\}$ for the optional line in the lift, and $N=2l+2+\epsilon$, with $p\nmid N$. All statements concern pairs in a fixed input format. [Symmetric final-digit construction](https://github.com/Dugongue/MathProofs/blob/main/FinalDigitFour/Tensor.md)

Put $U=R^\times$, $V=U^N$, and, for $\epsilon=0$, put $W=U^{N/2}$. For any equivalent pair of the displayed tensors, the independent-mode determinant triples are exactly
$$
 \begin{cases}
 \{(x,y,d/(xy)): d\in W,\ x,y\in dV\},&\epsilon=0,\\
 V^3,&\epsilon=1.
 \end{cases}
 \tag{1}
$$
The determinant image for diagonal transporters is $W$ for $\epsilon=0$ and $V$ for $\epsilon=1$. Every attained profile has the same number of transporters for its action. These images, including their sizes, depend only on the format and ring.

Let $A$ denote the number of unital $R$-algebra isomorphisms $A_t\to A_{t'}$, and let $J_3=|\{z\in R:3z=0\}|$. The exact counts for the four actions on the displayed tensors are
$$
\begin{array}{c|c}
\text{action}&\text{transporter count}\\ \hline
\mathrm{GL}^3& |A_t^\times|^2 A\\
\text{diagonal }\mathrm{GL}& J_3 A\\
\mathrm{SL}^3& |A_t^\times|^2 A/(|W||V|^2)\quad(\epsilon=0),\qquad
                 |A_t^\times|^2 A/|V|^3\quad(\epsilon=1)\\
\text{diagonal }\mathrm{SL}& J_3 A/|W|\quad(\epsilon=0),\qquad
                      J_3 A/|V|\quad(\epsilon=1).
\end{array}
\tag{2}
$$
All four counts are zero for inequivalent inputs. In particular, choosing diagonal transport rather than comparing independent witnesses introduces an exact factor from the annihilator of $3$. For $R=\mathbb Z/p^e\mathbb Z$, $e\ge2$, $J_3=3$ at $p=3$ and $J_3=1$ at every other prime. Section 4 computes $A$ from the original field transporter count by an explicit positive multiplier when $p$ is odd. Thus exact counting goes both ways on those formats; the profile and ratio formulas (1)–(2) hold at every $p$.

## 1. Transporters as units and one algebra isomorphism

For the field construction, use three argument spaces $X_i$ of dimensions $a_i$, put $n_0=\sum_i a_i$, and let
$$
 O_i=X_i\oplus X_i^*\oplus H_i,\qquad
 \dim H_i=2^i(n_0+7),\qquad K=\bigoplus_i O_i,\qquad
 L=K\oplus \operatorname{span}\{z_1,z_2,z_3\}.
$$
The pairing $\beta_i$ on $O_i$ is the evaluation pairing plus the split hyperbolic pairing on $H_i$. The only nonzero restrictions of $C_t$ are $t$ on $X_1\times X_2\times X_3$ and $\beta_i$ on $z_i\times O_i\times O_i$, copied to each argument permutation. Thus every nonzero basis triple has distinct indices. The vectors of full contraction rank at most $n_0+6$ are exactly $K$: a contraction by a vector in $K$ has rank at most $n_0$ on $K\times K$ and three extra rows and columns. Any nonzero marker coefficient creates rank at least $\dim H_i>n_0+6$. Restricted to $K\times K$, the ranks lie in bands of width $2n_0$ above the subset sums of $\dim H_i$ for the marker support. These sums are spaced by at least $2(n_0+7)$. In particular the three marker lines in $L/K$ are individually intrinsic. The pairing with marker and $O_i$ detects every nonzero vector in $K$, so $C_t$ has zero contraction radical. If $D_i^0$ is the contraction radical in $X_i$, the radical of $C_t|_{K^3}$ is $D=\bigoplus_i(D_i^0\oplus X_i^*\oplus H_i)$, by testing on the other two roles.

The lift has $A_t=R1\oplus I$, with $I=E\oplus Rz$ and
$E=L_R\oplus L_R^*\oplus R^\epsilon$. On $E$, let $B$ be the fixed hyperbolic pairing plus the optional rank-one form with value $1$ on its basis vector. The product of $x,y\in E$ is
$$
 B(x,y)z+sC_t(\bar x_L,\bar y_L,-),
 \tag{3}
$$
where the second term takes values in $sL_R^*$; write $s$ times a field coefficient using $k\cong sR$. The functional $\lambda_t$ takes the $z$-coordinate. The anchor pairs $1$ with $z$, and its restriction to $E$ is $B$. In particular the perfect pairing has exactly the same matrix $G$ for every $t$. The trace of left multiplication by $r1+x$, $x\in I$, is $Nr$, since left multiplication by $I$ is strictly triangular in the unit, $L_R$, $L_R^*\oplus R^\epsilon$, $Rz$ filtration (one can put the optional line with $L_R$). Thus $I$, and its annihilator $Rz$ inside $I$, are intrinsic under algebra isomorphism. The annihilator assertion follows by testing against the perfect $B$. The coefficient of $1$ is called the augmentation.

For a unital algebra isomorphism $\phi:A_t\to A_{t'}$, define $d_\phi$ by
$$
 \lambda_{t'}(d_\phi\,\phi(x))=\lambda_t(x)\qquad(x\in A_t).
$$
It exists uniquely by perfectness. Let $\phi(z)=\eta z$. Substituting $1,z$ shows that $d_\phi$ has zero $z$-coordinate and augmentation $\eta^{-1}$, so it is a unit. The inverse of a unit plus a nilpotent summand is given by a finite geometric series.

Every independent transporter is uniquely
$$
 (L_u\phi,L_v\phi,L_w\phi),\qquad u,v,w\in A_{t'}^\times,\quad uvw=d_\phi.
 \tag{4}
$$
To see this, from a transporter $(f,g,j)$ use the perfect pairings to define $h$ by $\lambda_{t'}(h(a)j(y))=\lambda_t(ay)$. Then $h(xy)=f(x)g(y)$. At an input equal to $1$, invertibility implies that $u=f(1)$ and $v=g(1)$ have bijective multiplication maps, hence are units. The map $\phi=(uv)^{-1}h$ is a unital algebra isomorphism by associativity. The pairing identity then determines $j=L_{(uv)^{-1}d_\phi}\phi$. Conversely the formula gives a transporter by evaluation and commutativity. In particular $u,v$ are free choices for the independent action, and the diagonal action uses exactly the choices $u=v=w$, equivalently $u^3=d_\phi$. [Albert, associative isotopy](https://doi.org/10.2307/1968960) · [Jagiełła–Jelisiejew, multiplication and evaluation tensors, Proposition 4.1](https://arxiv.org/html/2604.24879v1)

## 2. Determinants and orbit splitting

Multiplication by a unit with augmentation $a$ has determinant $a^N$. In fact it is triangular in the same ordered decomposition, with $a$ on every diagonal entry. Write $\delta=\det\phi$. The perfect-pairing identity has matrix $G=\phi^{\mathsf T}GL_{d_\phi}\phi$ and therefore
$$
 \delta^2=\eta^N .
 \tag{5}
$$
If $\epsilon=0$, then $p\ne2$. Modulo $\mathfrak m$, the induced map on $E$ preserves $L^*$, since $L^*$ is the contraction radical of the field cubic form obtained by dividing triple products in $I$ by $s z$ and restricting to $E$. Here the conciseness of $C_t$ is used. On $E$ the residue map is a $B$-similitude of multiplier $\bar\eta$ preserving that Lagrangian. If its quotient map on $L$ is $P$, then its map on $L^*$ is $\bar\eta P^{-\mathsf T}$, so its determinant is $\bar\eta^l$. Consequently $\delta\equiv\eta^{l+1}\bmod\mathfrak m$. Equation (5) strengthens this to $\delta=\eta^{l+1}=\eta^{N/2}$, since a square root of $1$ congruent to $1$ is $1$ when $2$ is a unit. For $\epsilon=1$, put $\tau=\delta\eta^{-(l+1)}$. Then (5) gives $\tau^2=\eta$ and $\delta=\tau^N$ in every characteristic.

The range of $\eta$ is $U$ when $\epsilon=0$ and $U^2$ when $\epsilon=1$. To see sufficiency, the field form $C_t$ has a diagonal similitude with any multiplier $\bar\eta\in k^\times$. Scale the three $X_i$ by arbitrary factors with product $\bar\eta$, scale their evaluation duals by $\bar\eta$ divided by the respective factor, fix the markers, and scale one vector in each split pair of each auxiliary $H_i$ by $\bar\eta$. Let $P$ be a lift on $L_R$. Use $P$ on $L_R$, $\eta P^{-\mathsf T}$ on $L_R^*$, $\eta$ on $z$, and, when present, $\tau$ on the optional line, where $\tau^2=\eta$. Equations (3) make this an algebra automorphism satisfying $\lambda_t\phi=\eta\lambda_t$, so its twist $d_\phi$ is the scalar $\eta^{-1}$. For a distinct equivalent pair first use the determinant-one, functional-preserving lift of an input transporter supplied by the construction. The same choices of $\eta$ and $\tau$ then apply.

Writing $a,b,c$ for the augmentations of $u,v,w$, (4) gives the determinants $x=\delta a^N,\ y=\delta b^N,\ z'=\delta c^N$ with $abc=\eta^{-1}$. Equation (5) yields $xyz'=\delta$. For every allowed $\delta$, any $x,y\in\delta V$ can be obtained by choosing the first two augmentations; the last determinant is forced. If $\epsilon=0$ this gives the first line of (1). If $\epsilon=1$, $\delta$ ranges over $V$ and the result is $V^3$. In the diagonal case $a^3=\eta^{-1}$. For $\epsilon=0$, the determinant is $a^{-N/2}$, and every such value occurs by taking the scalar-twist automorphism for $\eta=a^{-3}$ and $u=a$. For $\epsilon=1$, $a^3\tau^2=1$, and the determinant is $(a\tau)^N$. Given $r\in U$, take $a=r^2,\tau=r^{-3}$ with the scalar-twist automorphism and $u=a$; this realizes every element of $V$.

On an automorphism group the profile map is a homomorphism into the abelian determinant group. Fibers over its image have the same size. On equivalent displayed inputs the prescribed determinant-one witness transfers this conclusion to the transporter coset. The size of (1) is $|W||V|^2$ or $|V|^3$. This also computes the number of special-linear orbits inside a general-linear orbit, including arbitrary basis changes of the displayed tensors. In the independent action the number is $|U|^3/(|W||V|^2)$ or $|U|^3/|V|^3$, and in the diagonal action it is $|U|/|W|$ or $|U|/|V|$. Indeed the special-linear subgroup is normal, and a general-linear orbit of an object with stabilizer $H$ splits into cosets of the image of $H$ in the determinant quotient. Given an ordinary transporter between arbitrary copies, its determinant profile class in that quotient decides whether the two copies are special-linearly equivalent.

Both exponents $N$ and, when used, $N/2$ are prime to $p$. For either exponent $j$, the power map is bijective on the principal units $1+\mathfrak m$, a finite abelian $p$-group. Thus $|U^j|=|U|/\gcd(j,q-1)$, and membership is tested by the residue-field $(q-1)/\gcd(j,q-1)$ power. These computations and the ratios in (2) are polynomial bit-time for the prime-power rings. In particular an ordinary transporter of arbitrary copies whose determinants are all $1\bmod\mathfrak m$ always has the same profile class as the identity, regardless of precision.

## 3. Why the diagonal count contains exactly $J_3$

For any linear functional $\ell_0:E\to R$ there is an automorphism fixing $1,z$ with
$$
 x\longmapsto (1+sT)x+\ell_0(x)z\qquad(x\in E),
 \tag{6}
$$
where $T$ has its only nonzero block from $L_R$ to $L_R^*$. Choose $\bar T$ so that its matrix plus its transpose is the matrix of $(x,y)\mapsto\bar\ell_0(C_t(x,y,-))$ on $L$. In odd characteristic take half the matrix. In characteristic two it is alternating because all nonzero basis triples in $C_t$ have three distinct basis indices. Choose its upper triangle. Equation (3) verifies (6): the only change in $B$ is $s\bar\ell_0(C_t(x,y,-))$, which exactly accounts for the added $z$-coordinate of the image of the $sL_R^*$ product. Invertibility follows from the triangular shape.

For fixed $\eta$, the twists $d_\phi$ are uniformly distributed over $\eta^{-1}1+E'$, with zero $z$-coordinate. To verify uniformity, use $\lambda_{t'}(d_\phi y)=\lambda_t(\phi^{-1}(y))$. The value at $1$ is zero and the value at $z$ is $\eta^{-1}$. Postcomposing $\phi^{-1}$ with a fixed (6) in the source algebra adds the functional $\ell_0\circ M$ to its values on $E'$, with $M:E'\to E$ the original invertible induced map. The maps (6) form a finite group when all solutions for the residue matrix $\bar T$ are allowed. Composition adds the shear matrices because their supported blocks compose to zero. The functionals add and acquire one term of the form $\ell_2\circ sT_1$, which vanishes modulo $\mathfrak m$ and hence leaves the symmetrization condition unchanged. On a group orbit of inverse isomorphisms, fixing one starting map, every functional on $E'$ is attained the same number of times. To see this directly, let $M_0$ be that starting induced map and vary the automorphism in the entire group (6). Its functional contribution is exactly $\ell_0 M_0$, and for each $\ell_0$ the admissible skew differences of $T$ form a fixed additive set of the same size. Group action on isomorphisms by composition is free. Finally perfectness of $B$ identifies the functionals on $E'$ with the $E'$-coordinates of $d_\phi$. The multiplier fibers themselves also have equal sizes by the homomorphism $\phi\mapsto\eta$ on algebra automorphisms. Put $H=U$ or $U^2$ for the multiplier range.

For $u=r1+x+c z$, $r\in U,\ x\in E',\ c\in R$, the $z$-coordinate of $u^3$ is
$$
 3r^2c+3r B(x,x)+sC_{t'}(\bar x_L,\bar x_L,\bar x_L).
$$
If $p\ne3$, there is one choice of $c$ making this zero. If $p=3$, the last term is zero, since the value of $C_{t'}$ on a repeated vector is a sum over triples of distinct basis indices with coefficient $6$. In this case there are exactly $J_3$ values of $c$, since the equation is $3r(r c+B(x,x))=0$. The augmentation condition $r^3\in H$ is equivalent to $r\in H$; for $H=U^2$ this follows in the exponent-two quotient. Hence there are $|H||E'|J_3$ units whose cubes have matching allowable augmentation and zero $z$-coordinate. Each such cube is the twist of $A/(|H||E'|)$ isomorphisms. Summing proves the diagonal count in (2). The independent count follows from (4), with $|A_t^\times|=|U||R|^{N-1}$.

## 4. Exact reduction to the original field count at odd primes

Assume $p\ne2$. Let $r_i$ be the three support ranks of the input field form, and use the same ranks for the target for now. If ranks differ, all counts are zero. Let $m_i=\dim O_i$ in the marker construction, $d_i=m_i-2r_i$, $m=2l+\epsilon$. Write $I_{\mathrm{supp}}$ for the number of transporters of the input after quotienting its three contraction radicals. Then
$$
\begin{split}
 A ={}& I_{\mathrm{supp}}\,(q-1)^3
      \prod_{i=1}^3 \left[|\operatorname{O}^{+}_{d_i}(k)|\,
                    q^{r_i d_i+\binom{r_i}{2}}\right]\\
     &{}\cdot |R|^m\,|H|\, 2^\epsilon\,
        q^{\epsilon l+\binom l2} |\mathfrak m|^{\binom m2}.
\end{split}
\tag{7}
$$
Here $H=U$ or $U^2$ as above. The original full input count is $I_{\mathrm{supp}}\prod_i|\mathrm{GL}_{a_i-r_i}(k)|q^{r_i(a_i-r_i)}$, where $a_i=\dim X_i$. One chooses the invertible contraction-radical map and the unrestricted cross block in each input mode. Thus (7) and (2) give explicit exact multiplicative reductions in both directions.

To prove the first line, use the intrinsic $K=\bigoplus O_i$, the fixed marker lines in $L/K$, and the radical $D$ of $C_t|_{K^3}$, all recovered by the rank and restriction arguments of the starting construction. For a projective transporter of multiplier $\nu$, write $z_i\mapsto \rho_i z_i'+v_i$, $v_i\in K'$, and denote the map on $K$ by $P_K$. Each $D_i=D\cap O_i$ is recovered from the common kernels on $D$ of the pairings $\beta_j$ with $K$ for $j\ne i$. These pairings are obtained by testing the marker slice on $K\times D$, where a marker translation by $K$ has no effect. Thus $P_K D_i=D'_i$. Evaluating the transformed triple with markers $i,j$ and $d\in D_i$ forces $\beta_i'(v_j,P_Kd)=0$ for $i\ne j$. For $i=j$, the same expression occurs with coefficient $2\rho_i$, a unit. In both cases cubic terms on $K'^3$ vanish by the radical argument. Consequently every $v_j$ belongs to $\bigoplus_i(D_i')^\perp$ with perpendiculars taken within $O_i'$, which is contained in $\bigoplus_i X_i'^*\subset D'$. Testing one marker and two arbitrary vectors in $K$ now forces $P_K$ to preserve the blocks $O_i$ and act on $O_i$ by a similitude of multiplier $\nu/\rho_i$. Indeed each block is the intersection of the kernels of the other two pairings. Testing two markers on all of $K$ forces $v_j=0$ by the same equations, using nondegeneracy on $O_i'$.

Thus for fixed $\nu$, the marker scalars $\rho_i$ are free and the block similitudes must preserve the isotropic subspaces $D_i^\perp$, of dimensions $r_i$. Their maps on the quotients $O_i/D_i$ give a supported input transporter of multiplier $\nu$. Multiplying one of its modes by a fixed scalar gives a bijection with the exact supported transporters. The orthogonal middle quotient $D_i/D_i^\perp$ is split of dimension $d_i$, from the unused input hyperbolic pairs and $H_i$. Each fixed quotient map and multiplier has $|\operatorname{O}^{+}_{d_i}(k)|q^{r_i d_i+\binom{r_i}{2}}$ parabolic completions. Indeed a block-diagonal completion exists by taking the dual inverse with multiplier on the isotropic subspace and a split similitude on the middle quotient. Divide by this completion to reduce to quotient map and multiplier $1$. With basis order quotient, middle, isotropic, and pairing matrix with identity corners and middle matrix $B_0$, these maps are
$$
 \begin{pmatrix} I&0&0\\ X&S&0\\ Z&Y&I\end{pmatrix},\qquad
 S^{\mathsf T}B_0 S=B_0,\quad
 Y=-X^{\mathsf T}B_0 S,\quad Z+Z^{\mathsf T}=-X^{\mathsf T}B_0 X.
$$
Here $X$ is arbitrary, $Y$ is forced, and $Z$ is freely chosen up to a skew matrix, because $2$ is invertible. This proves the parabolic count. The split orthogonal group order for $d_i=2b>0$ is $2q^{b(b-1)}(q^b-1)\prod_{j=1}^{b-1}(q^{2j}-1)$, with order $1$ for dimension zero. One can count hyperbolic bases successively: in split dimension $2b$, there are $(q^b-1)(q^{b-1}+1)$ nonzero isotropic vectors, by counting pairs $x,y$ with $x\cdot y=0$, and $q^{2b-2}$ isotropic partners of pairing $1$ for each. Every such pair splits off a hyperbolic plane, so the count recurses.

For the second line, for each fixed multiplier $\eta$ and residue induced map on $E$, composing with (6) of residue identity sweeps all $|R|^m$ functionals on $E$ as the $z$-coordinate of $\phi|_E$. One may therefore count the maps with zero such functional and multiply by $|R|^m$. With zero functional, the map on $E$ is an exact $B$-similitude of multiplier $\eta$ by (3). Its residue preserves $L^*\oplus k^\epsilon$, the contraction radical of the extended $C_t$, and therefore preserves the perpendicular $L^*$. On the quotient $L$ it induces a projective transporter of multiplier $\bar\eta$. Conversely these conditions suffice. The $sL_R^*$-component of (3) transforms by the residue map on $L^*$, namely $\bar\eta P^{-\mathsf T}$, which is precisely the required condition on $C_t$ for a multiplier-$\bar\eta$ map $P$.

For each fixed such residue $P$ and multiplier, the block calculation above applies with isotropic rank $l$ and middle dimension $\epsilon$, giving $2^\epsilon q^{\epsilon l+\binom l2}$ possibilities. The middle line has two isometries in odd characteristic, and a block-diagonal completion exists since $\eta\in H$. Every residue possibility lifts to an exact $B$-similitude over $R$ with the specified ring multiplier. Lift it arbitrarily to $M_0$; the matrix $\eta^{-1}B^{-1}M_0^{\mathsf T}BM_0=I+E_0$ is self-adjoint for $B$ and $E_0$ has entries in the nilpotent ideal $\mathfrak m$. Right multiplication of $M_0$ by the truncated series $(I+E_0)^{-1/2}$ corrects it. The binomial coefficients have only powers of $2$ as denominators and the series terminates. Each fiber is a coset of the orthogonal congruence kernel. The Cayley transform identifies that kernel with the matrices in $\mathfrak m$ skew-adjoint for $B$: use $(I-M)(I+M)^{-1}$ and its inverse. Invertibility holds since $2$ is a unit, and multiplying a skew-adjoint matrix by $B$ identifies it with a skew-symmetric matrix with zero diagonal. This counts $|\mathfrak m|^{\binom m2}$ choices. Finally multiply by $|H|$. The factor for each $\eta$ is identical because the first line holds at every nonzero field multiplier. All multiplicative factors have polynomial-size binary encodings and can be computed in polynomial time for the prime-power rings. [O'Leary, Cayley representation](https://arxiv.org/abs/math/0606320)

## Relation to earlier results

Grochow–Qiao's linear-length reductions and Grochow–Qiao–Tang's symmetric-form equivalences concern tensor decision and related algorithms over fields. Grochow–Qiao's search/counting-to-decision results use stabilizer-chain reductions. The final-digit construction supplies a common reduction, fixed slice and a simultaneous determinant-one witness. The proof here counts all independent and diagonal witnesses by explicit ring factors, classifies their determinant profiles, and proves multiplicative counting equivalence with the original ordinary field problem in odd residue characteristic. The characteristic-two statements are (1)–(2), whose proofs use the special alternating shape of the marker coefficients. The odd-characteristic computation (7) uses $2$ as a unit in two separate steps and is stated only there. This is a prose proof. The literature search did not establish priority. [Grochow–Qiao IV](https://arxiv.org/html/2306.16317) · [Grochow–Qiao–Tang](https://arxiv.org/abs/2012.01085) · [Grochow–Qiao, search and counting](https://doi.org/10.4230/LIPIcs.CCC.2021.16)

Run the companion `Algorithms.py` for finite controls. It enumerates the profiles obtained from the scalar parameter equations over $\mathbb Z/8,\mathbb Z/27,\mathbb Z/25,\mathbb Z/49$ at actual construction dimensions. For example, $(R,N)=(\mathbb Z/25,332)$ has 250 independent profiles and 10 diagonal profiles, so its ordinary orbits split into 32 and 2 corresponding special-linear orbits. The script also verifies 1,536 basis-level shear identities and 5,620 cubic evaluations in small Frobenius models over $\mathbb Z/4,\mathbb Z/9,\mathbb Z/25$, and enumerates the odd-residue parabolic block completions in two small dimensions.
