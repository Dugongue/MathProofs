# Frobenius pairings for determinant-one associative algebra isomorphism

Informal mathematics over a fixed finite field $F=\mathbb F_q$. A local finite-dimensional unital algebra is given by its multiplication table in raw coordinates. The determinant is that of the $F$-linear map in the raw source and target bases. We prove a one-instance ordinary TI reduction for determinant-one isomorphism of local Frobenius algebras in characteristic two, with no bound on the dimensions of any radical layer. In odd characteristic a perfect pairing from a characteristic square-zero ideal isolates the unpaired determinant. A decomposition by left and right residue-field actions, and then an alternating form, can greatly reduce the remaining exterior dimensions or remove them entirely.

## 1. Recover the socle line and its norm

Let $A$ be a local algebra, $J$ its Jacobson radical, and $E=A/J$, a finite field extension of $F$. Use the condition that the left socle $S=\{x:Jx=0\}$ is simple as a left module, equivalently that $\dim_F S=[E:F]$. This is the local Frobenius condition. The radical and semisimple quotient are computable in deterministic polynomial time at fixed characteristic, and $S$ is found by linear equations. [Ivanyos–Qiao, Theorem 18](https://arxiv.org/html/1708.03495#Thmtheorem18)

Here $S$ is a two-sided ideal since $J$ is an ideal. Its right $J$-action is zero: every right multiplication by $j\in J$ on $S$ is $E$-linear for the left field action, and it is nilpotent, hence zero on this $E$-line. Choose any left $E$-basis element $s$ of $S$, and a functional $\tau:A\to F$ with $\tau(a s)=\operatorname{Tr}_{E/F}(a)$ on $S$. This functional is computed by linear algebra. The form $B(x,y)=\tau(x y)$ is nondegenerate. Indeed any nonzero left ideal contains $S$: apply successive powers of $J$ until the last nonzero submodule, which meets $S$, and use simplicity. The right kernel of $B$ is therefore zero, since a nonzero element $y$ of that kernel would put the whole left ideal $A y$ in $\ker \tau$. The trace of a finite separable field extension is a nonzero functional. The resulting nondegenerate associative form is also the usual Frobenius condition. Conversely for a local Frobenius algebra the regular left module identifies with the $F$-dual of the right regular module by this form, so its left socle is dual to the simple right quotient $E$, and thus simple.

Construct $J',E',S',s',\tau',B'$ for a second algebra $A'$. An algebra isomorphism $\theta:A\to A'$ induces $\sigma:E\to E'$ and satisfies
$$
 \theta(a s)=\sigma(a)\lambda s'\qquad(a\in E)
$$
for some $\lambda\in E'^\times$. There is a unique $u\in A$ with $\tau'\theta(x)=\tau(u x)$ for every $x$, by nondegeneracy of $B$. It is a unit because this new functional also has a nondegenerate associative form, which forces $L_u:x\mapsto u x$ to be invertible. Comparing on $S$ through the trace pairings gives $\bar u=\sigma^{-1}(\lambda)$ in $E$. Since left multiplication by $u$ induces multiplication by $\bar u$ on every radical grade, its determinant is $\mathrm N_{E'/F}(\lambda)^{\dim_F A/[E:F]}$. This uses the ordinary determinant on each $E$-linear grade and the field norm.

Writing $B,B'$ also for the matrices in the raw bases, the identity $B'(\theta x,\theta y)=B(u x,y)$ gives
$$
 (\det_F\theta)^2
   =\frac{\det B}{\det B'}\,\mathrm N_{E'/F}(\lambda)^{\dim_F A/[E:F]}.
$$
Thus only the norm of a single line multiplier is needed to test the square of the original determinant.

This norm is enforceable on the actual algebra isomorphism by one ordinary TI instance. Include the two algebras, the maps to their residue fields, and their inclusions of the socle lines with the residue-field actions. Every algebra isomorphism induces exactly the associated field and socle maps. For a line in chosen $E$-coordinates with map $z\mapsto\lambda\sigma(z)$, use $[E:F]$ copies chained by the $F$-linear $q$-Frobenius. This forces the successive multipliers $\lambda,\lambda^q,\ldots,\lambda^{q^{[E:F]-1}}$ under the shared field isomorphism. Binary multiplication maps between prefix lines combine them, and the inclusion of an $F$-line into the final $E$-line extracts $\mathrm N(\lambda)$. Binary multiplication maps and a marked terminal value then enforce the required power of the norm, with the displayed calibration. These attachments are the shared-Frobenius norm construction from the preceding MathProofs local-centroid work. Typed systems of a polynomial list of linear and bilinear maps can be packed in a fixed signature by tagging occurrences in direct sums and linking them back to their original spaces. The compiler sends this system to one ordinary TI pair. Every permissible $\theta$ extends to the system, and every system isomorphism enforces the exact formula. [Chen–Grochow–Qiao–Tang–Zhang, Theorem 4.1](https://arxiv.org/html/2306.03135v2#S4.Thmtheorem1)

When $\operatorname{char}F=2$, squaring is injective on $F^\times$, so imposing the squared target is exact. For odd $q$ this construction alone reads only the squared determinant.

## 2. Cancel the two ends of an intrinsic square-zero filtration

Take a two-sided ideal $K$ chosen by a polynomial-time isomorphism-invariant rule, with $K^2=0$. One may take a suitable high power of $J$. Its left and right annihilators coincide; denote them by $P$. To verify this, the right $B$-orthogonal to $K$ is its right annihilator: if $\tau(Ky)=0$, then $\tau(A k y)=0$ for every $k\in K$, so $k y=0$. The analogous argument gives the left annihilator as the left orthogonal. Nondegeneracy defines the Nakayama automorphism $\eta$ by $\tau(x y)=\tau(y\eta(x))$. Its multiplicativity follows by applying this identity twice, and invertibility follows by nondegeneracy. Since the ideal $K$ is invariant under every automorphism, $\eta(K)=K$, so the two orthogonals coincide. We have $K\subseteq P$, a perfect pairing $K\times (A/P)$ under $B$, and a nondegenerate induced form on $P/K$.

Choose adapted $F$-bases for $K,P,A$ and the corresponding quotients on each side. Let $B_{K,A/P}$ be the square pairing matrix in the chosen quotient bases. It is nonsingular. The same relation $B'(\theta x,\theta y)=B(u x,y)$ and the fact that $K$ is a left module give
$$
 \det\theta_K\cdot\det\theta_{A/P}
  = \frac{\det B_{K,A/P}}{\det B'_{K',A'/P'}}\,
        \mathrm N_{E'/F}(\lambda)^{\dim_F K/[E:F]} .
$$
The exponent is the length of $K$ as a module over the local algebra, as seen by its $J$-filtration. The determinant of $\theta$ in adapted bases is this product times $\det\theta_{P/K}$. The ratio of raw adapted-basis matrices is additional explicit calibration. Attach the inclusions and quotient maps to the original algebra so all these actions are those of the same $\theta$. This gives an exact determinant-one test with no exterior powers whenever $P=K$, and with exterior powers only on the middle $P/K$ otherwise. In particular an $O(\log L)$ middle dimension suffices, where $L$ is dense input bit length.

## 3. Remove all paired residue-field summands from the middle

Assume now $JP+PJ\subseteq K$. Then $M=P/K$ is an $E$-bimodule and multiplication gives a well-defined map $M\times M\to S$. Indeed $K$ annihilates $P$ on both sides, and $J(x y)=(Jx)y=0$ for $x,y\in P$. Give $S$ the chosen left basis $s$. Its right action is $s a=\nu(a)s$ for a unique $F$-automorphism $\nu$ of $E$, since the right action is a unital field homomorphism into the endomorphisms of a left $E$-line.

For each $\rho\in\operatorname{Gal}(E/F)$, set
$$
 M_\rho=\{x\in M:x a=\rho(a)x\text{ for every }a\in E\}.
$$
These are a direct-sum decomposition of $M$. The action of a right field generator on the left $E$-space is annihilated by its minimal polynomial over $F$, which splits over $E$ with distinct roots. Its eigenspaces are precisely the listed spaces, so they are computable by linear algebra. Field generators and alignment may be obtained by the standard finite-field algorithms. Alternatively find a generator by choosing coordinates in an $F$-basis to avoid the maximal proper subfields: each is the kernel of a known Frobenius power minus the identity, and the sum of their densities in a degree $f$ field is at most $\omega(f)q^{-\lceil f/2\rceil}<1$ for $f>1$. Fix coordinates one by one to avoid increasing the expected number of memberships, using Gaussian elimination for the conditional counts. The final integer number of memberships is zero. In degree one take $1$. [Lenstra, Finding Isomorphisms Between Finite Fields](https://pub.math.leidenuniv.nl/~lenstrahw/PUBLICATIONS/1991b/art.pdf)

If $x\in M_\rho$, $y\in M_\zeta$, their product in $S$ can be nonzero only if $\rho\zeta=\nu$. Indeed $(xy)a=x(ya)=\rho(\zeta(a))xy$, while $xy\in S$ has right twist $\nu$. The nondegenerate middle Frobenius form therefore pairs $M_\rho$ perfectly with $M_{\rho^{-1}\nu}$. Every algebra isomorphism maps each label to the corresponding label: $\sigma$ intertwines the $q$-Frobenius powers on the two fields. It also preserves the label of $\nu$.

For a pair of distinct labels $\rho,\zeta=\rho^{-1}\nu$, choose ordered bases and compute the nonsingular pairing matrices $B_{\rho,\zeta},B'_{\rho,\zeta}$ using $\tau,\tau'$ on the product. The same determinant equality as in Section 2 gives
$$
 \det\theta_{M_\rho}\,\det\theta_{M_\zeta}
  =\frac{\det B_{\rho,\zeta}}{\det B'_{\rho,\zeta}}\,
    \mathrm N_{E'/F}(\lambda)^{\dim_E M_\rho}.
$$
No width restriction applies to either paired space. There is at most one partner for every label, and the number of labels is the field degree. Matching labels and width comparisons impose only necessary actual isomorphism conditions and hold automatically on every feasible pair.

Only the self-paired labels, satisfying $\rho^2=\nu$, need an additional determinant test. One may use their usual exterior spaces when their $F$-dimensions are logarithmic in $L$. Alternatively an $E$-dimension bound suffices: for a semilinear action $G\sigma$ the determinant in the expanded $F$-bases is $\mathrm N(\det_E G)(\det_F\sigma)^{\dim_E}$. Use the $E$-exterior algebra and the norm chain in Section 1. To read $\det_F\sigma$, align the two fields in a common standard model. Let $\gamma$ be the determinant of $q$-Frobenius, and use the finite label algebra on the Frobenius orbit $w^{q^j}$ of a degree $f=[E:F]$ element. Its $j$-th idempotent maps to $w^{q^j}$ and also to $\gamma^j$ in an auxiliary $F$-line. A shift by $v$ on the labels forces the line multiplier $\gamma^v=\det_F\sigma$. These are polynomially sized attachments. If $\nu$ is not a square in the cyclic Galois group, there are no self-paired labels and no exterior width restriction at all, even in odd characteristic.

## 4. Read an alternating quotient of a self-paired space

When the self-paired label is $\rho=1$, we have $\nu=1$ and multiplication on $M_1$, with values in $S$, is $E$-bilinear. In the chosen basis of $S$, let $\beta$ be its scalar bilinear map, and set $\omega(x,y)=\beta(x,y)-\beta(y,x)$. Put $R=\operatorname{rad}(\omega)$, the kernel of its contraction. Every actual $\theta$ maps $R$ to $R'$ since it is a semilinear similitude of $\omega$ with multiplier $\lambda$. The induced $\omega$ on $M_1/R$ is alternating and nondegenerate. Choose symplectic bases there on both sides. In these bases the $E$-linear part of the relative map has determinant $\lambda^{\dim_E(M_1/R)/2}$, by the Pfaffian identity applied to the standard alternating form. The coordinatewise $\sigma$ factor has $F$-determinant one on this quotient: its $E$-dimension is even, and $\det_F\sigma=\pm1$ in aligned field models, since on the geometric embeddings it is a permutation. In arbitrary chosen bases there is the usual known frame determinant ratio.

Thus an exterior space on the possibly huge $M_1$ can be replaced by one on $R$. If $\dim_E R=O(\log L)$, this permits a polynomial one-instance test, including the case $R=0$, using only the small exterior and norm construction. All paired products, small residual determinants, raw change-of-basis factors and the socle multiplier can be combined by binary multiplication maps on $F$-lines and one terminal mark. Because the original multiplication and the defining inclusions, field actions, and quotients remain in the instance, every calculation is performed on the same actual algebra isomorphism. There is no independent choice of the action on any grade or summand.

## 5. Examples with unbounded radical layers

First take $E/F$ quadratic with nonidentity field automorphism $\nu$. Use the local algebra $A=E\oplus U\oplus V\oplus S$, with $U,V=E^d$ as left spaces and $S$ a left $E$-line. The right twists on $U,V,S$ are $1,\nu,\nu$, respectively. For $u\in U$, $v\in V$, set
$$
 u v=\Bigl(\sum_i u_i v_i\Bigr)s,\qquad
 v u=\Bigl(\sum_i v_i\,\nu(u_i)\Bigr)s .
$$
Both like-type products and all products involving $S$ and $J=U\oplus V\oplus S$ vanish. Associativity follows from the balanced $E$-actions and the vanishing of triple radical products. The pairings are perfect, so the left socle is $S$; also $J^2=S$ and $P=\operatorname{Ann}(S)=J$. Taking $K=S$ gives $M=U\oplus V$ with the two distinct paired labels. Since the nonidentity element of a group of order two is not a square, the reduction uses no exterior algebra, regardless of $d$.

For an odd-characteristic example where a self-paired space is present, let $B=F\oplus V\oplus Fz$ with $V$ of arbitrarily large even dimension, and $v w=\omega_0(v,w)z$ for a nondegenerate alternating form $\omega_0$. The top element $z$ annihilates the radical. Put $A=B\otimes_F F[t]/(t^\ell)$ for odd $\ell\ge3$. It is radical-graded and generated in degree one, with top socle degree $\ell+1=2a$, $a=(\ell+1)/2$. The homogeneous grades pair perfectly in complementary degrees into the top socle, by the product of the pairings in the two factors. Consequently $K=J^{a+1}$ is square-zero, $P=J^a$, and $JP+PJ=K$. The middle grade is
$$
 F t^a\ \oplus\ Vt^{a-1}\ \oplus\ Fzt^{a-2}.
$$
Its alternating part is nondegenerate on the $V$-summand and has radical equal to the two displayed scalar summands. Hence the determinant test uses exterior dimension only on a two-dimensional space, even though the middle grade and the radical generators grow linearly with $\dim_F V$. Taking $\ell$ fixed already makes these widths exceed logarithmic bounds, and taking $\ell$ growing also gives arbitrarily long radical towers.

These are determinant-one reductions on raw associative algebra tables. They do not give coverage of the whole unpadded triangular normalization: that normalization generally has three residue components and need not be Frobenius. Its tensor residues still require an unrestricted determinant test. The proof provides sufficient alternatives to exterior width on the stated Frobenius classes. Publication priority is unverified.
