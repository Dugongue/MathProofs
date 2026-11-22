# Exact distinguishing width for simultaneous slice similarity

Fix the simultaneous-slice carrier over a field $k$ for a positive input format $(a,b,c)$ and a prescribed width $h\ge 1$. Put $m=h+1$. Use the same marked coordinate spaces for the two instances. A query chooses a subspace $U$ of the marked degree-one block and obtains the simultaneous similarity class of the normalized slices on $k1+U$, with the input parameter held fixed. For the symmetric carrier, use simultaneous congruence of the slices including the unit metric. In the finite local-ring variant, take the width to be the dimension of the image of the chosen submodule in the residue degree-one block. [Simultaneous-slice carrier](https://github.com/Dugongue/MathProofs/blob/main/HessianFour/Tensor.md)

**Theorem.** Let $M,M'\subseteq\operatorname{Hom}(k^a,k^b)$ be the two original matrix spaces in these marked coordinates. If $M\ne M'$, set
$$
 d_*=\min\{\operatorname{rk} A:A\in M\triangle M'\}.
$$
The least distinguishing width is exactly
$$
 (h+1)d_* .
 \tag{1}
$$
If $M=M'$, every width agrees. The same assertions hold for the ordinary carrier, the symmetric carrier, and their final-digit versions over finite commutative local rings. Indeed a joint image-span computation already distinguishes at the first possible width. Given a nonzero matrix $A$ of rank $r$, one can construct a single $mr$-direction query that decides membership $A\in M$ by that image-span computation alone.

Consequently the complete transcript of all matching queries of width at most $t$ determines exactly the set of data matrices of rank at most $\lfloor t/m\rfloor$, in the sense that two instances give the same transcript exactly when these sets agree. This comparison is in the marked layout. It applies to arbitrary simultaneous conjugating matrices on the carrier, with no requirement that they preserve its displayed block spaces.

## 1. Local relations and visible image sizes

Recall the part of the construction used below. Write $Z=k^a\oplus k^b$, $d=a+b$, and let $\widetilde A\in\operatorname{End}(Z)$ take the first summand into the second by $A$ and kill the second. Form the anchored data space
$$
 \mathcal B_M=\{[xI_Z+\widetilde A,\ yI_Z]:x,y\in k,\ A\in M\}.
$$
If $(x,y)\ne(0,0)$, the matrix has rank $d$, since either the second block is invertible or the first is a nonzero scalar plus a square-zero correction. A data matrix with $x=y=0$ has rank $\operatorname{rk} A$. For a matrix $B$ of size $d\times 2d$, write $q_B=x^{\mathsf T}B^{\oplus m} y$ on the formal coordinate space $V=X\oplus Y$ of dimension $D=3md$. Let $H_M=\{q_B:B\in\mathcal B_M\}\subseteq\operatorname{Sym}^2 V$. In the ordinary carrier $A_M=R1\oplus V_R\oplus W_R$, the product on $V_R$ is $s\beta_M(\bar u,\bar v)$, where $\beta_M(u,v)=[uv]$ in $\operatorname{Sym}^2 V/H_M$ with the prescribed inert padding in $W$. Products with $W_R$ inside the augmentation ideal vanish. Over a field take $R=k,s=1$. Otherwise take $s\ne0$ in the socle of $R$, as in the starting construction.

Write $UV$ for the span of products $uv$ with $u\in U,v\in V$. The relations on these products are precisely $H_M\cap UV$. If
$$
 H_M\cap UV=H_{M'}\cap UV,
 \tag{2}
$$
the map $\beta_M(u,v)\mapsto\beta_{M'}(u,v)$ is well-defined and extends to an invertible map on $W$. Lift that map over $R$ if necessary and fix $1,V_R$. This intertwines the entire marked subpencil, because on the unit each centered slice $L_u$ sends $1$ to $u$ and on $V_R$ it acts by the displayed product. The same map, extended contragrediently to the dual and identically to the optional metric padding, is an isometry of the symmetric unit metric and gives the simultaneous congruence there.

Let $U_R$ lift a basis of $U$ as a free direct summand, and set $b_U=\dim_k\beta_M(U,V)$. For $u\in U_R$, take the sum of the images of the centered slices $L_u$. In the ordinary carrier the sum is
$$
 U_R\oplus s\beta_M(U,V).
 \tag{3}
$$
Its dimension over a field is $\dim U+b_U$. In a finite nonfield ring its cardinality is $|R|^{\dim U}|k|^{b_U}$. One may compute it using a basis of $U_R$ and the concatenated centered matrices, by rank over a field or Smith forms over an explicit prime-power ring. In either case
$$
 b_U=\dim UV-\dim(H_M\cap UV),\qquad
 \dim UV=(\dim U)D-\binom{\dim U}{2}.
 \tag{4}
$$
For the symmetric carrier the normalized centered operators on the trivial extension are $L_u\oplus L_u^*$. The extra sum of images in the dual has dimension $1+D$ over a field, or cardinality $|R||k|^D$ over the ring, provided $U\ne0$. To see this, for a primitive $u$ the evaluation on $u$ gives the entire unit-coordinate dual line. The projection of the dual image onto $V_R^*$ gives all $sV_R^*$, since $\beta_M(\bar u,-)$ is injective and hence its dual is surjective. Evaluation on $u$ uses the $V_R^*$-input and this second contribution uses the $W_R^*$-input, so the two contributions are independent. The other centered components vanish. The prescribed unit metric makes congruence imply conjugacy of the normalized tuples. Thus differing $b_U$ distinguishes in all versions.

For completeness there is a precise local similarity criterion for the ordinary field carrier even when the intersections in (2) differ. For $U\ne0$, its marked subpencils are similar exactly when there exists $P\in\mathrm{GL}(V)$ with $P|_U=a I_U$ for some $a\in k^\times$ and
$$
 (uv\mapsto uP v)(H_M\cap UV)=H_{M'}\cap UV.
 \tag{5}
$$
Here the displayed action on $UV$ is well-defined. In a basis extending $U$, the kernel of $U\otimes V\to UV$ is generated by $u\otimes u'-u'\otimes u$ with both factors in $U$, and $I\otimes P$ multiplies these generators by $a$. For necessity, $W$ is the kernel of every $L_u$ with $u\ne0$. On $A_M/W$ the common kernel is $V$, with $L_u$ taking the unit to $u$. An intertwiner must therefore induce $P$ on $V$, a map $Q$ on $W$, and a nonzero scalar $a$ on $A_M/(V+W)$. The unit equation gives $P|_U=a I_U$, and the product equation gives $Q\beta_M(u,v)=\beta_{M'}(u,Pv)$. Conversely (5) gives this $Q$ on the image of $UV$; extend it on a complement and take the block map with components $a,P,Q$. In particular the supplied-subpencil similarity problem over a field is a simultaneous intertwining problem with fixed operator generators, where the deterministic module-isomorphism algorithm applies. [Brooksbank–Luks, *Testing isomorphism of modules*](https://ix.cs.uoregon.edu/~luks/ModIso.pdf)

## 2. A two-copy isolation lemma

For any nonzero $d\times 2d$ matrix $B$ of rank $r$ and any $m\ge2$, there is an explicitly computable $U_B\subseteq V$ of dimension $mr$ such that
$$
 \{C:q_C\in U_BV\}=k B .
 \tag{6}
$$
The formula quantifies over the entire rectangular matrix space. Thus the query construction has no dependence on the matrix space $M$ being observed.

Choose source and target coordinates putting $B$ into identity form on $r$ supported coordinates and zero elsewhere. Apply these changes to every copy. In the first two copies write $x_0,y_0\in k^{2r}$ for the lists of supported linear coordinates. Let $J_1,J_2$ be alternating $r\times r$ matrices formed from disjoint oriented path edges: $J_1$ uses $(1,2),(3,4),\ldots$ and $J_2$ uses $(2,3),(4,5),\ldots$. The oriented contribution of $(i,i+1)$ is $E_{i,i+1}-E_{i+1,i}$. Put
$$
 S=\begin{pmatrix}J_1&I_r\\-I_r&J_2\end{pmatrix}.
$$
This matrix is alternating and invertible in every characteristic. Its kernel would give $y_0=-J_1x_0$ and $(I+J_2J_1)x_0=0$. The product $J_2J_1$ moves an odd index up by two and an even index down by two, with signs and with zero at the ends. It is nilpotent.

Take the generators of $U_B$ in the first two copies to be the coordinates of $x_0+S y_0$. In each remaining copy take its $r$ supported $x$-coordinates. These $mr$ generators are independent. To check $q_C\in U_BV$ is to set them to zero in the polynomial ring and test that the resulting quadratic vanishes. In the first two copies this substitutes $x_0=-S y_0$, leaving all $y$ and all unused $x$ free. The monomials with an unused $x$ force zero on the unsupported rows of $C$. The mixed monomials with a supported $y$ and an unused $y$ force zero on the unsupported columns, by invertibility of $S$. Let $C_0$ be the remaining $r\times r$ matrix. The surviving quadratic has matrix $S\operatorname{diag}(C_0,C_0)$. Its vanishing is equivalent to that matrix being alternating, including the zero-diagonal requirement in characteristic two.

The off-diagonal identity blocks force $C_0^{\mathsf T}=C_0$. The diagonal blocks then force $C_0J_i=J_iC_0$, with $J_i C_0$ alternating. If $r$ is odd, $\ker J_2$ is the first coordinate line. A commuting map is scalar there, and propagating along adjacent edges forces the same scalar on every coordinate. If $r$ is even, $\ker J_2$ is spanned by the two endpoints. The same propagation gives $C_0=\lambda I+\mu T$, where $T e_i=(-1)^{i-1}e_{r+1-i}$ is the signed reversal. In the matching containing the edge $(r/2,r/2+1)$, $J_iT$ has a nonzero middle diagonal entry. Since $J_i C_0$ has zero diagonal, $\mu=0$ in every characteristic. Conversely scalar $C_0$ works, since $S$ is alternating. The additional copies also vanish under their chosen substitutions for these scalar matrices. This proves (6).

## 3. Exact threshold and optimization complexity

If $q_C\in UV$, choose a basis $u_1,\ldots,u_t$ of $U$ to express $q_C=\sum_{j=1}^t u_jv_j$. Its polarization rank is at most $2t$, whereas the polarization of $q_C$ has rank $2m\operatorname{rk}C$ in every characteristic. Thus $m\operatorname{rk}C\le t$. Equivalently the least direction dimension needed to contain $q_C$ is $m\operatorname{rk}C$, since a rank factorization supplies that many products directly.

Every matrix in $\mathcal B_M\triangle\mathcal B_{M'}$ with a nonzero anchor coefficient has rank $d$. The least rank of a discordant matrix is attained with both anchors zero and equals $d_*$, because $d_*<d$. Therefore all intersections in (2) agree below width $md_*$. This applies to every query, even if the query choice depends on earlier simultaneous classes. At width $md_*$, choose a matrix in the symmetric difference with rank $d_*$ and take $U_B$ from (6) for its zero-anchor embedding. The intersection is the line $kq_B$ on one side and zero on the other. Equations (3)–(4) detect it. The same proof with a single specified rank-$r$ matrix gives the membership query in the theorem. The statement is over the named coefficient field or residue field. After extending that field the formula uses the minimum rank in the extended symmetric difference.

Over $\mathbb F_2$, deciding whether the threshold is at most a given integer is NP-complete for explicit pairs of matrix spaces at fixed $h\ge1$. A certificate is one matrix in exactly one space, of rank at most the integer bound divided by $m$ and rounded down. For hardness, let $C$ be a binary linear code of length $n$, let $M$ be the diagonal matrices whose diagonals are in $C$, and compare with $M'=0$. Use the code's generator matrices as the slice list and pad the zero instance to the same length. Because a diagonal matrix has rank equal to its Hamming weight, the threshold is $m\,d_{\min}(C)$. Vardy's minimum-distance problem gives the reduction. The multiplicative equality also transfers the inapproximability from Dumer, Micciancio and Sudan, with their randomized-reduction hypotheses. This applies to the displayed marked carrier instances as well, since the data can be read from the quadratic relations by retaining the zero-anchor first-copy matrices. [Vardy, binary minimum distance](https://doi.org/10.1145/258533.258559) · [Dumer–Micciancio–Sudan](https://cseweb.ucsd.edu/~daniele/papers/DMS.html)

## 4. Exponentially many globally distinct carriers with the same local views

Fix a finite field $k$ of order $q$, and let $n\ge5$ be prime. For every $r$-dimensional $k$-subspace $U\subseteq K=\mathbb F_{q^n}$ with $2\le r\le n$, set $M_U=\{L_x:x\in U\}$, where $L_x$ is field multiplication on $K$. Use the matched tensor format $(n,n,r)$. Every nonzero matrix in this entire multiplication space has rank $n$. Consequently distinct $U,V$ give exact distinguishing width $mn=D/6$, since $D=6mn$.

Matrix-space equivalence among the $M_U$ is exactly multiplication of $U$ by a nonzero field element followed by a field automorphism fixing $k$. To prove this, suppose $P L_x Q=L_{f(x)}$ for an isomorphism $f:U\to V$. Choose $x_0\ne0$ in $U$ and $y_0=f(x_0)$. Taking the ratio with the $x_0$ equation gives
$$
 P L_{x/x_0}P^{-1}=L_{f(x)/y_0}.
$$
One ratio $x/x_0$ lies outside $k$ because $r\ge2$. The field degree is prime, so this ratio generates $K$, and $P$ normalizes the full multiplication algebra. It acts there by a $k$-automorphism $\sigma$. The ratio identity then reads $f(x)=y_0\sigma(x/x_0)$. Conversely a scalar and a field automorphism are implemented by evident source and target maps. Thus the number of equivalence classes is at least
$$
 \frac{(q-1)\begin{bmatrix}n\\r\end{bmatrix}_q}{n(q^n-1)} .
 \tag{7}
$$
The carrier's reflection theorem carries these distinct classes to pairwise nonisomorphic tensors, in both ordinary and symmetric versions. With $r=\lfloor n/2\rfloor$, (7) is $q^{n^2/4-O(n+\log_q n)}$. For fixed $h$, the carrier has $\Theta(n^2)$ variables, so this gives $q^{\Omega(N)}$ globally distinct tensors on $N$ variables with identical transcripts in every marked width strictly below $D/6=\Theta(\sqrt N)$. The same lower bound applies to the finite local-ring outputs with the same residue field. [Liebhold–Nebe, finite-field multiplication and rank-metric equivalence](https://arxiv.org/abs/1603.09565)

The exact count is available by Burnside's lemma. Let $D_r(f)$ be the number of monic degree-$r$ divisors of $f\in k[X]$. For $1\le r<n$ the number of inequivalent carriers in this family is
$$
 \frac{
 (q-1)\begin{bmatrix}n\\r\end{bmatrix}_q
 +(n-1)\dfrac{q^n-1}{q-1}\displaystyle\sum_{c\in k^\times}D_r(X^n-c)
 }{n(q^n-1)} .
 \tag{8}
$$
Indeed, a nonzero scalar in $k$ fixes every subspace, whereas a scalar in $K\setminus k$ generates $K$ as an algebra and fixes no proper nonzero subspace. For $T:x\mapsto a x^{q^j}$ with $j\ne0\bmod n$, one has $T^n=\operatorname{Norm}_{K/k}(a)I$. There is no annihilating polynomial of smaller degree: a combination of $T^i$ for $0\le i<n$ evaluates to a linearized polynomial with distinct exponents $q^{ji\bmod n}$ and degree at most $q^{n-1}<q^n$. A nonzero such polynomial cannot vanish at every point of $K$. Thus $T$ is cyclic with characteristic polynomial $X^n-\operatorname{Norm}(a)$. Its invariant subspaces are the submodules of $k[X]/(X^n-\operatorname{Norm}(a))$, and their dimension-$r$ count is $D_r$ by the correspondence with divisors. The norm is surjective with fibers of size $(q^n-1)/(q-1)$, giving (8).

The divisor count can be evaluated directly for prime $n$. If $\operatorname{char} k=n$, each $X^n-c$ is a power of one linear factor. If $n\nmid q-1$ and $\operatorname{char} k\ne n$, every $c$ is an $n$-th power, and $X^n-1$ has one linear factor and $(n-1)/f$ irreducible factors of degree $f=\operatorname{ord}_n(q)$. If $n\mid q-1$, the $n$-th powers give $n$ linear factors and the other $c$ give an irreducible polynomial of degree $n$. Indeed Frobenius acts on any root by multiplication by an $n$-th root of unity, and without a root in $k$ that multiplier has order $n$.

## Scope and prior work

The earlier construction gives simultaneous similarity below the universal width $h+1$. Here the two-copy lemma identifies the first distinguishing width separately for every pair and gives an explicit query realizing it. The threshold draws on the rank metric, while the recognition of inequivalence after forgetting the common parameter coordinates uses the original tensor reduction. Constant Jordan type and rank-metric code equivalence have their own established literatures. The results above concern exact local query transcripts and the complexity of their first discrepancy. The proof is in prose. The primary-source search did not establish priority. [Carlson–Friedlander–Pevtsova](https://arxiv.org/abs/0707.3845) · [Iarrobino–Macias Marques–McDaniel](https://arxiv.org/abs/1806.02767) · [Grochow–Qiao IV](https://arxiv.org/abs/2306.16317)

Run `python Algorithms.py` for finite controls. It checks 36 quotient-kernel dimensions over $\mathbb F_2,\mathbb F_3,\mathbb F_5$ with two and three copies. It tests all 15 nonzero binary $2\times2$ membership probes for a pair sharing their rank-one data, with the first distinction at width four. It also enumerates 11,811 three-dimensional subspaces of $\mathbb F_{128}$, with exactly 15 scalar-Frobenius orbits as in (8).
