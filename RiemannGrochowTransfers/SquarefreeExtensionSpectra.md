# Squarefree extension degrees for finite-field tensor isomorphism

Classical RH gives a bound for the short-interval fluctuations in the number of squarefree extension degrees realizing any fixed collection of tensor-isomorphism outcomes. These can include ordinary and determinant-one tensor isomorphisms over distinct finite base fields. A squarefree extension degree is a product of distinct primes, so the corresponding finite field is the compositum of its prime-degree subextensions. The bound in the full interval-length range is already equivalent to classical RH for one pair of $2\times2\times2$ multiplication tensors.

## Theorem

Fix finitely many pairs of 3-tensors over finite fields. Each pair has two tensors of the same format over its own base field $\mathbb F_{q_i}$. For each pair choose the action of either the product of general linear groups or the product of special linear groups on its three factors. Let $B(m)$ be any fixed Boolean function of the resulting isomorphism predicates over the respective extensions $\mathbb F_{q_i^m}$. Define
$$
 A(x,H)=\#\{m\in\mathbb Z_{>0}:x<m\le x+H,\ m\ \text{squarefree},\ B(m)=1\}.
$$

For each pair with a nonempty geometric transporter, let its squarefree periods be the squarefree cycle lengths of the Frobenius action on the geometric connected components of that transporter. Take $M$ to be the least common multiple of all such periods for all queries, with empty least common multiple equal to $1$. Put
$$
 \mathcal E=\{d:d\mid M,\ B(d)=1\},\qquad
 c=\frac1{\zeta(2)},\qquad
 \delta=c\prod_{p\mid M}(1+p^{-1})^{-1}\sum_{d\in\mathcal E}d^{-1}.
$$
For $a>0$, write
$$
 C_a=\prod_{p\mid M}(1-p^{-a})^{-1}\sum_{d\in\mathcal E}d^{-a}.
$$

The set that $A(x,H)$ counts has natural density $\delta$. It is nonempty precisely when $\mathcal E\ne\varnothing$, and then $\delta>0$. Its count up to $Y\ge 1$ is
$$
 A(0,Y)=\delta Y+O(C_{1/2}Y^{1/2}).
$$
Under classical RH this improves to $\delta Y+O_\gamma(C_\beta Y^\beta)$ for $\beta=11/35+\gamma<1/2$ and every such $\gamma>0$. The improvement uses Liu's squarefree counting estimate. [Liu, Theorem 1](https://www.sciencedirect.com/science/article/pii/S0022314X15002462)

Assume classical RH. For $0<\varepsilon<1/100$, $0<\eta<1/2$, $a=1/4+\eta/2$, and $1\le H\le X^{1-\varepsilon}$, we have
$$
 \frac1X\int_X^{2X}|A(x,H)-\delta H|^2\,dx
 \ll_{\varepsilon,\eta} C_a^2 H^{1/2+\eta}.
$$
The implied constant is independent of the tensor pairs and their base fields. Without RH the bound with $a=1/4$ and $H^{1/2}$ holds through $H\le X^{6/11-\varepsilon}$. Classical Lindelöf extends that bound to $H\le X^{2/3-\varepsilon}$. [Gorodetsky–Matomäki–Radziwiłł–Rodgers, Theorems 1 and 3](https://link.springer.com/article/10.1007/s00039-021-00557-5)

If $\delta>0$, the fraction of $x\in[X,2X]$ with $|A(x,H)-\delta H|>\lambda\delta H$ is
$$
 \ll_{\varepsilon,\eta}\frac{C_a^2}{\lambda^2\delta^2}H^{-3/2+\eta}
$$
in the RH range, for any $\lambda>0$. This follows by Chebyshev's inequality.

## Proof

Let $T,S$ be one of the pairs over $\mathbb F_q$, and let $G$ be its chosen product of general or special linear groups. Let $Z$ be the transporter of $T$ to $S$. If $Z(\overline{\mathbb F}_q)$ is empty the predicate is identically false. Otherwise choose $g\in Z(\overline{\mathbb F}_q)$. Let $J$ be the reduced stabilizer of $T$ and $J^\circ$ its identity component. Reduction preserves the points over finite extensions and the algebraic closure. Over the perfect field $\mathbb F_q$, the reduced stabilizer is a smooth algebraic group. The geometric transporter is a translate of the stabilizer, so its geometric connected components on points are precisely the right cosets of $J^\circ(\overline{\mathbb F}_q)$ in $Z(\overline{\mathbb F}_q)$.

Write $F$ for $q$-power Frobenius. An $\mathbb F_{q^m}$-point lies in a component fixed by $F^m$. Conversely, choose $g$ in an $F^m$-fixed component. Then $F^m(g)=g u$ for $u\in J^\circ(\overline{\mathbb F}_q)$. Lang's theorem gives $b\in J^\circ(\overline{\mathbb F}_q)$ with $u=bF^m(b)^{-1}$. Thus $gb$ is $F^m$-fixed, hence is an $\mathbb F_{q^m}$-point of the transporter. The predicate is therefore true exactly when one of the Frobenius cycle lengths on the component set divides $m$. For squarefree $m$, only squarefree cycle lengths can divide it. For all the queries together this gives $B(m)=B(\gcd(m,M))$ for squarefree $m$. [Lang, Algebraic Groups Over Finite Fields](https://wstein.org/papers/bib/Lang-Algebraic_Groups_Over_Finite_Fields.pdf)

Let $\mu$ be the Möbius function and $\Omega(b)$ count prime factors with multiplicity. Write $\mathcal S_M$ for the positive integers all of whose prime factors divide $M$, including $1$. For each $d\mid M$ and each positive integer $m$,
$$
 \mu^2(m)\mathbf 1_{\gcd(m,M)=d}
 =\sum_{\substack{b\in\mathcal S_M\\ db\mid m}}
       (-1)^{\Omega(b)}\mu^2\!\left(\frac m{db}\right).
$$
If $d\nmid m$, both sides vanish. Otherwise put $n=m/d$. At a prime $p\mid M$ with $p^e\Vert n$ and $e\ge1$, the two possible exponents of $p$ in $b$ are $e$ and $e-1$, with opposite signs. When $e=0$ the local contribution is $1$. At a prime $p\nmid M$, $b$ cannot contain $p$, and the local factor requires that $v_p(n)\le1$. Thus the sum is $1$ precisely when $n$ is squarefree and coprime to $M$, in which case $m=dn$ is squarefree and has $\gcd(m,M)=d$.

Sum this identity over $d\in\mathcal E$ and over $x<m\le x+H$. The contribution indexed by $(d,b)$ is $(-1)^{\Omega(b)}$ times the squarefree count on $(x/(db),(x+H)/(db)]$. Its center is $cH/(db)$ times the same sign. The signed centers add to $\delta H$ by the absolutely convergent identity
$$
 \sum_{b\in\mathcal S_M}\frac{(-1)^{\Omega(b)}}b=\prod_{p\mid M}(1+p^{-1})^{-1}.
$$
For a count up to $Y$, apply $\sum_{n\le y}\mu^2(n)=cy+O(y^{1/2})$ on each dilated interval, or Liu's bound for the improvement. The elementary estimate follows by summing $\mu^2(n)=\sum_{r^2\mid n}\mu(r)$ and bounding the tail of $\sum_r\mu(r)/r^2$ absolutely. Both counting estimates also hold for $0<y<1$ because there the count is zero and $y\le y^\beta$ for $0<\beta\le1$. The error terms sum absolutely to the stated bounds since $\sum_{b\in\mathcal S_M} b^{-a}=\prod_{p\mid M}(1-p^{-a})^{-1}$ for every $a>0$.

For the short-interval statement, put
$$
 E_k(x)=\sum_{x/k<n\le (x+H)/k}\mu^2(n)-cH/k,
 \qquad
 \|E_k\|_2=\left(\frac1X\int_X^{2X}|E_k(x)|^2\,dx\right)^{1/2}.
$$
We claim $\|E_k\|_2\ll_{\varepsilon,\eta}(H/k)^a$ for every integer $k\ge1$. If $k\le H$, set $X'=X/k$, $H'=H/k$ and change variables to $x/k$. Then $1\le H'\le (X')^{1-\varepsilon}$, so Theorem 3 of Gorodetsky–Matomäki–Radziwiłł–Rodgers gives the claim. If $H<k\le3X$, the uncentered count takes values in $\{0,1\}$. Each multiple of $k$ contributes on a set of $x$ of length at most $H$, and there are at most $2X/k+1$ multiples to consider in $(X,2X+H]$. Its normalized second moment is therefore $O(H/k)$. Subtracting the center gives $\|E_k\|_2\ll (H/k)^{1/2}\le(H/k)^a$. If $k>3X$, the count vanishes and $cH/k\le(H/k)^a$. Theorem 1 gives the same argument with $a=1/4$ and either of the shorter ranges, since $H\le X^\theta$ implies $H/k\le(X/k)^\theta$ for $k\ge1$ and $0<\theta\le1$. [Gorodetsky–Matomäki–Radziwiłł–Rodgers, Theorems 1 and 3](https://link.springer.com/article/10.1007/s00039-021-00557-5)

Minkowski's inequality for the normalized $L^2$ norm now gives
$$
 \|A(\cdot,H)-\delta H\|_2
 \le \sum_{d\in\mathcal E}\sum_{b\in\mathcal S_M}\|E_{db}\|_2
 \ll_{\varepsilon,\eta} C_a H^a.
$$
The infinite sum is justified by absolute convergence of this norm bound. On the interval of integration its uncentered part has only finitely many nonzero terms, and its center converges absolutely. Squaring proves the desired bound.

## An explicit pair equivalent to RH

For any finite field $\mathbb F_q$, use the ordinary multiplication tensors of the two-dimensional $\mathbb F_q$-algebras
$$
 R=\mathbb F_{q^2},\qquad S=\mathbb F_q\times\mathbb F_q.
$$
For unital commutative algebras over any field, ordinary multiplication-tensor isomorphism is equivalent to algebra isomorphism. Indeed, if $h(xy)=f(x)g(y)$ for linear isomorphisms $f,g,h$, then $u=f(1)$, $v=g(1)$ are units because multiplication by each is an invertible linear map. We have $f(x)=v^{-1}h(x)$, $g(y)=u^{-1}h(y)$, so $\phi=(uv)^{-1}h$ is multiplicative and unital. An algebra isomorphism in all three positions gives the reverse implication. The base change of $R$ to $\mathbb F_{q^m}$ is a field for odd $m$ and a product of two copies of the extension field for even $m$. Thus the degree-$m$ tensors are isomorphic exactly when $m$ is even. [Finite étale descent](https://stacks.math.columbia.edu/tag/04JI)

Let $F(x,H)$ be the count for this pair, of density $\delta=c/3=2/\pi^2$. If $Q(x,H)$ counts all squarefree degrees on the same interval, then
$$
 Q(x,H)=F(x,H)+F(2x,2H).
$$
Doubling maps the odd squarefree degrees on $(x,x+H]$ bijectively onto the even squarefree degrees on $(2x,2x+2H]$. The centers on the right add to $3\delta H=cH$. Suppose the claimed full-range variance bound holds for this one pair for every allowed $\varepsilon,\eta$. For $H\le X^{1-\varepsilon}$, both intervals fall within the respective bound with $\varepsilon/2$ for all sufficiently large $X$, since $2H\le(2X)^{1-\varepsilon/2}$. The normalized $L^2$ triangle inequality and the change of variable $y=2x$ transfer the bounds back to $Q(x,H)-cH$. The bounded $X$ range is absorbed in the implied constant. Theorem 3 then implies classical RH. Restricting to $0<\eta<1/2$ makes no difference since $H\ge1$. [Gorodetsky–Matomäki–Radziwiłł–Rodgers, Theorem 3](https://link.springer.com/article/10.1007/s00039-021-00557-5)

## A determinant-one obstruction equivalent to RH

Over any odd finite field take the multiplication tensor of $R=\mathbb F_{q^3}$ in one basis and again in the basis obtained by negating the first vector. Ordinary tensor isomorphism holds at every extension. For determinant-one tensor isomorphism the unit normalization above gives $f=L_u\phi$, $g=L_v\phi$ and $h=L_{uv}\phi$, where $L_a$ is multiplication by $a$. Hence $\det\phi=\det(f)\det(g)/\det(h)$. A determinant-one algebra isomorphism therefore exists exactly when a determinant-one tensor isomorphism exists.

The identity on $R$, expressed from the first basis to the second, has determinant $-1$. When $3\nmid m$, the scalar extension of $R$ is a degree-three field over $\mathbb F_{q^m}$. Every automorphism acts on its three geometric primitive idempotents by a power of a three-cycle, so has determinant $1$. All the algebra isomorphisms from the first basis table to the second consequently have determinant $-1$. When $3\mid m$, the scalar extension splits as a product of three copies of $\mathbb F_{q^m}$. Transposing two factors gives determinant $-1$ and corrects the determinant of the identity. Thus ordinary isomorphism holds and determinant-one isomorphism fails exactly for $3\nmid m$.

Let $D(x,H)$ count the squarefree degrees for this distinction, whose density is $3c/4$. Every squarefree multiple of $3$ is uniquely $3n$ with $n$ squarefree and coprime to $3$. Consequently
$$
 Q(x,H)=D(x,H)+D(x/3,H/3).
$$
The centers on the right sum to $cH$. For $H\ge3$, the dilated interval satisfies $1\le H/3\le (X/3)^{1-\varepsilon}$ in the full range $H\le X^{1-\varepsilon}$. For $1\le H<3$, both discrepancies are bounded. The same $L^2$ triangle inequality gives the converse from Theorem 3. Thus in this fixed $3\times3\times3$ example the full-range variance bound for the ordinary-isomorphism and determinant-one distinction is equivalent to classical RH. [Gorodetsky–Matomäki–Radziwiłł–Rodgers, Theorem 3](https://link.springer.com/article/10.1007/s00039-021-00557-5)

The proof uses the established Frobenius component description of finite-field tensor extension spectra. The spectrum of the cubic example also follows from the earlier signed étale classification. [Frobenius components](../OptimalMaxRankAndDescent/ExtensionSpectra.md), [signed étale spectra](../VertexCoverAndExtensionSpectra/Spectra.md). The contribution is the uniform transfer to finite Boolean combinations, the exact density and the two fixed tensor-pair converses. This is an informal proof based on the cited theorems. Publication priority for the transfer is unverified.
