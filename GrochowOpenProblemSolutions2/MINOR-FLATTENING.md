# Third-minor flattening and conormal dimension in odd characteristic

The third-minor rank of a finite commutative algebra measures the conormal dimension over any field of characteristic different from two. In the Gorenstein case it also measures the Hilbert tangent dimension. The characteristic-zero algebraically closed comparison was already established by Doležálek, Jagiełła, Oszer, Seynnaeve and Stastny, who proved Doležálek and Michałek’s complex Conjecture 6.3. The argument here gives the extension to positive odd characteristic, including characteristic three, by directly describing the annihilator of the minor span. This is an informal proof. [Prior result, Theorem 1.5 and Corollary 7.9](https://arxiv.org/html/2610.17875v1)

## Statement

Let $k$ be a field with $\operatorname{char} k\ne 2$, let $P=k[x_1,\ldots,x_d]$, and let $R=P/I$ be a finite commutative unital $k$-algebra of dimension $n>0$. Write $T\in R^*\otimes R^*\otimes R$ for its multiplication tensor and $C=R$ for its output factor. Then
$$
 \operatorname{rank}\Phi_{\mathrm M,3}^{C}(T)-\binom n3=dn-\dim_k(I/I^2).
$$
If $R$ is Gorenstein, this also gives
$$
 \operatorname{rank}\Phi_{\mathrm M,3}^{C}(T)-\binom n3
 =dn-\dim_k T_{[R]}\operatorname{Hilb}_n(\mathbb A_k^d).
$$

## The third-minor span

For $a_i,b_i\in R$, set
$$
 D(a;b)=\sum_{\sigma\in S_3}\operatorname{sgn}(\sigma)
   (a_1b_{\sigma(1)})(a_2b_{\sigma(2)})(a_3b_{\sigma(3)})\in\operatorname{Sym}^3 R.
$$
The three inner products take place in $R$ and the outer product takes place in the symmetric algebra. By the determinant formula, the image $W$ of the third-minor flattening is precisely the span of these elements. Taking $a_i,b_i$ from a basis gives the ordinary minors of the multiplication matrix with entries in $R$ viewed as linear forms on $R^*$. Allowing arbitrary triples gives the same span by multilinearity. This interpretation uses polynomial coefficients and is valid over finite fields as well. [Definition of the minor flattening, §7](https://arxiv.org/html/2610.17875v1#S7)

Write $W^\circ$ for the annihilator in $(\operatorname{Sym}^3R)^*$. Its elements are symmetric trilinear forms $\Theta$ with
$$
 \sum_{\sigma\in S_3}\operatorname{sgn}(\sigma)
  \Theta(a_1b_{\sigma(1)},a_2b_{\sigma(2)},a_3b_{\sigma(3)})=0.       \tag{1}
$$
The restriction $\Theta\mapsto\Theta(1,\cdot,\cdot)$ is surjective onto symmetric bilinear forms. For a given symmetric bilinear form $U$, take
$$
 \Theta_U(a,b,c)=
 \frac{U(ab,c)+U(ac,b)+U(bc,a)-U(abc,1)}{2}.
$$
The restriction of $\Theta_U$ is $U$. Also, each of the first three terms satisfies (1) because after fixing the sole unmerged slot, the transposition of the other two slots cancels the summand by commutativity. The last term is independent of $\sigma$ in (1), so it satisfies (1) as well.

Let $N$ be the kernel of restriction. Then
$$
 \dim_k W^\circ=\frac{n(n+1)}2+\dim_k N.                            \tag{2}
$$

## The normalized annihilator and cocycles

Take the $R$-module $M=R^*$ with $(a\lambda)(b)=\lambda(ab)$, and put $e(\lambda)=\lambda(1)$. We identify $N$ with symmetric bilinear maps $\phi:R\times R\to M$ satisfying
$$
 \phi(1,a)=0,\qquad e(\phi(a,b))=0,\qquad
 a\phi(b,c)-\phi(ab,c)+\phi(a,bc)-c\phi(a,b)=0.                    \tag{3}
$$
For $\Theta\in N$, define $\phi(a,b)(c)=\Theta(a,b,c)$. The first two conditions follow from normalization. In (1) take triples $(1,a,b)$ and $(1,c,d)$. The terms matching the two units vanish, and the rest give
$$
 \Theta(ad,b,c)+\Theta(bc,a,d)=\Theta(ac,b,d)+\Theta(bd,a,c).
$$
By permuting the four variables the same expressions also equal $\Theta(ab,c,d)+\Theta(cd,a,b)$. Evaluation of the last expression in (3) at $d$ gives
$$
 \Theta(ad,b,c)-\Theta(ab,c,d)+\Theta(bc,a,d)-\Theta(cd,a,b)=0.
$$
This proves (3).

Conversely, equip $R\oplus M$ with the commutative unital product
$$
 (a,u)*(b,v)=(ab,av+bu+\phi(a,b)).
$$
It is associative by (3) and $M$ is a square-zero ideal. Write $\widehat a=(a,0)$ and let $\widetilde e(a,u)=e(u)$. By $e(\phi(ab,c))=0$,
$$
 \widetilde e(\widehat a*\widehat b*\widehat c)=e(c\phi(a,b))
 =\phi(a,b)(c).
$$
Hence $\Theta(a,b,c)=\phi(a,b)(c)$ is symmetric and normalized. For arbitrary triples and a permutation $\sigma$, set $t_i=a_i b_{\sigma(i)}$. Applying $\widetilde e$ to their product grouped in pairs gives
$$
 \widetilde e\left(\prod_{i=1}^{3}(\widehat a_i*\widehat b_{\sigma(i)})\right)
 =\Theta(t_1,t_2,t_3)+
   \sum_{i=1}^3 e\left(\left(\prod_{j\ne i} t_j\right)\phi(a_i,b_{\sigma(i)})\right).
$$
The left side is independent of $\sigma$. For each fixed $i$ the correction term depends only on $\sigma(i)$, since the ordinary products of the remaining factors may be reordered, so its alternating sum vanishes. It follows that $\Theta$ satisfies (1). This proves the stated identification of $N$.

## Dimension of the normalized cocycle space

Let $T^1(R,M)$ be the space of symmetric bilinear maps satisfying the first and third conditions in (3), modulo the coboundaries
$$
 (\partial X)(a,b)=aX(b)+bX(a)-X(ab),
 \qquad X\in\operatorname{Hom}_k(R,M),\quad X(1)=0.
$$
It classifies square-zero extensions of $R$ by $M$ with the indicated $R$-action, up to isomorphisms that fix $R$ and $M$. To see this, choose a linear unital section of an extension. Its error in respecting products is such a cocycle, and changing the section by $X$ changes the error by $\partial X$. A cocycle conversely supplies the displayed multiplication on $R\oplus M$.

Every class has a representative in $N$. For a normalized unital cocycle $\phi$, set $F(a,b)=e(\phi(a,b))$ and take $X(a)(b)=-F(a,b)/2$. Then $X(1)=0$ and $X(ab)(1)=0$ by $F(1,\cdot)=0$ and symmetry. It follows that $e((\partial X)(a,b))=-F(a,b)$, giving the required representative.

For a map $X:R\to M$, write $X^t(a)(b)=X(b)(a)$. For $m\in M$, set $J_m(a)(b)=m(ab)$. For $X(1)=0$ the equation $e(\partial X)=0$ is equivalent to $X+X^t=J_m$ where $m=X^t(1)$. Such maps are in bijection with skew-transpose maps $Y$ via $X=Y-J_{Y(1)}$. In one direction this gives $X(1)=0$, $X^t(1)=-2Y(1)$ and $X+X^t=J_{-2Y(1)}$. In the other direction take $Y=X-J_m/2$, which is skew-transpose and has $Y(1)=-m/2$. The skew-transpose space has dimension $n(n-1)/2$ because it is the space of alternating bilinear forms and $2$ is invertible. The kernel of $X\mapsto\partial X$ is the space $\operatorname{Der}_k(R,M)$. Thus
$$
 \dim_kN=\dim_k T^1(R,M)+\frac{n(n-1)}{2}-\dim_k\operatorname{Der}_k(R,M).   \tag{4}
$$

## Conormal dimension and conclusion

The algebra presentation gives the exact sequence
$$
 0\longrightarrow\operatorname{Der}_k(R,M)
 \longrightarrow\operatorname{Der}_k(P,M)
 \longrightarrow\operatorname{Hom}_P(I,M)
 \longrightarrow T^1(R,M)\longrightarrow0.
$$
Indeed, lift the variables into any extension of $R$ by $M$. The lifted polynomial homomorphism maps $I$ into $M$, where its restriction is $P$-linear for the action through $R$. Conversely, for $f\in\operatorname{Hom}_P(I,M)$ the quotient of the split square-zero algebra $P\oplus M$ by the ideal $\{(i,-f(i)):i\in I\}$ is an extension inducing $f$. Changing the lifts changes $f$ by the restriction of a derivation $P\to M$. Such a derivation descends precisely when it vanishes on $I$. The map to $T^1(R,M)$ is linear since with a fixed linear unital section $s:R\to P$ the cocycle of the extension obtained from $f$ is $f(s(a)s(b)-s(ab))$.

The middle derivation space has dimension $dn$, from freely choosing the images of the polynomial generators. Also, for every $R$-module $L$, evaluating at $1$ identifies $\operatorname{Hom}_R(L,R^*)$ with $\operatorname{Hom}_k(L,k)$. The inverse sends a functional $h$ to $v\mapsto(r\mapsto h(rv))$. As $I$ acts by zero on $M$, we obtain $\dim_k\operatorname{Hom}_P(I,M)=\dim_k(I/I^2)$. Equations (2) and (4) yield
$$
 \dim_kW^\circ=n^2+\dim_k(I/I^2)-dn.
$$
Since $\dim_k\operatorname{Sym}^3R=\binom{n+2}3=\binom n3+n^2$, this proves the conormal formula.

Finally, a finite Gorenstein $k$-algebra has an $R$-module isomorphism $R\cong R^*$. On each Artin local factor choose a $k$-linear functional nonzero on its socle, which is a simple module and meets every nonzero ideal, and sum these functionals. The induced multiplication pairing is nondegenerate. Thus the Hilbert tangent space $\operatorname{Hom}_R(I/I^2,R)$ has dimension $\dim_k(I/I^2)$ in the Gorenstein case, proving the second formula.
