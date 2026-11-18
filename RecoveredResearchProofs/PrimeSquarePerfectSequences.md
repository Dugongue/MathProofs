# Perfect prime-phase sequences of length p² are generalized Frank sequences

**Theorem.** Let $p$ be prime and let $\zeta$ be a primitive $p$th root of unity. A sequence $s(x)=\zeta^{f(x)}$, with $f : \mathbb Z/p^2\mathbb Z\to\mathbb F_p$, has zero periodic autocorrelation at every nonzero shift if and only if there are a permutation $\pi$ of $\mathbb F_p$ and a function $\sigma:\mathbb F_p\to\mathbb F_p$ such that
$$
f(t+pj)=j\pi(t)+\sigma(t)\quad (0\le t,j<p).
$$
In particular, there are exactly $p!\,p^p$ such sequences with their indices and phases fixed. At length 25 over the fifth roots of unity, the exact number is 375,000.

This is an informal analytic proof of the prime-square case of the generalized Frank classification. It generalizes an August 2026 exhaustive calculation at $p=5$. Mow's unified construction includes this family. His separate conjecture about the maximum possible length of a perfect sequence over an arbitrary root-of-unity alphabet concerns all possible periods. [Mow, Unified construction of perfect polyphase sequences](https://researchportal.hkust.edu.hk/en/publications/unified-construction-of-perfect-polyphase-sequences/) · [Blake, On the non-existence of perfect sequences with the array orthogonality property](https://arxiv.org/abs/2603.13914)

The known constructions include de Launey's and Brock's circulant generalized Hadamard matrices of this order. Tai Do Duc and Schmidt's Theorem 3.6 gives the existence criterion for circulant Butson matrices of prime-power order, with a closely related field-descent and character-basis argument. The classification here uses every nonzero frequency modulo $p$ to recover every column. We found no statement of this exact classification in the sources checked. [de Launey, 1992](https://doi.org/10.1007/BF02351588) · [Brock, 1993](https://doi.org/10.1016/0012-365X(93)90237-N) · [Tai Do Duc and Schmidt, Theorem 3.6](https://arxiv.org/abs/1903.07310) · [Mow's account of the finite search](https://eewhmow.home.ece.ust.hk/download/MyPerfectS.htm)

## Cyclotomic rigidity

Take a primitive $p^2$th root $\xi$ with $\xi^p=\zeta$. Let
$$
X_k=\sum_{x=0}^{p^2-1}\zeta^{f(x)}\xi^{kx},\qquad 0\le k<p^2.
$$
The square modulus $|X_k|^2$ is the Fourier transform of the periodic autocorrelation
$$
R(d)=\sum_{x=0}^{p^2-1}\zeta^{f(x+d)-f(x)}\qquad (d\in\mathbb Z/p^2\mathbb Z),
$$
as seen by expanding the product and collecting terms by the shift $d$. Perfection gives $X_k\overline{X_k}=p^2$.

Write $K=\mathbb Q(\xi)$ and $\mathcal O_K$ for its ring of integers. The rational prime $p$ is totally ramified in $K$, so its unique prime ideal $\mathfrak p$ is invariant under complex conjugation. The equality of principal ideals $(X_k)(\overline{X_k})=(p)^2$ forces $v_{\mathfrak p}(X_k)=v_{\mathfrak p}(p)$ and no valuation at any other prime ideal. Here the equality of the two $\mathfrak p$-valuations follows from conjugation, and the vanishing of the other valuations follows from integrality. Thus $X_k/p\in\mathcal O_K^\times$.

Complex conjugation commutes with every automorphism of $K$, since $K/\mathbb Q$ is abelian. Therefore every conjugate of $X_k/p$ has absolute value one. Kronecker's theorem says that an algebraic integer with this property is a root of unity. Equivalently, the powers of such an integer have uniformly bounded degree and integral minimal-polynomial coefficients, so only finitely many values occur. The roots of unity of $K$ are precisely $\{\pm\xi^a\}$ for odd $p$, and $\{\xi^a\}$ for $p=2$. For example, if a primitive $m$th root of unity belongs to $K$, then adjoining it to $\xi$ generates $\mathbb Q(\zeta_{\mathrm{lcm}(m,p^2)})=K$. Equality of the totients forces $\mathrm{lcm}(m,p^2)=p^2$ or, for odd $p$, $2p^2$. We conclude that $X_k=\pm p\xi^a$, where the sign may be absorbed into $\xi^a$ when $p=2$.

## Recovering the slopes

Write $F=\mathbb Q(\zeta)$. The powers $1,\xi,\ldots,\xi^{p-1}$ form an $F$-basis of $K$, since $[K:F]=p$ and $\xi^p=\zeta$. For $k=1,\ldots,p-1$, write $kt=pq_{k,t}+r_{k,t}$ with $0\le r_{k,t}<p$. The residues $r_{k,t}$ are all distinct as $t$ varies, and the digit decomposition of $x$ gives
$$
X_k=\sum_{t=0}^{p-1}\xi^{r_{k,t}}\zeta^{q_{k,t}}
       \left(\sum_{j=0}^{p-1}\zeta^{f(t+pj)+kj}\right).
$$
The representation $X_k=\pm p\xi^a$ has exactly one nonzero coefficient in this basis, of magnitude $p$. Consequently for exactly one $t=t_k$ the inner sum has magnitude $p$. Equality in the triangle inequality implies that its $p$ unit terms have the same phase. Thus $f(t_k+pj)=-kj+\sigma(t_k)$ for all $j$. The indices $t_k$ are distinct because a function on $\mathbb F_p$ has at most one affine slope. For the one remaining index $t_0$, the inner sums vanish at every $k\in\{1,\ldots,p-1\}$. Fourier inversion on $\mathbb F_p$ now says that $\zeta^{f(t_0+pj)}$ is constant in $j$. This yields the claimed formula with all $p$ slopes occurring once.

## Converse and count

Write a nonzero shift as $d=\delta+pe$ with $0\le\delta,e<p$. If $\delta\ne0$, the low digit changes from $t$ to $t'=t+\delta\bmod p$. In the autocorrelation, for a fixed $t$, the coefficient of $j$ in the exponent difference is then $\pi(t')-\pi(t)\ne0$. The carry into the high digit only affects terms independent of $j$. Summing over $j$ gives zero. If $\delta=0$, then $e\ne0$, and the full autocorrelation is $p\sum_t\zeta^{e\pi(t)}=0$ because $\pi$ runs through all slopes. Every such formula is therefore perfect.

The slopes and offsets are recovered uniquely from $f$ by reading $f(t)$ and $f(t+p)$. There are $p!$ choices of slopes and $p^p$ choices of offsets. At $p=5$, the additional normalization $f(0)=f(1)=0$ fixes two offsets and gives 15,000 sequences, the archived exhaustive count.
