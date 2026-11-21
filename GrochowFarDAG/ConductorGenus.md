# Graph isomorphism inside one integral tensor genus

Three fixed primes put ordinary and even graph isomorphism inside a family of integral tensors that are all special-linearly isomorphic over the rationals and over every $p$-adic integer ring. The construction combines scalar recovery from Manin's bilinear Diophantine problem with conductor gluing for invertible modules.

## Theorem

For every $n\ge3$, put $d=n(n-1)+1$. There is a deterministic polynomial-time construction $G\mapsto T_G\in\mathbb Z^{d\times d\times d}$ for simple undirected graphs on $[n]$ with these properties.

1. The integral ordinary transporter from $T_G$ to $T_H$ has exactly $4|\operatorname{Iso}(G,H)|$ elements. The integral special-linear transporter has exactly $|\operatorname{Iso}(G,H)\cap A_n|$ elements. Both sets of maps are explicit.
2. For this $n$, all $T_G$ lie in one $\operatorname{SL}_d^3$ orbit over each of $\mathbb Q$, $\mathbb R$, $\mathbb Z_\ell$ for every prime $\ell$, and $\mathbb Z/m\mathbb Z$ for every $m\ge2$. This extends to all fields and all commutative rings of positive characteristic by base change.
3. Given a promised tensor in the family after arbitrary integral changes of bases, one can recover the graph up to isomorphism in deterministic polynomial bit time. Ordinary tensor isomorphism on this promise is polynomial-time many-one equivalent to GI. On the displayed family, special-linear isomorphism is also GI-hard.
4. The common genus contains at least $2^{\binom n2}/n!$ integral ordinary orbits.

We use the bilinear convention $T\colon U\times V\to W$. A transporter satisfies $C(T_G(x,y))=T_H(Ax,By)$. Passing to the contragredient convention for either input preserves the determinant-one conditions and transporter counts.

## A split order and its modules

Let $D=\{*\}\sqcup\{(i,j):i,j\in[n],\ i\ne j\}$ and use coordinatewise multiplication in $S=\mathbb Q^D$. Form the order $R\subset\mathbb Z^D$ by three congruences.

- Modulo $2$, vectors are constant on each first-coordinate block, with $*$ in its own block.
- Modulo $3$, vectors are constant on each second-coordinate block, with $*$ in its own block.
- Modulo $5$, all coordinates are equal.

Let $a_G$ have anchor entry $1$, entry $2$ on ordered pairs corresponding to edges, and entry $1$ elsewhere. Form $I_G$ by retaining the modulo-$2$ and modulo-$3$ conditions and replacing the modulo-$5$ condition by membership in the line $\mathbb F_5 a_G$. Define $T_G\colon R\times I_G\to I_G$ by multiplication.

All lattices contain $30\mathbb Z^D$ and project onto $\mathbb Z$ on each coordinate by the Chinese remainder theorem. Their indices in $\mathbb Z^D$ are the same since the dimensions of their three reduction images are $n+1,n+1,1$.

For explicit positively oriented bases, order coordinates with $*$ first. Use the first coordinate in each residue block as its representative, and use the anchor for the mod-$5$ line. At each prime, a coordinate's residue is either free or determined by an earlier coordinate. The $i$-th basis column has earlier entries zero and diagonal entry equal to the product of primes at which the $i$-th coordinate is determined. Fill later entries with the least nonnegative CRT solution, using zero at free primes. Elimination of successive first nonzero coordinates proves this is a basis. Its entries are bounded by $30$, so the basis changes and structure constants are computable in polynomial bit time.

## Integral and signed transporters

Over a field $F$, every autotopy of coordinatewise multiplication on $F^D$ has the form
\[
A(x)=uP(x),\qquad B(x)=vP(x),\qquad C(x)=uvP(x)
\tag{1}
\]
where $u,v\in(F^\times)^D$ and $P$ is one coordinate permutation. Indeed $u=A(1)$ and $v=B(1)$ are units since $C(x)=uB(x)=vA(x)$ and the maps are surjective. Dividing by $u,v,uv$ gives a common unital multiplicative linear map. It permutes the primitive idempotents of $F^D$. Conversely (1) preserves the multiplication.

Apply (1) over $\mathbb Q$ to an integral comparison. Coordinate projections of all lattices equal $\mathbb Z$, so $u,v$ have entries in $\{\pm1\}$. The multiplier order of a lattice is unchanged by a coordinatewise scalar translate. The multiplier order of $R$ is $R$, since $R$ contains $1$. Thus $uP(R)=R$ forces $P(R)=R$. Tests of coordinate equality on the mod-$2$ and mod-$3$ reduction images recover the two partitions. Each partition has exactly one singleton, the anchor. Thus $P$ fixes the anchor and acts by separate permutations $\sigma,\tau$ of the two block sets. The missing diagonal forces $\sigma=\tau$, and all diagonal permutations preserve $R$.

Modulo $5$, all coordinates of $u$ equal $u_*$. For $v$, one has $\mathbb F_5 vP(a_G)=\mathbb F_5 a_H$. The anchor forces the line scalar to be $v_*$. Since $1$ and $2$ are in distinct classes of $\mathbb F_5^\times$ modulo signs, the induced $\sigma$ is a graph isomorphism. Then $P(a_G)=a_H$ and all entries of $v$ equal $v_*$. Conversely any graph isomorphism and any two global signs give (1).

Let $s=\operatorname{sgn}(\sigma)$. A vertex transposition makes $1+2(n-2)$ transpositions of ordered pairs, so the induced permutation on $D$ has sign $s$. Since $d$ is odd and the bases have positive equal covolumes within each leg, the three determinants are $(su_*,sv_*,su_*v_*)$. Their product is $s$. They all equal one exactly when $\sigma$ is even and $u_*=v_*=1$. Thus $\operatorname{Aut}_{\rm GL}(T_G)\cong C_2^2\times\operatorname{Aut}(G)$ and $\operatorname{Aut}_{\rm SL}(T_G)\cong\operatorname{Aut}(G)\cap A_n$.

The tree with three pendant paths of lengths $1,2,3$ at its central vertex is asymmetric. Its comparison with an odd relabeling gives an ordinary-positive and special-linear-negative pair. For the GI-hardness reduction to special-linear isomorphism, adjoin two isolated vertices to each graph. They supply an odd automorphism, and padding preserves graph isomorphism by cancellation of the extra isolated vertices. The number of ordinary orbits is at least the number of labelled graphs divided by $n!$.

## One special-linear genus

Compare to the empty graph, which uses $I_{\varnothing}=R$. Over $\mathbb Q$ and $\mathbb Z_\ell$ for $\ell\ne5$, the ambient identity suffices, with determinant one by equality of covolumes. Over $\mathbb Z_5$, choose a tuple of units $b$ with $\bar b$ a scalar multiple of $a_G$ and with coordinate product one. Such a multiple modulo $5$ exists because $\lambda\mapsto\lambda^d$ permutes $\mathbb F_5^\times$ for odd $d$. Lift all but one entry as units and choose the last as the inverse of their product. Multiplication by $b$ maps $R_{\mathbb Z_5}$ onto $(I_G)_{\mathbb Z_5}$ and has determinant one. Use it in the second and third legs and use the identity in the first. Reduce at prime powers and apply CRT for the result modulo $m$.

The displayed generators exhibit each $I_G$ as an invertible module over $R$. The integral orbit of its conductor gluing class records the graph.

## Decode an arbitrary integral presentation

Given $\beta\colon U\times V\to W$, form the left slices $L_x(v)=\beta(x,v)$. Find an invertible $L_h$ by testing $h=(1,t,\ldots,t^{d-1})$ at $d(d-1)+1$ distinct integers. In the split model, the determinant is a nonzero constant times a product of $d$ nonzero linear forms in $h$. Each remains a nonzero polynomial on this curve.

The space $\mathcal S=\{L_xL_h^{-1}:x\in U_{\mathbb Q}\}\subseteq\operatorname{End}(W_{\mathbb Q})$ is conjugate to the full diagonal algebra. Find an element with distinct eigenvalues by the same moment-curve search in a basis of $\mathcal S$, using degree bound $(d-1)\binom d2$ for the product of pairwise eigenvalue differences. Factor its characteristic polynomial over $\mathbb Q$ and compute its one-dimensional eigenspaces. Rational polynomial factorization and the linear algebra operations take deterministic polynomial bit time. [Lenstra–Lenstra–Lovász](https://doi.org/10.1007/BF01457454)

In eigenline coordinates, divide each coordinate of the given output lattice by the positive generator of its projection. Computing those generators amounts to clearing denominators and taking gcds. The resulting lattice is a signed coordinate permutation of $I_G$. Reduce a basis of this lattice modulo $2,3,5$. In the modulo-$2$ image, equality of coordinate functionals identifies the first partition. In the modulo-$3$ image, equality up to sign identifies the second. Distinct blocks have linearly independent functionals. The singleton in the first partition identifies the anchor, and missing intersections give the bijection between the two copies of the vertex set. Normalize the modulo-$5$ line at the anchor. The class of each entry modulo signs recovers the adjacency bit. This gives the reverse reduction for ordinary isomorphism.

## Sources and verification

The workspace source is the integral adjoint-ring construction in the Manin bilinear Diophantine project, which recovers scalar operations in arbitrary-rank integral pairings. The split case uses scalar recovery to read the normalization coordinates of an integral tensor. The other input is gluing a locally rank-one module across a conductor, the construction behind the Units–Picard sequence. Both mechanisms have explicit proofs here. [Manin, §7](https://arxiv.org/html/2007.10632#S7) · [Weibel, Chapter I §3.10](https://sites.math.rutgers.edu/~weibel/Kbook/Kbook.I.pdf)

Grochow–Qiao–Stange–Sun connect integral $2\times2\times2$ tensor isomorphism with quadratic principal ideals. Bhargava and Wood use orientation and balance in low-rank tensor parametrizations. The theorem here gives a growing split family with exact even transporters inside a single special-linear genus. The comparison of ordinary and special-linear tensor actions over finite fields remains open. [Grochow–Qiao–Stange–Sun, Part V](https://arxiv.org/abs/2611.00735) · [Bhargava](https://annals.math.princeton.edu/2004/159-1/p03) · [Wood](https://arxiv.org/abs/1008.4781) · [Chen–Grochow–Qiao–Tang–Zhang, Part III](https://arxiv.org/abs/2306.03135)

The full theorem has a written proof. The accompanying finite control checks explicit integral structure constants and local transporters.
