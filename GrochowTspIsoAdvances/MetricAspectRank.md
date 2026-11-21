# Accuracy and metric aspect ratio in TSP formulations

A shared LP relaxation for metric TSP can require $2^{\Omega(\varepsilon^{-1}\log(1+\min\{N\varepsilon,A\}))}$ inequalities to achieve a $1+\varepsilon$ guarantee on $N$ cities with aspect ratio at most $A$. The result holds for $A\ge5$ and any sequence $\varepsilon\to0$. Its hard instances are ordinary Hamming metrics up to a positive common scaling. At $\varepsilon=1/\log N$ and $A\ge N^\delta$ for any fixed $\delta>0$, the bound is $N^{\Omega(\log N)}$. The previous two-distance replication gives $2^{\Omega(\min\{N,1/\varepsilon\})}$, which at this accuracy is a polynomial lower-bound rate.

The bridge to Grochow's use of Newton polytopes is through assignment value reductions. A finite tree of affine guards and compact assignment leaves yields a single LP relaxation on its bounded cost domain. The metric construction below makes the cost of one hard objective proportional to the size of its odd cut, so the LP must factor Sinha's small-cut matching slack matrix. This improves the quantitative formulation bound without a new rank theorem. [Grochow, Lemma 3.1 and Theorem 4.2](https://theoryofcomputing.org/articles/v013a018/) · [Sinha, Theorem 3.3](https://arxiv.org/html/1711.10145)

## Exact Hamming encoding of matching columns

Let $k\ge1$ and let $n\ge2$ be even with $3kn\le N$. Use an ordered label pair $(b,i)\in[k]\times[n]$ for each of $kn$ paths $L_{b,i}$–$D_{b,i}$–$R_{b,i}$. There are also $N-3kn$ padding cities. Choose a perfect matching $M$ on $[n]$. In each block $b$, pair left vertices according to $M$. List and orient all $kn/2$ pairs as $(a_j,b_j)$, where $a_j,b_j$ now denote path labels. Join $R_{b_j}$ to $R_{a_{j+1}}$ cyclically. Following the left pairs, the paths and these right edges gives a single tour. Insert all padding cities along the first of these right edges. Denote the result by $T_M$. The order and orientation can be fixed from $M$ and the labels. In particular, $T_M$ is independent of the cost objective. This uses Yannakakis's matching-to-tour construction, with several separate left cliques and a common right clique. [Yannakakis, proof of Theorem 2](https://www.tcs.tifr.res.in/~prahladh/teaching/2011-12/comm/papers/Yannakakis1991.pdf)

Fix an odd $U\subseteq[n]$ and put $m=|U|$. Choose distinct coordinate unit vectors $e_{b,i}$ and $f_b$. In the Hamming cube put

$$
D_{b,i}=e_{b,i},\qquad L_{b,i}=e_{b,i}+f_b\qquad (i\in U).
$$

Every other city, including every right and padding city, is initially at $O=0$. Call the active $L$ and $D$ cities the ones with labels in $U$. Let $d_U^0$ denote the resulting pseudometric. Its nonzero distances among a single hub and the active cities are

| Endpoints | Distance |
|---|---:|
| $D$ and $O$ | $1$ |
| $L$ and $O$ | $2$ |
| $L$ and its corresponding $D$ | $1$ |
| $L$ and any other active $D$ | $3$ |
| Distinct active $D$ cities | $2$ |
| Distinct active $L$ cities in one block | $2$ |
| Active $L$ cities in different blocks | $4$ |

Write $q(U,M)=|M\cap\delta(U)|$. The target column $T_M$ costs exactly $k(3m+q(U,M))$. Each block has $m$ active forced paths of cost $2$ each. Its left matching uses $(m-q(U,M))/2$ active-to-active edges and $q(U,M)$ active-to-hub edges, all of cost $2$. The right and padding segments have cost zero.

**Optimum identity.** The minimum tour cost for $d_U^0$ is $k(3m+1)$.

To prove the lower bound, shortcut all hub cities except one using the triangle inequality. This leaves a tour on $2km+1$ representatives of no greater cost. Give every active city potential $1$ and the hub potential $0$. The sum over tour edges of the potentials at their endpoints is $4km$. Subtract these endpoint potentials from the distances. The only negative remainders are $-1$ on the $km$ private edges $L_{b,i}D_{b,i}$. The positive remainders are $1$ on nonprivate $LD$ edges or $LO$ edges, and $2$ on $LL$ edges between blocks.

Let $r$ count the omitted private edges. The tour cost is $3km+r$ plus the sum of its positive remainders. A block omitting a private edge contributes at least one to $r$, with different blocks charging distinct omissions. In a block containing all private edges, every one of its $m$ active left vertices has one remaining incident edge. The $m$ incidences cannot all be paired within its active left clique because $m$ is odd. Charge one incidence leaving that clique in each such block. A nonprivate $LD$ edge or $LO$ edge receives at most one charge, and a cross-block $LL$ edge receives at most two. Each has a remainder at least the number of charges it receives. Thus the cost is at least $3km+k$. To attain this, take a perfect matching with exactly one edge crossing $U$. It exists by choosing one cross edge and pairing the remaining vertices separately on the two even sides. Its column $T_M$ attains the lower bound.

To enforce strictly positive distances and aspect ratio at most $A$, let

$$
s=\left\lfloor (A-1)/4\right\rfloor,\qquad \tau=1/s .
$$

Here $A\ge5$, so $s\ge1$. Repeat each coordinate in the Hamming construction $2s$ times and append one separate identity bit for each original city. Dividing the new Hamming distances by $2s$ gives

$$
d_U(v,w)=d_U^0(v,w)+\tau \quad(v\ne w).
$$

Every tour cost increases by exactly $N\tau$. The aspect ratio is at most $(4+\tau)/\tau=4s+1\le A$, and $A\tau\le10$ follows from $\lfloor (A-1)/4\rfloor\ge(A-1)/8$. Consequently

$$
d_U(T_M)=N\tau+k(3m+q(U,M)),\qquad
\operatorname{OPT}(d_U)=N\tau+k(3m+1).
$$

The common normalization does not change approximation factors or the rank bounds. One may cap $A$ at $4N+1$ in the construction for $\varepsilon\le1$ without changing the bound's asymptotic rate. With this cap the unweighted Hamming representation uses at most $2N(kn+k)+N=O(N^2)$ bits per city.

## Aspect-ratio and error tradeoff

**Theorem.** Let $N\to\infty$, with $A=A_N\ge5$ and $\varepsilon=\varepsilon_N>0$ satisfying $\varepsilon_N\to0$. Suppose a polyhedron $Q$ contains the symmetric $N$-city tour polytope and for every Hamming objective $w$ of aspect ratio at most $A$ satisfies

$$
\min_{x\in Q} w\cdot x \ \ge\ \frac{\operatorname{OPT}(w)}{1+\varepsilon}.
$$

Then every LP extended formulation of $Q$ has at least

$$
2^{\Omega\left(\varepsilon^{-1}\log(1+\min\{N\varepsilon,A\})\right)}
$$

inequalities. The multiplicative guarantee is on the original edge-cost objective and the feasible region is shared across all objectives. Equivalently, it suffices to require the guarantee on the normalized Hamming metrics constructed above.

**Proof.** Use the restricted-row result in Sinha's Theorem 3.3. There are fixed constants $0<\beta<1$, $a>0$ and $C_1>0$ such that, for an even source size $n$ and parameter $C_1/n\le u\le1$, the matrix with entries $(q(U,M)-1+\beta)/2$ restricted to odd $|U|\le1+\beta/u$ and all perfect matchings $M$ has nonnegative rank at least $\binom{n}{\lfloor a/u\rfloor}$, with the integer rounding harmless in the asymptotic range below. We use that specified shift $\beta$ and the stated row cutoff. [Sinha, equations before (3.1) and Theorem 3.3](https://arxiv.org/html/1711.10145) · [SODA proceedings](https://doi.org/10.1137/1.9781611975031.104)

Choose $c_0=\beta/240$, a fixed $C\ge\max\{12,C_1,2a\}$, and put

$$
n=2\left\lfloor\frac12\min\{N/3,c_0 A/\varepsilon\}\right\rfloor,\qquad
k=\left\lfloor\frac{N}{3n}\right\rfloor,\qquad
u=C\max\{\varepsilon,1/n\}.
$$

Eventually $n$ is even and at least $2$, $k\ge1$, and $u$ lies in Sinha's range, with $u\to0$. Since $\lfloor x\rfloor\ge x/2$ for $x\ge1$, we have $N/k\le6n$. For each Sinha row, $m\le1+\beta/u$. For sufficiently large $N$ we have $\varepsilon\le\beta/16$, so

$$
\varepsilon(3m+1)\le4\varepsilon+\frac{3\beta\varepsilon}{u}\le\beta/2,
\qquad
\frac{\varepsilon N\tau}{k}\le6c_0 A\tau\le\beta/4.
$$

The gap between the exact optimum and its value divided by $1+\varepsilon$ is therefore at most $k\beta$. The affine inequality $d_U\cdot x\ge N\tau+k(3m+1-\beta)$ is valid on $Q$. At $\chi^{T_M}$ its slack is exactly $k(q(U,M)-1+\beta)$.

If $Q$ is an image of a polyhedron with $r$ inequalities, fix one feasible lift of each $\chi^{T_M}$. For each row, LP duality expresses its valid inequality as a nonnegative combination of those formulation inequalities plus a nonnegative constant, up to the formulation equalities. Evaluating at the fixed lifts yields a nonnegative factorization of the row-column slack matrix with at most $r+1$ terms. Scaling the entire matrix by a positive constant preserves its nonnegative rank. It follows that $r+1\ge\binom n{\lfloor a/u\rfloor}$.

Finally, $n=\Theta(\min\{N,A/\varepsilon\})$. For $n\varepsilon\le1$, $u=C/n$, and the logarithm of the binomial lower bound is $\Omega(n)$. For $n\varepsilon\ge1$, $u=C\varepsilon$, and it is $\Omega(\varepsilon^{-1}\log(1+n\varepsilon))$. These two cases both give $\Omega(\varepsilon^{-1}\log(1+n\varepsilon))$, which is $\Omega(\varepsilon^{-1}\log(1+\min\{N\varepsilon,A\}))$. The exponent tends to infinity, so the one extra factor does not change the asymptotic bound. $\square$

## Consequence for bounded-domain guarded assignment

Use the polyhedral cost domain $W$ defined by edge bounds $\tau\le w_e\le4+\tau$ and all metric triangle inequalities. Every hard normalized distance vector lies in $W$. Suppose a finite binary tree of affine comparisons outputs $g(w)$ with $\operatorname{OPT}(w)\le g(w)\le(1+\varepsilon)\operatorname{OPT}(w)$ on $W$. At a reachable leaf $\ell$, let $g_\ell(w)=\min_{(a,b)\in S_\ell}(w\cdot a+b)$ for a nonempty coefficient-intercept polytope $S_\ell$ with an LP of $s_\ell$ inequalities. This covers a minimum assignment with affine edge costs, where $S_\ell$ is an affine image of a Birkhoff face and $s_\ell$ is at most the square of the assignment order. It also covers a min-plus circuit of compact monotone optimization primitives whose augmented coefficient-intercept polytope has a compact formulation. [Grochow, proof of Theorem 4.2](https://theoryofcomputing.org/articles/v013a018/v013a018.pdf) · [Hertrich–Loho](https://arxiv.org/abs/2411.03006)

For completeness, write $B_\ell w\le d_\ell$ for the weak form of the leaf region including $W$, with $r_\ell$ rows. Since the actual region is nonempty, its closure is given by the weak form. This follows by mixing any weakly feasible point with a point in the actual region. The closed cone generated by $(w,1)$ from the region is $K_\ell=\{(w,t):B_\ell w\le t d_\ell,\ t\ge0\}$. Boundedness gives no nonzero direction with $t=0$. Let $K_\ell^*=\{v:k\cdot v\ge0\text{ for all }k\in K_\ell\}$. The shared relaxation

$$
Q=\{x:(x,0)\in S_\ell/(1+\varepsilon)+K_\ell^*\ \text{for all reachable }\ell\}
$$

contains every tour. Indeed, separation characterizes membership in each sum by the lower inequalities $(w,t)\cdot(x,0)\ge\min_{z\in S_\ell}(w,t)\cdot z/(1+\varepsilon)$ for $(w,t)\in K_\ell$. These hold for tours on the leaf region by the approximation guarantee, and hence on the closed cone by continuity and scaling. For any $w\in W$, the inequality from the actual leaf implies $\min_Q w\cdot x\ge g(w)/(1+\varepsilon)\ge\operatorname{OPT}(w)/(1+\varepsilon)$. Use the negative rows defining $K_\ell$ to generate $K_\ell^*$ with nonnegative multipliers. This yields an LP for $Q$ with at most $\sum_\ell(s_\ell+r_\ell+1)$ inequalities, so the theorem lower-bounds that full expanded budget. The conclusion concerns these guarded value representations with guarantees on $W$.

## Literature and verification

Sinha provides the quantitative rank of the restricted matching matrix. Braun, Fiorini, Pokutta and Steurer define the shared formulation model and exhibit the Held–Karp relaxation for metric TSP. Pokutta's fixed-factor LP lower bounds concern metric perfect matching, $T$-joins and odd cuts. The constructions here encode small odd cuts into Hamming TSP objectives with row-dependent baseline $3k|U|$ and replicated parity charges. A bounded priority search did not establish firstness. The asymptotic result is an informal deduction from the published rank theorem. It does not use the separate semidefinite rank preprint. [Sinha](https://arxiv.org/abs/1711.10145) · [Braun–Fiorini–Pokutta–Steurer](https://arxiv.org/abs/1204.0957) · [Pokutta](https://lemmata.iol.berlin/lp-hardness-in-p/)

Exact integer controls checked all odd sets for $(k,n,N,s)=(1,4,12,1),(2,4,25,7),(3,2,23,2),(2,4,31,3)$. On each of the 26 collapsed objectives, the Held–Karp subset recurrence with a fixed start city at the hub returned $k(3m+1)$. Listing every perfect matching on the chosen labels, forming the specified tour, and computing its unnormalized Hamming length checked all 74 row-column entries against $2sk(3m+q(U,M))+2N$. All 7,154 row-edge distances lay between $2$ and $8s+2$ before normalization.

