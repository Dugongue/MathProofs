# Optimization and polyhedra of tensor transporter degrees

Informal proofs. Fix a finite field $\mathbb F_q$. The inputs are explicit multiplication tensors of finite étale algebras $A,B$ of the same dimension $n$. Write $D$ for the least positive integer such that the two tensors become isomorphic over $\mathbb F_{q^D}$. The approximation objective is $\log D$. A factor $\alpha$ algorithm outputs a successful integer degree $m$ with $m\le D^\alpha$, in binary.

## 1. Reduction to a threshold covering problem

Let $c_A(d),c_B(d)$ be the multiplicities of the degree-$d$ field factors, and put $a_d=c_A(d)-c_B(d)$. An ordinary transporter between the two multiplication tensors normalizes to an algebra isomorphism by multiplying its output map by the inverse of its image of the unit. Over a common splitting field, an algebra isomorphism bijects primitive idempotents and must commute with the appropriate power of Frobenius. The difference of Frobenius fixed-point counts at power $t$ is therefore
$$
\Delta(t)=\sum_{d\mid t}d\,a_d.
$$
A degree $m$ works if and only if $\Delta(mj)=0$ for every positive integer $j$, because fixed-point counts at powers determine the cycle type of a permutation.

One can compute each profile from the raw table using the linear Frobenius map $M:x\mapsto x^q$. Over a splitting field the linear extension of $M$ permutes primitive idempotents, hence
$$
\dim\ker(M^k-I)=\sum_d c(d)\gcd(d,k)
=\sum_{e\mid k}\varphi(e)\sum_{e\mid d}c(d).
$$
Computing the left side for $1\le k\le n$ and applying divisor inversion followed by descending multiples inversion recovers all $c(d)$ in polynomial time for fixed $q$.

Let $N$ be the least common multiple of the field factor degrees on both sides. For every $k\mid N$ set
$$
h_k(t)=\prod_{p^a\parallel k}(1-\mathbf 1_{p^a\mid t}).
$$
The empty product is $h_1=1$. These functions form a basis of rational-valued functions of $\gcd(t,N)$. For a single prime, the functions $1,1-\mathbf 1_{p\mid t},\ldots,1-\mathbf 1_{p^{v_p(N)}\mid t}$ are a triangular basis on the chain of valuations. The product of these bases gives the claim. In that basis
$$
\Delta(t)=\sum_{k\le n} \beta_k h_k(t),\qquad
\beta_k=(-1)^{\omega(k)}
\sum_{\substack{d\le n,\ k\mid d\\ \gcd(k,d/k)=1}}d\,a_d.
$$
This follows by expanding each $\mathbf 1_{d\mid t}=\prod_{p^a\parallel d}(1-h_{p^a}(t))$. Its constant coefficient $\beta_1=\sum d a_d$ is zero because the algebras have equal dimensions.

Restrict $t$ to multiples of $m$. A term $h_k$ vanishes identically on this set if some $p^a\parallel k$ divides $m$. The surviving terms are linearly independent on this set. For each prime, write $b=v_p(\gcd(m,N))$. Only thresholds $a>b$ survive, and the restricted one-prime functions for those thresholds, together with $1$, remain a triangular basis on the valuations $b,b+1,\ldots,v_p(N)$. Each tuple of those valuations is attained by some multiple of $m$. Thus the exact criterion is one clause for each nonzero $\beta_k$,
$$
\bigvee_{p^a\parallel k}(p^a\mid m).
$$
Here all $k$ with nonzero coefficient are at most $n$. The construction takes polynomial time using only factorization of integers at most $n$ and exact linear algebra over the fixed finite field for profile recovery.

Introduce a Boolean variable $x_{p,a}$ for each prime-power threshold $p^a\mid N$. Require $x_{p,a}\ge x_{p,a+1}$, and give each such variable cost $\log p$. Integer feasible vectors correspond to successful divisors of $N$, with objective
$$
\sum_{p,a}x_{p,a}\log p=\log m.
$$
Every positive integer degree has the same feasibility as its gcd with $N$, so an optimum is obtained among these divisors.

## 2. An exact polynomial-time approximation guarantee

Let $r$ be the largest number of distinct prime thresholds in a clause. If there are no clauses, return $m=1$. Otherwise relax $x$ to $[0,1]$, keep the monotonicity inequalities, and encode each clause by $\sum_{p^a\parallel k}x_{p,a}\ge1$. Round every coordinate at least $1/r$ up to $1$ and the other coordinates down. Every clause contains a rounded $1$, and monotonicity is preserved. For any choice of nonnegative costs a rounded coordinate is at most $r$ times its fractional value. This gives a factor $r$ guarantee.

The irrational costs $\log p$ can be handled in polynomial bit time while preserving the exact factor $r$. Let $L$ be the number of threshold variables and replace each logarithm by a positive rational within $\delta<1/(2L(r+1)N^r)$. Use polynomial-time rational linear programming and the rounding rule above. If $m$ is the resulting degree, its true objective satisfies
$$
\log m-r\log D\le L(r+1)\delta.
$$
Both $m$ and $D$ divide $N$. If $m>D^r$, the displayed difference is positive and at least $1/N^r$ by the inequality $\log(a/b)\ge(a-b)/a$ for positive integers $a>b$ and by $m\le N\le N^r$. This contradicts the precision choice. The required precision has $O(r\log N+\log L)$ bits, which is polynomial in the explicit table size. It can be attained with rational arithmetic. Write $p=2^\ell y$ with $1\le y<2$, evaluate $\log y=2\sum_{j\ge0} z^{2j+1}/(2j+1)$ for $z=(y-1)/(y+1)$, and compute $\log 2$ by the same series at $z=1/3$. In both cases the geometric tail is bounded explicitly, and checking the truncation and rounding error takes polynomial bit time.

Consequently the algorithm outputs a successful $m\le D^r$. Since each clause uses distinct primes with product at most $n$, $r=O(\log n/\log\log n)$ as $n$ grows. This follows already from the lower bound $(r+1)!$ on a product of $r$ distinct primes. For bounded $r$ this is a constant approximation of the logarithmic degree.

The same bound applies to the determinant-one problem on inputs with a finite signed degree. Let $D_A,D_B$ be the trace form determinants in the supplied bases. Every algebra isomorphism has determinant $d$ with $d^2=D_A/D_B$. A determinant-one transporter exists exactly when the normalizing algebra isomorphism can have determinant $1$, since a transporter has the form $(u\phi,v\phi,uv\phi)$ with $u,v$ multiplication maps by units. Unequal trace determinants rule out all degrees. In characteristic two, equal trace determinants make every ordinary degree signed-successful. In odd characteristic, if the two algebras are nonisomorphic at base and their trace determinants agree, every ordinary successful degree is signed-successful. Indeed the powered common Frobenius profile cannot consist exclusively of distinct odd cycles. That would force every original cycle to remain unsplit, and then the two original profiles would coincide. An even cycle permits an odd rotation, and two equal odd cycles permit an odd exchange, so the presence of either allows correction of determinant sign. If the algebras are isomorphic at base, test the determinant sign of a base isomorphism and whether an odd base automorphism exists by the same cycle criterion. A successful base sign gives the optimum $1$. When the base sign cannot be corrected, the profiles have distinct odd lengths and exactly the degrees sharing a prime with $N$ give a sign correction. The least is then the smallest prime divisor of $N$, or there is no signed degree if $N=1$. The base isomorphism can be constructed from explicit field factors by splitting the Frobenius fixed algebra into coordinate idempotents and applying the finite-field isomorphism algorithm on matching factors. [Lenstra on constructing finite-field isomorphisms](https://pub.math.leidenuniv.nl/~lenstrahw/PUBLICATIONS/1991b/art.pdf).

## 3. Sharp thresholds for fixed rank

Given a simple graph $G$ on $v$ vertices, choose a distinct odd prime $p_i$ for every vertex, all in $[P,Q]$ with $Q/P\le1+1/v$ and $P$ growing with $v$. Such a cluster can be found deterministically by sieving $[v^3,2v^3)$ and partitioning it into $v$ equal blocks. The prime number theorem and the pigeonhole principle guarantee a suitable block for all sufficiently large $v$. For the finitely many smaller sizes, start with the same interval and repeatedly double its endpoints until the search succeeds.

For an edge $\{i,j\}$ let $M=p_i p_j$. Give $A$ the factor counts $M$ at degree $1$ and $1$ at degree $M$, and give $B$ the counts $p_j$ at degree $p_i$ and $p_i$ at degree $p_j$. Use a direct product of these gadgets over the edge set. Each gadget has the same dimension $2M$ on both sides and contributes $M h_{p_i p_j}(t)$ to $\Delta(t)$. The clauses are exactly the graph edges. For a nonempty hyperedge $S$, the same construction uses the factor of degree $d_J=\prod_{j\in J}p_j$ with multiplicity $M/d_J$ on the $A$ side for $|J|$ even and on the $B$ side for $|J|$ odd, where $M=\prod_{i\in S}p_i$. Its contribution is $M h_M(t)$, so distinct hyperedges give precisely their distinct clauses. Each gadget has dimension $2^{|S|-1}M$ on each side. At fixed rank the explicit tensor sizes remain polynomial. Each field factor can be constructed deterministically using irreducible polynomials over the fixed finite field. [Shoup on deterministic irreducible polynomial construction](https://www.shoup.net/papers/detirred.pdf).

Write $\tau$ for the unweighted minimum cover size, and let $m$ be a successful degree satisfying $m\le D^\alpha$. The chosen primes dividing $m$ give a cover of size at most
$$
\frac{\log m}{\log P}
\le \frac{\alpha\log D}{\log P}
\le \alpha\,\frac{\log Q}{\log P}\,\tau.
$$
Conversely a cardinality approximation of ratio $\alpha$ gives a logarithmic approximation of ratio at most $\alpha\log Q/\log P$ by taking the product of the cover primes. The distortion tends to $1$ and can be absorbed into any fixed approximation gap. One can handle bounded values of $v$ by exact search. This works directly from the input reduction for hardness, and Section 4 gives polynomial recovery of the cover instance from its image in the graph case.

For rank two, the revised OpenAI and community Vertex Cover paper gives a deterministic reduction from 3SAT to simple unweighted graph gaps with ratios tending to $2$. Its Theorem 1.1 has yes cover density below $1/2+1/s$ and no cover density above $1-1/s$, for every fixed integer $s\ge4$. The approximation transfer proves hardness for every fixed $\alpha<2$ for the logarithmic degree on these tensors. The upper bound in Section 2 is exactly $2$. This conclusion uses the October 30 revision as its hardness input. OpenAI's release notes report a Lean formalization of the source gap, while the reduction proved here is informal. [Community-revised Vertex Cover theorem](https://mathcommunity.github.io/oai-math-revised/papers/The-Factor-Two-Hardness-Threshold-for-Vertex-Cover-September-23-2026/paper.pdf), [OpenAI Lean scope note](https://raw.githubusercontent.com/openai/math/main/lean/docs/102.md).

For each fixed $r\ge3$, the classical Dinur–Guruswami–Khot–Regev hypergraph theorem gives hardness for every fixed $\alpha<r-1$ on rank-$r$ instances. The Khot–Regev $r$-uniform result supplies hardness for every fixed $\alpha<r$ using Unique Games, including conversion to unweighted hypergraphs. The September 23 OpenAI Unique Games theorem supplies their required promise on unweighted bipartite unique games. Giving each edge the same weight makes this a restriction of their Conjecture 2.2. Composing the three reductions yields the sharp threshold at every fixed rank, with the recent theorem as an external input. The factor-$r$ algorithm above holds independently of those sources. [Dinur–Guruswami–Khot–Regev](https://arxiv.org/abs/cs/0304026), [Khot–Regev, Sections 2–4](https://cims.nyu.edu/~regev/papers/vc_hard.pdf), [OpenAI Unique Games theorem](https://mathcommunity.github.io/oai-math-revised/papers/The-Unique-Games-Theorem-September-23-2026/paper.pdf).

Without a fixed rank restriction the logarithmic objective is NP-hard to approximate within every fixed factor $\alpha\ge1$ using the classical theorem alone. Choose a fixed integer $r>\alpha+1$ and apply its hardness with an approximation gap strictly between $\alpha$ and $r-1$. The corresponding bound in terms of actual degree is that, for every constant $\alpha$, finding a degree $m\le D^\alpha$ is NP-hard. The rank-dependent algorithm of Section 2 still gives $m\le D^{O(\log n/\log\log n)}$.

For odd $q$ the threshold hardness also applies to determinant-one TI. All the gadget lengths are odd, so Frobenius acts by an even permutation on the geometric idempotents of each algebra. The determinant of its embedding-evaluation matrix is fixed by Frobenius. Its square is the trace-form determinant, and hence the two trace determinants can be made equal by rescaling a single base-field basis vector, in polynomial time. Over $\mathbb F_3$ equality already holds because the only nonzero square is $1$. In characteristic two, one can likewise rescale a basis vector to equalize the trace determinants since squaring is a bijection. The graphs and hypergraphs used for hardness can be taken to have a nonempty edge set, so the constructed pair is nonisomorphic over the base and the signed and unsigned extension spectra agree.

## 4. Exact bipartite optimization from raw tables

The graph clause subclass is recoverable from the raw multiplication tables. Compute the coefficients $\beta_k$ from Section 1. When every active clause is a squarefree product of exactly two primes, the graph on its active primes is determined by these clauses. This includes the graph construction and arbitrary common étale padding on both sides. An exact algorithm for the bipartite case follows by testing bipartiteness and taking a min-cut, with no graph or prime data supplied separately.

For a bipartition $U,V$, give each arc from the source to $i\in U$ capacity $\log p_i$, and each arc from $j\in V$ to the sink capacity $\log p_j$. Give every arc $i\to j$ for an edge a capacity greater than the sum of all vertex capacities. A minimum cut cannot cross an edge arc. Its cover consists of the vertices of $U$ on the sink side and the vertices of $V$ on the source side, with capacity equal to the cover's logarithmic cost. Every cover produces a cut of the same cost.

For an exact integer-capacity implementation let $T=\prod_i p_i$. Every two distinct subsets have distinct products between $1$ and $T$, so their logarithmic costs differ by at least $1/T$. Round each capacity to a common dyadic grid within $1/(4vT)$, choosing the large edge capacity after rounding. The relative order of all cover costs is unchanged. Scale by the common denominator and solve integer min-cut in polynomial time. Returning the product of the selected primes gives exactly $D$ in binary. The cut and an integer flow of matching value give a polynomial-size certificate of optimality, with the same rational interval computation verifying that integer costs preserve the true product order. [Edmonds and Karp](https://doi.org/10.1145/321694.321699).

For arbitrary recovered graphs there is also a factor-two algorithm using rational arithmetic. Initialize rational residuals $z_i=p_i$ and an empty cover. On an uncovered edge $\{i,j\}$, let $a=\min(z_i,z_j)$, divide both residuals by $a$, and place every endpoint whose new residual is one in the cover. At least one new vertex enters on each step. Interpreting $\log a$ as an edge-price increment, the price sums at a vertex never exceed $\log p_i$ and equal it for every selected vertex. Every cover costs at least the sum of edge prices, while the selected cover costs at most twice that sum. For the bit bound, maintain disjoint supports of primes for the residuals of the unselected vertices. The supports start as singletons. A step discards at least one residual and replaces the surviving residual, if any, by the quotient of two rationals on disjoint supports. Each exponent in a live residual therefore belongs to $\{-1,0,1\}$, so the numerator and denominator each divide $T$ and all comparisons and updates have polynomial bit cost. This is an exact arithmetic implementation of weighted vertex-cover primal-dual updates. [Bar-Yehuda and Even](https://www.sciencedirect.com/science/article/abs/pii/0196677481900201).

## 5. The degree polytope and its LP limits

For the graph construction let $P(A,B)$ be the convex hull of the vectors $(\mathbf 1_{p_i\mid m})_i$ over all successful degrees $m$. Each such vector is a cover indicator, and each cover indicator is attained by the product of its selected primes. Thus $P(A,B)$ is exactly the vertex-cover polytope of the recovered graph. The coordinate map $x\mapsto\mathbf1-x$ identifies it affinely with the independent-set polytope. Göös, Jain and Watson give graphs on $v$ vertices with independent-set extension complexity $2^{\Omega(v/\log v)}$. Their lower bound applies to these degree polytopes. The dense tensor input length of the constructed instances is polynomial in $v$, so the lower bound is superpolynomial in that input length as well. [Göös–Jain–Watson](https://arxiv.org/abs/1604.07062).

There is also an approximate LP lower bound for the model in which one relaxation must handle every nonnegative price vector on the prime divisibility coordinates. Let each successful degree have a designated feasible LP point, and for each price vector $c$ require an affine objective agreeing with $\sum_i c_i\mathbf 1_{p_i\mid m}$ on those points. For every cover use the designated point of its prime product. This gives precisely the weighted vertex-cover LP model of Bazzi, Fiorini, Pokutta and Svensson, with the same optimum and gap for every price vector. Their Theorem 1.1 gives infinitely many graphs for which LPs of size $v^{o(\log v/\log\log v)}$ have integrality gap at least $2-o(1)$. The lower bound holds even for auxiliary variables unrelated to the prime coordinates. The result applies to formulations that handle all nonnegative prices simultaneously. [Bazzi–Fiorini–Pokutta–Svensson, Theorem 1.1 and LP model](https://arxiv.org/pdf/1503.00753).

The explicit threshold relaxation already has a sharp worst-case gap at each fixed rank. For the complete $r$-uniform hypergraph on $v$ vertices, every cover has at least $v-r+1$ vertices and the vector with every coordinate $1/r$ is feasible for the relaxation. With the clustered primes their objective ratio is at least
$$
r\left(1-\frac{r-1}{v}\right)\frac{\log P}{\log Q}\longrightarrow r.
$$
Together with the rounding bound, this determines the natural LP's asymptotic gap on the tensor instances themselves, for their actual intrinsic prices.

These transfers concern extension-degree optimization on finite étale multiplication tensors. The vertex-cover clauses, prices, and polytope are explicit mathematical objects in the result. The approximation and polyhedral bounds rely on the attributed source theorems. Priority for this tensor interpretation has not been established.
