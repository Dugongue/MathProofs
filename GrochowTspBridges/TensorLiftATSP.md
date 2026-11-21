# Exact ATSP certificates from projective lifts of tensor blocks

A matrix-space tensor can hide a bipartite graph whose edge labels transport projective points between blocks. In the resulting lifted directed graph, a tour can splice selected copies of a quotient cycle cover and attain an exact lower bound for **all** lifted tours. The central test is whether a product of matrices fixes a projective point. This certifies optima with different choices on different sheets and can operate without building the lifted graph.

The results below have constructive mathematical proofs and finite controls. There is no Lean formalization.

## 1. Recovering the weighted lift

Let $F=\mathbb F_q$. Contract one leg of a 3-tensor and take the image $S\leq L\otimes R$. This is a matrix-space presentation of the independent general-linear action in Grochow and Qiao's Tensor Isomorphism framework. Assume there are decompositions $L=\bigoplus_u U_u$ and $R=\bigoplus_v W_v$ with all summands of dimension $r\geq1$ such that
$$
S=\bigoplus_{uv\in E} S_{uv},\qquad
S_{uv}=F M_{uv}\leq U_u\otimes W_v,\qquad
M_{uv}\colon W_v^*\longrightarrow U_u\ \text{invertible}.
$$
Here $E$ is a simple bipartite support with no isolated vertices. We use the bidirected version of the support, with rational cost $c_a$ on each arc. Costs are additional markings on the recovered quotient. A change of coordinates carries those markings with the arcs. An unweighted tensor can use constant costs.

The displayed decompositions can be recovered from a basis of $S$. Compute the two unital algebras
$$
\mathcal A_L=\{a\in\operatorname{End}(L):(a\otimes 1)S\subseteq S\},
\qquad
\mathcal A_R=\{b\in\operatorname{End}(R):(1\otimes b)S\subseteq S\},
$$
Membership gives linear equations by applying the operator to a basis of $S$ and projecting to the ambient quotient by $S$. The block projections belong to these algebras. The corner associated to a left block consists of scalars because multiplication by its endomorphism has to preserve an incident invertible matrix line $F M_{uv}$. On the right the endomorphism acts by its dual, and the same argument applies. Thus the block projections constitute complete orthogonal systems of primitive idempotents.

In a finite-dimensional algebra, any two complete orthogonal primitive systems are conjugate up to permutation by a unit. To see this, decompose the right regular module as a direct sum of the right ideals of the idempotents. Those ideals are indecomposable because each corner has only trivial idempotents. Krull–Schmidt matches the summands of the two decompositions. The sum of the matching module isomorphisms is left multiplication by a unit and conjugates the projections. Units in each one-sided algebra preserve $S$, as do their inverses. Computing any complete system therefore recovers an equivalent decomposition, and after projecting $S$ to each pair of blocks the uniform size and invertible-line conditions are checkable. The idempotent algorithm is Las Vegas polynomial time, and deterministic polynomial time in the input size and characteristic. [Grochow–Qiao](https://doi.org/10.1137/21M1441110), [Chistov–Ivanyos–Karpinski, Proposition 11](https://theory.cs.uni-bonn.de/marek/publications/85169-cs.pdf), [Couvreur–Debris-Alazard–Gaborit on two-sided matrix-code stabilizer algebras](https://arxiv.org/abs/2011.04611).

The sheets at left vertex $u$ are the projective points of $U_u$ and those at right vertex $v$ are the projective points of $W_v^*$. Each fiber has size
$$
d=(q^r-1)/(q-1).
$$
An arc $v\to u$ transports a point by $[M_{uv}]$ and its reverse by $[M_{uv}^{-1}]$. A lifted arc has the cost of its quotient arc. A scalar multiple of $M_{uv}$ gives the same transport. Independent block coordinate changes conjugate the transports at their endpoints and give a lift isomorphism by relabeling the fibers. In particular, right changes of basis induce the inverse dual change on the corresponding sheet coordinates. This gives a permutation-voltage cover determined by the marked blocks. [Gross–Tucker on permutation voltage covers](https://doi.org/10.1016/0012-365X(77)90131-5), [Cavaleri–Donno on switching and closed-walk gains](https://arxiv.org/abs/2111.12428).

## 2. Assignment and a global-optimum splicing theorem

A directed cycle cover of the quotient chooses exactly one incoming and outgoing arc per vertex. Find a minimum-cost cover $C$ by bipartite assignment, or provide it with feasible assignment potentials $p_u,h_v$ satisfying $p_u+h_v\leq c_{uv}$ on every allowed arc and equality on every arc of $C$. Put $B=\sum_u (p_u+h_u)=c(C)$ and $\rho_{uv}=c_{uv}-p_u-h_v\geq0$. Any Hamiltonian cycle in the lift has cost $dB$ plus the sum of its reduced arc costs, since all $d$ sheets at each vertex have one arc entering and one leaving. This argument applies to any choice of different outgoing arcs at different sheets.

Write the cycles of $C$ as $C_1,\ldots,C_t$, with $t\geq2$, and assume each one's lift is a single directed cycle on all its sheets. For every $j$, define $\delta_j$ as the minimum reduced cost of an allowed arc from a vertex of $C_j$ to a vertex outside $C_j$. The certificate below uses only instances where all these minima are finite. Every lifted Hamiltonian cycle leaves each of these $t$ parts at least once, so its cost is at least
$$
dB+\sum_{j=1}^t\delta_j.
$$

**Splicing theorem.** Order the parts cyclically. In each $C_j$ choose a tail $u_j$ with successor $w_j$, and denote its cover-arc transport $u_j\to w_j$ by $P_j$. Suppose the quotient has a cross arc $u_j\to w_{j+1}$ of reduced cost $\delta_j$ for every $j$ (indices cyclic), with transport $A_j$. Set
$$
\tau_j=P_{j+1}^{-1}A_j,\qquad
T=\tau_t\cdots\tau_1.
$$
The projective maps $\tau_j$ go from the sheets at $u_j$ to those at $u_{j+1}$. If $T$ fixes a projective point, the lifted ATSP optimum is $dB+\sum_j\delta_j$.

**Proof.** Take a fixed point $x_1$ and set $x_{j+1}=\tau_j x_j$. In lifted cycle $j$, cut the arc from $(u_j,x_j)$ to $(w_j,P_j x_j)$. This produces a directed path through every sheet in that part. The cross arc from $(u_j,x_j)$ ends at $(w_{j+1},A_j x_j)=(w_{j+1},P_{j+1}x_{j+1})$, the start of the next path. Connecting the paths in order gives one Hamiltonian cycle. Its reduced costs are exactly the $\delta_j$, proving optimality. If $d>1$, the constructed tour uses one copy of each selected cross arc even though that arc has $d$ lifted copies. [Karp's assignment patching gives the antecedent at the level of explicit directed TSP instances](https://www2.eecs.berkeley.edu/Pubs/TechRpts/1978/28924.html).

When the cover is one quotient Hamiltonian cycle, a transitive return transport suffices by the same assignment bound, with value $dB$ and no cuts. The theorem above also applies when the minimum cover partitions the quotient and the globally optimal solution uses different arc choices on different sheets.

## 3. Computing and checking the certificate without listing sheets

The lift of any quotient cycle breaks into directed cycles indexed by the orbits of its cyclic return transport on one fiber. Each trip around the quotient applies the return map once. Thus a quotient cycle lifts to a single cycle exactly when its return map acts as a $d$-cycle.

For a matrix representative $H\in\operatorname{GL}(r,q)$ this last condition is testable arithmetically. Transitivity implies no nonzero proper invariant subspace, so $F^r$ is simple as an $F[X]$-module with $X$ acting by $H$. Hence the characteristic polynomial is irreducible. Under that condition, identify $F^r$ with $\mathbb F_{q^r}$ and $H$ with multiplication by a nonzero field element. The projective points are the cosets of $F^\times$, so multiplication is a single $d$-cycle exactly when the class has order $d$. Given the verified prime factorization of $d$, check $H^d$ is scalar and $H^{d/\ell}$ is nonscalar for each prime divisor $\ell$ of $d$. The checks use polynomially many bit operations in the succinct input size under the usual finite-field representation. Factorization of the integer $d$ is a separate input requirement for this bound. Trial division or explicit orbit enumeration yields unconditional finite alternatives with larger runtimes. [Singer's cyclic collineation](https://doi.org/10.1090/S0002-9947-1938-1501951-4), [Snapper on linear transformations in affine and projective geometries](https://www.cambridge.org/core/journals/canadian-journal-of-mathematics/article/periodic-linear-transformations-of-affine-and-projective-geometries/9752622D952412545B1FA68222214639).

The splice test requires a single fixed point of $T$, rather than transitivity. A lift of $T$ to a matrix fixes a projective point exactly when it has an eigenvalue in $F_q$. Test this by the degree of $\gcd(\chi_T(X),X^q-X)$, reducing $X^q$ modulo the characteristic polynomial by repeated squaring. A witness consists of a nonzero eigenvector, whose existence can also be certified directly. To construct one, find a root of that gcd and solve the homogeneous eigenvector equations. Enumerating field elements is deterministic for fixed $q$, and standard Las Vegas finite-field polynomial factorization works with variable $q$. Given the choice of crossing arcs, the proof stores only a quotient cover, potentials, matrix products, and the chosen vectors. Printing the full tour takes time proportional to its lifted length, as each sheet must be listed. [Cantor–Zassenhaus on finite-field polynomial factorization](https://doi.org/10.1090/S0025-5718-1981-0606517-5).

For discovery, assignment supplies a tight cover and the $\delta_j$. Candidate splices can be tried by fixing an order of the parts and enumerating a predecessor tail per part from minimum-cost crossing arcs. Polynomial verification applies per candidate. A polynomial search over all covers, orders, and tails is outside this result. For the single-cycle case, the Held–Karp subset recurrence can track the product of gains along each partial path and filter completed cycles by transitivity. That variant remains an exponential search on the quotient and may maintain many distinct group elements per state. [Held–Karp](https://doi.org/10.1137/0110015).

## 4. Several cuts and exact controls

Fix a splice template $(P_j,A_j)$ as above. If only cover arcs and these selected cross arcs may be used, let $X_j$ be the set of sheets at $u_j$ which take the cross arc. A degree-feasible selection has $X_{j+1}=\tau_j X_j$, since the start vertices vacated in the next part are exactly the new cross-arc targets. Thus all $|X_j|$ equal a number $s$ and $T X_1=X_1$. A spanning tour requires $s>0$. For nonempty selections, let $\sigma_j$ send each member of $X_j$ to its successor in the cyclic order of the cover lift at $u_j$. Traversing a segment after using cross arc $j$ gives the transition $\sigma_{j+1}\tau_j$ between selected tails. The splice is Hamiltonian exactly when the first-return permutation
$$
(\sigma_1\tau_t)(\sigma_t\tau_{t-1})\cdots(\sigma_2\tau_1)
$$
is one cycle on $X_1$. Every component of the modified cover contains a selected tail and visits every part before returning, which proves the criterion. Its cost if Hamiltonian is $dB+s\sum_j\delta_j$. Large field instances can supply exponents of the Singer cycle for the selected points to certify their cyclic order by powering and sorting. This is a witness check. Finding those exponents efficiently is a separate problem.

Consider two disjoint directed four-cycles $(0,1,2,3)$ and $(4,5,6,7)$, with cross arcs $0\to5$, $4\to1$ and all reverses available. Even vertices are the left part. Set $q=r=2$ and use projective points labeled $0,1,2$. Write $g=(0\ 1\ 2)$, represented by $\left(\begin{smallmatrix}0&1\\1&1\end{smallmatrix}\right)$ in the ordering of point representatives $(1,0),(0,1),(1,1)$. The cover arc transports are the identity except $3\to0$ has $g$ and $7\to4$ has $g^{-1}$. Costs are $1$ on cover arcs, $2$ on forward crosses and $8$ on all reverse arcs. Reverse transports are inverses. These labels give invertible tensor lines under the convention of Section 1.

- **Identity crossing control.** Both forward crosses have identity transport. The potentials $p_u=1,h_u=0$ give $B=8$ and the two exit minima are $1$. The splice return is the identity, and the exact lifted optimum on $24$ vertices is $26$. A quotient Hamiltonian cycle must traverse both connectors and the length-three path in each square between their endpoints. The two products along these paths are inverse, for either direction of traversal. Thus every quotient Hamiltonian cycle has trivial return transport in this control, and a single quotient tour cannot account for the lifted optimum.
- **Shifted crossing control.** Change only the transport on $0\to5$ to $g$ and adjust its reverse. The splice return is $g$, so a nonempty invariant cut set is the full three-point fiber. Any tour using a reverse arc already costs at least $24+7=31$. Any remaining tour uses the template and therefore costs at least $24+3(1+1)=30$. With all three sheets selected, the spliced quotient traverses the two original return transports and the shifted cross, giving $g$ as its return product. The resulting lift is Hamiltonian and the exact optimum is $30$.

As a finite control, a depth-first enumeration on the explicit $24$-vertex lifts followed every outgoing arc to an unvisited sheet, starting at $(0,0)$, and checked the final return arc. It found six tours with minimum $26$ in the identity case and two tours with minimum $30$ in the shifted case. The preceding lower bounds and witnesses establish both values independently of enumeration.

Permutation lifts, projective cyclic collineations, and patching of assignment covers have separate precedents. The proposed bridge combines them with recoverable tensor blocks to certify the global optimum of a succinct lifted ATSP instance using the quotient geometry and assignment dual. Priority for this combination remains unverified.
