# Graph critical groups as arithmetic tensor obstructions

Let $G$ be a connected undirected graph with a named sink $0$ and $n\ge1$ other vertices. Parallel edges may be specified by positive integer weights. Let $\Delta$ be its reduced Laplacian, and write $K(G)=\mathbb Z^n/\Delta\mathbb Z^n$ for the critical group. The action in this note is the product of the three diagonal tori in specified tensor coordinates. It also has a determinant-one realization on marked tensors.

**Theorem.** From $G$ one can construct in polynomial bit time a three-tensor support and tensors $T_G(r)$, with parameters $r\in(k^\times)^n$, having the following properties over every field $k$.

1. The diagonal transporter $T_G(r)\to T_G(r')$ is the product of two free nonzero scalars and the solution scheme of the multiplicative reduced Laplacian equation $\Delta_\times x=r'/r$. In particular the diagonal stabilizer has character group $\mathbb Z^2\oplus K(G)$, including its group-scheme structure in positive characteristic.
2. For $r_v=t^{b_v}$ over $k(t)$, the orbits are exactly the chip-firing classes $b\in K(G)$. A representative divisor that commutes with all sink-preserving relabelings is obtained by one polynomial-size minimum cut after a rational linear solve. The corresponding firing vector gives an explicit tensor transporter.
3. In the direction of the edges incident to the sink, the least optimal firing vector is periodic up to simultaneous translation of the coordinates. In one period it loses at most one unit at each vertex. A single ordinary parametric minimum-cut instance on $G$ gives the entire nested sequence, with at most $n$ strict changes.

Thus the same graph controls the arithmetic splitting of tensor transporters and the optimization that chooses their integral Laurent representatives. [Baker–Norine, graph divisor classes](https://arxiv.org/abs/math/0608360) · [Chen–Grochow–Qiao–Tang–Zhang, classical-group tensor actions](https://arxiv.org/abs/2306.03135)

## 1. Three tensor slots implement chip firing

Use three coordinate banks, each with an anchor $0$ and a copy of every circuit wire $u$. Each supported triple contributes one multiplicative equation $A_i B_j C_\ell=r'_{ij\ell}/r_{ij\ell}$ on the diagonal entries of the transporter. Include $(0,0,0)$, with ratio $1$, so that $A_0 B_0 C_0=1$. For every non-anchor wire $u$ include $(u,0,u)$ and $(0,u,u)$, with ratio $1$. After dividing by the anchors, these equations identify the two normalized entries in the first and second banks, denoted $x_u$, and set the third normalized entry to $x_u^{-1}$. Put $x_0=1$.

An addition gate $w=u+v$ on the formal exponents uses the triple $(u,v,w)$ with ratio $1$. Its output is a fresh wire, and its equation is $x_w=x_u x_v$. Start with free input wires $1,\ldots,n$. For every vertex $i$ compute wires for the formal exponents
$$
L_i=\deg(i)i,\qquad R_i=\sum_{j\ne i,\ j\ne0} w_{ij}j .
$$
Here a vertex symbol denotes its input wire and multiplication by an integer denotes repeated addition. Use binary doubling and addition for each coefficient. Give both outputs distinct dedicated terminal wires by adding the anchor separately on each side. The last triple $(L_i,0,R_i)$ carries coefficient $r_i$, where its two terminal indices are meant. All other supported coefficients of $T_G(r)$ are $1$. The terminal pair is fresh and its right terminal was computed independently of its left terminal. Thus its triple does not coincide with a gate triple. The copy equations have repeated wire indices and do not collide with a gate with a fresh output. Every gate is now a defined wire, and the last triples impose
$$
(\Delta_\times x)_i=x_i^{\deg(i)}
                    \prod_{j\ne i,\ j\ne0} x_j^{-w_{ij}}
                  =r'_i/r_i .
\tag{1}
$$
The anchors $A_0,B_0$ remain free and determine $C_0$.

These eliminations use only multiplication and inversion of units. They commute with scalar extension and are valid over every commutative $k$-algebra. For instance Smith normal form of $\Delta$ gives invariant factors $s_1,\ldots,s_n$ and a stabilizer isomorphic to $\mathbb G_m^2\times\prod_i\mu_{s_i}$. The group scheme $\mu_{s_i}$ is retained even when the characteristic divides $s_i$. Equivalently the cokernel of the support incidence map has presentation $\mathbb Z^2\oplus K(G)$ by the same eliminations. The circuit has polynomial size in the bit encoding of $G$, and an explicit dense tensor still has polynomial size. A determinant-one version adds a single unused coordinate in each bank and uses its diagonal entry to correct the determinant. One can require all coordinate lines, including the unused ones, to be marked, so the allowed transporters are precisely the coordinate-preserving diagonal maps. The correction is unique and gives the same solution scheme.

For Laurent exponents $r_i=t^{b_i}$, taking the order at $t=0$ sends (1) to $\Delta z=b'-b$ over $\mathbb Z$. Conversely any such $z$ gives a transporter by setting $x_i=t^{z_i}$ and propagating the gates. This proves the chip-firing characterization. The Laurent coefficients and witness can be stored as monomials with binary exponents. In particular any finite abelian group occurs as the torsion part of the character group in this family. Attach one leaf to the sink by an edge of weight (s) for each cyclic summand of order (s). The reduced Laplacian is diagonal with those entries.

## 2. The graph also normalizes the Laurent tensor

For $z\in\mathbb Z^n$, extend by $z_0=0$ and minimize
$$
f_b(z)=\tfrac12 z^{\mathsf T}\Delta z+b^{\mathsf T}z .
\tag{2}
$$
Equivalently minimize the inverse-Laplacian energy of the divisor $b+\Delta z$, up to the fixed scalar term, since
$$
\tfrac12(b+\Delta z)^{\mathsf T}\Delta^{-1}(b+\Delta z)
   =f_b(z)+\tfrac12b^{\mathsf T}\Delta^{-1}b .
$$
Connectedness makes $\Delta$ positive definite, so the integer minimizer set is finite and nonempty. The energy is submodular on the coordinate lattice. Indeed, for each edge, its squared difference satisfies the two-variable Monge inequality. For crossed entries $x_i\le y_i,\ x_j\ge y_j$, the difference between the old edge costs and the costs after coordinatewise meet and join is $2(y_i-x_i)(x_j-y_j)$ before multiplying by its positive weight. Sink and linear terms are modular. The minimizer set is closed under coordinatewise meet and join, so there is a coordinatewise least minimizer $z_b$. Because $f_{b+\Delta u}(z)=f_b(z+u)-f_b(u)$ for every integer $u$, one has $z_{b+\Delta u}=z_b-u$. Thus $b+\Delta z_b$ depends only on the class. Every permutation of vertices fixing the sink transports the coordinate order and the quadratic problem, so the normalizer is equivariant. Equation (1) reconstructs a witness to the normalized tensor. [Bacher–de la Harpe–Nagnibeda, integral cut lattices and their determinant groups](https://www.numdam.org/articles/10.24033/bsmf.2303/)

For $S$ a nonempty subset of nonsink vertices write $c(S)$ for its weighted cut size, including edges to the sink. At any $z$ the two unit moves have costs
$$
f_b(z\pm{\bf 1}_S)-f_b(z)
       =\tfrac12c(S)\pm(b+\Delta z)(S).
\tag{3}
$$
These tests suffice for global minimality. For a general integer increment $h$, write it as positive and negative indicator layers of its entries. Each edge crosses exactly $\lvert h_i-h_j\rvert$ such layers. This number is at most $(h_i-h_j)^2$, and the linear increment is exactly the sum of the signed linear layer increments. Hence the true cost is at least the sum of the costs of the signed layer moves from $z$. If all moves in (3) are nonnegative, $z$ minimizes globally. A negative-direction move with equality precludes being least. Conversely if all negative-direction moves are strict then any smaller integer vector has strictly larger value by the layer argument. Since the minimizers are closed under meet, $z$ is then the least minimizer. In particular the chosen divisor $d=b+\Delta z_b$ is the unique representative satisfying the half-open inequalities
$$
              -c(S)/2\ \le d(S)<c(S)/2
         \quad(\varnothing\ne S\subseteq \{1,\ldots,n\}).
\tag{4}
$$

To get a polynomial-time construction for binary edge weights and binary $b$, let $u=-\Delta^{-1}b$ be the rational unconstrained minimum. At any integer minimizer put $e=z-u$, with $e_0=0$. From (3), the absolute value of $(\Delta e)(S)$ is at most $c(S)/2$. If the maximum of $e$ exceeds $n/2$, the sorted positive entries together with zero have a gap greater than $1/2$. Choose $S$ to be the vertices above the gap. On each crossing edge the potential difference from $S$ to its complement exceeds $1/2$, and there is a crossing edge by connectedness. Their weighted sum is $(\Delta e)(S)>c(S)/2$, a contradiction. The same argument for $-e$ proves $\|z-u\|_\infty\le n/2$.

It suffices therefore to optimize in an integer box centered within one unit of $u$, with a common width $B=2n+2$. Translate each label interval to $\{0,\ldots,B\}$, and introduce ordered Boolean thresholds $X_{i,a}=1[y_i\ge a]$. Impose $X_{i,a+1}\le X_{i,a}$ with large-capacity implication arcs. The equalities $y_i=\sum_a X_{i,a}$ and $y_i^2=\sum_a(2a-1)X_{i,a}$ turn unary terms into linear costs. Each weighted square on an edge, after doubling (2) and expanding, has cross terms of the form $-2w_{ij}X_{i,a}X_{j,b}$. Replace each by
$$
w_{ij}|X_{i,a}-X_{j,b}|-w_{ij}X_{i,a}-w_{ij}X_{j,b}.
$$
The absolute differences are ordinary cut edges. Signed unary costs are cut arcs plus constants. An implication capacity larger than the sum of all finite capacities enforces the thresholds. Choose the inclusion-smallest source side among minimum cuts, given by the source-reachable vertices in a residual maximum-flow network. This gives the least minimizer in the original box and therefore globally. The network size and the rational solve have polynomial bit complexity. This is the ordered-label graph-cut construction specialized to the Laplacian, with the cut bound making the network independent of the numeric size of the divisor. [Ishikawa, exact graph cuts for convex priors](https://doi.org/10.1109/TPAMI.2003.1233908) · [Murota, Discrete convex analysis](https://doi.org/10.1007/BF02680565)

## 3. One parametric cut describes a whole firing period

Set $a=\Delta{\bf1}$. Its entries are the weights of the edges to the sink, so $a\ge0$. Define $b_\lambda=b+\lambda a$ and $z(\lambda)=z_{b_\lambda}$, allowing real $\lambda$ in the optimization. If $\lambda\le\nu$, let $x=z(\lambda)$, $y=z(\nu)$. Submodularity of $f_b$ and nonnegativity of $a$ give
$$
 f_{b_\lambda}(x\vee y)+f_{b_\nu}(x\wedge y)
                      \le f_{b_\lambda}(x)+f_{b_\nu}(y).
$$
By optimality both terms on the left individually have their minimum values. Since $y$ is the least minimizer at $\nu$, the meet must equal $y$. Thus $z(\nu)\le z(\lambda)$. The translation identity gives $z(\lambda+1)=z(\lambda)-{\bf1}$. For $\lambda\in[0,1]$ this forces $z(\lambda)=z(0)-{\bf1}_{S_\lambda}$, where the sets $S_\lambda$ are nested and grow from the empty set to all nonsink vertices.

By (3), $S_\lambda$ is exactly the inclusion-largest minimizer among subsets $S$ of
$$
 c(S)/2-(b+\Delta z(0))(S)-\lambda a(S).
\tag{5}
$$
This is a single $n$-vertex cut problem with fixed edge capacities and monotone unary terms. For example write each unary cost $\gamma_i-\lambda a_i$ on selected vertices as a constant plus a source arc of capacity $U_i-\gamma_i+\lambda a_i$ and a sink arc of capacity $U_i$, with $U_i\ge\max(0,\gamma_i)$. Parametric minimum cut computes its rational breakpoints from rational data. There are at most $n$ strict changes, and translating handles all other periods. The reduced divisor itself is periodic, since $b_{\lambda+1}+\Delta z(\lambda+1)=b_\lambda+\Delta z(\lambda)$. [Gallo–Grigoriadis–Tarjan, parametric maximum flow](https://epubs.siam.org/doi/10.1137/0218003)

## 4. Exact arithmetic and extension degrees

Use integer unimodular matrices to take (1) into Smith coordinates $y_i^{s_i}=u_i$. The $u_i$ are computed by integer monomials in the displayed ratios. Over an algebraic closure all these equations are solvable. Over $\mathbb F_q$ the test is $u_i^{(q-1)/\gcd(s_i,q-1)}=1$ for each $i$. If all pass, the number of transporters is
$$
                    (q-1)^2\prod_i\gcd(s_i,q-1).
$$
This includes the determinant-one marked version with forced corrections.

For a pair defined over $\mathbb F_q$, put $o_i=\operatorname{ord}(u_i)$ and
$$
        M=\operatorname{lcm}_{i}
           \prod_{\ell\mid o_i,\ \ell\ \mathrm{prime}}
                   \ell^{v_\ell(s_i)+v_\ell(o_i)} .
$$
Over $\mathbb F_{q^d}$, the power criterion is equivalent to $o_i\mid(q^d-1)/\gcd(s_i,q^d-1)$. At a prime dividing $o_i$ this says $v_\ell(q^d-1)\ge v_\ell(s_i)+v_\ell(o_i)$. Hence the exact extension-degree spectrum consists of the positive multiples of $\operatorname{ord}_M(q)$, with order one when $M=1$. This description uses orders for its closed form. A specified degree can also be tested in polynomial bit time without building the extension or factoring these orders. In each coordinate compute (q^d-1) modulo (s_i(q-1)). This residue determines its gcd with (s_i), and determines the quotient by that gcd modulo (q-1). Exponentiating (u_i) by that reduced quotient gives the test. For a graph with just a sink and one other vertex joined by eight parallel edges, $\Delta=[8]$. With $q=3$ and $u=-1$, the minimal extension degree is $\operatorname{ord}_{16}(3)=4$.

## Finite controls

Forty-three connected graphs with up to three nonsink vertices and seeded edge weights checked the circuit's support and terminal exponent identities. On those graphs 344 seeded divisors checked the half-open inequalities and the equivariance under integral firing translations. Exhaustive minimization in the certified box agreed with the single-cut profile in 1,720 price queries. A separate 3,306 cyclic-group tests checked the extension divisibility formula. The Lean lemma checks the step from the crossed inequality to the monotonicity of the least optimizer.

The graph critical group, Euclidean cut-lattice methods and parametric cuts are classical. In particular an obtuse superbasis gives minimum-cut closest-point algorithms for this kind of Laplacian norm. [McKilliam–Grant–Clarkson](https://epubs.siam.org/doi/10.1137/140952806) The construction here realizes the full critical group by an explicit three-way support, then uses the same $\Delta$ to recover rational transport, choose equivariant Laurent representatives and compute a whole normalized price period. The action is diagonal in fixed coordinates, or determinant one with the corresponding line marks. Publication priority for this construction remains open.
