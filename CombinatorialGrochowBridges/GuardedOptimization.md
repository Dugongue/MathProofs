# From guarded optimization to extended formulations

Grochow transferred extension-complexity lower bounds to monotone projections by showing that a monotone substitution induces a projection from a face of the source Newton polytope. For the permanent, the source is the Birkhoff polytope of bipartite perfect matchings. The target Newton polytopes for general perfect matching, Hamiltonian cycles, and cuts can have exponential extension complexity. This identifies a limitation of reductions that preserve the relevant optimization geometry. [Grochow, Lemma 3.1 and Theorems 4.2–4.5](https://theoryofcomputing.org/articles/v013a018/)

The bridge below extends this geometric approach to a finite decision tree that chooses an optimization routine after inspecting affine comparisons of the objective. A leaf can use a signed affine change of assignment costs. It can even use a model that overstates the target support function outside the leaf's own region. Recession cones identify the directions in which each leaf is valid, and the associated polars let us combine the leaf formulations into a single linear program.

## A sufficient condition for a compact formulation

Write $h_P(w)=\max_{x\in P}\langle w,x\rangle$ for the support function of a nonempty polytope $P\subseteq\mathbb R^d$. For a closed convex cone $K$, use the polar $K^\circ=\{y \mid \langle w,y\rangle\le 0\text{ for all }w\in K\}$. An extended formulation describes a set as the projection of a polyhedron. Its size counts inequalities, with equalities free.

**Theorem.** Let $D\subseteq\mathbb R^d$ be a closed polyhedral cone of admissible objectives. Let $f$ be specified on $D$ by a finite binary decision tree with affine comparisons, with a fixed rule for ties at each node. At each reachable leaf $\ell$, suppose the output has the form

$$
f_\ell(w)=\max_{(q,b)\in T_\ell}\big(\langle w,q\rangle+b\big)
$$

for some nonempty compact set $T_\ell\subseteq\mathbb R^{d+1}$. Suppose $Q_\ell=\operatorname{conv}\{q:(q,b)\in T_\ell\}$ is a polytope with an extended formulation using $s_\ell$ inequalities. Let $r_\ell$ count the oriented comparisons on the root-to-leaf path and the rows defining $D$. If two nonempty polytopes $A,B$ satisfy

$$
h_A(w)\le f(w)\le h_B(w)\qquad(w\in D),
$$

then one can construct a polyhedron $E$ with an extended formulation of at most $\sum_\ell(s_\ell+r_\ell)$ inequalities and

$$
A+D^\circ\ \subseteq\ E\ \subseteq\ B+D^\circ.
$$

In particular, an exact tree for $h_P$ on $\mathbb R^d$ gives an extended formulation of $P$. The bound measures the sum of costs over the reachable leaves in the expanded tree.

**Proof.** Write the nonempty region of leaf $\ell$ using rows $B_\ell w\le b_\ell$, with the appropriate rows interpreted strictly and with the inequalities defining $D$ included. Its cone of recession directions is $K_\ell=\{v:B_\ell v\le 0\}$. Indeed, starting from any point $u$ of that region, such a $v$ preserves all weak and strict inequalities along $u+t v$ for $t\ge 0$. A direction violating a homogeneous row eventually exits the region. Every ray $t v$ with $v\in D$ takes an eventually constant path because each affine predicate on the ray has an eventually constant truth value. Hence $\bigcup_\ell K_\ell=D$.

For $v\in K_\ell$, divide the bounds on $f_\ell(u+tv)$ by $t$ and let $t\to\infty$. Compactness of $T_\ell$ uniformly bounds $\langle u,q\rangle+b$, so the middle term tends to $h_{Q_\ell}(v)$. Compactness also gives the same limiting calculation for $A$ and $B$. Thus $h_A\le h_{Q_\ell}\le h_B$ on $K_\ell$.

Take

$$
E=\bigcap_\ell (Q_\ell+K_\ell^\circ).
$$

The support function of $Q_\ell+K_\ell^\circ$ equals $h_{Q_\ell}$ on $K_\ell$ and is $+\infty$ elsewhere. The sum is closed because $Q_\ell$ is compact and $K_\ell^\circ$ is closed. By separation, the sum is exactly the intersection of the halfspaces $\langle v,x\rangle\le h_{Q_\ell}(v)$ for $v\in K_\ell$. The same description holds for $A+D^\circ$ and $B+D^\circ$, with normals in $D$ and right-hand sides $h_A$ and $h_B$ respectively. The inequalities on each $K_\ell$ and the covering property prove both containments.

By the polyhedral form of Farkas' lemma, $K_\ell^\circ=\{B_\ell^{\mathsf T}\lambda:\lambda\ge 0\}$. Use a copy of the formulation of $Q_\ell$ and impose $x=q_\ell+B_\ell^{\mathsf T}\lambda_\ell$, $\lambda_\ell\ge 0$, for every leaf with the same projected variable $x$. This is the claimed formulation. $\square$

Three useful specializations follow directly.

- **Relative error on nonnegative objectives.** Suppose $P\subseteq\mathbb R_+^d$ is down-closed, meaning $0\le x\le y\in P$ implies $x\in P$. With $D=\mathbb R_+^d$, if $h_P/\alpha\le f\le h_P$ for $\alpha\ge 1$, then $R=\alpha(E\cap\mathbb R_+^d)$ obeys $P\subseteq R\subseteq\alpha P$. Indeed, $(P+D^\circ)\cap\mathbb R_+^d=P$. The nonnegativity constraints add $d$ inequalities.
- **Exact recovery from a restricted cone.** If $a\in\operatorname{int}D$ and $P\subseteq\{x \mid \langle a,x\rangle=b\}$, exactness on $D$ suffices to recover $P$ by adding this single equality to $P+D^\circ$. For any direction $v$, $v+ta\in D$ for all sufficiently large $t$. On that hyperplane $\langle v+ta,x\rangle\le h_P(v+ta)$ reduces to $\langle v,x\rangle\le h_P(v)$ because both sides gain $tb$.
- **Sublinear additive error.** The proof also gives the exact set $P+D^\circ$ if $|f(w)-h_P(w)|=o(\|w\|)$ uniformly as $\|w\|\to\infty$ on $D$. Divide along $u+tv$ for $v\ne0$, then use that support functions vanish at $0$.

## Assignment reductions and dynamic programming

At a leaf, allow an output $a_\ell\cdot w+b_\ell+\max_{X\in F_\ell}\langle M_\ell w+c_\ell,X\rangle$, where $F_\ell$ is the Birkhoff polytope on $m_\ell$ jobs and positions, or a nonempty face obtained by forbidding pairs. Then $Q_\ell=a_\ell+M_\ell^{\mathsf T}F_\ell$. The nonnegativity constraints on $X$ contribute at most $m_\ell^2$ inequalities. Row sums, column sums, and forbidden entries are equalities. The affine cost map $M_\ell$ may have signed entries. An exact optimizer built in this way therefore gives a formulation of size at most $\sum_\ell(m_\ell^2+r_\ell)$ when $D=\mathbb R^d$. This is the assignment-value analogue of Grochow's Newton-polytope transfer, with multiple conditional projections and affine offsets. [Grochow](https://theoryofcomputing.org/articles/v013a018/v013a018.pdf)

A leaf may also be a circuit with affine input forms, maximum gates, addition gates, and multiplication by nonnegative constants. It becomes a support-function circuit after removing input offsets. At each gate this follows from the support-function identities for the convex hull of a union, Minkowski sum, and nonnegative scaling. The finite max-of-affine representation follows by the same recursion with intercepts retained. To bound the formulation size, introduce one real variable per gate. At every maximum gate impose that its variable is at least each of its inputs. Use equalities for addition, scaling, and the affine input forms with offsets removed. Minimizing the output gives the circuit slope because every feasible assignment is coordinatewise at least the true gate evaluations, which themselves are feasible. LP duality expresses the optimum as the support function of the image of a fixed feasible region in the dual variables. Its inequalities are the signs on the dual variables of maximum-gate inequalities. The image has finite support in every direction, so it is bounded and equals $Q_\ell$ by separation. This argument gives a linear-size formulation in the circuit wire count and preserves shared gate computations within a leaf. The per-leaf connection between convex circuits and formulations has established precedents. [Hertrich–Loho](https://arxiv.org/abs/2411.03006) · [Hertrich–Stargalla](https://arxiv.org/abs/2607.11540)

## Arbitrary-depth monotone permanent oracle circuits

Grochow's Question 5.6 asks whether the projection lower bounds extend to monotone algebraic circuits with permanent oracle gates. In the model below they extend to arbitrary depth. This application uses one global linear program for the circuit DAG, with no expansion into decision-tree paths. [Grochow, Question 5.6](https://theoryofcomputing.org/articles/v013a018/v013a018.pdf)

**Theorem.** Consider a finite circuit of binary addition and multiplication gates, nonnegative real constants, variables, and permanent gates $\mathrm{perm}_{m_g}$ with $m_g^2$ input slots. Let $f\ne0$ be the formal polynomial at its output. If $s$ counts ordinary gates and $m_g$ is the matrix order at oracle gate $g$, then

$$
\mathrm{xc}(\operatorname{Newt}(f))\ \le\ 2s+\sum_{g}(m_g^2+1).
$$

More generally, a gate for a nonnegative-coefficient formal polynomial $H$ can replace a permanent gate, contributing $\mathrm{xc}(\operatorname{Newt}(H))+1$ in this bound. The proof uses preservation of support under sums and products of polynomials with nonnegative coefficients. It also works over semirings where sums of nonzero coefficients and products of nonzero coefficients are nonzero, with formal polynomial equality. Examples are formal Boolean polynomials and the ordinary tropical semirings with their absorbing zero. A total order with weak multiplication monotonicity alone does not guarantee the nonzero-product property.

**Proof.** First mark gates computing the zero polynomial. For each nonzero oracle gate $\mathrm{perm}_{m_g}$, omit the input positions with zero polynomial, allowing only permutations using the other positions. A permanent gate is zero exactly when no such permutation exists. A zero summand at an addition gate can be dropped. Products with a zero factor are marked zero. These steps leave the support computation on nonzero gates.

For each nonzero gate $g$, let $z_g(w)=h_{\operatorname{Newt}(f_g)}(w)$. At addition gates $z_g=\max(z_u,z_v)$, since the support is a union. At multiplication gates $z_g=z_u+z_v$, since the support is the sum of the input supports. At a permanent gate $z_g$ is the optimum assignment score with costs $z_{ij}(w)$ on the allowed positions. Replacing an oracle monomial by products of its input polynomials adds their support-function values, and taking the maximum over output monomials gives the claimed score.

Use variables $y_g$ for a single epigraph system. At sums and products use the maximum inequalities and the addition equality described above. At a permanent gate, assignment duality allows the constraints

$$
p_i+q_j\ge y_{ij}\quad((i,j)\text{ allowed}),\qquad
\sum_i p_i+\sum_j q_j\le y_g.
$$

Here $p_i,q_j$ are unrestricted and local to this gate. The block is feasible exactly when $y_g$ is at least the assignment optimum for the input values $y_{ij}$. For a general polynomial gate $H$, its source polytope is the face of $\operatorname{Newt}(H)$ in which coordinates for zero inputs vanish. Each exponent vector is nonnegative, so the face is exactly the convex hull of the surviving monomials. Take any extended formulation of the source polytope and impose those face equalities. Dualizing the LP for its support function gives an epigraph block with one sign constraint per source inequality and one objective inequality. Nonnegative exponents ensure the support function is coordinatewise nondecreasing in the input values.

Set $y_g=w_i$ at each variable $x_i$ and $y_g=0$ at nonzero constants. By monotonicity every feasible gate value bounds its actual $z_g(w)$ from above. The actual values are feasible by LP duality at every oracle gate. Minimizing $y_{\mathrm{out}}$ thus gives $h_{\operatorname{Newt}(f)}(w)$. Dualize this entire minimization. The feasible region of the dual is independent of $w$ and has at most the stated number of sign inequalities. Its objective is $\langle w,x\rangle$ for a linear image $x$ of the dual variables. That image is a closed polyhedron with finite support everywhere and agrees with $\operatorname{Newt}(f)$ by separation. $\square$

Consequently, Hamiltonian-cycle polynomials, general perfect-matching polynomials, and the $q$-cut polynomials in Grochow's theorems for $q\ge 2$ require exponential charged size $s+\sum_g m_g^2$ in this formal monotone model. Depth and reuse of gate outputs are unrestricted. This includes the usual polynomial-size reductions with polynomially bounded query order. The deduction concerns formal polynomials and their supports. Equality only on Boolean evaluations supplies less information and does not meet the theorem's hypotheses. [Rothvoss](https://arxiv.org/abs/1311.2369) · [Fiorini–Massar–Pokutta–Tiwary–de Wolf](https://doi.org/10.1145/2716307) · [Grochow, Theorems 4.2, 4.4, and 4.5](https://theoryofcomputing.org/articles/v013a018/v013a018.pdf)


The same epigraph proof applies directly to optimization circuits. An oracle gate can compute $h_F$ on its predecessor values for any fixed polytope $F\subseteq\mathbb R_+^k$ with a small formulation. Such a gate is coordinatewise nondecreasing and costs at most $\mathrm{xc}(F)+1$ inequalities in the assembled program. This includes assignment, flow over bounded nonnegative flow polytopes, and directed spanning-tree optimization. With affine input forms and maximum and addition gates, each output is a maximum of finitely many affine forms. The homogeneous circuit obtained by removing the offsets supplies the slope formulation for the guarded theorem, so a guarded leaf can compose several such oracle calls.

## Controls and consequences across problem classes

**Two affine regions.** Take $P=[0,1]^2$ and $D=\mathbb R_+^2$. Test $w_1-w_2\ge 1$. On the yes branch return $\max(w_1+w_2,2w_2+1)$, and on the no branch return $\max(w_1+w_2,2w_1-1)$. In each branch the second term is at most $w_1+w_2$. The slope polytopes are the segments from $(1,1)$ to $(0,2)$ and from $(1,1)$ to $(2,0)$, respectively. Maximizing over their union gives $2$ at $(1,0)$, while the correct value is $1$. For the cone construction, the first region contributes the ray $(1,0)$ and the second contributes $(0,1)$. These enforce $x_1,x_2\le 1$. Both cone sums contain $[0,1]^2-\mathbb R_+^2$ by the theorem, so intersecting them with nonnegativity gives the box exactly. The threshold and both intercepts can be checked by the two inequalities $2w_2+1\le w_1+w_2$ and $2w_1-1<w_1+w_2$ on their respective regions. Each branch also has a two-job assignment realization. Put its first term in matrix entry $(1,1)$ and its second in $(1,2)$, with both entries of the second row zero. The two permutation scores are exactly the two terms.

**Nested assignment calls.** With ordinary formal inputs $x,y$, use $q=\mathrm{perm}_2\left(\begin{smallmatrix}x^2&y\\1&1\end{smallmatrix}\right)$ and $r=\mathrm{perm}_2\left(\begin{smallmatrix}qx&qy\\1&1\end{smallmatrix}\right)$. The slope objective is $\max(2w_x,w_y)+\max(w_x,w_y)$, which is also the support function of the four candidate exponent vectors $(3,0),(2,1),(1,1),(0,2)$ obtained by expanding $r$.

**Bipartite assignment and directed spanning trees.** The Birkhoff formulation gives bipartite assignment a quadratic-size, one-leaf assignment primitive. Hertrich and Stargalla prove exponential lower bounds for the same value function in scalar tropical circuits, and also for maximum-weight directed spanning trees. Together with the compact formulations for these polytopes, those bounds show that allowing a polyhedral primitive as a leaf can change the cost of a reduction even in the absence of affine guards. [Grochow, proof of Theorem 4.2](https://theoryofcomputing.org/articles/v013a018/v013a018.pdf) · [Hertrich–Stargalla](https://arxiv.org/abs/2607.11540)

**General matching.** Maximum-weight matching has an exact polynomial-time algorithm. For complete graphs on even $n$, the perfect-matching polytope is the maximum-cardinality face of the matching polytope and has extension complexity $2^{\Omega(n)}$. The theorem forces an exponential total budget for exact guarded assignment-value reductions even when the permitted objectives are only nonnegative, since the matching polytope is down-closed. For approximation, the theorem gives a polyhedral relaxation from a $(1+\varepsilon)$ score guarantee. Braun–Pokutta force an exponential budget for fixed $\varepsilon=c/n$, $0<c<1$. Sinha gives the lower bound $\binom n{\lfloor c'/\varepsilon\rfloor}$ for some absolute $c'>0$ in the range $2/n\le\varepsilon\le1$, with the cost of the final nonnegativity rows included in the budget. A concrete heuristic at factor $2$ sorts edges by value and greedily accepts disjoint edges. Charge each optimum edge to the first accepted edge that blocks it or to itself if accepted. Each accepted edge receives at most two charges from optimum edges of no greater weight. Its full tree of order comparisons can have factorially many leaves, which explains why the formulation bound does not follow from a polynomial bound on comparisons per execution. [Edmonds](https://nvlpubs.nist.gov/nistpubs/jres/69B/jresv69Bn1-2p125_A1b.pdf) · [Rothvoss](https://doi.org/10.1145/3127497) · [Braun–Pokutta](https://arxiv.org/abs/1403.6710) · [Sinha](https://arxiv.org/abs/1711.10145)

**Metric traveling salesperson.** Negate the inputs and output of a min-plus leaf to obtain a max-plus leaf on the negative metric cone. The negative all-ones vector is in that cone's interior, and every undirected tour visits exactly $n$ edges. The exact restricted-cone recovery result therefore applies with $a=-\mathbf 1$ and $b=-n$. Rothvoss's TSP corollary then forces exponential total size even when correctness is asked only on metric costs. The classical subset dynamic program has an exponential number of entries. Metric approximation has different guarantees, exemplified by the deterministic improvement over $3/2$ by Karlin, Klein, and Oveis Gharan. The exact hyperplane argument uses equality of support values and gives no approximation lower bound for that algorithm. [Held–Karp](https://doi.org/10.1137/0110015) · [Rothvoss, Corollary 2](https://arxiv.org/abs/1311.2369) · [Karlin–Klein–Oveis Gharan](https://arxiv.org/abs/2212.06296)

**Independent set and knapsack.** For maximum-weight independent set on a fixed graph, Korhonen bounds pure max-plus dynamic programming using treewidth and maximum degree, with stronger bounds for excluded-minor families. Extension complexity of $2^{\Omega(n/\log n)}$ for some $n$-vertex independent-set polytopes gives a worst-case bound on the expanded guarded model through the theorem. The former bound applies to individual graphs with the stated structural parameters. The latter gives a family with high extension complexity. A positive one-leaf control is 0/1 knapsack with fixed positive integer item sizes $a_i$ and positive integer capacity $W$, where the profits $w_i$ are the objective. For $c\ge a_i$, the update is $V_i(c)=\max(V_{i-1}(c),w_i+V_{i-1}(c-a_i))$. For $c<a_i$, copy $V_{i-1}(c)$, starting with $V_0(c)=0$. This yields a formulation of size $O(nW)$, which tracks the numerical capacity. For graph vertex-subset problems, de Oliveira Oliveira and Van den Broeck obtain tight bounds from solution-preserving dynamic programs on tree decompositions. [Korhonen](https://arxiv.org/abs/2102.06901) · [Göös–Jain–Watson](https://arxiv.org/abs/1604.07062) · [de Oliveira Oliveira–Van den Broeck](https://arxiv.org/abs/2601.06947)

## Verification and priority

Both theorems are informal proofs using separation, Farkas' lemma, and LP duality. The two-region example was also checked at all 441 points $(w_1,w_2)=(i/2,j/2)$ with $0\le i,j\le20$, including 19 points on the guard boundary. The nested-oracle support values were checked at the 441 integer objectives in $[-10,10]^2$. The literature comparison distinguishes the guard-region construction from Grochow's single monotone projection, the established convex-circuit formulation, and tropical approximation lower bounds for pure dynamic programs. The contributions claimed here are the finite affine guard gluing with its explicit total size and support-function guarantees, and the composition argument for formal monotone oracle circuits in the stated model. The latter gives an affirmative answer to Grochow's Question 5.6 in that model. The priority search found related ingredients and models. It did not establish publication priority. [Grochow](https://theoryofcomputing.org/articles/v013a018/) · [Hertrich–Loho](https://arxiv.org/abs/2411.03006) · [Jukna–Seiwert](https://doi.org/10.1137/18M1196339)

