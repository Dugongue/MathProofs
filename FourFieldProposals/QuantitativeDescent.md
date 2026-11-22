# Quantitative witness descent

**Proposed field.** Quantitative witness descent studies the resources required to realize several compatible observations by one global witness. Witnesses are mathematical objects with a specified construction cost, such as factorization width, Lipschitz constant or circuit size. The central question is how the cost of a *single* witness varies with allowed observation error, when each local observation already has a cheap witness and a global realization exists. Finding that realization and certifying its cost are parts of the same problem.

## Objects, morphisms and equivalence

Fix a category of regions and restriction maps, with specified finite covers. A witness system consists of a metric presheaf $X$ of observations, a presheaf $W$ of witnesses, and a natural evaluation map $q:W\to X$. Restrictions of observations are 1-Lipschitz. A budget poset $P$ indexes increasing subsets $W_{\le b}(U)\subseteq W(U)$, with restrictions preserving the budget. The witness sets at different regions may contain different kinds of data. For example, a boundary witness can be a map on a subcomplex, while a global witness is a map on the whole complex.

For a cover $U_i\to U$ and assigned observations $x_i\in X(U_i)$, the basic invariant is the upward-closed set
$$
 \mathcal D(x)=
 \left\{(b,\epsilon_1,\ldots,\epsilon_s):
 \exists w\in W_{\le b}(U),\
 d_{U_i}\bigl(q(w)|_{U_i},x_i\bigr)\le\epsilon_i
 \text{ for every }i\right\}.
$$
One can ask separately for the analogous regions where each $x_i$ uses its own witness. Descent measures the difference between the joint region and these separate regions. Each explains something the unrestricted existence of a lift, or pairwise agreement of the local observations, leaves undecided.

On the same observation site, an exact morphism induces natural maps on observations and on witnesses commuting with evaluation, preserves the budget, and is 1-Lipschitz. A controlled morphism replaces the budget condition by a specified monotone regrading and allows a specified Lipschitz constant. Isomorphism is strict equivalence. Mutual controlled morphisms inverse on observations give mutual bounds on the frontier, with the regradings and constants retained as data. This distinction matters when the exact thresholds themselves are of interest.

The framework admits a basic composition law for finite coverings. Suppose a local assignment has overlap error at most $\delta$ on the common refinements. A uniform inner repair rule for a finer cover of each coarse region takes local budget $b$ and overlap error $\delta$ to one witness on that region, with budget at most $g(b,\delta)$ and observation error at most $e(b,\delta)$ on its fine pieces. Assume that the outer repair rule accepts the resulting coarse observations with the overlap error tested on those same common fine restrictions. The reconstructed coarse observations have overlap error at most $\delta+2e(b,\delta)$ by 1-Lipschitz restriction and the triangle inequality. If outer repair has output budget at most $G$ and error at most $E$ at these inputs, the composed output has budget at most $G$ and error at most $e(b,\delta)+E$ on the fine pieces. Thus uniform bounds on cost and error can be composed even when intermediate observations have to change. With exact repairs the two error terms vanish.

Even all proper subfamilies can lose the joint budget. For a finite set $U$ of $n\ge2$ sites, take the full observation and witness presheaves of binary assignments on subsets, and let evaluation be the identity. In one system every assignment has cost one. In another, every assignment on a proper subset has cost one, while a full assignment has cost one if its parity is even and cost $M$ if its parity is odd. Restrictions preserve cost. The images of the cost-one full witnesses onto every proper subset are the same in both systems, since an unobserved bit can fix the parity. The full unbudgeted realizations are also the same. Yet an observed odd full assignment has minimum cost one in the first system and $M$ in the second. This proves that no invariant retaining only those proper marginal images and the existence of unrestricted global witnesses can recover the cost of simultaneous realization.

## First theorem: a graph determines the cost of gluing identical positive observations

Let $G$ be a finite simple graph on $n$ vertices. An observation on an edge is the $2\times 2$ principal matrix with both diagonal entries and the off-diagonal entry equal to one. Every vertex observation is one. Global witnesses are decompositions $A=\sum_\ell a_\ell a_\ell^{\mathsf T}$, with $A$ real symmetric and diagonal one. Restriction takes principal submatrices. The budget $k$ means every vector $a_\ell$ has at most $k$ nonzero entries, so $A$ lies in the established factor-width cone $\mathrm{FW}_k$. An edge error at most $\epsilon$ means $A_{ij}\ge 1-\epsilon$, since the other inequality $A_{ij}\le1$ follows from positivity. Each exact edge observation has width two. All overlaps agree, and the all-ones matrix supplies an unrestricted exact global realization. [Boman, Chen, Parekh and Toledo on factor width](https://doi.org/10.1016/j.laa.2005.03.029)

**Theorem.** The least exact global width is the largest connected component size of $G$. If $G$ is connected, has at least two vertices, and has Laplacian spectral gap $\lambda_2$, then every width-$k$ global witness with edge error at most $\epsilon$ satisfies
$$
 k \ \ge\ n-\frac{2|E(G)|\epsilon}{\lambda_2}.
$$
If $G$ is vertex- and edge-transitive of degree $\Delta>0$, let $B$ be its adjacency matrix and put $\rho_k(B)=\max_{1\le|S|\le k}\lambda_{\max}(B[S,S])$. The least achievable edge error at width $k$ is exactly
$$
 \epsilon_{\min}(k)=1-\frac{\rho_k(B)}{\Delta}
 \qquad (1\le k\le n).
$$
This characterization does not require a method for evaluating the sparse eigenvalue efficiently on arbitrary input graphs.

**Exact case.** Write $A$ as the Gram matrix of unit vectors $v_i$. On an exactly glued edge their inner product is one, so they coincide. Thus on each connected component $C$ the principal matrix is the all-ones matrix $J_{|C|}$. Every rank-one positive summand of $J_{|C|}$ has range in the span of the all-ones vector, by testing vectors orthogonal to it. The block therefore has factor width $|C|$. The block-diagonal completion with these all-ones blocks achieves the maximum of these widths. In the connected case this also proves uniqueness of the unrestricted positive semidefinite completion.

**Noisy bound.** Put $\bar v=n^{-1}\sum_i v_i$. For an edge, $\|v_i-v_j\|^2=2(1-A_{ij})\le2\epsilon$. Apply the Laplacian Poincaré inequality to each coordinate and sum, giving
$$
 \sum_i\|v_i-\bar v\|^2\le 2|E(G)|\epsilon/\lambda_2.
$$
The left side is $n-n\|\bar v\|^2$. Hence $\mathbf 1^{\mathsf T}A\mathbf 1=n^2\|\bar v\|^2\ge n^2-2n|E(G)|\epsilon/\lambda_2$. In a factorization of width $k$, Cauchy–Schwarz gives $(\mathbf 1^{\mathsf T}a_\ell)^2\le k\|a_\ell\|^2$. Summing gives $\mathbf 1^{\mathsf T}A\mathbf 1\le k\operatorname{tr}A=kn$, which proves the claim.

**Exact noisy frontier in the transitive case.** Each $k$-sparse summand satisfies $a_\ell^{\mathsf T} B a_\ell\le \rho_k(B)\|a_\ell\|^2$. Consequently
$$
 2|E(G)|(1-\epsilon)\le\operatorname{tr}(BA)\le n\rho_k(B).
$$
Regularity supplies $2|E(G)|=n\Delta$. For attainment, choose a unit vector $a$ realizing the maximal Rayleigh quotient and supported on $S$. Average $n aa^{\mathsf T}$ over graph automorphisms. The average stays in $\mathrm{FW}_k$, has diagonal one by vertex transitivity and trace, and has constant edge value by edge transitivity. Its pairing with $B$ is $n\rho_k(B)$. This attains the bound.

For the complete graph $K_n$, the error is $(n-k)/(n-1)$. For the cycle $C_n$ and $k<n$, it is $1-\cos(\pi/(k+1))$. In the cycle every proper induced subgraph is a union of paths, and the largest Rayleigh quotient is attained by $k$ consecutive vertices, a path with largest eigenvalue $2\cos(\pi/(k+1))$. Every edge in either graph has the same local matrix. Both covers have zero overlap discrepancy and the same unique exact PSD completion. Their width-error frontiers are nevertheless different. At fixed small error, complete-graph width grows linearly in $n$, while cycle width is of order $\epsilon^{-1/2}$ once $n$ is large enough. By the portfolio's degree-constrained SOS theorem, requiring each completing homogeneous quadratic to be a coefficient limit of sums of squares of separation rank at most $r=2,3$ and total degree at most $2d$ is exactly the width budget $k=\min(n,rd)$. Thus the same examples explicitly compute a gluing cost with both approximation degree and a restriction on square roots. See the accompanying proof entitled Degree-constrained sum-of-squares tensor ranks.

## A topological instance

Take $W(U)=\operatorname{Lip}(U,Y)$ for a fixed compact piecewise Euclidean target $Y$, with Lipschitz constant as budget and the induced subset metrics on the source, so restriction preserves the budget. Boundary values are observations. For one observed region $A\subset U$, the resulting frontier gives the least Lipschitz constant of an exact or approximate extension. By the portfolio's Lipschitz extension theorem, rational H-space type through degree $d$ is precisely the condition for computable uniform exact lifting budgets on every fixed finite source pair of dimension at most $d+1$. At the first failing degree, one fixed pair already has extendable maps whose required budgets cannot be bounded by any total computable function of the boundary budget. This is the same formal uniform budget question in a domain where spectral dual prices give way to undecidability. The theorem invoked here is an earlier written result, while the graph frontier above has the elementary proof included here. [Portfolio Lipschitz extension theorem, Section 1](https://github.com/Dugongue/MathProofs/blob/d6933df162f8e998f27e007a42b8b6e55bb4858b/ManinTop20/ManinNewProofs.md)

## What would make this a field

The proposed common objects are witness spaces, observation maps and joint resource-error frontiers. The foundational questions are which frontiers can be realized on a fixed site, which structural decompositions of a site give uniform repair moduli, and when dual obstructions completely characterize the cost of simultaneous realization. Further domains include positive factorizations of marginals, distributed proof certificates, and prescribed-boundary topological fillings. A test of the proposed scope is whether a theorem about compositional cost in one of these domains can be transported to another by a controlled morphism.

Standard contextuality uses the existence of global sections, and metric sheaf consistency measures discrepancies among given local sections. Both supply tools for this question. Contextuality also has quantitative simulation costs, including the rank of contextuality. Here one instead asks for the cost of a common witness even for observations with a valid noncontextual realization, using resource models that can include geometric complexity rather than contextuality itself. The defining extra data here are the realization map and the resources of a common hidden witness, so the cost can change even for equal, globally realizable local observations. Matrix completion supplies the relevant feasibility problem, and integrality or relaxation gaps can express particular instances after an optimization model has been chosen. The proposed field would treat the observation maps, resource regradings and composition laws themselves as mathematical variables across models. The definition can be encoded using filtered presheaves. Its case for being a separate field depends on whether the resulting cost theorems transfer between domains. No literature search establishes priority of the definition or of the graph formula. [Abramsky and Brandenburger](https://arxiv.org/abs/1102.0264) · [Robinson’s metric consistency filtration](https://arxiv.org/abs/1805.08927) · [Rank of contextuality](https://doi.org/10.1088/1367-2630/acdf78) · [Laurent and Varvitsiotis on PSD completion and rigidity](https://doi.org/10.1016/j.laa.2014.03.015)
