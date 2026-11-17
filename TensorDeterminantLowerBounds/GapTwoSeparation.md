# Exact probe lower bounds for determinant-constrained tensor isomorphism

These are informal lower bounds in an explicit model for working with relative determinant signs over $\mathbb F_3$. They concern all three adjacent comparisons. They leave arbitrary deterministic polynomial-time many-one reductions open.

## 1. Model

Let $V=\mathbb F_2^r$ and suppose a nonempty affine subspace $D\subseteq V$ is hidden. An algorithm must decide whether $0\in D$. It may query $D$ adaptively. At a query it may supply a disjunction of any finite number of alternatives. Each alternative chooses any finite number $t$ of independent signs $d_1,\ldots,d_t\in D$ and any finite number of independent signs $h_1,\ldots,h_s$ from $H=\operatorname{dir}(D)$, the direction subspace of $D$. It asks whether

$$
 L_1d_1+\cdots+L_t d_t+M_1h_1+\cdots+M_sh_s+b\in C ,
$$

where $L_i,M_j:V\to\mathbb F_2^k$ are any linear maps, $b\in\mathbb F_2^k$, and $C$ is any known affine subspace. The query returns the OR of these feasibility bits. An empty disjunction or an infeasible constant alternative can be included, with the usual Boolean meanings. The number of alternatives, copies, and all preprocessing in this model are unrestricted. The algorithm's direct information about $D$ is limited to query answers. Translates or linear images of the individual copies can be absorbed into $L_i,b$, and fixed independent auxiliary determinant freedoms are included in $C$. For an ordinary-isomorphic tensor pair, source and target stabilizers have the same sign image because they are conjugate. This common image is precisely $H$.

In particular a query can test whether $D$ intersects any affine subspace of codimension at most $k$. It can also test signs of arbitrarily many independent copies of the same input in a single query, provided the only sign constraint has at most $k$ output bits in each alternative. If a construction tests extra sign-dependent conditions before activating an alternative, those tests must also be charged as queries for this model to apply.

## 2. Deterministic adaptive lower bound

**Theorem.** For $1\le k\le r$, any exact algorithm in this model uses at least

$$
 \left\lceil\frac{2^r-1}{2^k-1}\right\rceil
$$

queries on some input. For $k=0$, the query answers are identical for all nonempty $D$, so no number of queries suffices when $r\ge1$.

Run the algorithm on the yes input $D=V$. For every nonzero linear functional $\ell\in V^*$, let

$$
 D_\ell=\{d\mid\ell(d)=1\}.
$$

These are $2^r-1$ distinct no inputs. Along the transcript for $V$, an unsuccessful query also fails for every $D_\ell$ by inclusion $D_\ell\subseteq V$. For a successful query choose one successful alternative on $V$. If the full query fails on $D_\ell$, so does that alternative.

Fix this alternative. Write $C=c+W$ in the target space $Y=\mathbb F_2^k$, and take any $a\in D_\ell$. The image of all choices on $D_\ell$, after allowing the slack $W$, is the affine subspace

$$
 b+\sum_i L_i a + W+\sum_i L_i(\ker\ell)+\sum_jM_j(\ker\ell).
$$

The alternative succeeds exactly when this affine subspace contains $c$. If it fails, a nonzero functional $\lambda\in Y^*$ vanishes on $W+\sum_iL_i(\ker\ell)+\sum_jM_j(\ker\ell)$ and takes value one on $c-b-\sum_iL_i a$. Consequently every pullback $L_i^*\lambda$ and $M_j^*\lambda$ is either $0$ or $\ell$. At least one is nonzero. Otherwise $\lambda$ vanishes on $W+\sum_i L_i V+\sum_j M_jV$, and success on $V$ would give $\lambda(c-b)=0$, contradicting the separating value. Thus a particular $\lambda$ can certify failure of this same alternative on at most one $D_\ell$. There are at most $2^k-1$ candidates for $\lambda$.

Each query on the transcript for $V$ therefore distinguishes at most $2^k-1$ of the no inputs from $V$. If some $\ell$ is never distinguished, the adaptive algorithm follows the same complete transcript on $D_\ell$ and $V$. It gives the same decision even though one answer must be no and the other yes. This proves the bound. When $k=0$ all choices of $d_i$ are available and have the same target value, so the asserted indistinguishability holds directly.

## 3. Exact counts in the three-bit setting

The following lower bounds are attained in this model.

| Comparison of sign tests | Exact deterministic number |
| --- | --- |
| One sign using ordinary tests on nonempty sign sets | Impossible |
| Two signs using one-sign tests | 3 |
| Three signs using two-sign tests | 3 |
| Three signs using one-sign tests | 7 |

For one-sign queries, check all $2^r-1$ linear hyperplanes through zero. A nonempty affine subspace avoiding zero is separated from zero by at least one such hyperplane. For $r=3,k=2$, choose independent $u,v$ and query the lines through $u,v,u+v$. If a nonempty affine subspace avoiding zero meets all three lines, it must contain all three nonzero vectors. Their sum is zero and is an affine combination over $\mathbb F_2$, giving a contradiction. This shows why the earlier three-probe reductions have optimal query counts even after allowing adaptivity, affine shifts, and products of arbitrarily many independent copies in a single query.

## 4. Randomized refinement

For these same tasks, the lower bounds persist for zero-error randomized algorithms with a worst-case query bound. More generally define $M=2^r-1$. Among the hard alternatives considered along the full yes transcript, suppose $q$ probes can collectively distinguish at most $C_q$ alternatives. For $k=1$, one has $C_q\le\min(q,M)$. For $r=3,k=2$, the upper bounds for $q=0,1,2,3$ are respectively $0,3,5,7$.

The bound of five for two probes needs a refinement. If a single query excludes three distinct alternatives, the three possible nonzero target normals each must certify one, in the same chosen accepting branch. Write the normals as $\lambda,\mu,\lambda+\mu$, with the distinguished source functionals $\ell_1,\ell_2,\ell_3$ distinct. Choose one of the maps $L_i,M_j$ where the pullback of $\lambda$ equals $\ell_1$. Through that same map the pullback of $\mu$ cannot vanish, because otherwise the pullback of $\lambda+\mu$ would equal $\ell_1$, which differs from $\ell_3$. It follows there that $\ell_3=\ell_1+\ell_2$. Thus a query excluding three has excluded exactly the nonzero normals of some plane in $V^*$. Two such planes in dimension three intersect in at least a line. Two queries can therefore collectively exclude at most five. If either query excludes at most two, five is immediate.

With perfect completeness the worst-case false acceptance probability is at least $1-C_q/M$. With two-sided error the lower bound is

$$
 \frac{1-C_q/M}{2-C_q/M}.
$$

To see the latter, let $p$ be the yes probability on $V$, so $p\ge 1-\epsilon$ for maximum error $\epsilon$. Condition on a seed for which the algorithm accepts the full yes input. For a uniformly random $D_\ell$, at least $1-C_q/M$ of the transcripts coincide, so its average false acceptance probability is at least $p(1-C_q/M)$. Hence $\epsilon\ge(1-\epsilon)(1-C_q/M)$. The perfect-completeness case has $p=1$. All these bounds are attained for the displayed tasks. Choose a collection of linear probes through zero covering the maximum number of normals, and apply a uniformly random common invertible linear change of coordinates to that collection. For $k=1$ take distinct hyperplanes. For $r=3,k=2$ use one line, two distinct lines, or the three lines from Section 3. Every no affine subspace is contained in some $D_\ell$. It is rejected by at least the fraction $C_q/M$ of the changes. For the two-sided bound, accept when all probes succeed with probability $1/(2-C_q/M)$. The finite set of outcomes permits this exact sampling in the mathematical model.

## 5. Actual tensors and an object-map obstruction

The hard affine profiles used above occur as determinant sets of actual three-tensor comparisons. Start with the same zero three-tensor on three positive-dimensional spaces, for which the three determinant bits are independent. Apply the previous exact sign-projection construction using a binary linear map with image $\ker\ell$, then rebase the target by a determinant vector outside $\ker\ell$. This translates the sign set into $D_\ell$. The same zero input realizes the full sign space. To realize the two-bit hard instances with arbitrary third sign available, lift $\ell$ and $D_\ell$ along the projection $\mathbb F_2^3\to\mathbb F_2^2$. The sign profile theorem gives actual instances for the restricted model. Profiles alone do not encode all the information in their raw tensor entries.

For a separate obstruction, one can exhibit ordinary tensor orbits that split into the maximum number of determinant tiers. Let $T$ be the multiplication tensor of $R=\operatorname{Mat}_{2m}(\mathbb F_3)$. Every ordinary stabilizer is an algebra isotopy, written
$$
 \alpha(X)\beta(Y)=\gamma(XY).
$$
Putting $U=\alpha(I)$, $V=\beta(I)$ gives $\gamma(X)=\alpha(X)V=U\beta(X)$ for all $X$. Left multiplication by $U$ and right multiplication by $V$ are surjective, so $U,V$ are units. Thus the algebra automorphism $\phi(X)=U^{-1}\alpha(X)=\beta(X)V^{-1}$ satisfies
$$
 \alpha(X)=U\phi(X),\qquad
 \beta(X)=\phi(X)V,\qquad
 \gamma(X)=U\phi(X)V.
$$
Indeed the first identities show that $\phi(I)=I$, and cancellation of $U,V$ in the isotopy equation proves multiplicativity. Every algebra automorphism of $R$ is a conjugation. To see this, let $F_{ij}=\phi(E_{ij})$ be the images of the matrix units and choose a nonzero vector $v$ in $\operatorname{im}F_{11}$. The vectors $v_i=F_{i1}v$ are a basis, since applying $F_{1j}$ to a relation isolates its $j$-th coefficient, and $F_{ij}v_k=\delta_{jk}v_i$. The change to this basis implements $\phi$ by conjugation. Left and right multiplications by units act on $2m$ copies of their column or row action, so all their determinants equal $+1$. The same holds for conjugation. Therefore every stabilizer has all physical signs positive. Using dual factors to write multiplication as a tensor leaves signs unchanged.

Apply independent reflections in the three tensor modes to $T$. The resulting eight tensors lie in one ordinary orbit and are pairwise nonisomorphic under SL. They make four two-sign classes and two one-sign classes. An object map that preserves ordinary equivalence cannot reduce a finer tier to any coarser tier. It would have to send distinct source signed classes into distinct target signed classes within a single ordinary orbit, where there are at most $2^k$ signed classes for $k$ tested signs. This also holds for noncomputable object maps satisfying the same ordinary-orbit condition. A kernel reduction preserving only the signed equivalence relation may split the source ordinary orbit across multiple output ordinary orbits, and is not excluded by this argument.

## 6. Exponential lower bound for fixed markers with an odd lifting kernel

A fixed tensor system consists of finitely many labelled spaces and fixed tensors of order at most $d$ on them. Factors may be repeated or dualized. Let $G$ be its ordinary linear automorphism group over $\mathbb F_3$. Designate $j$ of its spaces $U_a$ of dimensions $n_a\ge3$ as the original modes that will have protected determinant signs. Let $\pi:G\to\prod_a\operatorname{GL}(U_a)$ be the corresponding projection. Also allow $k<j$ additional tests given by sign characters on $G$, such as determinants of chosen physical output modes. Call their joint kernel $G_+$. Suppose

$$
 \pi(G_+) \supseteq \prod_{a=1}^j\operatorname{SL}(U_a)
 \quad\text{and}\quad
 K=\ker(\pi|_{G_+})\ \text{has odd order}.
$$

This is a witness-preserving requirement for the allowed source actions. It does not assume a homomorphic section of $\pi$.

For each $a$, put $r_a=\lceil n_a/d\rceil$, with $d\ge2$. If some subset $I$ of more than $k$ protected modes has every labelled space of dimension less than
$$
 \min_{a\in I}\tfrac12\binom{n_a}{r_a},
$$
then $\pi(G_+)$ cannot equal $\prod_a\operatorname{SL}(U_a)$. In fact it contains a tuple of diagonal signs with at least one negative determinant. For fixed $d,j$ and growing $n_a=n$, this excludes polynomial-size fixed-marker constructions with an odd lifting kernel. The lower bound applies to arbitrary order-at-most-$d$ tensors, with coefficients chosen freely over the base field.

For the proof choose the even diagonal sign group $E_a$ in each $U_a$ with $a\in I$ and set $E=\prod_{a\in I} E_a$, with identity in the other modes. Let $H=(\pi|_{G_+})^{-1}(E)$, and let $P$ be a Sylow $2$-subgroup of $H$. Since $K$ is odd, $|P|=|E|$ and its projection is injective, hence $\pi|_P$ is an isomorphism onto $E$. In particular $P$ is elementary abelian. Every permutation $\sigma$ of the $n_a$ coordinates in a mode $a\in I$ has a determinant-one signed permutation lift in the $a$-th factor, with identities in the other factors. Such a matrix normalizes $E$. Choose any $g\in G_+$ over this signed permutation. Then $gHg^{-1}=H$. Its Sylow $gPg^{-1}$ is conjugate to $P$ by some $h\in H$, so $hg$ normalizes $P$. Its projection induces the same coordinate permutation on $E$, since $\pi(h)\in E$, which is abelian. This proves that the normalizer of $P$ in $G_+$ induces all coordinate permutations separately in every distinguished mode.

Over $\mathbb F_3$, the commuting involutions of $P$ are simultaneously diagonalizable, with characters taking values in $\{1,-1\}$. The characters of $E_a$ are indexed by subsets of its coordinate set modulo the equivalence identifying a subset with its complement. Say the size of such a class is the size $s$ of its smaller representative. If a weight on a labelled space has $a$-th component of size $s$, for $a\in I$, the coordinate permutations of $U_a$ force at least $\tfrac12\binom{n_a}{s}$ different weights in that space. This count follows by moving the smaller representative over all $s$-subsets, with identifications only when $s=n_a/2$. If $r_a\le\lfloor n_a/2\rfloor$, the dimension bound and monotonicity of binomial coefficients through the midpoint imply $s<r_a$. If $r_a>\lfloor n_a/2\rfloor$ the same inequality holds automatically. Thus every occurring weight has a unique smaller representative $S_a$, with $d|S_a|<n_a$.

On the weight space corresponding to the tuple of subsets $(S_a)_a$, let an arbitrary tuple of diagonal signs $\varepsilon=(\varepsilon_{a,i})_{a,i}$ act by the scalar $\prod_a\prod_{i\in S_a}\varepsilon_{a,i}$. This defines a homomorphic action of the full diagonal group on every labelled space, and restricts to the original action of $P$ when all diagonal determinants are positive. In a protected standard space $U_a$ for $a\in I$, the characters of $P$ are precisely the single-coordinate bits in that factor, so the resulting action on $U_a$ is the actual diagonal action. Dual colors give the same sign weights because the scalars are their own inverses.

Each fixed marker tensor is invariant under $P$. In its decomposition into weight components, every nonzero component has total character zero on $P$. Equivalently in each $a$ the symmetric difference of the corresponding at most $d$ small representative sets is empty or the full coordinate set. Its size is strictly less than $n_a$, so it is empty. Every nonzero component is consequently fixed by the full diagonal action above, and the whole action lies in $G$. It is the identity on the other protected standard spaces, because $P$ has trivial action there.

The $k$ output constraints restrict to $k$ linear functionals on the full binary diagonal group. The source determinants on $I$ restrict to $|I|$ independent linear functionals. If the kernel of the output functionals were contained in the kernel of the source ones on $I$, their ranks would satisfy $|I|\le k$. Since $|I|>k$, some lifted diagonal action obeys all output constraints and has a prohibited source determinant. This is the required automorphism in $G_+$. With no watched output signs this already rules out implementing a single determinant constraint using a small fixed marker in this model. With $j=2,k=1$ or $j=3,k=2$, it rules out the corresponding simultaneous implementation.

The argument covers unipotent lifting kernels over $\mathbb F_3$ because their orders are powers of three. It also applies when the kernel is trivial. An even lifting kernel may obstruct existence of the elementary abelian subgroup $P$ used in the proof. The theorem makes no lower-bound claim for that situation or for a decision-only transformation that does not surject onto the prescribed source automorphism group.
## Scope and references

The explicit probe model covers affine sign reprojections, fixed slack, signed direct sums and product equations whenever branch eligibility is independent of unqueried sign information. Arbitrary many-one reductions can inspect raw tensors, compute new ordinary invariants, and change both outputs jointly with the input comparison. The quantitative lower bounds do not constrain those unmodeled operations. In particular there is no claim of an unrelativized complexity separation here.

The project’s earlier results supply the exact sign-projection theorem used to realize the hard profiles. For the distinction between ordinary many-one and objectwise kernel reductions, see [Fortnow and Grochow](https://arxiv.org/abs/0907.4775) and [Finkelstein and Hescott](https://arxiv.org/abs/1604.08558). The general special-linear versus ordinary TI comparison is posed by [Chen, Grochow, Qiao, Tang, and Zhang](https://arxiv.org/html/2306.03135v2#S1.SS5). This note establishes no historical novelty priority.
