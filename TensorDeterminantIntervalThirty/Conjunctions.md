# Independent determinant comparisons and exact affine probe counts

Write $O,A,B,S$ for the four many-one degrees over $\mathbb F_3$. For decision problems $X,Y$, write $X\wedge Y$ for the decision problem on independent inputs asking that both answer yes, and $A^j$ for the conjunction of $j$ independent $A$ comparisons. These are abelian sign constraints on independently chosen transporters. A comparison with two signs on the same transporter is a different operation.

## Where three conjunction candidates sit

The existing sign isolation and conjunction constructions give
$$
A\ \le_m^p\ A^2\ \le_m^p\ B\ \le_m^p\ A^3\ \le_m^p\ B\wedge A\ \le_m^p\ S.
$$
Padding by a fixed positive comparison gives the first arrow. Isolating each independent sign on its own physical determinant gives the second. The shared two-bit sign coset meets all three lines through zero if and only if it contains zero, so three one-sign probes on that same pair give the third. The fourth uses $A^2\le_m^p B$. For the last arrow, erase the unused third sign of the $B$ input using the exact sign projection and append the independently oriented $A$ block at that axis. Also $B\wedge A\le_m^p A^4$ by expanding the $B$ component into three probes. These comparisons reuse the preceding MathProofs sign projection and axis assembly. See the project’s published-question context and the ordinary fixed-signature compiler of [Chen–Grochow–Qiao–Tang–Zhang](https://arxiv.org/html/2306.03135v2#S4).

The candidates stay meaningful if a gap turns out to be strict. For example $A^2\equiv_m^p A$ holds exactly when $B\equiv_m^p A$. Similarly $B\wedge A\equiv_m^p B$ holds exactly when $S\equiv_m^p B$. For the latter direction, closure under absorption of one $A$ comparison allows absorption of three, so it absorbs a second $B$ comparison. Three $B$ comparisons decide $S$ by the three-line test in a fixed plane, so this binary conjunction closure collapses $S$ to $B$. Conversely $B\wedge A\le_m^p S$ was just established.

For any fixed $j$, equality of the two degrees $A^j$ and $A^{j+1}$ implies equality of all subsequent fixed conjunction degrees, by repeatedly replacing $j+1$ factors by $j$. In particular equality at $j=2$ implies $B\equiv_m^p S\equiv_m^p A^2$, because $A^2\le_m^p B$ and $S\le_m^p A^7$. Equality at $j=3$ implies $S\equiv_m^p A^3$. None of these implications assumes a uniform closure for conjunctions of polynomially many signed instances.

## Exact theorem for independent profiles in the affine probe model

Let $V_i$ be finite binary vector spaces of positive dimensions $r_i$. A hidden input consists of affine subspaces $D_i\subseteq V_i$, possibly empty. The task is to decide whether every $D_i$ contains zero. A query applies at most $k$ affine sign equations per branch. In a branch it may take arbitrarily many independent relative witnesses from each $D_i$, independent stabilizer witnesses from its direction space when nonempty, and affine auxiliary slack. It can disjoin arbitrarily many such branches. On an empty $D_i$ any branch requiring a relative witness from it fails. The algorithm may adapt to all previous answers.

The deterministic worst-case number of queries equals the least number $t$ for which there exist dual subspaces $E_{ji}\subseteq V_i^*$ with
$$
\sum_i\dim E_{ji}\le k \quad (1\le j\le t),
\qquad
V_i^*\setminus\{0\}\ \subseteq\ \bigcup_{j=1}^{t}E_{ji}\quad\text{for every }i.
$$
In particular finite disjunction and arbitrarily many copies per input do not improve the optimum obtained by fixed simultaneous linear tests.

For the lower bound follow the algorithm on the all-full input $D_i=V_i$. For each $i$ and each $\ell\in V_i^*\setminus\{0\}$, change only profile $i$ to the opposite hyperplane $\{v\mid\ell(v)=1\}$. This is a no input. If a query on the all-full transcript already answers no, it answers no for every substitute because all available witness sets have only shrunk. Otherwise choose one branch that accepts the all-full input and quotient out any auxiliary slack. This branch has equations $\sum L_{ij}z_{ij}=b$ in a space of dimension at most $k$. Rejection on a single-profile substitute supplies a dual linear inconsistency certificate. The output functional $\lambda$ of that certificate has every pullback $\lambda L_{hj}$ zero for $h\ne i$, and every pullback for $h=i$ is either zero or $\ell$. At least one is nonzero, since otherwise the certificate would also reject the all-full input. These claims follow by taking a linear combination of the output equations and the defining $\ell$ equations on the substituted profile. A relative witness has right-hand side one and a stabilizer witness has right-hand side zero. A rejection of the whole query implies rejection of the selected branch, so this certificate covers every substitute distinguished by the query.

Let $W$ be the image of the output dual under the map taking $\lambda$ to the entire tuple of its pullbacks, and $W_i$ its intersection with the tuple coordinates supported on profile $i$. The $W_i$ have disjoint supports and the sum of their dimensions is at most $k$. Let $E_i$ be the span of the normals of those substitutes distinguished by this query. For any independent list $\ell_1,\ldots,\ell_a$ of these normals, choose a nonzero certificate tuple in $W_i$ for each. Those tuples are linearly independent. To see this, evaluate all of their component functionals at a vector of $V_i$ on which just one of the chosen normals evaluates to one. Each linear dependence would force the coefficient of that one tuple to vanish. Consequently $\dim E_i\le\dim W_i$, proving the row budget. Because every negative substitute must diverge from the all-full transcript, these $E_i$ cover all the normals.

For the upper bound, in query $j$ ask for one relative witness $z_i\in D_i$ annihilated by $E_{ji}$ for every $i$ with $E_{ji}\ne0$. The row budget makes this a legal query. A yes input passes all queries. If a nonempty $D_i$ misses zero, choose a linear functional constant one on it. Some row contains that functional and rejects it. An empty $D_i$ fails in any row with nonzero $E_{ji}$, which exists by coverage. Thus the same nonadaptive number suffices.

This proof concerns access only to the abstract sign sets. The earlier fixed-field sign constructions realize the profiles with dense tensor pairs. An arbitrary many-one reduction also sees the entries and can form new ordinary isomorphism tests. These bounds do not impose an oracle restriction on such a reduction.

| Profile dimensions | One sign per probe | Two signs per probe | Three signs per probe |
| --- | ---: | ---: | ---: |
| One shared two-sign comparison, $(2)$ | 3 | 1 | 1 |
| Two independent one-sign comparisons, $(1,1)$ | 2 | 1 | 1 |
| Three independent one-sign comparisons, $(1,1,1)$ | 3 | 2 | 1 |
| Independent two-sign and one-sign comparisons, $(2,1)$ | 4 | 2 | 1 |
| One shared three-sign comparison, $(3)$ | 7 | 3 | 1 |
| Independent three-sign and one-sign comparisons, $(3,1)$ | 8 | 4 | 2 |
| Two independent three-sign comparisons, $(3,3)$ | 14 | 6 | 2 |

For rank one, a row covers only one normal. For rank two, covering the seven nonzero vectors of a three-dimensional dual space consumes at least six units of dimension. With budget five, two planes and one line can cover at most six vectors because the two planes intersect. One plane and three lines also cover at most six, and the remaining cases cover fewer. Three rank-two planes through a common line attain coverage. This explains the last two rows as well as the single three-sign row. Other entries follow by placing independent dimensions into the row budget directly.

In particular, a shared two-sign test takes three one-sign probes in this model, whereas two independent one-sign tests take only two. This distinguishes the two intermediate definitions by a precise model even though their unrestricted many-one degrees could coincide.
