# Determinant constraints, support components, and graph switching

## Determinants of all anchored transporters

Let $K$ be any field. Consider a labelled tuple $A$ of square matrices
and the tuple $B$ with entries $B_{t,ij}=v_i A_{t,ij}/v_j$, where all
$v_i$ are nonzero. Require a transporter $X$ between $A$ and $B$ to
commute with a common family of diagonal anchors whose joint labels
separate the coordinate indices. Join $i$ to $j$ whenever some
$A_{t,ij}$ is nonzero, forgetting orientations, and write $C(i)$ for the
connected component of $i$.

Every transporter is exactly of the form
$$
X=\operatorname{diag}(v_i c_{C(i)}),
$$
with arbitrary $c_C \in K$. This includes singular solutions. A single
anchor need only participate in the jointly separating family. The exact
attainable determinant range is
$$
\left\{\Big(\prod_i v_i\Big)\prod_C c_C^{|C|}\;\middle|\;c_C\in K\right\}.
$$
The joint trace and determinant profile pairs this expression with
$\sum_i v_i c_{C(i)}$. Orthogonality adds the exact coordinate conditions
$(v_i c_{C(i)})^2=1$.

To see the classification, take the $(i,j)$ entry of each anchor equation.
Those equations kill every off-diagonal entry. Each nonzero tuple edge
then forces equality of the normalized diagonal scalars $X_{ii}/v_i$
and $X_{jj}/v_j$. Equality propagates across the undirected component.
Every assignment of the component scalars satisfies the original matrix
equations. Grouping determinant factors by component proves the profile.

A singleton component allows every determinant. More generally, for
positive matrix side and invertible transporters put
$g=\gcd_C |C|$. In the commutative group $K^\times$, the power-product
theorem proved in the file gives the determinant coset
$(\prod_i v_i)(K^\times)^g$. Thus over a finite field of order $q$ there
are $\gcd(g,q-1)$ determinant cosets in the corresponding family of
ordinary conjugates. Component sizes 2 and 3 already remove all
determinant obstructions without a singleton. Component sizes 2 and 4
leave precisely the square-class obstruction. These last observations
combine the formal component formula with the group-level gcd formula
and the elementary cyclicity of finite-field unit groups.

The earlier rooted-column theorem treats one connected support and one
simple-spectrum diagonal anchor. The present result permits disconnected
supports, arbitrary tuples, and separation by several anchors jointly.
The image of a determinant on a centralizer is a classical invariant.
The support classification here identifies that image in an explicit class
of anchored systems. [Britnell and Wildon](https://arxiv.org/abs/1001.0811)

## Rooted graph constraints

A directed graph has edge weights in a group $G$ and a chosen path from
a root to each vertex. Given edge weights $A$ and $B$, switching equations
are $g_i A_e=B_e g_j$. The prior root reconstruction allows the present
theorems to carry any further global predicate on the whole gauge,
intersections of two prescribed character lists, or a weighted product
of all vertex characters. For an abelian character $\chi$, the latter
product becomes one root power with exponent $\sum_i m_i$, times a
known product of character values on the chosen paths. When both edge
labellings have the same character, a kernel-valued gauge exists exactly
when the based-label conjugacy admits a root in the kernel. The
correction set is a character coset of a simultaneous centralizer.

The same stabilizer correction principle is proved for arbitrary group
actions. It gives an exact criterion for splitting an ordinary orbit into
kernel orbits, and it combines two characters when their values can be
corrected independently. The gain-graph reduction to simultaneous
conjugacy of closed-walk labels is classical. The additional predicates
and weighted character constraints are the scope of these results.
[Cavaleri and Donno](https://arxiv.org/abs/2111.12428)

## Other conclusions

The list of independent power contributions in any commutative group has
image equal to the image of a single power with the gcd exponent.
Two prescribed powers with coprime exponents have a common root exactly
when their cross powers agree. When a root exists it is unique.

An odd-dimensional ordinary simultaneous congruence can be corrected
to determinant one if a pair of corresponding invertible slices has
equal determinant. Negating a transporter of determinant minus one
preserves every congruence equation and flips the determinant.
For a diagonal source tuple a single coordinate reflection gives the
same correction in either parity. Additional matrix results give the
products of dual congruences, exact transfer to inverse-transpose
transporters, and assembly of complementary inverses from independent
corner solutions. The residual identities record their stated algebraic
relations and do not assert lower bounds for Polynomial Calculus.

## Structural provenance and scope

Anonymous motif 386978 connects 104498 and 249619, with a visible
bipartite-gauge and cycle connection after reveal. Motif 507386 connects
41330, 117066 and 24362, supplying the coprime and divisibility lead.
Motif 463172 connects 327410 and 18256, leading to a test for information
retained by compression. These supplied directions after the queue was
frozen. The actual results are explicit mathematical constructions.
The graph path machinery in the source reuses earlier audited definitions
and proofs as private support. The public inventory states the new
claims at their exact hypotheses, and some are formal refinements of
classical arguments. [Lean source](B.lean)
