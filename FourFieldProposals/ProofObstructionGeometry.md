# Geometry of proof obstructions

## Proposed definition

**Geometry of proof obstructions** studies mathematical families equipped with a filtration on how their identities can be certified. Its central objects are the obstruction functors of marked consequences under base extension. A family can be geometrically trivial while its obstruction functors carry arbitrary algebraic geometry.

Here is a concrete setting for the field. Fix a field $k$. Over a commutative $k$-algebra $B$, present a solution functor by a tuple $F=(f_i)$ in $B[\mathbf x]$ and mark a consequence $h\in(F)$. Give each generator its declared degree in the witness variables. A declared degree is retained after changing the base ring, even if a coefficient specializes to zero. For a $B$-algebra $A$ and a budget $d\ge\deg h$, let $M_d(F;A)$ be the $A$-submodule of $A[\mathbf x]_{\le d}$ spanned by the $x^\alpha f_i$ of declared degree at most $d$. Define the scalar obstruction of $h$ by
$$
 J_d(F,h;A)=\{a\in A:ah_A\in M_d(F;A)\},
 \qquad O_d(F,h;A)=A/J_d(F,h;A).
$$
The ideals $J_d$ increase with the proof budget. Under a base change $A\to A'$, an existing proof transports to $A'$. New proofs can become possible and so $J_d(F,h;A)A'\subseteq J_d(F,h;A')$. The corresponding quotient map gives the functor on rings.

One can keep several marked consequences using the kernel of the map from their free coefficient module to $A[\mathbf x]_{\le d}/M_d(F;A)$. The kernels record dependencies among marked certificates as well as individual provability. Different resource systems can use, for example, the span of dynamic derivations, the sizes of arithmetic certificates, or the degree of an exact positivity certificate. These choices are data of the theory. They need not agree for one presentation.

For clarity, the affine substitutions give one concrete comparison law. A substitution from one polynomial presentation to another induces a pullback on solution schemes. If the variables map to polynomials of degree at most $a$, and every substituted generator admits a target certificate of degree at most $a\deg f_i+b$, the substitution carries proofs of budget $d$ to proofs of budget at most $ad+b$. This follows by substituting in each product $x^\alpha f_i$ and multiplying the generator's new certificate by the substituted monomial. It is valid over every base ring on which the stated generator identities hold. A second comparison of budget $a'd+b'$ composes with the first at budget $a'ad+a'b+b'$. Exact equivalence means isomorphism of the solution functors together with natural isomorphisms of the marked obstruction functors at each budget, compatible with the budget maps. For families of presentations with a size parameter, bounded-loss equivalence allows mutually inverse comparisons on solutions and transport of marked proofs in both directions with uniform regrading bounds.

The foundational question is which obstruction functors can lie over a given solution functor, and which of their features survive changes of presentation. This puts the pair consisting of semantic geometry and resource-sensitive consequences at the center of the subject. The same question can be posed about a family of matrix transporters, a symbolic elimination procedure, or an exact polynomial model of a physical symmetry.

## Realization theorem on a smooth constant family

**Theorem.** Fix a field $k$, a commutative $k$-algebra $B$, and any finite increasing sequence of finitely generated ideals
$$
 I_1\subseteq I_2\subseteq\cdots\subseteq I_D\subseteq B .
$$
There is a finite polynomial presentation over $B$, with marked consequence $z$, whose underlying solution scheme is an affine space over $B$, and whose obstructions satisfy, simultaneously for each $1\le d\le D$ and every $B$-algebra $A$,
$$
 J_d(F,z;A)=I_d A,\qquad O_d(F,z;A)=A/I_d A .
$$
Its ambient equations can be chosen with degree at most $\max(3,D)$ in the witness variables. In particular, an arbitrary finitely presented affine subscheme of the base occurs as the budget-one obstruction scheme, including any nilpotent structure, while the solution scheme stays smooth and constant.

### A family with an exact certificate degree

For an integer $n\ge2$, use the system
$$
 E_n=\bigl(x_1,\,x_{i+1}-x_i^2\ (1\le i<n),\,x_n-1\bigr)
$$
over $k$. Its ideal contains 1. The least static Nullstellensatz degree of a certificate for 1 is exactly $n$.

For the upper bound, $x_1$ has a degree-one certificate. If $x_i$ has one of degree $i$, multiply it by $x_i$ and add the displayed generator to obtain a certificate for $x_{i+1}$ of degree at most $i+1$. Subtract the last generator from the certificate for $x_n$.

For the lower bound let $m=2^{n-1}$ and substitute $x_i=t^{2^{i-1}}$ into $k[t]/(t^m-1)$. The chain and terminal generators vanish. A degree-$d$ certificate would say that $1=tQ$ where $Q$ is the image of a polynomial of total degree at most $d-1$. The basis of the quotient is $1,t,\ldots,t^{m-1}$, so some monomial in that polynomial must have weighted exponent congruent to $m-1$ modulo $m$. Its exponent is a sum of at most $d-1$ powers $1,2,\ldots,2^{n-1}$, counting repetitions. Delete powers $m$, combine equal powers by carrying, and delete any newly created multiples $m$. None of these moves increases the number of summands. The residue $m-1$ needs $n-1$ distinct binary places, so $d\ge n$. The argument holds in every characteristic, because the quotient by the monic relation still has the stated vector-space basis.

This example isolates the chosen resource model. In ordinary Polynomial Calculus the same chain has a degree-two derivation of 1, since each newly derived linear equation can be reused at its own degree.

### Realize the whole obstruction flag

Choose $n>\max(D,1)$, introduce two variables $z,u$, and use the generators
$$
 z^2-z,\qquad u-1,\qquad zf\ (f\in E_n),\qquad
 g_{j\ell}z u^{j-1}\quad(1\le j\le D)
$$
where the $g_{j\ell}$ generate $I_j$. They have degree at most $\max(3,D)$. Since the $E_n$ generate the unit ideal, the entire displayed ideal is $(z,u-1)$. The solution scheme is $\mathbb A_B^n$, and $z$ is a marked identity of that scheme.

If $j\le d$, then $g_{j\ell}z$ has a degree-$j$ certificate: subtract from $g_{j\ell}z u^{j-1}$ the multiple of $u-1$ coming from $u^{j-1}-1$. For $j=1$ the generator is already the marked multiple. This proves $I_d A\subseteq J_d(F,z;A)$ over every base algebra $A$.

Conversely, suppose $az$ has a degree-$d$ certificate. Substitute $z=u=1$. The first two displayed types vanish. The chain terms give a degree-$d$ element of $M_d(E_n;k)$ extended $A$-linearly. Only the parameter generators with $j\le d$ can occur under the declared degree convention. They give an element of $I_dA[\mathbf x]$ of total degree at most $d$. Since $d<n$, the exact chain bound says $1\notin M_d(E_n;k)$. There is a $k$-linear functional on $k[\mathbf x]_{\le d}$ vanishing on that subspace and taking $1$ to $1$. Extend it $A$-linearly and apply it to the evaluated certificate. This gives $a\in I_dA$. The two inclusions give the theorem over every test algebra.

For example, take $B=k[s]$ and compare two choices $I_1=(s)$ and $I_1=(s^2)$. The solution families are the same affine space, and the points of the loci of failed cheap certification agree over every field. The obstruction functors are different over $A=k[\epsilon]/(\epsilon^2)$ at $s=\epsilon$. They are $A/(\epsilon)$ and $A$, respectively. The resource-sensitive theory detects an infinitesimal difference that the pointwise proof-degree jump and the underlying solution scheme both miss.

## Prior work and the proposed boundary

Nullstellensatz proof spaces, degree profiles, syzygies of certificates, and bounded-degree reductions are established tools. The proposal keeps the entire obstruction functor over the varying base as geometric data. The realization problem for these functors on a *fixed smooth solution scheme* is the focus here. The theorem above solves the finite flag realization problem for a scalar marked identity in the static linear certificate setting. It does not assert that the same realization holds for dynamic proof systems or for all naturally presented families. [Grochow–Pitassi on algebraic certificates and syzygies](https://arxiv.org/abs/1404.3820) · [Galesi–Grochow–Pitassi–She on bounded-degree reductions](https://arxiv.org/abs/2305.19320) · [Riis on degree profiles](https://arxiv.org/abs/2611.07280)

Three next questions distinguish the full proposed field from this first calculation. Determine which obstruction flags survive under certified changes of coordinates and redundant generators of uniformly bounded complexity. Characterize jumps and base change for *joint* marked identities and for dynamic certificates. Find how obstruction data behave when a construction simultaneously preserves actual transporters and their refutations, as in the portfolio's earlier tensor compiler. The answers would relate the geometry of a problem, the geometry of its formal consequences, and the cost of moving between presentations. [Earlier exact transporter and proof-complexity transfers](https://github.com/Dugongue/MathProofs/blob/d6933df162f8e998f27e007a42b8b6e55bb4858b/UniversalityConsequences/README.md)

This is a proposed subject with a written seed theorem. Publication priority for that theorem is provisional.
