# The complexity of fourfold Massey vanishing

For finite ordered simplicial complexes, existence of a defining system for at most four positive-degree classes and vanishing of the product of at most three such classes are decidable in polynomial time over $\mathbb Z$, each fixed prime field $\mathbb F_p$, and $\mathbb Q$. Fourfold vanishing on connected two-dimensional complexes with four degree-one classes is $\Sigma^0_1$-complete over $\mathbb Z$, NP-complete over each fixed $\mathbb F_p$, and polynomial-time many-one equivalent to Hilbert's tenth problem over $\mathbb Q$. The same hardness and membership statements hold for existence and vanishing of every fixed length $n\geq 5$ on two-dimensional complexes with degree-one classes.

The proof uses Dwyer's unitriangular lifting correspondence. The arithmetic encoding follows the Heisenberg-group equations in Duchin, Liang and Shapiro. Commutators of generators with prescribed first superdiagonals supply the two Heisenberg directions without requiring pinned matrix constants. [Dwyer (1975)](https://doi.org/10.1016/0022-4049(75)90006-7) · [Duchin–Liang–Shapiro (2015), Theorem 4](https://doi.org/10.1090/PROC/12630)

## Defining systems and the linear cases

Let $X$ be a finite ordered simplicial complex. Use its normalized simplicial cochains over $R$ with the Alexander–Whitney cup product, where $R$ is one of the coefficient rings above. The input supplies positive-degree cocycles representing $a_i\in H^{d_i}(X;R)$, $1\leq i\leq n$. Put $\bar w=(-1)^{\deg w}w$. A defining system has entries $a_{ij}$, $0\leq i<j\leq n$, $(i,j)\ne(0,n)$, of degree $\sum_{r=i+1}^j d_r-(j-i-1)$. It uses the chosen cocycles on the first superdiagonal and satisfies
$$
\delta a_{ij}=\sum_{i<k<j}\bar a_{ik}\smile a_{kj}.
$$
A full system also includes the entry $(0,n)$ and its equation. Thus existence of a defining system is $\mathrm{DEF}_n$ and existence of a full system is $\mathrm{VAN}_n$. The cohomology classes determine the product, so any supplied representatives on the first superdiagonal may be used. [May (1969)](https://www.math.uchicago.edu/~may/PAPERS/8.pdf)

A term on the right can have two unknown factors only if $k-i\geq 2$ and $j-k\geq 2$, so $j-i\geq 4$. For $\mathrm{DEF}_n$ with $n\leq4$, the entries used have $j-i\leq3$. The same holds for $\mathrm{VAN}_n$ with $n\leq3$. These cases therefore give a single inhomogeneous linear system in the unknown cochain entries. Its coefficients come from the given cocycles and the simplicial boundary and cup formulas. Its size and coefficient bit lengths are polynomial in the input size. Use Gaussian elimination over the fields and integer normal forms over $\mathbb Z$. [Kannan–Bachem (1979)](https://doi.org/10.1137/0208040)

For any fixed length, the same equations give upper bounds without a linearity hypothesis. Over $\mathbb Z$ the possible cochain entries can be enumerated. Over fixed $\mathbb F_p$ the cochain entries make a polynomial-size certificate. Over $\mathbb Q$ the equations are a polynomial-size system of degree at most two with rational coefficients. Clearing denominators gives an instance of Hilbert's tenth problem over $\mathbb Q$.

## Degree-one systems and unitriangular matrices

Let $U_{n+1}(R)$ be the group of upper unitriangular matrices, and let $Z=\{I+rE_{0n}:r\in R\}$, using indices $0,\ldots,n$. The map $\operatorname{sd}:U_{n+1}(R)\to R^n$ takes the first superdiagonal. If every $d_i=1$, each $a_{ij}$ is a 1-cochain. On an increasing oriented edge $e$, set $g(e)=I+\sum_{i<j}a_{ij}(e)E_{ij}$. The system equations on a triangle $[v_0v_1v_2]$ say exactly $g(v_0v_2)=g(v_0v_1)g(v_1v_2)$. This follows by computing the $(i,j)$ entry of the product, using $\bar a_{ik}=-a_{ik}$. For a defining system one uses $U_{n+1}(R)/Z$, where the corner entry is omitted.

The triangle identities and inverse edge labels make the product along a loop a homomorphism from the fundamental group. Conversely, given such a homomorphism, pick a spanning tree and label each edge by the image of the based loop formed from the edge and its tree paths. The triangle identities follow from the triangle relations in the edge-path presentation. The superdiagonal entries represent the classes induced on loops. Consequently $\mathrm{VAN}_n$ holds precisely when $\pi_1(X)\to R^n$ given by $(a_1,\ldots,a_n)$ lifts through $\operatorname{sd}$, and $\mathrm{DEF}_n$ uses $U_{n+1}(R)/Z$. [Dwyer (1975)](https://doi.org/10.1016/0022-4049(75)90006-7)

## Encoding arithmetic in a lift

In $U_5(R)$ use indices $1,\ldots,5$ and set $\Gamma=\ker(\operatorname{sd})$. For $x\in\Gamma$, let $\alpha(x)=x_{13}$ and $\beta(x)=x_{35}$. We use $[g,h]=ghg^{-1}h^{-1}$. For $g=I+A$, $h=I+B$,
$$
[g,h]=I+(AB-BA)g^{-1}h^{-1}.
$$
The first superdiagonal of $AB-BA$ is zero. On the second superdiagonal its entry $(i,i+2)$ is $A_{i,i+1}B_{i+1,i+2}-B_{i,i+1}A_{i+1,i+2}$. Right multiplication by $g^{-1}h^{-1}$ leaves these second-superdiagonal entries unchanged. If $g,h\in\Gamma$, the only possible nonzero entry of $AB$ is $A_{13}B_{35}$ at $(1,5)$. This proves that $\alpha,\beta$ are additive under multiplication in $\Gamma$ and that
$$
[x,y]=I+(\alpha(x)\beta(y)-\beta(x)\alpha(y))E_{15}
\qquad (x,y\in\Gamma).
$$
If the first superdiagonals of $s,t,u,v$ are respectively the four standard basis vectors, then $k_1=[s,t]$ and $k_2=[u,v]$ lie in $\Gamma$, with $(\alpha,\beta)(k_1)=(1,0)$ and $(\alpha,\beta)(k_2)=(0,1)$. These pairs follow from the second-superdiagonal formula and are independent of the higher entries of $s,t,u,v$.

Consider a system $S$ with equations of the forms $x_i+x_j=x_l$, $x_ix_j=x_l$, or $x_i=1$. Use generators $s,t,u,v,X_i,X_i'$ and the following relators, with $k_1,k_2$ denoting the commutator words above.

| Condition | Relator |
| --- | --- |
| Each variable $i$ | $[X_i,k_1]$, $[X_i',k_2]$, and $[X_i,k_2][k_1,X_i']^{-1}$ |
| $x_i+x_j=x_l$ | $[X_iX_jX_l^{-1},k_2]$ |
| $x_ix_j=x_l$ | $[X_i,X_j'][X_l,k_2]^{-1}$ |
| $x_i=1$ | $[X_ik_1^{-1},k_2]$ |

Each relator lies in the commutator subgroup of the free group and has length at most 20 after expanding the $k_j$. The abelianization of the presented group is therefore free on the generators. Take $a_1,\ldots,a_4$ to be the four dual homomorphisms for $s,t,u,v$, vanishing on the other generators.

The group and its cohomology classes have a polynomial-size two-dimensional simplicial presentation. Realize the generator graph as a wedge of subdivided circles and use a separate polygon for each relator, with one edge for each traversal of a graph edge. Attach the polygon to the graph by a mapping cylinder of the edge map and cap its free end with a cone disk. A strip of the cylinder has boundary consisting of one polygon edge, its graph image, and their endpoint tracks. Triangulate each strip by coning this four-edge boundary from its own new vertex, and use separate new vertices for the disks. This yields a finite simplicial complex with the required fundamental group by van Kampen's theorem. The number of cells is linear in the number of generators and relator letters. A dual cocycle gives each oriented generator circle the corresponding total weight, gives the polygon edges the weights of their image edges, and gives endpoint tracks weight zero. The boundary sum is zero on every strip and disk. Extend over the cone edges by taking successive partial sums of boundary weights, so every new triangle also has zero coboundary.

A lift to $U_5(R)$ with the prescribed superdiagonal sends $X_i,X_i'$ into $\Gamma$ and sends $k_1,k_2$ to elements with the pairs computed above. Set $x_i=\alpha(X_i)$, where matrix images are understood. The variable relators first give $\beta(X_i)=0$ and $\alpha(X_i')=0$, then give $\beta(X_i')=x_i$. The addition relator gives $x_i+x_j-x_l=0$ by additivity of $\alpha$. The multiplication relator gives $x_ix_j-x_l=0$ by the displayed commutator formula. The last relator gives $x_i-1=0$. Hence the lift determines a solution of $S$.

Conversely, from a solution of $S$, send $s,t,u,v$ respectively to $I+E_{12}, I+E_{23}, I+E_{34}, I+E_{45}$, and send $X_i,X_i'$ to $I+x_iE_{13}$ and $I+x_iE_{35}$. The same commutator identities verify every relator. The lift exists, so the fourfold product vanishes.

## Consequences over the three coefficient rings

Over $\mathbb Z$ and $\mathbb Q$, polynomial equations can be written as systems $S$ by introducing a variable for each arithmetic operation. Use $z+z=z$ for a zero, $x+y=z$ for negation with this zero, and doubling and addition for binary integer constants. The integer lower bound follows from the Davis–Putnam–Robinson–Matiyasevich theorem. The rational reduction, together with the upper bound, gives the stated many-one equivalence.

Over each fixed $\mathbb F_p$, represent Boolean variables by $x^2=x$, which gives exactly the two values $0,1$. A negative literal is $1-x$, and a clause $l_1\lor l_2\lor l_3$ holds exactly when $(1-l_1)(1-l_2)(1-l_3)=0$. Introduce intermediate variables to put these conditions into $S$. This is a polynomial-time reduction of 3-SAT and works for $p=2$.

To propagate hardness to $n\geq5$, append degree-one classes from successive new circle summands of $X$. A full system extends to the wedge by taking its old positive-degree entries to be zero on the new circle and all new entries of gap at least two to be zero. Every cup product with factors supported on different summands vanishes. Conversely, a defining system for the augmented list, restricted to $X$ and truncated at the old last index, includes the old corner equation and therefore gives a full system for the original list. Iteration reduces fourfold vanishing to both defining-system existence and vanishing at every larger length. The constructed complexes stay two-dimensional.

## Verification

This is a written proof. An independent exact matrix-word check compares the presentation relators against arithmetic solvability for 100 small systems over $\mathbb F_2$ and $\mathbb F_3$. The check covers the group reduction on those instances. [C++ verification source](Check.cpp)

