# A cohomology ring criterion for border determinantal lower bounds

## Specialization theorem

Let $k$ be an algebraically closed field and let $\mathfrak a,\mathfrak b$ be Lie algebras of dimension $m$ over $k$. For their Chevalley–Eilenberg differentials write
$$
\delta_i=\operatorname{rank}d_{\mathfrak a}^{\,i}-\operatorname{rank}d_{\mathfrak b}^{\,i}.
$$
Use rank zero outside the cochain degrees. Suppose the law of $\mathfrak b$ belongs to the Zariski closure of the $\operatorname{GL}_m$-orbit of the law of $\mathfrak a$. Then all $\delta_i$ are nonnegative. There are a graded subalgebra $A\subseteq H^*(\mathfrak b;k)$ and a graded ideal $I\subseteq A$ with
$$
\operatorname{codim}_{H^i(\mathfrak b)} A^i=\delta_i,\qquad
\dim I^i=\delta_{i-1}.
\tag{1}
$$
The ring $A/I$ is the special fiber of a finite free graded algebra over a discrete valuation ring with residue field $k$, whose generic fiber is the scalar extension of $H^*(\mathfrak a;k)$ after a finite extension of the fraction field. Equivalently, the law of $A/I$ lies in the graded change-of-basis orbit closure of the law of $H^*(\mathfrak a;k)$.

If both algebras are unimodular, $I$ is the orthogonal complement of $A$ under the Poincaré duality pairing on $H^*(\mathfrak b;k)$. In particular, $A/I$ is a Poincaré duality algebra. This applies to the two-step nilpotent Lie algebras below.

### Proof

Use a discrete valuation degeneration of the law, with uniformizer $t$. For clarity, choose a curve through the target in the orbit closure with generic point on the orbit, normalize the curve, and take the local ring at a point over the target. The required curve can be obtained from a finite Noether normalization to affine space by taking a line through the image of the target that meets the complement of the image of the orbit boundary. A component of the inverse image through the target has dimension at least one by the principal ideal theorem and dominates the line by finiteness. Its generic point lies in the orbit. If the closure has dimension zero, take the constant family over $k[[t]]$. The generic orbit transporter exists over an algebraic closure of the fraction field and therefore over a finite field extension. Normalizing in that extension and localizing at a point over the chosen point gives a discrete valuation ring $R$ with the same residue field $k$. This last step can be omitted if one only needs invariants after scalar extension. [Chouhy, orbit degenerations and discrete valuation rings](https://arxiv.org/abs/1708.02933)

Let $C$ be the finite free Chevalley–Eilenberg differential graded algebra of the resulting Lie law over $R$. Write $H_R=H^*(C)$ and let $T\subseteq H_R$ be its $t$-power torsion ideal. From the short exact sequence of complexes $0\to C\xrightarrow{t}C\to C/tC\to0$, the connecting homomorphism gives
$$
0\longrightarrow H_R^i/tH_R^i\longrightarrow H^i(C/tC)
  \longrightarrow H_R^{i+1}[t]\longrightarrow 0.
\tag{2}
$$
The injection in (2) preserves products because reduction is a morphism of differential graded algebras. Set $A$ to its image and let $I$ be the image of $T$. Then $A/I$ is the special fiber of the finite free graded algebra $H_R/T$. The fraction field is flat over $R$, so its generic fiber is the asserted cohomology ring. In a homogeneous basis the structure constants of $H_R/T$ are integral. Any polynomial on structure constants over $k$ vanishing on the graded orbit of the source ring vanishes on the generic fiber, hence on the special fiber. This proves orbit-closure containment.

The torsion in $H_R^i=\ker d_R^i/\operatorname{im}d_R^{i-1}$ coincides with the torsion of $\operatorname{coker}d_R^{i-1}$. Indeed the quotient of the latter module by $H_R^i$ is $\operatorname{im}d_R^i$, which is torsion free. Smith normal form therefore gives $\delta_{i-1}$ torsion elementary divisors in $H_R^i$. Each contributes one dimension to $H_R^i[t]$ and one to the image of $T^i$ modulo $t$, as $H_R^i$ splits as a free module and its torsion. In (2) these are the two defects in (1).

For the unimodular assertion, $d^{m-1}=0$ throughout the family. This holds generically by the trace characterization of unimodularity, and then over $R$ because the cochain modules are free. Thus $H_R^m=C^m$ is torsion free. The top wedge product makes $d_R^i$ and $d_R^{m-i-1}$ transposes up to signs in dual bases, by the Leibniz identity and $d_R^{m-1}=0$. The same holds in both fibers, so $\delta_i=\delta_{m-i-1}$. Over the residue field the induced top product is perfect on cohomology. In fact the annihilator of the cycles in the complementary degree is the boundary space, by the transpose relation on the cochains. In the pairing $H^i(\mathfrak b)\times H^{m-i}(\mathfrak b)\to k$, $I^i$ annihilates $A^{m-i}$ because a product involving a torsion class in $H_R$ is torsion. Its dimension $\delta_{i-1}$ equals $\operatorname{codim} A^{m-i}$, so $I^i=(A^{m-i})^\perp$. Passing to the quotient gives perfect pairings in $A/I$.

## A test with explicit defects

Write $b_i=\dim H^i(\mathfrak b;k)$, and $r_{ij}(\mathfrak l)$ for the rank of the product $H^i(\mathfrak l;k)\otimes H^j(\mathfrak l;k)\to H^{i+j}(\mathfrak l;k)$. Under the hypotheses of the theorem,
$$
r_{ij}(\mathfrak b)\ \le\
r_{ij}(\mathfrak a)+\delta_{i+j-1}
+b_i b_j-(b_i-\delta_i)(b_j-\delta_j).
\tag{3}
$$
To see this, first restrict the multiplication on $\mathfrak b$ to $A^i\otimes A^j$. The domain loses exactly $b_i b_j-(b_i-\delta_i)(b_j-\delta_j)$ dimensions. Next project to $A^{i+j}/I^{i+j}$, losing at most $\delta_{i+j-1}$ dimensions of image. The resulting map factors through the product on $A/I$. Its rank is bounded by the source rank by specialization of minors. One may use an exterior square when $i=j$ is odd and the characteristic is different from two. In that case the last two terms involving the domain dimensions in (3) become $\binom{b_i}{2}-\binom{b_i-\delta_i}{2}$.

The same subquotient test can retain polynomial identities or closed conditions on several products at once. If the endpoint ranks pass the elementary inequalities, choose graded bases of $H^*(\mathfrak b;k)$ with unknown change-of-basis matrices. In each degree use the first $\delta_{i-1}$ basis vectors for $I$ and the first $b_i-\delta_i$ for $A$. Inverse matrices are imposed by polynomial equations. Membership of products in $A$ and in $I$ is expressed by zero coordinates, so the multiplication table of $A/I$ is given by polynomial expressions in the matrices and their inverses. Add any specified closed graded change-of-basis invariant conditions on the source law, for instance multiplication rank bounds or multihomogeneous identities. In the unimodular case add the orthogonality equations above. Infeasibility of this finite polynomial system is a sufficient certificate of nondegeneration. This criterion uses the actual special cohomology multiplication when testing whether the defects can be absorbed.

## Application to Hessian Lie algebras

Let $f$ be a form of degree $d\ge 3$ on a vector space $V$. The Hessian Lie algebra has underlying space $(V_L\oplus V_R)\oplus U$, with $U=\operatorname{Sym}^{d-2}V^*$ central. The bracket is
$$
[(x_L,x_R),(y_L,y_R)]
   =\partial_{x_L}\partial_{y_R}f-\partial_{y_L}\partial_{x_R}f.
$$
It is alternating and has central image. The law is linear in $f$ and equivariant via the two copies of the action on $V$ and the induced action on $U$. Therefore orbit-closure membership for forms implies orbit-closure membership for their Hessian Lie algebras. A violation of (3), or a certified infeasible subquotient system, excludes the original orbit-closure membership.

In particular let $f$ be an $n$-variable degree-$d$ homogeneous form with $d\le N$ and $n+1\le N^2$. In $N^2$ variables consider its padding $z^{N-d}f(x)$. Any affine $N$-by-$N$ determinantal representation of $f$ homogenizes to a linear substitution into $\det_N$ giving the padded form. The image of any linear map under the substitution morphism lies in the orbit closure, by density of the invertible maps. The coefficient closure of the affine representations also maps into this orbit closure because homogenization is linear. Thus excluding the padded form from the orbit closure gives border determinantal complexity greater than $N$. The analogous homogeneous version needs only $n\le N^2$. For $d=N$, the degree-$N$ part of an affine determinantal representation is the determinant of its homogeneous linear part. Taking this component commutes with specialization. Thus for $d=N$ the same argument gives the affine border lower bound using only $n\le N^2$.

There is a finer test specific to these Lie algebras. Let $(p_L,p_R,q)$ count the factors from $V_L^*,V_R^*,U^*$ in an exterior monomial and give it weight
$$
w=(p_L+q,\ p_R+q).
$$
The differential increases $p_L,p_R$ by one and decreases $q$ by one, so it preserves $w$. Cup products add weights. When comparing forms in one orbit closure, take the discrete valuation family in the form space and apply the Hessian construction over its valuation ring. The generic change of variables respects both weights. Every step of the specialization proof now applies in each weight separately. For a product from degrees and weights $(i,w),(j,v)$, (3) holds with the corresponding ranks and dimensions, with input losses $\delta_{i,w},\delta_{j,v}$ and with output loss $\delta_{i+j-1,w+v}$. The degree-$m$ top class has weight $(\dim V+\dim U,\dim V+\dim U)$, so the duality constraint pairs complementary weights. This version can test a selected product using its own defects even when the unweighted defects in other summands are large.

### An explicit homogeneous benchmark

Over any algebraically closed field of characteristic different from two, the criterion excludes $\operatorname{perm}_3$ from the orbit closure of $\det_3$ on the nine matrix-entry variables. By taking degree-three components, this also gives affine border determinantal complexity at least four. This verifies a low-dimensional case using cohomology ring information.

For either cubic, the linear map $U^*=V\to\bigwedge^2(V_L\oplus V_R)^*$ sending a vector to its Hessian bracket form is injective. Each matrix entry occurs, with coefficient $1$ or $-1$, as the Hessian entry for a pair using precisely the two complementary rows and columns. Each such pair sees only that one entry. It follows that $H^1=(V_L\oplus V_R)^*$ and the relation space
$$
L=\ker\bigl(\bigwedge^2 H^1\longrightarrow H^2\bigr)
$$
is exactly the nine-dimensional image of that map, by the description of the Chevalley–Eilenberg differential on one-forms. The Pfaffian restricted to $L$, as a degree-nine polynomial in coordinates on $L$, equals the determinant of the nine-by-nine Hessian, up to sign. This uses the Pfaffian of the alternating block matrix with off-diagonal blocks $H$ and $-H^{\mathsf T}$.

If the permanent Lie law were a degeneration of the determinant Lie law, then $A^1=H^1(\mathfrak b)$ and $I^1=I^2=0$ in (1), since $d^0=0$ and $d^1$ has rank nine at both endpoints. The special relation space for $A/I$ would consequently be the actual $L$ of the permanent. In the finite free cohomology algebra $H_R/T$, the map from the exterior square of degree one to degree two then has constant rank in both fibers. Its kernel is a direct summand and reduces onto the special kernel, by Smith normal form. A basis of that kernel over $R$ gives a degree-nine restricted Pfaffian over $R$. If this polynomial is a cube up to scalar after passing to the generic algebraic closure, it remains a cube up to scalar or zero in the special fiber. Indeed the nonzero projective cubes form the image of the map $[g]\mapsto[g^3]$ between the projective spaces of cubics and degree-nine forms, a closed image by projectivity. Its affine cone is closed and the property is invariant under changes of basis of $L$ and $H^1$.

For $D=\det_3$, left multiplication by an invertible matrix $M$ on the matrix-entry space has determinant $(\det M)^3$, and $D(MX)=\det(M)D(X)$. Differentiating twice and taking determinants gives
$$
\det\operatorname{Hess}D(MX)=(\det M)^3\det\operatorname{Hess}D(X).
$$
Set $X=1_3$ and use density of invertible matrices to obtain $\det\operatorname{Hess}D=cD^3$ with constant $c$. For $P=\operatorname{perm}_3$, evaluate the Hessian on
$$
X(t)=
\begin{pmatrix}1&t&0\\ t&1&0\\0&0&1\end{pmatrix}.
$$
Each Hessian entry is zero if the differentiated entries share a row or column, and is the remaining entry otherwise. The block indexed by $(11,22,12,21,33)$ is
$$
\begin{pmatrix}
0&1&0&0&1\\
1&0&0&0&1\\
0&0&0&1&t\\
0&0&1&0&t\\
1&1&t&t&0
\end{pmatrix}.
$$
The upper-left four-by-four block is its own inverse and has determinant one, so the block determinant is $-2(1+t^2)$. The other block is indexed by $(13,23,31,32)$ and has zero diagonal blocks and off-diagonal blocks $\begin{pmatrix}1&t\\t&1\end{pmatrix}$, with determinant $(1-t^2)^2$. Thus
$$
\det\operatorname{Hess}P(X(t))=-2(1+t^2)(1-t^2)^2.
$$
It has simple roots at $t^2=-1$ in all the stated characteristics. The restriction of a cube to this line would be zero or a cube and could not have a simple root. The relation-space condition excludes the degeneration.

## Provenance and verification

Alpöge's theta-lattice calculation organizes congruence conditions by integral row lattices. The corresponding lattice operation here is taking the integral cycle lattice and tracking the elementary divisors of the boundaries before reduction. The argument uses Smith normal form and the cohomology exact sequence (2), independently of any analytic hypothesis. The cohomology exact sequence and the use of valuation curves for geometric degeneration are standard. The contribution is their explicit multiplicative subquotient test with rank-loss dimensions, the duality constraint, and the Hessian Lie application. The size-three example is a benchmark for the mechanism. [Alpöge's announcement](https://alpo.ge/remark.pdf) · [Released row-lattice calculation](https://raw.githubusercontent.com/CocoSgt/riemann-hypothesis-lean/main/src/Development/WeilBound/ThetaLifts/SphericalLattices/BelowIffRows.lean)

The results above are written mathematical proofs. The general specialization theorem and its application have not been formalized in Lean. The theorem supplies sufficient certificates for noncontainment at a specified size. Superpolynomial lower bounds would require an asymptotic family of certified violations.
