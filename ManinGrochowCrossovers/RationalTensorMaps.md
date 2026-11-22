# Rational Tensor Isomorphism and nonzero-degree maps of six-manifolds

## Main theorem

Deciding whether a nonzero-degree map exists between closed, oriented, simply connected smooth six-manifolds with equal rational Betti numbers is equivalent to rational Tensor Isomorphism under deterministic polynomial many-one reductions for finite oriented triangulations. The equivalence also holds for cup-table input, consisting of the symmetric trilinear pairing on $H^2$ and the third Betti number. Hardness already holds for stably parallelizable, torsion-free examples with $H^3=0$.

This combines Fedor Manin's six-dimensional cup-product realization and positive-weight mapping machinery with Grochow–Qiao's reductions. The extra step is a scalar-removal construction that lets an arbitrary nonzero map degree vary without weakening the tensor-isomorphism test.

## From maps to cubic similitude

Write $\mu_M(x,y,z)=\langle xyz,[M]\rangle$ on $H^2(M;\mathbb Q)$, and similarly for $N$. A degree-$d\ne0$ map $M\to N$ injects rational cohomology by Poincaré duality. Equality of rational Betti numbers therefore gives a linear isomorphism $A:H^2(N;\mathbb Q)\to H^2(M;\mathbb Q)$ with
$$
\mu_M(Ax,Ay,Az)=d\,\mu_N(x,y,z).
$$

Conversely, take such a similitude for any $d\in\mathbb Q^\times$. Send the chosen top cohomology generator of $N$ to $d$ times that of $M$. In degree four use $d$ times the inverse dual of $A$ via the Poincaré pairings. In degree three choose any isomorphism scaling the alternating Poincaré pairing by $d$. This exists because the two spaces have the same dimension, and a symplectic basis permits multiplying one vector per pair by $d$. The displayed cubic condition ensures that the degree-two products agree with the map in degree four. Together these rules preserve every possible nonzero product and give a graded rational cohomology algebra isomorphism. This reasoning includes the cases of zero cubic and vanishing middle cohomology.

Both manifolds are formal by Miller's theorem. The degree grading of the formal cohomology algebra supplies positive weights. Manin's Theorem B then gives actual maps in both directions whose rationalizations are equivalences. In particular the map $M\to N$ has nonzero degree. The argument needs existence of some degree and places no requirement on realizing the given rational multiplier as an integer degree. [Miller](https://mathscinet.ams.org/mathscinet-getitem?mr=528561) · [Manin, Theorem B](https://doi.org/10.1090/proc/15978)

### Similitude reduces to associative algebra isomorphism

First compute the contraction radical $R=\{v: \mu(v,-,-)=0\}$ by rational linear algebra. Compare the two original dimensions and radical dimensions. A similitude of the forms on the quotients by the radical lifts to a similitude of the original forms by choosing splittings and identifying the radical spaces. If both forms vanish, the answer is determined by the dimensions.

For a nonzero form with zero contraction radical on $V$, construct the rational commutative unital algebra $A_\mu=\mathbb Q\oplus V\oplus V^*\oplus\mathbb Q s$. Give its summands grades $0,1,2,3$. Define $xy=\mu(x,y,-)$ and $x\varphi=\varphi(x)s$ for $x,y\in V$, $\varphi\in V^*$. Products of positive grades summing to more than three vanish. Symmetry of $\mu$ gives associativity. The positive-grade part $\mathfrak m$ is the unique maximal ideal, since it is nilpotent and the quotient is $\mathbb Q$. The products $xy$ span $V^*$, because their common annihilator in $V$ is the contraction radical. Thus $\mathfrak m^2=V^*\oplus\mathbb Q s$ and $\mathfrak m^3=\mathbb Q s$. An algebra isomorphism induces a cubic similitude on $\mathfrak m/\mathfrak m^2$ by its action on the triple product into $\mathfrak m^3$. Conversely a similitude extends to the algebra by using its multiplier times the inverse dual on $V^*$ and that multiplier on $\mathbb Q s$.

This is a polynomial-time reduction, including the rational basis changes used to remove the radical. Algebra isomorphism reduces to ordinary TI by Grochow–Qiao, Corollary B. [Grochow–Qiao](https://arxiv.org/html/1907.00309#S3)

For a triangulation, rational linear algebra on finite simplicial cochains computes the third Betti number, a rational basis in degree two, the orientation pairing and all basis triple products in polynomial bit time. Fixed-dimensional cup products use the simplicial cup formula. This establishes the upper reduction on triangulations as well.

## From cubic isometry to actual maps

Let $\mu,\nu$ be rational symmetric trilinear forms on $n$-dimensional spaces. Define their padded forms by adjoining $n+1$ mutually orthogonal unit cubic axes. The cubic on a unit axis is $t^3$. We prove
$$
\mu\cong\nu\quad\Longleftrightarrow\quad
\mu\oplus\langle1\rangle^{n+1}\text{ and }\nu\oplus\langle1\rangle^{n+1}
\text{ are similar}.
$$
For a symmetric form $\eta$, write $B_v(x,y)=\eta(v,x,y)$. In a direct sum, the ranks of the contractions add. Each axis vector has rank-one contraction and cube one. Under a similitude, the images of the $n+1$ axes are linearly independent vectors with rank-one contraction. Some image has a nonzero padding coordinate because the old space has dimension $n$. Its remaining padding coordinates vanish and its old component has rank-zero contraction. Its cube is therefore a nonzero rational cube, which equals the common multiplier. Dividing the similitude by its cube root makes it an isometry.

For cancellation of a unit axis, suppose an isometry sends the chosen axis vector to $v$ in the other form. Then $B_v$ has rank one and $\eta(v,v,v)=1$. Let $e$ be the other form's chosen unit axis. Write $v=w+a e$ in its direct sum with the complement. If $a\ne0$, rank additivity gives $B_w=0$, and $a^3=1$ gives $a=1$ over $\mathbb Q$. The shear $e\mapsto e-w$ fixing the complement preserves the form and sends $v$ to $e$. If $a=0$, split the complement as $\mathbb Q v\oplus\ker(\eta(v,v,-))$ within that complement. The two summands are orthogonal for cubic products because $B_v$ is rank one and $B_v(v,v)=1$. Thus interchanging $v$ and $e$ is an isometry. In both cases we may arrange that the given map sends the chosen axis to the chosen axis, and restrict it to the remaining summands. Iterate to cancel all the padding. The forward implication uses the identity on the added axes.

Start from the symmetric cubic isometry instance given by Grochow–Qiao. Pad both forms, multiply both by a common denominator. The triangulated construction multiplies the cup pairing by six. Both common scalings preserve isometry and similitude and keep the bit size polynomial. The polynomial triangulated framed surgery construction in the companion proof produces an oriented closed simply connected stably parallelizable smooth six-manifold with the resulting integral cup form and $H^3=0$. The lattice underlying $H^2$ is free. In the realization the divisibility by six supplies the Wall congruence with vanishing first Pontryagin class, and the spin condition is part of the construction. Thus each padded pair is realized by actual manifolds, and the previous two arguments give the asserted equivalence. The companion construction outputs a triangulation in polynomial time, and its intermediate integral cup table suffices for the cup-table version. [Triangulated construction](IntegralTensorManifolds.md) [Grochow–Qiao](https://arxiv.org/html/1907.00309#S3) · [Wall](https://doi.org/10.1007/BF01389738)

## Decidability and priority

Remark 3.4 asks about decidability of rational TI. Sarkisjan's Theorem 4.1 (Part I, p. 167) decides rational orbits for representations of linear algebraic groups over any number field provided the Hasse principle holds for the indicated simply connected semisimple cover. The Kneser–Harder–Chernousov theorem supplies that principle. This gives unconditional decidability of rational TI and of the manifold problem above. The literature result settles the decidability question through its applicability to the product general-linear action. The new claim here concerns the equivalence with existence of actual maps. [Remark 3.4](https://arxiv.org/html/1907.00309#S3) · [Sarkisjan, §4](https://www.mathnet.ru/links/0603804c36a51db932acf5e5c0b47658/sm2788_eng.pdf) · [Hasse principle cited in Borovoi–van Hamel, Proposition 5.8](https://pure.mpg.de/rest/items/item_3123433_2/component/file_3123434/content)

A second decidability route exhibits where the Brauer–Manin obstruction enters. The transporter of two points in a linear algebraic action is either geometrically empty or is a right torsor under the stabilizer. In characteristic zero it is smooth. Compute the geometric components by absolute decomposition, retaining the Galois-invariant ones, since every rational point belongs to one. Each retained component $X$ is a torsor under the identity component of the stabilizer. Take a smooth projective compactification $Y$ by constructive resolution. If $Y$ has a rational point, its elementary obstruction vanishes, hence so does that of $X$ by birational invariance. Density of $X(K_v)$ in the smooth $Y(K_v)$ and Proposition 5.8 of Borovoi–van Hamel imply $X(K)\ne\varnothing$. The converse is immediate. Sansuc's theorem says $Y(K)\ne\varnothing$ if its Brauer–Manin set is nonempty. Dovetail point enumeration on $X$ with the search for a finite Brauer–Manin obstruction on $Y$. The latter is effective by the projective Azumaya enumeration argument of Poonen, Remark 5.3. Thus at least one search halts for every component. This route provides a second explanation of decidability using established arithmetic results. [Borovoi–van Hamel, Proposition 8, Proposition 5.8 and Corollary 14](https://pure.mpg.de/rest/items/item_3123433_2/component/file_3123434/content) · [Poonen](https://arxiv.org/abs/math/0507329)

The main theorem is a written mathematical proof. No full theorem is claimed as Lean-checked. Priority for the crossover remains provisional.
