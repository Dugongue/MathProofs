# Rational-Point Decision on Smooth Hypersurfaces and Marked Projective Varieties

## Results and scope

1. For every fixed number field $K$, deciding whether a smooth geometrically integral affine hypersurface over $K$ has a $K$-point is many-one equivalent to Hilbert's tenth problem over $K$. There is also a Turing reduction uniform in the presentation of $K$. These results are unconditional.
2. Over $\mathbb Q$, Hilbert's tenth problem reduces to deciding whether a smooth projective geometrically integral variety has exactly one rational point or infinitely many, even when a rational point is supplied. Assuming [Glazer's claimed definition of the integers in the rationals](https://github.com/elliotglazer/diophantine-z-q), this promise problem is halting-complete on the fibers of one fixed smooth projective family with a section.

The first result answers the smooth-affine-hypersurface equivalence question in [Poonen, *Rational points on higher-dimensional varieties*, §1](https://people.mpim-bonn.mpg.de/zagier/files/doi/10.4171/OWR/2009/33/fulltext.pdf). The second gives a negative algorithmic answer to the finiteness half of [Poonen, *Rational Points on Varieties*, Question 2.6.7](https://math.mit.edu/~poonen/papers/Qpoints.pdf#page=64), over $\mathbb Q$ under the stated premise. The finite-input listing problem is separate. Publication priority for the reductions here is unverified. Poonen's [earlier smoothing result for integer solutions](https://math.mit.edu/~poonen/papers/automorphism.pdf) concerns an integral-point predicate. His [smooth projective rational-point existence reduction](https://math.mit.edu/~poonen/papers/chatelet.pdf) concerns nonemptiness.

## 1. Smooth affine hypersurfaces over each fixed number field

Let $h(Y)=Y^5+Y+1$. This polynomial is squarefree. A common root of $h,h'$ would satisfy $Y=-5/4$ and $5Y^4+1=0$, which is impossible. The smooth projective model of $z^2=h(y)$ is a genus-two curve over $K$, so its $K$-rational points are finite by Faltings's theorem. It has the two affine $K$-points $(0,\pm1)$.

Choose a nonsquare $c_0\in K^\times$ whose square class contains no nonzero first coordinate of an affine $K$-point on this curve. Such a class exists. The excluded list is finite, and the rational primes unramified in $K$ give infinitely many distinct square classes by their odd valuations at the primes of $K$ above them.

Given an input polynomial $f$ over $K$, take
$$
G(\mathbf x,u)=f(\mathbf x)^2-a u^2
$$
with a fixed nonsquare $a\in K^\times$. Then $G$ is nonconstant, and it vanishes on $K$ exactly when $u=0$ and $f(\mathbf x)=0$. Consider
$$
z^2=h\bigl(cG(\mathbf x,u)^2\bigr),\qquad
c\in c_0(K^\times)^2 .
$$
Any $K$-solution gives a point on the fixed genus-two curve with $y=cG^2$, so the choice of square class forces $G=0$. Conversely any solution of $f=0$ lifts with $u=0,z=1$.

The hypersurface is geometrically integral for every $c\ne0$. Reducibility of this monic quadratic over the algebraic closure would give a square root of $h(cG^2)$ in the rational function field of the $\mathbf x,u$ variables. That would give a nonconstant rational map from affine space to the genus-two curve. Restricting to a general line gives a nonconstant rational map from a projective line to the smooth projective model, which is impossible by Riemann–Hurwitz.

All but finitely many $c$ give geometric smoothness. A singular point must have $z=0$ and $cG^2$ a root of $h$. These roots are simple and nonzero, so the derivative in the $\mathbf x,u$ variables forces all partial derivatives of $G$ to vanish. A polynomial over an algebraically closed field of characteristic zero has finitely many critical values. Its differential vanishes on each irreducible component of its critical locus, so its restriction in the function field of that component is constant. Thus there are only finitely many nonzero values $g$ to exclude via $cg^2\in h^{-1}(0)$. Testing the Jacobian ideal for the unit ideal is effective. Search the infinite sequence $c=c_0n^2$ with positive integers $n$ until that test passes.

For each fixed $K$, $c_0$ can be hardcoded as a finite field element, giving a many-one reduction. The reverse reduction just reads the defining polynomial. The proof of a many-one reduction for each fixed $K$ does not require computing the list of $K$-points of the genus-two curve.

### Uniform reduction in the number field

A smooth-affine-hypersurface oracle can find a suitable $c_0$ uniformly. For each unramified rational prime $p$, query the affine curve
$$
v^2=p^5+p w^8+w^{10}.
$$
There is no $K$-point with $w=0$ because $p$ is a nonsquare. For $w\ne0$, the substitution $(y,z)=(p/w^2,v/w^5)$ identifies the $K$-points in the query with lifts of points having nonzero $y$ in the square class of $p$. The right side is squarefree. Its nonzero roots come from simple roots of $h$ under $w\mapsto p/w^2$, whose derivative is nonzero, and it does not vanish at $w=0$. Thus every query is smooth and geometrically integral. The first negative answer supplies a valid $c_0$, and a negative answer must occur because only finitely many square classes are excluded. Now apply the many-one construction to the original input. This proves a uniform Turing reduction, distinct from the per-field many-one assertion.

### Degree eight over the rationals

Over $\mathbb Q$ one can instead use the elliptic curve $E$ given by $y^2=z^3+z$. Its only affine rational point is $(0,0)$. If $z=a/b>0$ is in lowest terms, the equation forces $ab(a^2+b^2)$ to be a square. Its factors are pairwise coprime, so $a=A^2,b=B^2$ and $A^4+B^4$ is a square, contradicting [Fermat's descent](https://home.mathematik.uni-freiburg.de/arithgeom/lehre/ss20/algzt/TNT2.pdf). The cases $z<0$ and $z=0$ follow from the sign of $z^3+z$.

Compile $f=0$ into a finite system of quadratic equations by introducing arithmetic-gate variables. Take $G$ to be the sum of their squares and the square of an extra coordinate pinned to zero. Then the degree is at most four, $G$ is nonconstant, and rational zeros of $G$ correspond exactly to rational solutions of the compiled system. The hypersurface $z^3+z=c^2G^2$ has degree at most eight and exactly the required rational nonemptiness. It is geometrically integral because a reducible monic cubic over the geometric rational function field would have a root there, yielding a nonconstant rational map to $E$. A singular point requires $3z^2+1=0$, $G\ne0$, and $\nabla G=0$. The same critical-value argument and Jacobian test select a nonzero rational $c$ giving smoothness.

## 2. Exactly one or infinitely many points on a marked projective variety

Start with a polynomial $F(t,\mathbf x)$ over $\mathbb Q$, treating $t$ as a parameter. For the unrestricted reduction one can simply take the input polynomial independent of $t$ and carry out the construction for a single fiber. For the fixed-family assertion use MRDP and the assumed Diophantine definition of $\mathbb Z$ to choose one $F$ whose rational solvability for nonnegative integer $t$ is a fixed many-one complete halting predicate. Polynomial systems can be combined as sums of squares over $\mathbb Q$.

### Encode a bounded witness and an isolated marked point

Let $d$ be the degree of $F$ in the witness variables. Replace the witness $\mathbf x$ by $\mathbf y/b$ and impose
$$
 w=2v^2-1,\qquad b=w^2,\qquad b^d F(t,\mathbf y/b)=0,
$$
where the last expression is expanded as a polynomial. For rational $v$ one always has $b\ne0$. For every actual witness $\mathbf x$ one can choose rational $v\in(-1,1)$ as close to $1/\sqrt{2}$ as needed to make all the coordinates of $\mathbf y=b\mathbf x$ lie in $[-1,1]$. The witnesses $v,w,b,\mathbf y$ can thus be kept in a fixed bounded box. Compile these equations to a fixed system of equations $q_i(t,\mathbf a)=0$ of degree at most two in its witness variables, leaving $t$ in the coefficient ring. Every added gate variable is the value of a fixed polynomial in the bounded inputs and $t$. Consequently one can choose an explicit polynomial $C(t)$ with integer coefficients, for example using bounds on the sums of the absolute values of the gate coefficients, such that
$$
C(t)>2+\sum_i a_i^2
$$
on these chosen witnesses for every $t\ge0$. For a single input polynomial, a constant $C$ suffices. This bound only needs to hold on the chosen lifts.

Use one more variable $s$ with $s^2=s$. Homogenize each $q_i$ to degree two using $s$, calling the result $q_i^{[2]}(t,s,\mathbf a)$. Introduce one free rational coordinate $r$ and four slack coordinates $\mathbf u$. Use the quadratic system
$$
s^2-s=0,\qquad q_i^{[2]}(t,s,\mathbf a)=0,\qquad
s^2+\|\mathbf a\|^2+r^2+\|\mathbf u\|^2=C(t)s.
$$
On the $s=0$ branch the norm equation forces every coordinate to be zero, and that point satisfies the whole system. On the $s=1$ branch a solution decodes to a zero of $F$. Conversely for a zero of $F$ use a chosen bounded lift. For each rational $r\in[-1,1]$, the remaining slack is positive and is a sum of four rational squares by Lagrange's theorem, applied after clearing a square denominator. The different $r$ values yield infinitely many rational points. Thus the system has exactly one rational solution or infinitely many, according to solvability of $F(t,\mathbf x)=0$.

Let $\mathbf X$ collect all variables of this system and let $G_t(\mathbf X)$ be the sum of the squares of its left sides, with each equation written with right side zero. It has degree four. Let $G_t^h(H,\mathbf X)$ be its homogenization to degree four. At $H=0$ the leading term of the norm equation contributes $(\sum X_i^2)^2$, so
$$
G_t^h(0,\mathbf X)>0
\qquad
\text{for all nonzero }\mathbf X\in\mathbb Q^N .
$$

### Smooth the affine chart and keep rational points off the boundary

Consider the affine hypersurface
$$
z^3+z=c^2G_t(\mathbf X)^6.
$$
Its rational points have $z=0$ and $G_t=0$ by the preceding computation of the affine rational points of $E$, applied with $y=cG_t^3$. Thus it preserves the exact point counts, including the marked point $z=0,\mathbf X=0$. The monic cubic is geometrically irreducible over the spatial function field by the same rational-map argument to $E$. Singularity in the affine chart requires $3z^2+1=0$, $G_t\ne0$, and $\nabla G_t=0$. There are only finitely many bad $c$ for a single input, and only finitely many over the algebraic closure of the generic parameter field $\mathbb Q(t)$. Choose a positive rational prime $c$ outside the bad set. For a single input one can search primes with the Jacobian test. For the fixed family the choice is made once.

For compactification use the line bundle $\mathcal O(8)$ over $\mathbb P^N$ with homogeneous coordinates $(H,\mathbf X)$. Write $Z$ for the fiber coordinate, interpreted as a section of the pulled-back line bundle, and impose
$$
Z^3+H^{16}Z=c^2\bigl(G_t^h(H,\mathbf X)\bigr)^6 .
$$
All terms are sections of $\mathcal O(24)$. In a local trivialization this is a monic cubic in the fiber coordinate, so it defines a finite cover of $\mathbb P^N$, and in particular is projective. Over $H\ne0$ it is the original affine hypersurface. At a rational point of the base with $H=0$, choose a rational trivialization. The equation becomes $Z^3=c^2 g^6$ with $g=G_t^h(0,\mathbf X)\ne0$ in that trivialization. The right side has valuation $2$ modulo $3$ at the prime $c$, so there is no rational point above the boundary. This argument takes place in actual line-bundle fibers over rational points and needs no assumption on rational weighted coordinates.

Resolve the projective cover in characteristic zero by a projective resolution that is an isomorphism over the smooth locus. The affine chart is preserved. A rational point of the resolution above the boundary would map to a rational point of the original boundary, which has none. Hence the resolution is smooth, projective and geometrically integral, and has precisely the rational points of the affine chart. The supplied point is the unique lift of $(z,\mathbf X)=(0,0)$. Resolution can be performed effectively. [Włodarczyk, *Simple Hironaka resolution in characteristic zero*](https://www.math.purdue.edu/~wlodarcz/Hiron-Complexity/complexity.pdf)

### One fixed family and the decision problem

For the fixed-family assertion take the cubic cover over $\mathbb P^N\times\mathbb A^1$ and resolve its total space once. The cover is integral because it is locally free over the integral base and its monic cubic is irreducible at the generic point. Its generic fiber over the parameter line is geometrically integral and smooth on the affine chart by the choice of $c$. The generic fiber of the resolution is smooth and geometrically integral. Shrink to a nonempty Zariski open $U$ of the parameter line where the resolved morphism has smooth geometrically integral fibers and where the affine chart of the cubic cover has smooth fibers. Such an open exists by spreading out these generic properties and by properness for the resolved morphism. The resolution is an isomorphism over that affine chart on $U$, since relative smoothness there implies that the total space is smooth. The marked affine origin lifts to a section over $U$.

There are only finitely many excluded integer parameters. Use a padded halting set for $F$, with a distinct parameter for each pair consisting of the program input and a redundant padding index. For every input, search its padding indices until its parameter lies in $U$. This terminates and gives a many-one reduction to the promised family. The equations of the fixed family and the open $U$ are finite data that can be fixed once. The yes side is computably enumerable by searching for a point distinct from the section value. This proves halting completeness for infinitude, and co-halting completeness for uniqueness, on the stated promise.

Even without the integrality premise, the single-input construction reduces general rational polynomial solvability to the same marked one-versus-infinite promise. Conversely, testing whether a second rational point exists is an existential polynomial question. Use finitely many affine charts, express being distinct from the marked point by a nonzero coordinate difference or cross-product minor, and encode nonzeroness by an inverse witness. Over $\mathbb Q$ the finite disjunction of such systems is equivalent to one polynomial equation. Thus the promised decision problem and rational polynomial solvability are unconditionally many-one equivalent.

### Transfer to function fields with dense rational specializations

Let $L=\mathbb Q(X)$ for an integral $\mathbb Q$-variety $X$ with Zariski-dense rational points. Any finite polynomial system over $\mathbb Q$ solved in $L$ specializes to a rational solution. Choose a common nonempty affine open where the finitely many entries of a witness are regular, then evaluate at a rational point. Nonzeroness can be included by adjoining inverse witnesses. In particular, a $\mathbb Q$-variety with a finite set of rational points acquires no additional $L$-points. A hypothetical new point would give an existential solution of the equations for one chart with inequalities excluding all the old points, hence an additional rational point. If the rational point set is infinite it remains infinite over $L$. Thus the same marked family has the same one-versus-infinite dichotomy over all these function fields, including the purely transcendental case.
