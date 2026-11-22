# Bounded-degree arithmetic traces of smooth hypersurfaces

Fix a number field $K$ and a positive integer $D$. The **bounded-degree arithmetic trace** of a $K$-scheme $X$ is the functor taking a finite extension $E/K$ with $[E:K]\le D$ to $X(E)$, with the usual maps induced by $K$-embeddings between such fields. Its data include the closed points of $X$ of degree at most $D$, their residue fields, and their behavior under the allowed embeddings.

## Realization theorem

Let $X\subseteq\mathbb A^n_K$ be an affine closed subscheme defined by finitely many equations. There is a closed immersion $i:X\hookrightarrow H$ into a smooth geometrically integral affine hypersurface $H\subseteq\mathbb A^{n+2}_K$ with the following properties.

1. For every finite field extension $E/K$ of degree at most $D$, the map $i_E:X(E)\to H(E)$ is a bijection. These bijections commute with $K$-embeddings between such extensions.
2. The hypersurface has a point over every completion of $K$.

For fixed $K,D$, the transformation from a finite list of defining equations to a defining polynomial for $H$ is computable. It uses one field-dependent prime chosen by a finiteness argument. Uniform computation of that prime from $K,D$ is a separate problem. If the input equations have degree at most $b$ and there are $r$ of them, the output polynomial in the proof has degree $O(D^2 [K : \mathbb Q](D+r+1)(b+1))$.

### A curve that controls every extension of bounded degree

Choose an odd prime $\ell>2D$ with $\ell-1>D[K : \mathbb Q]$, and put $m=2\ell+1$ and $L=D+1$. Let $C$ be the smooth projective model of
$$
z^\ell=1+y^m.
$$
Projection to $y$ has degree $\ell$. The extension of function fields has full ramification at the $m$ simple zeros of $1+y^m$ and at infinity, with no other ramification. Riemann–Hurwitz gives
$$
g(C)=\frac{(\ell-1)(m-1)}{2}=\ell(\ell-1).
$$
A map of degree $e<\ell$ to the projective line over $\overline K$ would give a second function independent of $y$. In fact a nonconstant function in $\overline K(y)$ has degree divisible by $\ell$ on $C$. Since $\overline K(C)/\overline K(y)$ has prime degree, the two functions generate $\overline K(C)$. The two projections would therefore map $C_{\overline K}$ birationally onto a curve in $\mathbb P^1\times\mathbb P^1$ of arithmetic genus $(\ell-1)(e-1)$. This is smaller than $g(C)$. Thus the geometric gonality is $\ell$.

Frey's bounded-degree point theorem says that a curve over a number field with infinitely many closed points of degree at most $D$ has gonality at most $2D$. For the needed implication, suppose there are infinitely many closed points of some degree $d\le D$. They give infinitely many $K$-points in the $d$-th symmetric power. Its image $W_d$ under the Abel map also has infinitely many $K$-points, since distinct linearly equivalent effective divisors of degree $d$ would give a pencil of degree at most $d$. The Abel map makes sense in a translate of the Jacobian using $(y,z)=(0,1)$. By Faltings, $W_d$ contains a translate of a positive-dimensional abelian subvariety. Fix a total class in the sum of that translate with itself. There are infinitely many ways to write it as the sum of two points of the translate. The corresponding effective divisors of degree $2d$ include infinitely many distinct divisors, since a fixed effective divisor has finitely many effective subdivisors. Two distinct linearly equivalent divisors give a pencil of degree at most $2d$, a contradiction. Thus $C$ has only finitely many closed points of degree at most $D$. [Frey, Proposition 2](https://doi.org/10.1007/BF02758637) · [Faltings](https://annals.math.princeton.edu/1991/133-3/p04)

Choose a rational prime $p$ unramified in $K$ such that each finite nonzero $y$-coordinate of these points is a unit at every place above $p$ in its field of definition. Only finitely many rational primes are excluded. Let $c=p a^L$ with $a\in K^\times$. If $E/K$ has degree at most $D$, $g\in E^\times$, and $w$ is a place of $E$ above $p$, then
$$
v_w(cg^L)\equiv v_w(p)\pmod L,\qquad 1\le v_w(p)\le D.
$$
Here valuations have value group $\mathbb Z$, and the upper bound follows from the unramified choice of $p$ in $K$. Hence $cg^L$ is never the nonzero $y$-coordinate of an $E$-point on the affine chart of $C$.

### Encode all equations and preserve the field of definition

Write $f_1,\ldots,f_r\in K[\mathbf x]$ for the input equations. Choose a prime $s>\max(D,r)$ and a rational prime $p'$ unramified in $K$. The polynomial $T^s-p'$ is Eisenstein at a place of $K$ above $p'$. Set $K'=K(\alpha)$ for a root $\alpha$. For every $E/K$ of degree at most $D$, $[E(\alpha):K]$ is divisible by $s$ and $[E:K]$ is prime to $s$. It follows from $[E(\alpha):E]\le s$ that $[E(\alpha):E]=s$. The norm polynomial
$$
G(\mathbf x,u)=\operatorname{Norm}_{K'/K}
 \left(u+\sum_{j=1}^r\alpha^j f_j(\mathbf x)\right)
$$
is monic of degree $s$ in $u$, and over every such $E$ its zeros are precisely the tuples with $u=0$ and $f_1=\cdots=f_r=0$.

Take
$$
H\colon\qquad z^\ell=1+(cG(\mathbf x,u)^L)^m.
$$
An $E$-point of $H$ gives an $E$-point of $C$ with $y=cG^L$. Its image is a closed point of degree at most $D$. The valuation condition forces $G=0$, and then $u=0$ and every $f_j$ is zero. Also $z^\ell=1$ forces $z=1$, since a nontrivial $\ell$-th root of unity generates a field of degree $\ell-1>[E : \mathbb Q]$ over $\mathbb Q$. The required closed immersion is $\mathbf x\mapsto(\mathbf x,0,1)$. Projection to $\mathbf x$ gives the inverse on bounded-degree points and commutes with the field embeddings.

For smoothness, a singular point over $\overline K$ requires $z=0$, $G\ne0$, $dG=0$, and $1+(cG^L)^m=0$. The differential of $G$ vanishes along every irreducible component of its critical locus, so $G$ is constant on each component in characteristic zero. There are finitely many critical values. Consequently only finitely many $c$ are excluded. For every other $c$, the polynomial $1+(cG^L)^m$ has a nonempty reduced zero divisor over $\overline K$. Nonemptiness follows because $G$ is monic of positive degree in $u$. Reducedness follows because its differential is nonzero on that divisor. Its simple divisor valuations make it a non-$\ell$-th-power in the rational function field. The extension in $z$ is therefore irreducible by prime-degree Kummer theory, and the hypersurface is geometrically integral.

The norm has total degree at most $s\max(1,b)$, so a degree bound for the defining polynomial is $\max(\ell,mLs\max(1,b))$. Taking primes in intervals given by Bertrand's postulate yields the stated bound.

### Arrange points at all completions

Put $G_0(u)=G(0,u)$ and $N=sLm$. This is a fixed monic degree-$s$ polynomial for each input. Call a finite place bad if a coefficient of $G_0$ is nonintegral there, its residue characteristic divides $\ell m$, or its residue cardinality $q$ fails
$$
q+1-(N-1)(N-2)\sqrt q>\ell(N+1).
$$
Only finitely many places are bad. Choose a positive rational integer $A$ divisible by large enough powers of all rational primes below these places so that
$$
v\big((pA^L)^mG_0(0)^{Lm}\big)>2v(\ell)
$$
at each bad place. If $G_0(0)=0$, take $A=1$, since the point with $\mathbf x=u=0,z=1$ then works everywhere. Choose $c=p(An)^L$ with a positive integer $n$ outside the finitely many smoothness exceptions. The factor $n$ contributes nonnegative valuation at every finite place, so all the required inequalities persist. At any bad place, Hensel's lemma applied at $z=1$ to $z^\ell-1-c^m G_0(0)^{Lm}$ gives a local point with $\mathbf x=u=0$.

At a good place with $c=0$ in the residue field, the residue point with $u=0,z=1$ has nonzero $z$-derivative and lifts. At a good place with $c\ne0$ in the residue field, work with the affine residue curve
$$
z^\ell=1+(cG_0(u)^L)^m.
$$
It is geometrically integral. Otherwise prime-degree Kummer theory over the algebraic closure of the residue field would give a rational root in $z$ as a function of $u$. The functions $z$ and $y=cG_0(u)^L$ would then give a nonconstant map from $\mathbb P^1$ to the smooth projective model of $z^\ell=1+y^m$ in that characteristic. The same tame ramification calculation gives positive genus for this target, and Lüroth's theorem rules out such a map even in positive characteristic.

The residue curve has plane degree at most $N$, so its smooth projective normalization has genus at most $(N-1)(N-2)/2$. The projection to $u$ has degree $\ell$. At most $\ell(N+1)$ geometric points lie above $u=\infty$ or the roots of $1+(cG_0^L)^m$. The Hasse–Weil bound and the definition of a good place therefore supply a residue point with affine $u,z$ and $z\ne0$. Its $z$-derivative is nonzero, so Hensel gives a point of $H(K_v)$ by lifting $u$ and taking $\mathbf x=0$. At real places an $\ell$-th root exists because $\ell$ is odd. At complex places a root always exists.

Given $K,D$, the choices of $\ell,m,L,p$ can be fixed independently of the input. For each input one computes the norm, the finite set of bad places, and a sufficiently divisible $A$. Test geometric smoothness for $c=p(An)^L$ by the Jacobian ideal until the unit ideal occurs. This terminates and proves the effectiveness assertion.

## Consequences

**Prescribed closed points through a fixed degree.** Fix any positive dimension $h$ and any finite multiset of finite extensions of $K$ of degree at most $D$. There is a smooth geometrically integral affine hypersurface of dimension $h$ with points over all completions of $K$ whose entire multiset of closed residue fields of degrees at most $D$ is the given multiset. For a nonempty list, take a squarefree product $f(t)$ of minimal polynomials of primitive generators of the specified fields. Translating the generators by elements of $K$ gives distinct irreducible polynomials for repeated fields. For an empty list use $f(t)=t^s-p'$ with a prime $s>D$, which has no roots in the prescribed extensions. Use the preceding construction with
$$
G(t,u_2,\ldots,u_h)=\operatorname{Norm}_{K'/K}
 \left(f(t)+\sum_{j=2}^h\alpha^{j-1}u_j\right),
$$
where the norm extension has prime degree greater than $\max(D,h)$. This realizes exactly the same bounded-degree field points as the zero set of $f$ with all $u_j=0$. The polynomial $G$ is monic and nonconstant on the line $u_2=\cdots=u_h=0$. The local proof uses this line, with its actual degree in place of $s$ in the definition of $N$. The constructed immersion preserves residue fields, so the point-by-point bijection identifies the entire multiset. In particular there are everywhere locally soluble smooth affine curves with no points over any extension of degree at most $D$, and curves with exactly two degree-two closed points having a specified common quadratic residue field and no other points through degree $D\ge2$.

**Local solubility does not simplify bounded-degree global point decision.** For any fixed $K,D$, ordinary polynomial solvability and solvability on everywhere locally soluble smooth affine hypersurfaces are equivalent at the level of the entire set of extensions of degree at most $D$ over which a solution exists. The result keeps every witness and its field embeddings, so it also preserves exact finite counts over any specified extension in that range.

**Integral traces and a halting-complete family.** If $X$ is defined over the ring of integers $\mathcal O_K$, use the same defining equations over $\mathcal O_K$. The norm $G$ has integral coefficients since $\alpha$ is integral. More generally the integer $A$ above can clear the denominators of all coefficients of $G$, so the equation $z^\ell=1+p^m(AnG)^{Lm}$ gives an integral model whenever it is needed. For integral input the closed immersion identifies all $X(\mathcal O_E)$ with all $H(\mathcal O_E)$ for $[E:K]\le D$. This follows by intersecting the field-point bijection with the coordinatewise integrality conditions. The local witnesses in the proof have integral coordinates at every finite place, since the Hensel lifts were made in the valuation rings.

For any fixed $K,D$, deciding whether an output model has an $\mathcal O_K$-point is computably enumerable complete, even with fixed bounds on ambient dimension and degree and with the promise of integral local points everywhere. Apply the Davis–Putnam–Robinson–Matiyasevich theorem to a fixed universal computably enumerable predicate on natural numbers, then use the Diophantine definition of $\mathbb Z$ in $\mathcal O_K$ given by Koymans–Pagano, Theorem 1.2. This gives a fixed polynomial system apart from its substituted integer parameter. The theorem transfers its integral solutions, with dimensions and degrees bounded independently of the parameter. Searching for tuples over $\mathcal O_K$ gives computable enumerability. The smoothness assertion is on the generic fiber, and the integral model has local points at every finite place. Poonen's earlier integral smoothing theorem gives undecidability over $\mathbb Z$ on smooth hypersurfaces and precedes this application. The added scope here is the simultaneous integral trace and the everywhere locally integral promise. [Koymans–Pagano, Theorem 1.2](https://arxiv.org/html/2412.01768v3#S1.SS2) · [Poonen, Lemma 4.1](https://math.mit.edu/~poonen/papers/automorphism.pdf#page=3)

## Research scope and prior work

The object is the truncated point functor, together with the natural transformations induced by $K$-morphisms. The theorem shows that within this functor every finite system of equations can be replaced by one smooth geometrically integral affine hypersurface with points at all completions. The trace does not capture infinitesimal structure. The theorem uses a finite degree cutoff, and it concerns affine hypersurfaces.

Our earlier single-field construction transfers nonemptiness to smooth affine hypersurfaces. Poonen transfers rational-point decision to smooth projective geometrically integral varieties. Frey's criterion controls the bounded-degree points of the auxiliary curve. Here the added claims are simultaneous exact point-set realization over all bounded-degree extensions, compatibility with embeddings, prescribed residue-field multiplicities, and local solubility everywhere. A targeted literature search did not identify this combined theorem. Publication priority is provisional. [Earlier affine reduction](https://github.com/Dugongue/MathProofs/blob/d6933df162f8e998f27e007a42b8b6e55bb4858b/RationalPointDecision/PROOF.md) · [Poonen's projective reduction](https://doi.org/10.4171/JEMS/159)

A natural next question is whether the same bounded-degree functors can be realized by smooth projective hypersurfaces, with no additional bounded-degree points at infinity. Another is whether the prime selection can be made effective uniformly in $K,D$. The results here are written proofs.
