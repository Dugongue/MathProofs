# A strict second-to-third Hella game separation on colored groups

Two-colored elementary abelian 2-groups require unboundedly many pebbles in Hella's second bijective game, even when the marked generated subgroup is initially colored in full. In the third game three pebbles in a single round identify every finite colored group. Thus there is a strict width separation between the second and third levels on this class. This strengthens the earlier colored abelian ordinary-WL result. It does not imply the corresponding lower bound for uncolored groups in Grochow–Levet Question 5.5. [Hella games and Questions 5.3–5.5](https://arxiv.org/html/2209.13725v7#S5) · [Earlier colored abelian lower bound](https://github.com/Dugongue/MathProofs/tree/main/ColoredAbelianWL)

## The two colorings

For a given pebble bound \(k\), take \(s\ge k+1\). Let \(X=\mathbb F_2^{s+2}\), and let \(\Phi(x)\) list all nonconstant squarefree monomials in \(x\) of degree at most \(s\). Use the group \(X\oplus Y\), with \(Y\) the dual-coordinate space for \(\Phi\). Its two colorings are
\[
c_0(x,y)=\langle y,\Phi(x)\rangle,\qquad
c_1(x,y)=\langle y,\Phi(x)\rangle+\prod_i x_i.
\]
Their Boolean polynomial degrees are \(s+1\) and \(s+2\), respectively. Invertible binary linear substitution preserves this degree, since substitution followed by squarefree reduction does not increase it and the inverse gives the reverse bound. Thus the colored groups are nonisomorphic.

For the game, maintain a linear shear on the span of the marked first coordinates. If \(U\subseteq X\) is that span, the shear is \((x,y)\mapsto(x,y+Lx)\) for a linear \(L:U\to Y\), and it preserves colors for every \((x,y)\) with \(x\in U\). This implies preservation of the full marked generated subgroup. When replacing pebbles, restrict to those retained and choose a complement \(X=U\oplus W\). We have \(\dim U\le s-1\). In coordinates \(a,w\) for these spaces write
\[
E(a,w)=\prod_i(a+w)_i+\langle La,\Phi(a+w)\rangle .
\]
It has degree at most \(s+2\) and vanishes at \(w=0\). The linear span of \(\Phi\)'s coordinates is exactly the space of zero-constant polynomials of degree at most \(s\), and this remains true in the adapted coordinates. Thus slots below may be specified using monomials in those coordinates.

## Extending across a pair selected after one bijection

There exists \(P:W\to Y\) with \(P(0)=0\) and
\[
\big\langle P(z+w)+P(z),\Phi(a+w)\big\rangle=E(a,w)
\quad\text{for all }a,w,z.
\]
Construct it one monomial \(m\) of \(E\) at a time. Each has a \(W\)-factor. If \(\deg m\le s+1\), choose one factor \(w_i\) and put \(z_i\) in the slot for \(m/w_i\); if that slot would be constant, use the slot for \(w_i\), since \(w_i^2=w_i\). The derivative pairs to \(m\). For \(\deg m=s+2\), at least three factors are from \(W\). Choose three and, for each of their three pairs \(i,j\), put \(z_i z_j\) in the slot for \(m/(w_i w_j)\). Under \(z\mapsto z+w\) each quadratic difference has two cross terms and the term \(w_i w_j\). The cross terms for each vertex of the triangle occur twice, so cancel, while the three copies of \(m\) add to \(m\). Sum these contributions.

Announce the single bijection \((a+w,y)\mapsto(a+w,y+La+P(w))\) for the round. The first-coordinate components of a pair selected by Spoiler add at most two new \(W\)-directions \(w_1,w_2\). Extend the shear linearly on these directions using \(P(w_1),P(w_2)\). This is consistent when a direction is zero or when the directions coincide. The displayed derivative identity with \(z=0\) proves color preservation on each singleton direction, and with \(z=w_1\) and \(w=w_1+w_2\) proves it on their sum. Together with the old \(U\) condition this verifies the invariant on the whole extended subgroup. It works also for moves from the other structure by using the inverse announced bijection. The invariant can therefore be maintained for arbitrarily many rounds. The group rank is \(2^{s+2}-2\), so the pebble obstruction has the same logarithmic-logarithmic scale in group order as the earlier one-point construction.

In the third game, after a single bijection is announced, either it mismatches a color at some point, or it fails to preserve a multiplication triple \((x,y,xy)\) if the two colored groups are nonisomorphic. Spoiler can select the offending one or three points together, and the violation is already visible under the weaker ordinary partial-isomorphism test. This gives the upper level of the claimed strict separation. This proof is informal.
