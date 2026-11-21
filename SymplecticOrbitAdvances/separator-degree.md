# Exponential separating degree for single symplectic cubics

**Theorem.** For every \(m\ge 3\), there are explicit integer-coordinate pairs in \(\operatorname{Sym}^3(\mathbb C^{2m})\) and in \(\bigwedge^3(\mathbb C^{8m})\) with distinct closed symplectic orbits. No invariant of degree below
\[
D_m=\frac{4(2^m-1)}{\gcd(7,2^m-1)}
\]
separates either pair. Under the natural inclusions into ordered cubics the same lower bound holds for the product of three independent symplectic groups, with both displayed product orbits also closed. Consequently each of these single-tensor formats needs exponential degree in the side dimension to separate all orbit closures.

The cyclic recurrence is related to the earlier exact separating degree for balanced general-linear signatures. Here the guards and payload belong to one cubic, under a symplectic group, and full orbit closedness follows from a diagonal Gram computation. [Earlier exact general-linear separation degree](https://github.com/Dugongue/MathProofs/blob/main/GrochowResearchSynthesis/EXACT-GL-SEPARATOR-DEGREES.md), [Derksen–Makam on other tensor representations](https://arxiv.org/abs/2107.06838).

**Symmetric cubic.** Take an orthonormal symplectic basis \(e_i,f_i\), \(0\le i<m\), with indices modulo \(m\). Write a monomial below for the sum of its distinct permutations in the ordered tensor power. Let
\[
g_i=e_i e_i f_{i+1},\qquad h_i=f_i f_i e_{i+1},\qquad p=e_0 e_1 e_2.
\]
Take \(T_x=\sum_i(g_i+h_i)+xp\) for \(x=0,1\). Within the tensor support no two distinct ordered coordinates differ only in a single position. Indeed distinct guard multisets share at most one entry with multiplicity, a guard and the payload share at most one, and distinct permutations of the same multiset cannot agree at two positions. The assumption \(m\ge3\) precludes a two-cycle of guard indices. Thus all single-mode partial Hermitian Gram matrices are diagonal and identical. This remains so after any diagonal rescaling.

The real positive symplectic diagonal torus acts by \(e_i\mapsto \exp(u_i)e_i\), \(f_i\mapsto\exp(-u_i)f_i\). Write \(\epsilon_i\) for the coordinate character of \(e_i\). Guard and reversed guard have weights \(\pm w_i\) with \(w_i=2\epsilon_i-\epsilon_{i+1}\), and equal squared norm \(a_i\) before rescaling. These weights span the real character space, since \(2u_i=u_{i+1}\) cyclically forces all \(u_i=0\). Along the diagonal torus the squared norm is a sum of terms
\[
\sum_i a_i\bigl(e^{2w_i(u)}+e^{-2w_i(u)}\bigr)
        +x^2\|p\|^2 e^{2(\epsilon_0+\epsilon_1+\epsilon_2)(u)}.
\tag{1}
\]
The paired guard contribution is coercive because the weights span. It is bounded below by \(2\sum_i a_i\), achieved at \(u=0\). For \(x=1\) the norm attains its torus minimum at a finite \(u\), and the value there is strictly larger than \(2\sum_i a_i\).

At each torus minimizer the derivative vanishes in all real symplectic diagonal directions. Because the Gram is diagonal, its pairing with every Hermitian symplectic Lie algebra element also vanishes: the diagonal part of such an element is itself in the symplectic Lie algebra. For the single group the moment is three times the pairing with the first Gram. For the product group the three Grams are identical, so each factor has zero moment separately. Thus each torus minimum is also a minimum in the full corresponding orbit, and the orbit is closed by Kempf–Ness. Their distinct minimum norms ensure that the orbits are distinct. [Kempf–Ness](https://doi.org/10.1007/BFb0066647).

**Alternating cubic.** Use four orthonormal symplectic pairs \(e_{i,a},f_{i,a}\) for every \(i\), with \(a\) modulo \(4\). Replace each guard and its reverse by
\[
g_{i,a}=e_{i,a}\wedge e_{i,a+1}\wedge f_{i+1,a},\qquad
h_{i,a}=f_{i,a}\wedge f_{i,a+1}\wedge e_{i+1,a},
\]
and use payload \(p=e_{0,0}\wedge e_{1,0}\wedge e_{2,0}\), represented by the full alternating sum in the tensor power. Again any two different support triples share at most one element. Within a layer the pairs in the four-cycle share at most one, and across layers the opposite-variance guards can share both types only if the layer cycle has length two. The payload uses three different layers. All partial Grams are diagonal and identical. For the full real positive symplectic diagonal torus, the guard and reverse weights are opposite. Their span is the full character space: a vector annihilated by all guards satisfies
\[
u_{i+1,a}=u_{i,a}+u_{i,a+1}.
\]
Writing \(S\) for cyclic shift on the four coordinates, this is \(u_{i+1}=(I+S)u_i\). The eigenvalues \(2,0,1+i,1-i\) of \(I+S\) are never roots of unity, hence \((I+S)^m-I\) is invertible. The same coercivity, moment, and unequal-minimum argument proves the closed-orbit assertion.

**Degree calculation.** In the alternating case restrict to the subtorus identifying the four characters in each layer. Its guard and reverse weights become \(w_i,-w_i\), and the payload has weight \(\epsilon_0+\epsilon_1+\epsilon_2\), exactly as in the symmetric case. In the product group use the diagonal copy of this torus in the three factors. The independent guard, reverse, and payload coordinates parametrize a torus-stable linear coordinate slice. Thus restriction of a polynomial invariant preserves its degree bound and only contains weight-zero monomials. A monomial distinguishing \(T_0,T_1\) must use the payload with some exponent \(t>0\).

Put \(M=2^m-1\). Map the character lattice to \(\mathbb Z/M\) by \(\epsilon_i\mapsto 2^i\). All \(w_i\) map to zero and the payload weight maps to \(7\). Therefore \(M\mid 7t\), giving \(t\ge M/\gcd(7,M)\). Applying the sum-of-coefficients map to the same weight equality gives
\[
r=3t+f,
\]
where \(f\) and \(r\) are the total forward and reverse exponents. The total degree is \(t+f+r\ge 4t\), proving the displayed bound. The assertion is a lower bound on the minimum separating degree for the full symplectic invariant rings.
