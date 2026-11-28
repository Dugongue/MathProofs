# Exact smooth affine hypersurface realizations over every global field

**Theorem.** There is one algorithm taking a global field \(k\) and any list of polynomial equations in \(m\ge1\) unknowns over \(k\). It outputs a smooth geometrically integral hypersurface \(H\subseteq\mathbb A_k^{m+1}\) whose projection onto the first \(m\) coordinates induces a bijection from \(H(k)\) to the solutions of the given list. This projection is finite étale over an explicitly specified principal open in \(\mathbb A^m_k\) and has image that open. The theorem holds in every characteristic and adds exactly one ambient coordinate. For \(m=0\) the rational-point bijection alone holds with ambient dimension at most two, using the unique projection to \(\mathbb A_k^0\).

Thus the rational-point decision problems for arbitrary affine varieties and for smooth geometrically integral affine hypersurfaces are uniformly computably many-one equivalent over all global fields. The comparison applies to arbitrary systems over a number field or a finite extension of \(\mathbb F_p(t)\), including characteristic two. The construction invokes Poonen's effective construction of a curve with exactly one rational point. [Poonen, Curves over every global field violating the local-global principle](https://arxiv.org/abs/0902.3965).

## 1. A plane curve with a known rational point and an étale projection

Apply Poonen's Theorem 1.1 with \(n=1\) to get a smooth projective geometrically integral curve \(C/k\) with \(C(k)=\{P\}\). The unique point \(P\) is computable by enumeration in projective coordinates.

We first choose a finite morphism \(t\colon C\to\mathbb P^1\) such that \(t(P)=0\) and the geometric fibers above both zero and infinity are reduced. Here is a construction that also works in positive characteristic. Take a sufficiently large power \(L\) of a line bundle from a projective embedding of \(C\). Use a section of \(L(-P)\) whose zero divisor is geometrically reduced and excludes \(P\). Such sections form a nonempty open because \(L(-P)\) can be made very ample. Indeed, over the algebraic closure the hyperplanes for the embedding by \(L(-P)\) that contain a tangent line form a proper closed subset of the dual projective space. The same holds for hyperplanes through the image of \(P\). The field \(k\) is infinite, so this open has a \(k\)-point. Viewing the section as a section \(s_0\) of \(L\) gives a simple zero at \(P\) and a geometrically reduced zero divisor. Choose a section \(s_\infty\) of \(L\) with geometrically reduced zero divisor disjoint from that of \(s_0\), by the same hyperplane argument. Set \(t=s_0/s_\infty\). The two sections have no common zeros, the map is nonconstant, and its two stated fibers are reduced. Properness and finite fibers make \(t\) finite. A simple zero implies separability. The poles of \(t\) on \(C_{\bar k}\) are all simple. For effectivity, spaces of sections are computable by linear algebra on the curve, or using restrictions of homogeneous forms for sufficiently high powers. The geometric reducedness and disjointness conditions are decidable by elimination. Searching powers and candidate sections therefore terminates.

Let \(B\) be the coordinate algebra of \(t^{-1}(\mathbb A^1)\). It is finite free of rank \(d=\deg t\) over \(k[T]\), because it is finite torsion-free over that PID. Choose \(y\in B\) taking different values on the \(d\) distinct geometric points over zero. To do this, choose a sufficiently large pole bound supported on the fiber over infinity. Riemann–Roch gives surjectivity of evaluation on the zero fiber once the bound is large. In that finite-dimensional space of sections, choose a point outside the finitely many hyperplanes where two geometric values agree. These tests and the search are effective.

Write \(P_0(T,Y)\) for the characteristic polynomial of multiplication by \(y\) on \(B\), which can be computed as the monic minimal polynomial of \(y\) over \(k(T)\) by elimination. To verify the equality of these polynomials, the characteristic polynomial specializes at zero to a product of distinct linear factors over \(\bar k\). The characteristic polynomial of multiplication by an element of a field extension is a power of its minimal polynomial. Its characteristic polynomial is squarefree at the generic point because it is squarefree at zero, so this power is one. The argument also works after replacing \(k\) by \(\bar k\), where the function field remains a field. Hence \(P_0\) is monic of degree \(d\) and geometrically irreducible. Put \(\Delta(T)=\operatorname{disc}_Y P_0(T,Y)\); then \(\Delta(0)\ne0\).

Over \(\Delta\ne0\), the equation \(P_0=0\) describes the given curve over the line. In fact \(k[T,1/\Delta,Y]/(P_0)\) is finite étale over \(k[T,1/\Delta]\), so is a normal domain. Its finite integral extension \(B[1/\Delta]\) has the same fraction field and therefore equals it.

The following elementary translation incorporates the open condition in a single affine equation. If \(P_0(T,Y)=Y^d+\sum_{i<d}b_i(T)Y^i\), put

\[
Q(T,Z)=(\Delta Z+1)^d+\sum_{i<d} b_i(T)\Delta^{d-i}(\Delta Z+1)^i.
\]

The polynomial \(Q\) equals 1 modulo \(\Delta\), so \(\Delta\) is a unit in the coordinate ring of \(Q=0\). On that open, the substitution \(Y=Z+1/\Delta\) transforms \(Q=0\) into \(P_0=0\). Consequently the plane curve \(C_*:=V(Q)\) is geometrically integral, its map to the \(T\)-line is étale, and \(C_*(k)\) is precisely one point, with \(T=0\). All these constructions depend only on the field \(k\).

## 2. Compression and a simple-pole irreducibility argument

Compress the given list \(f_1,\dots,f_s\) to the equation \(f=0\) by putting \(f=\operatorname{Norm}_{M/k}(\sum_i f_i\beta_i)\), where \((\beta_i)\) is a basis of a separable extension \(M/k\) of degree \(s\). Define \(f=0\) identically if the list is empty. Such extensions can be constructed by lifting monic irreducible polynomials from a finite residue field. A monic lift with irreducible reduction is irreducible over the completed field and hence over \(k\), and separability of the reduction implies separability of the lift. A norm is zero precisely on the zero field element, so the compression preserves solutions without adding variables.

Assume first that \(f\) is nonconstant, of total degree \(e\). Make an invertible linear change over \(k\) in the \(m\) spatial coordinates so that in the new first coordinate \(x_1\), its degree is \(e\) and its leading coefficient \(a_e\) is a nonzero scalar. In fact, choose the direction of \(x_1\) to have nonzero evaluation under the top homogeneous part of \(f\), which is possible over the infinite field \(k\). Write the remaining coordinates as \(\boldsymbol x'\).

Let \(K=\bar k(C)\), and let \(v\) be the normalized valuation of \(K\) at any geometric pole of \(t\). Extend it to \(K(\boldsymbol x')\) by the Gauss valuation, assigning each spatial coordinate valuation zero. The polynomial \(f(x_1,\boldsymbol x')-t\) is irreducible over \(K(\boldsymbol x')\). To see this, take the reversed polynomial

\[
 t^{-1} U^e\big(f(U^{-1},\boldsymbol x')-t\big).
\]

Its leading coefficient is \(t^{-1} f(0,\boldsymbol x')-1\), a unit since \(v(t)=-1\). All its lower coefficients have positive valuation, and the constant coefficient \(t^{-1}a_e\) has valuation exactly one. Eisenstein's criterion proves irreducibility of the reversed polynomial, and reversing preserves irreducibility here since the leading and constant coefficients are nonzero. This argument works even when the spatial polynomial is inseparable in \(x_1\).

## 3. The hypersurface and its full rational point set

For nonconstant \(f\), output the single equation

\[
Q\big(f(\boldsymbol x),Z\big)=0.
\]

This is the fiber product of \(C_*\to\mathbb A^1\) with the map \(f\) from affine space. It is finite étale over the principal open \(\Delta(f)\ne0\), surjectively because the cover of the open \(T\)-line has constant positive degree. This proves smoothness.

Over \(\bar k\), its coordinate ring is

\[
A[\boldsymbol x]/(f(\boldsymbol x)-T),\qquad A=\bar k[C_*].
\]

Compute in the coordinates used in Section 2, where the relation has a scalar unit as its leading coefficient in \(x_1\). Division by this relation makes the displayed algebra free over the domain \(A[\boldsymbol x']\) with basis \(1,x_1,\ldots,x_1^{e-1}\). It injects into the corresponding quotient over the fraction field \(K(\boldsymbol x')\). That quotient is a field by Eisenstein's criterion above, so the original hypersurface is geometrically integral.

A \(k\)-point maps to the unique \(k\)-point of \(C_*\), so \(f=0\). Conversely any solution of \(f=0\) has precisely one lift, obtained by taking the known point on \(C_*\) for the additional coordinate. This description uses the original spatial coordinates, since the temporary linear change was only for the integrality proof.

If \(f\) vanishes identically, use the hypersurface \(Z=0\). If \(f\) is a nonzero constant and \(m\ge1\), replace it by a fixed monic irreducible quadratic in the first spatial coordinate and apply the same construction. Both equations have empty rational zero sets, and the quadratic is available by lifting an irreducible quadratic from a finite residue field. If there are no spatial coordinates and no solutions, apply this last construction with one dummy coordinate. If there is one solution in zero spatial coordinates, \(Z=0\) in the affine line has precisely one rational point. This handles all inputs. The reverse decision reduction just reads the one defining equation of the hypersurface.

## Scope and relation to previous work

The result gives a uniform exact form of the smooth affine reduction. The prior MathProofs theorem gave a many-one reduction for a separately fixed number field, with a nonuniformly chosen square class, and a uniform Turing reduction. The present construction is a single many-one reduction in the field presentation, includes positive characteristic, and preserves individual solutions bijectively with one additional coordinate. It requires no Diophantine definition of the integers in the rationals and no finiteness hypothesis on the input point set. Poonen's older smoothing construction for integral points and his smooth projective rational-point reduction address related decision problems. [Prior smooth affine reduction](https://github.com/Dugongue/MathProofs/blob/main/RationalPointDecision/PROOF.md) · [Poonen, Automorphisms mapping a point into a subvariety](https://arxiv.org/abs/0902.3571) · [Poonen, Existence of rational points on smooth projective varieties](https://arxiv.org/abs/0712.1782).
