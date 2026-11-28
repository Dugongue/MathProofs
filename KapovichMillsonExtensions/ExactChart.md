# Exact algebraic \(\mathrm{SL}_2\) charts and the compact base condition

These written arguments separate the algebraic chart issue in Kapovich–Millson Remark 1.5 from the requirement that the distinguished representation have dense image in \(\mathrm{SU}_2\). The statements below give two positive forms of the stronger exact isomorphism. [Kapovich–Millson, Corollary 1.4 and Remark 1.5](https://www.math.ucdavis.edu/~kapovich/EPR/char.pdf)

## Exact product charts at Zariski-dense representations

**Theorem 1.** Let \(X\) be a finite-type affine scheme over \(\mathbb Q\) and \(x\in X(\mathbb Q)\). There is an open neighborhood \(X'\subset X_{\mathbb C}\) of \(x\), a closed hyperbolic three-manifold \(M\), a nonnegative integer \(k\), and a conjugation-equivariant isomorphism
\[
\mathcal R^\circ\ \simeq\
X'\times \mathrm{SL}_{2,\mathbb C}^{\,k}\times\mathrm{PGL}_{2,\mathbb C},
\]
where \(\mathcal R^\circ\) is a Zariski-open subscheme of \(\operatorname{Hom}(\pi_1(M),\mathrm{SL}_2)\). The action is trivial on \(X'\), acts by left multiplication on the final factor, and the coordinates on \(\mathrm{SL}_2^k\) are measured in the moving frame, so the action there is trivial as well. The representation corresponding to \((x,1,1)\) is Zariski dense in \(\mathrm{SL}_{2,\mathbb C}\). Its image contains nontrivial unipotents. The quotient chart on the character scheme is \(X'\times\mathrm{SL}_2^k\). In particular, both germs are Zariski-locally products with smooth rational factors.

**A rigid frame.** Work throughout with the functor on commutative \(\mathbb C\)-algebras. Write
\[
U(s)=\begin{pmatrix}1&s\\0&1\end{pmatrix},\qquad
L(s)=\begin{pmatrix}1&0\\s&1\end{pmatrix},\qquad
D(t)=\operatorname{diag}(t,t^{-1}).
\]
Use group generators \(A,B,D\) with relations
\[
DAD^{-1}=A^2,\qquad DB^2D^{-1}=B,\qquad (AB^{-1})^6=1.
\]
Consider the point \(A=U(1), B=L(1), D=D(\sqrt2)\). The trace identities \(\operatorname{tr}(A)=\operatorname{tr}(A^2)\) and the corresponding identity for \(B\) imply \((t-2)(t+1)=0\) for each trace. Localize so that \(t+1\) is a unit. The two traces equal 2 over the resulting ring. Let \(P=AB^{-1}\) and \(t=\operatorname{tr}(P)\). At the chosen point \(t=1\) and \(P^3=-1\). Invert \(\det(P^3-1)\) and \(\det((t+1)P-1)\), which are nonzero at the chosen point. The relation \(P^6=1\) now gives \(P^3=-1\). The Cayley–Hamilton identity gives
\[
P^3+1=(t-1)((t+1)P-1),
\]
so \(t=1\) on this open. With \(a=A-1\) and \(b=B-1\), Cayley–Hamilton yields \(a^2=b^2=0\), \(\operatorname{tr}(a)=\operatorname{tr}(b)=0\), and \(\operatorname{tr}(ab)=1\). Its polarized form gives \(ab+ba=1\). Consequently \(a,b,ab,ba\) are the four corresponding matrix units. They provide an algebra automorphism of \(M_2\) taking \(E_{12},E_{21}\) to \(a,b\). This description works over each coefficient ring, for instance the trace pairings of these four matrices make them a basis. The automorphism scheme of \(M_2\) is \(\mathrm{PGL}_2\) and supplies the frame coordinate.

In the normalized frame the first two relations give \(DE_{12}=2E_{12}D\) and \(2DE_{21}=E_{21}D\). They make \(D\) diagonal with \(D_{11}=2D_{22}\). The determinant makes \(2D_{22}^2=1\). Invert \(D_{22}+1/\sqrt2\) in this frame, an invariant condition since a normalized matrix is calculated via the inverse matrix-unit automorphism. Thus \(D\) is fixed at \(D(\sqrt2)\). The open frame scheme is precisely \(\mathrm{PGL}_2\). Its conjugation action changes only this frame.

**Exact arithmetic in the normalized frame.** A generator commuting with \(A\), with \(\operatorname{tr}+2\) inverted, is uniquely \(U(s)\) for one scalar \(s\). Indeed the commutator equation forces an upper triangular matrix with equal diagonal entries and determinant forces their common value to satisfy \(a^2=1\). The open condition forces \(a=1\). The analogous condition with \(B\) gives \(L(s)\). A generator commuting with \(D\) is uniquely \(D(t)\) for a unit \(t\). These extra constraints are all group relators with invariant open conditions. To implement addition, use \(U(x+y)=U(x)U(y)\). Let \(J=AB^{-1}A\). Then \(J U(-y)J^{-1}=L(y)\). Thus the lower triangular realization of any named scalar is a word in its upper triangular realization and the frame.

For multiplication, designate the upper triangular generators for \(x,y,z\) and use a single fresh diagonal generator \(T\) and four fresh triangular generators subject to the following two equations:
\[
 U(z)L(1)=L(r_0)\,T\,U(s_0),\qquad
 U(x)L(y)=L(r_1)\,T\,U(s_1).
\]
The two left-hand sides have upper left entries \(1+z\) and \(1+xy\). A product \(L(r)D(t)U(s)\) has upper left entry \(t\), lower left entry \(rt\), and upper right entry \(ts\). Therefore the equations force \(t=1+z=1+xy\), and the four remaining parameters are uniquely determined by the displayed entries and division by \(t\). Conversely, whenever \(z=xy\) and \(1+z\) is a unit, both equations hold with those auxiliary parameters, since the last entry then follows from determinant one. This is an exact scheme statement, with no other branch inside the specified opens.

Translate the input point to the origin and clear rational denominators in the defining polynomial equations. Every defining polynomial then has constant coefficient zero. Write it using additions and multiplications on inputs, and use powers or inverses of the unipotent generators for integer multiples and negations. Every wire value at the origin is zero, including outputs of multiplication gates. Consequently all \(1+z\) inverted by the construction are units on an actual Zariski-open neighborhood \(X'\) of the input base point. Constrain each final polynomial output to be the identity by a group relator. The resulting finite presentation \(\Gamma\) has a conjugation-invariant open in \(\operatorname{Hom}(\Gamma,\mathrm{SL}_2)\) isomorphic to \(X'\times\mathrm{PGL}_2\). The functor calculations show this for arbitrary coefficient rings, including nilpotent points. The image at the base contains \(U(1),L(1)\). Their integer powers are Zariski dense in the respective one-parameter unipotent subgroups. These subgroups generate \(\mathrm{SL}_2\), proving density.

**The closed hyperbolic source.** Apply Kapovich–Millson Lemma 4.4 to \(\Gamma\) with \(H=\mathrm{SL}_{2,\mathbb C}\). For clarity, the topological step starts with the Panov–Petrunin orbifold for the finitely presented \(\Gamma\), removes conical neighborhoods, and pairs the projective-plane boundaries. In the resulting closed manifold group, killing the designated order-two elements gives \(\Gamma*F_k\). The locus where these elements have trivial image is open and closed over \(\mathbb C\), because the identity is an open and closed subscheme of the order-two locus in \(\mathrm{SL}_2\). It therefore gives the full product with \(\mathrm{SL}_2^k\). Conjugating these free-factor coordinates by the inverse frame automorphism makes the product action as stated. The perfect-kernel hyperbolic replacement preserves that open subscheme and its image subgroups. An invariant chart on the character scheme follows from the trivialized frame on this irreducible chart, which makes the conjugation quotient exactly the projection onto \(X'\times\mathrm{SL}_2^k\). [Kapovich–Millson, Lemma 4.4](https://www.math.ucdavis.edu/~kapovich/EPR/char.pdf) · [Derived hyperbolic transfer, Theorem 1 and §3](DerivedHyperbolicTransfer.md)

## Exact compact charts for split lift torsors

**Theorem 2.** In the set-up of Kapovich–Millson Theorem 5.1, suppose the finite \(\mu_2\)-power torsor of lifts of the normalized \(\mathrm{PO}_3\) chart has a section on a Zariski open neighborhood of the designated point, over \(\mathbb C\). Then there is a closed hyperbolic three-manifold with an exact \(\mathrm{SL}_2\) product chart of the form in Theorem 1 whose designated representation has dense image in \(\mathrm{SU}_2\). In particular this holds for any finite-type affine \(\mathbb Q\)-scheme whose designated rational point is isolated in its support, regardless of nilpotent structure at the point.

**Proof.** The normalized Coxeter chart \(S_c'\simeq X'\) is a section of the adjoint conjugation bundle in Theorem 5.1. Proposition 3.9 gives the specified lift torsor for the extended Coxeter group \(\widetilde\Gamma\). Restrict it to \(S_c'\), and then to the open where the torsor has a section. The image of that section is a clopen sheet of the restricted torsor and projects isomorphically onto the restricted \(X'\). If the sheet's representation at the base does not coincide with a prechosen lift there, a deck transformation switches it. The \(\mathrm{PGL}_2\) action by conjugation on all \(\mathrm{SL}_2\) tuples is well defined. Acting on the normalized sheet supplies the exact product with \(\mathrm{PGL}_2\), because the original adjoint chart has a unique conjugation frame. The resulting scheme is open in \(\operatorname{Hom}(\widetilde\Gamma,\mathrm{SL}_2)\). Any lift at the specified real compact representation lies in \(\mathrm{SU}_2\). Its image is dense there, since its projection is dense in \(\mathrm{SO}_3\) and no proper closed subgroup of \(\mathrm{SU}_2\) surjects onto \(\mathrm{SO}_3\). Lemma 4.4 again gives the product with \(\mathrm{SL}_2^k\), now applied to \(\widetilde\Gamma\), and perfect-kernel replacement gives the closed hyperbolic source.

If \(x\) is isolated in the support, one can take the component supported on that point, whose complex coordinate ring is local Artinian with residue field \(\mathbb C\). It is strictly Henselian. Every finite étale torsor on it splits, including when the point carries a nonreduced structure. This supplies the required section.

**The square-class test.** The normalized projective axis of an anisotropic involution has an algebraic representative \(v=(v_1,v_2,v_3)\) on a coordinate chart. In the pure quaternion realization of \(\mathrm{SL}_2\), its two spin lifts are the two norm-one multiples of \(v\). Thus the single-generator lift torsor there is the Kummer torsor of \(q(v)=v_1^2+v_2^2+v_3^2\). A change of projective representative changes \(q(v)\) by a square. In the Coxeter lift charts of Proposition 3.9 the choices of signs of the individual generators are independent. Consequently, a sufficient condition for splitting is a square root for each of these axis norms on a common Zariski neighborhood. For an integral input chart over \(\mathbb C\), triviality in the function field suffices if the roots are regular at the specified point, as they are on a normal input chart. This describes exactly the issue with choosing a Zariski section of this particular cover. A nontrivial function-field square class can persist on every nonempty Zariski open even though the étale fiber and analytic germ split.

The two theorems leave the simultaneous arbitrary-input and dense-\(\mathrm{SU}_2\) requirement open. They establish exact algebraic charts in the two stated scopes.
