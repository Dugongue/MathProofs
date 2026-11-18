# Hyperbolic matrix conjugacy for arbitrary associative algebras

Let \(R\) be a nonzero commutative ring with identity. For every finite free unital associative \(R\)-algebra \(A\) of positive rank \(n\), we construct a unital matrix subalgebra \(\mathcal H(A)\) in ambient dimension \(6n+6\). It is stable under the adjoints of the standard split symmetric and alternating forms. For algebras \(A,A'\) of equal rank, the following are equivalent.

1. \(A\cong A'\) as \(R\)-algebras.
2. \(\mathcal H(A)\) and \(\mathcal H(A')\) are conjugate by an invertible \(R\)-linear map.
3. They are conjugate by a symplectic map.
4. They are conjugate by a determinant-one isometry of the split quadratic form.

In fact the sets of conjugators in 3 and 4 coincide. All constructions given by structure constants have polynomial cost in ring operations and coefficient storage under the usual explicit encodings. In characteristic two the quadratic form in 4 is given explicitly, so its isometries preserve the quadratic form itself.

The proof combines the hyperbolic doubling argument from *Four algorithms and reductions around Grochow's questions* with the quiver and idempotent recovery argument from *Tensor-isomorphism reductions that act on all homomorphisms*. The new step is to orient the double for an arbitrary input algebra, including decomposable and noncommutative ones.

## Orienting the algebra

Put \(r=n+1\). Use the triangular ring

\[
B(A)=
\begin{pmatrix}
R & A\oplus R^r\\
0 & A\times R
\end{pmatrix}.
\]

The top right is an \((R,A\times R)\)-bimodule with the usual scalar left action and the separate right actions on the two summands. The rank is \(1+(n+r)+(n+1)=3n+3\). Write \(s\) for the top scalar idempotent, \(t\) for the last scalar idempotent, and \(e=1-s-t\) for the \(A\)-corner idempotent. Every algebra isomorphism \(A\to A'\) extends to \(B(A)\to B(A')\) by applying the isomorphism to the two copies of \(A\).

Over a field \(k\), the radical of \(B(A)\) consists of the entire top-right module and the copy of \(J(A)\) in the bottom corner. The described ideal is nilpotent, and quotienting by it gives \(k\times(A/J(A))\times k\), which is semisimple. In the radical modulo its square, consider the directed graph on the central primitive idempotents of this semisimple quotient, with edge weights the vector-space dimensions of the corresponding left-right components. The component \(s\to t\) has dimension \(r\). The components from \(s\) into the simple factors of \(A/J(A)\) are the corresponding regular module components of \(A/J(A)\), all nonzero and of dimension at most \(n\). All components internal to the \(A\)-corner have dimension at most \(n\) and there are no other incident edges at \(t\). Thus \(s\to t\) is the unique edge of weight greater than \(n\). Its source has another neighbor and its target has no other neighbor. In the opposite algebra the direction reverses and the source has no other neighbor. The graph is connected since \(s\) is joined to every other vertex. This forces \(B(A)\) to be indecomposable as an algebra. Indeed any central idempotent would give a partition of the semisimple factors with all radical components crossing the partition zero, and a central idempotent with zero image in a nilpotent ideal is zero.

Consequently over every field an isomorphism of \(B(A)\times B(A)^{\mathrm{op}}\) with \(B(A')\times B(A')^{\mathrm{op}}\) preserves the ordered two summands. Within the first summand it maps the distinguished \(s,t\) to their counterparts modulo the radical, by the unique weighted edge.

## Recovery over the base ring

Suppose the two double algebras over \(R\) are isomorphic. Reduce an isomorphism modulo each maximal ideal of \(R\). The construction commutes with this reduction, and the field argument shows that the two central idempotents naming the ordered sides are preserved in every residue field. They are preserved over \(R\) as well. For commuting idempotents \(p,p'\) with equal residue images everywhere, \(p(1-p')\) and \(p'(1-p)\) give finite projective direct summands of the ambient finite free algebra by multiplication. Their fibers are zero at every maximal ideal, hence they vanish by Nakayama's lemma after localization. Thus \(p=p'\). Apply this to each side.

Let \(f:B(A)\to B(A')\) be the resulting isomorphism and consider the families \(f(s),f(t),f(e)\) and \(s',t',e'\). Set

\[
u=s'f(s)+t'f(t)+e'f(e).
\]

Over each residue field this element is 1 modulo the radical, so it is a unit there. Left multiplication by \(u\) on the finite free algebra therefore has determinant outside every maximal ideal, hence is invertible over \(R\). This makes \(u\) a unit, since the inverse image of 1 is a right inverse and injectivity of left multiplication then gives a left inverse. Orthogonality of the families gives \(u f(e)=e'u\), and analogous equations for \(s,t\). After inner conjugation the isomorphism restricts to the \(e\)-corner, which is \(A\). This proves recovery without a locality assumption on \(R\).

## Matrix realization and all isometric conjugators

Write \(B=B(A)\), \(X=B\oplus B^*\), and let \(L_b\) denote left multiplication. Take

\[
\mathcal H(A)=\{\,\operatorname{diag}(L_b,L_c^*) : b,c\in B\,\}.
\]

This is the faithful regular and dual representation of \(B\times B^{\mathrm{op}}\). On \(X\) take the split quadratic form \(Q(x,\lambda)=\lambda(x)\) and the alternating form \(\omega((x,\lambda),(y,\mu))=\mu(x)-\lambda(y)\). The adjoints for the polar form of \(Q\) and for \(\omega\) both exchange the roles of \(b,c\). If \(A\cong A'\), the induced map \(f:B\to B'\) gives the conjugator \(\operatorname{diag}(f,(f^{-1})^*)\). This preserves \(Q\) and \(\omega\) and has determinant one. Conversely any invertible conjugator induces an algebra isomorphism on the two doubles, so the recovery argument applies.

Every conjugator preserves the two ordered central idempotents by the same residue argument. It is therefore block diagonal, say \(\operatorname{diag}(g,h)\). Preserving either \(\omega\) or \(Q\) forces \(h=(g^{-1})^*\), by evaluating the defining pairings, and this condition suffices for both. More precisely the common transporter consists of these matrices with \(g(x)=f(x)v\), where \(f:B\to B'\) is an algebra isomorphism and \(v\in (B')^\times\). Indeed \(gL_b=L_{f(b)}g\) gives that formula with \(v=g(1)\). Bijectivity of right multiplication by \(v\) gives a two-sided inverse. The formula conversely implies that \(g\) transports the left regular algebras, and its dual inverse transports the other summands.

## Consequence for tensors over commutative rings

For any fixed tensor order at least two, the earlier tagged path-algebra reduction works over this same class of base rings. Use a directed chain whose consecutive arrow modules are the tensor modes, a parallel length-two arm with scalar arrows \(a,b\), and add distinct positive numbers of private outward leaves to every core vertex. Impose \(ab=T\) in the path algebra. Normal forms delete the scalar path \(ab\) and its extensions by a leaf arrow, so the algebra is finite free of polynomial rank in the explicit input. The relation lies in the square of the arrow ideal. Over every residue field the radical is the arrow ideal, and the numbers of terminal neighbors identify all ordered core vertices in the radical graph. Use the core idempotents together with a single idempotent for the sum of all leaves. An algebra isomorphism identifies these families modulo the radical in every residue field. The same sum-of-products conjugation and determinant argument align them over \(R\). The consecutive corner maps recover invertible changes of basis on the tensor modes. The tag-arrow maps rescale \(a,b\) by units, so the relation gives the tensor equivalence after absorbing their product into one mode. Conversely every tensor equivalence yields an algebra isomorphism by direct substitution on paths.

Composing the constructions transfers ordinary tensor isomorphism over \(R\) to either of the two split classical matrix conjugacy problems. When comparing tensors of matched mode dimensions, the intermediate ranks agree even when the tensors have different supports. Mismatched dimensions are rejected directly. The conclusion concerns conjugacy of unital matrix subalgebras stable under adjoint. This is an informal proof.
