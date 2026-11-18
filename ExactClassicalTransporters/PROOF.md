# Exact classical transporters for associative algebras

Let \(A,A'\) be unital associative algebras of the same positive finite free rank \(n\) over a commutative ring \(R\). The hyperbolic encoding of the earlier proof gives two matrix algebras with one common split symplectic and determinant-one split quadratic transporter. As a functor on commutative \(R\)-algebras \(S\), this transporter has a natural isomorphism of underlying schemes with

\[
\operatorname{Isom}_{R\text{-alg}}(A,A')
\times \mathbb G_m^2 \times
\operatorname{GL}_1(A')^2 \times
\operatorname{GL}_{n+1} \times \mathbb A^{4n+2}.
\]

Here the units functor \(\operatorname{GL}_1(A')\) assigns \((A'\otimes_R S)^\times\) to \(S\). When \(A=A'\), projection to the algebra automorphism group is a split group homomorphism. Over a field its kernel is smooth, geometrically connected and rational. This combines the hyperbolic construction with canonical idempotent alignment and the earlier exact Peirce transporter argument.

## Recovering the triangular algebra

Set \(r=n+1\) and write \(B=B(A)\) for
\[
\begin{pmatrix}R & M\\0&A\times R\end{pmatrix},
\qquad M=A\oplus R^r .
\]
The right module structure on \(M\) is componentwise and the left structural action is by scalars. Write \(s,e,t\) for the three diagonal idempotents. Let \(\mathcal H(A)\) act on \(B\oplus B^*\) by \(\operatorname{diag}(L_b,L_c^*)\) for \(b,c\in B\).

For use over any scalar extension, recall the orientation argument. Over each residue field, the radical of \(B\) is \(M\) together with the \(J(A)\)-corner. In the radical modulo its square, the unique directed component of dimension greater than \(n\) is \(s\to t\), of dimension \(r\). The source also has a nonzero component to each simple block of \(A/J(A)\). The target has no other neighbors. The graph is connected, so \(B\) is indecomposable and the orientation distinguishes \(B\) from the opposite construction. Thus an isomorphism of the two doubles preserves the ordered summands in every residue field. It does so over the base ring because central idempotents agreeing in all residue fields are equal. Indeed their cross-products with the respective complements define finite projective direct summands with zero fibers, hence vanish by Nakayama's lemma.

An isomorphism \(f:B\to B'\) sends the ordered idempotents to their counterparts modulo the radical in every residue field. The sum \(u=\sum_{v=s,e,t}v'f(v)\) is a unit over the base since the determinant of its left multiplication is a unit in every residue field. It intertwines the two families. An aligned isomorphism sends \(M=sB(1-s)\) to \(M'\), so every isomorphism does too because \(M'\) is a two-sided ideal. Modulo \(M'\), all three distinguished target idempotents are central. Consequently \(f(v)\equiv v'\pmod{M'}\) holds before alignment.

## Exact decomposition, including over nonreduced scalars

There is a unique \(m\in M'\) for which conjugation by \(1+m\) makes \(f\) aligned. Existence follows from the same sum \(u\), which now belongs to \(1+M'\). For uniqueness, a shear commuting with \(s'\) is trivial because \(s'm=m\) and \(ms'=0\). The treatment works over each \(S\), including nilpotent coefficients.

An aligned isomorphism consists of an arbitrary \(\alpha:A\to A'\), the identity on the two scalar diagonal factors, a map \(A\to A'\) on \(sBe\) of the form \(x\mapsto w\alpha(x)\) with \(w\in A'^\times\), and an arbitrary \(V\in\operatorname{GL}_r(S)\) on \(sBt\). These are all the data because the regular right module map is determined by the image of 1 and the two module corners have no further products. Together with the shear this gives parameters \((\alpha,m,w,V)\), all recovered functorially.

An isometric transporter of the doubled matrix algebra preserves the ordered summands and acts as \(\operatorname{diag}(g,(g^{-1})^*)\) for either split form. Its first block is \(g(x)=f(x)v\) for a unique \(f:B\to B'\) and \(v\in B'^\times\), by evaluating the conjugation of left multiplications at 1. The units of \(B'\) are parametrized by their diagonal entries in \(S^\times,(A'\otimes S)^\times,S^\times\) and their arbitrary \(M'\)-entry. Combining the parameters gives the stated product, with two copies of \(M'\) of rank \(2n+1\) each. All constructions and their inverses use polynomial expressions and inversions of units, and commute with base change. In particular this is an identification of functors and of the schemes representing them.

On stabilizers, the recovered \(\alpha\) is the restriction of the induced automorphism on the \(A\)-factor in \(B/M\). This is a group homomorphism. The diagonal extension of \(\alpha\) followed by hyperbolic doubling is a group section. Over a field \(\operatorname{GL}_1(A)\) is the nonempty principal open subset cut out by the determinant of left multiplication in affine \(n\)-space. This proves smoothness, geometric connectedness and rationality of the displayed kernel. In particular the construction preserves the component group of the algebra automorphism scheme over a field and preserves transporter nonemptiness over every scalar extension. It also preserves the local solubility pattern of an algebra-isomorphism instance over a global field, including a failure of the Hasse principle if present in the input. This is an informal proof.
