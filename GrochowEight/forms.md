# Direct degree raising for exact form equivalence

Let \(K\) be any field and fix \(3\le e<d\). There is a polynomial-time instancewise reduction from exact equivalence of homogeneous degree-\(e\) forms over \(K\) to exact equivalence of degree-\(d\) forms over \(K\). It adds four variables if \(e\ge4\) and at most \(3n+16\) variables for cubics in \(n\) variables. The construction uses coefficients from the prime ring, works over the input field itself, and recovers a witness by restriction and a linear extension. This proves the higher-source-degree reduction proposed after Proposition A.1, for all source degrees at least three. The unmarked map from the appendix can lose scalar information, as quantified in the companion note. [Grochow–Qiao, Appendix A](https://arxiv.org/html/1907.00309#A1)

## A three-variable marker for source degree at least four

Use \(h(y)=y_1y_2y_3+y_1^2+y_1+y_2+y_3\). For a nonzero degree-\(e\) form \(f(x)\), output
\[
 P_f=z^{d-e}\big(f(x)+z^e h(y/z)\big).
\]
Output the zero form in the same number of variables for zero input. Each power of \(z\) inside the bracket is positive. An equivalence of the inputs extends by fixing the new variables.

For reflection, first show that the bracket has no linear factor. A linear factor independent of \(y\) divides both the coefficient \(z^{e-3}\) of \(y_1y_2y_3\) and the nonzero constant-in-\(y\) term \(f(x)\), which is impossible. A factor involving \(y\) has leading \(y\)-degree-one term proportional to some \(y_i\) by unique factorization of the leading \(y\)-degree-three term. Write the factor as \(y_i+\ell(x,z)\) after normalization. Set \(y_i=-\ell\). The mixed product of the other two \(y\)'s then has coefficient \(-z^{e-3}\ell\), so \(\ell=0\). A linear term in a remaining \(y\) still survives. This rules out the factor.

A linear transporter of outputs must therefore send the target \(z\) to \(\lambda z\) for \(\lambda\ne0\). Write its action on the other variables \(u=(x,y)\) as \(Au+cz\). The invertible map \(A\) on \(z=0\) sends the essential linear-form support of \(g\) onto that of \(f\) under pullback, since on that hyperplane the bracket equality is \(f=\lambda^{d-e}g\circ A\). The essential support is the smallest linear space of linear forms whose symmetric algebra contains the polynomial. It exists because the symmetric algebras of two subspaces intersect in the symmetric algebra of their intersection, as seen in a basis adapted to both subspaces.

Dehomogenize at \(z=1\), and use the rational function field in the essential coordinates of \(f\) as coefficient field. The other coordinates are spectator variables and include the three new \(y\)'s. In the transported \(g\), the spectator variables are absent, even after translation by \(c/\lambda\). Thus the marker comparison has the form
\[
 h(L+b)=s h(y)+C,\qquad s=\lambda^{-d},
\]
where each of the three entries of \(L\) is linear in the spectators and \(b,C\) involve only the coefficient field. The cubic coefficient identifies these three linear forms as a permutation of \(y_1,y_2,y_3\) with nonzero scales. Comparison of the three mixed quadratic coefficients gives \(b=0\). The only square term pins the first coordinate of the permutation. Comparison of linear coefficients makes each of the three scales \(s\). The square term then gives \(s^2=s\), so \(s=1\). Thus \(\lambda^d=1\). Because \(g\) is homogeneous of degree \(e\),
\[
 f=\lambda^{d-e} g\circ A=g\circ(\lambda^{-1}A).
\]
The marker comparison also proves that the marker rows of the normalized linear map are a permuted and scaled copy of the three marker coordinates, with zero original-variable part. Its original-variable block is therefore invertible. Restrict the displayed equality to zero marker coordinates to decode a transporter. The algorithm does not compute essential supports.

## A cubic marker in every characteristic

Choose even \(m\ge\max(4,n)\) as small as possible. Set \(U=K\oplus K^m\), with coordinates \((a,w)\), and take
\[
 q(w)=\sum_{j=1}^{m/2} w_{2j-1}w_{2j},\qquad
 C(a,w)=a q(w),\qquad
 B((a,w),(a',w'))=aa'+\beta(w,w'),
\]
where \(\beta\) is the nondegenerate bilinear polar form of \(q\). Take three copies \(Y_i=U\) with coordinates \(y_i\) and put
\[
 F_f=f(x)+\sum_{i=1}^3 C(y_i),\qquad
 Q(y)=\sum_{i<j}B(y_i,y_j),\qquad
 P_f=z^{d-3}\big(F_f+zQ\big).
\]
The bracket has no linear factor. Indeed, setting \(z=0,x=0\) and all marker coordinates except one disjoint coordinate triplet in each of two blocks to zero gives \(abc+def\), which is irreducible. View it as primitive and linear in \(a\), with coprime coefficient \(bc\) and constant term \(def\). A nonzero homogeneous specialization of a homogeneous factorization keeps each factor nonzero and preserves its degree. Thus any transporter again takes \(z\) to \(\lambda z\), and dehomogenizing at \(z=1\) yields
\[
 F_g(M(x,y)+b)+Q\big((M(x,y)+b)_Y\big)=s(F_f(x,y)+Q(y)),\qquad s=\lambda^{-d},
\]
where \(M\) is invertible.

For any cubic \(F\), its full polarization \(T_F(v_1,v_2,v_3)\) is the coefficient of \(t_1t_2t_3\) in \(F(\sum t_i v_i)\). This convention works in characteristics two and three. For \(C\), this tensor is
\[
 T_C((a,w),(a',w'),(a'',w''))=
 a\beta(w',w'')+a'\beta(w,w'')+a''\beta(w,w').
\]
It has zero radical and scalar centroid. Here the centroid is the algebra of linear maps that can be transferred between slots in a tensor contraction. To see the assertion in this case, moving a centroid map between slots of triples of vectors in \(W=0\oplus K^m\) shows that its first-coordinate functional \(\ell\) on \(W\) obeys \(\ell(w)\beta(w',v)=\ell(w')\beta(w,v)\). Nondegeneracy and independent \(w,w'\) give \(\ell=0\). For the distinguished vector \(u=(1,0)\), moving the map from \(u\) to \(w\) in \(T_C(u,w,w')\) makes its restriction to \(W\) scalar, with scalar the first coordinate of its value on \(u\). Moving it in \(T_C(u,u,w)\) kills the \(W\)-component of its value on \(u\).

On the radical quotient of a symmetric trilinear tensor the centroid is a finite-dimensional commutative algebra. To verify commutativity, transfer \(S\) from slot 1 to 2, \(D\) from 1 to 3, \(S\) from 2 to 1, and \(D\) from 3 to 1. This transfers \(SD\) to \(DS\) in slot 1, and the zero radical makes the maps equal. Transferring both maps between slots then shows closure under multiplication. Primitive idempotents give an orthogonal direct decomposition. On any existing orthogonal direct sum of such tensors, centroid maps preserve the summands. If \(x\) belongs to one and \(y,z\) to another, transferring a centroid map from \(x\) to \(y\) gives zero, so the projection of the value on \(x\) to the other summand vanishes.

The top cubic part therefore forces \(M\) to permute the three marker summands on the polar radical quotient. Each has dimension \(m+1>n\) and scalar centroid, and every primitive summand of the original polar tensor has dimension at most \(n\). Consequently the marker coordinates of \(M\) are a block permutation by invertible maps \(D_i\), independent of \(x\). The original-coordinate components of \(M\) restricted to marker directions have values in the polar radical of \(T_g\).

Consider the mixed quadratic terms between two different marker blocks. A translated cubic contributes the coefficient \(T_{F_g}(Mv_i,Mv_j,b)\) for marker directions \(v_i,v_j\) in those blocks. This is zero because the two marker directions land in distinct marker blocks modulo the original polar radical. The comparison of the quadratic terms now gives
\[
 D_i^T B D_j=sB\quad(i\ne j).
\]
The three pair equations and nondegeneracy of \(B\) give \(D_1=D_2=D_3=D\) and \(D^T B D=sB\).

The subspace \(W\subset U\) is characterized by contraction rank at most two in \(T_C\). For \(a=0\) the displayed trilinear formula gives rank at most two. For \(a\ne0\) its restriction to \(W\times W\) has rank \(m\). Since \(D\) scales \(T_C\), it preserves \(W\). Since it also scales \(B\), it preserves \(W^{\perp_B}=Ku\). Let \(\alpha\) be its scalar on \(Ku\). The bilinear comparison gives \(\alpha^2=s\) and scales \(\beta\) by \(s\). Evaluating the trilinear comparison on \(u,w,w'\) then gives \(\alpha s\beta(w,w')=s\beta(w,w')\), so \(\alpha=1\) and \(s=1\).

Finally, set \(y=0\) in the equality of the homogeneous cubic parts. The transported marker cubics vanish and the original \(x\)-block of \(M\) is invertible by block triangularity. This recovers an exact original equivalence. The forward map fixes every new variable.

For \(e=d\) use the identity map. For degrees fixed, both constructions expand in deterministic polynomial coefficient time. The cubic adds \(3(m+1)+1\) variables, which is at most \(3n+16\). These are paper proofs.

## Degrees one and two

In degree one, the zero form and all nonzero linear forms give the two orbits. Taking the \(d\)-th power of the given form reflects this distinction and preserves equivalence.

For degree two, a polynomial-size reduction exists over every field by composing the known fixed-signature and cubic reductions. To encode a quadratic \(f\in\operatorname{Sym}^2(V)\) without dividing by two, use the two roles \(V\) and \(W=\operatorname{Sym}^2(V)\) with the named symmetric-product map \(V\otimes V\to W\). An isomorphism of these data induces the symmetric-square map on \(W\), since the displayed map is surjective. Add a one-dimensional role with its usual nonzero multiplication and a named map from that role to \(W\) taking \(1\) to \(f\). An automorphism of the one-dimensional multiplication is the identity, so this last map tests exact equivalence of \(f\). Every original equivalence lifts. Apply the fixed linked-tensor compiler to this signature, then the same-field \(3\)-tensor-to-cubic reduction, and use the cubic construction above if \(d>3\). For \(d=2\) use the identity. This answers the existence question for every pair of positive degrees \(e\le d\). The direct small-dimension bounds above concern source degree at least three. [Futorny–Grochow–Sergeichuk, Theorem 1.1](https://arxiv.org/abs/1810.09219) · [Grochow–Qiao, Corollary 8.6](https://arxiv.org/html/1907.00309) · [Agrawal–Saxena, Theorem 4.1](https://doi.org/10.1007/11672142_8)
