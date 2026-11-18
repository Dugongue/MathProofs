# Exact isotopy transporters and degenerations of unital algebras

For two finite free unital associative algebras \(A,B\) of the same positive rank over a commutative ring \(R\), the ordinary three-factor transporter of their multiplication tensors is naturally isomorphic as a scheme to
\[
\operatorname{Isom}_{R\text{-alg}}(A,B)\times\operatorname{GL}_1(B)^2.
\]
In particular their stabilizer surjects by a split group homomorphism onto the algebra automorphism group, with two unit-group factors for its kernel as a scheme. Over an algebraically closed field, \(B\) is a degeneration of \(A\) as a unital associative algebra if and only if its multiplication tensor is a degeneration of the multiplication tensor of \(A\) under the three-mode action. This gives a converse orbit-closure transfer to the path-algebra construction and uses the multiplication-compilation and exact-transporter arguments.

## Recovering all isotopisms

Use the convention that an isotopism consists of invertible linear maps \((P,Q,W)\) with
\[
P(x)Q(y)=W(xy).
\]
Write \(a=P(1)\), \(b=Q(1)\). Substituting the unit gives \(P(x)b=W(x)\) and \(aQ(x)=W(x)\). Right multiplication by \(b\) and left multiplication by \(a\) are therefore bijective, so \(a,b\) are units. For example if \(1=ac\), injectivity of left multiplication applied to \(ca-1\) gives \(ca=1\). Put \(\phi(x)=a^{-1}W(x)b^{-1}\). The displayed isotopy gives \(\phi(x)\phi(y)=\phi(xy)\) and \(\phi(1)=1\). Conversely every choice of \(\phi,a,b\) gives the triple
\[
P(x)=a\phi(x),\qquad Q(x)=\phi(x)b,\qquad W(x)=a\phi(x)b.
\]
These formulas are inverse over every commutative extension ring, and use only regular operations on the specified schemes. On stabilizers the recovered \(\phi\) is multiplicative under composition and the choice \(a=b=1\) is a section. In particular the kernel is smooth, geometrically connected and rational over a field, since the unit group is a principal open in affine space.

## Recovering a unital family from a tensor degeneration

A unital algebra degeneration gives a tensor degeneration by forgetting the unit and allowing independent mode maps. Conversely let \(M:U\times V\to X\) be the bilinear map over a complete DVR produced by a tensor degeneration, with generic fiber isotopic to \(A\) and special fiber identified with the multiplication of \(B\). As usual one can obtain the DVR by curve selection and finite extension to realize a generic transporter. Take \(u\in U\) and \(v\in V\) lifting the two special unit vectors. Then the two linear maps \(R_v(x)=M(x,v)\) and \(L_u(y)=M(u,y)\) are isomorphisms to \(X\) because they are so on the special fiber. Define a new multiplication on \(X\) by
\[
x\circ y=M(R_v^{-1}x,L_u^{-1}y).
\]
It has two-sided unit \(e=M(u,v)\) and reduces to the multiplication of \(B\). In the generic fiber the isotopy identifies it with a principal isotope of \(A\). More explicitly, in the output coordinates of \(A\) it has the form \(x\circ y=x c y\), for a fixed unit \(c\) obtained from the two invertible partial multiplications. This is associative and isomorphic to \(A\), for example by \(x\mapsto cx\). Associativity over the DVR follows because its matrix entries hold in the fraction field and the underlying module is free. Hence this is a unital associative algebra family proving the converse.

The normalization also works in an arbitrary local ring family with invertible partial evaluations and an injective base change on which the generic multiplication is an associative isotope. The orbit-closure statement uses just the DVR case. This is an informal proof.
