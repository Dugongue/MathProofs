# Determinant coordinates for étale multiplication

For a field \(F\) of characteristic zero, write a multiplication tensor as the bilinear map of a finite étale \(F\)-algebra \(E\). We use the bilinear-map convention \(Px\cdot Qy=R(xy)\) for an isotopy. The duals on the two input factors preserve both the ordinary and the special-linear equivalence relations.

The descent of the geometric diagonal tensor to multiplication of a finite étale algebra is part of the degree-six theorem. The ordinary classification also follows directly once the multiplication form is known. An isotopy \(P(x)Q(y)=R(xy)\) from \(E\) to \(E'\) has \(u=P(1)\) and \(v=Q(1)\). Multiplication by \(u\) identifies \(Q\) with \(R\), and multiplication by \(v\) identifies \(P\) with \(R\), so both elements are units. The map \(\phi=(uv)^{-1}R\) is a unital algebra isomorphism, and
\[
(P,Q,R)=(m_u\phi,m_v\phi,m_{uv}\phi).
\]
Conversely this triple is an isotopy for any such isomorphism and units. The prior arithmetic calculation gives the determinant obstruction in these terms. [Degree-six diagonal classification](https://github.com/Dugongue/MathProofs/blob/main/DickeAndIsomorphismMethods/GEOMETRY.md), [earlier determinant and norm calculations](https://github.com/Dugongue/MathProofs/blob/main/TISLWorlds500/Arithmetic.md).

For an \(F\)-automorphism of \(E\), \(s=\det\phi\) is the sign of its permutation of geometric embeddings. Set \(\Sigma(E)=\det\operatorname{Aut}_F(E)\subseteq\{\pm1\}\). With \(a=N_E(u)\) and \(b=N_E(v)\), the stabilizer determinant triples are exactly \((sa,sb,sab)\). In \((F^\times)^3\) use the invertible multiplicative change of coordinates
\[
(d_1,d_2,d_3)\longmapsto
(c,x,y)=\left(\frac{d_1d_2}{d_3},\frac{d_1}{c},\frac{d_2}{c}\right),
\qquad
(d_1,d_2,d_3)=(cx,cy,cxy).
\]
The stabilizer image in these coordinates is \(\Sigma(E)\times N_E(E^\times)^2\), where the latter denotes a product of two copies of the norm group. The determinant map from \(\mathrm{GL}_n(F)^3\) is surjective with kernel \(\mathrm{SL}_n(F)^3\). It follows that the global special-linear classes in the fixed ordinary orbit are the determinant triples modulo the stabilizer image.

Now let \(F\) be a number field. Write \(E_v=E\otimes_F F_v\) and
\[
\mathfrak K(E/F)=
\{a\in F^\times : a\in N_{E_v/F_v}(E_v^\times)\text{ for every }v\}/N_{E/F}(E^\times).
\]
The signed local genus **within the ordinary orbit** of the multiplication tensor has the following group of classes, with that tensor as the basepoint:
\[
\frac{\bigcap_v\Sigma(E_v)}{\Sigma(E)}\times\mathfrak K(E/F)\times\mathfrak K(E/F).
\tag{1}
\]
Indeed, the determinant quotient and its localization have the same product coordinates. The signed local genus of any other representative in that ordinary orbit has the same count, since applying a fixed ordinary change of bases transports the local special-linear conditions by normality.
