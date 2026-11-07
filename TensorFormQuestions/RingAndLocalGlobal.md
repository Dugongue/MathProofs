# Cubic form equivalence over rings and completions

This note gives two informal answers to the questions in Section 6 of Agrawal and Saxena's *On the Complexity of Cubic Forms*. The ring question is interpreted in the finite-free basis representation used for the surrounding field problem. The local question is answered even with equivalence modulo every prime power. [Original questions, p. 38](https://www.cse.iitk.ac.in/%75sers/nitin/papers/cubic-forms.pdf)

## 1. An arbitrary-base-ring reduction

Let \(R\) be a commutative ring with identity. A finite free commutative associative unital \(R\)-algebra \(A\) of rank \(n\), supplied by its multiplication structure constants, can be represented by the cubic

\[
q_A(x,y,\phi)=\phi(xy),\qquad (x,y,\phi)\in A_1\oplus A_2\oplus A^*,
\]

where \(A_1,A_2\) are two copies of its underlying \(R\)-module and \(A^*=\operatorname{Hom}_R(A,R)\). Fixing a basis and its dual gives a formal cubic in \(3n\) variables. The coefficient of \(x_i y_j\phi_k\) is the structure constant of the \(k\)th basis vector in the product of the \(i\)th and \(j\)th basis vectors. All other coefficients are zero. Thus the output takes polynomial time to write in a dense representation and does not require arithmetic on coefficients.

An algebra isomorphism \(P:A\to B\) induces a linear equivalence by \((x,y,\phi)\mapsto (Px,Py,\phi\circ P^{-1})\). For the converse, form the symmetric trilinear map

\[
T_A(u,v,w)=[s t h]q_A(su+tv+hw).
\]

Because this is coefficient extraction in a polynomial identity, it commutes with every invertible linear substitution over \(R\). It is meaningful without division by 2 or 3. On inputs drawn from single summands, \(T_A\) is zero unless all three summands occur, in which case it is the product pairing \(\phi(xy)\) with coefficient 1. The product pairing separates each argument when the others vary. For the two algebra inputs this follows by using the unit for the other algebra input and a separating dual functional. For the dual input it follows by testing its value on each element \(x=x\cdot1\). The dual separates points because the underlying module is free.

The centroid consists of endomorphisms \(C\) for which inserting \(C\) in any of the three argument slots gives the same value. To isolate the block of \(C\) from summand \(i\) to another summand \(j\), evaluate on two inputs from \(i\) and one from the third summand \(k\). Inserting \(C\) at the first \(i\)-input keeps only its \(j\)-component. Inserting it at the \(k\)-input leaves two arguments from \(i\), giving zero. Separation shows the \(i\)-to-\(j\) block is zero. All off-diagonal blocks vanish this way.

Write the diagonal blocks as \(P,Q,S\). The centroid equations are

\[
\phi((Px)y)=\phi(x(Qy))=(S\phi)(xy).
\]

With \(y=1\) and \(x=1\), respectively, dual separation gives \(Px=xa\) and \(Qy=ay\) for \(a=P1=Q1\). With \(y=1\) again the last equality gives \((S\phi)(x)=\phi(ax)\). Conversely multiplication by any \(a\) on the two algebra summands, with its dual action on \(A^*\), is in the centroid by associativity and commutativity. The correspondence is an algebra isomorphism under composition. Consequently a cubic equivalence conjugates the two centroids and implies \(A\cong B\) as \(R\)-algebras. This gives a polynomial-time many-one reduction for the stated input model. There is no restriction on characteristic or zero divisors. If the base ring is the zero ring, all inputs of the same prescribed format are trivial and can be handled separately.

The construction uses the classical centroid of a higher form. Agrawal and Saxena's subsequent field-case reduction uses a different construction. Their basis input supplies the meaning of the ring generalization used here. [STACS 2006 field-case reduction](https://www.cse.iitk.ac.in/%75sers/nitin/papers/stacs06.pdf) · [O’Ryan and Shapiro on higher trace centroids](https://doi.org/10.1016/j.jpaa.2013.03.005)

## 2. Six-variable smooth cubic forms with no rational equivalence

Consider the two rational étale algebras

\[
A=\mathbb Q\times\mathbb Q\times\mathbb Q(\sqrt{13},\sqrt{17}),\qquad
B=\mathbb Q(\sqrt{13})\times\mathbb Q(\sqrt{17})\times\mathbb Q(\sqrt{221}).
\]

The primitive factors of \(A\) have dimensions \(1,1,4\), while those of \(B\) have dimensions \(2,2,2\). Thus \(A\) and \(B\) are not isomorphic over \(\mathbb Q\).

At every completion \(F\) of \(\mathbb Q\), the square classes of 13 and 17 span at most a line in \(F^*/F^{*2}\). Over \(\mathbb R\) they are both squares. Over \(\mathbb Q_2\), 17 is a square because it is 1 modulo 8. Over \(\mathbb Q_{13}\), 17 is a square by Hensel's lemma applied to its nonzero square residue 4. Over \(\mathbb Q_{17}\), 13 is a square by the nonzero residue \(8^2\equiv13\pmod {17}\). At every other prime, the two numbers are units and the unit square-class group has order two, since the prime is odd.

If both numbers are squares over \(F\), both algebras become \(F^6\). Otherwise write \(E/F\) for the quadratic extension defined by the common nontrivial square class in their span. Exactly one of 13, 17, and 221 is a square. On the \(B\) side this gives one split quadratic factor and two copies of \(E\). On the \(A\) side the biquadratic tensor product is \(E\times E\). To see this even when neither of the two numbers is a square, the two quadratic extensions are isomorphic to \(E\), so their tensor product is \(E\otimes_F E\cong E\times E\) by separability. Hence in the nonsplit case both algebras are \(F^2\times E^2\).

Take

\[
f_A(x)=\operatorname{Tr}_{A/\mathbb Q}(x^3),\qquad
f_B(y)=\operatorname{Tr}_{B/\mathbb Q}(y^3)
\]

in arbitrary integral bases of their maximal orders, using products of the rings of integers for the product algebras. They have integral coefficients because the trace of multiplication by an integral element is the trace of an integer matrix. Local algebra isomorphisms preserve multiplication traces and identify the maximal local orders. The latter are the integral closures of \(\mathbb Z_p\) in the corresponding products of local fields, equivalently the completions of the maximal orders. Thus the local isomorphism matrices in the chosen bases lie in \(\operatorname{GL}_6(\mathbb Z_p)\) and give cubic equivalence modulo \(p^k\) for every \(p\) and \(k\ge 1\). Equivalence over \(\mathbb R\) also follows from the local algebra isomorphism. The Chinese remainder theorem then gives equivalence modulo every positive integer.

Here are explicit polynomials. Put \(\alpha=(1+\sqrt{13})/2\), \(\beta=(1+\sqrt{17})/2\). The two quadratic discriminants are 13 and 17. The product basis \(1,\alpha,\beta,\alpha\beta\) is integral and maximal. At 13 the \(\beta\)-order splits as \(\mathbb Z_{13}^2\), so its tensor product with the maximal \(\alpha\)-order is two copies of the latter. The same argument exchanges \(\alpha,\beta\) at 17. Away from 13 and 17 both quadratic orders are finite étale over \(\mathbb Z_p\), and so is their tensor product. It is therefore a product of maximal unramified orders. This gives maximality at every prime. On the \(B\) side use the bases \(1,(1+\sqrt m)/2\) for \(m=13,17,221\), since the three \(m\) are squarefree and 1 modulo 4. The quadratic factor contributes

\[
P_m(u,v)=2u^3+3u^2v+\frac{3(m+1)}{2}uv^2+\frac{3m+1}{4}v^3.
\]

Then \(f_B=P_{13}(u_1,v_1)+P_{17}(u_2,v_2)+P_{221}(u_3,v_3)\) and \(f_A=r^3+s^3+P_K(a,b,c,d)\), where

\[
\begin{aligned}
P_K={}&4a^3+6a^2b+6a^2c+3a^2d+42ab^2+6abc+42abd\\
      &+54ac^2+54acd+189ad^2+20b^3+21b^2c+30b^2d\\
      &+27bc^2+378bcd+270bd^2+26c^3+39c^2d+273cd^2+130d^3.
\end{aligned}
\]

For verification, expand \((a+b\alpha+c\beta+d\alpha\beta)^3\), replacing each \(\alpha^i\beta^j\) by the product of its two quadratic traces. The traces of powers 0 through 3 are \((2,1,7,10)\) for \(\alpha\) and \((2,1,9,13)\) for \(\beta\). For \(P_m\), the corresponding traces are \(2,1,(m+1)/2,(3m+1)/4\).

For the global obstruction, polarize \(f_A\) over \(\mathbb Q\) to \(T(x,y,z)=\operatorname{Tr}(xyz)\). This uses the mixed coefficient divided by 6. If \(C\) is in its centroid, using \(y=1\) gives \(\operatorname{Tr}((Cx)z)=\operatorname{Tr}(x(C1)z)\) for every \(z\). The trace pairing of an étale algebra is nondegenerate, so \(Cx=x(C1)\). Every multiplication map conversely satisfies the centroid condition. Hence the centroid is the original algebra. A rational equivalence of the cubics would identify their centroids, which is impossible by the global factor dimensions. The same obstruction holds if equivalence up to a nonzero rational scalar is allowed, since rescaling a trilinear form preserves its centroid.

Over \(\overline{\mathbb Q}\), both algebras split into six copies of the base field, and both trace cubics become the sum of six independent cubes. In particular their projective hypersurfaces are smooth. The local statements here concern linear equivalence of whole cubic polynomials.

The same underlying algebras refute the local–global conjecture for rational algebra isomorphism in Kayal's thesis. De Smit and Perlis had already constructed nonisomorphic number fields with isomorphic local algebras everywhere, so they supply an earlier counterexample to the algebra formulation. Their construction also yields an eight-variable trace-cubic example. [Kayal, §8.5, p. 124](https://www.cse.iitk.ac.in/%75sers/manindra/Students/thesis_kayal.pdf) · [De Smit and Perlis, p. 2](https://arxiv.org/pdf/math/9410216)

## Priority and scope

Lin, Shinder and Zimmermann already give the six-dimensional étale-algebra pattern with general independent rational square classes in Example 2.14 of *Factorization centers in dimension 2*. Their Example 2.7 describes the underlying Klein-four relation between the split, quadratic, and regular permutation actions. The trace centroid is classical. The result claimed here is the choice of square classes giving equivalence at every completion and the trace-cubic transfer answering the precise cubic equivalence question. A targeted literature search did not identify an earlier statement of this particular six-variable cubic counterexample or of the arbitrary-ring reduction above. Priority remains provisional. Both proofs are informal. [Lin, Shinder and Zimmermann, Examples 2.7 and 2.14](https://api.algebraicgeometry.nl/Article/20075/2023-6-024.pdf)

Six variables are optimal within the class of trace cubics of finite étale \(\mathbb Q\)-algebras. Indeed, local equivalence at all but finitely many primes identifies the local centroid algebras by the same trace-pairing proof over \(\mathbb Q_p\). If one starts with equivalence modulo all powers of \(p\), the compactness of \(\operatorname{GL}_n(\mathbb Z_p)\) gives a single \(p\)-adic equivalence: the closed sets of matrices solving the polynomial identity modulo successive powers are nested and nonempty. For unramified primes the local centroid isomorphisms identify the Frobenius cycle types on the two finite sets of embeddings. By Chebotarev, every conjugacy class of a common Galois splitting group occurs at a good prime, so the two Galois sets are Gassmann equivalent. For cardinality at most five, Proposition 2.5 of Lin, Shinder and Zimmermann makes them isomorphic as Galois sets. Étale descent then identifies the rational algebras and hence their trace cubics. [Lin, Shinder and Zimmermann, Proposition 2.5](https://api.algebraicgeometry.nl/Article/20075/2023-6-024.pdf)
