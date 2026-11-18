# Descent of arithmetic witnesses and polynomial-oracle reductions

Two extensions of the function-field IPS proof follow from combining multiplication coordinates, deterministic specialization, coefficient interpolation, and Hensel lifting. Throughout, shared subcircuits are charged once and an inverse gate is allowed only on a nonzero syntactically constant input, or a unit if the scalar algebra is not a field.

## 1. Simultaneous preservation of circuit witness tests

Let \(A\) be any finite-dimensional unital algebra over \(L=\mathbb Q(t_1,\ldots,t_d)\), with an explicit multiplication table in a basis \(b_0=1,b_1,\ldots,b_{r-1}\). The table and scalar inputs are rational functions given by division-free numerator and denominator circuits. The dimension, coefficient presentations and tests may all be parts of the input. Let \(C_w\) be a finite family of arithmetic witness circuits over \(A\), whose variables commute with the coefficients and each other. Consider any finite family of tests

\[
\sum_j R_j(x)\,C_{w_j}(\phi_j(x))=S(x)
\]

with rational polynomial multipliers \(R_j\), rational polynomial substitutions \(\phi_j\), and rational right side \(S\), all given by circuits. There is a deterministic polynomial-bit-time translation to rational witness circuits \(C'_w\) such that every test has exactly the same truth value on the two witness families. More strongly, every test residual has exactly the same monomial support in \(x\). In particular this covers both acceptance and rejection for the two identities of the Ideal Proof System on witnesses with legal scalar gates. The proof requires neither a map of rings \(A\to\mathbb Q\) nor that \(A\) be reduced.

First represent each \(A\)-gate by its coordinates. Multiply using the multiplication table. A constant inverse is the vector obtained by applying the inverse of its left multiplication matrix to the unit vector. Its coordinates use determinants and cofactors, which have polynomial-size division-free circuits from the characteristic-polynomial recurrence. This is valid for a unit even in a noncommutative algebra. All rational functions can be stored as integer-circuit numerator-denominator pairs by using shared circuit arithmetic. In each pair the denominator depends only on \(t\). This remains true after substituting the rational test polynomials. Form residual coordinate circuits for every test. Clear a common denominator \(D_i(t)\) for the coordinates of each residual, and denote the resulting integer polynomials by \(P_{ij}(t,x)\) for \(0\le j<r\).

Introduce a parameter \(u\) and form the polynomial \(\sum_j u^j P_{ij}(t,x)\) for each test. The powers of \(u\) distinguish the coordinate positions. Take the list of all required denominators together with these tagged residual circuits. A division-free integer circuit of size \(m\) with integer leaves of at most \(b\) bits has degree at most \(2^m\) and coefficient absolute sum at most \(2^{(b+1)2^m}\). The latter follows by induction since squaring a common bound \(B\ge 2\) covers both multiplication and addition. Take \(D=2^m+1\) and \(H=2^{(b+2)2^m}\) for common bounds \(m,b\). Set \(t_k=H^{D^{k-1}}\) and \(u=H^{D^d}\). Each exponent vector of a parameter monomial gives a distinct exponent of \(H\) by base-\(D\) expansion. Each nonzero coefficient polynomial in the remaining variables \(x\), viewed as a polynomial in the parameters, evaluates nonzero since its largest power of \(H\) dominates the sum of all lower powers. The same argument makes every required denominator nonzero. All chosen constants have polynomial-length circuit descriptions by repeated squaring, even when \(d\) varies.

For a witness with coordinates \(C_{wj}\), output

\[
C'_w(x)=\sum_{j=0}^{r-1} u^j C_{wj}(t,x)
\]

using the same chosen values of \(t,u\) everywhere. This coefficient map is rational-linear, fixes the unit and commutes with rational substitutions and multiplication by rational polynomials. Hence each translated residual is precisely the chosen specialization of its tagged cleared residual divided by \(D_i(t)\). The support assertion and truth equivalence follow. The construction uses the same witness variables throughout. The tests can also themselves be built from earlier translated rational-linear components, by treating their final shared circuit descriptions as the input. This strengthens the earlier valid-IPS certificate descent, which used only the coordinate of 1.

## 2. Polynomial-oracle reductions

Let \(K/\mathbb Q\) be a fixed finitely generated field with an explicit finite multiplication basis over \(L\) as above. Consider arithmetic circuits that can call a family of rational polynomial oracles of degree at most \(\delta\), where each oracle takes arbitrary circuit values as arguments. Every rational polynomial computable by a size-\(s\) such circuit over \(K\) is computable over \(\mathbb Q\) by a circuit over the same oracles with size polynomial in \(s,\delta\). Thus polynomially bounded-degree rational polynomial-oracle reducibility is invariant under this field extension. For uniform bit-time translation using explicit coefficient circuits, allow constant inverse gates whose operands are oracle-free. The nonuniform arithmetic size result allows legal constant inversions involving oracle evaluations.

By the primitive element theorem \(K=L[z]/(\mu)\) for a monic polynomial \(\mu\) of degree \(r\). Fix the resulting power basis and its coordinate conversion. Simulate all ordinary gates in this basis. At an oracle gate for \(g\in\mathbb Q[Y_1,\ldots,Y_k]\), the arguments are represented by \(v_i(z)\) of \(z\)-degree less than \(r\). The polynomial

\[
P(z)=g(v_1(z),\ldots,v_k(z))
\]

has \(z\)-degree at most \(\delta(r-1)\). Use that number plus one of distinct rational interpolation nodes. At each node evaluate the argument polynomials using the current coordinates and call the same oracle once. Fixed rational Lagrange interpolation recovers every coefficient of \(P\). Reduce \(P\) by the monic \(\mu\) to get the true \(r\) output coordinates. This only uses scalar additions and products, with shared input coordinates. Thus even arbitrarily nested oracle gates cost polynomial overhead in total circuit size and the degree bound. Powers of \(z\) modulo \(\mu\) and interpolation coefficients can be shared.

Next specialize the \(t\)-parameters. For the uniform version, the only denominators that must be inverted come from scalar leaves, multiplication and basis data, interpolation and the oracle-free constant inverses. The coordinates throughout the oracle computation belong to the localization inverting those denominators because each oracle has rational coefficients and calculates a polynomial. The same deterministic specialization as above, applied just to these denominator circuits, avoids all their zeros without requiring heights of oracle coefficients. For the nonuniform version every legal constant inverse gives finitely many additional nonzero denominators, and one rational point avoiding them exists. The coordinate of 1 at the output equals the required rational polynomial before specialization, so it still equals it afterwards. The reverse field transfer uses scalar inclusion. This combines the earlier deterministic specialization with the coefficient interpolation from the ideal-degree argument.

## 3. Closure under rational factors

In the nonuniform oracle model of the preceding section, if the output \(f\in\mathbb Q[x]\) has polynomially bounded degree, every rational factor of nonzero \(f\) also has a polynomial-size circuit over \(\mathbb Q\) with the same oracles. This combines oracle descent with the earlier coprime factor lifting argument.

After descending the oracle circuit, choose a rational direction \(y\) at which the highest homogeneous part of \(f\) is nonzero. In the resulting linear coordinates the polynomial and each nonconstant factor have their total degree as their \(y\)-degree and constant nonzero leading coefficient in \(y\). For an irreducible factor \(h\) occurring with multiplicity \(a\), take \(\partial_y^{a-1}f\). In characteristic zero this contains \(h\) with multiplicity exactly one. Indeed \(h\) has positive \(y\)-degree and is coprime to \(\partial_y h\), so successive derivatives reduce the multiplicity exactly by one until this stage. The derivative is computed by interpolation in \(y\). After normalization the resulting polynomial is monic in \(y\), with monic factors \(h,k\) coprime over the rational function field in the other variables. The resultant is nonzero. Choose a rational shift in the remaining variables \(x\) so that at \(x=0\) the univariate seeds \(h_0,k_0\) are coprime.

Insert a formal parameter \(t\) by replacing \(x\) with \(tx\). Extract coefficient circuits in \(t,y\) from the oracle circuit by bounded-degree rational interpolation. At lifting order \(j\), if \(E_j\) is the coefficient of the residual product error, determine corrections \(U,V\) solving

\[
k_0 U+h_0 V=E_j,\qquad \deg_y U<\deg_y h_0,\qquad \deg_y V<\deg_y k_0.
\]

Use \(U=(k_0^{-1}\bmod h_0)E_j\bmod h_0\) and \(V=(E_j-k_0U)/h_0\). All these operations divide by fixed monic polynomials or use fixed coprime seed data, and the residual degree in \(y\) is below \(\deg_y(h_0 k_0)\) by monicity. Each coefficient is therefore computed by polynomially many arithmetic gates, sharing earlier stages. The unique lifts agree through the degree of the desired factor with those of \(h(tx,y)\). Set \(t=1\), restore the original coordinates, and adjust leading scalars. Multiplying the recovered irreducible factors with their desired multiplicities proves the claim. The direction, shift and coprime seeds are nonuniform data.

These are informal arguments. They build on the repository's *Boolean Ideal Proof Systems and identity testing over function fields*, the deterministic descent in *Four algorithms and reductions around Grochow's questions*, and its ideal coefficient-recovery and Hensel uniqueness results. [Grochow, IPS and PIT](https://arxiv.org/html/2306.02184v1#S7.SS2)
