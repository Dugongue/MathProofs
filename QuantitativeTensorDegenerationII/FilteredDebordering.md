# Exact degeneration order and debordering for filtered split algebras

For a finite-dimensional commutative \(K\)-algebra \(B\), write \(\mu_B\) for its multiplication tensor, in bilinear-map notation. Write \(\Delta_n\) for coordinatewise multiplication on \(K^n\). A witness of approximation order \(a\) and error degree at most \(b\) is a polynomial identity
\[
 W(t)(U(t)x\odot V(t)y)=t^a\bigl(\mu_B(x,y)+tT_1(x,y)+\cdots+t^b T_b(x,y)\bigr)
\]
with all three matrices square of size \(n=\dim_K B\). We use the minimum \(a\) over these same-size witnesses. The displayed identity is simultaneously an order and an error bound for one witness.

**Theorem 1 (filtered split algebras).** Let \(F_{-1}=0\subseteq F_0\subseteq\cdots\subseteq F_s=K^n\) be an increasing unital \(K\)-linear filtration of \(K^n\) with coordinatewise multiplication, extended by \(F_j=K^n\) for \(j\ge s\). Assume \(F_iF_j\subseteq F_{i+j}\). Then \(\mu_{\operatorname{gr}_F K^n}\) has a same-size polynomial witness of order \(s\), with its error degree and each of its three matrix degrees at most \(s\). For \(s>0\) and \(|K|\ge s+1\), the tensor rank is at most \(sn+d_s\), where \(d_s=\dim(F_s/F_{s-1})\). If the associated graded algebra is generated over \(F_0\) by its degree-one part with nonzero degree-\(s\) part, its minimum order is exactly \(s\).

*Construction.* Choose nested coordinate sets \(S_d\) with \(S_{-1}=\varnothing\) and \(F_d\to K^{S_d}\) an isomorphism by restriction. Coordinate functionals independent on \(F_{d-1}\) remain independent on \(F_d\) and can be extended to a basis of \(F_d^*\) using coordinate functionals. In each \(F_d\), choose basis vectors for the kernel of restriction to \(S_{d-1}\), a complement to \(F_{d-1}\). Write the combined basis as \((f_i)\) with degrees \(d_i\) and put \(E=[f_1\ \cdots\ f_n]\). If \(f_i f_j=\sum_k c^k_{ij} f_k\), every nonzero coefficient satisfies
\[
 \max(d_i,d_j)\le d_k\le d_i+d_j.
\]
The upper bound follows from multiplicativity. For the lower bound, the product vanishes on \(S_{\max(d_i,d_j)-1}\), as do all basis vectors in degrees at least \(\max(d_i,d_j)\). Restriction is injective on the span of the lower-degree basis vectors.

Set \(D(t)=\operatorname{diag}(t^{d_i})\) and \(D_s(t)=\operatorname{diag}(t^{s-d_i})\). Use \(U(t)=V(t)=E D(t)\) and \(W(t)=D_s(t)E^{-1}\). The coefficient in question is \(c^k_{ij}t^{s+d_i+d_j-d_k}\). Terms with \(d_k=d_i+d_j\) give multiplication in the associated graded, and every remaining exponent exceeds \(s\) by at most \(\min(d_i,d_j)\le s\). Dividing by \(t^s\) gives a degree-\(\le s\) tensor polynomial. At each nonzero parameter its rank is at most \(n\) because of the displayed diagonal witness. For \(s>0\), exponent excess \(s\) requires \(d_i=d_j=d_k=s\). The degree-\(s\) basis spans the subspace of functions vanishing on \(S_{s-1}\). This is a coordinate ideal of dimension \(d_s\), so the highest coefficient is its coordinatewise multiplication, extended by projecting both inputs to that component. Its rank is at most \(d_s\). Interpolate the normalized polynomial after subtracting its known highest term at \(s\) distinct nonzero scalars. This expresses the constant coefficient as a linear combination of the \(s\) original evaluations and the highest coefficient, and gives rank at most \(sn+d_s\). For \(s=0\) the tensor is split diagonal in any field. Finally the unit slice is invertible, so flattening rank is \(n\) and the exhibited \(n\)-summand degeneration attains border rank \(n\).

### Elementary order lower bound

For any finite-dimensional commutative unital target with Jacobson radical \(\mathfrak m\), approximation order \(a\) for a same-size witness implies \(\mathfrak m^{a+1}=0\). To see this, let \(O=K[[t]]\), \(L=K((t))\), and write \(D=t^{-a}W\). Let \(u=U1\), \(v=V1\), \(P=D\operatorname{diag}(v)U\), and \(Q=D\operatorname{diag}(u)V\). The two unit slices \(P,Q\) belong to \(\operatorname{GL}_n(O)\), by reduction modulo \(t\). Hence \(D,U,V\) are invertible over \(L\) and all entries of \(u,v\) are nonzero in \(L\). Precompose the two inputs of the normalized family with \(P^{-1},Q^{-1}\). The resulting product is
\[
 (x,y)\longmapsto H\bigl((H^{-1}x)\odot(H^{-1}y)\bigr),\qquad
 H=D\operatorname{diag}(u\odot v).
\]
It is defined over \(O\), with the original multiplication modulo \(t\) and with unit \(H1\in O^n\). Therefore \(\Lambda=H^{-1}O^n\) is a unital finite free \(O\)-algebra inside \(L^n\). Integrality of each coordinate gives \(\Lambda\subseteq O^n\), and \(t^aH\in\operatorname{Mat}_n(O)\) gives \(t^aO^n\subseteq\Lambda\). If a lift in \(\Lambda\) reduces to an element of \(\mathfrak m\) in \(\Lambda/t\Lambda\), a power of the lift lies in \(t\Lambda\subseteq tO^n\). Thus the lift is in \(tO^n\), and the product of \(a+1\) such lifts belongs to \(t^{a+1}O^n\subseteq t\Lambda\). The conclusion follows. In Theorem 1 the positive-degree ideal is the Jacobson radical, since it is nilpotent and the degree-zero quotient is a reduced finite algebra. If the graded algebra is generated in degree one over degree zero, then \(A_s=\mathfrak m^s\ne0\) for \(s>0\), so this lower bound is sharp. The case \(s=0\) follows from the explicit witness.


For \(a\le2\) this argument also gives an intrinsic description of the targets. If \(A\) is split local, the image of \(\Lambda\to K^n\) modulo \(t\) is \(K1\), since the map factors through \(A\) and \(K^n\) has no nonzero nilpotents. Since \(t^2O^n\subseteq\Lambda\), every element of \(\Lambda\) is a constant in \(K1\), plus \(t\) times an element of a subspace \(F_1\subseteq K^n\), plus an arbitrary element of \(t^2O^n\). More precisely, \(F_1=\{x\in K^n:tx\in\Lambda\}\) contains \(1\), and the description follows by subtracting the constant and the terms of order at least two. Thus \(A=\Lambda/t\Lambda\) is isomorphic to the associated graded algebra of \(K1\subseteq F_1\subseteq K^n\), by sending the class of \(x\) in degree \(i\) to the class of \(t^i x\). Theorem 1 proves the converse. In particular, on split local targets with \(\mathfrak m^2\ne0\), minimum order \(2\) is equivalent to the existence of this split filtration with \(s=2\).

## An explicit family of Loewy length three

**Theorem 2 (cyclic self-adjoint powers).** Let \(K\) be algebraically closed of arbitrary characteristic. Let \(V\) be an \(e\)-dimensional \(K\)-space, \(q\) a nondegenerate symmetric bilinear form, and \(T\) a \(q\)-self-adjoint endomorphism with a cyclic vector. For \(1\le h\le e\), consider \(A=K1\oplus V\oplus K^h\) with the product of \(x,y\in V\) given by
\[
 xy=(q(x,y),q(Tx,y),\ldots,q(T^{h-1}x,y)),
\]
and with \(K^h\) annihilating the positive-degree part. Put \(n=1+e+h\). Then \(A\) admits a split filtration model \(K1\subseteq F_1\subseteq K^n\). Its multiplication tensor has border rank \(n\) and minimum same-size approximation order exactly \(2\). The witnessing matrices have degrees at most \(2\), the error degree is at most \(2\), and its tensor rank is at most \(2n+h\). The same-field conclusion holds over any \(K\) admitting the polynomial \(P\) constructed below with all its roots in \(K\).

*Choosing the nodes.* A chosen cyclic vector identifies \(V\) with \(R=K[z]/(p)\), where \(p\) is the monic minimal polynomial of \(T\), of degree \(e\), and \(T\) acts as multiplication by \(z\). Put \(\tau(r)=[z^{e-1}]r\) for the unique representative of degree \(<e\). The pairing \(\tau(rs)\) is perfect. Indeed, a nonzero degree-\(d\) representative pairs nontrivially with \(z^{e-1-d}\). Self-adjointness implies \(q(r,s)=q(1,rs)=\tau(grs)\) for a unique \(g\in R\). Multiplication by \(g\) is injective because \(q\) is nondegenerate, hence \(g\) is a unit.

Let \(a\in K[z]\) of degree \(<e\) represent \(-g^{-1}\). Choose a monic split squarefree \(P\) of degree \(n\) congruent to \(a\) modulo \(p\). To prove existence over an algebraically closed field, consider
\[
 P_\lambda=a+p(z^{h+1}+u z+\lambda).
\]
Choose \(u\) so the rational function \(z^{h+1}+uz+a/p\) has nonzero derivative. At most one \(u\) can be excluded. Since \(\gcd(a,p)=1\), a multiple root of \(P_\lambda\) must be a zero of this derivative away from the roots of \(p\). There are finitely many such zeros and each excludes at most one \(\lambda\). This yields the required split \(P\) in every characteristic, including when \(p\) is inseparable.

*The filtered algebra.* Let \(c_1,\ldots,c_n\) be the distinct roots of \(P\), and set \(d_i=p(c_i)/P'(c_i)\). On \(K^n\) define
\[
 \ell_j(X)=\sum_i c_i^j d_iX_i \quad(0\le j<h),\qquad
 F_1=\bigcap_{j=0}^{h-1}\ker\ell_j.
\]
These \(h\) functionals are independent because the \(c_i\) are distinct and the \(d_i\) are nonzero. By Lagrange interpolation, \(\sum_i f(c_i)/P'(c_i)=0\) whenever \(\deg f<n-1\). Taking \(f=z^j p\) shows \(1\in F_1\). Taking \(f=z^jr\) shows that \(F_1\) contains every evaluation vector \((r(c_i)/p(c_i))_{i=1}^n\) with \(\deg r\le e\). These vectors form a space of dimension \(e+1\) by injectivity of polynomial evaluation in this degree range, so they exhaust \(F_1\). Constants correspond to multiples of \(p\).

Identify \(F_1/K1\) with \(R\) via those evaluations. Identify \(K^n/F_1\) with \(K^h\) via the \(\ell_j\). To compute the resulting product on the associated graded, take representatives \(r,s\) of degree \(<e\). Write the partial fraction identity
\[
 \frac{z^jrs}{pP}=\frac{u_j}{p}+\frac{v_j}{P},
 \quad\deg u_j<e,\quad \deg v_j<n.
\]
Here \(u_j\equiv z^jrsP^{-1}\pmod p\) and \(v_j\equiv z^jrsp^{-1}\pmod P\). The rational function on the left has zero coefficient of \(z^{-1}\) at infinity by its degree. Lagrange interpolation identifies the contribution from \(v_j/P\) to this coefficient with \(\ell_j((r(c_i)s(c_i)/p(c_i)^2)_i)\). Thus
\[
 \ell_j\bigl((r(c_i)s(c_i)/p(c_i)^2)_i\bigr)
 =-\tau\bigl(z^jrsP^{-1}\bigr)
 =\tau\bigl(gz^jrs\bigr)
 =q(T^jr,s).
\]
This proves the required product, including all Gram coefficients, without a field-dependent choice of square roots. The \(h\) forms are linearly independent because \(q\) is perfect and the minimal polynomial of \(T\) has degree \(e\). Their simultaneous map onto \(K^h\) is surjective on the linear span of the products, so the degree-two part is generated by the degree-one part. Theorem 1 and the order lower bound apply.

For \(h=2\) this includes any regular pencil of symmetric bilinear forms whose normalized operator with respect to an invertible member is cyclic. It includes the simple-spectrum locus and cyclic Jordan blocks in every characteristic. The parameter \(h\) may grow to \(e\). These are intrinsic multiplication conditions on \(A\), and the cyclic operator acts on the first radical quotient \(V\).


For example, one may take \(p=z^e\) and \(q(r,s)=\tau(rs)\), so the operator has a single nilpotent Jordan block of size \(e\). If a field contains all \(n\)-th roots of unity and its characteristic does not divide \(n\), \(P=z^n-1\) works for this example. More generally, over any field with more than \(2e+h\) elements, the same derivative argument gives a squarefree \(P\) over the field, since the derivative numerator has degree at most \(2e+h\). The split model then holds over the separable splitting field of \(P\). The existence of a squarefree \(P\) over a finite field alone gives no splitting assertion over that field.

### Single output form over finite fields

Here is a same-field construction for a separate class. Let \(b\) be the nonzero symmetric bilinear form defining \(\mathfrak m^2\) for a split local algebra with \(\mathfrak m^3=0\) and \(\dim_K\mathfrak m^2=1\). Choose any complement of \(\mathfrak m^2\) in \(\mathfrak m\) to view \(b\) as a form on the first radical quotient. Its radical splits off as a square-zero summand with a common unit. It suffices to treat the perfect part of \(b\), of dimension \(r\).

Choose \(r+2\) nonzero weights \(d_i\) whose sum is zero, and set \(F_1=\ker\ell\) for \(\ell(x)=\sum_i d_i x_i\) in \(K^{r+2}\). The induced form \(\ell(xy)\) on \(F_1/K1\) is perfect, since \(F_1\) is the orthogonal complement of \(1\) for the perfect diagonal form with coefficients \(d_i\). A match with \(b\) up to scalar yields the required split filtration. A square-zero summand with common unit is accommodated by adjoining a simple filtered point algebra. In detail, for any two filtered point-algebra models with scalar degree zero, take the fiber product of their split sources along a selected coordinate evaluation of each to \(K\), with the entrywise filtration. This is a split algebra of dimension \(n_1+n_2-1\). In each positive degree the associated graded is the direct sum of the two graded parts, since matching the chosen coordinates requires only subtracting a constant from one component. The associated graded multiplication is the original componentwise multiplication with common constants. A square-zero graded algebra itself is obtained from the filtration \(K1\subseteq K^m\). Theorem 1 now gives exact order \(2\) and error degree at most \(2\).

Over a finite field of odd order, the square class of the determinant of the induced form is the class of \(-\prod_i d_i\), by splitting out the hyperbolic plane containing \(1\). Perfect symmetric forms there are classified by dimension and determinant square class. One can see this by diagonalizing, then using that the equation \(a x^2+b y^2=1\) for nonzero \(a,b\) has a solution by intersecting two sets each of size \((|K|+1)/2\). Repeatedly splitting out a line of norm \(1\) leaves a final line of prescribed square class. If \(r\) is odd, scaling the output form can change its determinant square class, and zero-sum weights come from \((1,1,-2)\) and cancelling pairs. If \(r\) is even and \(|K|\ge5\), use \((1,1,x,-2-x)\) and cancelling pairs. The product in the quartet takes both nonzero square classes. For the quadratic character \(\chi\), the sum of \(\chi(y^2-1)\) over the field is \(-1\), by counting solutions of \((y-v)(y+v)=1\). Removing the two zeros leaves both signs when the field has at least five elements. The quartet product is \(1-(x+1)^2\), so the claim follows. Over \(\mathbb F_3\) and even \(r\ge4\), six weights equal to \(1\) give the opposite product square class from three cancelling pairs, and add cancelling pairs for the remaining even number of positions.

Over a finite field of characteristic two, the induced form is alternating exactly when all \(d_i\) are equal, since
\[
 \sum_i d_i x_i^2=\Big(\sum_i \sqrt{d_i}\,x_i\Big)^2,
\]
and this is zero on \(\ker\ell\) exactly when the two linear functionals are proportional. A perfect alternating form has even dimension, and constant weights suffice, including over \(\mathbb F_2\). Over an even field of size at least four, obtain nonconstant weights for an even number of positions using identical pairs of two distinct nonzero values, and for an odd number using \((a,b,a+b)\) with nonzero distinct \(a,b\) plus identical pairs. Over a perfect field of characteristic two a perfect nonalternating symmetric bilinear form is congruent to the identity: split off norm-one lines as long as possible, put any alternating remainder into hyperbolic planes, and use one norm-one line together with any one such plane to split out three norm-one lines. In coordinates for \(1\perp\left(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\right)\), the three vectors are \((1,1,0),(1,0,1),(1,1,1)\). This proves the same-field conclusion for every single-form algebra over finite fields of size at least four, as well as the specified cases over \(\mathbb F_2\) and \(\mathbb F_3\).


## Relation to earlier work

The filtered split model is the algebra of a one-step graded limit of a reduced point configuration. Erman and Velasco give the total-degree initial-ideal map and a quadratic coordinate formula for this construction in Propositions 3.1–3.2. Cartwright, Erman, Velasco and Viray prove qualitative smoothability for the full family with Hilbert function \((1,e,2)\). Zhao uses the one-step parametrization to establish smoothability for additional Hilbert functions in embedding dimension five. The quantitative statements here use a basis adapted to nested coordinate restrictions, and Theorem 2 constructs a point configuration with the exact target bilinear forms, including cyclic non-semisimple operators and arbitrarily large \(h\). [Erman–Velasco](https://arxiv.org/abs/0812.3342) [Cartwright–Erman–Velasco–Viray](https://arxiv.org/abs/0803.0341) [Zhao](https://arxiv.org/html/2606.22368v2)

Ganesh, Koiran and Oliveira obtain polynomial approximation-order bounds for their three-slice setting and apply a \(1\)-regular normalized-slice hypothesis for arbitrarily many slices. The multiplication tensor in Theorem 2 has \(n\) independent regular-representation slices, and its invertible slices are multiplication by a unit. Each normalized multiplication slice is multiplication by an element, which is a scalar plus a nilpotent operator of cube zero. For \(n>3\) the eigenspace is larger than one-dimensional. Here cyclicity acts on the smaller space \(V\), and the quantitative bound uses the filtered split model for the full multiplication tensor. [Ganesh–Koiran–Oliveira, Theorems 1.6–1.7](https://arxiv.org/html/2608.10179)

The proofs above are mathematical arguments. This note does not contain a Lean kernel verification.
