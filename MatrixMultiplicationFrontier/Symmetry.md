# Tensor isomorphism on pencils of matrix multiplication tensors

**Theorem.** Over every field, ordinary three-tensor isomorphism is polynomial-time many-one equivalent to isomorphism of an unmarked pencil of bilinear maps on three matrix spaces, even on the promise family constructed below. The pencil is a four-tensor of format \((2,n^2,n^2,n^2)\). Equivalence allows arbitrary independent changes of basis in each of the four modes, including its two-dimensional parameter space. All points of the projective parameter line except one represent square matrix multiplication up to isotopy, over every extension field. At the exceptional point the output flattening has smaller rank. For each fixed input format and fixed support dimensions, even that point has the same individual tensor isomorphism type for all instances.

The same equivalence holds for simultaneous isomorphism of an **ordered pair** of matrix multiplication tensors, the second obtained from the first by one determinant-one output change \(I+N\) with \(N^2=0\). On the displayed hard instances, every positive comparison of either kind admits determinant-one changes on every mode. These statements concern the relative position of tensors. They give an informal proof of restricted TI-completeness and make no claim concerning the matrix multiplication exponent.

## Embed a slice space in one output shear

By Gaussian elimination on the three flattenings, restrict the input tensors to their minimal supports. Unequal original formats or unequal support dimensions give an immediate negative answer, and zero tensors can be handled directly. Every isomorphism of the supports extends to the original spaces of equal dimensions. For each remaining nonzero tensor take its independent matrix slices \(M_1,\ldots,M_r\in\operatorname{Hom}(B,A)\). Write \(a=\dim A\), \(b=\dim B\), and \(S=\langle M_i\rangle\). Their joint image spans \(A\) and their common kernel is zero. Isomorphism of the input tensors is equivalent to \(P_0 S Q_0^{-1}=S'\) for isomorphisms on \(A,B\), since the third change of basis takes care of the choice of basis of the slice space. [Grochow and Qiao, section 2](https://arxiv.org/abs/1907.00309)

Set \(C=F^r\) with ordered basis \(c_i\) and define \(m:C\to S\) by \(m(c_i)=M_i\). Set \(n=\max(a+r+1,b+2)\). Make three spaces \(U,W,V\) of dimension \(n\). In \(U=A\oplus C\oplus U_0\), the space \(U_0\) has dimension at least one. In \(V=B\oplus Ft\oplus V_0\), the space \(V_0\) also has dimension at least one. Identify \(S\) with maps \(V\to U\) supported on the block from \(B\) to \(A\), and put \(E=\operatorname{Hom}(V,U)\). Write \(\pi_C:U\to C\) for the displayed projection. Use ordinary square matrix multiplication
\[
 \mu:\operatorname{Hom}(W,U)\times\operatorname{Hom}(V,W)\to E,
 \qquad (X,Y)\mapsto XY.
\]
Define \(N:E\to E\) by \(N(Z)=m(\pi_C Zt)\). Its image is \(S\), its rank is \(r\), and it squares to zero because its output is supported in the indicated block. The ordered pair is \((\mu,(I+N)\mu)\), and the pencil is the two-dimensional space \(\mathcal L_S=\langle\mu,N\mu\rangle\). All entries of the output can be written using polynomially many field operations, and \(n\) is linear in the sum of the input side lengths.

The output flattening of \((sI+uN)\mu\) has rank \(n^2\) for \(s\ne 0\), since \(\mu\) is onto and \(I+(u/s)N\) is invertible. At \(s=0\), \(u\ne0\), it has rank \(r<n^2\). Thus the exceptional line is intrinsic, including in characteristic two. Every normalized regular member \((I+vN)\mu\) is individually equivalent to \(\mu\) by a determinant-one output change. For fixed dimensions the exceptional member factors as the same map \((X,Y)\mapsto\pi_C XYt\) followed by the injection \(m:C\hookrightarrow E\). Any two such injections differ by a change of basis of \(E\), whose determinant can be made one using a complement to their images. This proves the individual-member assertions, after every field extension as well.

## Recover the slice space from a pencil transporter

Let \(f,g,h\) be invertible maps of the three matrix spaces taking the pencil onto the target pencil, with the action on a bilinear map given by output change and inverse input changes. The unique exceptional line goes to its counterpart. For some \(s,u,v\in F\), with \(sv\ne0\), the transport equations therefore read
\[
 h(XY)=(sI+uN')\big(f(X)g(Y)\big),\qquad
 hN(XY)=vN'\big(f(X)g(Y)\big).
\]
Put \(k=(sI+uN')^{-1}h\). Then \(k(XY)=f(X)g(Y)\), and surjectivity of multiplication gives
\[
 kNk^{-1}=(v/s)N',
\]
using \((N')^2=0\). In particular \(k(S)=S'\). An ordered-pair transporter also transports the pencil because the two specified members span it.

In square matrix coordinates every output isotopy \(k\) of multiplication has the form \(Z\mapsto PZQ^{-1}\). Here is a direct argument over the ground field. Put \(D=f(I)\) and \(H=g(I)\). Both are invertible because the maps \(Y\mapsto Dg(Y)\) and \(X\mapsto f(X)H\) are onto. Substitution gives \(k(XY)=k(X)(DH)^{-1}k(Y)\). Hence \(Z\mapsto(DH)^{-1}k(Z)\) is a unital algebra automorphism of \(M_n(F)\). If \(E'_{ij}\) are the images of the matrix units, take any nonzero \(w\) in the image of \(E'_{11}\). The vectors \(E'_{i1}w\) are a basis, as applying \(E'_{1j}\) detects the \(j\)-th coefficient. In that basis the images are the ordinary matrix units. Thus the automorphism is inner and the asserted left-right form follows. This is the usual matrix multiplication symmetry computation. [Bürgisser and Ikenmeyer, matrix multiplication stabilizer](https://www3.math.tu-berlin.de/algebra/work/stoc256-burgisser.pdf)

Now \(PSQ^{-1}=S'\) in \(E\). The sum of the images of \(S\) is precisely \(A\), and its common kernel is \(Ft\oplus V_0\). Thus \(P\) induces an isomorphism on the image support, while \(Q\) induces one on the quotient by the common kernel. On these intrinsic spaces the equation recovers a left-right equivalence of the original slice spaces. This proves soundness even under arbitrary pencil reparametrizations.

## Lift all input equivalences and account for complexity

Conversely let \(P_0 S Q_0^{-1}=S'\), and define \(R:C\to C'\) by
\[
 m'(Rz)=P_0 m(z) Q_0^{-1}.
\]
Extend \(P_0,R\) block-diagonally to \(P:U\to U'\) and \(Q_0\) to \(Q:V\to V'\), taking \(t\) to \(t'\). Choose the maps on the nonzero padding spaces to give both \(P,Q\) determinant one in the displayed bases. With the middle spaces identified by their bases, set
\[
 f(X)=PX,\qquad g(Y)=YQ^{-1},\qquad h(Z)=PZQ^{-1}.
\]
Then \(h\mu=\mu'(f,g)\) and \(N'h=hN\), the second equality following from \(\pi_{C'}P=R\pi_C\) and \(Qt=t'\). Thus the maps transport the ordered pair and the pencil with the identity parameter map. Each of \(f,g,h\) has determinant one because matrix left and right multiplication have determinants \((\det P)^n\) and \((\det Q)^{-n}\), respectively.

For trivial decision branches of the forward reduction use fixed identical instances for yes and fixed instances of different \(n\) for no. In the reverse direction an unmarked pencil is already a four-tensor, so the polynomial reduction from fixed-order tensor isomorphism to ordinary three-tensor isomorphism applies over the same field. For an ordered pair, one may instead encode a fixed system of two trilinear tensors with shared roles. Both upper bounds apply to arbitrary raw changes of basis under ordinary equivalence. The determinant-one witness assertion concerns the displayed outputs of the forward construction. [Grochow and Qiao, Theorem B and Corollary B](https://arxiv.org/abs/1907.00309) · [Futorny, Grochow and Sergeichuk, Wildness for tensors](https://arxiv.org/abs/1810.09219)

All arguments are algebraic over the ground field. The reduction uses polynomially many arithmetic operations in the dense representation, and gives ordinary deterministic polynomial-time reductions over each fixed finite field. The proof is informal.

## A pencil of compatible associative products

**Theorem.** A second construction gives the same TI-completeness for unmarked pencils on a single vector space whose every member is an associative product. There is a common identity for all normalized affine products. Every affine product gives a split full matrix algebra, and every fourfold product in the exceptional algebra vanishes. Equivalence of these pencils is TI-complete both for a single change of algebra coordinates and for three independent changes of matrix-space coordinates. The parameter change is unrestricted in both cases. The ordered pair of products at parameters 0 and 1 gives the corresponding completeness results for ordered pairs of split matrix algebra structures. On the constructed instances each positive comparison has a simultaneous algebra-coordinate change of determinant one.

Odesskii and Sokolov relate associative products compatible with ordinary complex matrix multiplication to representations of their M-structures. With further hypotheses they describe M-structures associated with affine Dynkin diagrams, and they connect compatible products to the classical Yang–Baxter equation. Here the input is an arbitrary three-tensor over any field, and the output is a pencil whose equivalences recover precisely the input isomorphism decision. The rank gap below yields this recovery even under three independent matrix-space changes on an unmarked pencil. The construction uses the familiar operator formula for an infinitesimal deformation. [Odesskii and Sokolov, Algebraic structures connected with pairs of compatible associative algebras](https://arxiv.org/abs/math/0512499) · [Odesskii and Sokolov, Pairs of compatible associative algebras, classical Yang–Baxter equation and quiver representations](https://arxiv.org/abs/math/0611200)

Take the same compact slice space \(S\) and injection \(m:C\to S\). On this occasion use a single space
\[
 H=A\oplus B\oplus C\oplus Ft\oplus H_0,
 \qquad n=\dim H=\max(a+b+r+1,4r+1).
\]
The padding \(H_0\) can have dimension zero. Put \(E=\operatorname{End}(H)\), and extend \(m(z):B\to A\) by zero on the other summands. Again write \(N(X)=m(\pi_C Xt)\). Then \(N(I)=0\) and \(N^2=0\). Let \(\mu\) denote ordinary multiplication on \(E\). For an operator \(L\) on \(E\), write
\[
 \delta L(X,Y)=L(XY)-L(X)Y-XL(Y).
\]
The new pencil is \(\langle\mu,\nu\rangle\) with \(\nu=\delta N\). The shear \(\phi_z=I_E+zN\) fixes the identity matrix. Its transport of the ordinary product is exactly
\[
 \phi_z\big(\phi_z^{-1}(X)\phi_z^{-1}(Y)\big)=XY+z\nu(X,Y).
\]
Indeed \(N(X)N(Y)=0\), \(N(N(X)Y)=0\), and \(N(XN(Y))=0\) by the disjoint supports: the image of \(N(X)\) lies in \(A\), its only active input block is \(B\), and it kills \(t\). This identity holds over the polynomial ring in \(z\). The affine products are split matrix algebras sharing the identity, and the coefficient of \(z^2\) in their associativity identity proves associativity of \(\nu\), including over finite fields.

Write \(D=\operatorname{Hom}(B,A)\subset E\) for the indicated block and let \(J\subset E\) be the sum of the maps with image in \(A\) and those supported on input \(B\). Then \(N(J)=0\), and
\[
 \nu(E,E)\subset J,\qquad \nu(J,E)+\nu(E,J)\subset D,
 \qquad \nu(D,E)=\nu(E,D)=0.
\]
The first inclusion follows directly from the formula for \(\delta N\). For the second, ordinary products in \(JD+DJ\) lie in \(D\), while every value of \(N\) lies in \(D\). For the last, \(D^2=0\), \(N(DE)=0\) and \(N(ED)=0\). This proves the fourfold vanishing by associativity. Since \(J\) is proper and all the affine products are onto, the exceptional projective line is intrinsic as soon as \(\nu\ne 0\).

We use the following rank fact twice. A derivation \(d\) of \(M_n(F)\) is inner: putting \(K=\sum_i d(E_{i1})E_{1i}\) gives \([K,E_{ab}]=d(E_{ab})\) by differentiating \(E_{ab}E_{i1}=\delta_{bi}E_{a1}\). If \(K\) is nonscalar there exists \(w\) such that \(w,Kw\) are independent: otherwise every line is invariant, which forces a common eigenvalue by considering sums of basis vectors. For matrices \(Y\) with \(Yw=0\), the vectors \([K,Y]w=-YKw\) run through the whole \(n\)-space. Hence any nonzero derivation has rank at least \(n\). In particular \(\nu=\delta N\ne0\), since \(N\ne0\) has rank \(r<n\).

Consider an equivalence of pencils, allowing three independent matrix-space maps. Its action takes \(\mu\) to \(s(\mu'+z\nu')\) and \(\nu\) to \(v\nu'\) for nonzero scalars \(s,v\). The simultaneous action of \(\phi'_u\) translates the affine parameter by \(u\) and fixes \(\nu'\), by \(\phi'_u\phi'_z=\phi'_{u+z}\) and the polynomial identity above. Compose with translation by \(-z\) and then scale the output by \(s^{-1}\). The resulting triple \((f,g,h)\) transports \(\mu\) to \(\mu'\) and \(\nu\) to \(c\nu'\) for \(c=v/s\ne0\). This normalization takes place in the larger independent-change group and so applies to the soundness of both comparisons.

With source and target in square matrix coordinates, define
\[
 D_1=fNf^{-1}-cN',\qquad D_2=gNg^{-1}-cN',
 \qquad D_3=hNh^{-1}-cN'.
\]
Expanding the transformation of \(\delta N\) and using \(h(XY)=f(X)g(Y)\) gives
\[
 D_3(XY)=D_1(X)Y+XD_2(Y).
\]
Each \(D_i\) has rank at most \(2r\), as the support dimensions can be checked before the reduction. Substituting the identity in the two input slots shows that \(D_3-D_1\) and \(D_3-D_2\) are right and left multiplications, respectively. A nonzero such multiplication has rank at least \(n\), while these differences have rank at most \(4r<n\). Thus all three maps coincide and are a derivation of rank below \(n\). The rank fact makes them zero. In particular \(hNh^{-1}=cN'\). As an output isotopy of matrix multiplication, \(h\) acts by a left-right change on \(E\). Passing to the image of \(N\) recovers the slice-space equivalence on its two supports exactly as before.

Conversely extend \(P_0,Q_0,R\) on the **disjoint** summands \(A,B,C\) to one block diagonal \(L:H\to H'\), with the evident identifications on \(Ft,H_0\). Then \(h(X)=LXL^{-1}\) intertwines \(N,N'\). It preserves ordinary multiplication and carries \(\delta N\) to \(\delta N'\), giving the desired simultaneous algebra change with identity parameter map. Conjugation on a full matrix space has determinant one. An ordered-pair transporter transports the whole pencil and the same converse works for the ordered pair.

For completeness in the reverse direction, the independent comparison is again an ordinary four-tensor problem. For the shared algebra-coordinate comparison introduce a parameter space \(K=F^2\), a role \(P=K\otimes E\), and the canonical bilinear map \(K\times E\to P\). Encode the pencil by the bilinear map \(P\times E\to E\) taking \((k\otimes X,Y)\) to the product at \(k\). The first map forces the induced coordinate change on \(P\) to be the tensor product of the changes on \(K,E\). This is a fixed system of order-three tensors sharing named roles, to which the same ordinary three-tensor compiler applies. For ordered pairs take the two individual product maps with their shared roles. The construction is polynomial in the original dense input size and holds over every field extension. The associative result is an informal proof. [Grochow and Qiao, Theorem B and Corollary B](https://arxiv.org/abs/1907.00309) · [Futorny, Grochow and Sergeichuk, Wildness for tensors](https://arxiv.org/abs/1810.09219)
