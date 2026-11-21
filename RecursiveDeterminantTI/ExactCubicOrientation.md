# An exact orientation-preserving cubic for associative algebra transporters

Let \(R\) be a commutative ring and let \(A,B\) be finite free, positive-rank unital associative \(R\)-algebras with displayed bases of the same size \(n\). Let \(X=A^2\) as a right regular module, \(Y=A^3\) as a left regular module, and \(W=A^{2\times3}\). Write
\[
 b_A(x,y)=(x_i y_j)_{i,j},\qquad
 f_A(x,y,z)=\sum_{i,j}z_{ij}(x_i y_j),\quad z\in W^*.
\]
The \(11n\)-variable cubic is linear in the number of nonzero structure constants and is used as a polynomial, including over finite rings.

**Theorem.** The transporter \(f_B\circ T=f_A\) is functorially parameterized by an algebra isomorphism \(\phi:A\to B\), a right \(A\)-linear automorphism \(P\) of \(A^2\), a left \(A\)-linear automorphism \(Q\) of \(A^3\), and a space of vertical shears whose coordinates are described below. The determinants in the displayed bases satisfy
\[
 \det_R T=(\det_R\phi)^{-1}(\det_R P)^{-2}(\det_R Q)^{-1}.
 \tag{1}
\]
There is a similar parameterization of the ordinary three-mode TI transporter of \(b_A,b_B\) with the same \(\phi,P,Q\) and no shears. If the algebra is split scalar-residue over \(R\) with a free based nilpotent filtration, the exact fiber \(\det_R T=\nu\) over \(\phi\) is a product of the stated shear space, explicit affine and linear-group factors, and the Kummer fiber
\[
 \{u\in R^\times : u^n=(\nu\det_R\phi)^{-1}\}.
 \tag{2}
\]
Over \(\mathbb F_3\) and even \(n\), this gives equality of signs for every cubic transporter. In particular it applies to the full family of commutative cube-zero algebras used in the ternary square-zero normal form, without restrictions on the graded bilinear data. The exterior volume of \(A\) is never materialized in this encoding. [Open Question 1.9](https://arxiv.org/html/2306.03135v2#S1.SS5) · [Earlier cubic transporter calculation](CubicTransporterSeed.md)

## Recovering the vertical space

Use the full polarization of \(f_A\) by inclusion-exclusion. It is natural under linear substitution and vanishes whenever two arguments are in \(W^*\). We call such a subspace isotropic: the two arguments are in the subspace and the third is arbitrary. Over a field, let \(L\subseteq X\oplus Y\) be the horizontal projection of an isotropic subspace and \(I\) its intersection with \(W^*\). The subspace \(I\) annihilates the image of every \(b_A(L_X,y)\) and \(b_A(x,L_Y)\) as \(x,y\) vary, where \(L_X,L_Y\) are the projections of \(L\). Indeed take one argument in \(I\), the second in a lift of \(L\), and the third purely horizontal in the opposite input slot. Taking \(y\) to be the unit separately in each of its three slots gives a common image span of dimension at least \(3\dim L_X\). Taking \(x\) to be the unit in each of its two slots gives at least \(2\dim L_Y\). For \(L\ne0\), at least one of these bounds strictly exceeds \(\dim L_X+\dim L_Y\): the failure of both would give \(2\dim L_X\le\dim L_Y\le\dim L_X\). Thus the codimension of \(I\) exceeds \(\dim L\). The unique isotropic subspace of dimension \(6n\) is the vertical one.

This descends to every commutative ring, with no loss over nilpotents. In every residue field the vertical component of the restriction of \(T\) to \(W^*\) is invertible, so its determinant is a unit over \(R\). Hence \(T(W^*)\) is the graph of \((u,v):W^*\to B^2\oplus B^3\). Take a functional \(z\) supported on \((i,j)\), take \(z'\) supported on \((i',j')\) with \(j'\ne j\), and put the third polarization argument entirely in the \(j'\)-th \(Y\) slot with value \(1\). The identity gives \(z'_{i'j'}(u(z)_{i'})=0\), since the other vertical term has column \(j\). Varying \(i'\) and the functional gives \(u(z)=0\). Taking \(i'\ne i\) and testing the \(i'\)-th \(X\) unit similarly gives \(v(z)=0\). These supported \(z\) span \(W^*\), proving the claim. This argument uses neither division nor identification of polynomials with polynomial functions.

## Recovering the ordered horizontal spaces and the algebra

Polarization with a vertical last argument yields the symmetric bimap
\[
 \beta((x,y),(u,w))=(x_i w_j+u_i y_j)_{ij}.
\]
Its paired adjoints are pairs \((D,E)\) of horizontal operators satisfying \(\beta(Dv,w)=\beta(v,Ew)\). Their multiplication is \((D,E)(D',E')=(DD',E'E)\). For two pure \(X\) arguments, the paired equality is \(u_i(D_{YX}x)_j=x_i(E_{YX}u)_j\). Take \(x\) supported at one row and \(u\) equal to the unit at a different row. This kills \(D_{YX}\) on each supported vector, and exchanging roles kills \(E_{YX}\). Two pure \(Y\) arguments kill the other off-diagonal blocks in exactly the same way using distinct columns. The mixed equation is
\[
 (D_Xx)_i w_j=x_i(E_Yw)_j.
\]
Taking unit vectors in turn forces \(D_X\) to be componentwise right multiplication by one \(\alpha\in A\) and \(E_Y\) to be componentwise left multiplication by \(\alpha\). The other mixed equation gives \(D_Y=L_\eta\), \(E_X=R_\eta\) for one \(\eta\in A\). This proves the adjoint algebra is \(A^{\mathrm{op}}\times A\), with the involution exchanging its paired operators interchanging the two factors.

A linear cubic transporter induces an isomorphism of these adjoint algebras by conjugation on the horizontal quotient. Over a field the adjoint factor idempotent corresponding to an indecomposable central block \(C\) of \(A\) has first-operator rank \(2\dim C\) on the \(X\) side or \(3\dim C\) on the \(Y\) side. An adjoint algebra isomorphism preserves the dimension of the block, and conjugation preserves the first-operator rank. The unequal multiplicities therefore pin the two sides even if \(A\) is commutative or has many central blocks. Over \(R\), the computed adjoint description commutes with base change. The central side idempotents thus agree with the prescribed ones over all residue fields. To see they agree over \(R\), localize at any maximal ideal. For a finite free algebra over a local ring, the maximal ideal times the algebra lies in its Jacobson radical: left and right multiplication by \(1-v\) for any \(v\) in that ideal are invertible by their determinants. Commuting idempotents that coincide modulo this ideal are equal, since their products with the other's complement are idempotents in the radical. Equality in all localizations is equality over \(R\). The first operators of the two idempotents project precisely onto the ordered horizontal spaces.

The induced isomorphism on \(A^{\mathrm{op}}\times A\) commutes with the involution, so is given by one algebra isomorphism \(\phi\). Its intertwining identity on the two regular module actions makes the horizontal blocks the base changes of \(\phi\) on the two and three copies, composed with \(P,Q\) as stated. Also \(b_A\) identifies \(X\otimes_A Y\) with \(W\) in the written coordinates. The horizontal blocks induce the map \(H:W_A\to W_B\) in this identification. The vertical linear block is \(H^{-T}\): it is determined by the polarization, and the module tensor product identity then shows that the three diagonal blocks preserve the original cubic as well. This yields a split parametrization over any base, even when \(2\) or \(3\) vanishes.

For the ordinary three-mode TI transporter of \(b_A,b_B\), the ordered slots are already included. Its middle paired adjoint algebra consists precisely of \((R_\alpha,L_\alpha)\), by testing the coordinate units in \(b_A(D_X x,y)=b_A(x,E_Yy)\). Its conjugation again recovers \(\phi\), and the module arguments give \(P,Q,H\). On these ordinary TI transporters the scalar \(\det_R P_{\rm full}\det_R Q_{\rm full}/\det_R H\) is exactly the determinant of the induced cubic map.

## The shear parameter and determinant

After removing the three diagonal blocks, a vertical shear is \(z\mapsto z+\gamma_X(x)+\gamma_Y(y)\). Its two bidegrees in the cubic condition give separate alternation equations. For \(\gamma_X\) the form \(L(x,x';y)=\gamma_X(x)(x'\otimes y)\) is balanced between \(x'\) and \(y\), and alternating in \(x,x'\). The coefficient of \(x_i^2\) vanishes and the sum of the two orders of every off-diagonal pair vanishes, so this conclusion holds in characteristic two. With \(y\) in one free left module slot, write \(L(x,x';r)\) for \(r\in A\). Moving \(a\) from either horizontal factor puts \(a\) on the left of \(r\). Hence the two ways to move \(a,b\) give \(L(x,x';(ab-ba)r)=0\). The span of these right multiples is the two-sided commutator ideal \(J_{\rm com}\), since \(u[a,b]=[ua,b]-[u,b]a\). Conversely alternating coefficients with values in \(\operatorname{Hom}_R(A/J_{\rm com},R)\) extend by multiplying the three coefficients in the commutative quotient. The \(Y\)-shear has the same description with left multiples. The whole additive shear parameter is thus
\[
 \operatorname{Hom}_R(A/J_{\rm com},R)^{\,3\binom 22+2\binom 32}.
\]
For a commutative \(A\) this is a free affine factor of rank \(9n\). Every shear has determinant one.

On the horizontal-plus-vertical blocks, applying \(\phi\) gives two plus three copies on the inputs and six inverse-dual copies on the vertical space. The output action of \(P\) on \(X\otimes_A Y\) is three copies of \(P\) and the output action of \(Q\) is two copies of \(Q\), using the other free module. Passing to inverse dual gives their inverse determinants. This proves (1).

For the split scalar-residue hypothesis, write \(A=R1\oplus J\), with \(J\) a nilpotent ideal and its graded factors free. Filter \(A^r\) by \(J^j\). The determinant of a module map is the \(n\)-th power of its residue determinant, since each quotient action consists of the same residue matrix repeated \(\operatorname{rank}(J^j/J^{j+1})\) times. The reduction splits and the lifts of the identity are the freely parameterized matrices \(1+M_r(J)\). Write \(p,q\) for the two residue determinants. By (1), their product in the cubic determinant is \((p^2 q)^{-n}\). Both \(p,q\) independently range over all units by a single diagonal entry. Changing coordinates from \((p,q)\) to \((p,u=p^2q)\) gives (2), and independently split each residual linear group into its determinant and determinant-one matrix. This is a functorial formula including nonreduced rings and all prescribed units. Over the ternary field and even \(n\), the residual powers are one, so every cubic sign equals the sign of \(\phi\) and every such sign lifts via the diagonal cubic action.

## A single ordinary TI instance when the determinant is recorded by a compact line

For a scalar-residue family, suppose the multiplication table of each member is augmented by a fixed number of tensors of order at most three, of polynomial coefficient size. Suppose this augmentation has a based one-dimensional role \(D_A\) and the following exact property: every algebra isomorphism \(\phi:A\to B\) lifts to it, and all such lifts act on \(D_A\to D_B\) by the scalar \(\det\phi\). This section uses an actual determinant record, for example the explicit Frobenius construction in [the companion proof](FrobeniusDeterminantLines.md).

Over any field \(k\), add the truncated polynomial algebra \(k[t]/t^{n+1}\) with its multiplication and a one-dimensional role attached to the line \(kt\). Every isomorphism of this record sends \(t\) to \(ut\) for an arbitrary \(u\in k^\times\); the action of \(t^n\) is exactly \(u^n\). Add an anchored line \(k e\), anchored by the vector \(e\). Append a bilinear map from the determinant role and the polynomial algebra to this line. In the source this map sends \(d_A\otimes t^n\) to \(e\); in the target it sends \(d_B\otimes t^n\) to \(\nu e\). It is zero on the other displayed monomial degrees. Since the polynomial-algebra map is forced by the degree-one inclusion and multiplication, preservation of the appended bilinear map gives exactly \(\nu\det\phi\,u^n=1\). Thus (2) is expressed on one and the same algebra isomorphism. The tensor-system compiler applies with a constant number of records. The extra algebra has dimension \(n+1\), and there is one ordinary TI instance over the original field, including in characteristics two and three. The same typed equivalence before that compiler holds over commutative base rings.

The unmarked cubic construction is uniform for all the algebras in the ternary square-zero normal form. The line-record step is established here for families with the stated explicit record. That distinction is the unresolved step for this approach to the unrestricted question. [Square-zero normal form](https://github.com/Dugongue/MathProofs/blob/main/TISLAtlasClosure/SquareZeroClosure.md) · [Tensor-system compiler, Theorem 4.1](https://arxiv.org/html/2306.03135v2#S4)

The proofs are written. The accompanying Lean replay verifies the elementary mode-rank, residual power, and determinant-coordinate identities used in the argument.

## Exact norm corrections beyond scalar-residue algebras

Suppose \(A\) is the base change of a finite-dimensional algebra \(A_0\) over a finite field \(k\). Let \(J_0\) be its Jacobson radical, and identify
\[
 A_0/J_0=\prod_i M_{d_i}(E_i)
\]
with finite field extensions \(E_i/k\). Write \(w_i^L\) for the sum of the multiplicities of the \(i\)-th simple left module in the layers \(J_0^j/J_0^{j+1}\), starting with \(j=0\), and \(w_i^R\) for the corresponding right multiplicities. These numbers can also be computed by the ranks of a minimal block idempotent on the layers, divided by \([E_i:k]\).

Over any commutative \(k\)-algebra \(R\), the residue \(P\) is described by a matrix \(P_i\in\mathrm{GL}_{2d_i}(E_i\otimes_k R)\) on each block, and similarly \(Q_i\in\mathrm{GL}_{3d_i}(E_i\otimes_k R)\). Their determinants on the underlying \(R\)-modules are
\[
 \det_R P=\prod_i N_{E_i\otimes R/R}(\det P_i)^{w_i^L},\qquad
 \det_R Q=\prod_i N_{E_i\otimes R/R}(\det Q_i)^{w_i^R}.
\]
Indeed the grade quotients are direct sums of the standard matrix modules, extended from \(k\). Restriction of scalars for a standard module gives the norm of its determinant, as can be checked after the faithfully flat finite étale extension splitting \(E_i\otimes_k R\). Nilpotent kernel matrices have determinant one by the radical filtration. Every residue matrix lifts to an invertible module map because the kernel ideal is nilpotent. Each block determinant can therefore be any unit of \(E_i\otimes_k R\), independently. This gives the exact unit equation over arbitrary \(R\)
\[
 \nu\det_R\phi\,
 \prod_i N_{E_i\otimes R/R}(p_i)^{2w_i^L}
 \prod_i N_{E_i\otimes R/R}(q_i)^{w_i^R}=1 .
 \tag{3}
\]
For \(R=k\), finite field norms are onto. Consequently the whole determinant fiber above any given \(\phi\) is the coset \((\det\phi)^{-1}(k^\times)^g\) for \(g=\gcd(|k^\times|,(2w_i^L)_i,(w_i^R)_i)\). When \(g=1\), prescribed-determinant equivalence of these cubics is therefore exactly one ordinary TI instance, namely \(b_A,b_B\).

For split residue, the norm factors in (3) are unit variables over the original base and the Euclidean algorithm combines them into a single power equation with exponent \(\gcd((2w_i^L)_i,(w_i^R)_i)\). The line-record compiler applies verbatim in this case with that exponent in place of \(n\).

The same product of norm factors reduces to a single power over any finite commutative \(k\)-algebra \(R\), including nonreduced ones. For this use that the norm of \(E\otimes_k R\) onto \(R^\times\) is surjective. Work on a local factor with maximal ideal \(\mathfrak m\). The reduced extension is a product of finite fields, so its unit norm is surjective. Each reduced unit lifts to a unit. To correct the norm on principal units, successively use
\[
 N(1+x)=1+\operatorname{Tr}(x)\pmod{\mathfrak m^{j+1}},\qquad x\in\mathfrak m^j(E\otimes_k R),\quad j\ge1.
\]
This is the degree-one term of the determinant of multiplication by \(1+x\), since \(2j\ge j+1\). The trace on each layer is onto by the surjective residue trace and freeness of the extension. Nilpotence terminates the correction. The different factors of a finite ring are independent. Thus the exact remaining arithmetic over these rings is one power equation with the same integer exponent as for split residue, including when that power is inseparable.

## Equivalence with the remaining ternary reduction

Let \(H_3\) mean that arbitrary \(\mathsf{TI}_{\mathrm{SL}}(\mathbb F_3)\) deterministically reduces in polynomial time to one ordinary \(\mathsf{TI}(\mathbb F_3)\) instance. The following restricted compilation question is equivalent to \(H_3\): given based algebras \(A,B\) in the ternary cube-zero normal form, compile the test for a determinant-one linear transporter from \(f_A\) to \(f_B\) into one ordinary TI instance over \(\mathbb F_3\).

The earlier square-zero normal form shows that the forward problem on arbitrary tensors reduces to a conjunction of at most seven signed algebra-isomorphism tests in this class. Its algebras have scalar residue and even dimension. By (1) and (2), the signed tests are exactly the determinant-one cubic tests, with a reflected target basis to implement the negative sign if needed. If the restricted compiler exists, combine these ordinary queries as one constant-size tensor system. In the converse direction, the determinant-one cubic test on these based inputs is already equivalent to determinant-one TI of the multiplication tensors. For an isotopy \(h(xy)=a(x)b(y)\), the values \(u=a(1)\) and \(v=b(1)\) are units by the two unit substitutions and surjectivity. The algebra map is \(x\mapsto u^{-1}h(x)v^{-1}\). The three original maps differ from it by left and right unit multiplication, each acting with determinant one on the radical layers over \(\mathbb F_3\) because the total dimension is even. Therefore the three determinant-one constraints hold exactly when the recovered algebra map has determinant one. Apply \(H_3\). [Ternary square-zero equivalence](https://github.com/Dugongue/MathProofs/blob/main/TISLAtlasClosure/SquareZeroClosure.md)

The explicit centroid and Frobenius criteria yield single-instance reductions on their stated domains. The equivalence above leaves the scalar-centroid family with large unconstrained determinant roles as a case for further work.
