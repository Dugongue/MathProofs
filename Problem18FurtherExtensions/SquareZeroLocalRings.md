# Orthogonal tensor isomorphism over square-zero local rings of residue characteristic two

Let \(R\) be a finite commutative local ring with maximal ideal \(\mathfrak m\), residue field \(k\) of characteristic two, and \(\mathfrak m^2=0\). Give \(R\) by additive cyclic coordinates and multiplication structure constants. The ring has characteristic two or four. Examples include the Galois rings \(\operatorname{GR}(4,f)\) and the nonprincipal rings \((\mathbb Z/4)[t_1,\ldots,t_e]/(2t_i,t_it_j:1\le i,j\le e)\).

**Theorem.** For dense three-tensors over \(R\) with ordered mode dimensions \(2\le a\le b\le c\), there is a recognizable, orthogonally invariant source domain of density at least \(1-C(1+\log b)/\sqrt b\), with an absolute \(C\) for sufficiently large \(b\). Against each source in this domain and every second tensor, there is a uniform deterministic polynomial-bit-time algorithm for orthogonal orbit decision, an exact count of all three-factor transporters, and a transporter on yes-instances. The coefficient-ring presentation contributes to the input length. The mode actions preserve the standard bilinear dot product \(x^Ty\).

The proof below also gives a deterministic polynomial-time algorithm for the following problem without a tensor density hypothesis. Given arbitrary same-sized matrices \(H,D\) over \(R\), decide, count, and construct solutions of \(Q^TQ=I,\ QH=D\). In particular, the columns may generate a nonfree submodule.

## 1. The residue of the bilinear orthogonal group

Write \(n\) for the row dimension, \(h=(1,\ldots,1)^T\) over \(k\), \(\ell(x)=h^Tx\), and
\[
P(x)=\sum_{i<j}x_i x_j,\qquad B_P(x,y)=x^Ty+\ell(x)\ell(y).
\]
Every residue dot-product isometry fixes \(\ell\) since \(x^T x=\ell(x)^2\) and Frobenius is injective. It fixes \(h\) by nondegeneracy of the dot product. The group of residue dot-product isometries is therefore the group preserving \(B_P\) and fixing \(h\) when \(n\) is even: then \(B_P(h,x)=\ell(x)\), so those two conditions recover the dot product. When \(n\) is odd, the group is the identity on \(kh\) times the symplectic group on \(h^\perp\), where \(B_P\) restricts to the nonsingular alternating dot product.

The value \(N(x)=\tilde x^T\tilde x\) of a residue vector is independent of its lift to \(R^n\), because \(\mathfrak m^2=0\) and \(2\mathfrak m=0\). If \(R\) has characteristic two, \(N\) is preserved by every residue isometry: it is the square in \(R\) of any lift of \(\ell(x)\). If \(R\) has characteristic four, the map \(k\to 2R\), \(u\mapsto 2\tilde u\), is injective, because every element outside \(\mathfrak m\) is a unit. The identity
\[
\tilde x^T\tilde x=\left(\sum_i\tilde x_i\right)^2-2\sum_{i<j}\tilde x_i\tilde x_j
\]
therefore shows that a residue dot-product isometry preserves \(N\) exactly when it preserves \(P\). For even \(n\) the allowed group in characteristic four is the orthogonal group of the nonsingular quadratic form \(P\) with \(h\) fixed. For odd \(n\) it is the identity on \(kh\) times the orthogonal group of \(P|_{h^\perp}\). Indeed \(kh\) is the radical of \(B_P\) then, so \(P\) splits additively along \(kh\oplus h^\perp\). For even \(n\) the matrix of \(B_P\) is invertible since \((I+hh^T)^2=I\).

## 2. Exact extension for arbitrary prescribed columns

Apply invertible column operations to both matrices. Use unit-pivot elimination on \(H\), allowing auxiliary invertible row operations to find the pivots; return to the original row coordinates. This produces a list of columns \(u_1,\ldots,u_r\) with linearly independent residues followed by columns in \(\mathfrak m^n\). Their paired columns in \(D\) are \(v_1,\ldots,v_r\) and a tail. Reject if the target tail lies outside \(\mathfrak m^n\), or any exact pairings \(u_i^Tu_j=v_i^Tv_j\) fail.

The ideal \(\mathfrak m\) is a \(k\)-vector space, with scalar action through any lift. Let \(d=\dim_k\mathfrak m\). In a \(k\)-basis of \(\mathfrak m\), each tail column specifies \(d\) residue vectors and each target tail column specifies their images. Combine these prescriptions with \(\bar u_i\mapsto\bar v_i\) and \(h\mapsto h\). The induced residue map must be well-defined, injective, and preserve the dot product on the marked span. In characteristic four it must preserve \(P\) there as well. All checks use Gaussian elimination and values and polar pairings on a basis. For even \(n\) Witt extension in the nonsingular symplectic or quadratic space applies directly to this augmented span. For odd \(n\) project along \(h\) to \(h^\perp\), where Witt extension applies to the induced map. The projection agrees with the marked prescription since it preserves \(\ell\) and fixes \(h\).

For any allowed residual extension \(Q_0\), choose an arbitrary matrix lift \(A\). It is invertible. Write
\[
E=A^TA-I,\qquad w_i=A^{-1}v_i-u_i.
\]
The entries of \(E\) and of \(w_i\) are in \(\mathfrak m\), and the diagonal of \(E\) is zero because \(Q_0\) preserves \(N\). The tail equations already hold for \(A\), since \(A\) acts on the tail through \(Q_0\). The same is true for every \(A(I+Z)\) with \(Z\in M_n(\mathfrak m)\). The remaining equations on \(Z\) are exactly
\[
Z+Z^T=-E,\qquad Z\bar u_i=w_i.
\]
View \(x^TZy\) as a \(k\)-bilinear form valued in \(\mathfrak m\), and extend \(\bar u_1,\ldots,\bar u_r\) to a \(k\)-basis. The equations prescribe its first \(r\) columns in this basis. Its first \(r\) rows follow from the transpose equation. On their intersection the prescriptions agree, because
\[
v_i^Tv_j-u_i^Tu_j
 =\bar u_i^T E\bar u_j+w_i^T\bar u_j+\bar u_i^T w_j=0.
\]
On the remaining square block the transpose equation has zero diagonal and can always be solved. The difference of two corrections is an arbitrary symmetric \(\mathfrak m\)-valued form on the \(n-r\) complementary coordinates. Each admissible residue thus has exactly
\[
|k|^{d(n-r)(n-r+1)/2}
\]
lifts, and a lift can be constructed by linear equations. This proves necessity and sufficiency of all checks, even when the source column module has arbitrary torsion.

All coordinate operations are effective in the stated input model. In characteristic four, \(\mathfrak m=\ker(x\mapsto 2x)\); in characteristic two, \(\mathfrak m=\ker(x\mapsto x^2)\) by the local and square-zero assumptions. The latter map is linear over \(\mathbb F_2\). Compute the residue field and its action on the ideal in additive coordinates. A \(k\)-basis of the ideal can be found by testing linear dependence over \(\mathbb F_2\) after multiplying each candidate by a field basis. Finite-field inversion uses multiplication matrices over \(\mathbb F_2\), and finite-field square roots are obtained by inverse Frobenius. Ring unit inversion is a linear congruence solve in the additive coordinates.

## 3. Counting and constructing the residual extensions

It suffices to work in the nonsingular symplectic or quadratic space from Section 1. Suppose an injective, form-preserving partial map is prescribed. In the even-dimensional case the marking of \(h\) is already part of the subspace. The extensions form a coset of the source pointwise stabilizer. Extend a basis of the marked span to a basis \(x_1,\ldots,x_s\) of the ambient space. At step \(j\) compute the orbit size of \(x_j\) under the pointwise stabilizer of \(x_1,\ldots,x_{j-1}\). By Witt extension the orbit consists exactly of the \(y\) outside \(S=\operatorname{span}(x_1,\ldots,x_{j-1})\) satisfying
\[
B(x_i,y)=B(x_i,x_j)\quad (i<j),\qquad P(y)=P(x_j)
\]
where the last equality is imposed in the quadratic case. Orbit-stabilizer gives the extension count by multiplying the orbit sizes: the final pointwise stabilizer is trivial. For search use the same equations with \(x_i\) on the left of each pairing replaced by the chosen images. Every admissible \(y\) extends the partial map.

In the symplectic case these are affine linear problems with a subspace excluded. For the quadratic case, let \(a+U\) be any affine solution set of the pairing equations. Split \(U=W\oplus J\) into a nonsingular part and the polar radical by symplectic elimination. Complete the square on \(W\) using its nonsingular polar form. The quadratic equation becomes a norm equation on \(W\) whose target is an affine \(\mathbb F_2\)-linear function of the \(J\)-coordinate. For \(W=0\) solve the resulting linear equation directly. Otherwise, if \(q=|k|\) and \(\dim W=2t\), the number of vectors of norm \(v\) is
\[
q^{2t-1}+\epsilon q^{t-1}
\begin{cases}
q-1,&v=0,\\
-1,&v\ne0.
\end{cases}
\]
To see this, decompose \(W\) into symplectic planes with equations \(a_i x^2+xy+b_i y^2\). For each nontrivial additive character \(\chi(ux)=(-1)^{\operatorname{Tr}_{k/\mathbb F_2}(ux)}\) the character sum of a plane is \(q(-1)^{\operatorname{Tr}(a_i b_i)}\): sum over \(y\) first and use \(\operatorname{Tr}(b y^2)=\operatorname{Tr}(\sqrt b\,y)\), normalizing the coefficient of \(xy\) to one. The product over the planes followed by character orthogonality gives the formula, with \(\epsilon=(-1)^{\operatorname{Tr}(\sum_i a_i b_i)}\). Count the radical coordinates for which the target is zero by \(\mathbb F_2\)-linear algebra, and use the displayed formula on the zero and nonzero targets. Count once on \(a+U\) and once on its intersection with \(S\), then subtract.

For deterministic construction it remains to satisfy the quadratic equation outside \(S\). Try each functional in a basis of the annihilator of \(S\), asking for a point with its value nonzero. If its value is constant over the affine solution set of the pairing equations, the zero case fails, and the nonzero case is an unconstrained affine norm equation. To solve such an equation use the preceding split. When the nonsingular part is nonzero, it represents every \(k\)-value by scaling one vector of nonzero norm, since all field elements have square roots. A nonzero-norm vector is found among basis elements and their pairwise sums. When the nonsingular part is zero use \(\mathbb F_2\)-linear algebra.

For a nonconstant functional, use its value \(t\) as one affine coordinate and choose its coordinate line \(a+t e\). Decompose the linear kernel of that functional in the affine solution space as \(W\oplus J\) as before. If \(W\ne0\), fix \(t=1\) and any radical coordinate, then solve on \(W\). If \(W=0\), write the equation for \(z\in J\) as
\[
L(z)^2+\ell_0(z)+t\ell_1(z)=c(t),\qquad t\ne0
\]
with \(k\)-linear forms \(L,\ell_0,\ell_1\) and \(c\) of degree at most two. If the image of \(\ell_0+t\ell_1\) in the dual modulo \(kL\) is not identically zero, at most one \(t\) is exceptional. For \(q>2\) try two distinct nonzero \(t\) to find a nonexceptional one, then solve on \(\ker L\). For \(q=2\) solve at the sole nonzero \(t\) by \(\mathbb F_2\)-linear algebra. If both forms are in \(kL\), the case \(L=0\) is a scalar quadratic equation in \(t\) and a nonzero root can be found by the same linear algebra. When \(L\ne0\), reduce to the plane conic \(s^2+(\alpha+\beta t)s=c(t)\), in coordinates \(s=L(z)\) and \(t\). A degenerate polar form gives an affine \(\mathbb F_2\)-linear equation, where exclusion of \(t=0\) is a subspace test. In the nonsingular case translate the conic into a homogeneous norm level. The zero level is either one point or two isotropic lines, which are found by solving a scalar quadratic equation for their slopes. For a nonzero level find one point by scaling a vector of nonzero norm. If that point has \(t=0\), consider lines through it. At most four directions are excluded: the tangent, at most two isotropic directions, and the direction along \(t=0\). In every other direction \(d\), the second intersection is obtained by solving the linear equation for the nonzero distance parameter after factoring out the known root. Trying five directions suffices for \(q\ge4\), and \(q=2\) requires only direct constant-size checking. This constructs every requested extension in deterministic polynomial time.

## 4. Transfer of the Lean-checked finite-field density

Use the two Gram-derived matrix lists in the high-median branch of Problem 1.8. With tensor axes ordered \(a,c,b\), let \(A_i\) be the \(a\times c\) slices in mode \(b\) and \(F\) the \(c\)-flattening. Use the partial-trace Gram list
\[
(R_t)_{ij}=\sum_{u,v,w}((FF^T)^t)_{wv} A_{uvi}A_{uwj}\qquad(0\le t<c).
\]
Use \(Z_{ij}=A_iA_j^T\) for the second list. The domain tests that both lists generate the full matrix algebras after reduction to \(k\). The ring identities giving covariance of the first list under orthogonal action and invertible mixing of the labels of the second are exact over \(R\). Reduction of a uniform tensor is uniform. Thus the simultaneous generation test inherits the density theorem in the [Problem 1.8 Lean development](https://github.com/Dugongue/MathProofs/tree/main/Problem18). The matrix words whose reductions give a basis are already a basis over \(R\), since their change-of-basis determinant is a unit.

Solve the ordered intertwining equations \(X R_t(A)=R_t(B)X\) over \(R\). Additive cyclic coordinates allow linear congruence solving and generating the solution module as an additive group. There is an invertible solution if and only if some additive generator has nonzero reduction. Indeed the kernel of a residue intertwiner is invariant under the full source algebra. Any two invertible solutions differ by a unit scalar, by the centralizer of the full matrix algebra. Adjoints and self-adjointness give \(X^TX=d_bI\), as \(X^TX\) commutes with the full algebra. Undo \(X\) in the \(b\)-mode of \(B\), call the resulting slices \(Y_i\), and similarly solve \(P_0 Z_{ij}(A)=d_bY_iY_j^T P_0\). This gives \(P_0^TP_0=d_a I\), since transposition interchanges the two ordered labels. If a transporter exists its last factor equals \(\beta X\), and \(d_bY_iY_j^T=PZ_{ij}(A)P^T\) for its first factor \(P\). Therefore its first factor equals \(\alpha P_0\).

The scalar requirements are \(\alpha^2=d_a^{-1}\) and \(\beta^2=d_b^{-1}\). Taking the unique residue square root and squaring any lift gives the only possible squared value over \(R\). Thus each test either rejects or gives exactly \(|\mathfrak m|\) roots by choosing any additive ideal translation of the fixed lift. For one choice of roots put \(\lambda=\alpha\beta\). Let \(H\) be the \(c\)-flattening of \((P_0,I,X)A\) and \(D\) that of \(B\). Apply Sections 1–3 to \(QH=\lambda^{-1}D\). Other choices of roots produce equally many middle solutions by rescaling \(Q\) by the ratio of the two products, which squares to one. Multiply the count by \(|\mathfrak m|^2\). This yields the exact orbit decision, construction, and transporter count.

## 5. Finite products of these rings

The frame theorem also holds over any finite commutative ring \(R\) whose Jacobson radical \(J\) satisfies \(J^2=0\) and whose residue fields have characteristic two. The ring has characteristic two or four because \(2\in J\). The radical can be computed without factoring a characteristic or listing elements. Take the inverse image in \(R\) of the kernel of Frobenius on \(R/2R\). In fact \(x^2\in2R\) implies \(x^4=0\), so \(x\in J\), and \(x\in J\) implies \(x^2=0\). Frobenius on the characteristic-two additive quotient is \(\mathbb F_2\)-linear.

Find a basis of the idempotent subalgebra of \(R/J\) by solving \(x^2=x\) over \(\mathbb F_2\). In the product of \(s\) finite residue fields this subalgebra is \(\mathbb F_2^s\). Its basis separates all the factors, so successive refinements by each basis idempotent and its complement extract the primitive idempotents in polynomial time. Lift a primitive idempotent with arbitrary representative \(a\) by replacing it with
\[
a+(1-2a)(a^2-a).
\]
Expanding and using \(J^2=0\) shows this is an idempotent. The lift is unique because \(2e-1\) is a unit for any idempotent \(e\). Products of distinct lifted idempotents and their sum therefore give zero and one, respectively. They present \(R\) as the product of the local factors required by the theorem, with explicit coordinate maps. Solve and count the frame problem in each factor, then combine witnesses and multiply counts. The same componentwise construction recognizes tensors whenever each residue factor passes the two generation tests. For a uniform tensor the residue factors are independent. Its domain therefore has density at least \((1-C(1+\log b)/\sqrt b)^s\) whenever the parenthesized bound is positive. No bound independent of the number of factors is asserted.

## Attribution and scope

The residue characteristic-four quadratic refinement and its characteristic vector have direct precedents in [Wood, Witt's extension theorem for mod four valued quadratic forms](https://www.maths.ed.ac.uk/~v1ranick/papers/woodj.pdf) and [López-Díaz and Rúa, Witt's theorems for Galois Ring valued quadratic forms](https://doi.org/10.1016/j.jpaa.2008.03.028), especially their Proposition 3. The new argument uses these ideas on all square-zero local rings in residue characteristic two and couples the arbitrary torsion-column lift and its uniform count to the Problem 1.8 recognition theorem. [Grochow, Qiao, Stange and Sun](https://arxiv.org/abs/2611.00735) study the general linear tensor-isomorphism problem over commutative rings. The theorem here concerns orthogonal actions on the stated recognizable domain. The tensor density input is Lean-checked, and the new ring extension and algorithm are informal proofs.
