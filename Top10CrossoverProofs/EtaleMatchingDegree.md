# Algebraic proof complexity of finite-field étale tensor isomorphism

Let \(k=\mathbb F_q\) with \(q\ge3\). Let \(A,B\) be nonisomorphic commutative étale \(k\)-algebras of the same positive dimension \(n\). Use the usual cubic action equations for \(T_A,T_B\), both matrix inverse equations in all three modes, and \(x^q-x=0\) on their variables. Write \(D_{\rm TI}\) for the minimum Polynomial Calculus refutation degree of this system. [The tensor-isomorphism encoding](https://arxiv.org/abs/2305.19320).

For positive \(l\), let \(a_l,b_l\) count the degree-\(l\) field factors of \(A,B\), respectively. Write \(D_l\) for the minimum PC refutation degree of the \(a_l\) by \(b_l\) rectangular permutation system over \(k\). Its axioms are Booleanity, pairwise exclusion within each row and each column, and all row and column sums equal to \(1\). If exactly one side is empty this system includes \(1=0\) and has degree \(0\). Equal-size systems have no refutation and carry degree \(\infty\). Put \(D=\min_l D_l\). Then

\[
\boxed{\quad \max(q+1,D)\ \le D_{\rm TI}\ \le\ \max(q+1,2D).\quad}
\]

In particular, for fixed \(q\) this identifies the full PC degree problem for étale multiplication tensors, up to a factor of two, with the corresponding modular bijective pigeonhole problems. The statement applies to the original cubic tensor presentation, with arbitrary coordinates and no commutative-algebra-isomorphism axioms added.

## Coordinates and proof rules

After scalar extension to a finite splitting field \(K\), use the primitive idempotent basis in each algebra. In these bases both multiplication tensors are the diagonal tensor. The field equations for each forward or inverse matrix \(M\) become the coordinate equations \(m^q-m'=0\), where \(m'\) is obtained by simultaneously cycling the row and column indices by the respective Frobenius permutations. To see that these are allowable axioms in the changed coordinates, write the change of coordinates on a forward matrix as \(P_B^{-1}M_0P_A\), where \(P_A,P_B\) are the idempotent bases in the original coordinates. Frobenius permutes the columns of each \(P\). The asserted equations are invertible linear combinations of the original field equations after change of variables. For an inverse matrix the same rule applies with source and target exchanged.

Linear changes and scalar extension in this argument preserve minimum proof degree. A variable multiplication can be replayed as multiplication by a linear form using individual variable multiplications and a linear combination of their results. For scalar descent, expand each line in a field basis of \(K/k\) containing \(1\), and replay the coefficient derivations. In particular these rules apply to degree measured on lines of the proof.

## Lower bound by rectangular permutation systems

For each \(l\) introduce one Boolean variable for each pair consisting of a source cycle and a target cycle of length \(l\). Fix an origin in every cycle. Set the three forward action matrices equal to the matrix \(P\) with this variable at every pair of equally offset positions from these two origins, and zero elsewhere. Set the three inverses equal to \(P^{\mathsf T}\).

In this substitution each entry is invariant under simultaneous Frobenius shifting of its two indices. Hence each twisted field equation becomes \(z^q-z\) or zero, derivable from Booleanity in degree \(q\). The product \(P^{\mathsf T}P\) or \(PP^{\mathsf T}\) gives either a degree-two row or column exclusion, or a sum of squares of one line. Booleanity and its line sum give every inverse equation at degree two. A cubic diagonal action entry is either a sum of cube powers along a line, reducing to \(1\), or a sum of cubic terms each containing a product excluded by a column. Thus those equations have degree-three derivations. Every TI proof maps to a proof over the union of the rectangular permutation systems with no degree increase as soon as its degree is at least \(q+1\).

For completeness the refutation degree of a disjoint union is the minimum of the degrees of its factors. Fix a trial bound \(d\) and let \(V_i\) be the space of polynomials in block \(i\) of degree at most \(d\). Let \(W_i\subseteq V_i\) be the space of lines derivable from the \(i\)-th block in degree at most \(d\). Give both spaces the induced degree filtration. If no block derives \(1\), each quotient \(V_i/W_i\) has nonzero constant class. Map the full polynomial space of total degree at most \(d\) into the tensor product of these quotients. Choose a filtration-adapted basis of \(W_i\), and extend it to one of \(V_i\). This shows that every kernel element of total degree at most \(d-1\) is a sum of elementary tensors of total degree at most \(d-1\) with at least one factor in a \(W_i\). When multiplying such a tensor by a variable in its \(W_i\) block that factor stays in \(W_i\) by the PC multiplication rule. When multiplying in a different block a \(W_i\)-factor is unchanged. All axioms are in the kernel, which is thus closed under all degree-\(d\) proof rules. It does not contain \(1\). A proof of one contradictory block also proves the union, giving the minimum formula.

The lower bound \(D_{\rm TI}\ge q+1\) is the exposed-weight argument for general pairs of commutative étale algebras. Briefly, evaluate the equations on each geometric isomorphism family given by a common permutation of the diagonal coordinates and independent scalings \(u_i,v_i,(u_iv_i)^{-1}\). The six matrix types have six distinct exposed Laurent weights per position, namely \((1,0),(0,1),(-1,-1),(-1,0),(0,-1),(1,1)\). The \(q\)-fold multiple of any such weight cannot occur in a polynomial of degree below \(q\). In each original matrix, as the position and the permutation vary, the leading coefficients of its entrywise \(q\)-th powers pair against all combinations of two Frobenius-powered bases. Therefore a linear combination of the field equations can cancel into degree below \(q\) modulo polynomials vanishing on all the families only when all its coefficients are zero. Induction through a putative degree-\(q\) proof then keeps each line in the sum of the vanishing space and the constant linear span of the field equations. A multiplication step can use only a lower-degree line, where that field-equation contribution has already vanished. The constant \(1\) cannot occur. [Complete exposed-weight argument](https://github.com/Dugongue/MathProofs/blob/main/OneillCrossovers/QuadraticTensorCertificates.md).

## Upper bound by deriving the matching equations inside the tensor system

Use a forward matrix \(X\) in one mode and its inverse \(R\). Index \(R_{ia}\) by a source idempotent \(i\) and a target idempotent \(a\). In the cubic action equations, contract the output of the chosen mode against row \(i\) of \(R\). Using \(RX=I\) gives \(\operatorname{diag}(R_{i\bullet})=Y_{\bullet i} Z_{\bullet i}^{\mathsf T}\) in degree four. Substitution in its two-by-two minors proves \(R_{ia}R_{ib}=0\) for \(a\ne b\) in degree four.

Multiplying \((RX)_{ij}=\delta_{ij}\) by \(R_{ia}\) and using row exclusion gives
\[
R_{ia}^2 X_{aj}=\delta_{ij}R_{ia}.
\]
If \(j\ne i\), multiply this equation by \(X_{ai}\), multiply its diagonal counterpart by \(X_{aj}\), and subtract. We obtain \(R_{ia}X_{aj}=0\) in degree four. Multiplying \(R_{ja}^2 X_{aj}=R_{ja}\) by \(R_{ia}\) now gives \(R_{ia}R_{ja}=0\) in degree four. Thus both row and column exclusion hold for \(R\).

For source and target indices whose Frobenius periods differ, their orbit under simultaneous shifting contains two distinct positions sharing a row or column: advance by the smaller period. The product of the two entries is zero by the exclusions. The field equation \(u^q=u'\) allows either factor of a zero product to advance one step, in degree \(q+1\). Indeed \(uv=0\) implies \(u^qv=0\) by repeated multiplication, then \(u'v=0\). Advance until the two positions coincide to obtain \(w^2=0\). This implies \(w^q=0\) since \(q\ge3\), and the field equations then eliminate every entry in that shift orbit. All entries between cycles of different lengths vanish at degree at most \(q+1\).

Define \(E_{ia}=R_{ia}X_{ai}\). The equations already derived give \(E_{ia}^2=E_{ia}\) and row and column exclusions for \(E\) in degree four. Both families of line sums equal \(1\) by the diagonal entries of \(RX\) and \(XR\).

We next derive shift invariance without multiplying two degree-\(q\) terms. On a simultaneous shift orbit write \(r_t=R_{i_ta_t}\), \(x_t=X_{a_ti_t}\) and \(E_t=r_tx_t\). Multiplying \(r_t^2x_t=r_t\) by \(r_t^{q-2}\) and substituting \(r_t^q=r_{t+1}\) gives \(r_{t+1}x_t=r_t^{q-1}\) in degree \(q+1\). Multiply the reduced equation by \(r_t\) and substitute again to get \(r_{t+1}E_t=r_{t+1}\). Multiplying by \(x_{t+1}\) gives \(E_{t+1}E_t=E_{t+1}\).

These relations propagate around the orbit in degree five. In detail, from \(r_{j}E_i=r_j\), \(r_{j+1}E_j=r_{j+1}\) and \(E_jE_i=E_j\), compare the last two equations after multiplication by \(E_i\) and \(r_{j+1}\), respectively. The difference gives \(r_{j+1}E_i=r_{j+1}\), and multiplication by \(x_{j+1}\) gives \(E_{j+1}E_i=E_{j+1}\). Each multiplication by \(E_i\) uses two individual variable multiplications. Going around the finite orbit gives both \(E_iE_j=E_i\) and \(E_iE_j=E_j\). Thus the indicators are simultaneously shift invariant in degree at most \(\max(q+1,5)\).

When \(q=3\) we can get the equality in degree four directly. Multiply \((XR)_{aa}=1\) by \(X_{ai}\). The already derived products \(R_{ja}X_{ai}=0\) for \(j\ne i\) leave \(X_{ai}^2R_{ia}=X_{ai}\). The same field substitution used above therefore gives \(x_{t+1}r_t=x_t^2\), as well as \(r_{t+1}x_t=r_t^2\). Substituting these two quadratic identities into
\[
E_{t+1}E_t=(r_{t+1}x_t)(x_{t+1}r_t)
\]
gives \(E_{t+1}E_t=r_t^2x_t^2=E_t\) in degree four. The already proved one-way identity gives \(E_{t+1}E_t=E_{t+1}\). Thus in every field under consideration \(E_{t+1}=E_t\) has a degree-\((q+1)\) derivation.

Fix a length \(l\). For source cycle \(I\) choose a representative \(i\), and for target cycle \(J\) set
\[
z_{IJ}=\sum_{a\in J}E_{ia}.
\]
Row Booleanity, row exclusion and row sums for \(z\) follow from the corresponding row identities for \(E\), since the other lengths have vanished. Simultaneous shift invariance also gives
\[
z_{IJ}=\sum_{i'\in I} E_{i'a_0}
\]
for any fixed target representative \(a_0\in J\): rotating each summand to \(a_0\) visits all positions of \(I\) once. This gives the column exclusions and column sums. The shifts are linear combinations of the already derived quadratic identities, and any further multiplication in deriving these axioms is by a quadratic sum. Thus the matching axioms under \(z\mapsto \sum E_{ia}\) are derivable in degree at most \(q+1\). Replay a degree-\(D_l\) proof of this system by that degree-two substitution, multiplying by a sum of quadratic monomials one monomial at a time. The resulting degree is at most \(\max(q+1,2D_l)\). Minimizing proves the upper bound.

In particular, if any cycle-count difference is nonzero in \(k\), the row and column sums of that board give \(D\le1\). The exact tensor degree is then \(q+1\) even when both algebras are nonsplit, including when \(l\) is a multiple of the characteristic.

More generally, write \(q=p^e\) and choose any length \(l\) with \(a_l\ne b_l\). In a board, expand the product of the line sums for each set of \(d\) distinct rows and use pairwise exclusions to remove nonmatchings. This uses degree at most \(d\). Sum over the row sets and repeat on columns. Both expansions count exactly the same partial matchings, once each, so the difference of the constants is \(\binom{a_l}{d}-\binom{b_l}{d}\). For \(d=p^{v_p(a_l-b_l)}\) it is nonzero in \(k\) by Lucas's theorem. Alternatively, select \(\min(a_l,b_l)+1\) lines on the larger side. Their single expansion has no matching terms. Thus
\[
D_l\le \min\bigl\{p^{v_p(a_l-b_l)},\,\min(a_l,b_l)+1\bigr\}.
\]
In particular any cycle-count difference nonzero modulo \(q\) implies \(D_{\rm TI}=q+1\). The matching-count proof of the board bound is the standard modular pigeonhole argument. [Razborov's survey, Theorem 8](https://www.mathnet.ru/eng/present152).

## An explicit family and a Nullstellensatz lower bound

For integers \(s>r\ge1\), take \(A=k^{2s}\times(\mathbb F_{q^2})^r\) and \(B=k^{2r}\times(\mathbb F_{q^2})^s\). Both dimensions equal \(2(r+s)\). The lower-bound substitution can use just the single \(s\)-by-\(r\) board: use its variables in two disjoint copies for the degree-one factors and the transposed board on the degree-two factors, with offsets aligned. The upper bound still follows from the degree-two-factor board. This transfers the full modular bijective pigeonhole degree problem even to étale algebras with just two residue degrees.

Over a fixed field of characteristic two, take \(r=(4^h-2^h)/2\) and \(s=r+2^h\). Beame and Riis give a matching design of order \(2^h-1\) for this board in Theorem 8.1. The same design works over the given field by scalar extension from \(\mathbb F_2\). The monomial functional induced by the design annihilates every axiom times a monomial multiplier below that order. Under the linear substitution above, the image of each original tensor axiom is a combination of board axioms with total degree no greater than the original axiom's stated degree. Therefore a Nullstellensatz identity transfers with the same total-degree bound. It follows that the finite-field tensor systems in this family have Nullstellensatz degree \(\Omega(\sqrt n)\), where \(n=2(r+s)\), even though their two multiplication tensors are geometrically isomorphic and the field factor degrees are at most two. This consequence uses the published Nullstellensatz theorem. The analogous Polynomial Calculus lower bound requires a Polynomial Calculus bound for the board. [Beame–Riis, Theorem 8.1](https://homes.cs.washington.edu/~beame/papers/riis.pdf).
