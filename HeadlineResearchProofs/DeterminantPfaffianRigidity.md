# Every shortest even determinant partition decomposition comes from a symplectic form

Let \(n\ge4\) be even, and let \(V=K^n\) over a field \(K\). Write the determinant as a multilinear form in the \(n\) ordered columns. An admissible summand is the product of two multilinear forms on complementary nonempty sets of columns.

**Theorem.** Every shortest column partition decomposition of the determinant is the row expansion of the Pfaffian of a Gram matrix for a single nondegenerate alternating form, up to column permutation and inverse scaling of the two factors in each summand. This holds over every field, including characteristic two.

More precisely, there is a center column, number it 1, and one term for each \(j=2,\ldots,n\), with the term at \(j\) having the factorization

\[
\lambda_j\omega(v_1,v_j)\cdot
\frac{(-1)^j}{\lambda_j\operatorname{Pf}(\omega)}
\operatorname{Pf}\bigl((\omega(v_a,v_b))_{a,b\notin\{1,j\}}\bigr),
\tag{1}
\]

where \(\omega\) is alternating and nondegenerate, \(\lambda_j\in K^\times\), and \(\operatorname{Pf}(\omega)\) is computed in the standard coordinate basis of \(V\). The center is unique for \(n\ge6\). For \(n=4\) the same three unordered splits permit any center after choosing which factor to list first.

**Scheme refinement.** Fix the ordered star layout at 1, and consider the affine coefficient scheme over \(\mathbb Z\) of the pairs of factors whose sum is the determinant. This scheme is isomorphic over \(\mathbb Z\) to

\[
\left\{\omega\in \bigwedge^2(\mathbb Z^n)^*: \operatorname{Pf}(\omega)\text{ invertible}\right\}
\times(\mathbb G_m)^{n-2}.
\tag{2}
\]

The notation in (2) denotes an open subscheme of affine space. The isomorphism uses (1) with \(\lambda_2=1\), so that the first factor at \(j=2\) is exactly \(\omega\). Thus the classification works over arbitrary commutative rings for the fixed layout, including nilpotent test rings. Up to inverse rescalings there is one parameter, a projective nondegenerate alternating form.

## 1. The vanishing class forces the star layout

The exact value \(n-1\), including the Pfaffian construction, was proved in Krishnan and Moshkovitz's November 2026 manuscript. We use the cohomological obstruction in the portfolio's independent proof. The needed assertion is the following. If the determinant has a decomposition with one chosen side \(I_i\) of each split, then

\[
\prod_i\left(\sum_{a\in I_i}x_a\right)=0
\quad\text{in}\quad \mathbb Z[x_1,\ldots,x_n]/(e_1,\ldots,e_n).
\tag{3}
\]

For completeness, work over an algebraic closure of \(K\), and take the variety of ordered independent lines in \(K^n\). The map to the complete flag variety by successive spans is a tower of affine-space bundles: each line lifts the next graded line by choosing a splitting of a short exact sequence over the previously chosen lines. Accordingly pullback identifies the two Chow rings. The flag Chow ring is the coinvariant presentation in (3), with \(x_i\) the first Chern class of the dual of the \(i\)-th line. The chosen factors are sections of the corresponding direct sum of tensor line bundles. Their common zero is empty because the determinant does not vanish on independent lines. Taking the top Chern class gives (3). [Independent cohomological proof](https://github.com/Dugongue/MathProofs/blob/main/GrochowOpenProblemSolutions2/DETERMINANT-PARTITION-RANK.md).

Assign the \(n\)-th roots of unity to \(\alpha_1,\ldots,\alpha_n\) in any order. The substitution \(x_a\mapsto t\alpha_a\) in \(\mathbb C[t]/(t^n)\) respects (3), since the roots are all roots of \(z^n-1\). For \(n-1\) factors, \(t^{n-1}\ne0\). Thus for every assignment at least one \(I_i\) has zero sum. Complementation preserves the zero-sum condition. Choose a uniform assignment and let \(p_s\) denote the chance that the sum in a particular \(s\)-set is zero. The cases \(s=1,n-1\) have \(p_s=0\). For \(2\le s\le n-2\), double count the swaps joining a zero-sum \(s\)-subset of the roots to a nonzero-sum one. All \(s(n-s)\) swaps from a zero-sum subset leave the zero-sum locus. From a subset of nonzero sum \(z\), a swap back requires a pair of unit roots with difference \(z\). There are at most two such ordered pairs, as the last condition is the intersection of the unit circle with one of its nontrivial translates. Thus

\[
p_s\le\frac2{s(n-s)+2}\le\frac1{n-1}.
\]

Equality in the last bound requires \(s=2\) or \(s=n-2\). The \(n-1\) events must cover all assignments, so every probability equals \(1/(n-1)\), and the events are pairwise disjoint. Choose a pair side for each split. Its event prescribes opposite roots at the pair. The chosen edges are distinct because a repeated edge would give the same event. Two disjoint edges could both be assigned opposite pairs of roots and hence cannot occur. Pairwise intersecting edges of a simple graph either share a vertex or consist of the three edges of a triangle. Indeed two edges with common center force any third avoiding the center to connect their two endpoints, after which no other edge can intersect all three. For \(n\ge6\) there are at least five edges, so they form the entire star at the common center. For \(n=4\) the star and triangle describe the same three unordered splits by complementation. A column permutation can be accompanied by a factor sign to account for the determinant convention; we henceforth fix the star at column 1.

## 2. The factors over a field

Write a star decomposition as

\[
\det(v_1,\ldots,v_n)=\sum_{j=2}^n F_j(v_1,v_j)G_j(v_{\widehat1,\widehat j}).
\tag{4}
\]

Fix a nonzero \(u\in V\). Let \(H_j=\ker F_j(u,-)\), allowing \(H_j=V\). If choices \(v_j\in H_j\) gave a basis together with \(u\), (4) would be a contradiction. In \(W=V/Ku\) each image \(\overline H_j\) has dimension at least \(n-2\). Independent choices from these \(n-1\) subspaces exist provided their sum is all of \(W\): every proper nonempty subcollection of size at most \(n-2\) already has sum dimension at least its size, and the full collection then also satisfies the linear independent-transversal criterion.

Here is a proof of that criterion. For subspaces \(U_i\), suppose each subcollection has sum dimension at least its size. If a nonempty proper subcollection achieves equality, choose independent representatives there by induction and pass to the quotient by their span. Dimension inequalities for unions with that subcollection give those for the remaining images. If there is no such proper subcollection, choose any nonzero representative for one index and quotient by its line. All proper nonempty subcollections had a spare dimension, so induction applies. The one-subspace case is immediate.

Therefore the \(\overline H_j\) are all one common hyperplane of \(W\). This forces the \(H_j\) to be one common hyperplane of \(V\) containing \(u\), because only a hyperplane containing \(u\) has a hyperplane as its image in \(W\). In particular each functional \(F_j(u,-)\) is nonzero, vanishes at \(u\), and is proportional to \(F_2(u,-)\). It follows that each \(F_j\) is an alternating form and that \(F_2\colon V\to V^*\) is invertible. Each linear operator \(F_jF_2^{-1}\) on \(V^*\) preserves every line and thus is scalar: compare its actions on basis vectors and each sum of two distinct basis vectors. Hence \(F_j=\lambda_j\omega\), where \(\omega=F_2\) and \(\lambda_j\) is nonzero.

The Pfaffian congruence identity gives

\[
\operatorname{Pf}((\omega(v_a,v_b))_{a,b})=
\operatorname{Pf}(\omega)\det(v_1,\ldots,v_n).
\]

Together with expansion along row 1, this proves that (1) indeed gives (4). For fixed \(F_j=\lambda_j\omega\), the \(G_j\) are unique. To see this, pass to an algebraic closure if necessary, choose an independent \((n-1)\)-tuple \((v_2,\ldots,v_n)\), and compare the resulting linear functions of \(v_1\). The functions \(\omega(-,v_j)\) are independent, so each difference of complementary factors is zero on that tuple. The independent tuples are dense, so the differences are zero polynomials. The same identity descends to \(K\). The Pfaffian identities hold in characteristic two because they are polynomial identities over \(\mathbb Z\), and alternation here includes zero diagonal. This proves the field claim.

## 3. The tangent calculation

Work over an algebraically closed field \(k\), and fix any point of the coefficient scheme of (4). By base-point rescalings take all \(F_j\) there to equal \(\omega\) and write \(G_j^0\) for the complementary factors given by (1). A tangent over \(k[\epsilon]/(\epsilon^2)\) with first variations \(h_j,k_j\) satisfies the polynomial identity

\[
\sum_{j=2}^n\left(h_j(v_1,v_j)G_j^0(v_{\widehat1,\widehat j})+
\omega(v_1,v_j)k_j(v_{\widehat1,\widehat j})\right)=0.
\tag{5}
\]

For fixed nonzero \(u=v_1\), let \((v_2,\ldots,v_n)\) be a basis of \(H=\ker\omega(u,-)\). The radical of \(\omega|_H\) is the line \(ku\). Evaluate the identity (4) at this tuple while allowing its \(v_1\) variable to vary. The covector \(\det(-,v_2,\ldots,v_n)\) is nonzero with kernel \(H\), and hence is a nonzero multiple of \(\omega(-,u)\). By invertibility of \(\omega\), there is a nonzero scalar \(b\) such that

\[
\sum_{j=2}^n G_j^0(v_{\widehat1,\widehat j})v_j=bu.
\]

Let \(c_j\) be the coordinates of \(u\) in this basis. Substituting the basis and \(v_1=u\) into (5) gives \(\sum_j c_jh_j(u,v_j)=0\). To isolate \(h_j(u,u)\), take a basis with \(v_j=u\). Thus every \(h_j\) is alternating. For distinct \(i,j\) and any \(v\in H\setminus ku\), take \(v_i=v\) and \(v_j=u-v\). These are independent and extend to a basis of \(H\). The same relation, using alternation, gives

\[
(h_i-h_j)(u,v)=h_i(u,v)+h_j(u,u-v)=0.
\]

The relation is also zero for \(v\in ku\). Hence for every \(u\ne0\), \((h_i-h_j)(u,-)\) is a multiple of \(\omega(u,-)\). Applying the line-preserving argument from Section 2 to the difference gives \(h_j=h_2+a_j\omega\), with constants \(a_j\) and \(a_2=0\). These are precisely the variations of the first factors along the model (2). Subtracting the corresponding model tangent leaves only the equation \(\sum_j\omega(v_1,v_j)k_j=0\). The independent-tuple argument again shows that each \(k_j=0\). Thus every tangent vector belongs to the smooth model (2).

## 4. Descent to the integral coefficient scheme

Let \(S\) be the affine scheme over \(\mathbb Z\) whose coordinates are the coefficients of all \(F_j,G_j\), and whose equations equate the coefficients in (4). Interpret \(F_j\) as a linear map from \(V\) to \(V^*\). The field proof shows \(\det(F_2)\) is a unit in \(\mathcal O(S)\), since it vanishes at no residue field point. Define \(\lambda_j\) in \(\mathcal O(S)\) as the first diagonal entry of \(F_jF_2^{-1}\), so that each \(\lambda_j\) is a unit by the same argument. Also define \(P\) in \(\mathcal O(S)\) to be the Pfaffian of the alternating matrix with entry \(F_2(e_a,e_b)\) at \((a,b)\) for \(a<b\). This agrees with \(\operatorname{Pf}(F_2)\) where \(F_2\) is alternating, and the field proof makes \(P\) a unit on \(S\).

The formulas stating that \(F_2\) is alternating, that \(F_j=\lambda_jF_2\), and that the \(G_j\) have the coefficients of (1), with denominators \(P\lambda_j\), now cut out a closed model \(Z\subseteq S\). Formula (1) and the extraction of \(F_2,\lambda_3,\ldots,\lambda_n\) are inverse maps between \(Z\) and (2). In particular \(Z\) is smooth and flat over \(\mathbb Z\).

For every algebraically closed field \(k\), every closed point of \(S_k\) lies on \(Z_k\). At such a point the closed immersion gives a lower bound of \(\dim Z_k\) on local dimension and the tangent calculation gives that same number as an upper bound on tangent dimension. The local ring is therefore regular, hence reduced. Consequently \(S_k\) is reduced and the closed immersion is an isomorphism, since its image contains every closed point of the finite type \(k\)-scheme. Faithfully flat field extension proves the same fiber equality over each residue field of \(\mathbb Z\), including \(\mathbb Q\).

Write \(A=\mathcal O(S)\), \(B=\mathcal O(Z)\), and \(I=\ker(A\to B)\). Flatness of \(B\) over \(\mathbb Z\) makes \(I\otimes\mathbb F_p\) inject into \(A\otimes\mathbb F_p\), and equality of the fibers makes the injection zero. Thus \(I/pI=0\) for each prime \(p\). At points of \(S\) over \(p\), localization and Nakayama give \(I=0\) locally since \(I\) is finitely generated over the Noetherian ring \(A\). Over the generic point it vanishes by the rational fiber equality. This proves \(I=0\) and hence the integral isomorphism. Absent a star layout for \(n\ge6\), the set of field-valued solutions is empty, so the fixed-layout coefficient scheme is empty as well.

## 5. Exact sparsity and finite-field counts

Let \(\Omega\) be the matrix of \(\omega\), and let \(a\) and \(b\) be the numbers of nonzero strictly upper triangular entries in \(\Omega\) and \(\Omega^{-1}\), respectively. A quadratic factor in (1) has \(2a\) monomials. Its complementary factor has exactly \(b(n-2)!\) monomials. To see the latter, the Gram Pfaffian is alternating in its \(n-2\) input vectors. Its coefficient on the coordinate minor of an \((n-2)\)-set \(I\) is \(\operatorname{Pf}(\Omega_{I,I})\), as follows by evaluation on those coordinate vectors. Different coordinate minors have disjoint monomial supports. Deleting the two indices \(i,j\) gives a Pfaffian equal, up to sign, to \(\operatorname{Pf}(\Omega)(\Omega^{-1})_{ij}\). This last identity follows by differentiating \(\operatorname{Pf}(\Omega)^2=\det(\Omega)\) in the generic skew entry over \(\mathbb Q\): the derivative of the Pfaffian is the signed deleted Pfaffian, and the determinant derivative is \(2\det(\Omega)(\Omega^{-1})_{ji}\). Clearing denominators gives an integer polynomial identity, so the result applies in every characteristic.

The exact sum of the monomial counts of all \(n-1\) products, each expanded separately, is therefore

\[
(n-1)2ab(n-2)!\ \ge\ \frac n2\,n!.
\]

An invertible alternating matrix has at least one nonzero entry in each row and zero diagonal, so \(a,b\ge n/2\). Equality requires exactly one nonzero entry in every row of \(\Omega\). Such matrices are precisely the weighted coordinate-perfect-matching forms, and their inverses have the same matching support. Thus the sparsest optimal partition formulas are exactly the matching forms. This counts monomial occurrences before cancellation between different summands.

Over a finite field \(\mathbb F_q\), the number of decompositions for a fixed center, with the factors listed by their splits and modulo inverse rescaling, is

\[
\frac{|\mathrm{GL}_n(\mathbb F_q)|}{(q-1)|\mathrm{Sp}_n(\mathbb F_q)|}.
\]

Indeed, all nondegenerate alternating forms are equivalent under change of basis, with symplectic stabilizer, and scalar multiplication on the set of nonzero forms is free. The class of a form is recovered from the projective class of the quadratic factor at \(j=2\). For \(n\ge6\), varying the center multiplies this count by \(n\) because the unordered split layouts are distinct. For \(n=4\), the unordered splits are identical at every center and the three Pfaffian product terms are independent of that choice.

## Relation to existing work

Krishnan and Moshkovitz independently obtained the exact rank and exhibited the family in (1) in Theorem 4.8 of their publicly posted November 2, 2026 STOC submission. They also treat every polynomial with permutation monomial support. Their determinant result is therefore prior to the portfolio's exact-rank manuscript. The theorem here is the converse specific to the determinant and the determination of the full coefficient scheme. Lampert and Moshkovitz earlier classified all optimal **slice** decompositions and wrote an optimal partition formula for the \(4\times4\) determinant. The characteristic-class obstruction is related to the strength lower bounds of Chen and Zhao. [Krishnan–Moshkovitz, STOC paper 631](https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/631.pdf) · [Lampert–Moshkovitz](https://doi.org/10.4230/LIPIcs.ITCS.2026.90) · [Chen–Zhao](https://arxiv.org/abs/2607.21015).
