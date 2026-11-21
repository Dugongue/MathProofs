# Exponential Laurent complexity for two-step nilpotent Lie laws

Fix a field \(k\), \(R=k[[t]]\), and \(K=k((t))\). A same-parameter Laurent witness between Lie laws is an integral bracket arc, with the given special bracket, whose generic bracket is isomorphic to the given source over \(K\). The polynomial image degree is the greatest degree of its bracket coefficients in the original coordinates. The symmetric pole depth of a matrix \(P\) is the greatest pole order among entries of \(P\) and \(P^{-1}\), with zero as a lower bound.

**Theorem.** In every characteristic there are explicit two-step nilpotent Lie laws \(L_m^+,L_m^-\) of dimension \(M=O(m)\), with \(O(M)\) nonzero coefficients in \(\{1,-1\}\), with these properties.

1. A line \(L_m^-+cE_m\), supported on a bounded number of bracket coefficients, lies in the geometric orbit of \(L_m^+\) for \(c\ne0\). Over any field containing \(k\), for \(c\ne0\) it is in the actual orbit exactly when \(c\) is a \(2^{m-1}\)-st power. In particular the degree-one line with \(c=t\) lifts over \(k((t^{1/e}))\) exactly when \(2^{m-1}\mid e\).
2. Every polynomial image arc with a same-parameter Laurent witness over \(K\) has degree at least \(2^{m-1}/O(M^7)\). A polynomial image arc of degree \(2^{m-1}\) is realized by a monomial Laurent witness.
3. The least symmetric pole depth is \(\Theta(2^m)\), even with arbitrary changes of basis on the full Lie algebra.

The construction uses an alternating commutator bracket and an intrinsic adjoint algebra. This permits the earlier contact-lattice construction for relative tensor degenerations to be read from two-step nilpotent Lie laws. The lower bounds concern a specified source Lie law and a specified Laurent uniformizer.

## 1. The sparse source algebra and the Heisenberg bracket

Use the thin Peirce multiplication table on the terminally capped, subdivided telescope from [the contact proof](ContactSeed.md) and [the sparse seed](SparseSeed.md). Its old vertices are totally ordered, its arrow corners are one-dimensional, and the order agrees with directed reachability by added successor arrows. The degree-one arrows multiply only on flag faces \((i,j,\ell)\) as \(p_{ij}p_{j\ell}=p_{i\ell}\), of degree two. Both algebras are associative and unital. Write \(A_c\) for the table with coefficient \(c\) on one chosen flag in the terminal cap, all other face coefficients \(1\), and the same structural zeros. The punctured complex has first homology \(\mathbb Z[C_1]\), and the marked oriented boundary equals \(\pm 2^{m-1}[C_1]\). The erased coefficient is \(c=0\). An alternative flag produces its endpoint edge, so the same based spaces describe the strict ideal \(J\), its square and its cube for every \(c\).

To distinguish orientations, append one new vertex *before* the old ordered list, with a two-dimensional arrow corner to the first old vertex and no other new strict corner. All products of strict arrows involving this corner vanish. The new reachability order is again total, and exactly its first successive corner has dimension two. All old strict corners are still thin. This marker works also after matrix amplification: multiplying corner dimensions by a constant does not change which one is doubled. It has no effect on the face cocycles. Keep the notation \(A_c\) for the marked algebra, and set \(B_c=M_2(A_c)\). Its multiplication contains no nonzero new structure constants outside locally fixed copies of the table of \(A_c\).

For any unital associative \(B\) define a Lie algebra on \(B_X\oplus B_Y\oplus B_Z\) by
\[
[(x,y,z),(u,v,w)]=(0,0,xv-uy).
\]
It is alternating in all characteristics and satisfies the Jacobi identity since its image is central. Its center and its derived space both equal \(B_Z\): the unit gives surjectivity and, by testing inputs with a unit in just one coordinate, the induced alternating bimap on \(B_X\oplus B_Y\) has zero radical. Take \(L_m^+\) and \(L_m^-\) to be the brackets from \(B_1,B_0\). Its middle laws from \(B_c\) are linear in \(c\). The sparse table grows by only constant factors, because the matrix size is fixed at two. In particular \(\dim L_m^\pm=12\dim A_c\).

## 2. Recovering an associative algebra from the bracket

For an alternating bimap \(\omega:V\times V\to Z\), define its adjoint algebra by
\[
\operatorname{Adj}(\omega)=\{(P,Q)\in\operatorname{End}(V)^2:
          \omega(Px,y)=\omega(x,Qy)\ \text{for all }x,y\}.
\]
The product is \((P,Q)(P',Q')=(PP',Q'Q)\). An isomorphism of bimaps induces an isomorphism of these algebras by conjugating both operators on \(V\). This adjoint construction is standard in the isomorphism theory of alternating bilinear maps. [Wilson, *Decomposing p-groups via Jordan algebras*](https://www.math.colostate.edu/~jwilson/papers/Central.pdf)

For the alternating bimap of \(B_X\oplus B_Y\), write the four blocks of \(P\) as \(p,q,r,s\) in row order. Comparing each of the four pairs of input slots in the adjoint identity and evaluating at the unit gives
\[
p(x)=xa,\quad s(y)=by,\quad q(y)=cy,\quad r(x)=xd,\qquad
c[B,B]=0=[B,B]d .
\]
For example the \(X,Y\) slots give \(p(x)v=xs'(v)\), so \(p\) is right multiplication by \(a=p(1)\) and \(s'\) is left multiplication by \(a\). The \(Y,X\) slots give left multiplication by \(b\) and its adjoint right multiplication by \(b\). The \(Y,Y\) slots give \(q(y)v=-(q'v)y\), forcing \(q(y)=cy,\ q'(v)=-cv\) and \(c(yv-vy)=0\). The \(X,X\) slots give \(r(x)=xd,\ r'(u)=-ud\) and \((ux-xu)d=0\). The bimap is radical-free, so \(Q\) is uniquely determined by \(P\). In \(B=M_2(A_c)\), the commutator \([E_{12},E_{21}]=E_{11}-E_{22}\) is invertible, also in characteristic two. Thus \(c\) and \(d\) in the block formulas vanish. Composition of the remaining right and left multiplications proves
\[
\operatorname{Adj}(\omega_{B_c})\ \simeq\ B_c^{\mathrm{op}}\times B_c .
\tag{1}
\]

For an arbitrary integral Lie arc from the indicated source, first take the derived space as the image of the bracket. Its rank agrees generically and specially. A minor of full rank modulo \(t\) makes this image a free direct summand with the required special fiber: after a unit-pivot elimination the residual block vanishes by generic rank. Its brackets with the whole algebra vanish because they vanish generically. Passing to the quotient \(V\) gives the integral alternating bimap. Its adjoint algebra is the kernel of an explicit linear map on pairs of endomorphisms. By (1) the rank of that map agrees generically and specially. The same unit-pivot argument gives a free, split kernel with the prescribed special fiber. Its associative law is given by the displayed operator composition. Denote this free \(R\)-algebra by \(D\); its generic and special algebras are the indicated products (1). The same recovery holds over fields for exact isomorphisms of the coordinate-line brackets.

## 3. Intrinsic matrix corners and marked coefficients

The radical \(J_D\) of the written endpoints of \(D\) is the product of the strict matrix-corner ideals, one in the original order and one in the opposite order. Its square is the face-output span, and its cube vanishes. In the integral algebra use the ideal generated by the values of the degree-four standard polynomial
\[
s_4(x_1,x_2,x_3,x_4)=\sum_{\pi\in S_4}\operatorname{sgn}(\pi)
                 x_{\pi(1)}x_{\pi(2)}x_{\pi(3)}x_{\pi(4)}.
\]
At either endpoint it equals the strict ideal. It vanishes in every diagonal block \(M_2(k)\) by Amitsur–Levitzki. For a strict corner \(i\to j\), choose three elements \(E_{11},E_{12},E_{22}\) in block \(i\) and the fourth argument in that corner. The fourth argument must appear last for a nonzero word. The first three multiply nontrivially in exactly the displayed order. By varying the fourth argument and multiplying by endpoint matrix units, the ideal therefore contains the whole corner, including both copies of a doubled corner. This works for the opposite-order component as well by using its source vertex. [Amitsur–Levitzki](https://doi.org/10.1090/S0002-9939-1950-0035758-5)

Compute the ideal \(J_D\) as a linear image using the multilinear map \(a\otimes x_1\otimes\cdots\otimes x_4\otimes b\mapsto a s_4(x_1,\ldots,x_4)b\). Likewise compute \(J_D^2\) by multiplication. Their equal endpoint ranks make them split free images, with the indicated special fibers, by unit-pivot elimination. The cube is zero. Let \(Q=D/J_D\), \(W=J_D/J_D^2\), and \(Z_D=J_D^2\).

The quotient \(Q\) splits into copies of \(M_2(R)\). Indeed, lift the special diagonal matrix idempotents successively in complementary corners. An idempotent approximation \(h\) is improved by \(h-(2h-1)^{-1}(h^2-h)\), which squares the error, also in characteristic two. The resulting integral corners have their special ranks, being images of idempotent projections. In each block lift the special units \(E_{i1},E_{1i}\) in their respective corners, scale so that the second times the first is \(E_{11}\) in its rank-one corner, and multiply these two systems to obtain matrix units. The positive graded corners of \(W,Z_D\) likewise admit matrix-unit bases from lifting their \((11,11)\) generators. The original and opposite components have the same graded support before specialization, including the doubled first corner for the original order and doubled last corner for the opposite order. A generic algebra isomorphism matches the central block labels of \(Q\) and the supports of the graded corners. Each component has a total reachability order, and the doubled corner distinguishes the two orders. Thus each original edge is matched to the identical written label, irrespective of the actual Lie change of basis.

Let \(H\) be the induced generic isomorphism from the fixed source adjoint algebra to \(D_K\). Its maps on diagonal matrix blocks are inner, so there are \(S_i\in\mathrm{GL}_2(K)\) such that the map of block \(i\) is \(X\mapsto S_i X S_i^{-1}\). Every thin graded corner then has map \(X\mapsto \eta_{ij}S_i X S_j^{-1}\) for some \(\eta_{ij}\in K^\times\), by the scalar commutant of the regular matrix bimodule. The generic multiplication on a face in the terminally capped original component is \((X,Y)\mapsto c_{ij\ell}XY\) with
\[
c_{ij\ell}=\eta_{i\ell}/(\eta_{ij}\eta_{j\ell}).
\]
The formula follows by transporting ordinary matrix multiplication and canceling the matrices at the intermediate vertex. It is integral in the chosen frames and reduces to the written face coefficient. In particular the face contact is the coboundary evaluated on the flag of the integer edge cochain \(-v_t(\eta_{ij})\). The added markers never enter face equations. The contact on the deleted face of the original-order component is a *positive* multiple of \(2^{m-1}\), since on the punctured complex the cochain is a cocycle and the terminal boundary has that index. The same conclusion holds for the opposite component up to its equivalent labeling, though only the original-order one is needed for the lower bound.

For a static exact comparison with the line law \(B_c\), use the same face equation with multiplicative edge cochains. On all retained faces the coefficients are \(1\); hence the scalar on the marked boundary is a \(2^{m-1}\)-st power. Conversely any such power is achieved by a multiplicative cocycle on the punctured complex evaluated on that boundary. To construct it, evaluate a character of the first homology on the cycles formed by closing each edge along a spanning tree. The resulting diagonal edge scaling gives an algebra isomorphism \(A_1\to A_c\), hence a Lie isomorphism. This proves the line and ramification assertions. It also gives the upper polynomial image degree by taking \(c=t^{2^{m-1}}\). For any multi-mark contact lattice from the prior construction, the same argument gives exactly the same set of contact vectors when read in the original-order adjoint component. For a lift at a given vector, use the previous monomial cochain on \(A_c\), identity on the orientation marker, and extend the resulting algebra map to the Heisenberg bracket.

## 4. A minor detects the contact without solving for individual idempotents

Let \(C=Z(Q)\), the center of the split matrix-block quotient. Its regular trace pairing is unimodular: in the basis of central block idempotents its matrix is the identity. Let \(\theta\) be the tensor inverse of that pairing. In this basis \(\theta=\sum_j e_j\otimes e_j\). Using a general basis \(c_u\) of \(C\), form the map
\[
\mathcal M:W\otimes W\longrightarrow Z_D\otimes C,\qquad
x\otimes y\longmapsto\sum_{u,v}\theta_{uv}\big((xc_u)y\big)\otimes c_v.
\]
It is defined intrinsically by the graded product and right action. The tag keeps the intermediate block \(j\). In matrix-unit corner frames every face acts by \(c_{ij\ell}\) times the split surjection \(M_2(R)\otimes M_2(R)\to M_2(R)\), tagged by the pair of endpoints and intermediate block. The surjection has an integral section \(X\mapsto X\otimes I\). Distinct faces use disjoint basis blocks of the domain and distinct tagged blocks of the codomain, since all participating corners are thin and each flag is determined by its three vertices. All other columns are zero. Thus the ideal of all generic maximal-rank minors has valuation at least \(4\cdot 2^{m-1}\), from the original-order marked face alone. The rank is \(O(M)\), since there are linearly many faces.

Here is an explicit bound on the rational height from an input arc of Lie image degree \(d\). An array has height \(h\) if it has a common polynomial denominator that is a unit at \(t=0\), and that denominator and all numerators have degree at most \(h\). Products of arrays add heights, and the inverse of an \(a\times a\) pivot array of height \(h\) invertible at zero has height at most \(ah\). In a rank-constant kernel system whose coefficients have a common denominator, selecting a maximal unit pivot and solving for the pivot coordinates produces a kernel basis of height at most \(ah\) when the pivot has size \(a\). Indeed the common denominator cancels in the equations, and the adjugate of the numerator pivot yields the bound. Free coordinates in that basis give an integral projection recording coefficients of any kernel vector.

- Start with derived-space bracket columns and supplement with standard vectors for the whole Lie basis. The basis matrix has degree at most \(d\). The induced alternating bimap in that basis has height at most \((M+3)d\). Its adjoint equations use at most \(2M^2\) unknowns and have this same height. The kernel basis has height \(O(M^3d)\). Composition of its operator pairs, read using the free coordinates just described, gives the multiplication of \(D\) with height \(H=O(M^3d)\).
- Columns for \(J_D\) are polynomials in products of at most six elements, using the standard polynomial displayed above, so have a uniform denominator to power five and height at most \(5H\). Columns for \(J_D^2\) have height at most \(11H\) with the corresponding shared denominator. Supplement independent special columns for \(J_D^2\) and \(J_D\) to an integral basis of \(D\), of height at most \(11H\). Its size is at most \(M\), so the adapted multiplication has height \((11M+23)H=O(M^4d)\). Call the latter bound \(h\).
- Obtain a basis of \(C\) by writing its linear commutator equations in \(Q\). The system has at most \(M\) unknowns and constant rank, so the center basis has height at most \(Mh\). Its multiplication, read in its free coordinates, has height at most \((2M+1)h\). The center trace pairing is built by two multiplications, and its inverse has height \(O(M^2h)\). The map \(\mathcal M\) uses this inverse, the central basis embedding, and two graded multiplications, so has height \(O(M^2h)=O(M^6d)\).

Consequently a nonzero maximal-rank minor has a polynomial numerator of degree \(O(M^7 d)\) and a denominator that is a unit at zero. Valuation of that numerator cannot exceed its degree. The intrinsic ideal-of-minors bound therefore implies \(d\ge 2^{m-1}/O(M^7)\). This detects the obstruction on arbitrary image arcs, without rationally solving for the individual central idempotents or matrix units.

## 5. Symmetric pole depth

If a Lie change of basis has symmetric pole depth \(b\), its induced isomorphism on the quotient by the derived space and its inverse have entries of valuation at least \(-b\) in integral frames. The change on adjoint operators is conjugation by this quotient map, so its two directions cost at most \(2b\), using the integral kernel frames. The same bounds hold on each graded corner of \(D\), by the split radical filtration. On a thin corner write its map as in Section 3 and set \(w_{ij}'=\tfrac14 v_t(\det H_{ij})\). Then
\[
w_{ij}'=v_t(\eta_{ij})+\frac{v_t(\det S_i)-v_t(\det S_j)}2,\qquad |w_{ij}'|\le 2b.
\]
The extra vertex difference vanishes on a cycle. Thus the absolute circulation on the subdivided terminal cycle is at least \(2^{m-1}\); it consists of six edge traversals, giving \(12b\ge 2^{m-1}\). For the matching upper bound use the explicit integer cocycle extending a primitive initial circulation through the original telescope blocks. Its terminal circulation is multiplied by \(2^{m-1}\). A fixed punctured-cap pattern scaled by the same factor completes it, with all edge values \(O(2^m)\), as in the prior sparse construction. The monomial map on the source algebra gives a Lie map of the same depth, using its induced maps on all three copies of \(M_2(A_c)\).

These are written proofs. The earlier transfer applied to split solvable Lie laws with a large torus. Here both endpoint laws are two-step nilpotent, and the labels and contacts are recovered from the adjoint algebra of their alternating bimaps. The usual Lie-law degeneration over a DVR permits a finite extension for the generic isomorphism; the lower bound here fixes the Laurent field and measures the image degree or the required ramification. [Burde](https://am-brno.math.muni.cz/07-5/burde.pdf) · [Grochow–Qiao](https://arxiv.org/abs/1907.00309)
