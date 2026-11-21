# Sharp pole and clearing orders for the terminal-cap telescope

Use the sparse thin multiplication tensors \(U_m,V_m\) from the Möbius telescope with its punctured cap on the **last** three-edge circle. Let \(E_m\) be its one deleted coordinate, so \(U_m=V_m+E_m\), and put \(d=2^{m-1}\). The doubled homology class makes \(d\) the index of the marked contact lattice. Tensor powers are regrouped into three modes. The coefficient field \(k\) is arbitrary. [Contact lattices](ContactSeed.md)

**Theorem 1.** The possible positive coordinate-fiber contacts of a Laurent degeneration from \(U_m^{\otimes r}\) to \(V_m^{\otimes r}\) are exactly the tuples \(c_i\in d\mathbb Z_{>0}\). For prescribed contacts, put \(C=\sum_i c_i\). The largest intrinsic contact of any such witness is \(C\). Its possible nonnegative integer forward pole caps are exactly
\[
 p_1+p_2+p_3\ \ge\ \left\lceil C/2\right\rceil.
\]
There is an order-\(\lceil C/2\rceil\) polynomial-matrix presentation of the coordinate arc \(\bigotimes_i(V_m+t^{c_i}E_m)\), with all three matrix degrees at most the order. Its normalized image has degree \(C\). In particular the unrestricted minimum polynomial order for the power is \(\lceil rd/2\rceil\). These conclusions are independent of the order of labels within each barycentric rank.

Here a contact is the valuation of a generically nonzero corner product in the normalized associated graded law. The corner bases are integral and can be rescaled only by units, which leaves the valuations unchanged. Forward poles bound the entries of the three acting matrices.

## 1. Lower bounds and separation of the factors

The terminal variant and any partial deletion in its tensor powers have the same based radical powers as the source. Indeed, the retained flag through the other edge barycenter keeps the same degree-two corner when the marked flag is deleted. All strict corners have the indicated degree in the tensor product filtration. The support order is the product of total vertex orders, whose automorphisms permute coordinate chains. Thus the earlier arbitrary-map extraction of integer corner weights applies. It uses unit normalization, the constant-rank commutator-power filtration, and rank-one graded corner modules. After alignment of the factors, a corner weight \(w(x,y)\) has zero defect on retained products at the special law, and the defect \(w(x,z)-w(x,y)-w(y,z)\) is the contact on any deleted product. [Amplification and cancellation](PowerSeed.md)

As in the exact power formula, mixed-coordinate squares are retained. Any simultaneous forward step can be split into its single-coordinate steps without changing weight. A closed walk, based at a chosen reference tuple, can then be sorted by its coordinates by exchanging adjacent steps in distinct factors; squared commutation preserves its weight. Subtracting the sum of its restrictions to the reference fibers therefore leaves a vertex coboundary. In particular, the defect on a product is the sum of the defects in the participating factors. In a base fiber the marked boundary represents \(d\) times the homology generator up to sign, giving a contact in \(d\mathbb Z\). The product of the marked triple in every affected factor reaches the sum of the positive contacts. Identity products may be used in the other factors. [Exact power orders](PowerOrderSeed.md)

The cap inequalities give a three-layer difference graph. With total cap \(p\) after scalar redistribution, the edges for a corner \(x\to y\) are the following, with respective rewards \(w(x,y),w(x,y),-w(x,y)\).
\[
 B_x\to A_y,\qquad A_x\to C_y,\qquad C_y\to B_x .
\]
The reward of any closed walk is at most \(p\) times the number of its edges of the last type. For a product of defect \(\delta=w(x,z)-w(x,y)-w(y,z)\), traverse it in reverse by
\[
 B_x\to A_z\to C_z\to B_y\to A_y\to C_y\to B_x .
\]
The three identity steps cost zero reward. The resulting bound is \(2p\ge\delta\). Apply it to the simultaneous marked triple of largest defect \(C\). This also bounds polynomial orders, by dividing the output map by its leading power of \(t\). For partial endpoints, the same reasoning gives the lower bound with zero contacts allowed in the other factors.

## 2. An angle construction attaining half the contact

We first construct base weights of a single prescribed contact \(c=dh>0\), normalized to a real gauge interval \([-c/2,0]\). For \(m\ge2\), use the compatible lifted angles of the initial-cap construction on all blocks up to the last outer annulus, multiplied by \(h\). In block \(i\) the lift on the Möbius strip is \(-h2^{i-1}x/3\) in the horizontal coordinate. The lifts on a common simplex differ by an integer, since advancing through the strip adds \(-h2^{i-1}\). Use the boundary orientation that agrees with the cap convention below. On every earlier annulus attach each new vertex \(a_j\) at the same angle as \(b_{2j}\), as in the earlier construction. All these local lift diameters are at most \(c/6\). [Exact initial-cap order](ExactSparseOrders.md)

On the last annulus the old boundary vertices \(b_0,\ldots,b_6\) have lifted angles \(-jc/6\), with \(b_6=b_0\) after one turn. Give the new boundary vertices \(a_0,a_1,a_2,a_3\) angles \(0,-c/2,-c/2,-c\), with \(a_3=a_0\) after the turn. In units of \(-c/6\), the three triangles of each sector now have angle labels
\[
\begin{array}{c|ccc}
0&(0,0,1)&(0,1,2)&(0,2,3)\\
1&(3,2,3)&(3,3,4)&(3,4,3)\\
2&(3,4,5)&(3,5,6)&(3,6,6).
\end{array}
\]
Their diameters are at most \(c/2\). The overlapping lifts remain consistent, including at the seam where they differ by the integer \(c\). The angles of the new boundary vertices are themselves integers because \(d\) is even. Starting positions and overall orientation can be chosen to match any omitted apex-spoke-face flag.

For an original barycentric corner \(x\subset y\), subtract the minimum angle on the lifted simplex \(x\) from that on \(y\), evaluating both in a lift of \(y\). Call the result \(\omega(x,y)\). It is in \([-c/2,0]\) and telescopes on every flag. Let \(u_x\in\{0,1/3,2/3\}\) be the minimum on a lift of \(x\) modulo \(\mathbb Z\). These residues suffice because all angles lie in \(\tfrac13\mathbb Z\). Then \(\omega(x,y)=w_c(x,y)+u_y-u_x\) with \(w_c(x,y)\) integral. On the terminal boundary the three cyclic angle drops are \(c/2,0,c/2\). Their corresponding barycentric forward weights are the negatives of these drops on the initial endpoint incidence and zero on the terminal endpoint incidence.

Label the terminal boundary \(0,1,2\), its cone apex \(3\), and the removed flag \((3,03,013)\). On the original cap use the integer cochain \(v=-1\) at \(03\to013,0\to013,0\to01\) and zero elsewhere. Its only nonzero defect is \(1\) at the marked flag. Put \(S=\{0,02,03,023\}\) and give vertices in \(S\) value \(-1/2\), the other vertices value zero. The three incidences from \(S\) to its complement are exactly the three corners with weight \(-1\). Consequently adding this vertex coboundary puts every cap corner weight in \(\{-1/2,0\}\). The boundary pattern is \(-1/2,0,-1/2\) on the initial incidences in cyclic order, and zero on the other three incidences. Multiplying by \(c\) matches the new annulus boundary. For even \(c\) all these cap gauge values are integral, so the cap can use residue \(u_x=0\) with the resulting \(\omega\) as its integer cochain. For \(m=1\) there is only the cap, \(d=1\), and the multiplied half-integral gauges provide the construction directly for any positive \(c\).

For \(m\ge2\) assign each added successor corner the weight in \(\{0,-1/3,-2/3\}\) congruent to \(u_y-u_x\) modulo \(\mathbb Z\). This lies in the same interval since \(c/2\ge1\). For \(m=1\), use the representative in \(\{0,-1/2\}\) for the possibly half-integral gauges. The added corners impose no triangular relations. Identity weights are zero. We have therefore obtained integer weights plus a gauge throughout the graph, with the sole defect \(c\) and all normalized weights in \([-c/2,0]\).

On the regrouped product sum these normalized weights (using zero weights for contact zero). If \(U_x\) is the sum of the corresponding gauges at \(x\), replace \(U_x\) by \(\lfloor U_x\rfloor\), retaining the integer cochain sum. This changes the normalized corner weights by a difference of fractional parts strictly between \(-1\) and \(1\). The resulting integer exponents \(W(x,y)\) satisfy
\[
 -\lceil C/2\rceil \ \le W(x,y)\le0 .
\]
The defects are unchanged. With \(H\) diagonal of entries \(t^{W(x,y)}\), the two input maps \(H^{-1}\) and output map \(t^{\lceil C/2\rceil}H\) achieve the stated order and degree bounds. For the cap region, move scalar powers among the three Laurent maps with total scalar exponent zero. This distributes the required total cap arbitrarily.


## 3. Fixed coordinate arcs and their ramification

For any extension field \(K\) of \(k\), consider a tensor on the written support of \(U_m^{\otimes r}\), with every source coordinate nonzero and all coordinates retained in the full target equal to \(1\). Such a tensor is in the ordinary three-mode orbit of \(U_m^{\otimes r}\) over \(K\) exactly when it has the form
\[
 \mathcal A_f=\bigotimes_{i=1}^r(V_m+f_iE_m),\qquad f_i\in(K^\times)^d .
\]
For necessity, the tensor has the written unit. Its isotopy with the source multiplication law is therefore an algebra isomorphism after multiplying by units. On the intrinsic graded corner lines it gives nonzero scalars \(\eta(x,y)\) whose multiplicative defects are the coordinate coefficients. The identification of labels is unique up to the coordinate permutations already described. Mixed squares have coefficient \(1\), so the same subdivision and exchange argument used for integer cochains applies with multiplication in \(K^\times\). Up to a multiplicative vertex gauge these scalars are the product of their reference-fiber restrictions. Each fiber's defect on its marked boundary is a \(d\)-th power by the homology relation, and the coefficients in multiple-mark positions are the products of the corresponding fiber values. Conversely, given \(f_i=g_i^d\), use the base integer cochain of contact \(d\) from Section 2 and substitute \(g_i\) in its monomial diagonal action. The resulting product is exactly \(\mathcal A_f\). [Bläser–Lysikov](https://arxiv.org/abs/1606.04253)

It follows that among coordinate polynomial arcs over \(k[t]\) which reduce to \(V_m^{\otimes r}\) and admit a Laurent lift over \(k((t))\), the exact minimum image degree is \(rd\). In fact the coordinate polynomials \(f_i(t)\) vanish at zero and have positive orders divisible by \(d\). The degree of the coordinate arc is \(\sum_i\deg f_i\), since \(\prod_i f_i\) occurs as a coordinate and all other products have degree at most this sum. Equality is attained with all \(f_i=t^d\).

More generally, fix a Laurent-liftable coordinate arc of positive valuations \(c_i=\operatorname{ord}_t f_i\). Its exact total forward pole budget is \(\lceil\sum_i c_i/2\rceil\). The lower bound is the reverse marked product from Section 1. To attain the bound, choose Laurent roots \(g_i\) with \(g_i^d=f_i\), and write \(g_i=t^{c_i/d}\epsilon_i\) with unit \(\epsilon_i\in k[[t]]^\times\). Multiply the diagonal algebra map from Section 2 by the unit-valued diagonal maps from the base contact-\(d\) cochain evaluated at \(\epsilon_i\) in each factor. These maps correct all generic coefficients to the prescribed values and leave the entry valuations unchanged.

For \(f_i=t^{b_i}\) with \(b_i>0\), the least ramification index of a lift in \(k((t^{1/e}))\) is
\[
 e_{\min}=\frac{d}{\gcd(d,b_1,\ldots,b_r)}.
\]
Indeed \(d\) must divide \(e b_i\) in every factor, and those divisibilities give the monomial roots in the new uniformizer \(s=t^{1/e}\). Measured in \(s\), the exact cap sum and least polynomial order for the fixed arc are both \(\lceil e\sum_i b_i/2\rceil\). Thus at \(m\ge2\) the total pole budget in valuations normalized by \(v(t)=1\) is \(\sum_i b_i/2\) over every allowed ramification. The polynomial image degree in the original coordinate \(t\) is still \(\sum_i b_i\).

## 4. Exact polynomial clearing at every prime

**Theorem 2.** Fix nonzero \(f_i\in k[t]\) vanishing at zero, and let \(q\in k[t]\setminus\{0\}\). There are three square polynomial matrices over \(k[t]\) taking \(U_m^{\otimes r}\) to \(q(t)\mathcal A_f(t)\) exactly when both of the following hold.

1. Every \(f_i=g_i^d\) for a polynomial \(g_i\in k[t]\).
2. For each monic irreducible polynomial \(\pi\in k[t]\),
   \[
   \operatorname{ord}_\pi q\ \ge\
   \left\lceil\frac{\sum_i\operatorname{ord}_\pi f_i}{2}\right\rceil .
   \]

When these conditions hold the matrices can all have degree at most \(\deg q\). In particular for \(m\ge2\) the minimum clearing polynomial, up to a nonzero scalar, is \(\prod_i g_i^{d/2}\), of degree half the coordinate image degree. A fixed arc of this kind has a polynomial presentation with scalar \(t^P\) precisely when its \(f_i\) are \(d\)-th-power monomials and \(P\ge\lceil\sum_i\operatorname{ord}_t f_i/2\rceil\).

*Necessity.* The three matrices are invertible over \(k(t)\), since the generic target is concise. Absorbing \(q^{-1}\) in the output yields an orbit witness over \(k(t)\), so the field criterion gives \(f_i\in(k(t)^\times)^d\). Every rational root of a polynomial has nonnegative valuation at every irreducible polynomial and is therefore itself a polynomial.

Let \(\alpha\) be any root of \(\pi\) in an algebraic closure of \(k\), and let \(s=t-\alpha\). If the multiplicity of this root in \(\pi\) is \(a\), then the \(s\)-valuation of each \(f_i\) is \(a\operatorname{ord}_\pi f_i\), and that of \(q\) is \(a\operatorname{ord}_\pi q\). Divide the output matrix by \(q\) in the completion in \(s\). This has total forward cap at most \(a\operatorname{ord}_\pi q\) and its normalized image is \(\mathcal A_f\). Its special tensor has the marked flags deleted just in the factors whose \(f_i\) vanish at \(\alpha\). The other factors have nonzero special marked coefficients and can be aligned with the written source by constant diagonal maps. The partial-endpoint case of Section 1 gives \(2a\operatorname{ord}_\pi q\ge a\sum_i\operatorname{ord}_\pi f_i\). Cancelling \(a\) also handles inseparable \(\pi\).

*Sufficiency.* Factor each \(g_i\) over \(k[t]\) as \(a_i\prod_\pi\pi^{h_{i,\pi}}\) for \(a_i\in k^\times\). For each \(\pi\), take the integer weights \(W_\pi\) from Section 2 with contact vector \((d h_{i,\pi})_i\), allowing zeros. Put \(P_\pi=\lceil\sum_i d h_{i,\pi}/2\rceil\), so each entry of \(W_\pi\) lies in \([-P_\pi,0]\). On the regrouped corner basis form the diagonal matrix \(H\) with entry the product of \(\pi^{W_\pi(x,y)}\) over these primes, times the constant diagonal term from evaluating the base contact-\(d\) cochain in each factor at \(a_i\). Its multiplicative defects are the required \(f_i\) in single marks and the corresponding products in multiple marks. The inputs \(H^{-1},H^{-1}\) and output \(qH\) are polynomial matrices with the specified image. Each input entry has degree at most \(\sum_\pi P_\pi\deg\pi\le\deg q\). Each output entry divides \(q\) up to a nonzero scalar and has degree at most \(\deg q\). This proves the exact clearing assertion.

The results on least image degree are for the stated coordinate pattern. The sharp pole and polynomial-order bounds for the degeneration itself allow arbitrary independent maps on the regrouped modes. The proof uses the earlier degree-doubling telescope and cap extraction. Changing the angle distribution in the last outer annulus allows sharp matching to the half-integral terminal cap and gives the simultaneous exact local and global clearing bounds. [Filakovský–Franek–Wagner–Zhechev](https://doi.org/10.1007/s41468-018-0021-5)

These are written proofs. The note has no Lean kernel verification.
