# Exact order for the Möbius-telescope tensor powers

Let \(T_m^+,T_m^-\) be the sparse pair obtained from a chain of \(m-1\) Möbius-band and annulus blocks and a cap on the first three-edge circle. In the barycentric subdivision, vertices are ordered by simplex dimension, and missing successor corners are added with no nonzero products of two strict corners. The target deletes one cap flag product. We use the weight convention that a deleted product has positive defect \(w(x,z)-w(x,y)-w(y,z)\). The coefficient field is arbitrary. [Sparse exponential poles](SparseSeed.md)

**Theorem.** The exact base cycle-mean slope is
\[
 \lambda_1=\tfrac12,\qquad \lambda_m=\frac{2^{m-1}}3\quad(m\ge2).
\]
This holds for every order of labels within each barycentric rank. Consequently for each \(r\ge1\) and every nonnegative integer cap triple, arbitrary Laurent witnesses for \((T_m^+)^{\otimes r}\rightsquigarrow (T_m^-)^{\otimes r}\) exist precisely when
\[
 p_1+p_2+p_3\ \ge\ \lceil r\lambda_m\rceil .
\]
The right side is the minimum order of a polynomial-matrix presentation. There are monomial matrices attaining this order whose degrees are all at most the order, and whose image after removing its leading parameter power is a polynomial arc of degree \(r\).

More generally, prescribe positive integers \(c_1,\ldots,c_r\) for the deleted-product contacts in the coordinate fibers, in a chosen factor ordering. Write \(C=\sum_i c_i\). The exact cap threshold becomes \(\lceil C\lambda_m\rceil\). It is attained by monomial matrices of degrees at most that order and a normalized polynomial image arc of degree \(C\). The largest intrinsic contact of every witness with these fiber contacts is also \(C\).

The use of arbitrary Laurent witnesses in the lower bound invokes the existing extraction of integral corner weights from arbitrary regrouped changes of basis and the ensuing cycle lower bound. The new upper bound is independent of cycle optimization and gives the matrices directly. [Amplification and cancellation](PowerSeed.md) [Exact power orders](PowerOrderSeed.md)

## 1. Compatible lifted angles on the blocks for m ≥ 2

Put \(d_i=2^{i-1}\) and \(a=d_m/3\). Use values in \((\tfrac13\mathbb Z)/\mathbb Z\) as combinatorial labels. The differences of compatible real lifts will serve as formal rational weights over any coefficient field. Choose the starting position and overall sign to agree with the cap convention below. With this orientation initially label the vertices of the core by \(0,-1/3,-2/3\) modulo \(\mathbb Z\), in cyclic order. On every edge use a lift in which the change on traversing this order is \(-1/3\), including the edge closing the cycle.

On block \(i\), use the real lift \(-d_i x/3\) on the rectangular covering strip of its Möbius band. The values at the identified ends of the strip differ by the integer \(-d_i\), so this gives compatible angular lifts on all triangles, differing by an integer constant on each common simplex. The core has change \(-d_i/3\) on each of its three edges, matching the previous block. If the horizontal coordinate is taken with the opposite orientation, use the opposite sign and the corresponding additive constant in the lift. The range of the lift on the vertices of any triangle in the rectangular grid is at most \(d_i/3\).

Number the six consecutive vertices of the outer boundary of the band as \(b_j\), starting over horizontal coordinate zero and following the increasing horizontal orientation. Their lifted values are \(-j d_i/3\), continued to \(j=6\). In the annulus, give \(a_j\) the lifted value at \(b_{2j}\). The three triangles in sector \(j\) have vertex positions with horizontal indices
\[
 \{2j,2j,2j+1\},\qquad
 \{2j,2j+1,2j+2\},\qquad
 \{2j,2j+2,2j+2\}.
\]
Use the consecutive indices in the lifts around the seam, where advancing a full turn changes the value by the integer \(-2d_i\). Thus the diameter of the values on each triangle of the annulus is at most \(2d_i/3=d_{i+1}/3\). Its new core has change \(-d_{i+1}/3\) on each of its three edges. This proves compatibility at each successive block. Every simplex in all these blocks has lift diameter at most \(a\), and all vertex lifts are in \(\tfrac13\mathbb Z\).

A vertex \(x\) of the barycentric subdivision corresponds to an original simplex. For an original support corner \(x\subset y\), choose a local lift \(f\) on the simplex \(y\) and set
\[
 \omega_{xy}=\min_{v\in y} f(v)-\min_{v\in x} f(v).
\]
This difference is independent of the allowed integer shift of the lift. It is in \([-a,0]\), since the minima are over nested sets and the diameter is at most \(a\). It telescopes on every flag. Choose a gauge \(u_x\in\{0,1/3,2/3\}\) congruent to the minimum on any lift of \(x\). Compatibility of lifts gives
\[
 \omega_{xy}=w_0(x,y)+u_y-u_x,\qquad w_0(x,y)\in\mathbb Z.
\]
On a core edge in cyclic order, with endpoints \(v_i,v_{i+1}\) and barycenter \(e_i\), the weights on \(v_i\to e_i\) and \(v_{i+1}\to e_i\) are \(-d_i/3\) and \(0\), respectively. In particular the initial core has an explicit boundary pattern for attaching the cap.

## 2. The cap and the ordering corners

Relabel the three boundary vertices as \(0,1,2\) in the chosen cyclic order, and the apex as \(3\), so the omitted flag is \((3,03,013)\), where strings denote sets of vertices. Any choice of the omitted apex-spoke-face flag permits this naming and either orientation of the core may be used consistently throughout the blocks. This naming is independent of the total order on labels within a rank. Start on the original cap corners with an integer cochain \(v\) equal to \(-1\) at \(03\to013,\ 0\to013,\ 0\to01\), and zero elsewhere. Its only nonzero flag defect is \(1\) at the omitted flag. The other two flags incident to its nonzero corners are \((0,03,013)\) and \((0,01,013)\), whose defects cancel.

For the cap take \(u_x=k_x/3\) from the following table and set \(\omega_{xy}=v(x,y)+u_y-u_x\).

| Simplex labels | Values of \(k_x\) in the same order |
| --- | --- |
| \(0,1,2,3\) | \(0,2,1,1\) |
| \(01,02,03,12,13,23\) | \(2,0,0,1,1,1\) |
| \(013,023,123\) | \(1,0,0\) |

For each of the thirty strict cap incidences, \(3v(x,y)+k_y-k_x\) is between \(-2\) and \(0\). In particular the weights on \(0\to01,1\to12,2\to02\) are \(-1/3\), and those on the other three incidences of the boundary circle are zero. These weights and gauge residues agree with the first core of the telescope. The omitted defect remains \(1\). Since \(a\ge2/3\) for \(m\ge2\), all cap weights land in \([-a,0]\).

For any added successor corner \(x\to y\), choose \(\omega_{xy}\) as the unique element of \(\{0,-1/3,-2/3\}\) congruent to \(u_y-u_x\) modulo \(\mathbb Z\). This also lands in \([-a,0]\), and choosing it creates no new flag condition. Finally set the weight of each identity corner to zero. Thus the entire graph admits an integral cochain \(w_0\) with unit contact and a rational gauge \(u\) for which
\[
 -a\le w_0(x,y)+u_y-u_x\le0
\]
on every corner. With both vertex isotope weights zero this supplies a rational cycle-mean certificate of cap \(a\) in the three-layer cycle formulation. For the reverse inequality, the terminal subdivided circle has circulation of magnitude \(d_m\), from the degree-doubling homology relation. Traverse it in the direction of positive reward in the three-layer graph, inserting one identity step between each forward and backward pair. The resulting directed cycle has three triples of steps. Thus every unit-contact cochain has cycle mean at least \(d_m/3\), and contact \(c\) gives the lower bound \(c\,d_m/3\). The bound is attained at any such \(c\) by multiplying the constructed cochain and gauge by \(c\).


For \(m=1\), use the same cochain \(v\) on the original cap, but choose \(u_x=-1/2\) on \(S=\{0,02,03,023\}\) and \(u_x=0\) elsewhere. The only original corners from \(S\) to its complement are precisely the three with \(v=-1\). Therefore every original normalized weight \(v(x,y)+u_y-u_x\) is either \(-1/2\) or \(0\). On every added ordering corner choose the unique element of \(\{-1/2,0\}\) congruent to \(u_y-u_x\) modulo \(\mathbb Z\). This constructs the same kind of certificate with \(a=1/2\) for every labeling. For the lower bound, traverse the reverse of the omitted flag, padding the two backward steps with identities to form two triples in the layered graph. The reward is the marked defect \(c\), giving mean \(c/2\). Thus the least base cycle mean at contact \(c\) is \(c/2\).


## 3. Integer weights and explicit polynomial matrices on the power

Put \(a=\lambda_m\), fix positive contacts \(c_i\), and set \(P=\lceil a\sum_i c_i\rceil\). On tuple vertices define \(U_x=\sum_i c_i u_{x_i}\). For each supported corner set
\[
 W(x,y)=\sum_i c_i w_0(x_i,y_i)+\lfloor U_y\rfloor-\lfloor U_x\rfloor.
\]
This is an integer equal to \(\sum_i c_i\omega_{x_i y_i}+\{U_x\}-\{U_y\}\), with \(\{\cdot\}\) denoting fractional part. Since the sum is in \([-a\sum_i c_i,0]\) and the fractional-part difference lies strictly between \(-1\) and \(1\), integrality gives
\[
 -P\le W(x,y)\le0.
\]
The gauge term contributes zero to every defect. A retained product has defect zero. At a deleted product the defect is the sum of the \(c_i\) over the coordinates whose factors use the deleted flag. All such subsets occur, by choosing an identity product in unused coordinates. In particular the largest defect is \(\sum_i c_i\).

Let \(H\) be diagonal on the written corner basis with entry \(t^{W(x,y)}\). Use the two input maps \(H^{-1}\) and output map \(t^P H\), in bilinear-map notation. All three maps are polynomial matrices of degrees at most \(P\), by the bounds on \(W\). Their tensor action is \(t^P\) times the normalized law with coefficient \(1\) at each retained product and \(t^{\delta}\) at each deleted product of defect \(\delta\). The image has the stated lowest order and normalized degree. The construction uses integer exponents and coefficients from \(\{0,1\}\) over every field.

Conversely, any arbitrary Laurent witness with the prescribed positive contacts gives an integral cochain on the product corner graph by the earlier cap extraction. Split it into the sum of its coordinate fiber cochains up to a gauge, using the retained squares. The largest intrinsic contact is then \(\sum_i c_i\), because a defect is the sum of its factor defects. Each fiber has a layered cycle of mean \(ac_i\), using the terminal circle for \(m\ge2\) and the reverse marked flag for \(m=1\). The additive cycle-mean bound gives cap sum at least \(a\sum_i c_i\). This also gives the polynomial order lower bound, since dividing the output map in any order-\(P\) polynomial presentation by \(t^P\) produces a Laurent witness with corresponding cap. The cap distribution is arbitrary once this sum is feasible: multiplying the three Laurent matrices by scalar powers whose exponents sum to zero transfers any cap budget to the desired modes.

## 4. Exact period and succinct witnesses

For \(m=1\) the least order increases by \(1\) when the power \(r\) increases by \(2\). For \(m\ge2\), the reduced denominator of \(\lambda_m\) is \(3\), and the least order increases by \(2^{m-1}\) when the power increases by \(3\).

The base graph has \(O(m)\) supported corners, each with a cochain value of \(O(m)\) bits and a gauge in constant denominator. Its table follows directly from the specified triangulation and the cap weights. Given a corner of the regrouped power as a tuple of base corners, the formula for \(W\) needs \(r\) table lookups and integer arithmetic on values of bit length \(O(m+\log C)\), where \(C=\sum_i c_i\). This specifies every diagonal entry of all three matrices without enumerating the powered graph or searching for a minimum.

The contact conclusions concern the intrinsic associated graded law of an arbitrary witness. The polynomial image degrees are attained by the constructed presentations. The earlier Möbius-band construction supplies the doubled homology class. Here, minimum values of compatible lifts put its entire weight representative in the sharp interval, which permits exact integer rounding after taking powers. [Filakovský–Franek–Wagner–Zhechev](https://pmc.ncbi.nlm.nih.gov/articles/PMC6777513/)

These are written proofs. The cap incidence table was verified by exact arithmetic. This note has no Lean kernel verification.
