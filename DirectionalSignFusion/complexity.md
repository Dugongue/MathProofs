# Exact affine directional readout and sharp query bounds

Work over \(\mathbf F_3\), with dense based three-tensors. Put \(V=(\mathbf F_2)^3\) and write determinant signs additively. The ordinary transporter profile \(C(x)\subseteq V\) of an input pair is empty or an affine coset. Use \(B(x)=[C(x)\ne\varnothing]\), \(A(x)=[0\in C(x)]\), and \(D(C)=[e_1\in C,\ 0\notin C]\), where \(e_1=(1,0,0)\). A directional query is promised ordinary-positive. These are written proofs.

## The theorem

For every affine map \(f:V\to V\) there is a uniform polynomial-time transformation of a raw tensor pair into a pair of concise, local-centroid three-tensors with exact profile \(f(C(x))\). A supplied ordinary witness for \(x\) lifts explicitly.

Consequently on the ordinary-positive promise, either signed rail \(A,\neg A\) can be decided by two nonadaptive directional queries and a fixed Boolean decoder, or by three nonadaptive directional queries and a positive decoder. The positive decoders are one AND for \(A\) and one OR for \(\neg A\). With a supplied ordinary witness of sign \(a\ne0\), one directional query gives \(\neg A\), one gives \(A\) with output negation, and two with a positive decoder give \(A\). For \(a=0\) the signed decision is immediate.

These numbers are sharp in the affine-profile oracle model defined below. Both the upper bounds on actual tensors and the lower bounds in that specified oracle model are unconditional. The model exposes profile information and a supplied witness sign when applicable.

## Construction of the simultaneous sign carrier

Let \(f(v)=Lv+b\), and write its linear part as \(Lv=(\chi_1(v),\chi_2(v),\chi_3(v))\). Start with the earlier weighted cube-zero construction over \(\mathbf F_3\), using weight \(\chi_1\) on the original three typed roles. It produces a commutative local unital algebra \(R\) of even dimension, with scalar residue and \(J^3=0\) for \(J=\operatorname{rad}R\). Its properties used here are as follows.

- Each algebra transporter induces a raw transporter \(g\), and \(\operatorname{sgn}\det\phi=\chi_1(v(g))\), where \(\phi\) is the algebra transporter and \(\operatorname{sgn}\) denotes the sign bit. Each raw transporter lifts by the prior construction.
- The marker ranks recover an intrinsic subspace \(X_0\subseteq J/J^2\). In \((J/J^2)/X_0\), the individual original roles and the pure pin lines are intrinsically labeled. Their induced maps are \(\tau g_i\) and \(\tau\), respectively, with one common scalar \(\tau\in\mathbf F_3^\times\).
- The algebra turns the symmetric bimap into multiplication. All layers and prescribed role quotients are explicitly based in the construction.

These facts apply even if the raw positive mode format is nonconcise and even on the raw zero tensor. In the earlier proof \(X_0\) is the common radical of the low-rank forms, and the role quotient is recovered from the pairing with their evaluation duals. This use of the markers needs the induced role decomposition modulo \(X_0\), without any choice of invariant lifts. [Weighted cube-zero construction, §§2–4](https://github.com/Dugongue/MathProofs/tree/main/TISLDirectionalGap) · [Tensor-system framework and the signed TI question](https://arxiv.org/html/2306.03135v2)

For a character \(\lambda\), select in \((J/J^2)/X_0\) the original roles on which \(\lambda\) has weight one. If their total dimension is even, add one pure pin line. Their sum has odd dimension. Let \(I_\lambda\subseteq J\) be the inverse image under \(J\to (J/J^2)/X_0\) of the direct sum of all discarded roles. It is an ideal, as it contains \(J^2\); the intrinsic labels imply that it is transported by every algebra isomorphism. Put \(Q_\lambda=R/I_\lambda\). It has even dimension and, for the induced quotient transporter, sign
\[
 \operatorname{sgn}\det(\overline\phi_\lambda)
   =\operatorname{sgn}(\tau)+\lambda(v(g)).
\]
Indeed the unit line is fixed, and the remaining determinant is that on an odd-dimensional sum of the chosen normalized roles. Let \(Q_*\) be the quotient retaining just a fixed pure pin line by the same construction. It has even dimension and sign \(\operatorname{sgn}(\tau)\). Thus \(U_\lambda=Q_\lambda\oplus Q_*\) is a based \(R\)-module, and the induced module transporter has sign \(\lambda(v(g))\). If \(\lambda=0\), the construction still works, retaining one pin for \(Q_\lambda\).

We use a sign fact about the displayed modules. Every \(R\)-linear automorphism of any finite direct sum of even-dimensional cyclic modules \(R/I\), including \(R\) itself, has determinant one over \(\mathbf F_3\). The endomorphism ring of each summand is the local quotient \(R/I\). A unit on one summand has scalar residue \(\gamma\) and regular determinant \(\gamma^{\dim(R/I)}=1\), since its principal-unit factor acts unipotently. To reduce a general automorphism \(g\), fix a summand \(M_i\) and expand the \(ii\)-block of \(g^{-1}g\). It is a sum of endomorphisms of \(M_i\) equal to the identity. Since nonunits form the maximal ideal in \(\operatorname{End}_R(M_i)\), at least one summand is a unit. The corresponding \(g_{ji}:M_i\to M_j\) is split injective and therefore an isomorphism, since \(M_j\) is indecomposable (its endomorphism ring is local). Move it to the diagonal by an \(R\)-linear swap of those isomorphic even-dimensional summands, which has determinant one. Normalize the pivot by a summand unit and eliminate the other blocks in its row and column by elementary off-diagonal shears, each with determinant one. Induction reduces the map to the identity, proving the claim.

Set \(U=U_{\chi_2+\chi_1}\) and \(W=U_{\chi_3+\chi_1}\). Define a bimap \(\beta:X\times Y\to Z\) over the base field by
\[
 X=R^3,\qquad Y=R\oplus U\oplus W^2,\qquad
 Z=R^3\oplus U^2\oplus W,
\]
\[
 \beta\big((x_1,x_2,x_3),(y,u,w_1,w_2)\big)
  =\big((x_1y,x_2y,x_3y),\ (x_1u,x_2u),\ x_1w_1+x_2w_2\big).
\]
The displayed core \(Y_0=R,\ Z_0=R^3\) is regular scalar multiplication. Its input \(y=1\) eliminates the left radical of the whole bimap. Varying \(x_1,x_2\) between \(0,1\) eliminates the right radical on all quotient components as well as on \(R\). The output spans each summand separately, by choosing an input supported in the corresponding \(Y\)-summand and using those same coordinate choices. Hence \(\beta\) is concise.

The centroid, meaning the triples \((c_X,c_Y,c_Z)\) with
\[
 \beta(c_Xx,y)=\beta(x,c_Yy)=c_Z\beta(x,y),
\]
is precisely the scalar image of \(R\). To see commutativity of the centroid, compute \(\beta(c_Xx,d_Yy)\) using the two identities in opposite order. The output maps commute since the products span \(Z\); zero radicals then imply commutation on the inputs. The bimap is \(R\)-balanced, so it has a faithful scalar copy of \(R\) in this centroid. The three maps of any centroid element are therefore \(R\)-linear. For \(y\in Y_0\), the identity with \(c_X\) shows that \(c_Z\) preserves \(Z_0\), because the products with \(Y_0\) span \(Z_0\). The identity with \(c_Y\) then shows that \(c_Y\) preserves \(Y_0\): the quotient components of \(\beta(x,c_Yy)\) vanish for every \(x\), so taking \((x_1,x_2)=(1,0),(0,1)\) makes each of their coefficients vanish. With \(y=1\), the identity gives \(c_Xx=c_Y(1)x\) in \(Z_0=R^3\). Zero radicals and spanning products give the same scalar action on \(Y,Z\). This proves the centroid assertion and in particular its locality.

Every bimap transporter induces a unital algebra isomorphism \(\phi:R\to R'\) by conjugation on the centroid, and its three maps are semilinear for this same \(\phi\). Conversely every such algebra isomorphism gives the displayed blockwise lift, using \(\phi\) on \(R\) and its induced maps on the quotient modules. The ideals used in these modules are intrinsic, as established above. Comparing any transporter to this lift gives \(R\)-linear corrections independently on the two sources and the target. All of their determinants are one by the direct-sum sign fact. Consequently the determinant sign vector is exactly that of the blockwise lift:
\[
\begin{array}{c|c}
 X & 3\chi_1=\chi_1\\
 Y & \chi_1+(\chi_2+\chi_1)+2(\chi_3+\chi_1)=\chi_2\\
 Z & 3\chi_1+2(\chi_2+\chi_1)+(\chi_3+\chi_1)=\chi_3 .
\end{array}
\]
Thus the profile is exactly \(L C(x)\). The source and target are based using the same block ordering, and inverse-transpose changes between bimap and covariant tensor conventions preserve the signs. Reflect the target with bit vector \(b\) to obtain the profile \(f(C(x))\). The weighted algebra has linear dimension in the sum of raw mode dimensions over this fixed field, and each module uses only a constant number of its direct sums and quotients. The transformation is polynomial time. The raw-to-algebra lift is given by the earlier marker construction, and the module lift and final reflection are explicit. This supplies an ordinary witness whenever one is supplied for the original comparison.

All 51 nonempty affine cosets in \(V\) occur in these concise local-centroid formats. Start with the self-pair of the raw zero tensor with positive format \(1\times1\times1\); its profile is all of \(V\). Choose \(L\) with the desired image and reflect by the desired coset representative. More generally if a particular sign inside that coset is prescribed, choose a preimage under the affine map and lift the corresponding raw scalar transporter, so these examples also admit witnessed realizations.

## Exact query normal forms

A fiber-hit query for an affine line \(\ell\subseteq V\) is one directional query. Take a rank-two linear map with kernel the direction of \(\ell\) and with image \(\langle e_2,e_3\rangle\). Translate its output so the fiber of \(e_1\) is \(\ell\), and the whole image avoids 0. The directional answer is exactly \([C\cap\ell\ne\varnothing]\). Also for every two distinct \(u,v\in V\), one full-rank affine readout maps \(u\) to 0 and \(v\) to \(e_1\), and its directional answer is \([v\in C,\ u\notin C]\).

**Two queries with general Boolean decoding.** Fix \(a\ne0\). Ask the hit of \(\ell=\{0,a\}\) and the directed comparison \([a\in C,\ 0\notin C]\). The hit and the negated comparison together are exactly \(A\). The complement uses the negation of that Boolean decoder. Both queries are nonadaptive.

**Three positive queries for \(A\).** Choose independent \(u,v\in V\). Test the hits of \(\{0,u\},\{0,v\},\{0,u+v\}\), and take their AND. If \(0\) is absent but the hits succeed, the affine profile contains \(u,v,u+v\), and hence their sum 0, as a sum of an odd number of its elements. This contradiction proves the decoder.

**Three positive queries for \(\neg A\).** Fix coordinates and put \(K_j=\{z:z_1=\cdots=z_j=0\}\), with \(K_0=V\). For \(j=1,2,3\), take the linear readout \((z_j,z_1,\ldots,z_{j-1},0,\ldots,0)\). Its 0-fiber is \(K_j\) and its \(e_1\)-fiber is \(K_{j-1}\setminus K_j\). The directional answer detects that the intersection with \(K_{j-1}\) is nonempty while the intersection with \(K_j\) is empty. The OR of these answers detects \(C\cap K_3=\varnothing\), since on the promise \(C\cap K_0\ne\varnothing\). This decoder even works for nonempty subsets without the affine-coset hypothesis.

**Witnessed queries.** If the given sign is \(a\ne0\), the query \([a\in C,\ 0\notin C]\) has answer \(\neg A\). For a positive decoder for \(A\), choose \(u\notin\langle a\rangle\) and ask the hits of \(\{0,u\},\{0,u+a\}\), using AND. If both hit without 0, then \(a,u,u+a\in C\), contradicting exclusion of 0 by the same affine identity. Every transformed query can carry its lifted witness.

These bounds also shorten the existing guarded ordinary-TI implication. A hypothetical one-output directional compiler gives \(A\le_m B\) by a conjunction of three directional outputs and the ordinary guard. For \(\overline A\), use the always-promised ordinary-NO directional gate from the previous directional chapter, and otherwise use the three positive negative-rail tests above with the ordinary guard. Positive ordinary TI aggregation compiles these bounded formulas into one query. The coTI premise remains unnecessary in these directions. [Ordinary-NO gate and positive aggregation](https://github.com/Dugongue/MathProofs/tree/main/TISLDirectionalGap)

## Sharpness in the affine-profile oracle model

The unknown object in this model is a nonempty affine coset \(C\subseteq V\). A query selects any affine map \(f:V\to V\) and receives \(D(f(C))\). Apart from its query answers, the decoder knows only the ambient model and, in the witnessed version, the specified \(a\in C\). In the positive version it selects a fixed query list and uses a monotone Boolean decoder on the bits. Reading tensor entries, dimensions, or additional witnesses is outside this model.

A test true on the full cube \(V\) must have \(e_1\in f(V)\) and \(0\notin f(V)\). It has rank at most two and is simply a hit of the affine fiber \(f^{-1}(e_1)\), which has at least two points. If only two queries feed a monotone decoder for \(A\), choose a nonzero point from each fiber of a query true on \(V\), and form their affine line (or a singleton if only one distinct point is chosen). If neither query is true on \(V\), choose any nonzero singleton. The resulting coset omits 0 and makes every query true that was true on \(V\), so the monotone decoder would also accept it. This proves the positive lower bound of three for \(A\).

One general Boolean-decoded query cannot decide either signed rail. If its answer at \(V\) is true, some nonzero singleton shares that answer by the fiber argument. If its answer at \(V\) is false, it would have to be true on all seven nonzero singletons. For a singleton \(\{z\}\) the answer is true exactly when \(f(z)=e_1\). The differences of the nonzero vectors span \(V\), so an affine map sending all seven nonzero vectors to \(e_1\) is constant \(e_1\). Then it also answers true at the positive singleton \(\{0\}\), a contradiction.

For the positive lower bound for \(\neg A\), a monotone function of two bits is constant, a projection, an AND or an OR. Constants and projections already fail. An AND accepting all seven nonzero singletons would require both maps to be constant \(e_1\), and would accept \(\{0\}\). In an OR, each \(e_1\)-fiber must omit 0, since the accepted singleton \(\{0\}\) is forbidden for this decoder. The fibers have sizes at most four. Two size-four fibers are affine hyperplanes; if parallel they coincide (both avoid 0), and if nonparallel their union has size six. If one is smaller the union also has size at most six, as an affine set below size four has at most two points. They cannot cover all seven nonzero singletons. Thus three positive queries are necessary.

Finally when the supplied sign is \(a\ne0\), the two possible hidden cosets \(\{a\}\) and \(\{0,a\}\) make zero queries insufficient. For a positive one-query decoder of \(A\), the answer must be true on \(V\). Choose a nonzero point of its hit fiber and form its affine line with \(a\), or the singleton \(\{a\}\) if they coincide. The new coset contains the supplied sign but omits 0 and still gives the same answer. This establishes the witnessed lower bounds.
