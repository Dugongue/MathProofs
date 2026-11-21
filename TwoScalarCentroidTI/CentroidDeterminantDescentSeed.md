# Determinant descent through local centroid modules over the ternary field

Let \(F=\mathbb F_3\). Let \(\beta:U\times U\to Z\) be a symmetric or alternating bimap with zero common radical and spanning image, in the supplied bases. A transporter \((p,t)\) to \(\beta'\) satisfies \(t\beta(x,y)=\beta'(px,py)\). Fix exponents \(a,b\in\{0,1\}\) and prescribe the value of \((\det p)^a(\det t)^b\). The prescribed label sign in an anchored ternary square-zero pencil is the case \((a,b)=(0,1)\): \(Z\) is the dual of the square-zero label radical, and inverse determinants give the same sign in \(F\). [Ternary square-zero normal form](https://github.com/Dugongue/MathProofs/blob/main/TernaryOneSignCongruence/SquareZeroNormalForm.md)

Recover the intrinsic centroid of \(\beta\), and split it into its primitive local factors \(C\). Let \(E\subseteq C\) be the coefficient field, let \(\mathfrak m\) be the nilradical, and put \(\ell=\dim_E C\). For each factor let the tested modules \(M\) be its summand of \(U\) when \(a=1\) and its summand of \(Z\) when \(b=1\). Write \(T_M=M/\mathfrak mM\) and \(r_M=\dim_E T_M\). Let \(L\ge2\) denote the dense input length.

**Theorem.** Fix \(c>0\). A deterministic polynomial-time construction reduces the prescribed sign to one ordinary three-tensor isomorphism instance over \(F\) if every primitive local factor on both inputs satisfies at least one of the following tests.

1. The sum of the tested \(r_M\)'s is even. For each tested \(M\), all kernels
   \[
   K_{M,j}=\ker\bigl((\mathfrak m^j/\mathfrak m^{j+1})\otimes_E T_M
                 \longrightarrow \mathfrak m^jM/\mathfrak m^{j+1}M\bigr)
   \]
   of the natural multiplication maps have \(E\)-dimension at most \(c\log_2 L\). If \(\ell\) is odd, also require \(r_M\le c\log_2 L\) for each tested \(M\). When \(\ell\) is even the top ranks are unrestricted. There is no bound on the cotangent rank, nilpotence index, or degree of \(E/F\).
2. The local centroid is \(E[\epsilon]/(\epsilon^h)\) for some \(h\ge1\). In each tested module only the multiplicities of odd-length cyclic summands need be at most \(c\log_2 L\). The even-length multiplicities, nilpotence index and field degree are unrestricted.
3. Every tested module of that factor has \(E\)-dimension at most \(c\log_2 L\).

The tests are intrinsic and polynomial-time recognizable. There is no bound on the number of local factors or on the number of repeated isomorphic factors. The local construction handles each prescribed sign on the actual transporter, and the primitive-factor assembly uses the full requested signed comparison. This gives a sufficient domain for the ternary determinant reduction in Open Question 1.9. [Chen–Grochow–Qiao–Tang–Zhang](https://arxiv.org/html/2306.03135v2#S1.SS5)

## 1. Recovering the coefficient rings and their module factors

The centroid is the linear solution space of
\[
 \beta(Px,y)=\beta(x,Py)=Q\beta(x,y).
\]
Its operators \((P,Q)\) multiply componentwise. Moving centroid actions across the two slots proves multiplicative closure. For two solutions, evaluate \(\beta(Px,P'y)\) in the two orders. Surjectivity shows \(Q,Q'\) commute, and the zero common radical shows \(P,P'\) commute. Thus the centroid is a finite commutative \(F\)-algebra, and every transporter conjugates its two faithful actions simultaneously. For primitive idempotents \(e_i\) it gives direct-sum factors on \(U\) and \(Z\). The products between distinct factors vanish because \(\beta(e_i x,e_j y)=0\) when \(i\ne j\). Each local bimap is still surjective with zero common radical. [Wilson, bilinear map decomposition](https://arxiv.org/abs/1005.0548)

The cube Frobenius of a commutative algebra here is \(F\)-linear. The stable image under its powers is a product of fields and maps isomorphically onto the product of the residue fields. Indeed a large cube power kills the nilradical and induces a bijection on that product. Its cube-fixed subalgebra is a product of copies of \(F\), one for each primitive factor. To find the primitive idempotents, refine by the indicator \(1-(x-u)^2\) for each basis element \(x\) of the cube-fixed algebra and \(u\in F\). The basis separates factors, there are at most the dimension of the algebra many nonzero simultaneous slots, and each step is linear algebra with explicit multiplication. This also gives each local coefficient field \(E\), and the nilradical is recovered as the kernel of a sufficiently large cube power in the local algebra. All are intrinsic under conjugation. [Prior coefficient-field determinant construction](https://github.com/Dugongue/MathProofs/blob/main/AlpogeTISL/CentroidNormLines.md)

Fix one pair of local factors. Model their fields of the same degree by one fixed \(E/F\), using deterministic finite-field isomorphism; a mismatch is a fixed negative instance. Use \(E\)-bases obtained by linear independence over \(F\), and link the algebra, field, their inclusions and their actions on the original bimap slots by multiplication and module records. Thus an arbitrary extended transporter acts on the two modes as semilinear maps for the same \(\sigma\in\operatorname{Gal}(E/F)\), and its ring map is the actual conjugation \(\alpha:C\to C'\). Faithfulness makes each indicated centroid map the one induced by the bimap transporter. No field automorphism is fixed in advance. [Lenstra, finite-field isomorphisms](https://pub.math.leidenuniv.nl/~lenstrahw/PUBLICATIONS/1991b/art.pdf)

We use a standard small-rank determinant attachment on an \(E\)-space of rank \(q\le c\log_2 L\). The exterior algebra over \(E\), with inclusion of the space and wedge multiplication, forces the action on its top line to be \(u\sigma\), with \(u\) the \(E\)-determinant of the linear part. Make the \(F\)-linear Frobenius copies \(x\mapsto x^{3^i}\) of the top line and link a chain of field multiplications. The last line restricted to \(F\cdot1\) has multiplier \(N_{E/F}(u)\). When \([E:F]\) is even the trace-zero line of the unique quadratic subfield has action \(\det_F\sigma\); this follows from the two-cycle in the quadratic field and the cycle of the full Frobenius on a normal basis. When \([E:F]\) is odd this sign is one. Multiplying by \((\det_F\sigma)^q\) therefore gives the determinant over \(F\) of the original semilinear action in its field-basis frames. The total exterior dimension over \(F\) is \([E:F]2^q\). Both the norm and Frobenius factors are attached to the actual linked field maps, so a certified local sign uses one common transporter. [Norm and trace-zero lines](https://github.com/Dugongue/MathProofs/blob/main/AlpogeTISL/CentroidNormLines.md)

## 2. Cancelling the large local determinants

For a module \(M\) write \(C_j=\mathfrak m^j/\mathfrak m^{j+1}\), \(M_j=\mathfrak m^jM/\mathfrak m^{j+1}M\) and \(T=T_M\). The map
\[
 C_j\otimes_E T\longrightarrow M_j,\qquad \bar v\otimes\bar x\longmapsto\overline{vx}
\]
is well-defined and surjective. Changing \(v\) or \(x\) by the next filtration step changes the product by \(\mathfrak m^{j+1}M\), and the products span by definition. Its kernel \(K_j\) is intrinsic. All these flags, quotients, module actions, product maps and kernels are linked to the original \(M\)-map; they can be computed by linear algebra and products in the displayed centroid. In particular a transporter induces the specified semilinear map on every factor and on every kernel.

Choose \(E\)-bases of \(C_j,T,M_j,K_j\) and use one \(F\)-basis of the fixed field model in all frames. Compute the comparison factor on each exact sequence by concatenating the basis of \(K_j\) with lifts of the basis of \(M_j\) in \(C_j\otimes_E T\). Its determinant over \(F\) is the norm of the corresponding \(E\)-change-of-basis determinant. Also compute the determinants of the adapted radical frame in the original basis of \(M\). These supply known frame ratios in the following formulas. The sequence determinant formula is just block triangularity. In particular if \(D_j,D_j'\) are the source and target adapted exact-sequence frame determinants in the tensor bases, then the determinant on \(M_j\) is the determinant on the domain times \(D_j/D_j'\) divided by the determinant on \(K_j\).

Write \(\sigma\) for the shared field action of the transporter, \(\alpha_j\) for its semilinear action on \(C_j\), \(g_0\) for its action on \(T\), and \(g_{K_j}\) for its action on the kernel. For \(c_j=\dim_E C_j\), \(r=\dim_E T\), the tensor product action has determinant over \(F\)
\[
 (\det_F\alpha_j)^r(\det_F g_0)^{c_j}(\det_F\sigma)^{-c_jr}.
\]
Indeed the linear parts have Kronecker product determinant with exponents \(r,c_j\) over \(E\), followed by the field norm. The coordinatewise semilinear part contributes \((\det_F\sigma)^{c_jr}\) once, whereas the two displayed factors already contribute it twice. Thus, apart from the computed frame ratios, the determinant on \(M\) is exactly
\[
 (\det_F g_0)^\ell
 \left(\prod_j\det_F\alpha_j\right)^r
 (\det_F\sigma)^{-\ell r}\,
 \prod_j(\det_F g_{K_j})^{-1}. \tag{1}
\]
This is an equality of signs on the actual transporters, regardless of the nilpotent corrections to the lifted maps. In particular those corrections do not act as independent sign parameters. The two radical filtrations make the total matrices block triangular, so only their induced layers contribute.

Multiply (1) over the tested modules. The power of \(\prod_j\det_F\alpha_j\) is the sum of the \(r_M\)'s, and the Frobenius factor has exponent \(-\ell\) times that same sum. Both disappear by the parity hypothesis in test 1. The top determinant factors disappear when \(\ell\) is even. When \(\ell\) is odd they are read by the small-rank attachment. All remaining determinants are those on the specified kernels and meet the same rank limit. Thus the local sign, including its calibration, is imposed by linked one-dimensional lines. This gives a single ordinary local query for either sign. The product of the raw frame scalars is computed before the query and contributes only a known input calibration.

## 3. Mixed module lengths over a truncated local ring

A nonfield local centroid \(C\) is of the form \(E[\epsilon]/(\epsilon^h)\) exactly when its cotangent space \(\mathfrak m/\mathfrak m^2\) has dimension one over \(E\). A lift \(\epsilon\) of a nonzero cotangent vector generates \(\mathfrak m\), by iterating \(\mathfrak m=(\epsilon)+\mathfrak m^2\) until the nilpotent power vanishes. Then \(1,\epsilon,\ldots,\epsilon^{h-1}\) give the usual graded basis, where \(h\) is the first power for which \(\epsilon^h=0\). The field case has \(h=1\). This is an intrinsic test, and a generator is used only to fix coordinates. Its map is never pinned.

Let \(T=M/\mathfrak mM\) as above and let
\[
 T_{\le u}=(\operatorname{Ann}_M(\mathfrak m^u)+\mathfrak mM)/\mathfrak mM,\qquad
 L_u=T_{\le u}/T_{\le u-1}.
\]
Use \(T_{\le0}=0\). The dimensions \(q_u=\dim_E L_u\) are the multiplicities of cyclic blocks of length \(u\): view multiplication by \(\epsilon\) as a nilpotent \(E\)-matrix, and inspect each Jordan chain. Its top vector appears in \(T_{\le u}\) precisely when its length is at most \(u\). The flags are intrinsic under the ring and module maps. In the chosen local coordinates the residue multiplier of the cotangent action is \(\lambda\), so
\[
 \alpha(\epsilon)\equiv\lambda\epsilon'\pmod{\mathfrak m'^2}.
\]
It is read from the actual one-dimensional \(E\)-space \(\mathfrak m/\mathfrak m^2\), where the map is \(\lambda\sigma\). The same Frobenius-product construction extracts \(N_{E/F}(\lambda)\). When \(h=1\) there is no cotangent term.

For each \(j\), multiplication by \(\epsilon^j\) gives the surjection \(T\to\mathfrak m^jM/\mathfrak m^{j+1}M\) with kernel \(T_{\le j}\), again by inspecting each nilpotent chain. The target acquires the flag with successive spaces indexed by \(u>j\). On the space corresponding to \(L_u\), the induced semilinear map in these identification frames is \(\lambda^j g_u\), where \(g_u\) is the actual semilinear map on \(L_u\). This follows from \(\alpha(\epsilon^j)\equiv\lambda^j\epsilon'^j\bmod\mathfrak m'^{j+1}\). Therefore, multiplying over the radical layers and these inner flags, the determinant is exactly
\[
 \det_F(g_M)=
 N_{E/F}(\lambda)^{\sum_u q_u u(u-1)/2}
 \prod_u(\det_F g_u)^u \tag{2}
\]
in the adapted frames. Frames in the original bases are obtained by first choosing \(E\)-bases for the \(L_u\), lifting them to the indicated tops, and then using their \(\epsilon^j\)-images in the successive radical layers. The ratio of the determinants of these two full frames gives the exact raw calibration. The field-semilinear sign is already included in each \(\det_F g_u\); no additional sign is needed.

Because the base field is ternary, only odd \(u\) can contribute a \(g_u\)-determinant. Their ranks are within the stated bound. Thus the norm of the single cotangent multiplier and these small-rank attachments read (2), including for arbitrary large even-length multiplicities and for mixed length modules. For test 3 the direct small-rank attachment to \(M\) suffices.

## 4. Primitive-factor assembly in one ordinary comparison

Every local test gives a polynomial-size family of linear and bilinear records, with the original bimap and all used maps fixed as records. A local transporter of the desired sign lifts to the induced maps and to precisely its readout signs. Conversely the records force all used actions on quotients, kernels, and linked scalar lines, so the projected transporter has the desired sign. Named roles and copy maps can be packed into a constant-size tensor-system signature and hence one ordinary TI comparison. The number of centroid filtration grades and the dimensions of the ring and all spaces are polynomial in \(L\), and the largest exterior cost is \([E:F]2^{c\log_2 L}\) per space. [Fixed-signature tensor-system reduction, Theorem 4.1](https://arxiv.org/html/2306.03135v2#S4)

For explicit packing, take the direct sum of the named roles and a second direct sum with one separate copy for every map-slot occurrence. Use the split coordinate algebra of role labels with a module of distinct positive multiplicities to pin its idempotents. Its action on the sums marks the summands, and the incidence map from the occurrence sum to the role sum ties each copy to the same actual transporter. Store the linear and bilinear records on the appropriate occurrence blocks in a constant number of arrays, using a fixed scalar role for lower orders. The two input places of the original bimap link to the same role \(U\). This supplies the constant-size signature to which the prior theorem applies and never enlarges the number of independent transporter maps.

Use the prior ternary primitive-factor assembly to pass from these local sign tests to a single comparison even for unrestricted repetitions. Its parity argument applies to an arbitrary fixed binary determinant character on a fixed-arity direct sum. Here a component carries the weighted dimension \(a\dim_F U_i+b\dim_F Z_i\). Interchanging two equally typed components contributes the parity of that dimension, since the two local transfer determinants used in the interchange cancel. The original order of the input bases contributes the separately computed frame ratio. [Primitive-factor assembly for repeated types](https://github.com/Dugongue/MathProofs/blob/main/TISLWorlds500/prior/prior/PrimitiveAssembly.md)

For clarity, the assembly uses an ordinary guard for the full pair, and source-to-source local tests to recognize a sign-changing self-map or two ordinarily isomorphic odd-weighted components. The latter gives a sign-changing swap. When the guard holds and either exists, any global transporter can be corrected to either sign. Otherwise local signs are rigid, all odd-weighted component types are distinct, and the odd-block matching is the unique permutation determined by ordinary equivalence. The prior query-dependent determinant compiler reads its sign using the ordinary comparisons as entries; competitors in a row are their complements on this guarded rigid domain.

For the product of local signs in the same domain, take one binary variable for each candidate source–target component pair and sign, enabled by its corresponding local signed comparison. Require that each source and each target occurs an odd number of times and that the parity of selected negative signs be the prescribed bit. The prior linear-switch compiler imposes these equations in one ordinary query. To verify the incidence step, inside each ordinary type choose a conceptual reference component. Rigidity makes the sign on each enabled pair a product of the reference signs at its two endpoints. Each odd-incidence solution therefore has the same sign product as any actual matching, and a matching exists by the ordinary guard. This avoids choosing a matching before the query. Combine the two possible odd-block permutation signs with the complementary local sign targets, then the flexibility branch and ordinary guard. The prior positive AND and OR packing yields one polynomial-size ordinary TI instance. This applies to both symmetric and alternating bimaps because the signs and the decomposition argument concern only the transported module roles. In particular it uses the same raw bimap congruence and the label map it determines, and the class is closed under the comparisons between source summands needed by the compiler.

## 5. Wide examples and exact ring thickening

The first criterion allows a large, noncurvilinear centroid and a large nonfree label module with nontrivial local sign. Let \(C=F[\epsilon_1,\ldots,\epsilon_{2d+1}]/(\epsilon_i\epsilon_j:1\le i,j\le 2d+1)\), with \(d\ge1\). Choose a one-dimensional ideal \(D\) in its square-zero radical and put \(M=C^{r-1}\oplus C/D\) for an arbitrary even \(r\ge2\). The label module has top rank \(r\), and \(C\) has even length \(2d+2\). Its only nonzero multiplication kernel of Section 2 is \(K_{M,1}\), of dimension one. For an alternating example use \(U=C\oplus M\) and
\[
 \beta((u,x),(v,y))=uy-vx.
\]
Replace the minus by plus for a symmetric example. This bimap spans \(M\), and its common radical is zero because \(M\) is faithful, containing a free summand. The centroid is exactly \(C\). Indeed for a centroid action \((P,Q)\), testing \((1,0)\) against \((0,y)\) forces \(Qy=\gamma y\) for the first component \(\gamma\) of \(P(1,0)\). Then the zero common radical forces \(P=\gamma\) on both input summands. Scaling \(D\) by \(-1\) and fixing a radical complement is a ring automorphism, and its induced semilinear action on \(M\) has determinant \(-1\) by (1). Thus a genuinely varying sign on a wide nonfree label module is read on a single relation line.

For the second criterion, let \(C=F[\epsilon]/(\epsilon^4)\) and \(M=C^r\) with \(r\) arbitrarily large, including odd \(r\). The same bimap has centroid \(C\). All cyclic summands have length four, and the norm exponent in (2) is \(6r\). Hence every self-transporter has label determinant one. Composing the output with any fixed determinant-\(-1\) change of basis gives an ordinary equivalent target whose transporters all have label determinant \(-1\). The signed reduction can therefore distinguish comparisons within the same ordinary orbit, also when the large top rank is odd.

More generally the ring construction gives exact descent for thickening an arbitrary symmetric or alternating bimap with reduced centroid. Let \(C_0\) be its centroid, assume \(C_0\) is reduced, and replace \(\beta\) by its scalar extension over \(D_h=F[\epsilon]/(\epsilon^h)\), regarded again as an \(F\)-bimap. Its centroid is \(C_0\otimes_F D_h\). In fact the scalar \(D_h\)-actions already lie in the centroid. Commutativity forces every centroid map to be \(D_h\)-linear. The resulting linear kernel over \(D_h\) is just the base change of the \(F\)-kernel, by flatness over \(F\). Since \(C_0\) is a product of fields, the nilradical is \(C_0\otimes(\epsilon)\), and quotienting by its actions on both roles gives the original bimap. Every thickened transporter descends, and any original transporter lifts by scalar extension.

In the frames ordered by \(\epsilon\)-layers, a thickened transporter with residue mode map \(\bar g\) has determinant
\[
 \det_F g=(\det_F\bar g)^h
      \left(\det_F(\lambda\mid M_{\mathrm{red}})\right)^{h(h-1)/2},
\]
where \(\lambda\) is the unit of the target reduced centroid for which \(\alpha(\epsilon)=\lambda\epsilon\bmod\epsilon^2\), and \(M_{\mathrm{red}}\) is the corresponding original mode. Indeed the induced map on layer \(j\) is \(\lambda^j\bar g\). This formula already incorporates permutations of the residue factors. For \(h\equiv1\bmod4\) the determinant on each role equals its residue determinant. For \(h\equiv0\bmod4\) every thickened transporter has determinant one on both roles, even if the residue map has either sign. In the latter case the ordinary residue comparison embeds into this theorem's signed class with no rank bound on any free module or number of repeated factors.

These are written proofs of the stated sufficient classes. They do not impose a general logarithmic bound on label dimension, but the unrestricted large-rank case of scalar centroid is not covered by these ring criteria.
