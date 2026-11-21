# One directional query for an ordinary tensor-isomorphism difference

The directional promise problem \(D_1\) over \(\mathbb F_3\) is defined for an ordinary-isomorphic pair by
\[
D_1(T,U)=[e_1\in P(T,U)\text{ and }0\notin P(T,U)],
\]
where \(P\) is the determinant-bit profile and \(e_1=(1,0,0)\). A reflection of bits \(w\) on the target adds \(w\) to this profile. Let \(B\) denote ordinary ternary TI and let \(A\) denote the determinant-one version.

## One instance with an explicit ordinary witness

**Theorem.** For any two ordinary TI queries \(x,y\), there is a deterministic polynomial-time map to one concise pair \(z\) with an explicit ordinary transporter and
\[
D_1(z)=[x\in B]\wedge[y\notin B].
\]
The tensors in \(z\) are reflected copies of the same tensor. The reflection has one negative coordinate in mode 2 and one in mode 3. In particular the construction evaluates the Boolean difference of two independent ordinary TI queries in one directional call. No ordinary complement compiler is required.

More generally the two input predicates may be existence of an odd algebra automorphism for each of two supplied even-dimensional commutative local algebras with residue \(\mathbb F_3\). The tensors remain concise and the two local coefficient algebras are recovered intrinsically as the centroid factors. For ordinary TI input queries the coefficient algebras can both have cube-zero radical.

### Scalar-centroid coefficient carriers

Write \(k=\mathbb F_3\). A bilinear map \(\beta:X\times Y\to Z\) is concise here if its common radicals in \(X,Y\) vanish and its products span \(Z\). Its centroid consists of triples \(C=(C_X,C_Y,C_Z)\) satisfying
\(\beta(C_Xx,y)=\beta(x,C_Yy)=C_Z\beta(x,y)\).
For concise \(\beta\) the centroid is commutative. In fact the products span \(Z\) and
\[
C_ZD_Z\beta(x,y)=\beta(C_Xx,D_Yy)=D_ZC_Z\beta(x,y).
\]
The zero radicals then give commutation in \(X\) and \(Y\). Each of the three centroid projections is faithful, by the same two conditions.

Let \(R\) be a finite-dimensional commutative \(k\)-algebra with identity and let \(f:k^a\times k^b\to k^c\) be concise with scalar centroid. The relative bimap \(f_R:R^a\times R^b\to R^c\), viewed over \(k\), is concise. Indeed the span and kernel conditions are exact linear equations over \(k\) and extend to \(R\). Coordinatewise multiplication embeds \(R\) into the centroid. Every centroid element commutes with this \(R\)-action, so its maps are \(R\)-linear. The \(R\)-linear centroid equations are obtained from the \(k\)-linear equations for \(f\) by extension of scalars. Their solution module is therefore exactly \(R\).

If an ordinary transporter maps \(f_R\) to \(f_S\), conjugation on the centroid gives a unital \(k\)-algebra isomorphism \(\phi:R\to S\). The three maps are semilinear with respect to \(\phi\). Applying \(\phi\) coordinatewise gives a canonical transporter and leaves an \(S\)-linear automorphism on each free mode. For a scalar-residue local algebra \(S\) of even dimension, every \(S\)-linear automorphism of \(S^j\) has \(k\)-determinant one. On each grade of its radical filtration the map is a direct sum of copies of the same reduction matrix in \(\mathrm{GL}_j(k)\). Their product determinant is \((\det \overline M)^{\dim_k S}=1\). Consequently the full determinant profile is precisely
\[
\{(a\epsilon,b\epsilon,c\epsilon):\epsilon\in\det_{\rm bit}\operatorname{Iso}(R,S)\},
\]
where dimension coefficients are taken modulo two. Every underlying \(\phi\) lifts.

### Two independent sign directions

Use two concise scalar-centroid templates. The first is multiplication on \(k\), of format \((1,1,1)\). The second, of format \((2,3,3)\), is
\[
((x_1,x_2),y)\longmapsto (x_1 I+x_2 \Delta)y,\qquad
\Delta=\operatorname{diag}(0,1,-1).
\]
To check the second centroid, let \((P,Q,M)\) be a centroid element. Evaluating at \((1,0)\) shows \(M=Q\in\langle I,\Delta\rangle\). Evaluating at \((0,1)\) shows \(M\Delta\in\langle I,\Delta\rangle\). The matrices \(I,\Delta,\Delta^2\) are independent, so \(M,Q\) are scalar. The zero left radical then forces \(P\) to be the same scalar. Conciseness holds since a slice is the identity and the slices are independent.

Apply the first template over \(R\) and the second over \(S\), then take their direct sum \(T\). The centroid is \(R\times S\). The two coordinate projections already belong to the centroid, so every centroid map preserves each block by commutativity and the centroid splits. In an ordinary automorphism of \(T\), the two primitive centroid factors cannot be exchanged, since the first factor has all three format dimensions equal and the second has proportions \(2:3:3\). Thus its sign subgroup is exactly
\[
\{\epsilon d+\eta v:
\epsilon\in\det_{\rm bit}\operatorname{Aut}(R),\
\eta\in\det_{\rm bit}\operatorname{Aut}(S)\},\qquad
d=(1,1,1),\quad v=(0,1,1).
\]
The identity is always available in both groups. The pair \(z=(T,r_vT)\) has the coordinate reflection as a witness and its sign profile is the displayed subgroup translated by \(v\). The vectors \(d,v\) are independent and \(d+v=e_1\). Thus \(e_1\) belongs to the profile exactly when \(R\) has an odd automorphism, and \(0\) belongs exactly when \(S\) does. This proves the result for the two arbitrary coefficient algebras.

### Turning each ordinary input into an odd-automorphism switch

Use the already explicit odd-dimensional parity-rigid algebra \(C_T\) for an ordinary tensor \(T\). For a matching pair \(x=(T,U)\), \(C_T\times C_U\) has an odd automorphism exactly when \(x\in B\), via swapping its odd-dimensional factors. The total sign of any autotopism of the multiplication tensor of an associative unital algebra is the sign of its unital automorphism: in the formula \((L_a\phi,R_b\phi,L_aR_b\phi)\), each unit sign occurs twice in the product. Apply the weighted cube-zero character construction to this **self** comparison with weight \((1,1,1)\). Its even-dimensional commutative local output \(R_x\) has residue \(k\) and odd automorphism available exactly when \(x\in B\). Preprocess malformed or unequal-format inputs to a fixed ordinary-NO pair. If the convention permits zero side lengths, preprocess matching formats with a zero side to a fixed ordinary-YES pair. All constructions are deterministic polynomial time and therefore give the displayed ordinary-query theorem. [Parity-rigid product switch and weighted construction](https://github.com/Dugongue/MathProofs/blob/002a1088187a6f9e08e08b3c4fe5d20ba53bee15/TISLDirectionalGap/RESULTS.md)

## Refinement to one local centroid

The simultaneous-character readout in the companion theorem gives a second construction whose centroid itself is local. For the two ordinary TI queries, make the ordinary two-factor switches independently. Each is a product of two ordinary tensor algebras with an attached two-point split algebra recording the factor idempotents. Call the two determinant bits on the two-point algebras \(s\) and \(t\). Then \(s=1\) is available exactly when \(x\in B\), and \(t=1\) exactly when \(y\in B\), independently.

Put these two systems into one fixed typed signature. To encode any noncommutative algebra product, use one extra tagged copy of its right input space and an identity link so every repeated-input bimap is symmetric. The weighted cube-zero construction applies to this fixed signature. Its role extraction and common pin scale use one independent tag for each named variable, one pin for each linear link, and at most one bilinear block per unordered pair of source roles. The same quotient-line sign calculation uses the chosen role weights on this fixed list, so it remains valid for these two marked switches. Use the companion readout with characters \(s,s+t,s+t\). Its concise single-local-centroid tensor has precisely the same subgroup \(\{s d+t v\}\) and hence the same directional comparison with an explicit reflector. The two local coefficient factors in the elementary proof are therefore dispensable for the ordinary-input version. [Two-point switches](https://github.com/Dugongue/MathProofs/blob/002a1088187a6f9e08e08b3c4fe5d20ba53bee15/TISLDirectionalGap/Aggregate.md) · [Simultaneous-character proof](complexity.md)

## Consequences for reduction degree

Let \(\mathrm{Diff}(B)=\{(x,y):x\in B,\ y\notin B\}\). The reduction \(\mathrm{Diff}(B)\le_m^P D_1\) is unconditional and always lands in the promise. If \(A\le_m^P B\), it is a degree equivalence: compute the two ordinary instances for \(A(r_{e_1}z)\) and \(A(z)\) and return their pair in \(\mathrm{Diff}(B)\). This reverse map uses the signed collapse alone. It extends to the total language that declares ordinary-negative inputs directional NO. In particular, if \(B\) is NP-complete, the total directional language is DP-complete and the hardness outputs have explicit ordinary witnesses. DP membership follows directly from the two NP predicates in the definition.

Composing with the guarded integer path-sum compiler gives one directional query that tests whether the first of two supplied weighted programs has positive path sum and the second has nonpositive path sum, when their input guards are supplied as complementary TI queries. No complement map on all ordinary TI instances enters that composition. [Guarded path-sum compiler](https://github.com/Dugongue/MathProofs/blob/002a1088187a6f9e08e08b3c4fe5d20ba53bee15/TISLWorlds500/Complexity.md#c08-one-ordinary-test-for-the-sign-of-a-guarded-integer-path-sum)
