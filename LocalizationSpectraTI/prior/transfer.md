# A directional gap is an exact one-localization defect of ordinary tensor isomorphism

Let \(A_v(x)\) test whether a framed tensor pair in a common positive format over \(\mathbb F_3\) has a transporter with determinant tuple \(v\). Write \(0=(1,1,1)\), \(e_1=(-1,1,1)\), and \(D_1(x)=A_{e_1}(x)\wedge\neg A_0(x)\). This paper proof uses the ordinary free three-module tensor action in the target.

## The exact transfer

For each of the following two fixed ring inclusions there is a deterministic polynomial-time map \(x\mapsto (F_0(x),F_1(x))\) to **one pair of free three-tensors over \(R\)**:
\[
\mathbb Z\ \subset\ \mathbb Z[1/2],
\qquad
\mathbb F_3[t]\ \subset\ \mathbb F_3[t,1/(t^2+t+2)].
\]
Write \(R'\) for the localized ring in the chosen inclusion. For the same output pair,
\[
\begin{aligned}
 F_0(x)\cong_R F_1(x)&\ \Longleftrightarrow\ A_{e_1}(x)\wedge A_0(x),\\
 F_0(x)\cong_{R'} F_1(x)&\ \Longleftrightarrow\ A_{e_1}(x).
\end{aligned}
\]
Consequently \(D_1(x)\) is exactly failure of ordinary \(R\)-isomorphism repaired by this single specified localization. The map supplies one arithmetic tensor pair and does not turn the two sides into unrelated ordinary queries.

A uniform version uses the fixed domains
\[
R=\mathbb F_3[t,s],\qquad R'=R[1/(s^2+s+2)].
\]
Here the input field \(K=\mathbb F_3[t]/(f(t))\) is explicitly given by a monic irreducible \(f\), with arbitrary degree. The same two equations hold for prescribed determinant tuples \(0,e_1\) in \(K\), interpreted as the literal units \(1,-1\). In fact any monic nonconstant \(f\) is permitted if the source is the free-module comparison over the finite quotient rather than necessarily a field. No factoring of \(f\) is required in construction. On these two-variable outputs the ordinary comparison succeeds over every height-one localization of \(R\), on every input. The \(R'\) comparison still detects \(A_{e_1}\) exactly.

There is also a single characteristic-zero ring inclusion for **all explicitly presented finite fields, all characteristics, and any two prescribed determinant tuples**:
\[
 S=\mathbb Z[t,s,r_1,r_2,r_3],
 \qquad S'=S[1/(r_1r_2r_3)].
\]
For the two given tuples \(\alpha,\beta\), the same construction with the screens below gives global ordinary equivalence exactly for \(A_\alpha(x)\wedge A_\beta(x)\), and localized equivalence exactly for \(A_\alpha(x)\). Every localization at a prime of height at most five gives ordinary equivalence on every output pair. No multiplicative generator of the residue field is required.

For the three maps, the roles of \(A_{e_1}\) and \(A_0\) can be replaced by any two prescribed determinant tuples whose coordinatewise ratios are \(1\) or \(-1\). Over \(\mathbb F_3\) this includes every directed difference on the sign cube.

## A free congruence diagram

Use a tensor as a bilinear map \(X\times Y\to Z\), so a transporter consists of three invertible role maps with a linked product on \(X\otimes Y\). Inverting a determinant under the dual convention does not change \(1\) or \(-1\). Let \(I,J\) be comaximal ideals of a commutative domain \(S\), given by finite generator lists. We will use the following diagram for a comparison \(T,U\) over \(S/I\). The role maps must reduce to a transporter at \(I\) and reduce to the identity at \(J\).

Use free lifts of the three original roles. Write \(P=X\otimes_S Y\) for a named free module, and include the tensor-product bimap. It forces the map of \(P\) to be the tensor product of the first two role maps. On \(P\oplus Z\) include its two named inclusions. The map of the sum is therefore the block sum of the written role maps. If \(I=(a_1,\ldots,a_\ell)\), represent the full inverse image of the graph of \(T:P/IP\to Z/IZ\) by the free map
\[
(p,z_1,\ldots,z_\ell)\longmapsto
  (p,\widetilde T(p)+a_1z_1+\cdots+a_\ell z_\ell).
\]
The source is free even when the graph submodule itself is not. Preservation with an invertible domain map implies equality of graph images, hence precisely the tensor congruence. Conversely suppose named maps \(G_P,G_Z\) preserve the congruence. Write
\[
G_Z\widetilde T-\widetilde U G_P=\sum_j a_jD_j
\]
entrywise. The free-domain map on the displayed graph is
\[
 (p,(z_j)_j)\longmapsto (G_Pp,(G_Zz_j+D_jp)_j).
\]
It is invertible by its triangular form and supplies the required commuting arrow. Thus equality of the graph images imposes exactly the congruence in both directions.

For each original role \(V\), add a separate copy \(V_*\) pinned at every basis vector. Its map is the identity. Include the two inclusions into \(V_*\oplus V\) and the graph of the identity modulo \(J\), with the same free-cover construction. This forces the original role map to be identity modulo \(J\). A basis vector can be marked by a linear map from one shared scalar line. Its map on both sides is pinned to one by including the multiplication tensor on this rank-one module. No unknown maps on the two independent comparison diagrams are identified by this shared fixed line.

In the constructions below, write \(E=S/I\), and let
\[
\mathcal U_{S,I,J}
 =\{u\bmod I:u\in S^\times,\quad u\equiv1\bmod J\}
 \ \subseteq (S/I)^\times.
\]
The diagram isomorphisms exist precisely when the residue tensors admit a transporter with each determinant belonging to \(\mathcal U_{S,I,J}\). For necessity, apply the determinant to a role map. For sufficiency, choose an allowed unit \(u\) realizing the required determinant in each mode. Divide the residual role map by \(\operatorname{diag}(u\bmod I,1,\ldots,1)\) on the left. The remaining residual map is special-linear. It lifts by elementary matrices with off-diagonal coefficients congruent to zero at \(J\), by CRT. The rings \(E\) used below are fields or products of finite local principal rings, over which elementary matrices generate the determinant-one subgroup: a unimodular column over a local factor has a unit entry, elementary elimination reduces to diagonal unit pairs \(\operatorname{diag}(a,a^{-1})\), and such pairs are elementary products. CRT combines the factorwise products with independent support. The rank-one special-linear group is trivial. Restore \(\operatorname{diag}(u,1,\ldots,1)\), then lift the graph-domain arrows as above.

For the stated field inputs, lifting a supplied transporter is constructive in polynomial time with the corresponding displayed units. Gaussian elimination gives a polynomial-size elementary list. Its coefficients lift by small integer CRT or the polynomial interpolation specified below. Over a finite polynomial quotient one can obtain the same witness bound by deterministic fixed-characteristic factoring of the modulus and the local CRT proof. The comparison construction itself does not need this factoring. For principal ideals the coefficients \(D_j\) are found by exact division. For \((f(t),s-a)\), evaluate a numerator at \(s=a\), divide that value by the monic \(f\), and divide the remaining difference by \(s-a\). If working in the localization, denominators are powers of the explicitly inverted polynomial, whose image is a unit modulo the ideals. Clear these denominators first. These are polynomial-size coordinate calculations for the lifts constructed here. Reflection from a linked transporter is just restriction and reduction of its role maps.

## The selective determinant screens and the two independent diagrams

For the two-variable construction put
\[
 I=(f(t),s),\qquad J_{\mathrm{keep}}=(f(t),s+1),\qquad
 J_{\mathrm{relax}}=(f(t),s-1),\qquad u=s^2+s+2.
\]
The three ideals are pairwise comaximal, since their displayed degree-one polynomials in \(s\) have pairwise unit differences. They each have quotient \(K\). Over \(R\) every unit is \(1\) or \(-1\), and either pin forces that unit to be one. Thus both screens have image \(\{1\}\). The polynomial \(u\) is irreducible over \(\mathbb F_3[s]\) by checking its three possible roots, and remains irreducible in \(\mathbb F_3[t,s]\) because it has degree zero in \(t\). The units of \(R'\) are exactly \(\pm u^k\), \(k\in\mathbb Z\), by unique factorization. At \(s=0,-1,1\), respectively, \(u\) has values \(-1,-1,1\). A unit congruent to one at \(J_{\mathrm{keep}}\) therefore still reduces to one at \(I\). At \(J_{\mathrm{relax}}\), the unit \(u\) itself reduces to one and reduces to \(-1\) at \(I\). Hence the two determinant images in \(K^\times\) are exactly \(\{1\}\) and \(\{1,-1\}\). Off-diagonal elementary coefficients can be lifted uniformly by multiplying an \(\mathbb F_3[t]\) representative by \(1-s^2\), which is one at the data place and zero at both pins.

For the one-variable version use \(I=(t)\), \(J_{\mathrm{keep}}=(t+1)\), \(J_{\mathrm{relax}}=(t-1)\), and \(u=t^2+t+2\). The same evaluation and unit-group proof applies. For \(R=\mathbb Z\) use \(I=(3)\), \(J_{\mathrm{keep}}=(11)\), and \(J_{\mathrm{relax}}=(5)\). Both screens force a global sign \(+1\) since the only integral units are signs. In the localization the units are \(\epsilon 2^k\). Since \(2\) has order ten modulo eleven and \(2^5=-1\bmod11\), the keep-pin condition forces \(k=5j\) and \(\epsilon=(-1)^j\). Reduction modulo three then gives \((-1)^{j+k}=1\). For the relax pin the unit \(-4\) is \(1\bmod5\) and \(-1\bmod3\), so its image has both signs. All masks and unit representatives have constant size in the one-variable and integral versions.

For the **first independent diagram**, use the input pair \(x\) with its target reflected in the first mode, and the keep pin. Its ordinary diagram comparison over both rings tests \(A_{e_1}(x)\). For the **second independent diagram**, use \(x\) without reflection, with the relax pin. Over \(R\) that tests \(A_0(x)\). Over \(R'\) it allows any of the three determinant signs independently among \(\{1,-1\}\). Whenever the first diagram is soluble the original tuple \(e_1\) already satisfies this second condition, including when the residue field has other units. Consequently the conjunction over \(R'\) is exactly \(A_{e_1}\). The conjunction over \(R\) is exactly \(A_{e_1}\wedge A_0\). This also verifies the variant for two prescribed tuples whose ratios are signs, by absorbing each prescribed unit into the corresponding target frame.

Both diagrams are packed together as one ordinary tensor comparison as follows. Formats with a zero side or unequal input shapes give a negative directional answer whenever regarded as fixed-language inputs. For a total language reduction they can be sent to a fixed identical tensor pair, which has no localization defect. The two exact formulas are stated on common positive formats.

## Ordinary free-tensor packing and base change

Here is a direct linked-system packing over all the stated domains. Take the direct sum \(W\) of a master space for every named free module and private copies for their occurrences. Add two symbols \(e_1,e_2\) with quotient multiplication \(e_i e_j=\delta_{ij}e_i\), and give each zero right action by \(W\). On the left let \(e_1\) act by an operator \(L_1\) with a different nonzero scalar \(c_i\ne1\) on each slot. Integer labels \(i+2\) suffice in characteristic zero. In characteristic three, use distinct positive powers of the polynomial localization variable, which remain distinct in all the domains used. Let \(e_2\) act by a nilpotent \(L_2\) containing each master-to-occurrence identity link and each private linear constraint. They form paths of length at most two. Define products within \(W\) by the given bilinear maps on private slots, and zero on other pairs. All these products lie in private output slots \(W_1\), which kill all further \(W\)-products and satisfy \(L_2W_1=0\). Marks were linear maps from the fixed scalar line. The result is a possibly nonassociative free algebra table.

Over any of these domains \(W\) is the largest nilpotent ideal, since every nilpotent ideal has zero image in the diagonal quotient \(S^2\). The two quotient idempotents have unique idempotent lifts: a lift \(e_i+w\) would give \((I-L_i)w=w^2\in W_1\), forcing its image in \(W/W_1\) to vanish by injectivity over the domain. Since \(L_i\) preserves \(W_1\), the same equation then gives \(w=0\). The left actions distinguish the tags by nilpotence versus nonnilpotence, and the distinct labels of \(L_1\) force every slot to be preserved. The \(L_2\) equations link the same maps across their master and private slots and impose each original linear constraint. The product equations impose each bimap separately. Conversely all given linked isomorphisms extend on the assigned slots and the two fixed tags. The construction depends only on the written tables and uses the same coefficients before and after localization.

For completeness, an algebra isomorphism comparison over a commutative ring is directly a fixed-partition tensor comparison. Use a copy of \(W_*=S e_1\oplus S e_2\oplus W\) plus one scalar line in every mode. On the three big parts write the algebra product. The two big-small products are the canonical scalar actions with values in the big output, and the small-small product is scalar multiplication with values in the small output. Write \(P,Q,H\) for the three mode maps on the big parts and \(\alpha,\beta,\gamma\) for the scalar actions. The last three equations force \(H=\alpha Q=\beta P\) and \(\gamma=\alpha\beta\). The algebra-product equation becomes exactly the algebra-isomorphism identity for \((\alpha\beta)^{-1}H\). Conversely an algebra isomorphism gives such a partitioned transporter with all scalars one.

Erase the constant block partitions using the raw identity-slice construction of Grochow–Qiao–Stange–Sun, Theorem 3.12 in §3.3.2. All of these rings are domains and hence satisfy its diagonal-full hypothesis. One can erase the partitions successively, retaining the original partitions of as-yet unprocessed modes and appending an aggregate part for their new marker coordinates. The proof extracts the original blocks of the two unprocessed mode maps, so their restrictions respect the retained partitions. In the forward direction the construction extends the two source maps block diagonally on the original and new spaces, again respecting those partitions. The number of parts is bounded by a constant, so the raw construction is of polynomial size. Its operations copy the data blocks and adjoin fixed zero and identity matrices, and the same formulas and correctness proof apply over the localized domains. This gives one pair of plain free three-tensors, with no marked actions in the target. [Grochow–Qiao–Stange–Sun, Theorems 3.7 and 3.12](https://arxiv.org/html/2611.00735v1#S3.SS3)

The sizes and all written coefficient data are polynomial in the source encoding. Reflected entries are changes of sign in a known block, the degree of \(f\) occurs only as polynomial coefficient data, and the tag exponents are bounded by the polynomial number of slots. With the format and layout supplied, each raw free output's original graph data can be extracted from the copied tensor blocks, the algebra table, and the specified private linear arrow. In a fixed ambient ring one can also recognize the bare coordinate image by enumerating the three input side lengths bounded by the output size, extracting the modulus \(f\) from its designated graph-generator coefficient when variable, and verifying by re-encoding. Layouts depend on the three positive side lengths and the ring construction, not on the data coefficients or on \(\deg f\) in the two-variable version. If several formats produce the same bare pair, the localization difference forces the same directional bit for all verified preimages. This supplies a polynomial decoder back to the directional problem on the explicit coordinate image. It is not a decoder from arbitrary arithmetically isomorphic presentations.

## A uniform characteristic-zero lift for arbitrary determinant directions

For an input \(K=\mathbb F_p[t]/(f(t))\) and two literal tuples \(\alpha,\beta\in(K^\times)^3\), compute \(\delta_j=\alpha_j\beta_j^{-1}\) by elementary field arithmetic. Use canonical integer coefficient lifts \(\widetilde f,\widetilde\delta_j\). In the fixed polynomial ring \(S\) from the theorem let
\[
\begin{aligned}
 I&=(p,\widetilde f,\ r_j-\widetilde\delta_j\ (1\le j\le3),\ s),\\
 J_{\mathrm{keep}}&=(p,\widetilde f,\ r_j-\widetilde\delta_j\ (1\le j\le3),\ s-1),\\
 J_{\mathrm{relax}}&=(p,\widetilde f,\ r_j-1\ (1\le j\le3),\ s-1).
\end{aligned}
\]
Each quotient is the same given field \(K\). Each pin is comaximal with \(I\), because \(s\) and \(s-1\) have difference one. The pins play roles in separate diagrams and do not require comaximality with each other. The monomial \(r_1r_2r_3\) reduces to a unit at every displayed ideal. Its inversion in the unique factorization domain \(S\) makes the units of \(S'\) exactly
\[
\epsilon r_1^{k_1}r_2^{k_2}r_3^{k_3},
\qquad \epsilon\in\{1,-1\},\quad k_j\in\mathbb Z.
\]
The keep pin and the data ideal give identical values for all these units, hence the permitted keep determinant remains one. The relax pin sends all \(r_j\) to one, so its permitted determinant subgroup at the data ideal is \(\langle\delta_1,\delta_2,\delta_3\rangle\). The possible sign \(\epsilon\) adds nothing: at an odd prime it must reduce to one at the pin, and at characteristic two it already equals one in \(K^\times\). The global unit group of \(S\) is \(\{1,-1\}\), so both global screens force determinant one in \(K\).

Use the \(\alpha\)-reflected target in the keep diagram and the \(\beta\)-reflected target in the relax diagram. Here a target reflection for a prescribed tuple means applying a diagonal target map of determinant tuple its inverse, in the chosen bimap convention. It is performed on the residue tensor before lifting coefficients and does not require a corresponding unit determinant in \(S\). The first comparison tests \(A_\alpha\) in both rings. The second tests \(A_\beta\) globally, and it passes after localization whenever \(A_\alpha\) holds, since the latter supplies the residual determinant ratios \(\delta_j\). In constructing that lift, use \(r_j\) in the \(j\)-th mode as its explicit correction unit. This proves the two exact formulas.

For explicit witness lifting, a residual elementary coefficient can be represented by \(\widetilde c(t)(1-s)\), which has the correct value at \(I\) and is zero at each pin. Given an entry in a graph ideal, first subtract its evaluation at the designated values of \(s,r_1,r_2,r_3\), recording each difference as the appropriate linear generator times a polynomial. Divide the remaining polynomial in \(t\) by \(f\) modulo \(p\), then the leftover integer coefficients are multiples of \(p\). In \(S'\) one first clears the \(r_j\)-denominators, each of which is a unit at the ideals. Over a variable prime the source witness elimination is over the given field \(K\), so there is no factorization or primitive-element search requirement. These operations take polynomial time on the displayed lifts, whose polynomials have bounded numbers of variables and polynomial degrees and coefficient bit sizes. The construction itself merely writes the free covering maps and fixed typed blocks. The same packing gives one plain ordinary tensor pair over \(S\) with identical coefficients used over \(S'\).

Each ideal displayed above is maximal of height six. One may see the height by successively imposing \(p,f\), the three monic linear coordinate conditions in \(r_j\), and the last linear condition in \(s\); the successive quotients are domains. No prime of height at most five contains any one of the ideals. All congruence conditions are therefore trivial after any one of those localizations, and the produced tensors are ordinarily isomorphic at every such localization. All maximal localizations pass exactly when the original residue pair is ordinary YES, by the same argument as for the two-variable construction. If the two pin ideals happen to coincide, the two role sets are nevertheless independent and can both use the identity at that localization. Neither pin can survive at the data maximal ideal. This proves the stated locality for the arbitrary-field carrier.

## Height-one behavior and the exact fixed-field consequence

For the two-variable ring the ideals \(I,J_{\mathrm{keep}},J_{\mathrm{relax}}\) all have height two. Their quotient rings have dimension zero. At any height-one prime each ideal therefore becomes the unit ideal, so both graph and pin conditions disappear. The identity on the original roles supplies linked maps and hence an ordinary tensor comparison there. The same holds over the fraction field. If \(f\) is irreducible, all maximal localizations pass exactly when the original pair is ordinarily equivalent. The three ideals are pairwise comaximal, and at each maximal ideal at most one type of congruence survives. At the data maximal ideal, all pin conditions disappear and every ordinary residue transporter lifts to invertible matrices over the local ring. At either pin maximal ideal the data condition disappears, and elsewhere both conditions disappear. The same maximal-localization conclusion holds in the two fixed one-dimensional rings at their respective data primes. Thus the defect can persist after testing all maximal localizations on the original ordinary YES promise.

Let \(A\) and \(B\) denote signed and ordinary TI over \(\mathbb F_3\). On any of the displayed fixed-ternary image families the localization-defect language has ordinary many-one degree at most \(B\) if and only if both \(A\le_m^{\rm P}B\) and \(\overline B\le_m^{\rm P}B\). The forward implication composes the construction with the preceding directional theorem, which gives both requirements already on ordinary YES inputs. The reverse implication decodes the source and uses the preceding total directional compiler. The statement uses the specified image family and does not assert that arbitrary localization differences over any of these rings are decidable or have the same degree.

These are paper proofs. The unrestricted ternary equality and ordinary complement closure remain separate open premises. [Original same-field question](https://arxiv.org/html/2306.03135v2#S1.SS5)
