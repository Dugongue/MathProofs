# Central-shift conjugacy, normalizers and centralizers from bare class-two decision

**Theorem.** Let \(G,H\) be finite groups given by Cayley tables, with specified central subgroups \(C\le Z(G)\), \(C'\le Z(H)\) containing their derived subgroups. Write \(A=G/C\) and \(A'=H/C'\). Let \(D\le\operatorname{Hom}(A,C)\) and \(D'\le\operatorname{Hom}(A',C')\) be subgroups given by lists of their elements. For \(d\in D\), denote the automorphism \(g\mapsto g\,d(gC)\) by \(\tau_d\), and write \(\tau_D=\{\tau_d:d\in D\}\).

A bare class-two group isomorphism oracle suffices for deterministic polynomial-time decision, search, and exact counting of isomorphisms \(f:G\to H\) satisfying
\[
f(C)=C',\qquad f\tau_D f^{-1}=\tau_{D'}.
\]
The reduction can also require an explicitly prescribed isomorphism \(t:D\to D'\) to be the conjugation map. It simultaneously allows a fixed number of named subgroups of each of \(A,C\) whose images are prescribed. On equal inputs it computes generators for the corresponding automorphism group. In particular, it computes the normalizer, the centralizer, and the induced action on \(D\) in the group of automorphisms preserving \(C\). If \(C\) is characteristic, that ambient automorphism group is \(\operatorname{Aut}(G)\).

For \(p\)-groups each feasible decision test uses at most one ordinary unmarked class-two \(p\)-group query per candidate prefix. All query groups have order bounded by \((|G||D|)^{O(1)}\) on the source side and the analogous bound on the target side. The constants are absolute with one marked subgroup in each of \(A,C\) and depend only on their allowed counts in the fixed-count variant. In particular, \(|D| \le |G|^{O(1)}\) gives polynomial-size Cayley queries in the source group order. The proof works at \(p=2\) and with arbitrary mixed cyclic orders. No restriction on the order of any individual central shift is needed.

This uses the projective cyclic-frame and torsion-weighted paired markers from the preceding class-two search proof. Two new ingredients are a copy of the specified kernel that realizes it as a commutator image even when \(C\) strictly contains the derived subgroup, and an evaluation block that encodes conjugacy of the *whole* subgroup \(D\). The condition uses how \(D\) acts on the original group in addition to the abstract group structure of \(D\). [Preceding class-two reduction](https://github.com/Dugongue/MathProofs/blob/main/GrochowResearchSynthesis/CLASS-TWO-BLACK-BOX.md) · [Grochow–Qiao on group extensions and cohomology](https://arxiv.org/abs/1309.1776)

## 1. What a decorated transporter must preserve

Use additive notation in \(A,C,D\). Each \(\tau_d\) is an automorphism. The assignment is a homomorphism from the additive group of homomorphisms into \(\operatorname{Aut}(G)\), since shifts are the identity on \(A\) and \(C\). Its inverse at \(d\) is the shift at \(-d\), and evaluation on lifts distinguishes two different \(d\).

If \(f(C)=C'\), let \(\alpha:A\to A'\) and \(\gamma:C\to C'\) be the induced isomorphisms. Direct substitution into the shift on a lift gives
\[
f\tau_d f^{-1}=\tau_{\gamma d\alpha^{-1}}.
\]
Thus the required action on \(D\), if it exists, is unique. Write it \(s:D\to D'\). Its defining relation is the preservation of the evaluation bimap
\[
s(d)(\alpha a)=\gamma(d(a)).
\]
This also proves that changing \(f\) by a shift trivial on \(A,C\) cannot change the conjugation action.

For a \(p\)-group, put \(M=p^e=\max(\exp A,\exp C)\) and \(R=\mathbb Z/M\mathbb Z\); exclude the trivial group for now. The shift group \(D\) is killed by \(M\). Write \(\beta:A^2\to C\) for the commutator bimap, with \([x,y]=x^{-1}y^{-1}xy\). For each \(m\mid M\) use
\[
q_m:A[m]\longrightarrow C/mC,\qquad q_m(a)=\widetilde a^{\,m}\bmod mC.
\]
The record is independent of the lift. If \(a_i\) is an additive cyclic basis of \(A\), with orders \(d_i\), then a pair \((\alpha,\gamma)\) lifts precisely when it preserves \(\beta\) and the values of \(q_{d_i}\) on the \(a_i\). Choose source lifts \(x_i\); choose any target lifts of the prescribed quotient images. The congruences on the powers supply central corrections to these lifts. The corrected lifts and \(\gamma\) preserve all central relations, pair commutators, and basis powers. These relations give the original group, since collecting bounds the order by \(|A||C|\) and the presented group surjects to the original group of that same order. There are
\[
k(A,C)=|\operatorname{Hom}(A,C)|=\prod_i|C[d_i]|
\]
distinct lifts of every admissible pair. Their differences are the shifts trivial on \(A,C\), hence every one satisfies the same decoration conditions. This argument uses only centrality and applies even if \(\beta(A,A)\) generates a proper subgroup of \(C\).

We use the \(R\)-dual \(X^*=\operatorname{Hom}_R(X,R)\). Every finite \(R\)-module is reflexive for this dual, and \(|X^*|=|X|\). In fact a cyclic summand \(R/(p^a)\) has dual \(p^{e-a}R\), which also has order \(p^a\); evaluation has zero kernel. Direct sums give the assertions for every \(X\). The cyclic basis coordinates and the module types used below can be found from abelian tables by Smith normal form with transformations. [Kannan–Bachem, polynomial-time Smith and Hermite algorithms](https://doi.org/10.1137/0208040)

## 2. Encode the extended diagram in one unmarked group

We describe one named quotient subgroup \(J\le A\) and one named central subgroup \(K\le C\). Use \(J=A\) or \(K=0\) to omit a mark. Paired comparisons first check the types of the named modules \(A,C,D,K,A/J\) and the supplied prefix types. An impossible type comparison is a negative answer before any query.

### The quotient carrier and the central output

Make a separate copy \(C_0\simeq C\) and a copy \(K_0\simeq K\). Add two free cyclic anchors \(Ru,Rv\). Put
\[
S=A\oplus C_0\oplus D\oplus Ru\oplus Rv.
\]
Include an ordered tuple in \(S^*\) beginning with \(u^*,v^*\), followed by any prescribed partial cyclic basis in each of \(A^*, C_0^*, D^*\). The tuples on the two sides are ordered in the same manner. Use the labelled frame from the preceding class-two reduction on this partial cyclic basis of \(S^*\). Its frame carrier \(L\) and central output \(B_{\mathrm{fr}}\) have orders \(|S|^{O(1)}\). The skew extension of the frame pairing on \(S\times L\) gives a named component \(S\times L\to B_{\mathrm{fr}}\). For completeness, if there are \(t\) named vectors \(g_i\), write \(L_i=Rg_i\) and \(L_*=R\sum_i g_i\). For \(t\le 6\) use \(i\) slots of \(L_i\) and \(t+1\) slots of \(L_*\). For \(t\ge 7\) use each \(L_i\) once, \(L_*\) twice, and \(L_i+L_j\) once per edge of the tree with center 1 and arms \(2\), \(3,4\), and \(5,\ldots,t\). Each \(U_j\) in this list has a cyclic slot carrier of order \(\exp U_j\) in \(L\), and its dual is a summand of \(B_{\mathrm{fr}}\). The form on \(S\times L\) is the evaluation of \(U_j\) on \(S\) times the \(j\)-th cyclic coordinate. The contraction images and incidence counts recover the labelled coordinate lines and their sum line. A maximal nonzero cyclic contraction image is a listed line, since every cyclic summand obtained from a plane slot lies in one of its two separate coordinates. All listed lines are attained and incomparable. The orders of the slots and outputs give the stated cost because the tree has maximum degree three and only two extra sum-line slots. In the small case all multiplicities are bounded. At each incidence test the dimension of the permitted contraction coordinates modulo \(p\) counts the slots whose submodules lie in the tested submodule. The distinct multiplicities or the labelled asymmetric tree recover the ordered lines. Consequently paired transport of this record gives one common unit multiplier on the indexed covectors. This use of the frame is valid for mixed types, because each prescribed coordinate line is part of a cyclic basis and the sum line has two full-order anchor coordinates.

Use the quotient carrier and central output
\[
E_0=S\oplus K_0\oplus L,\qquad
B_0=C\oplus Rc\oplus(A/J)\oplus B_{\mathrm{fr}}.
\]
Here individual modules \(A,C_0,D,Ru,Rv,K_0,L\) are the seven named blocks. Use the following alternating records, with one displayed order selected for each cross term and its negative for the reverse order.

| Domain | Value in \(B_0\) |
| --- | --- |
| \(A\times A\) | \(\beta\) in \(C\) |
| \(C_0\times Rv\) | \((w,rv)\mapsto rw\) in \(C\) |
| \(Ru\times Rv\) | \((ru,sv)\mapsto rsc\) |
| \(A\times D\) | \((a,d)\mapsto d(a)\) in \(C\) |
| \(A\times Ru\) | \((a,ru)\mapsto r(a+J)\) in \(A/J\) |
| \(K_0\times Rv\) | \((k,rv)\mapsto rk\) in \(C\) |
| \(S\times L\) | the labelled frame in \(B_{\mathrm{fr}}\) |

All unlisted components are zero. These brackets generate \(B_0\). In particular \(C_0\times Rv\) generates the entire specified group \(C\), even if the old commutator bimap does not. There are no cross relations between the displayed central summands. The frame values generate \(B_{\mathrm{fr}}\) because every slot submodule from the frame is a direct summand of \(S^*\), so restriction of \(S\) onto its dual is surjective.

For multiple named central subgroups, give each its own \(K_0\)-type block paired with \(v\). For multiple named quotient subgroups, use a separate free cyclic line and a separate quotient summand for each additional pair. Additional line scalars multiply their quotient records by units and leave the kernel of each such record intact. The number of new blocks is fixed throughout the reduction.

### Recover the individual blocks

Apply the preceding paired-marker construction, using two markers for each named block of \(E_0\). Here are its rank and cardinality guarantees with the current dimensions. Write \(l\) for the number of markers, \(r_e=\dim_{\mathbb F_p}p^{e-1}E_0\) and \(d_0=3r_e\). For each marker on a block \(V_i\), adjoin a private copy \(V_i^*\) and a private free module \(R^{w_i}\), where
\[
w_i=2(l+i)(d_0+1),\qquad 1\le i\le l.
\]
Add one central coordinate \(R b_i\). Its marker form \(F_i\) is the evaluation pairing on \(V_i,V_i^*\) plus a perfect alternating form on the private free module. All other forms vanish on that free module. Extend \(E_0\) to \(\widehat E\) by these modules and \(B_0\) to \(\widehat B=B_0\oplus B_{\mathrm{aux}}\) by the \(R b_i\). The bimap generates \(\widehat B\). Zero named modules cause no problem, since their block and private partner are both zero and their free marker still has positive rank.

Every covector form is \(F=Q+\sum_i\alpha_iF_i\) with \(Q\) supported on the old carrier. Its contraction image \(I(F)\) satisfies
\[
\dim_{\mathbb F_p}p^{e-1}I(F)\in
 \left[\sum_{\alpha_i\in R^\times} w_i,
        \sum_{\alpha_i\in R^\times}w_i+d_0\right].
\]
Indeed the private free modules are independent and contribute rank \(w_i\) exactly at a unit coefficient, and \(p^{e-1}\) of all the remaining carrier dual has dimension \(d_0\). The weights separate the empty and singleton bands, and \(2w_1>w_l+d_0\). Thus the transport of the pure marker \(F_i\) has exactly its \(i\)-th coefficient a unit. The nonfree evaluation pair at that coefficient projects onto \(V_i^*\oplus V_i^{**}\). Solving first for the \(V_i\) input from the private output and then for its private input from the \(V_i^*\) output shows that the kernel of this projection inside the image is the range of the remaining principal block, apart from the independent free parts. Equality of image cardinalities with the source pure marker forces every other heavy coefficient to vanish and the remaining principal block to be zero. This also shows the transported marker image intersects the dual core in \(V_i^*\). Two copies of the marker have disjoint private supports outside that dual core and their image intersection is \(V_i^*\). The argument works for every component because paired source and target formats have matching sizes.

Consequently every isomorphism of the resulting unmarked groups preserves the dual core and carries every one of its named blocks to the corresponding one. The central covector forms supported on that dual core are exactly \(B_0^*\), since every nonzero \(\alpha_i\) has nonzero image on a private free part. This recovers the annihilator \(B_{\mathrm{aux}}\). Passing to the quotients gives maps on the named primal blocks of \(E_0\), the central output \(B_0\), and all the displayed alternating records. In particular the image of \(C_0\times Rv\) recovers the \(C\) summand and the image of \(Ru\times Rv\) recovers the \(Rc\) summand. Recover the frame form submodule as the forms supported on \(S\times L\) and its reverse. These are precisely the covectors of \(B_{\mathrm{fr}}\), since every other summand is generated by the brackets of pairs disjoint from this support.

### Put back the old group powers

For a cyclic basis of the original \(A\), keep the actual old basis powers of its chosen lifts in \(G\). Set the \(M\)-th power of the lift of \(u\) to \(c\). On every other new basis lift assign zero power at its cyclic order. To construct the oracle group explicitly, with quotient basis \((e_i)\) of orders \(d_i\) and specified powers \(s_i\), add the quotient coordinates as residues and use central correction
\[
\sum_i\left\lfloor\frac{a_i+b_i}{d_i}\right\rfloor s_i+
\sum_{j>i}a_jb_i\,\widehat\beta(e_j,e_i).
\]
The first summands are carry cocycles. The second is bilinear on the cyclic residues, since each bracket entry is annihilated by both coordinate orders. This gives associativity and the stated powers and commutators. The derived subgroup is \(\widehat B\), so it and the abelianization \(\widehat E\) are intrinsic even when the larger group has other central elements.

Modulo \(B_{\mathrm{aux}}\) the presentation is a direct product of the displayed core extension and the auxiliary carrier made abelian, with zero basis powers at its cyclic orders. For an element of \(\widehat E[m]\), the auxiliary component contributes zero to the \(m\)-th power in this quotient. Thus the induced maps on \(E_0,B_0\) preserve the projected \(q_m:E_0[m]\to B_0/mB_0\). The original power records are their restrictions to \(A[m]\) with values in the direct summand \(C/mC\).

The frame gives a common unit on the two anchor lines, so their primal maps scale by one common unit \(\mu\). Since the bracket of the anchors is \(c\), the transported \(c\) is \(\mu^2c'\). Since \(u^M=c\) and \(MB_0=0\), the power record gives \(\mu c'\). Comparing in the full-order direct summand \(Rc'\) yields \(\mu=1\). Thus all the labelled frame covectors transport exactly. The bracket \(C_0\times Rv\) now identifies the induced map on \(C_0\) with \(\gamma\), the induced map on \(C\). In particular the conditional \(C_0^*\) marks are genuine marks on the central action. Equation \(A\times D\to C\) identifies the induced map \(s\) on \(D\) with the conjugation action on the shift subgroup. The \(D^*\) marks can specify that \(s=t\): pin the dual full cyclic basis of \(D\) to its image under the inverse dual of \(t\). The kernel of the \(A\times Ru\) bracket gives \(J\), and the image of \(K_0\times Rv\) gives \(K\). Finally the projected old \(q_m\) and \(\beta\) imply that \((\alpha,\gamma)\) lifts to \(G\to H\) by §1. Each such lift meets all the required marks.

Conversely a decorated isomorphism of the original groups determines \(\alpha,\gamma,s\) and maps on \(A/J,K_0\). Use those maps on the indicated modules and \(\gamma\) on \(C_0\); fix the two anchors. The marks give exact transport of the frame submodules, so one can use the identity on the frame slot coordinates and the inverse duals of the transported slot maps on \(B_{\mathrm{fr}}\). For each paired copy use the inverse dual of the associated block map, and fix the heavy free modules and their output coordinates. These maps preserve the full bracket. Every auxiliary module on its own has zero internal brackets and zero basis powers, so its \(q_m\) vanishes on its \(m\)-torsion for every \(m\). The powers on \(A\) match because of the given isomorphism and the \(u\)-power relation is fixed. The lift criterion therefore gives an isomorphism of the unmarked oracle groups.

The logarithmic sizes \(\log_p|E_0|,\log_p|B_0|\) are \(O(\log_p|G|+\log_p|D|)\) for a fixed number of marks. The free marker parts use \(O(e(r_e+1))\) further logarithmic size, since the number of markers is fixed. A highest-order cyclic summand contributes \(e\) to \(\log_p|E_0|\), so \(er_e\le\log_p|E_0|\); the anchors also give \(e\le\log_p|E_0|\). The collecting formula produces the Cayley table in time polynomial in \(|G||D|\). All module and subgroup tables used in the formula can be generated in that bound. In particular no field reduction or dividing by 2 occurs.

## 3. Search, counts and induced normalizer action

Use the decision query with exact prescribed dual prefixes. Start with a full cyclic basis of \(A^*\) and a full cyclic basis of \(C^*\) on the source side. A target prefix must extend to a cyclic basis of the same ordered type. This is testable in polynomial time: require each proposed column to be killed by its source cyclic order, group source and target coordinates by orders, and test independence of the prescribed columns in each corresponding diagonal block modulo \(p\). Maps respecting the cyclic orders become block triangular modulo \(p\). Completing each diagonal block gives an invertible matrix modulo \(p\), hence an invertible map on the finite module by the \(p\)-power filtration. Thus the test is exact and may reject without calling the oracle.

Grow the prefixes by enumerating possible images of the next dual generator, using the marked decision test after each guess. The completed prefixes recover \(\alpha,\gamma\) by duality. Recover one lift by choosing corrected central lift powers as in §1. The old group size bounds \(|A^*|\) and \(|C^*|\), so search uses polynomially many oracle calls. Any prescribed action on \(D\) is kept fixed during this process.

For counting on equal inputs, take the stabilizer chain of the induced group on \(A^*\oplus C^*\) obtained from the decorated automorphism group. The orbit of each next basis generator under its current stabilizer consists of the target marks accepted by the decision test. The final stabilizer in this induced group is trivial. The product of orbit sizes therefore counts the admissible pairs \((\alpha,\gamma)\), and multiplication by \(k(A,C)\) counts actual group automorphisms. If the comparison between different inputs is feasible, the transporter is a right coset of the stabilizer on the source side and has the same cardinality. This applies to specified \(t\) too, because the source-side group in that case acts as the identity on \(D\). For generators, use the search procedure on each successful orbit point to get a representative of its coset. These representatives and the elementary shifts from \(\operatorname{Hom}(A,C)\) generate the decorated group.

When the two inputs and the \(D\) marks agree, leaving \(s\) free gives the normalizer of \(\tau_D\) inside the automorphisms preserving \(C\). Pinning all \(D^*\) generators to themselves gives the centralizer. Applying the normalizer generators to the explicitly listed elements of \(D\) gives the induced conjugation image as a permutation group, with this centralizer as its kernel. Exact conjugation by a proposed \(t\) is thus decidable without testing automorphisms of \(D\) one at a time.

For a general finite group in the theorem, class at most two follows from \(G'\le C\le Z(G)\). Its Sylow factors are characteristic direct factors; orders and factors can be found using the Cayley tables and trial division. The additive groups \(C,A,D\) and each named subgroup split into their primary parts. Taken componentwise, all conjugation conditions and any \(t\) split as well. Combining witnesses and generators, and multiplying counts, gives the stated reductions without any restriction on the primes. Trivial factors require no oracle calls.

## 4. Consequences and scope

If \(G=A\oplus C\) is abelian with the second summand marked, every compatible pair \((\alpha,\gamma)\) lifts. The theorem therefore treats arbitrary subgroups of matrices \(\operatorname{Hom}(A,C)\) over finite abelian modules under independent changes of bases, with simultaneous kernel and range-side subgroup marks. For genuine nonabelian extensions the same construction enforces the original power records. This is the part needed for \(2\)-groups where alternating commutators alone do not determine the extension.

For \(C=Z(G)\) or \(C=G'\), the resulting normalizer and centralizer are taken in the full automorphism group. Their computation uses only ordinary class-two decision and the finite group and module data. For example, when the odd-order decision bound \(N^{O((\log N)^{8/9})}\) is used, it transfers to all these queries and outputs with the same exponent when \(|D|=|G|^{O(1)}\). [Grochow–Qiao–Stange–Sun, Part V](https://arxiv.org/abs/2611.00735)

The argument is a written proof. Its explicit-shift-list input is important: a succinct generating set for a subgroup of order superpolynomial in \(|G|\) need not admit Cayley queries of order polynomial in \(|G|\) by this construction.

The finite replay checks 192 equal-bracket pairs rejected by the old powers in a mixed-exponent 2-group comparison, 64 admissible pairs with exact lift fibers, and 8,192 equations intertwining actual central shifts. It also checks a subgroup of four shifts whose normalizer, centralizer, and induced conjugation image have orders 192, 32, and 6, respectively.