# A directional query characterizes two separate many-one reductions

Work over \(K=\mathbb F_3\). Let \(B\) be ordinary dense three-tensor isomorphism and let \(A_v\) test feasibility of a transporter with sign vector \(v\in(\mathbb F_2)^3\). Write \(A=A_0\), \(H=(A\le_m^{\mathrm P}B)\), and \(D_1=A_{e_1}\wedge\neg A_0\). The reflection \(r_v\) acts on the target of a pair and translates its sign profile by \(v\). A promise compiler for \(D_1\) is a polynomial-time map to ordinary TI whose output is correct whenever the input has an ordinary transporter. It can act arbitrarily on ordinary NO inputs.

## Theorem

The following conditions are equivalent.

1. \(D_1\) has a deterministic polynomial-time many-one compiler to ordinary TI on the ordinary YES promise.
2. The total language \(D_1\) reduces many-one to ordinary TI.
3. Both \(A\le_m^{\mathrm P}B\) and \(\overline{B}\le_m^{\mathrm P}B\).

The two necessary reductions use different constructions. The sign constraint is read out on multiplication tensors whose determinant triples are diagonal. Ordinary complement hardness already occurs on a self-reflected multiplication tensor with an explicitly supplied ordinary transporter. In particular, complement closure in the old conditional equivalence is necessary, and the implication from the directional compiler to \(H\) requires no complement assumption.

## Reading a sign without a negative query

Use the earlier weighted cube-zero construction in its fixed ternary case. For each nonzero linear character \(\chi:(\mathbb F_2)^3\to\mathbb F_2\), it maps a pair \(x\) to two even-dimensional scalar-residue commutative local algebras. Their ordinary isomorphisms exist exactly when \(x\in B\), and their attainable determinant signs are exactly the values \(\chi(v)\) over the original transporter profile. Their units all have regular determinant one: a unit is \(\lambda+j\) with \(j\) in the radical, so its determinant on the regular module is \(\lambda^{\dim A}\), and the dimension is even. The same holds for both left and right regular actions. This uses the earlier polynomial-time weighted carrier with radical cube zero and is the only input to this direction beyond ordinary gate compilation. See *CubeZeroAndExtensions*, Sections 2–4, in the prior atlas.

Let \(Y_\chi(x)\) be the pair of multiplication tensors of those algebras. The multiplication isotopy calculation below shows that its determinant profile is contained in \(\{0,(1,1,1)\}\). Consequently \(e_1\) is unattainable, identically throughout this image. Thus
\[
 D_1\big(r_{e_1}Y_\chi(x)\big)
 = A_0\big(Y_\chi(x)\big)
\]
as total answer bits, since reflection exchanges the queried signs and the other sign is structurally impossible. The right side asks for some original transporter with \(\chi(v)=0\). On \(B\)-YES inputs the left side is an honest promise query.

A nonempty original profile is a coset \(c+S\). It contains zero exactly when every nonzero linear \(\chi\) takes zero somewhere on it. If \(c\notin S\), separate the class of \(c\) from zero in the quotient by \(S\) by a nonzero functional. Its lift is constantly one on the profile. Conversely zero itself witnesses every individual test when present. Therefore the seven directional answers comprise an ordinary conjunction under a hypothetical promise compiler. Include one copy of the original ordinary comparison \(x\) as a guard: on ordinary NO inputs any off-promise output from the directional compiler is irrelevant. The constant ordinary conjunction maps the entire construction to one ordinary TI pair. This proves \(H\) from condition 1 without a complement hypothesis.

The elementary conjunction used here can be obtained by ordinary TI of an ordered tuple of triangular corner algebras. Encode each bimap by the three-vertex algebra of the next section. Join consecutive such chains by a one-dimensional directed bridge, with all their additional radical products zero. The joined graph has a unique topological order, so its algebra isomorphisms compare the individual bimap blocks in order. Its unital associative multiplication tensor gives one ordinary comparison. Fixed-format degeneracies and unequal formats are decided by routine dimension or zero-tensor tests before using this compiler. [Grochow–Qiao, tensor and algebra isomorphism](https://arxiv.org/abs/1907.00309)

## A self-contained source algebra with orientation rigid automorphisms

For a based tensor \(T:X\times Y\to Z\) of positive format, define a unital associative algebra \(\Lambda(T)\) with scalar diagonal idempotents \(e_0,e_1,e_2\), radicals \(X=e_0Je_1\), \(Y=e_1Je_2\), and \(Z=e_0Je_2\). On radical elements the only potentially nonzero product is \(xy=T(x,y)\). It is associative since the idempotents act according to the arrow endpoints and every triple radical product is zero. Its radical is precisely \(J=X\oplus Y\oplus Z\), and its residue algebra is \(K^3\).

Any algebra isomorphism permutes the primitive residue idempotents. To inspect the corners, align their lifts. More generally, two complete orthogonal systems \((e_i),(f_i)\) lifting the same assigned residue classes are conjugate by \(u=\sum_i f_i e_i\): this element is one modulo the radical, hence a unit, and \(ue_i=f_i u\). After alignment the directed graph of nonzero radical corners has the unique order \(0,1,2\), so the three labels are fixed. Thus restriction to the corners yields a transporter for \(T\), and conversely such a transporter gives a blockwise algebra isomorphism. This proves exact ordinary reflection even when \(T\) has a deficient contraction support.

Set \(P(T)=M_2(\Lambda(T))\). Matrix amplification also reflects ordinary isomorphism here. Indeed its semisimple quotient is \(M_2(K)^3\). The image of the standard matrix idempotent \(E_{11}\) under an isomorphism has rank one in each semisimple factor, as arbitrary algebra isomorphisms preserve the property of being primitive in a simple factor. Conjugate in the quotient to the designated rank-one idempotents, lift that conjugating unit, and then align the two idempotents by the preceding lemma applied to the two-element system with their complements. Their corners are isomorphic, and the standard corner is \(\Lambda(T)\). The converse, entrywise extension of an isomorphism, is immediate. Units of \(P(T)\) have determinant one in their right regular action: right matrix multiplication acts identically on two row modules, so the determinant is a square in \(K^\times\). The same argument with columns works for the left action.

Now form the unital triangular algebra
\[
 C(T)=
 \begin{pmatrix}P(T)&P(T)\\0&K\end{pmatrix},
\]
where the upper right corner is the regular left \(P(T)\)-module with right scalar action. Its dimension \(2\dim_K P(T)+1\) is odd. Its Jacobson radical consists of the radical of \(P(T)\) in the leading corner and the full upper right corner. The quotient is \(M_2(K)^3\times K\), with a unique scalar simple factor. Therefore any isomorphism of two such algebras preserves the sum of the three matrix-factor identities and the scalar identity at the residue level. Align their lifts by a unit congruent to one modulo the radical. The leading corner recovers \(P(T)\) and hence \(T\) up to ordinary isomorphism. Conversely every isomorphism on \(P(T)\) extends by the same map on the upper right copy and the identity on \(K\).

The center of \(C(T)\) is exactly \(K\). Commutation with its two diagonal idempotents first kills the off-diagonal part of a central element. Writing the diagonal as \((a,b)\), commuting with every upper right \(m\) requires \(a m=m b\), so evaluating at \(m=1\) gives \(a=b1\). Thus \(C(T)\) is centrally indecomposable.

Every automorphism of \(C(T)\) is even. The lift alignment acts by conjugation by a unit \(1+j\) with \(j\) nilpotent. Left and right multiplication by such a unit and its inverse are unipotent on the regular algebra and have determinant one. After alignment, the leading corner has some algebra automorphism \(\phi\). The upper right map must have the form \(m\mapsto\phi(m)u\) by preservation of its regular module structure, with \(u\) a unit since the map is invertible. The scalar corner is fixed. Therefore the determinant is
\[
 (\det_K\phi)^2\,\det_K R_u=1,
\]
where the regular right-unit determinant on \(P(T)\) was proved above. This verifies parity rigidity on the entire algebra, including changes of idempotent lifts.

## Ordinary complement is a directional test on a known ordinary pair

For an ordinary input \(x=(T,U)\) in one positive format, set \(P_x=C(T)\times C(U)\), and let \(S_x\) be its multiplication tensor in the displayed basis. The two centrally indecomposable factors have equal odd dimension. Any factor-preserving automorphism is even. A factor swap exists exactly when \(C(T)\cong C(U)\), equivalently \(x\in B\). When available, use an isomorphism and its inverse as the two block maps. Their determinants cancel and the block exchange is odd. Thus \(P_x\) admits an odd algebra automorphism if and only if the original pair is ordinarily isomorphic.

For an arbitrary associative unital algebra, the isotopy condition \(H(xy)=F(x)G(y)\) yields \(a=F(1)\), \(b=G(1)\), and \(H(x)=F(x)b=aG(x)\). Invertibility of the maps forces \(a,b\) to be units. Then \(\phi(x)=a^{-1}H(x)b^{-1}\) is a unital multiplicative isomorphism, and the three maps are exactly \(L_a\phi,R_b\phi,L_aR_b\phi\). Conversely each such choice provides an isotopy. If \(\ell,r,d\) denote respectively the determinants of \(L_a,R_b,\phi\), the isotopy tuple is
\[
(\ell d,rd,\ell r d).
\]
Its product is \(d\) over \(\mathbb F_3\). Hence an \(e_1\)-isotopy requires an odd algebra automorphism. Conversely, given an odd algebra automorphism of \(P_x\), take \(a=1\) and \(b=(-1,1)\) on its two factors. Right multiplication by \(b\) is odd because the first factor has odd dimension, so the resulting triple is \((-1,1,1)\).

Output the pair \(q(x)=(S_x,r_{e_1}S_x)\). It always has a written ordinary transporter with sign \(e_1\), the displayed reflection. A determinant-one transporter of this pair exists precisely when \(S_x\) has an \(e_1\)-autotopism, which holds precisely when \(x\in B\). Therefore
\[
 x\notin B\quad\Longleftrightarrow\quad D_1\big(q(x)\big).
\]
This is a polynomial many-one reduction to the ordinary YES promise, with no guard and no promise recognition. For inputs whose ordinary answer can be determined directly, such as unequal or zero formats, substitute a fixed known YES or NO instance of that promise accordingly. Both kinds exist by the construction using a matching pair and a fixed ordinary nonmatching pair of positive format.

More specifically the automorphism sign subgroup of \(S_x\) is exactly the even-total hyperplane when \(x\notin B\), and the full sign cube when \(x\in B\). The unit choices \(a=(-1,1)\) and \(b=(-1,1)\) independently realize the two generating even signs, and an odd algebra automorphism supplies an independent sign when it exists. Conversely the total sign of every isotopy is the algebra automorphism sign. On this displayed multiplication-table subfamily the reverse comparison to \(\overline B\) just finds the two primitive central idempotents of the center \(K^2\) and compares the corresponding ordinary factor multiplication tensors. Thus even this narrow D1 promise has exactly ordinary complement degree.

## Completion of the equivalence and a certificate consequence

A promised compiler, composed with \(q\), gives \(\overline B\le_m^{\mathrm P}B\). The diagonal readout gives \(H\). Conversely assume both reductions. Implement \(A_{e_1}\) by applying \(H\) after a fixed reflection. Implement \(\neg A_0\) by first applying \(H\) and then the ordinary complement compiler. Compile their conjunction into one ordinary comparison. This proves condition 3 implies condition 2, while condition 2 plainly implies condition 1.

The ordinary language \(B\) itself also reduces to the D1 promise. On \(q(x)\) an attainable sign of even total parity exists exactly when \(x\in B\), by the even-hyperplane versus full-cube description. Use the weighted carrier for the total sign character and its diagonal directional readout. The intermediate pair \(q(x)\) is always ordinary YES, so the weighted carrier and its reflected query are still on the promise. Thus both \(B\) and \(\overline B\) reduce honestly to the directional promise. In particular membership of that promise problem in either PromiseNP or Promise-coNP would put \(B\) in \(\mathrm{NP}\cap\mathrm{coNP}\). This statement concerns completeness and soundness on promised inputs, since the constructed queries lie there for every source input.

## Fixed odd-field extension

The same implications hold over any fixed finite field \(F\) of odd order if \(e_1\) denotes the determinant tuple \((-1,1,1)\). Write \(m=|F^\times|\), replace the amplification by \(P(T)=M_m(\Lambda(T))\), and replace the upper right regular module in \(C(T)\) by \(P(T)^{m-1}\). The scalar residue factor is still unique, and the center is still scalar. The full dimension is \(m\dim_F P(T)+1\), which is odd. A linked automorphism acts on the leading corner and the \(m-1\) copies through \(m\) copies of \(\phi\) before its residual module automorphism, so \((\det\phi)^m=1\). The residual operator is a matrix of right multipliers on \(P(T)^{m-1}\). In terms of \(m\times m\) matrices over \(\Lambda(T)\), it acts identically on each of the \(m\) row indices across the copies. Its determinant is an \(m\)-th power and is therefore one. Unit alignment is unipotent as before. Thus any factor-preserving automorphism has determinant exactly \(1\) and an exchange, when it exists, has determinant \(-1\). For the multiplication isotopy formula the ratio of the first two determinants multiplied together to the third determinant is always \(d\), even when the units range beyond signs. Thus an \(e_1\)-autotopism again exists exactly when a factor exchange exists.

For the other direction use the earlier weighted construction over the fixed field \(F\), whose carrier dimension is divisible by \(m\) and whose left and right unit determinants are one. Its diagonal profile again excludes \(e_1\). Test all characters of \((F^\times)^3\) into \(F^\times\), a constant-size set. They separate every nonidentity element of every quotient, since the quotient has exponent dividing \(m\) and \(F^\times\) is cyclic of order \(m\). Hence a nonempty determinant coset contains the identity exactly when each character takes value one somewhere on it. This gives the same ordinary conjunction. The fixed-field promise equivalence therefore does not rely on the special fact that all nonzero ternary values are signs.

The result determines the conjunction of premises that is necessary and sufficient for the directional compiler. It does not settle either premise separately. These are paper proofs. [Original same-field question](https://arxiv.org/html/2306.03135v2#S1.SS5)
