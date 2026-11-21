# The ternary directional sign gap and signed nonisomorphism

Let \(B=\mathsf{TI}(\mathbb F_3)\) and \(A=\mathsf{TI}_{\mathrm{SL}}(\mathbb F_3)\) on dense ordered three-tensors. For a tensor pair \(x=(T,U)\) let \(P(x)\subseteq V=\mathbb F_2^3\) be the determinant-bit profile of all ordinary transporters. Bit \(0\) stands for determinant \(+1\). Let \(e_1=(1,0,0)\), \(d=(1,1,1)\), and let \(r_vx\) apply fixed diagonal reflections of bits \(v\) to the target. Then \(P(r_vx)=v+P(x)\). The promise for the directional problem is \(x\in B\), and its YES predicate is
\[
D(x)=[e_1\in P(x)\ \wedge\ 0\notin P(x)].
\]
A promise compiler is a deterministic polynomial-time map to one ordinary ternary TI instance, correct on every ordinary-positive input. Its answer on other inputs may be arbitrary.

## Exact characterization

The following statements are equivalent.

1. \(D\) on the ordinary-positive promise compiles into one ordinary TI instance.
2. Signed ternary **nonisomorphism** reduces to ordinary ternary TI, \(\overline A\le_m^{\mathrm P} B\).
3. Both \(A\le_m^{\mathrm P}B\) and \(\overline B\le_m^{\mathrm P}B\).
4. The other rail \(\neg D\) on the same ordinary-positive promise compiles into one ordinary TI instance.

The equivalence leaves the unrestricted compiler open and removes every complement premise from the forward implications. In particular, even an ordinary-positive promise compiler would put both ordinary and signed ternary isomorphism in \(\mathrm{NP}\cap\mathrm{coNP}\).

## Two exact interfaces

**Determinant characters.** For each linear character \(w:V\to\mathbb F_2\), the weighted cube-zero construction turns \(x\) into a pair \((R,S)\) of even-dimensional scalar-residue local commutative algebras with exact set of algebra-isomorphism determinant bits \(w(P(x))\). Every original ordinary transporter extends explicitly in polynomial time. This is the determinant-image statement of the construction, including empty profiles. On its multiplication tensor pair \(X_w(x)=(M_R,M_S)\) the full profile is precisely \(\{td:t\in w(P(x))\}\). Indeed an ordinary multiplication isotopy is \((L_a\phi,R_b\phi,L_aR_b\phi)\), where \(\phi:R\to S\) is a unital isomorphism and \(a,b\) are units of \(S\). Each unit has the form \(\lambda 1+j\), so both determinants of multiplication by it equal \(\lambda^{\dim S}=1\). Inversion of input variances leaves ternary determinant bits unchanged. The construction uses role-tagged symmetric bipartite multiplication blocks and dual copies to cancel unwanted determinants. [Exact carrier and lifting proof](WeightedCubeZero.md)

**Positive aggregation.** A constant number of known ordinary TI outputs may be combined by a fixed AND, OR, or positive Boolean formula into one ordinary TI instance. AND is the disjoint typed diagram tying each tensor to its own three labeled roles. For OR, encode each ordinary comparison by ordinary isomorphism of its two three-vertex triangular algebras. Take their product and link the two identities to the split two-point algebra. The swap bit is free on YES and forced zero on NO. Link these bit spaces by a bilinear group-addition tensor \(e_i\otimes e_j\mapsto e_{i+j}\) with subscripts modulo two. Pin the sum to the nonzero bit by mapping its named vector \(e_0\) to \(e_1\). This succeeds exactly when some comparison is true. The fixed-component tensor-system theorem compiles these constant-size diagrams. [Fixed-component tensor-system theorem](https://arxiv.org/html/2306.03135v2#S4) · [Switch construction](Aggregate.md)

## A reduction from ordinary nonisomorphism into the promise

For a positive-format tensor \(T:U\times V\to W\), take the three-vertex triangular unital algebra \(\Lambda_T\) with scalar diagonal idempotents, radical corners \(U,V,W\) at positions \(01,12,02\), and only nonzero radical product \(U\times V\xrightarrow{T}W\). The radical is intrinsic and the directed three-corner graph forces each quotient idempotent to its own vertex after the lifts are aligned by a unit congruent to \(1\) modulo the radical. The restricted isomorphism equations are exactly ordinary tensor isomorphism. In particular this is a uniform ordinary reduction even for \(T=0\).

Set \(L_T=M_2(\Lambda_T)\). This matrix amplification preserves and reflects ordinary isomorphism. In the reverse direction an isomorphism sends the matrix idempotent \(E_{11}\) to an idempotent of rank one over each simple quotient factor \(M_2(\mathbb F_3)\), since the induced quotient isomorphism permutes factors and preserves their simple rank. Align the image with \(E_{11}\) in the quotient by an invertible element, lift that unit, and then align the congruent idempotents by a unit congruent to the identity modulo the radical. Their two corners are copies of \(\Lambda_T\) and \(\Lambda_U\). Right multiplication by a unit of \(L_T\) acts identically on the two matrix rows, so it has square determinant, hence determinant \(+1\) over \(\mathbb F_3\).

Now take the odd-dimensional associative unital algebra
\[
C_T=\begin{pmatrix}L_T&L_T\\0&\mathbb F_3\end{pmatrix}.
\]
The upper-right corner is the left regular module for \(L_T\) and has scalar right action. Its center is the scalar line, since commuting with the two diagonal idempotents removes the upper-right entry and commuting with the whole corner forces the diagonal blocks to be the same scalar. The scalar factor is unique in its semisimple quotient, whose other factors are all \(M_2(\mathbb F_3)\). Consequently an algebra isomorphism preserves the two distinguished quotient idempotents and, after conjugating by a radical unit, their lifts. It restricts to an isomorphism on \(L_T\) and conversely any such isomorphism extends. For an automorphism the maps on \(L_T\) and on its regular corner are \(\phi\) and \(R_u\phi\) for some unit \(u\). Their determinant product is \((\det\phi)^2\det R_u=1\). The lower-right scalar is fixed. Conjugating by a unit congruent to \(1\) modulo the radical has determinant one by the radical filtration. Thus every automorphism of \(C_T\) is even.

For a matching pair \(x=(T,U)\), form \(C=C_T\times C_U\) in its displayed direct-sum frame. All product automorphisms either preserve or swap the two primitive central idempotents. A map preserving both factors is even. A factor swap exists exactly when \(T\cong U\) ordinarily. When the swap exists, use any factor isomorphism and its inverse to get an odd swap, since each factor has the same odd dimension. Thus \(C\) admits an odd automorphism exactly when \(x\in B\).

Write \(M=M_C\). The regular sign of left multiplication can be prescribed arbitrarily, by using the unit \((-1,1)\) on the two factors. The same independently holds for right multiplication. The determinant-bit profile of the multiplication autotopisms is exactly
\[
(\ell+t,\ r+t,\ \ell+r+t),\qquad
\ell,r\in\mathbb F_2,\quad t\in \det\operatorname{Aut}(C).
\]
Here \(\det\operatorname{Aut}(C)\) denotes the available determinant bits. The profile is the even-total plane on an ordinary NO and the whole cube on an ordinary YES. The pair
\[
N(x)=(M,r_{e_1}M)
\]
has its ordinary transporter explicitly displayed by the coordinate reflection. In its shifted profile the bit \(e_1\) is always available, and \(0\) is available exactly when \(x\in B\). This gives
\[
D(N(x))=[x\notin B].
\]
A format mismatch or invalid input maps to a fixed ordinary-positive directional YES, for example a one-coordinate scalar and its negative. This reduction even lies in the subpromise with a supplied signed transporter for the **reflected** pair, since the second reflection returns \(M\) to itself. [Further structural variants](group.md)

## Recovering both signed rails from directional queries

A nonempty profile is an affine subspace, by taking the determinant image of a transporter coset. It contains zero exactly when every nonzero character image contains zero. If \(P(x)=v+S\) omits zero, a linear functional annihilating \(S\) with value one on \(v\) separates it.

For an ordinary-positive \(x\), put \(Y_w=r_{e_1}X_w(x)\). Its profile is \(\{e_1+td:t\in w(P(x))\}\). In particular \(0\) is structurally unavailable and \(D(Y_w)\) tests \(0\in w(P(x))\). Hence the signed YES rail is the positive formula
\[
B(x)\ \wedge\ \bigwedge_{w\ne0}D(Y_w).
\]
All seven queries respect the promise when \(B(x)\) holds. The ordinary guard protects against every out-of-promise answer when it fails.

For the signed NO rail, start again from \(X_w(x)\) and add one unused line to each of modes 2 and 3, leaving mode 1 unchanged. Call the resulting pair \(Z_w\). Multiplication tensors of unital algebras have full contraction supports. Restriction to the intrinsic supports recovers the original transporter; on the unused lines both signs extend independently. Thus \(P(Z_w)=w(P(x))\times\mathbb F_2^2\). On ordinary-positive pairs its directional predicate tests \(0\notin w(P(x))\), since the one-dimensional character image is nonempty. It follows that
\[
[x\notin A]
=
D(N(x))\ \vee\
\left(B(x)\wedge \bigvee_{w\ne0}D(Z_w)\right).
\]
This uses eight directional calls and one ordinary guard, with a constant positive decoder. The ordinary-NO control \(N(x)\) always lies in the promise. The other queries need the promise only when their guard is true. The two formulas, including the witness gate, are exact before any hypothetical directional compiler is invoked.

Now a promised compiler for \(D\) turns the displayed positive formula into one ordinary TI query, proving \(1\Rightarrow2\). Padding one unused line in every mode gives \(B\le_m^{\mathrm P}A\) and hence \(\overline B\le_m^{\mathrm P}\overline A\). If \(\overline A\le_m^{\mathrm P}B\) this proves complement closure of \(B\). Composing its complement map with the signed nonisomorphism map then gives \(A\le_m^{\mathrm P}B\), proving \(2\Rightarrow3\). For \(3\Rightarrow1\), compile the two signed tests on \(x\) and \(r_{e_1}x\), complement the first using ordinary complement closure, and combine by ordinary AND.

## The other rail carries the same two difficulties

Under statement 3, compile the two signed tests and apply ordinary complement closure and positive aggregation to the formula \([x\in A]\vee[r_{e_1}x\notin A]\). This gives statement 4.

In the reverse direction take the self comparison of \(M_C\) in the ordinary-NO construction and use the character \(w=(1,1,1)\) in the weighted cube-zero compiler. Its diagonal profile is \(\{0\}\) on ordinary NO and \(\{0,d\}\) on ordinary YES, because the sum of the multiplication profile bits is \(t\). Shift by \(e_1+d\). The resulting promised profile always omits zero and contains \(e_1\) exactly on ordinary YES. Thus this time the **negative** directional rail tests \(\overline B\). It again has an explicit ordinary reflector. On malformed or unequal-format source pairs, output any fixed ordinary-positive negative-directional instance, such as a scalar compared to itself. A compiler for that rail therefore supplies ordinary complement closure, which then converts the rail into a compiler for \(D\). This proves \(4\Rightarrow1\).

## Supplying the ordinary transporter

Define \(H_{\rm w}\) as the positive signed compiler when a verified ordinary transporter is supplied alongside the input. On the corresponding witnessed promise either directional rail compiles if and only if \(H_{\rm w}\) holds and \(\overline B\le_m^{\mathrm P}B\). The ordinary-NO gates above always supply the required witnesses. In the positive signed formula, the weighted construction lifts the provided witness and reflection changes it explicitly. Thus a witnessed compiler yields \(H_{\rm w}\) by the same seven character guards. Conversely apply \(H_{\rm w}\) to the two signed tests using the given and reflected witnesses, then use the ordinary complement map and positive aggregation.

There is a simpler equivalent target for \(H_{\rm w}\) itself. Let \(S_T=P(T,T)\), the sign subgroup of the ordinary stabilizer, and ask whether \(e_1\in S_T\). This question reduces to witnessed signed comparison by \((T,r_{e_1}T)\). Conversely, for an ordinary witness of sign \(v\), the yes condition is \(v\in S_T\). For each \(w\) with \(w(v)=1\), check that \(1\in w(S_T)\). This is exactly the fixed \(e_1\)-stabilizer question on the weighted self carrier with modes 2 and 3 padded. By annihilator duality all those tests hold precisely when \(v\in S_T\). Apply ordinary AND. [Witnessed and algebraic variants](algebra.md)

## Decision and certificate consequences

The directional promise is in deterministic polynomial time if and only if signed ternary TI is in deterministic polynomial time. A polynomial directional solver decides ordinary nonisomorphism via \(N\), hence decides the ordinary guard, and the seven character tests decide the signed problem. The converse uses the two signed decisions in the definition of \(D\).

Either rail is in PromiseNP if and only if signed TI is in coNP. For \(D\), certify signed NO using the positive formula for \(\overline A\). In its second branch include an ordinary transporter to verify the guard, a character index, and the directional certificate. The first branch is unconditionally promised. For \(\neg D\), its own always-promised ordinary-NO gate works in the first branch, while in the second branch a certificate for \(\neg D(Y_w)\) detects a missing character zero. Conversely, if \(A\) is in coNP, both signed rails are in NP and the two Boolean formulas defining the directional rails are NP predicates on the promise.

## An unconditional tractable family

A third-mode map list sufficient to contain every possible sign profile, of polynomial total size, gives a deterministic polynomial-time compiler using the constructive fixed-slice transporter problem and the determinant image of its two-mode automorphism algebra. In particular this applies when one tensor support rank is \(O(\sqrt{\log L})\), for dense input length \(L\), by enumerating its linear maps. This tests the entire profile and supplies fixed ordinary YES/NO output without a complement assumption. [Algorithm and exact hypotheses](complexity.md)

## Verification scope

The carrier proofs are written mathematics. The supporting diagonal, padding, and promise-guard identities have a separate Lean source. Exact controls enumerate all 52 ternary affine profiles including the empty set. Result novelty beyond the stated prior reductions is unverified. [Lean source](DirectionalGap.lean) · [Controls](direction_controls.py) · [Verification](Verification.json)
