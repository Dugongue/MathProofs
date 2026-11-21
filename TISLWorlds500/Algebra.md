# Further algebraic orientation worlds

Write \(H\) for deterministic polynomial-time many-one reduction from \(\mathsf{TI}_{SL}(\mathbb F_3)\) to ordinary TI over the same field. For a finite ring use free modules, dense coefficient tensors and displayed bases. Groups are specified by compact coefficients or explicit matrix generators as indicated, without expanding Cayley tables. “Incompatible” means that the proposed premise implies \(H\); a failed map or a model distinction is not a logical independence result. The 31 entries explicitly labeled **Paired comparison** place one sufficient premise or valid construction beside an explicitly weaker or different premise. Unless a counterexample is given, the weaker premise is left open as an implication to \(H\). Proofs are informal. The prior atlas is used only for its specific weighted character carriers, square-zero reflection and fixed-signature ordinary TI compilers.

## Mixed characteristic and the socle

### A01. Socle-supported tensors reflect residue isomorphism exactly

Let \(R\) be any fixed finite commutative local ring, \(J\) its maximal ideal, \(E=R/J\), and \(0\ne s\in\operatorname{Ann}_R(J)\). The map \(j_s:E\to R\), \(a\mapsto s\widetilde a\), is independent of the lift, injective, and satisfies \(rj_s(a)=j_s(\bar r a)\). Injectivity follows since a lift of any nonzero residue is a unit. Applying it to all entries of a tensor makes a transporter equation over \(R\) exactly the residue transporter equation. Every invertible residue matrix lifts: determinant outside \(J\) is a unit. Hence the ordinary comparison of tensors supported on this chosen socle line is equivalent, both ways, to ordinary TI over \(E\). This argument needs no coefficient-field section, and includes rings of characteristic \(9\).

### A02. The entire socle determinant profile is a pullback

For any tensor pair in A01, every attainable determinant tuple over \(R\) is exactly an arbitrary lift of an attainable residue tuple in \((E^\times)^3\). For sufficiency lift a residue transporter and multiply one coordinate in each mode by any necessary principal unit. These independent multipliers reduce to the identity and act trivially on the socle coefficients. Thus simultaneous full SL is reflected and lifted, and its degree on the socle-supported R-domain is exactly the residue SL degree. For \(E=\mathbb F_{3^r}\) this gives strictness on the restricted domain under \(\neg H\), using the fixed-field extension reflection from the previous atlas. On arbitrary \(R\)-tensors the reflection of determinant to \(E\) is always valid, while lifting the transporter needs the stated socle support.

### A03. Multiple independent socle coordinates retain shared witnesses

If \(s_1,\ldots,s_m\) are linearly independent over \(E\) in the socle, place \(T_1,\ldots,T_m\) over \(E\) into one \(R\)-tensor as \(\sum_j j_{s_j}(T_j)\). The transporter equations on these socle coordinates split uniquely as the \(m\) equations for the same residue triple. Conversely any common residue triple lifts with arbitrary principal determinants by A02. Thus one ring comparison can carry **simultaneous** residue constraints with exact determinant profile, not merely a conjunction of independent comparisons. This is an encoding for supplied independent socle vectors and does not assert that a fixed ring has unbounded socle dimension.

### A04. Principal-unit equality can coexist with full strictness

**Paired comparison.** Every principal-unit modification of the three determinant lifts is free on socle-supported inputs. Full determinant removal with an ordinary target on those same inputs with \(E=\mathbb F_3\) would imply \(H\).

The first statement is exactly the coordinate multiplier correction in A02, and uses the same ordinary transporter for all three prescribed principal modifications. For the second, translate an arbitrary ternary pair to the socle, use the proposed restricted reduction, and pull the resulting ordinary socle target back to \(E\). This last step requires that the proposed ordinary target remain in the socle domain or have a separate ordinary reduction back to \(E\). Thus a theorem about principal lifts alone cannot supply the residual sign. The older principal-unit compiler on all equicharacteristic inputs is logically compatible with this strictness.

### A05. Which unit characters survive passage to a socle

**Paired comparison.** On the socle domain, a single multiplicative determinant character nontrivial on a principal-unit factor always attains \(1\) when the required correction is in its principal image. A character trivial on the principal subgroup instead tests the corresponding residue character exactly.

For a character \(\chi:(R^\times)^3\to A\), with \(A\) any finite abelian group, write \(U=(1+J)^3\). For a residue sign tuple \(d\), its lifts have \(\chi\)-image one coset of \(\chi(U)\), by A02. In particular if \(\chi(U)\) is all of \(\operatorname{im}\chi\), it corrects every ordinary comparison. If \(\chi(U)=1\), \(\chi\) factors through the residue units, with no correction. Intermediate subgroups are exact tests of the induced residue character modulo \(\chi(U)\). The result concerns one prescribed character; unrelated correction choices for several characters cannot be assumed compatible without checking their joint image.

### A06. Teichmüller lifts can destroy a residue SL transporter

**Paired comparison.** Socle lifts reflect full SL by A02. Ordinary entrywise Teichmüller lifts from \(\mathbb F_3\) to \(\mathbb Z/9\) do not.

For side format \(2\times2\times1\), compare \(I_2\) with \(\begin{psmallmatrix}-1&1\\1&1\end{psmallmatrix}\). Both determinants are \(1\) modulo \(3\), so a special-linear matrix transporter exists there. Over \(\mathbb Z/9\) the indicated Teichmüller lifts have determinants \(1\) and \(-2\), unequal. The one-dimensional special-linear factor is the identity and the other two preserve the matrix determinant, so the lifted pair is signed NO. Reduction of an actual signed \(\mathbb Z/9\) transporter modulo \(3\) is always a signed witness. This counterexample falsifies the reverse direction for that particular lift, not the socle construction.

### A07. Congruence-kernel subgroup conjugacy carries the same signs

Let \(J\ne0\) and choose \(s\ne0\) in \(\operatorname{Ann}_R(J)\). Then \(s\in J\), so \(s^2=0\). For an \(E\)-matrix space \(M\) form \(G_M=\{I+j_s(A):A\in M\}\subseteq\operatorname{GL}_n(R)\) by entrywise application. It is an elementary abelian group of exponent \(\operatorname{char}E\), given by generators \(I+j_s(A_i)\) for an \(E\)-basis and its multiples by a fixed prime-field basis of \(E\). Conjugation is exactly residue conjugation on \(M\). Every residue conjugator lifts with all possible principal determinants, by multiplying by a diagonal matrix reducing to identity, which fixes the socle matrices under conjugation. Thus the framed signed and ordinary congruence subgroup comparisons reflect the corresponding residue matrix-space comparisons. Taking the earlier square-zero matrix spaces over \(E=\mathbb F_3\) gives a restricted regime with collapse equivalent to \(H\) for every such mixed or equal characteristic \(R\). The ordinary target is again the restricted carrier or any target explicitly reduced back to ternary TI.

### A08. Elementary abelian abstract isomorphism cannot replace conjugacy

**Paired comparison.** The compact matrix groups in A07 have trivial abstract classification by dimension, while their ambient signed conjugacy can still carry \(H\).

For a separate concrete ordinary obstruction, let \(M\) and \(M'\) be the one-dimensional ternary spans of square-zero matrices of ranks one and two respectively, in dimension four. The lifted groups have the same abstract order and are both cyclic of order three, but a conjugator would give a residue conjugator sending one nonzero matrix to a nonzero scalar multiple of the other, contradicting rank. Thus even ordinary ambient comparison is stronger than abstract isomorphism on these presentations. A GAP-style classification of the abstract groups alone cannot give the proposed ordinary compiler.

### A09. Product rings preserve the socle obstruction in any component

Let \(R=\prod_i R_i\) be a fixed finite commutative ring decomposed into local factors. Use one socle-supported comparison in a chosen \(R_i\) and constant zero tensors in all other factors. By the product decomposition of free modules, invertibility, equality of products and determinants split componentwise. On zero components identity maps supply the required determinant-one witnesses. Thus the exact ordinary and signed questions on this support equal those over the chosen residue field. In particular every finite commutative ring with a scalar-characteristic-three local factor contains the ternary gap on a restricted domain under \(\neg H\), even if it also has many characteristic-two or characteristic-zero-residue factors. No reduction of unrestricted ordinary ring TI back to the residue field is implicit here.

### A10. Full-ring ordinary hardness alone supplies no reverse direction

**Paired comparison.** If the full SL-to-ordinary comparison over a fixed local \(R\) with \(E=\mathbb F_3\) and the full ordinary \(R\)-to-ordinary ternary comparison both hold, then \(H\) follows. Knowing only the first comparison leaves a specific missing edge.

Compose the socle lift A02 with both hypothesized maps. The promised restriction concerns the input of the first map. Its ordinary outputs can have arbitrary \(R\)-coefficients, so A01 cannot be used on them without support recognition or a separate reduction. The same caution applies to characteristic mixtures in A09. By contrast a polynomial-time algorithm for **signed** comparison over \(R\) would directly put signed ternary TI in P by A02, implying \(H\) via fixed ordinary yes/no outputs.

### A11. Exact determinant stabilizer of a chain-ring matrix

Let \(R=\mathcal O/(\pi^k)\) for a discrete valuation ring \(\mathcal O\) with finite residue field. For the square matrix \(D=\operatorname{diag}(\pi^{a_i})\) with all \(a_i<k\), the exact attainable \(\det P\det Q\) for \(P D Q=D\), \(P,Q\) invertible, is \(1+(\pi^{k-\max_i a_i})\). If some \(a_i=k\) denotes a zero diagonal, the exact image is all \(R^\times\).

Lift the equation to \(\mathcal O\), writing \(R_0=Q^{-1}\). Then \(P-DR_0D^{-1}\) has entries divisible by \(\pi^{k-\max a_i}\), by dividing its \(j\)-th column error by \(\pi^{a_j}\). This also shows that the apparently fractional conjugate is integral. Its determinant equals \(\det R_0\), proving necessity. For sufficiency scale the largest-valuation row by any allowed unit; its error vanishes modulo \(\pi^k\). A zero row permits arbitrary scaling. Also each paired simultaneous scaling of one row and its corresponding column by inverse units stabilizes \(D\), so every pair with an allowed product is attainable. Relative raw determinant requirements follow by the known Smith-frame ratios. This is an unconditional exact orientation algorithm for the format \(n\times n\times1\) on fixed such rings.

### A12. Invertible matrices distinguish determinant constraints invisible to rank

**Paired comparison.** Ordinary comparison of invertible square matrices over a commutative local ring is trivial, but special-linear comparison in format \(n\times n\times1\) is equality of their full determinants.

Necessity is multiplicativity of determinant. For sufficiency if \(\det S=\det T\), use \(S T^{-1}\) on one side and identity on the other. A01–A02 and A11 show two different ways singular layers alter the problem: a socle matrix retains its scalar residue determinant test if its residue matrix is invertible, and a genuine zero Smith factor makes all determinant products correctable. Thus even a complete ordinary Smith-profile algorithm needs the orientation calibration to be a full signed solver. This distinction concerns matrix tensors and does not imply a general complexity lower bound.

## Invariants, degrees, and orbit separation

### A13. Finite rational orbits have bounded-degree invariant functions

For any \(G\le\operatorname{GL}_N(\mathbb F_q)\), every \(G\)-orbit \(O\) on \(\mathbb F_q^N\) has its indicator represented by a polynomial of total degree at most \((q-1)N\). Namely, sum over distinct \(a\in O\) the point indicators \(\prod_{i=1}^N(1-(x_i-a_i)^{q-1})\). The functions are invariant, and distinct orbit values do not cancel because at most one point term survives on any evaluation. This is an existence bound in the coordinate function ring, not an algorithm for constructing the list of orbit points and not a statement of formal polynomial invariance in modular characteristic.


### A14. Formal finite-group invariants can instead require exponential degree

**Paired comparison.** The low-degree functional statement A13 holds even for the natural \(\operatorname{SL}_n(\mathbb F_q)\) representation, but any nonconstant formally invariant polynomial on that representation has degree at least \(q^{n-1}\).

If the polynomial has positive degree in \(x_i\), work over \(K=\mathbb F_q(x_j:j\ne i)\). For each of the \(q^{n-1}\) distinct \(K\)-elements \(\sum_{j\ne i}a_jx_j\), an elementary determinant-one row operation gives invariance under translating \(x_i\) by that element. Subtracting the value at zero gives a nonzero polynomial in \(K[x_i]\) vanishing at all these translations. Therefore its degree is at least \(q^{n-1}\). A nonconstant formal polynomial has some such variable. This already distinguishes the zero tensor from a nonzero tensor in format \(n\times1\times1\), so no general separating family of low-degree **formal** invariants exists. Yet these two cases can be decided by just scanning the coordinates.

### A15. Uniform separating fingerprints would decide signed TI

**Paired comparison.** A deterministic polynomial-time computable finite string fingerprint separating precisely the rational ternary SL orbits would imply \(H\). A fingerprint separating precisely the rational GL orbits has a different property and can give false signed answers.

Compare the two SL fingerprints, then use a fixed ordinary yes/no output. On the GL side use the sign-rigid free cube-zero table \(F[x_1,\ldots,x_n]/(x_1,\ldots,x_n)^3\) for \(n\equiv2\bmod4\), and conjugate its multiplication table by an odd basis change. Every algebra automorphism has determinant \((\det g)^{n+2}=1\) by the tangent and symmetric-square grades, whereas every relative algebra isomorphism is odd. Unit-normalized isotopy makes these an ordinary YES and signed NO. Hence every GL orbit fingerprint agrees on the pair. This does not prove that a given constructive ordinary fingerprint yields no other signed algorithm.

### A16. Algebraic-group invariants cannot separate all rational signed orbits

**Paired comparison.** Exact effective rational SL-orbit separation would imply \(H\) by A15. Even evaluating arbitrary algebraic-group invariant polynomials cannot distinguish some rational signed NO pairs.

Use the free table with \(n=2\) in A15. Over the algebraic closure an automorphism induced from the tangent can have any nonzero algebra determinant, because its character is \((\det g)^4\). Choose determinant \(-1\) to correct the odd frame change. Thus the pair belongs to the same geometric SL orbit while rationally having no signed transporter. A formal algebraic-group invariant is constant on the geometric orbit. This is a concrete distinction between geometric and rational orbit comparison, even before asking which invariants can be computed.

### A17. A bounded nullcone test does not recover even ordinary orbits

**Paired comparison.** Complete rational signed orbit equality suffices for \(H\); complete knowledge of membership in the geometric SL nullcone is too coarse even for ordinary equality.

Take rank-one and rank-two tensors in shape \(3\times3\times3\) with support in \(2\times2\times2\). The one-parameter determinant-one diagonal scaling \(\operatorname{diag}(t,t,t^{-2})\) in a mode sends either to zero as \(t\) tends to zero since both use only the first two coordinates there. Thus all positive-degree homogeneous polynomial invariants vanish on both, while a contraction rank distinguishes their ordinary orbits. The example works over the algebraic closure of any field. It establishes failure of the nullcone criterion rather than any claimed relationship between the two decision complexities. [Derksen and Makam, computational invariant theory](https://arxiv.org/abs/1512.03393)

### A18. High degree alone gives no arithmetic-circuit or decision lower bound

**Paired comparison.** The exponential degree obstruction in A14 is a genuine obstruction to polynomial-degree formal separation. It is compatible with low circuit size and trivial orbit decisions on that same subfamily.

Each \(\operatorname{SL}_n(\mathbb F_q)\) has exactly two orbits in its natural module for \(n\ge2\): extend a vector to a basis and adjust another basis vector to correct the determinant. Polarizing a formal invariant into low degree cannot evade A14. But the Moore polynomial
\[
 D(x)=\det(x_i^{q^{j-1}})_{1\le i,j\le n}
\]
is a nonzero formal invariant of exponential degree and has polynomial arithmetic-circuit size by repeated powering and a polynomial determinant circuit. Frobenius entrywise commutes with linear changes over \(\mathbb F_q\), and determinant-one changes preserve \(D\). Distinct highest monomials in the determinant expansion show the polynomial is nonzero. Its high degree therefore supplies no arithmetic-circuit lower bound. Equally, evaluating this particular invariant on rational vectors is usually useless here: for \(n\ge2\) every column is then the same.

### A19. A finite separating function count still leaves a polynomial information budget

For cubic ternary \(n\times n\times n\) inputs, any full orbit-separating list of \(\mathbb F_3\)-valued functions has length at least \(n^3-3n^2\). There are \(3^{n^3}\) tensors, each orbit has size at most \(|\operatorname{SL}_n(\mathbb F_3)|^3\le3^{3n^2}\), and \(r\) trits can give at most \(3^r\) values. Conversely a lexicographic canonical orbit representative gives a separating string of \(n^3\) trits with unbounded computation. Thus the information-theoretic count is polynomial and compatible with the hypothetical efficient fingerprints in A15. It imposes no uniform procedure for constructing them.

### A20. One free algebra family gives an exact extension-degree threshold

For \(k\ge2\) put \(n=2^k-2\) and \(A=F[x_1,\ldots,x_n]/(x_1,\ldots,x_n)^3\). Compare its multiplication table with an odd basis conjugate, over each \(\mathbb F_{3^r}\). The signed comparison holds exactly when \(2^{k-1}\mid r\).

Over every extension the algebra-isomorphism determinant image on the self-pair is \((E^\times)^{n+2}\), by the tangent and symmetric-square action, and all tangent determinants occur. The relative pair is multiplied by \(-1\). Normalization of unital multiplication isotopy gives a determinant-one transporter precisely when the algebra determinant can be made one. Thus the test is \(-1\in(E^\times)^{2^k}\). In a cyclic group of order \(3^r-1\) this means \(v_2(3^r-1)>k\). For odd \(r\) the valuation is one; for even \(r\) it equals \(2+v_2(r)\) by factoring \(3^{2u}-1\) and doubling. This supplies explicit unital commutative cube-zero examples without any assumption about \(H\). The threshold grows with dimension; no superpolynomial claim is made for this family.

### A21. A successful even extension can coexist with failure in every odd degree

**Paired comparison.** Existence of an even-degree-extension transporter does not imply a base signed transporter. The free tables in A20 give the stronger failure that every odd degree fails while every multiple of a specified even degree succeeds.

Take \(k=2\), or any \(k\) in A20. The ordinary transporter is defined already over \(F\), so the failure over odd degrees is purely orientation. Conversely, if a signed transporter exists over the base, scalar extension gives one over **every** degree. This is a direct counterexample to using a single even extension as a substitute for the rational SL decision; it does not invalidate norm descent under the coprimality assumptions in the earlier atlas. The example is field-natural, with exactly the same coefficients used at all degrees.

### A22. Graph-isomorphism hardness and a signed graph upper bound are different premises

**Paired comparison.** A reduction of signed ternary TI to ordinary GI implies \(H\). The ordinary reduction \(\mathrm{GI}\le_m\mathrm{TI}\) alone allows either ternary branch.

For the first, compose the signed-to-GI reduction with Grochow and Qiao's explicit graph-to-tensor reduction. In the second, the direction is into ordinary TI and supplies no map *from* signed TI. Even knowing ordinary ternary TI lies in the GI degree only identifies the ordinary target and does not construct the missing signed-to-ordinary map. The sign-rigid GL-equal pair in A15 rules out the much narrower idea of treating the two questions as the same orbit relation before applying a GI algorithm. [Graph-to-tensor reductions](https://arxiv.org/abs/1907.00309)

### A23. Ordinary canonization with a transporter is different from a signed normal form

**Paired comparison.** A polynomial-time \(\operatorname{SL}\)-canonical form table is sufficient for \(H\). An ordinary canonizer, even with one ordinary transporter to a canonical representative, does not directly give an SL certificate.

The first follows by equality of forms. For the second, the determinant of the resulting relative witness may be odd while another witness is even, since the whole ordinary coset may have an odd stabilizer. For an explicit compact example use a zero-padded zero tensor, whose stabilizer has every sign triple; choose an odd ordinary relative witness and the even answer is still YES. In the free orientation-rigid example of A15 an odd ordinary witness instead proves NO. Thus the same witnessed parity does not decide the signed comparison on general inputs. If the ordinary canonizer also returns generating matrices for the stabilizer, the sign subgroup is obtained by taking generator determinants, and the combined premise **does** imply \(H\).

### A24. A full invariant-ring existence theorem does not supply a uniform signed decision

**Paired comparison.** Polynomial-time evaluation of a polynomially enumerable family of invariant circuits that separates all rational signed orbits gives \(H\). Mere finite generation or degree bounds for generating invariant rings are different statements.

With the claimed circuits, compare the evaluation vectors and use ordinary fixed outputs. A13 gives low degree in the function-ring model without giving this efficient circuit list. A14 shows that a uniform polynomial degree requirement in the formal-invariant model is already false; A18 shows that high degree does not exclude a small circuit. Algebraic-group generators can also fail to separate rational orbits at all by A16. None of these distinctions assumes that the conjectured efficient rational fingerprint is false. [Invariant algorithms and orbit problems](https://arxiv.org/html/2306.03135v2)

### A25. Exponent-three permutation parity lifts differently in larger odd prime fields

**Paired comparison.** Over an odd prime \(p\), the permutation sign of a compact Baer group transporter is the quadratic character of its additive determinant. It is the full determinant-one test exactly in the special scalar group \(\mathbb F_3^\times=\{\pm1\}\), not in general.

Any transvection of \(\mathbb F_p^N\) is a product of odd-length cycles. A diagonal scaling acts on \(p^{N-1}\) copies of \(\mathbb F_p\), so its permutation sign is the quadratic character by Zolotarev's lemma, or directly by taking a generator acting as a single \((p-1)\)-cycle off zero. These transformations generate GL. In the class-two exponent-\(p\) groups the additional central shear has determinant one. For a concrete failure at \(p=5\), use the free alternating bracket \(\Lambda^2\mathbb F_5^4\) as center. Every automorphism total determinant is \((\det g)^4=1\), while conjugating the bracket output by a map of determinant \(-1\) makes all relative total determinants \(-1\). This is a square in \(\mathbb F_5\), so the group isomorphisms are all even permutations but none has determinant one. [Grochow and Qiao, Baer tensor comparisons](https://arxiv.org/abs/1907.00309)

### A26. Full field orientation is detected by all primary characters, not only quadratic ones

**Paired comparison.** For every fixed finite field \(F\), suppose ordinary TI can test the value \(1\) of every character of the original three-mode determinant group that has prime-power order. Their conjunction gives full SL-TI. Taking just characters of order two may lose information even on normalized algebra multiplication pairs.

The attainable determinant vectors form an ordinary coset. If the identity misses it, the quotient by the stabilizer image has a character nontrivial on the coset. Project it to a prime-power factor on which it remains nontrivial. Conversely every character test holds if identity occurs. Include an ordinary guard for the empty case and combine the constant many ordinary comparisons. For failure of quadratic information over \(\mathbb F_5\), take a free symmetric cube-zero algebra with tangent dimension two. Its algebra automorphism determinant is \((\det g)^4=1\). A basis conjugation of determinant \(-1\ne1\) in the raw algebra frame then makes an ordinarily equivalent pair with no determinant-one algebra isomorphism, while its relative sign data at the quadratic character are trivial. The older exact weighted character compiler supplies the same separation for prescribed mode characters. This conclusion concerns multiple characters of the same transporter coset, not independent witnesses on unrelated quantities.


## Ideals, central filtration, and group representations


### A27. Any cyclic coefficient ideal transfers an exact quotient comparison

The socle argument extends to every nonzero \(s\) in a finite commutative local \(R\), using \(R/\operatorname{Ann}(s)\) in place of \(E\). Multiplication by \(s\) gives an injective module map from that quotient into \(R\). Its equation with a matrix multiplication follows entrywise, so the tensor transporter equations reflect exactly; the annihilator lies in \(J\) because no unit kills \(s\). Invertible quotient witnesses lift, and the diagonal corrections with units congruent to \(1\) modulo \(\operatorname{Ann}(s)\) fix all supported coefficients. This transports the **whole** determinant profile from arbitrary intermediate quotient rings, including ramified ones, rather than just a residue field. For \(\mathcal O/(\pi^k)\) and \(s=\pi^a\) the lower ring is exactly \(\mathcal O/(\pi^{k-a})\).

### A28. Two ideal supports impose an actual common congruence

**Paired comparison.** If \(Rs_1\cap Rs_2=0\), their tensor coefficients can encode two quotient comparisons with a shared transporter. Separate ordinary YES answers need not give a shared YES.

Let \(I_i=\operatorname{Ann}(s_i)\). Equality in the sum of the two supported ideals splits into the two quotient equations by the direct sum. A pair of quotient matrices lifts to one matrix exactly when their images modulo \(I_1+I_2\) agree, since \(R/(I_1\cap I_2)\cong R/I_1\times_{R/(I_1+I_2)}R/I_2\). Over a local \(R\), invertibility of the glued lift follows from its residue. For an explicit conflict take \(R=\mathbb F_3[x,y]/(x^3,y^3,xy)\), \(s_1=x,s_2=y\). In scalar tensor format \(x+y\) and \(x-y\) have separately ordinary equivalent supported components. A common product of the three units would require opposite residues on the two cyclic ideals, which is impossible. This explains why independent successful signed or ordinary queries cannot be combined by merely aggregating their witness signs.

### A29. Positive joint signs cannot be inferred from all marginal sign tests

**Paired comparison.** Querying every character of one determinant coset detects joint orientation by A26. Querying the three coordinate marginals alone has an unconditional counterexample in format \(1\times1\times1\).

Over \(\mathbb F_3\) compare the scalars \(1\) and \(-1\), in the covariant tensor action. Each prescribed single mode can have sign \(+1\), by taking a different mode negative. Yet every actual triple has product \(-1\), so no triple is all-positive. In bimap coordinates the same signs are used, since inverses of \(\pm1\) coincide. Thus independent choices of local witnesses cannot be identified with the character separation argument. This example requires neither a large orbit nor a complexity assumption.

### A30. Parity factors along any odd-order group extension

For group isomorphism \(\phi:G\to G'\) taking \(N\lhd G\) to \(N'\lhd G'\), where \(|G|\) is odd, its permutation sign is the product of its signs on \(N\) and on \(G/N\) in ordered transversal frames. Indeed the quotient permutes fibers each of odd size; within every fiber the map is the same \(\phi|_N\) followed by a multiplication correcting the representative. Every translation of an odd-order group has odd cycles only, and the number of fibers is odd. When comparing arbitrary endpoint enumerations, multiply by the known signs of changing to these frames. This is valid for nonabelian \(N\) and does not require a split extension.

### A31. Odd-order graded parity is exact on actual witnesses, not on independent layer witnesses

**Paired comparison.** For a finite odd \(p\)-group, the sign of an actual isomorphism equals the product of the quadratic characters of its induced determinants along its exponent-\(p\) central series. Multiplying marginal allowed signs of the layers can falsely predict a total correction.

Apply A30 iteratively to the characteristic series \(P_1=G,\ P_{i+1}=P_i^p[P_i,G]\), whose quotients are elementary abelian and which terminates for finite \(p\)-groups. Use A25 on each quotient. For a counterexample to independent marginals take the extraspecial exponent-three group with two-dimensional central quotient and one-dimensional center. A bracket similitude with multiplier \(\alpha\) has determinant \(\alpha\) on both layers. Both marginal signs occur, but their total is always \(+1\). This is an incompatibility between independently choosing allowed layers, with no claim that the graded table determines group isomorphism.

### A32. A central shear can be odd in characteristic two

**Paired comparison.** The translation-neutrality in A30 is true for odd-order kernels. Extending it to even-order kernels is false even for an elementary abelian group.

In \(G=\mathbb F_2^2\) with \(N=\langle e_1\rangle\), the shear \(e_2\mapsto e_2+e_1\) fixes \(N\) and the quotient pointwise, but exchanges exactly \(e_2\) and \(e_2+e_1\). It is odd, while both layer signs are positive. In \(\mathbb F_2^n\) for \(n\ge3\) every transvection instead exchanges \(2^{n-2}\) pairs, an even number, so every invertible linear map is even. Thus the rule \(\operatorname{GL}_n=\operatorname{SL}_n\) over the binary field cannot be used as a uniform replacement for the group-permutation parity mechanism.

### A33. Regular permutation conjugacy and regular linear conjugacy have different orientations

**Paired comparison.** For a group of odd order, the sign of a permutation conjugator of two regular group actions genuinely tests even group isomorphism. On the same permutation matrices viewed as an odd-dimensional representation over \(\mathbb F_3\), determinant-one **linear** conjugacy simply equals ordinary linear conjugacy.

A regular permutation normalizer is the holomorph: the image of a chosen basepoint gives a translation and a basepoint-fixing normalizer acts by a group automorphism. Odd-order translations are even. Use the orientation-rigid extraspecial group from A31, and conjugate its regular action by an odd permutation. The resulting pair is ordinary-conjugate but has no even permutation conjugator. On the matrix side \(-I\) commutes with all of the matrices and has determinant \(-1\) because the representation dimension is odd. Composition supplies a determinant-one linear conjugator. Adding a fixed dummy coordinate also fails to preserve the gap, since a reflection in that dummy coordinate remains available. The contrast uses exactly the same group representations and changes the allowed conjugator group.

### A34. The augmentation ideal preserves permutation signs in linear conjugacy

**Unconditional exact transfer.** For finite nontrivial \(p\)-groups with \(p\) odd, take the representation by left multiplication on the augmentation ideal \(J_G\) of \(\mathbb F_p[G]\). It is faithful, and the possible determinants of matrix conjugators are exactly the signs of the corresponding group isomorphisms. Over \(\mathbb F_3\) this gives exact even-to-SL transfer, polynomial in Cayley-table size.

For faithfulness, if \(g\ne1\) acts trivially on \(J_G\), then \((g-1)^2=0\) using \(g-1\in J_G\); the distinct group elements \(1,g,g^2\) contradict this in odd characteristic. A group isomorphism induces a map on the regular algebra with determinant its permutation sign, and the quotient by \(J_G\) is fixed, so the sign is the same on \(J_G\). To bound all other conjugators, use that \(\mathbb F_p[G]\) is local with nilpotent augmentation radical. Its regular left socle is the one-dimensional fixed line generated by \(\sum_{g\in G}g\), lying inside \(J_G\). Every nonzero submodule meets that line by multiplying by powers of the radical. Hence \(J_G\) is indecomposable. Its module endomorphism ring is local by Fitting decomposition, and its action on the fixed line gives its residue field exactly \(\mathbb F_p\). A centralizer unit therefore acts as a scalar modulo its nilpotent radical, and has determinant \(\lambda^{|G|-1}=1\) for \(p=3\). For arbitrary odd \(p\) this value is still one, since \(p-1\) divides \(p^a-1=|G|-1\). Thus arbitrary conjugators have the exact signs claimed. This repairs A33 by removing the scalar correction through a specific indecomposable module, and does not claim polynomial dimension in a compact source presentation.

### A35. A faithful cubic augmentation quotient reads just the central sign

For a compact special exponent-three group \(G\), write \(X=G/Z\), \(Z=[G,G]\), \(n=\dim X,z=\dim Z\), and \(J\) for its group algebra augmentation ideal. The group acts faithfully by left multiplication on the regular module of \(\mathbb F_3[G]/J^3\). Its dimension is \(d=1+n+\binom{n+1}{2}+z\). On this module a group isomorphism has determinant \((\det g_X)^{n+2}\det h_Z\), and all lifts to matrix conjugators differ by a centralizer with image \((\mathbb F_3^\times)^d\).

The degree-one and degree-two layers of the Jennings graded algebra are \(X\) and the symmetric square of \(X\) plus the degree-two commutator copy \(Z\) for purposes of a determinant filtration. The dimension subgroup at level three is trivial for class two and exponent three, giving faithfulness. Canonical group maps preserve that filtration; the determinant on the symmetric square is \((\det g_X)^{n+1}\). In the regular module the commutant is exactly right multiplication by units. Their determinant is scalar residue to power \(d\) via the augmentation filtration. Thus on even \(n\) the chosen module reads the central determinant, not the group permutation sign on \(X\oplus Z\). All coefficients can be computed from the ordered augmentation monomials and the written class-two commutators, using only degrees below three. [Jennings' dimension subgroup theorem and graded basis](https://doi.org/10.1090/S0002-9947-1941-0004626-6)

### A36. A fourth augmentation layer restores the total sign on a specified parity class

**Unconditional exact transfer on a subclass.** In A35 take \(n\) even and \(n/2+z\) odd. Then the regular module of \(\mathbb F_3[G]/J^4\) has even dimension and SL linear conjugacy exactly reflects and lifts even group isomorphism. Its dimension is polynomial in \(n+z\), so this construction does not expand the group elements.

The third graded layer has a filtration with factors \(X\otimes Z\) and \(\operatorname{Sym}^3 X/\langle x_i^3\rangle\). In the restricted graded group algebra, the missing pure cubes correspond to exponent three. By the Jennings basis this accounts for all third-degree dimensions. In a triangular determinant computation on the symmetric cube (after extension to a splitting field), the exponent of each eigenvalue is \(\binom{n+2}{2}\); deleting the cube submodule subtracts \(3\). The exponent for \(X\otimes Z\) is \(z\) on \(\det g_X\) and \(n\) on \(\det h_Z\). Adding A35 gives total exponents congruent to \(n/2+z\) and \(1\) modulo \(2\) for even \(n\). The module dimension has parity \(1+n/2+z\): the symmetric third-degree dimension \(\binom{n+2}{3}-n\) is even for even \(n\), and so is \(nz\). The canonical determinant therefore equals the total sign and the centralizer is even by regular-unit multiplication. The representation is faithful by A35. For an explicit low-degree table, write \(u_i=g_i-1\) for the chosen quotient generators and \(v_j=z_j-1\) for central generators, of weights one and two. Use the ordered monomials of weight below four with exponents at most two. Moving two out-of-order \(u\)'s past one another uses the product of the two \(1+u_i\)'s and the explicitly known central commutator \(\prod_k(1+v_k)^{\beta_{ij,j}}\), discarding all terms of weight at least four. Each correction has fewer noncentral letters, and the swapped term decreases inversions. There are polynomially many low-degree monomials. This computes the multiplication matrices of the compact generating group in the stated dimension. This gives an explicit polynomial-size construction on the stated parity class; no claim is made that this subclass already retains the full ternary gap. [Jennings' theorem](https://doi.org/10.1090/S0002-9947-1941-0004626-6)

### A37. Truncating at two layers can destroy even ordinary group information

**Paired comparison.** The faithful representation in A35 reflects group isomorphism. At \(J^2\) the analogous group image cannot in general recover ordinary group isomorphism.

Modulo \(J^2\), every commutator \(c\) satisfies \(c-1=0\); the group image acts by \(1+x\) in the square-zero algebra \(F1\oplus X\). Thus it depends just on the elementary abelian quotient. For a concrete pair, take groups on \(X=F^4\), one with nonsingular scalar alternating commutator and the other with the free output \(\Lambda^2 X\). Their centers have dimensions one and six, so they cannot be ordinarily isomorphic. Their actions modulo \(J^2\) are the same standard four-parameter elementary-abelian action. Faithful reflection in A35 is an essential change of truncation level, not a computational assumption.

### A38. Raw monomial tensor rules admit an exact parity-relational reduction

For explicit ternary tensors with the allowed mode maps restricted to monomial matrices, each comparison reduces, preserving the full three-sign profile, to colored relational isomorphism with prescribed permutation signs on three specified unions of colors. Give each coordinate line one vertex and two attached vector vertices \(+e,-e\), separately colored by mode. For an ordered triple of signed basis vectors include a relation precisely when the tensor evaluation on their indexed coordinates is \(+1\). The zero entries have no such tuples. For any isomorphism of the signed fiber incidence, its line permutation and pair flips give a unique monomial map; preserving the displayed relation is exactly tensor equality since both signs of each coefficient are sampled. Conversely every monomial transporter extends. On one mode, the permutation sign on both line and vector vertices is \(\operatorname{sgn}(\pi)\prod_i\epsilon_i\), because permuting two two-element fibers is even, while individual flips contribute \(\epsilon_i\). This is exactly its linear determinant. The representation has polynomial size without expanding \(F^n\). The atlas's square-zero relational algebra carrier can then serve as an algebraic target for any selected combination of these signs.

### A39. Equivariantly selecting coordinate rays cannot monomialize a full linear action

**Paired comparison.** The polynomial compression in A38 depends on given monomial fibers. Replacing arbitrary vector coordinates by a polynomial-size invariant spanning set of actual rays in the natural full \(\operatorname{SL}_n(\mathbb F_3)\) action is impossible.

The full special linear group is transitive on nonzero vectors for \(n\ge2\), by extending to bases and adjusting the determinant in a second coordinate, hence transitive on projective rays. Any nonempty invariant set of rays is therefore the set of all \((3^n-1)/2\) rays. Equivariance on a natural tested mode with a full special linear stabilizer already forces this size. This rules out the proposed ray-selection mechanism, not arbitrary auxiliary representations or task-dependent ordinary reductions.


### A40. On individually matched line roles, all sign products have one ordinary compiler

**Paired comparison.** In an ordinary typed comparison whose tested modes are sums of explicitly identified ordered one-dimensional roles, any prescribed product of the mode determinants has one ordinary TI compiler. Mere invariance of an unordered family of lines does not supply this construction.

Each role is forced to the same named role at the target. Link their scalar maps by nonzero bilinear products into successive one-dimensional output roles, and pin the final scale to the desired product. Any eligible transporter extends through the product maps; every extension forces the same scalars. With arbitrarily many roles use the previously proved fixed-signature packing of typed constraints. In the unordered model the determinant also contains the unknown permutation sign. In a self-instance swapping two identical one-dimensional components contributes \(-1\) while neither individual scalar need change. Omitting that permutation can therefore give an incorrect sign calculation. Compare A38 for the exact monomial accounting. [Typed tensor systems](https://arxiv.org/html/2306.03135v2)

### A41. Projective permutation sign depends on the parity of the ambient dimension

For \(q\) odd, the permutation sign of \(g\in\operatorname{GL}_n(\mathbb F_q)\) acting on projective points equals \(\chi(\det g)^{n-1}\), with \(\chi\) the quadratic character. Transvections have odd order. For a diagonal generator scaling the first coordinate by \(a\), the hyperplane \(x_1=0\) is fixed pointwise and the affine chart \(x_1=1\) identifies with \(\mathbb F_q^{n-1}\), scaled by \(a^{-1}\). Apply the elementary cycle argument of A25 to its determinant. These generators establish the formula. Thus projective points detect the sign in even dimension but completely erase it in odd dimension. Merely passing from vectors to rays without accounting for dimension can lose the test.

### A42. Grassmann actions have an exact quadratic determinant exponent

For \(q\) odd and \(1\le k\le n-1\), the permutation sign on \(k\)-dimensional subspaces is
\[
 \chi(\det g)^{\,k{\,n-1\brack k\,}_q}.
\]
For a first-coordinate diagonal scaling, a \(k\)-space in the complementary hyperplane or containing the first coordinate line is fixed. Each other space is a nonzero graph of a functional on a \(k\)-space in the complementary hyperplane; adjoining its zero functional gives an affine \(\mathbb F_q^k\) where the action is scalar multiplication. Its sign is the quadratic character to the power \(k\). There are the Gaussian binomial number of such charts. Transvections again give even permutations. Modulo two the Gaussian binomial has the parity of the ordinary binomial, since \(q\equiv1\bmod2\) in its recurrence. This gives a sharp criterion for detecting linear sign by an intermediate Grassmann action, and gives legitimate cases where a larger subspace carrier has no sign at all.

### A43. Ordered vector frames of length at least two erase odd-field determinant parity

**Paired comparison.** The permutation action on the full vector set detects \(\chi(\det g)\). The action on ordered independent \(k\)-frames is always even for odd \(q\) and \(2\le k\le n\).

For a first-coordinate scaling by a generator of \(\mathbb F_q^\times\), the fixed frames lie in the complementary hyperplane; all other cycles have length \(q-1\). The number of frames in dimension \(n\) is \(\prod_{i=0}^{k-1}(q^n-q^i)\), divisible by \((q-1)^k\), as is their number in dimension \(n-1\) (including the case zero). Thus there are an even number of moving cycles for \(k\ge2\). As usual transvections have odd order. Consequently replacing vectors by ordered bases to make the group action free does not provide the desired orientation test. This is an exact comparison of two permutation representations of the same action.

### A44. Unordered subset relabeling can likewise erase vertex parity

For an ordinary permutation \(\pi\in S_n\), its sign on \(k\)-element subsets is \(\operatorname{sgn}(\pi)^{\binom{n-2}{k-1}}\). A transposition exchanges exactly the pairs of subsets containing exactly one of the two transposed points, paired by replacing that point. There are \(\binom{n-2}{k-1}\) pairs, and transpositions generate \(S_n\). In particular for even \(n\) the action on all two-element edge labels is always even, while the vertex action need not be. This is why orientation on the specified entity colors in the square-zero incidence construction cannot generally be replaced by orientation on its tuple color classes. The formula is independent of field and complements the Grassmann calculation.

### A45. Forgetting ordered polarizations changes symmetric parity but can preserve alternating parity

**Paired comparison.** Let two odd-dimensional spaces be paired perfectly into a scalar output, and consider the associated symmetric or alternating cross bimap, with the polarizations held in ordered roles. In both cases all ordered self-transporters have total sign \(+1\). Forgetting the order supplies an odd correction in the symmetric case, while evenness is unchanged in the alternating case.

If \(P,Q\) are the two ordered maps and \(\alpha\) the output multiplier, perfect pairing gives \(\det P\det Q=\alpha^n\). Multiplication by the output sign gives \(\alpha^{n+1}=1\) for odd \(n\). Swapping the two equal-dimensional polarizations has tangent determinant \((-1)^n=-1\). Its output action is \(+1\) in the symmetric case, \(-1\) in the alternating case. In the alternating case every unmarked transporter is a symplectic similitude with total sign \(\alpha^{n+1}=1\), even if it does not carry the designated pair of polarizations to itself. Twisting the one-dimensional output by \(-1\) therefore gives symmetric unmarked YES and alternating unmarked NO, despite ordinary YES for both and ordered signed NO for both. The example compares removal of polarization data, distinct from just fixing a scalar form.

### A46. Ordered scalar tuple comparisons and permitted output action are different orbit problems

**Paired comparison.** If the output isomorphism \(h\) of an alternating matrix space is prescribed, simultaneous congruence of the two resulting ordered tuples is decidable by the fixed-characteristic forms algorithm. A single such branch cannot substitute for comparison under an unknown \(h\).

For example, take an alternating tuple in which the first scalar form has rank two and the second rank four, with disjoint symplectic blocks and spanned two-dimensional output. Exchange the two output coordinates. The unmarked bimap pair is ordinarily isomorphic by that output exchange, but the fixed-identity output comparison is impossible by the different rank labels. More generally each fixed \(h\) must be checked with the **same** induced map on all linked forms; the determinant correction on its pointwise kernel can be computed by the adjoint algebra. Unknown output maps have many branches, even though each pinned branch is polynomial. Existing full compact-group lower reductions concern the unknown-output action. [Ivanyos and Qiao, simultaneous isometry](https://arxiv.org/html/1708.03495)

### A47. Normalized cube-zero multiplication has a rigid diagonal sign relation

**Unconditional.** In any even-dimensional ternary scalar-residue local associative multiplication algebra, every unital-table isotopy has the same sign in all three modes. For two independent unit calibrations of odd dimension this statement fails, even on a one-dimensional multiplication table.

Evaluating at the two units writes an isotopy as \((L_a\phi,R_b\phi,L_aR_b\phi)\). Unit determinants are the scalar residue to power the algebra dimension via the radical filtration. For even dimension they vanish as signs, giving exactly \((\det\phi,\det\phi,\det\phi)\). For \(F\) itself, the two unit signs vary independently and the triple is \((u,v,uv)\). Thus even on associative multiplications it matters whether one invokes a diagonal sign restriction or a zero-product determinant correction; changing the radical algebra dimension can change the exact attainable profile. Raw isotopy frames further multiply those triples by the explicit endpoint ratios before applying a decision.

### A48. Norm-one on cyclic subgroups cannot see the whole residue determinant

**Paired comparison.** The residue norm \(N_{\mathbb F_{3^r}/\mathbb F_3}\) gives the exact permutation sign on the additive coefficient vectors of that field. It cannot generally replace full coefficient determinant-one, even for scalars.

Multiplication by a generator of \(\mathbb F_{3^r}^\times\) is a single even-length cycle off zero, hence odd. This matches its norm to \(\mathbb F_3^\times\). By elementary row operations the general linear permutation sign is this norm of the determinant. For \(r>1\) choose \(a\ne1\) in the kernel of that norm. In \(1\times1\times1\), the tensors \(1\) and \(a\) are related by a norm-one mode scalar but cannot be related by an all-mode determinant-one map because each SL factor is trivial. Thus a norm-preserving permutation realization does not encode exact determinant-one, even though it can be used to test signs.

### A49. A field norm changes base signs according to the extension degree

**Unconditional contrast.** On a base determinant \(d\in\{\pm1\}\), restriction of scalars from \(\mathbb F_{3^r}\) reads \(d^r\). The exact same base-field transporter can consequently be even under the scalar-expanded permutation representation and odd in its original scalar frame.

For a linear map over \(\mathbb F_3\), its determinant after scalar extension as a coefficient matrix is still \(d\), while the determinant on the full underlying ternary space after restriction is \(N(d)=d^r\). Take a single coordinate reflection with \(r\) even. This is a concrete failure of **that** norm readout for even extensions. It does not rule out an alternative exact determinant compiler over the even extension, and illustrates why coprime-degree norm reflection is a separate hypothesis.

### A50. Distinct actual extensions can have the same associated graded additive dimensions

An exponent-three extraspecial group and the compact exponent-nine group with the same nonsingular commutator on two quotient variables and nonzero cube functional both have the same dimensions on center and central quotient, and the same commutator tensor there. They are not abstractly isomorphic because the exponents differ. The power function is an additional linear invariant in the elementary-center class: for odd \(p\), \((xy)^p=x^p y^p\) in class two when commutators have exponent \(p\). In the coordinate extension it is the carry term. Thus the determinant product formula from layer maps in A31 does not imply the layers and their commutator tables suffice to characterize the underlying isomorphism. A correct oriented comparison also needs those power constraints. The example shows precisely where omitting carries changes the ordinary problem.

### A51. Connected algebraic correction requires a statement about the determinant map, not only the group

**Paired comparison.** For a connected algebraic stabilizer over a finite field, a surjective determinant character with smooth connected kernel supplies all rational determinant corrections. Bare connectedness of the stabilizer does not do so.

The first is Lang's theorem applied to the connected character kernel, which lifts every rational point of \(\mathbb G_m\) through the exact sequence. For failure of the weaker property even in a connected example, use \(\operatorname{GL}_n\) with character \((\det g)^2\) over \(\mathbb F_3\). It is surjective geometrically but its rational image is trivial. The kernel is disconnected in odd characteristic. The same effect occurs in the free symmetric multiplication automorphism group: arbitrary tangent maps and unipotent shears have square determinant when the tangent dimension is even, as in A15. This is a concrete reason that geometric connectedness only of the larger stabilizer does not automatically remove orientation. [Lang, algebraic groups over finite fields](https://wstein.org/papers/bib/Lang-Algebraic_Groups_Over_Finite_Fields.pdf)

### A52. A common nondegenerate alternating form is a valid correction only on the action it controls

**Paired comparison.** A transporter preserving a named nondegenerate alternating form on one tested mode has determinant one on that mode in compatible symplectic frames. This does not correct the free action on a separate coefficient/output space.

The Pfaffian identity \(\operatorname{Pf}(G^{\mathsf T}BG)=\det(G)\operatorname{Pf}(B)\) proves the first assertion, with the numerical ratio of two endpoint Pfaffians if the frames differ. The earlier exact marked symplectic matrix-space carrier realizes arbitrary determinant characters entirely on the output. It has a named nonsingular alternating slice so every ambient map is symplectic, and every original weighted transporter lifts. A sign-rigid marked source can be turned into an ordinarily equivalent signed NO by an odd output reframe while adjusting the named covector, leaving the scalar ambient form unchanged. Hence the premise “a fixed nonsingular alternating form controls all determinant conditions” is false unless the output action is accounted for. A reduction of the remaining output-determinant question on that entire marked carrier would imply \(H\). [Ordinary classical tensor actions](https://arxiv.org/html/2306.03135v2)

## Scope

The new unconditional transfer works through arbitrary cyclic coefficient ideals and hence includes genuinely mixed characteristic. The augmentation-ideal construction and its explicit low-degree variants compare different linear models of the same group, while the invariant examples compare rational function, formal finite-group invariant, and algebraic-group invariant semantics. None proves or refutes unrestricted \(H\).


## Bounded controls

The chain-ring formula was checked against all 3,888 invertible \(2\times2\) matrices over \(\mathbb Z/9\), matching both equation sides for all six valuation patterns. The exact extension threshold passed 1,408 degree and exponent combinations. The Grassmann sign formula was checked by reduced row echelon enumeration of 2,902 subspaces in ten small cases. These finite checks supplement the written proofs and are not a decision test for the unrestricted problem.
