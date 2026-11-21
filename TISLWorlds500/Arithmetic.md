# Arithmetic and geometric comparisons in the strict ternary world

Write \(A=\mathsf{TI}_{\rm SL}(\mathbb F_3)\), \(B=\mathsf{TI}(\mathbb F_3)\), and \(H=(A\le_m^{\rm P}B)\). A **clash** is a proved implication to \(H\), usually from a specified conjunction. A **scope limit** is a counterexample to an intermediate equivalence or a missing implication. A **relative result** changes computational access to fixed languages and leaves standard arithmetic unchanged. The paired cases below always state what follows in each case, without assuming that the negative branch of an open premise is known.

## Arithmetic coefficient rings

### A01. Typed algebra encoding in positive characteristic

The two-tag free-algebra packing of the cross-world atlas works over any infinite effective integral domain, including \(\mathbb F_3[t]\). Use distinct nonzero scalar labels \(c_i\ne1\) on the master and occurrence slots of \(W\), chosen as distinct nonconstant polynomials over \(\mathbb F_3\). Give the two quotient idempotents left actions \(L_1=\operatorname{diag}(c_iI)\) and the nilpotent \(L_2\) that encodes the linked linear arrows. Keep right actions zero and products of private occurrences in the annihilating output slots \(W_1\). Then \(W\) is the largest nilpotent ideal, and the unique lifts of the quotient idempotents follow from \((I-L_j)w=w^2\in W_1\) and injectivity on \(W/W_1\). The two tags are distinguished by nonnilpotence versus nilpotence of their left actions on \(W\), even when their traces coincide in characteristic three. Distinct labels force preservation of each individual slot because their difference is a nonzero element of the domain. The remaining equations recover the typed maps, and any linked transporter lifts.

**Paired cases.** In a domain with distinct labels this bidirectional reflection is exact. A residue at which two labels coincide need not preserve the reflection proof, so the generic marker argument gives only forward extension there. Over a domain the action \(5\)-to-\(1\) algorithm of Theorem 3.7 then reduces these free algebra tables to one ordinary free three-tensor comparison. [Grochow–Qiao–Stange–Sun, Theorem 3.7 and §3.3.2](https://arxiv.org/html/2611.00735v1#S3.SS3)

### A02. Uniform transfer from all explicitly represented ternary extensions

Given any monic irreducible \(f\in\mathbb F_3[t]\), full signed TI over \(E=\mathbb F_3[t]/(f)\) reduces deterministically to one ordinary free TI comparison over the fixed ring \(R=\mathbb F_3[t]\). Choose an auxiliary polynomial \(g\) coprime to \(f\), for example \(g=tf+1\). Use the full inverse image of the tensor graph modulo \(f\) on \(X\otimes_RY\oplus Z\). In each framed mode use a pinned identity graph modulo \(g\). These are sublattices supplied by triangular injective matrices with diagonal entries \(1,f\) or \(1,g\). Any linked ordinary \(R\)-transporter satisfies the residue tensor equation and is congruent to identity modulo \(g\). Its determinant is a nonzero constant, hence is one. Conversely elementary matrices generate \(\mathrm{SL}_n(E)\); their coefficients lift by CRT to coefficients zero modulo \(g\), giving the required integral role maps. In dimension one the allowed map is the identity. Apply A01. Both sides use the same ordinary ring for every degree.

**Paired cases.** A signed residue YES lifts to an ordinary polynomial-ring YES. A signed residue NO stays NO even if it has an ordinary residue transporter. In the strict ternary world, even the degree-one image family cannot have a deterministic ordinary reduction back to \(B\).

### A03. Nonreduced polynomial quotients transfer as well

A02 also works when the supplied monic \(f\) is reducible or has repeated factors, as long as \(\deg f>0\). Over \(\mathbb F_3[t]/(f)\), reason by its CRT decomposition into local principal factors. Each determinant-one matrix is elementary by local elimination and CRT, including the nonreduced local factors. The construction writes the same congruence matrices, without factoring \(f\); the factorization is used only in the proof of witness lifting. The auxiliary \(tf+1\) is still coprime. This gives one ordinary free \(R\)-comparison for the full signed action, uniformly on explicitly presented quotients of unbounded nilpotence depth.

**Paired cases.** Repeated roots do not change correctness. Replacing the congruence modulus by its squarefree part changes the comparison in general, already for signed format \(1\times1\times1\) and distinct scalars equal modulo that squarefree part.

### A04. Local genus over a function ring loses the global sign

Take irreducible \(f\) in A02. The two outputs are ordinarily equivalent over every prime localization of \(R=\mathbb F_3[t]\) if and only if the original ternary extension pair is ordinarily equivalent. At the prime \((f)\), the pins are invertible and the residue comparison is ordinary. At primes dividing the auxiliary polynomial, the graph modulo \(f\) imposes no condition and the identity satisfies the pins. Elsewhere both presentations are invertible. Over the fraction field both are invertible. The A01 proof applies on all these domains to the same algebra table. The published direction \(5\)-to-\(1\) in §3.3.2 uses input blocks and fixed identity tensors and has the same correctness after these domain extensions, so the statement holds also for its actual ordinary free tensor outputs.

**Paired cases.** Signed residue YES gives a global and all-local YES. Ordinary residue YES with signed residue NO gives all-local YES and global NO, e.g. the earlier \(A(x,y)=\operatorname{diag}(xI_3,yI_4,(x+y)I_5)\), \(B(x,y)=A(-x,y)\), with \(f=t\). No conjecture is needed.

### A05. Every finite modulus can pass on the same global function-ring NO

In the A04 counterexample, ordinary equivalence holds modulo every nonzero ideal of \(\mathbb F_3[t]\). A localized isomorphism at a prime reduces to each of its prime-power quotients, and CRT combines those maps. This works for both the intermediate algebra and the actual free tensor outputs. The rational-function comparison and the same pair over every completion, including the field completion at infinity, also pass. The global obstruction is a compatibility condition on units of the polynomial ring, which are simultaneously constant across all finite primes.

**Paired cases.** All congruence tests are necessary for a global ordinary comparison of free ring tensors. Even the entire infinite family of such tests is insufficient on this explicit carrier.

### A06. Logarithmic polynomial degrees suffice for the fixed-field carrier

For the fixed ternary source one may use \(f=t\), \(g=t-1\) and enumerate distinct nonconstant labels \(c_i\) of degree at most \(1+\lceil\log_3(N+1)\rceil\) for the \(N\) typed slots. Because each data entry is a constant or linear polynomial, only these labels contribute above degree one. The subsequent ordinary free-tensor compilation copies these coefficients and adjoins constant identity gadgets. Thus in the \(\neg H\) world a return reduction to \(B\) fails even on a family over \(\mathbb F_3[t]\) with entry degrees \(O(\log L)\), where \(L\) is the ternary input length.

**Paired cases.** A polynomial-time decision algorithm for this ordinary bounded-degree family implies \(H\). A polynomial-time algorithm over \(\mathbb F_3(t)\) alone would return YES on the entire fixed-format image and gives no such decision.

### A07. Exact Laurent-polynomial transfer despite infinite units

Take \(R=\mathbb F_3[t,t^{-1}]\), data modulus \(t+1\), and pin moduli \(t-1\) and \(t^2+1\). Its units are \(ct^k\). Congruence to one modulo \(t-1\) forces \(c=1\). The class of \(t\) in \(\mathbb F_3[t]/(t^2+1)\) has order four, so the second pin gives \(4\mid k\). Hence any allowed unit reduces to one at \(t=-1\), as needed for ternary signed reflection. Elementary lifts obey both pins by CRT. The free algebra and free tensor encodings of A01 apply.

**Paired cases.** With both pins every original signed NO reflects. With only the pin at \(t=1\), the unit \(t\) still reduces to \(-1\) at the data place and supplies the missing sign via a diagonal matrix.

### A08. The exact determinant screen after a localization

Fix coprime data and pin moduli \(f,g\) and localize \(R=\mathbb F_3[t]\) by inverting a polynomial coprime to both. On the resulting congruence family define
\[
D=\{u\bmod f:u\in R_{\rm loc}^{\times},\ u\equiv1\bmod g\}.
\]
The ordinary localized diagram isomorphisms exist precisely when there are residue tensor transporters with all three determinants in \(D\). Reflection is immediate. For lifting each residual role map, first choose a permitted unit realizing its determinant and remove the diagonal matrix \(\operatorname{diag}(u,1,\ldots,1)\). Lift the residual determinant-one part by elementary matrices via CRT and put the diagonal matrix back. Equality of the graph images gives the domain maps. This is an exact test of localization effects, not a necessary-only condition.

**Paired cases.** For \(f=t\), \(g=t-1\), inverting \(t+1\) makes \(-(t+1)\) a unit congruent to one at the pin and to \(-1\) at the data place, so the comparison becomes ordinary. Inverting \(t^2+t+2\), which is irreducible and has residue \(2\) at \(0\) and \(1\) at \(1\), likewise removes the sign; inverting instead an irreducible polynomial congruent to the same nonzero constant at both places, e.g. \(t^2-t+2\), preserves the signed comparison. For the last polynomial the unit group is generated by constants and its powers, whose two residues are identical.

### A09. Equal-characteristic CRT data can impose several independent comparisons

At pairwise coprime monic moduli \(f_i\), one common polynomial-ring linked diagram can impose different tensor equations on the same framed roles. If the role determinants are fixed to one by a further coprime pin, then such a diagram is isomorphic exactly when the signed comparisons at every \(f_i\) are YES. Any family of componentwise elementary lists lifts across all conditions by using coefficients supported at only the desired CRT factor. If no extra pin is imposed, each role instead has a common nonzero constant determinant across all residues, and the same proof lifts all choices with those common determinants. This is a finite conjunction with a precise shared determinant constraint.

**Paired cases.** With the pin each of the independent local signed answers survives. Removing the pin permits negative constant determinants only when one common triple of signs works across every component, which differs from testing completely independent ordinary comparisons.

### A10. The arithmetic localization effect also occurs in mixed characteristic

For the integer construction of the prior atlas with data mod \(3\) and pin mod \(5\), localizing to \(\mathbb Z[1/2]\) makes the congruence comparison exactly ordinary ternary TI. The unit \(-4\) is \(1\bmod5\) and \(-1\bmod3\); lift a general determinant by that unit and a CRT elementary correction as in A08. Localizing instead to \(\mathbb Z[1/31]\) preserves the signed comparison: units are \(\pm31^k\), \(31\equiv1\bmod 3,5\), and the mod-five pin forces the initial sign to be positive.

**Paired cases.** Both localizations retain the two designated residue rings. One erases the global unit obstruction and the other preserves it, so retaining the residue rings alone does not preserve the arithmetic comparison.

### A11. More ordinary target actions over the same function ring inherit the bridge

Theorem 3.7 applies over the fixed diagonal-full domain \(\mathbb F_3[t]\). Therefore A02, followed by its exact action equivalences, maps signed ternary TI to ordinary matrix-space conjugacy and to ordinary symmetric three-form equivalence over \(\mathbb F_3[t]\). These targets are concrete further arithmetic families, with polynomial coefficient size and no extra determinant restriction. The source \(f=t\) suffices for the strictness consequence.

**Paired cases.** An ordinary polynomial-time return reduction for either image family implies \(H\). A same-ring equivalence between the two ordinary target models is unconditional and does not remove the determinant sign over \(\mathbb F_3\). [Grochow–Qiao–Stange–Sun, Theorem 3.7](https://arxiv.org/html/2611.00735v1#S3.SS3)

### A12. Unit screening extends to suitable global function rings

Let \(R\) be a fixed \(S\)-integer ring in a global function field of odd characteristic with a prime of residue \(\mathbb F_3\). Its unit group modulo squares is finite by the \(S\)-unit theorem. Each unit class negative at that prime is a nonsquare in the function field, because a square root of a unit has zero valuations outside \(S\) and is an \(S\)-unit. For each such class choose a distinct allowed place at which the corresponding quadratic extension is inert. The global function-field Chebotarev theorem supplies such places, using the admissible odd-degree progression if the quadratic extension is constant. The combined pin ideal excludes all negative classes. The free covering congruence maps from the prior atlas handle nonprincipal ideals, and CRT gives elementary lifts. A01 and the diagonal-full theorem apply to the resulting domain.

**Paired cases.** For a fixed ring these finitely many prime choices are hardcoded and give an unconditional exact ordinary compiler. Uniform polynomial construction of those constants from arbitrary varying function fields is a separate assertion. [Effective function-field Chebotarev](https://doi.org/10.1112/blms/24.1.52), [Grochow–Qiao–Stange–Sun, Theorem 3.7](https://arxiv.org/html/2611.00735v1#S3.SS3)

## Prime screens, arithmetic genus, and genuine algorithmic inputs

### A13. A genuine Dirichlet-GRH prime-screening bridge

For a supplied nonsquare integer \(u\ne0\) and a nonzero forbidden modulus \(M\), the Dirichlet extended RH gives a deterministic polynomial-time search for an odd prime \(p\nmid 2uM\) with \((u/p)=-1\). Work modulo \(4|uM|\), through which the quadratic character of \(u\) factors. Its kernel is a proper subgroup of the units. Bach's bound gives a positive unit outside it of size \(O(\log^2|4uM|)\). Such a number has a prime factor outside the kernel, since the character is multiplicative, and every prime factor avoids the modulus. Enumerate the primes up to this bound and evaluate the Jacobi symbol.

**Paired cases.** The Dirichlet GRH gives the stated uniform complexity guarantee for these inputs. Without it Chebotarev still assures a prime exists, and the fixed finite lists in the prior number-ring construction can be hardcoded. This is a bridge to auxiliary prime choice, not a proof that standard GRH implies \(H\). [Bach, explicit subgroup bounds](https://doi.org/10.1090/S0025-5718-1990-1023756-8)

### A14. Effective Chebotarev with forced exclusion of bad primes

Given a Galois extension \(L/\mathbb Q\) and a supplied list of primes to exclude, put \(d\) equal to their squarefree product. Adjoin \(\sqrt d\) (unless the list is empty). Every excluded prime ramifies in this quadratic field, so is excluded when using an unramified Frobenius prime in the compositum. Any prescribed conjugacy class of \(\mathrm{Gal}(L/\mathbb Q)\) has a lift. The compositum has degree at most \(2[L: \mathbb Q]\), and \(\log|\Delta_{L\mathbb Q(\sqrt d)}|\) is bounded by \(2\log|\Delta_L|+[L: \mathbb Q]\log|\Delta_{\mathbb Q(\sqrt d)}|\), by the compositum discriminant bound. Thus effective least-prime Chebotarev under the Dedekind GRH for the relevant extension gives an upper bound polynomial in these explicit degree and logarithmic discriminant parameters. The same exclusion trick works with the larger unconditional effective bound.

**Paired cases.** With polynomial bounds on these written parameters and a usable small-residue test one can scan bounded primes. A compact input tensor alone does not supply a polynomial-degree component splitting field or a polynomial logarithmic discriminant, so this does not yield unrestricted signed descent. [Bach–Sorenson](https://doi.org/10.1090/S0025-5718-96-00763-6), [Ahn–Kwon, unconditional effective bound](https://www.numdam.org/item/AIF_2019__69_3_1411_0/)

### A15. Transitive finite components have a bad Frobenius class

A nontrivial transitive Galois action on a geometric component set of an arithmetic transporter has a derangement: the average fixed-point count is one by Burnside and the identity has more than one. Outside the model's finitely many bad primes such a Frobenius class gives a residue field with no transporter by Lang. For a supplied finite splitting field and good-model exclusion list, A14 bounds the first such prime under its GRH hypothesis. For arbitrary nontransitive actions the assertion fails. For example \((x^2-13)(x^2-17)(x^2-221)\) has no rational zero and has a zero in every completion. At unramified odd primes at least one of the three squareclasses is positive by multiplicativity. At \(13\) and \(17\), the other prime is a square locally, and at \(2\), \(17\equiv1\bmod8\) is a square. There is a real root.

**Paired cases.** A nontrivial transitive action forces some missing local class. A union of several orbits can hit every Frobenius class without any rational point. [Lang](https://wstein.org/papers/bib/Lang-Algebraic_Groups_Over_Finite_Fields.pdf), [Chebotarev](https://websites.math.leidenuniv.nl/algebra/chebotarev.pdf)

### A16. A pure finite-component Hasse failure in format \(4\times4\times4\)

Let \(E=\mathbb Q(\sqrt{13},\sqrt{17})\), and twist its multiplication tensor with diagonal reflections of determinant \(-1\) on each of the three modes. The earlier autotopism identity says the two tensors are signed-equivalent over a field exactly when \(E\) there admits an odd algebra automorphism. In detail the determinant tuple of any autotopism is \((a d,b d,ab d)\) for two unit norms and automorphism determinant \(d\). Requiring \((-1,-1,-1)\) forces \(d=-1,a=b=1\), so there is no norm obstruction.

Over \(\mathbb Q\) the four embeddings are regularly permuted by the Klein group, whose nonidentity elements are even double transpositions. At \(13\), \(17\equiv4\bmod13\), and at \(17\), \(13\equiv8^2\bmod17\). Thus no ramified place has full Klein decomposition group. Other finite places are unramified and have cyclic decomposition groups, and the real algebra splits. Each local factor therefore has degree at most two. A degree-two component provides an odd conjugation, and a split algebra provides an odd swap. The tensors have the same closed geometric signed orbit by the diagonal multiplication result in the prior atlas.

**Paired cases.** The twist is locally signed YES everywhere and rational signed NO. The obstruction is the component sign itself, independent of the prior norm twist on the same field.

### A17. Four is the minimum for this automorphism-only norm-free construction over \(\mathbb Q\)

No étale algebra of degree at most three over \(\mathbb Q\) can have even automorphism group at the base and an odd automorphism at every completion. A repeated degree-one component gives an odd swap at the base, and a quadratic factor gives an odd conjugation. The remaining possibility of degree three is a cubic field. Its transitive Galois group on its embeddings contains a 3-cycle, since its order is divisible by three. An unramified Frobenius of that cycle type makes it an unramified cubic at that place. All automorphisms there are powers of a 3-cycle and so even. Degree one is immediate.

**Paired cases.** Degrees at most three cannot supply the stated local/global parity failure. Degree four achieves it by A16, without a lower bound claim for arbitrary tensors or more general arithmetic obstructions.

### A18. The exact unramified parity detector is the distinct-odd cycle condition

Let \(E/\mathbb Q\) be any finite étale algebra with splitting group \(\Pi\) acting on its geometric embeddings. At a prime unramified in its splitting model let \(\ell_1,\dots,\ell_s\) be the Frobenius cycle lengths. The completion algebra has an odd automorphism precisely when at least one \(\ell_i\) is even or two odd lengths coincide. An even cycle gives an odd internal unramified Frobenius; two equal odd degree factors yield an odd block swap. Otherwise every factor is fixed and its internal permutations are even. Thus the local YES density of the triple-reflection twist is the fraction of elements of \(\Pi\) whose cycle lengths are not all distinct odd integers. This gives an explicit class function to which A14 applies.

**Paired cases.** Distinct odd lengths produce NO, including a single odd inert factor. Equal odd lengths can produce YES without any even factor. [Chebotarev](https://websites.math.leidenuniv.nl/algebra/chebotarev.pdf)

### A19. Infinite families of pure component failure in twice an odd prime degree

Fix an odd prime \(\ell\), take \(p\equiv1\bmod\ell\), and write \(K_p\) for the degree-\(\ell\) cyclic subfield of \(\mathbb Q(\zeta_p)\). Choose \(q\ne p\) splitting completely in the compositum of \(K_p\) and the splitting field of \(x^\ell-p\) with \(\mathbb Q(\zeta_\ell)\). Chebotarev gives infinitely many. Then \(q\equiv1\bmod\ell\), \(q\) splits in \(K_p\), and \(p\) is an \(\ell\)-th power modulo \(q\), so \(p\) splits in \(K_q\). The algebra \(E=K_p\times K_q\) has no odd automorphism globally: its factors have different ramified primes, and cyclic odd-prime automorphisms are even. At the two ramified primes the other factor splits, supplying an odd swap. At unramified primes either one factor splits or both are isomorphic unramified degree-\(\ell\) fields, whose interchange is odd. At infinity both cyclic fields split over \(\mathbb R\), because inversion of roots of unity acts trivially on each odd-degree quotient.

**Paired cases.** Every triple-reflection twist is rational signed NO and everywhere local signed YES. The two explicitly distinct cyclic cubics of conductors \(7,181\) are an example: \(181\equiv-1\bmod7\) and \(7^{60}\equiv1\bmod181\). [Chebotarev](https://websites.math.leidenuniv.nl/algebra/chebotarev.pdf)

### A20. An exact two-class local genus when the multinorm obstruction vanishes

For \(E=K_p\times K_q\) in A19, the two cyclic fields are linearly disjoint, so their product-norm equation satisfies the Hasse multinorm theorem. In the rational ordinary orbit of \(M_E\), let \((a,b,h)\) be the determinant correction of a twist and put \(d=ab/h\). Local signed equivalence to \(M_E\) says \(d\in\{\pm1\}\) and \(a/d,b/d\) are everywhere local norms. By the multinorm theorem the latter two are already global norms. The only remaining rational invariant is \(d\), because the rational algebra automorphism determinant is always \(1\).

**Paired cases.** The local genus inside the rational ordinary orbit has exactly two rational signed orbit classes. The trivial class has \(d=1\), and \(d=-1\) is a pure component class without a norm obstruction. [Pollio–Rapinchuk, main theorem](https://arxiv.org/abs/1203.0359)

### A21. Exactly eight rational signed classes in one closed local genus

Use \(E\) from A16, where the global field norm knot group has order two by Tate's formula for the biquadratic extension with cyclic decomposition groups. Use the same twist coordinates \((d,a/d,b/d)\) as A20. All local automorphism determinants allow both signs, and local norm membership of the other two coordinates is independent. Globally the automorphism determinant is always \(1\), and each norm coordinate is taken modulo the global norm group. Accordingly the rational signed orbit classes inside the local genus of \(M_E\) and its rational ordinary orbit are in bijection with the product of one sign group and two copies of the order-two norm knot group. Surjectivity follows by taking diagonal twists with any prescribed nonzero rational determinants in each mode.

**Paired cases.** One of the eight classes equals the original rational signed orbit. Seven give genuine rational NO comparisons despite local signed YES everywhere. This exhibits simultaneous independent finite-component and toric obstructions in one fixed closed geometric orbit. [Frei–Loughran–Newton, Theorem 6.1 and Lemma 6.5](https://arxiv.org/pdf/1508.02518)

### A22. Integer factoring is a genuine auxiliary input for the regular rational cube test

For the regular \(2\times2\times2\) rational stratum, the earlier atlas reduces signed comparison to equality of the binary slice discriminants and then two quadratic norm conditions. A rational ordinary transporter, in the equal-discriminant case, can be constructed by choosing invertible slices and changing the other normalized slices to their degree-two cyclic companion models. A cyclic vector can be found among the two basis vectors and their sum, since a nonscalar endomorphism cannot have all three of those lines as eigenlines. The two quadratic algebras are identified using the known rational square ratio of their discriminants. All these operations have polynomial bit complexity in fixed dimension. In the nonsplit case the two norms are decidable by checking quadratic Hilbert symbols at the primes dividing the numerators and denominators of the norm targets, the discriminant, or \(2\), and at infinity. At all other places the symbols are one. Given the prime factors, the odd-prime signs are computed by residue exponentiation and the \(2\)-adic one by valuations and odd units modulo eight. Hasse–Minkowski, applied to the norm conic, makes these tests sufficient.

**Paired cases.** A polynomial integer factorization algorithm gives a deterministic polynomial decision on this rational stratum. Its absence would remove that particular complexity guarantee and would not prove even this stratum hard or imply \(\neg H\).

### A23. Fixed-characteristic nonsquares need no GRH

Given an explicit finite field \(E\) of odd fixed characteristic, start at \(-1\) and repeatedly extract a square root when one exists. Each successful extraction doubles its multiplicative \(2\)-power order, because the square of an element of order \(2^{a+1}\) has order \(2^a\). This must stop within \(\log_2|E|\) steps. The final element is a nonsquare, and fixed-characteristic deterministic polynomial factoring supplies every root test and extraction. For characteristic three this gives a public representative of the nontrivial norm class to \(\mathbb F_3^\times\), as that norm is the exponent \((|E|-1)/2\).

**Paired cases.** Even-degree extensions do have public determinant norm-\(-1\) elements in polynomial time. The image of the base sign \(-1\) itself has norm \(+1\) in even degree, so finding a nonsquare does not repair the even-degree norm-only reduction issue. [Shoup, deterministic small-characteristic factoring](https://shoup.net/papers/quadfactor.pdf)

### A24. Small-prime-power classes can also be calibrated in fixed characteristic

Fix a prime \(\ell\) different from the characteristic and suppose \(\ell\mid |E^\times|\). Factor \(x^\ell-1\) to find a primitive \(\ell\)-th root, and repeatedly extract an \(\ell\)-th root of it while one exists. Every extraction increases the order by exactly a factor \(\ell\), since an \(\ell\)-th root of an element of exact order \(\ell^i\) has exact order \(\ell^{i+1}\). The terminal element generates the Sylow \(\ell\)-subgroup and is outside the total \(\ell\)-th-power subgroup. In fixed characteristic and for fixed \(\ell\) this is deterministic polynomial time by the same factoring routine. Its powers give explicit representatives of the cyclic quotient by \(\ell\)-th powers.

**Paired cases.** A fixed or polynomial-degree root polynomial fits the explicit algebraic model. This construction does not amount to a polynomial algorithm in \(\log \ell\) for an arbitrary variable prime order. [Shoup](https://shoup.net/papers/quadfactor.pdf)

### A25. Small-extension interpolation can avoid an irreducible-construction hypothesis

For a determinant pencil of explicit degree bound \(D\) in a fixed number of variables over \(\mathbb F_p\), construct a field of order greater than \(D\) only if \(p\le D\). Choose the least extension degree \(r\) with \(p^r>D\). Then \(p^r\le pD\le D^2\), so enumerating monic polynomials of degree \(r\) and testing irreducibility is polynomial in the written size and \(D\). Over this field the product interpolation grid detects whether the determinant polynomial is identically zero. If \(p>D\), work directly over the given field. This is a deterministic algorithm without GRH. It applies to polynomial coefficients only where the number of variables is fixed.

**Paired cases.** Fixed variable count yields a polynomial grid. Unrestricted variable count gives an exponential grid by this argument, irrespective of how cheaply the extension was constructed.

### A26. General variable-prime factoring and the fixed ternary kernel are different premises

For general variable \(p\), deterministic polynomial-time finite-field polynomial factoring is still a separate problem even under GRH. Existing conditional results place additional constraints on the Galois or association-scheme structure, or use different runtime bounds. Fixed-characteristic factoring, which is what the ternary centroid, finite étale decomposition and root calibration routines require, is already available. In particular replacing the variable-prime factoring conjecture by an oracle does not change the proof of any of those ternary subroutines.

**Paired cases.** A theorem in variable-prime factoring could discharge a genuinely factorization-dependent preprocessing stage. Neither that theorem nor its failure supplies the missing orientation-preserving reduction on arbitrary ternary tensors. [Guo, uniform \(P\)-schemes](https://doi.org/10.1016/j.jsc.2019.02.011), [Arora–Ivanyos–Karpinski–Saxena](https://arxiv.org/abs/1205.5653)

## Other number-theory and finite-field transfers

### A27. Principality is an exact fixed-format bridge, with a distinct complexity degree

The ordinary \(\mathbb Z^{2\times2\times2}\) comparison is polynomial-time equivalent to the principal ideal decision problem for real quadratic fields in the formulation of the cited theorem. This is genuinely an arithmetic equivalence, proved using quadratic composition laws, rather than an analogy involving tensor determinants. The unbounded-dimensional congruence carrier in the earlier atlas has growing formats and does not land in that stratum.

**Paired cases.** A polynomial classical principality test gives a polynomial classical decision on the fixed format. It yields \(H\) only if an additional reduction places the unbounded carrier into that format or otherwise returns its decisions to \(B\). [Grochow–Qiao–Stange–Sun, Theorem 1.7 and §4](https://arxiv.org/html/2611.00735v1#S4), [Bhargava, higher composition laws I](https://annals.math.princeton.edu/wp-content/uploads/annals-v159-n1-p03.pdf)

### A28. The quantum branch of the principality bridge

Hallgren's quantum algorithm gives the stated real-quadratic principality test a quantum polynomial-time bound. Consequently a hypothetical deterministic polynomial reduction from signed ternary TI to the ordinary integral cube stratum would give a quantum polynomial-time signed decision. One can turn the decision into a bounded-error quantum one-output map by printing a fixed \(B\)-YES or \(B\)-NO. If one additionally assumes \(\mathrm P=\mathrm{BQP}\), the same hypothetical compression would imply \(H\).

**Paired cases.** With that additional complexity equality the two premises clash with \(\neg H\). A quantum small-format algorithm without the compression supplies no bound for the variable-format seed, and the quantum bound alone is not a classical reduction. [Hallgren, Pell and principality](https://doi.org/10.1145/1206035.1206039), [Integral cube theorem](https://arxiv.org/html/2611.00735v1#S4)

### A29. Integral Hilbert's tenth problem separates computationally from integral TI

An integral tensor transporter is an existential system of polynomial equations over \(\mathbb Z\), with variables for the matrices and their inverses, or with chosen determinant-one equations. Thus ordinary and signed integral TI reduce computably, and via their usual formula encoding in polynomial time, to Hilbert's tenth problem over \(\mathbb Z\). Ordinary integral TI is decidable by Grunewald–Segal's arithmetic orbit algorithm, while signed integral TI is decidable by the same algorithm on the explicitly specified arithmetic determinant-one subgroup. The undecidability theorem for integer Diophantine solvability therefore rules out the reverse computable reduction to these problems.

**Paired cases.** Every integral transporter comparison can be made Diophantine. Arbitrary Diophantine instances cannot be made exact integral transporter comparisons by a computable map. This incompatibility is unconditional and does not establish a polynomial-time bound for integral TI. [Grunewald–Segal](https://annals.math.princeton.edu/1980/112-3/p04), [Davis–Putnam–Robinson](https://annals.math.princeton.edu/1961/74-3/p03), [Matiyasevich](https://m.mathnet.ru/php/archive.phtml?jrnid=dan&option_lang=eng&paperid=35274&wshow=paper)

### A30. The rational Hilbert's tenth problem supplies only a one-way decision premise

The same polynomial-equation construction over \(\mathbb Q\) puts rational tensor comparison below existential Diophantine solvability over \(\mathbb Q\), in either action. Denominator clearing is harmless for input coefficients, while the unknown matrix entries remain rational. A decision algorithm for the rational Hilbert's tenth problem would therefore decide the entire rational tensor problem.

**Paired cases.** The positive Diophantine decision branch supplies that upper bound. Undecidability of the full rational problem would not imply undecidability of its tensor subclass without a reverse reduction. This is a scope limit, not a claimed independence of the conjecture and the fixed ternary degrees.

### A31. GRH gives an AM upper bound for geometric comparison in characteristic zero

Over the algebraic closure of \(\mathbb Q\), the tensor equations form an explicit Hilbert Nullstellensatz decision instance of polynomial length. Invertibility is imposed by auxiliary inverse matrices if ordinary, and determinant conditions can be evaluated by division-free determinant circuits whose gates become polynomial equations if signed. Koiran's GRH-conditional Arthur–Merlin upper bound therefore applies to both geometric comparison languages on integer or rational input coefficients.

**Paired cases.** In the charged GRH branch both geometric languages have that AM upper bound. This neither decides rational transporters nor supplies an ordinary ternary reduction. Without GRH the AM conclusion is not supplied by this theorem, while geometric decidability remains unconditional. [Koiran, Hilbert's Nullstellensatz is in the polynomial hierarchy](https://doi.org/10.1006/jcom.1996.0019), [Parametric Nullstellensatz paper, §§1–2](https://epubs.siam.org/doi/10.1137/1.9781611978315.32)

### A32. Algebraically closed transporter tests are finite algebraic decisions without GRH

For any given tensors with coefficients in an effective field \(K\), existence of a transporter over its algebraic closure is equivalent to properness of the ideal generated by the exact transporter equations and inverse variables. Gröbner ideal membership or the Nullstellensatz decision algorithm determines whether this ideal contains \(1\). The two feasibility outcomes are separated by the same criterion in every characteristic.

**Paired cases.** If the ideal contains \(1\), the geometric comparison is NO over every extension. If it is proper, a geometric point exists; the same conclusion about a point over \(K\) can fail by the explicit closed ternary orbits in the prior atlas. The size of a Gröbner computation is not a polynomial reduction bound.

### A33. Unbounded tensor complexity is outside the elementary characteristic-transfer statement

For each fixed format, the existential transporter statement and any fixed-format universal equality between two polynomial representations are first-order formulas in field operations. Their algebraically closed truth in characteristic zero transfers to all sufficiently large characteristics, and conversely a fixed sentence true in infinitely many positive characteristics has the same truth in characteristic zero, by the completeness and compactness of algebraically closed field theories. Proof sizes and the characteristic threshold can depend on the fixed formula.

**Paired cases.** This transfers a specified algebraic assertion of fixed format. It supplies neither a threshold at characteristic three nor a uniform machine over unbounded input sizes, and hence does not decide \(H\). [Ax, elementary field theory](https://annals.math.princeton.edu/1968/88-2/p04)

### A34. Ordinary finite-field tensor equivalence also has nonprincipal extension spectra

For distinct primes \(p,q\), compare multiplication tensors of the two \(\mathbb F_3\)-étale algebras
\[
E_1=\mathbb F_{3^{pq}}\times\mathbb F_3^{pq},
\quad
E_2=(\mathbb F_{3^p})^q\times(\mathbb F_{3^q})^p.
\]
They are ordinarily equivalent after degree \(k\) exactly when \(p\mid k\) or \(q\mid k\). A field factor of degree \(e\) becomes \(\gcd(e,k)\) factors of relative degree \(e/\gcd(e,k)\). If \(p\mid k\) and \(q\nmid k\), each displayed algebra gives \(p\) degree-\(q\) factors and \(pq\) scalar factors. The other cases follow by symmetry or complete splitting. If neither divides \(k\) the degree multisets differ. Ordinary multiplication isotopy of a unital associative algebra normalizes to algebra isomorphism, giving reflection.

**Paired cases.** Degree \(p\) and degree \(q\) are both YES, while degree one is NO. This is an ordinary-target construction, so nonprincipal spectra are not themselves a distinction between unrestricted ordinary and signed actions.

### A35. Arbitrary finite unions of progressions occur in ordinary tensor comparison

For any positive period \(m\), multiplication of \(\mathbb F_{3^m}\) versus the split algebra \(\mathbb F_3^m\) gives ordinary equivalence exactly over degrees divisible by \(m\). Apply the prior ordinary disjunction gadget repeatedly to a list of these pairs. Its triangular-algebra product proof is valid over each extension with the same coefficients because it only uses ordinary component matching and associative unit-normalization. Balanced composition gives polynomial size in the sum of written side lengths. Thus every finite union of multiples occurs as an ordinary rational extension spectrum.

**Paired cases.** A degree divisible by at least one listed period succeeds, and a degree divisible by none fails. A field-natural target class constrained to principal spectra cannot realize this ordinary family either.

### A36. Split alternating-group classes explain a closed signed nonprincipal spectrum

In the split diagonal multiplication tensor's geometric signed orbit in odd characteristic, the component group of the split reference stabilizer is constant \(A_n\). Take \(n=p+q\) for distinct odd primes and let \(a\) be a product of one \(p\)- and one \(q\)-cycle, with \(b\) any odd-conjugate of \(a\) in \(S_n\). Its \(S_n\)-centralizer contains only even elements, since the cycle lengths are distinct and powers of odd cycles are even. Thus \(a,b\) represent different \(A_n\)-classes. Via Lang these give rational forms in the fixed closed signed orbit. On extension of degree \(k\), the comparison is conjugacy of \(a^k,b^k\) in \(A_n\). If \(k\) kills one cycle, its split fixed points allow an odd swap in the centralizer, and conjugacy holds. Otherwise the two distinct odd lengths persist and conjugacy fails.

**Paired cases.** The exact spectrum is multiples of \(p\) or \(q\), despite trivial Frobenius action on the split reference component group. This concerns comparison of two twists. The stabilizer Frobenius for either twisted endpoint can instead be inner conjugation and need not be trivial. [Lang](https://wstein.org/papers/bib/Lang-Algebraic_Groups_Over_Finite_Fields.pdf)

### A37. A combinatorial extension algorithm on the full split diagonal family

For two rational forms of the odd-characteristic split diagonal signed orbit, supply their \(A_n\)-classes as permutations. To test extension degree \(k\), power the two permutations and compare their cycle types. If different, answer NO. If equal, compare their \(A_n\)-classes: the \(S_n\)-class splits if and only if every length is odd and occurs only once. An even length gives an odd centralizing rotation, and a repeated odd length gives an odd centralizing swap. In the split case choose any combinatorial \(S_n\)-conjugator by matching cycles and compute its permutation sign, which is independent of this choice. This algorithm is polynomial in \(n+\log k\) and never has to build the extension field.

**Paired cases.** Centralizer parity is all the additional information after ordinary cycle type on the supplied representation. Extracting an analogous finite permutation model from arbitrary tensors is a separate problem.

### A38. A factored bound makes nilpotent extension-period search logarithmic in the bound

Suppose the nilpotent-component theorem of the prior atlas applies and its minimum period is known to divide a supplied factored integer \(N\). With an oracle for the extension-degree comparison, start at \(N\) and strip each prime factor whenever the smaller degree remains a YES. Since the spectrum is a single divisibility progression, termination yields the exact minimum after \(O(\log N)\) queries. This is a genuine use of factor data in an arithmetic restricted setting.

**Paired cases.** With explicit fields and a numerically polynomial bound \(N\), all queried fields can be built at polynomial cost in fixed characteristic. A merely polynomial bit length for \(N\) can still entail exponentially large explicit extension inputs; succinct access would be a separate oracle premise. [Shoup, irreducibles in small characteristic](https://www.shoup.net/papers/detirred.pdf)

### A39. Constant component quotients have reciprocal-image prime density

Let \(X\) be a geometric transporter of rational tensors over a number field and let its component scheme be a torsor under a constant finite group \(\Gamma\). It corresponds to a homomorphism of the absolute Galois group into \(\Gamma\), up to conjugacy. Write \(I\) for the finite image. Outside finitely many primes all points of the component scheme are fixed by Frobenius if its image is the identity, and none is fixed otherwise, because the action is by translations on the regular \(\Gamma\)-set. Lang on the connected stabilizer gives the same YES profile for reductions of \(X\). Chebotarev therefore gives density exactly \(1/|I|\), independently of whether the algebraic stabilizer extension has a rational section.

**Paired cases.** A density greater than one half already forces a rationally split component scheme. A split component scheme alone can leave a nontrivial connected rational torsor, as shown by the prior biquadratic norm twist. [Lang](https://wstein.org/papers/bib/Lang-Algebraic_Groups_Over_Finite_Fields.pdf), [Chebotarev](https://websites.math.leidenuniv.nl/algebra/chebotarev.pdf)

## Relative separation and scope for distant conjectures

### A40. The exact unrelativized collapse assertion has a low arithmetical form

Fix brute-force recursive membership tests for \(A,B\). Enumerate machines equipped with explicit polynomial clocks \(n\mapsto c(n+1)^d\). For a fixed machine and clock, whether a given string is mapped to a correct \(B\)-instance is recursive. Thus
\[
H\quad\Longleftrightarrow\quad
\exists e,c,d\ \forall x\ [M_{e,c,d}(x)\in B\ \Longleftrightarrow\ x\in A]
\]
is a \(\Sigma^0_2\) assertion in the arithmetical hierarchy, and \(\neg H\) is \(\Pi^0_2\). Using halting-oracle stages gives a decision by the second jump, since the predicate for one clock has only a recursively enumerable failure set.

**Paired cases.** Truth provides one uniform clock that works for all strings. Falsehood supplies a finite counterexample for every such clock. The quantifier bound neither separates the Turing degrees of particular arithmetic conjectures nor proves independence from PA or ZFC.

### A41. A computable counterexample stream is exact in the negative branch

Enumerate polynomial-clocked candidate maps. For the \(i\)-th map run the exhaustive, exact tests of \(A\) and \(B\) on inputs in length-lexicographic order until a mismatch appears. Under \(\neg H\) this process halts for each \(i\), and dovetailing gives a total computable sequence of counterexamples covering every candidate. A finite observed prefix can always be handled by a hardcoded map to canonical YES and NO instances.

**Paired cases.** If \(H\) is false all searches halt, with no useful uniform runtime promised. If \(H\) is true a correct clock never produces a mismatch. An arbitrary finite collection of observed mismatches is compatible with both cases.

### A42. Relative tensor strictness can change while all fixed arithmetic truth stays fixed

For the fixed standard languages \(A,B\), let \(H^O\) allow an external oracle in the reduction while leaving their definitions unchanged. The empty oracle yields \(H\). The recursive oracle \(O=A\) yields \(H^O\), since it decides the source and one prints either fixed target answer. Under \(\neg H\) these are two computable-oracle models with opposite relative collapse answers and identical interpretations of all oracle-free arithmetic and geometric predicates in the same standard model.

**Paired cases.** In the assumed strict world, any absolute sentence, including the standard versions of RH, GRH, Goldbach, twin primes, or \(abc\), has the same truth value in both relative examples, so no universally oracle-relative characterization of \(H^O\) by that sentence can hold. If \(H\) is true then every oracle preserves the reduction, so this argument gives no opposite pair. This is not logical independence of the unrelativized assertions.

### A43. Naming a recursive oracle gives a conservative definitional extension

For a theory supporting elementary coding of finite fields and matrices, one may add an oracle predicate defined by the brute-force arithmetic formula for \(A\), or instead define it to be always false. These are definitional extensions: eliminating the added predicate from any formula gives an old-language formula and preserves provability of old-language sentences. The trivial oracle-based reduction is available in the first interpretation and the second gives the original comparison. Thus the distinction between computational oracle access and an arithmetic theorem is also syntactic.

**Paired cases.** An oracle-defined proof can certify a relative reduction without adding an arithmetic axiom. A genuine unrelativized proof must eliminate the actual cost of computing that predicate, something conservative definitional extension does not do.

### A44. An undecidable arithmetic oracle erases the relative gap without deciding conjectures

Access to the halting language is sufficient to decide \(A\) in one polynomial-time query. From input \(x\), write a machine that runs the exact brute-force test and halts only if \(x\in A\). Its description length and construction time are polynomial in \(|x|\), regardless of its future runtime. This yields \(A\le_m^{\mathrm P}B\) relative to halting. The complete integer Diophantine decision oracle suffices as well in polynomial query-construction time for this fixed language. MRDP gives a fixed polynomial representing positive membership on natural-number codes. Substitute a binary integer code of the input and replace each nonnegative witness by a sum of four squares to allow integer variables. The fixed polynomial and fixed exponents give coefficients with polynomial bit lengths.

**Paired cases.** Powerful arithmetic decision access can erase the relative gap. That statement does not make Hilbert's tenth problem decidable, nor decide any of the fixed oracle-free conjectures. [Matiyasevich](https://m.mathnet.ru/php/archive.phtml?jrnid=dan&option_lang=eng&paperid=35274&wshow=paper)

### A45. Polynomial arithmetic predicates are inert as external oracle bits

If \(D\in\mathrm P\) is a fixed arithmetic decision language, any deterministic polynomial Karp map with oracle \(D\) can be simulated in polynomial time without it by simulating each query. Hence \(H^D=H\). Instances include primality by AKS, finite-field irreducibility by repeated Frobenius and gcd, and arithmetic equality of explicitly represented rationals. This is a direct scope result for the frequently proposed arithmetic oracles.

**Paired cases.** These polynomial predicates may simplify the presentation of a construction without altering its collapse degree. Harder search problems such as integer factorization do not follow from primality alone by this simulation. [Agrawal–Kayal–Saxena](https://annals.math.princeton.edu/2004/160-2/p12)

### A46. A precise factoring-oracle world and its limits

Let \(D(N,k)\) ask whether \(N\) has a proper nontrivial divisor at most \(k\). This language is in \(\mathrm{NP}\cap\mathrm{coNP}\): a divisor certifies YES, and a verified prime factorization certifies NO because the least proper divisor of a composite is its least prime factor. Given this decision oracle one can binary search the least divisor and recursively factor the quotient with polynomially many queries. Conversely a factorization gives each answer. Thus deterministic polynomial access to this oracle is equivalent to polynomial access to integer factoring search.

**Paired cases.** If general factoring is in deterministic polynomial time, this world has \(H^D=H\) by A45. If it is not, the equivalence still specifies the right oracle model, but it does not determine whether \(H^D\) holds.

### A47. An arithmetic prerequisite can be held fixed in generic-oracle comparisons

Take any fixed background oracle \(D\), such as the factoring predicate in A46. If \(H^D\) is false, the successful extra oracles \(O\) for \(H^{D\oplus O}\) form a meager set. For each clocked machine its successful set is closed, since a counterexample uses finitely many extra queries. An interior cylinder would permit hardcoding its finite prescription and declaring all other extra bits zero, giving a \(D\)-reduction and contradicting the premise. Countably many machines yield the conclusion. On the other hand adjoining \(O=A\) makes the collapse hold with this same background. If \(H^D\) is true, it survives all further joins.

**Paired cases.** In the negative background branch a generic extra oracle preserves strictness while a supplied decisive oracle erases it, holding the arithmetic background predicate fixed. This does not establish which background branch obtains for actual integer factoring.

### A48. Hodge data after complexification cannot certify rational descent by itself

Complexification can give identical cohomology and algebraic-cycle data to different rational forms. For a smooth example the conic \(x^2+y^2+z^2=0\) and \(\mathbb P^1_{\mathbb Q}\) are isomorphic after complexification, but have different rational point existence and hence cannot be rationally isomorphic. The projective determinantal suspension from the prior atlas yields the same obstruction on an explicit tensor-derived presentation: use the rational signed twist of A16 and apply the exact rational field construction. Its two complexifications are isomorphic while its two rational varieties are not. Those tensor-derived varieties need not be smooth, so the smooth Hodge conjecture is not being applied to them.

**Paired cases.** The complex Hodge conjecture, in Deligne's formulation, concerns rational Hodge classes of smooth projective complex varieties. Even complete information about such geometric invariants alone cannot certify rational descent. This is a scope result for that proposed method, not independence of the two unrelativized conjectures. [Deligne, official Hodge problem description](https://www.claymath.org/wp-content/uploads/2022/06/hodge.pdf)

### A49. BSD data of a Jacobian do not identify a specific torsor class

The Selmer plane cubic \(3x^3+4y^3+5z^3=0\) is a smooth genus-one curve with points at every completion and no rational point. It is a nontrivial torsor under its Jacobian \(J\). The curve \(J\) itself is the trivial torsor with a rational point. Their common Jacobian has the same \(L\)-function, Mordell–Weil rank and group of torsor classes in either comparison. Therefore attaching the Jacobian and its BSD invariants to a local-global comparison cannot distinguish the two particular torsors without information about their classes.

**Paired cases.** One torsor is globally soluble and the other is not, despite the same Jacobian-level arithmetic information. Even a theorem determining those BSD invariants is not an algorithm identifying each torsor class. No relationship between this example and the full fixed ternary collapse is asserted. [Selmer](https://doi.org/10.1007/BF02395746), [Clay's BSD description](https://www.claymath.org/millennium/birch-and-swinnerton-dyer-conjecture/)

### A50. Quartic local parity densities can be computed without counting points

For a quartic field, the only possible cycle partition of four with all lengths distinct and odd is \(3+1\). Thus its triple-reflection multiplication twist has an unramified local NO precisely at Frobenius 3-cycles. In \(S_4\) there are eight of them, giving local YES density \(2/3\). In \(A_4\) the same eight yield local YES density \(1/3\). For \(V_4,D_8,C_4\) no element has order three, so all unramified primes give local YES. This is an exact enumeration in natural quartic Galois permutation actions.

**Paired cases.** A missing local class can have positive density, or can be absent at every good prime. These are statements about local automorphism parity, regardless of the global norm image or the ternary degree question.

### A51. Density one among good primes can miss a concrete ramified obstruction

For \(E=\mathbb Q(\sqrt5,\sqrt{13})\), the triple-reflection twist of its multiplication tensor passes at every unramified finite prime, since all such decomposition groups in the Klein extension are cyclic and yield local odd automorphisms. At \(5\), the ramified extension by \(\sqrt5\) and the unramified extension by \(\sqrt{13}\) are distinct because \(13\equiv3\bmod5\) is nonsquare. Their compositum is a local Klein quartic field, with only even automorphisms. Thus the same twist fails at \(5\).

**Paired cases.** Every good-prime test succeeds, while a bad-prime comparison fails. A stronger bound for unramified Frobenius primes, even from GRH, cannot reveal a local obstruction that occurs only outside its good-reduction scope.

### A52. Regular cubes over \(\mathbb F_3(t)\) have an unconditional polynomial signed algorithm

For regular \(2\times2\times2\) tensors over \(K=\mathbb F_3(t)\), the same invertible-slice normalization and discriminant identity as the rational cube theorem reduce signed comparison to equality of discriminants and two norm conditions in a common quadratic étale algebra. In the nonsplit case use Hilbert symbols over the global function field, or equivalently its cyclic Hasse norm theorem. The only finite places to check divide the numerators or denominators of the discriminant or the norm targets, and the place at infinity must also be checked. Factor the input polynomials over \(\mathbb F_3\) deterministically. Each local symbol is computed from two valuations and a residue-field quadratic character, all polynomial in the explicit data. A cyclic companion basis and the square ratio used in identifying the quadratic algebras are obtained using the same constant-size linear algebra and polynomial factors. The split case needs no norm checks.

**Paired cases.** In this regular function-field format the arithmetic decision is polynomial without a conjecture about integer factoring or GRH. It does not decide ordinary \(\mathbb F_3[t]\)-TI on the much larger image family of A02. [Shoup, small-characteristic factoring](https://shoup.net/papers/quadfactor.pdf), [Frei–Loughran–Newton, norm context](https://arxiv.org/pdf/1508.02518)

The constructive bridges, arithmetic counterexamples and relative examples above are written proofs. They leave the unrestricted deterministic same-field ternary comparison open. [Chen–Grochow–Qiao–Tang–Zhang, Open Question 1.9](https://arxiv.org/html/2306.03135v2#S1.SS5)
