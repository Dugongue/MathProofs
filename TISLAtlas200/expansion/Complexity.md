# Additional complexity entries for the determinant-one TI atlas

Definitions and inherited proofs appear in the [earlier complexity chapter](../baseline/ComplexityWorlds.md), [fixed-field protocol proofs](../baseline/earlier/ComplexityWorlds.md), and [complexity transfers](../baseline/earlier/hypoworld/ComplexityTransfers.md).

Unless an entry states otherwise, the field is fixed \(\mathbf F_3\), tensors are dense with positive mode dimensions and fixed mode labels, \(A\) denotes determinant-one TI, \(B\) denotes ordinary TI, and \(H\) denotes \(A\le_m^P B\). Write \(H_R\) for randomized bounded-error many-one reducibility. \(G=\prod_i\mathrm{GL}_{d_i}(\mathbf F_3)\), \(K=\prod_i\mathrm{SL}_{d_i}(\mathbf F_3)\), and \(\chi:G\to D=\{\pm1\}^3\) is the determinant tuple. The entries below add models, conclusions, or constructions beyond the preceding 78-entry atlas. All proofs here are informal.

<a id="entry-119"></a>

### 119. Planted transporter search preserves arbitrary source distributions

For any common distribution of \(T\), compare planted pairs \((T,gT)\) with \(g\) uniform in \(G\) and \((T,kT)\) with \(k\) uniform in \(K\). An ordinary planted witness solver of success \(\epsilon\) gives a signed planted witness solver of success at least \(\epsilon/8\). Blind only the target of the signed pair by a fresh uniform \(u\in G\). The resulting solver input has exactly the ordinary planted distribution, with the original \(T\) unchanged. If the solver returns \(w:T\to ukT\), then \(u^{-1}w\) is uniform in the original ordinary transporter conditional on the blinded target and solver output. This follows since the fiber of \(u\mapsto ukT\) is a coset of the target stabilizer, and its image by unblinding is a bijection onto the transporter. Check the signs and witness. Conversely, on an ordinary planted pair run the signed solver on all eight reflected targets. The reflection matching the original sampled determinant tuple gives exactly the signed planted law after averaging over that sign, and any valid signed response for any reflection lifts to an ordinary witness. This reverse construction succeeds with probability at least \(\epsilon\). Approximate group sampling with error much smaller than \(\epsilon\) yields strict bounded-coin algorithms without changing the inverse-polynomial-success regime.

<a id="entry-120"></a>

### 120. Exact statistical distance between the two planted laws

For fixed \(T\), let \(m(T)=[GT:KT]\) mean the ratio \(|GT|/|KT|\), an integer in \(\{1,2,4,8\}\). With \(T\) included in the public challenge, the statistical distance between the signed and ordinary planted-pair laws is exactly \(\mathbb E_T[1-1/m(T)]\), for any distribution of \(T\). The ordinary law given \(T\) is uniform on \(GT\), the signed law is uniform on its subset \(KT\), and the common first marginal permits decomposing variation distance by fibers. If the sampler produces a split orbit only with probability \(\delta\), the distance is at most \(7\delta/8\). If signed decision lies in BPP, comparison of the challenge to its public source achieves this distance up to arbitrarily small inverse-polynomial additive error.

<a id="entry-121"></a>

### 121. Signed pseudorandom planting implies ordinary pseudorandom planting

Fix any efficiently samplable source and compare planting to the law with an independent uniform target of matching shape. The channel that applies a fresh uniformly random determinant representative to the target sends the signed planted law to the ordinary planted law. It preserves the independent uniform null law. Thus any PPT distinguisher of ordinary planting from that null law gives a PPT distinguisher of signed planting with the same gap, up to the sampling implementation error. The direction uses a randomized channel on the distributions, without any worst-case reduction hypothesis. An ordinary distinguisher advantage gives no corresponding bound for arbitrary signed source versus ordinary-yes target tasks.

<a id="entry-122"></a>

### 122. Passive leakage of the sampled determinant character

For fixed public \(T\), sample \(g\in G\) uniformly and reveal \(gT\). Given the revealed target, the determinant tuple of \(g\) is uniform in a coset of \(H_T=\chi(G_T)\). For any character \(\ell:D\to\{\pm1\}\), if \(\ell|_{H_T}\) is nontrivial, the bit \(\ell(\chi(g))\) remains exactly fair conditional on the entire target. If \(\ell|_{H_T}\) is trivial, the target determines the bit information-theoretically. Indeed any two group elements producing the same target differ by a source stabilizer element. The determinant tuple itself has conditional entropy \(\log_2|H_T|\), so its mutual information with the target is precisely \(3-\log_2|H_T|\). This is a statement about the hidden sampled transporter, independent of decision hardness.

<a id="entry-123"></a>

### 123. Signed-invariant tests of planted challenges

Let \(I\) be any efficiently computable complete or incomplete signed invariant with finite output. Comparing \(I(T)\) and \(I(U)\) always accepts signed planted pairs. On independent draws of the same source/target marginal with invariant distribution \((p_i)\), the false acceptance rate is exactly \(\sum_i p_i^2\). In particular any nonnegligibly nonconstant efficient invariant for that sampler yields a concrete nonnegligible planted distinguisher. A semi-invariant with \(I(gT)=\ell(\chi(g))I(T)\) qualifies as a signed invariant, even when its raw value is unsuitable for the ordinary planting test. For different independent marginals the corresponding rate is \(\sum_i p_iq_i\).

<a id="entry-124"></a>

### 124. Independently uniform balanced tensors are overwhelmingly nonisomorphic

Two independent uniform \(n\times n\times n\) tensors over \(\mathbf F_3\) have ordinary-isomorphism probability at most \(3^{3n^2-n^3}\). For any first tensor its orbit size is at most \(|\mathrm{GL}_n(\mathbf F_3)|^3<3^{3n^2}\), out of \(3^{n^3}\) choices. The bound also applies to signed TI. Thus the always-NO rule has negligible error on this input ensemble, in either world. This demonstrates why an average-case assertion relevant to strictness must identify a nontrivial sampling distribution.

<a id="entry-125"></a>

### 125. Birthday lower bound for opaque orbit sample distributions

In a sample-only model, let two unknown laws be uniform on identical or disjoint supports of size \(M\), encoded by fresh random labels in an ambient set of size at least \(2M\). A classical tester using at most \(q\) samples in total, allowing adaptive choice of sampler, has advantage bounded by \(O(q^2/M)\) under the two random-support priors. Couple each experiment to one that always emits a uniformly unused label. In either experiment, on a transcript of \(j\) distinct samples the next repeat has probability at most \(j/M\), and every unused ambient label is equally probable conditional on a fresh draw by exchangeability. The chance that either coupling fails is at most \(q(q-1)/M\). A lower bound of order \(\sqrt M\) follows. This model gives no lower bound for written tensor coefficients or queries supplying group elements.

<a id="entry-126"></a>

### 126. Exact instance-dependent statistically hiding commitments from tensor orbits

For any signed pair \(x=(T_0,T_1)\), a commitment to \(b\) samples \(gT_b\) with \(g\) uniform in \(K\) and opens by revealing \(g,b\). On signed YES the commitment distributions agree exactly with exact sampling. On signed NO no string opens to both bits, since the orbits are disjoint. A strictly bounded-coin version selects a uniform index by a bounded rejection draw and on rejection sends a separate tagged copy of \(b\). This preserves perfect binding on NO and permits arbitrarily small statistical hiding error on YES by using more bits. Open the bounded-coin commitment by revealing the actual coin string and the bit, and check the sample or the rejection tag from them. The public parameter is the input pair. This is an instance-dependent primitive and requires no assertion about the sampler of hard pairs.

<a id="entry-127"></a>

### 127. Finite-orbit membership gives a proof of knowledge with special soundness

For a signed YES pair, the standard three-message orbit protocol is a sigma-style proof of knowledge of a signed transporter. Commit with \(S=kT_0\), receive a fair bit \(b\), and answer with \(r_b\in K\) satisfying \(r_bT_b=S\). From two accepting responses to the same commitment at challenges 0 and 1, extract \(r_1^{-1}r_0\). Before rewinding no hidden stabilizer data is needed. In the usual black-box model, if the single-round prover accepts with probability \(1/2+\epsilon\) for inverse-polynomial \(\epsilon\), then with probability at least \(2\epsilon\) over its fixed tape and first-message state both challenges can succeed, and testing both challenges by rewinding extracts in expected polynomial time. This applies to the ordinary version with \(G\) as well.

<a id="entry-128"></a>

### 128. Perfect witness indistinguishability survives parallel repetition

In a parallel batch of signed orbit proofs, conditioned on every commitment and on any challenge vector chosen as a function of those commitments, each response is uniform on its transporter fiber and independent of the particular initially held signed witnesses. Indeed the prover samples independent uniform group blinding elements, and converting from a witness for one source to a response for the other source is a bijection of fibers. Thus the joint view of a malicious verifier is exactly witness-independent, while any two accepting challenge vectors differing in one component extract a witness in that component. This gives witness indistinguishability in the expected-time exact sampling convention.

<a id="entry-129"></a>

### 129. Both nonisomorphism languages have concurrent statistical zero knowledge

Signed and ordinary nonisomorphism have unconditional concurrent statistical zero-knowledge proofs in the Micciancio–Ong–Sahai–Vadhan model. Use the bounded-coin orbit samplers from [Entry 126](#entry-126), including distinct rejection tags for the two circuits. On nonisomorphic inputs their supports are disjoint, so their distance is exactly one. On isomorphic inputs their conditional laws on good draws are equal and their statistical distance is at most the common rejection probability, which can be made less than \(1/2\). This maps to their restricted Statistical Difference promise problem, with nonisomorphism mapping to the YES/far side. The concurrent proof transfers along this deterministic reduction. Equivalently the orbit commitment is binding on YES for nonisomorphism and hiding on NO, the orientation required for their theorem. [Micciancio, Ong, Sahai and Vadhan, Theorem 10 and Corollary 11](https://cseweb.ucsd.edu/~daniele/papers/ConcZK.pdf).

<a id="entry-130"></a>

### 130. Polynomial Boolean assertions remain in statistical zero knowledge

A language computed by a polynomial-time generated Boolean formula of polynomial size on queries to \(A\) and \(B\) lies in SZK. Negations are allowed. Use the Sahai–Vadhan formula closure theorem after replacing each atomic predicate by its deterministic reduction to the complete Statistical Difference problem. The result also covers fan-in-two logarithmic-depth Boolean circuits, by polynomial unfolding. This uses an SZK target and is independent of the ordinary-TI decoder results. [Sahai and Vadhan, Theorem 4.9 and its formula extension](https://web.cs.ucla.edu/~sahai/work/web/2003%20Publications/J.ACM2003.pdf).

<a id="entry-131"></a>

### 131. NP-hardness by adaptive randomized reductions would collapse PH

For each of \(L=A,B\), \(\mathrm{BPP}^{L}\subseteq\mathrm{AM}\cap\mathrm{coAM}\). Amplify public-coin proofs for \(L\) and its complement to error beneath \(2^{-p(n)-6}\) on each individual query of length at most \(p(n)\). The union bound makes both tapes simultaneously correct for every such query. Merlin supplies a purported accepting adaptive computation and the matching publicly verifiable answer proofs. On simultaneously good tapes it can follow only the true oracle computation. The same construction handles the complement. Thus an adaptive BPP-Turing reduction from SAT to \(L\) would give \(\mathrm{coNP}\subseteq\mathrm{AM}\), so \(\mathrm{PH}=\Sigma_2^P\) by Boppana–Håstad–Zachos. Under strictness and noncollapse of PH, signed TI is a concrete NP-intermediate problem for deterministic many-one reductions. [Boppana, Håstad and Zachos](https://doi.org/10.1016/0020-0190(87)90232-8).

<a id="entry-132"></a>

### 132. Strong AM derandomization yields an NP-intersection-coNP separation

If \(\mathrm{AM}=\mathrm{NP}\), the known \(\mathrm{AM}\cap\mathrm{coAM}\) upper bound puts \(A\) in \(\mathrm{NP}\cap\mathrm{coNP}\). Therefore \(\neg H\) in that world implies \(\mathrm P\subsetneq\mathrm{NP}\cap\mathrm{coNP}\), separately from the SZK and counting intersections. A sufficient premise for AM derandomization is an \(\mathrm E\) language whose SAT-oracle circuit complexity is exponentially large at all sufficiently large lengths. A uniform truth-table generator over logarithmic seeds allows Merlin to give witnesses for a majority of Arthur's possible pseudorandom tapes, and membership is verified deterministically in NP. Neither a worst-case signed separator nor ordinary TI hardness gives the derandomization premise. [Klivans and van Melkebeek](https://doi.org/10.1137/S0097539700389652).

<a id="entry-133"></a>

### 133. Both answers have polynomial advice certificates without derandomization

Both \(A\) and \(B\) lie in \(\mathrm{NP/poly}\cap\mathrm{coNP/poly}\). To see the nontrivial complementary certificate, amplify the \(\mathrm{AM}\) protocol for the complement to error \(<2^{-n-1}\) on every \(n\)-bit input, and fix one Arthur tape that works simultaneously on all these inputs. Give that tape as advice. A nondeterministic verifier guesses Merlin's response. In the stronger nonuniform strictness branch, \(A\notin\mathrm{P/poly}\) therefore separates \(\mathrm{P/poly}\) from this advice-bearing intersection. This argument does not give a uniform NP witness for nonisomorphism.

<a id="entry-134"></a>

### 134. Randomized witness isolation gives a Unique-SAT benchmark

Write the signed transporter verifier as a polynomial-size Boolean circuit with a canonical bit encoding of the matrix tuple. Apply the Valiant–Vazirani hash to that bit tuple, and enforce the circuit gates in a parsimonious CNF using uniquely determined auxiliary gate values. NO cases remain empty on every tape, and YES cases have a unique satisfying assignment with inverse-polynomial probability. Thus a deterministic solver for the Unique-SAT promise would give \(A\in\mathrm{RP}\) by accepting any uniquely satisfiable query and amplifying. Every generated query on an original NO input stays on the unsatisfiable side of the promise. Under \(\mathrm P=\mathrm{RP}\) this would rule out strictness. Mod-two counting of the hashed formula also suffices, since its parity is odd on the isolated branch and zero on all original NO inputs. This does not require parity of the raw transporter count. [Valiant and Vazirani](https://ics.uci.edu/~vazirani/ValVaz.pdf).

<a id="entry-135"></a>

### 135. Rigidity yields unambiguous verification on its explicit promise

Fix a mode format, a group action, and its computable kernel \(Z\). On the promise that the source stabilizer is exactly \(Z\), a transporter witness can be made unambiguous. Verify a candidate in the usual way and keep only a canonical representative of its right \(Z\)-coset. For ordinary TI over \(\mathbf F_3\), use the scalar kernel with product of the three scalars \(+1\), and for signed TI intersect this kernel with \(K\). The kernel is known and of size at most four, so canonical choice is polynomial. Under the stated promise NO has no paths and YES has exactly one. This is a PromiseUP-type guarantee and makes no claim about the set of rigid inputs being recognizable in P.

<a id="entry-136"></a>

### 136. MCSP yields one-sided decision and explicit transporter search

For either \(L=A,B\), an MCSP oracle gives a randomized verifier-backed transporter finder with inverse-polynomial success, and hence \(L\in\mathrm{RP}^{\mathrm{MCSP}}\). Sample a bounded-coin image of \(T_0\), use the Allender–Das MCSP-assisted average inverter for the sampler circuit \(r\mapsto g(r)T_1\), and verify the returned seed. On YES the two sample laws are multiplicatively close to the same uniform orbit, so the average inversion guarantee on the target distribution transfers to the source samples. The kept group elements \(g_0,g_1\) explicitly give \(g_1^{-1}g_0\). On NO their orbits have disjoint support, so the verification never succeeds. This obtains witnesses and one-sided error, beyond a decision upper bound for general SZK. [Allender and Das, Theorem 1 and the discussion after Theorem 4](https://www.cs.rutgers.edu/~allender/papers/szk.mcsp.pdf).

<a id="entry-137"></a>

### 137. Adaptive MKTP supplies zero-error tensor decisions

Both \(A\) and \(B\) are in \(\mathrm{ZPP}^{\mathrm{MKTP}}\), in addition to the separate bounded-error nonadaptive result in the earlier atlas. In Theorem 5.7 of Allender–Grochow–van Melkebeek–Moore–Morgan the required group samplers, group operations, dimensions as complete presentation invariants, and exact group orders are polynomial-time available here. The order is a product of \(\prod_{j<d}(3^d-3^j)\) and its division by two for SL. If a faithful action is required, add a tagged disjoint regular orbit of the same group without changing comparisons of the original tensors. Thus if \(\neg H\) and \(\mathrm P=\mathrm{ZPP}\), MKTP cannot lie in P. This is a zero-error adaptive algorithm, with no claim that the known truth-table reduction becomes zero error. [Allender, Grochow, van Melkebeek, Moore and Morgan, Theorem 5.7](https://pages.cs.wisc.edu/~dieter/Papers/gi-mktp-sicomp.pdf).

<a id="entry-138"></a>

### 138. Resource-class equivalences when the target decision is easy

If \(B\in\mathrm P\), then \(H_R\) is equivalent to \(A\in\mathrm{BPP}\), and a one-sided randomized many-one reduction is equivalent to \(A\in\mathrm{RP}\) in the same direction of error. In the forward direction simulate the target decision. In the reverse direction, let the randomized decision choose a fixed ordinary YES or NO output. When \(B\in\mathrm{P/poly}\), deterministic polynomial-size many-one reducibility is equivalent to \(A\in\mathrm{P/poly}\), by circuit composition and the same fixed-output construction. These equivalences identify additional premises, unlike the unconditional implications from nonuniform strictness.

<a id="entry-139"></a>

### 139. External oracles that make ordinary TI easy separate the Cook question exactly

There exists an external oracle \(\Omega\) with \(B\in\mathrm P^\Omega\) and \(A\not\le_m^{\mathrm P^\Omega}B\) exactly when \(A\notin\mathrm P^B\). The forward implication holds because otherwise the deterministic Cook computation with oracle \(B\) could run inside \(\mathrm P^\Omega\), and constant ordinary outputs would erase strictness. Conversely take \(\Omega=B\). Thus a deterministic many-one gap with Cook equivalence cannot survive in any external world where the fixed ordinary language is already easy. The statement holds with the two tensor languages fixed as sets, independent of \(\Omega\).

<a id="entry-140"></a>

### 140. Random external oracles characterize randomized Cook reducibility

For a fixed target \(B\), \(A\in\mathrm{BPP}^{B}\) is equivalent to \(A\in\mathrm P^{B\oplus R}\) for almost every fair independent \(R\), and equivalently for a positive measure of such \(R\). Amplify the decision error exponentially, replace coins by independent addressed bits of \(R\), and hardcode finitely many exceptions after a sum over all input strings. In the other direction take a clocked oracle algorithm correct on positive measure of \(R\)'s, condition on a finite cylinder of density \(>2/3\), and generate its previously unqueried \(R\)-bits lazily while making actual \(B\)-queries. No monotone output compiler is needed because the machine computes a decision bit. This extends the earlier random-oracle criterion from many-one to adaptive Cook access. [Bennett and Gill, corollary to Theorem 5](https://www.cs.cornell.edu/courses/cs682/2006sp/Handouts/BennettGill.pdf).

<a id="entry-141"></a>

### 141. Every Martin–Löf random oracle has the predicted many-one behavior

The earlier measure-one dichotomy strengthens to each Martin–Löf random external oracle \(R\) individually. If \(H_R\) holds, exponential amplification and ordinary majority compilation give finite-bit bad events at length \(n\) of probability at most \(2^{-n-4}\). These events are uniformly computably clopen because \(A,B\) are decidable and the map is clocked. Their tails give an effective Martin–Löf test, so only finitely many errors occur for each Martin–Löf random \(R\). If \(H_R\) fails, the correctness set of each fixed polynomial-clocked transducer is an effectively closed null class by the previous positive-measure argument. Its decreasing clopen approximations have computable measures, so searching for the first prefix of measure below \(2^{-j}\) gives a Martin–Löf test covering that class. Each such random oracle therefore preserves the gap. The exception tables and clocked transducers may depend on \(R\).

<a id="entry-142"></a>

### 142. Random-oracle criterion for verifiable witness search

For either tensor action, a worst-case polynomial-time randomized witness finder with inverse-polynomial success on every YES input exists if and only if deterministic polynomial-time witness finding relative to a fair random external oracle is possible for almost every oracle. Positive measure again suffices. Amplify using witness verification until error is summable over all inputs. Hardcode the finitely many missed YES witnesses for each good oracle. The same density-cylinder argument applied to the event that a fixed transducer returns a valid witness for every YES input gives a bounded-error randomized finder, without checking the membership of NO inputs online. A version with a fixed decision oracle \(B\) throughout the two computations is proved identically. This characterizes functional verified search and does not turn it into a language many-one map.

<a id="entry-143"></a>

### 143. A recursive oracle makes equality coexist with a BPP separation

There is a recursive \(\Omega\) with \(A,B\in\mathrm P^\Omega\) but \(\mathrm{UP}^\Omega\cap\mathrm{coUP}^\Omega\cap\mathrm{SZK}^\Omega\nsubseteq\mathrm{BPP}^\Omega\). Use \(\Omega=\mathrm{SAT}\oplus C\) and the earlier equal-versus-disjoint injection construction, with a unique hidden marker of the branch bit. At a fresh parameter \(n\), choose a uniform random completion independently for each branch, including a uniformly placed allowed marker. For a \(q\)-query algorithm the transcript distributions differ in total variation by \(O(q^2/2^n+q/2^n)\). For the injection part, answer a new argument by a uniformly fresh label in both worlds until an equal-image cross-collision would occur; its conditional probability is \(O(q/(2^n-q))\) per probe. Whole injection values can be supplied to this coupling even if only one bit is requested. Marker queries hit a fresh hidden marked word with total probability \(O(q/(2^{n-1}-q))\). Repeated queries receive the same answers. Conditioning on the machine's coins shows that coupled acceptance probabilities differ by less than \(1/3\) for sufficiently large \(n\). Thus in at least one branch some finite completion makes the decision machine err with probability \(>1/3\). Exhaustively find it, then freeze every parameter up through the clocked query bound. Machines are enumerated with polynomial clocks and finite random tapes, and the SAT part is decidable, so the oracle is recursive. The proof languages still have unique markers for both outcomes, and the oracle-circuit proof of SZK is unaffected.

<a id="entry-144"></a>

### 144. Approximate transporter samples still yield controlled conditional samples

Suppose a generator outputs a distribution within total variation \(\delta\) of the uniform ordinary transporter on a known ordinary YES input. Filter invalid outputs and all determinant tuples except a feasible requested \(d\). The probability of acceptance is at least \(1/8-\delta\). The conditional output law has total variation at most \(2\delta/(1/8-\delta)\) from the uniform \(d\)-fiber. To see this, write each conditional expectation against the accepted event \(E\) and bound separately the numerator difference and the change of normalization, each by at most \(\delta\). For \(\delta<1/16\) the expected number of draws is at most 16. Rejection on an infeasible sign never misreports a verified witness. The statement assumes a probabilistically accurate whole-transporter sampler, which is stronger than an ordinary decision oracle but weaker than an exact sampler.

<a id="entry-145"></a>

### 145. Known determinant-profile cardinality gives a zero-error stopping rule

On an ordinary YES input, suppose the number \(m\) of attainable determinant tuples is supplied correctly. Given an exact ordinary witness solver, blind and sample until \(m\) distinct determinant tuples have been observed. At that stopping time the list is complete and resolves every sign test. The expected number of successful ordinary witness calls is \(m(1+1/2+\cdots+1/m)\le 8(1+1/2+\cdots+1/8)\), by uniform occupancy. An ordinary decision oracle can first remove ordinary NO inputs. This is a Las Vegas promise algorithm with an explicit stopping criterion using the supplied \(m\).

<a id="entry-146"></a>

### 146. Conditional equivalence of actual representative canonization

Under \(H\), ordinary and signed representative canonization have polynomial-time functional Turing reductions to one another. Given an ordinary canonical representative \(C(T)\), list its eight reflections and use signed decision, implemented via \(H\) and ordinary comparison, to pick the first reflection in the signed orbit of \(T\). This output lies in that orbit and is invariant on it. Conversely invoke signed canonization on each of the eight reflections of \(T\). The lexicographically smallest returned signed canonical representative is an ordinary canonical representative, without assuming \(H\) in that direction. The construction uses representatives that lie in actual orbits, and does not require computing the lexicographically least element of the entire orbit.

<a id="entry-147"></a>

### 147. Full-coset search-to-decision claims become equivalent under H

The known unconditional functional transfers between ordinary and signed complete coset search strengthen under \(H\) to equivalence of the two specific search-to-decision statements. If ordinary full-coset search uses ordinary decision, form a signed coset from its witness and stabilizer generators by the determinant image and a Schreier kernel, then replace every ordinary decision query by its null-padded signed test. Conversely extract the ordinary coset from the at most eight signed reflected coset queries, and replace any signed decision used by the presumed search-to-decision solver by \(H\). This compares two algorithmic assertions and does not assume either complete coset search reduces to its own decision unconditionally.

<a id="entry-148"></a>

### 148. A fixed-field subexponential bound applies directly to signed coset search

For maximum mode dimension \(n\), signed decision and signed full-coset search have running time \(3^{\widetilde O(n^{3/2})}\). Use the published matrix-space left-right equivalence algorithm returning stabilizer generators and a transporter, with the concise tensor's independent slices as the matrix space. A space equivalence uniquely recovers the third-mode map. On raw inputs first test equality of support ranks. Extend support transporters to the entire mode spaces with arbitrary complement invertibles and shears. Together these give full ordinary cosets within the same time. The finite-index determinant kernel and the sign representative selection add polynomial overhead. The bound therefore holds independently of the availability of a polynomial-size \(H\) map, which need not preserve the exponent in \(n\). [Ivanyos, Mendoza, Qiao, Sun and Zhang, Sections IV-D and IV-E](https://chuanqizhang.com/assets/pdf/pdf/focs24.pdf).

<a id="entry-149"></a>

### 149. Square-root-logarithmic support rank gives deterministic polynomial time

Let \(r_i\) be the dimensions of the three contraction supports. Fixed-field signed decision and witness search take \(3^{O(r_1^2+r_2^2+r_3^2)}\operatorname{poly}(L)\) time for dense input bit length \(L\). Compute supports and enumerate the possible isomorphisms between corresponding supports in known bases. On any proper support a restriction extends to the full mode with a prescribed determinant, by adjusting a single complement direction. On full support explicitly test its determinant in the original coordinates. The tensor lies in the product of its supports and hence only the enumerated restrictions affect equality. In particular rank-\(r\) tensors admit the bound \(3^{O(r^2)}\operatorname{poly}(L)\), since no contraction support exceeds the tensor rank. In particular this is polynomial time when every support dimension is O(sqrt(log L)). The algorithm need not decide membership in the bounded-rank promise.

<a id="entry-150"></a>

### 150. One square-root-logarithmic mode gives a randomized polynomial-time algorithm

If one raw mode dimension is \(d\), signed decision and witness search take \(3^{O(d^2)}\operatorname{poly}(L)\) randomized time with one-sided verification error. Enumerate the determinant-one actions on that mode. For each choice the remaining task is equivalence of an ordered matrix tuple by left and right invertible maps. The latter has a polynomial-time ordinary witness algorithm via module isomorphism for the two-vertex quiver with one arrow per slice. Blind one tuple by a uniform left-right action, obtain an ordinary tuple witness, and unblind. Any feasible pair of determinant signs has conditional probability at least \(1/4\), since the signed subgroup has index at most four. A constant number of trials per choice suffices for decision error at most \(1/3\), since any particular feasible choice yields a verified success with probability at least \(1/4\) per exact trial and false claims are always rejected. A bounded rejection sampler reduces the trial success probability by a constant factor only. Thus \(d=O(\sqrt{\log L})\) is an RP regime, even if the other two supports have high rank. [Brooksbank and Luks, testing module isomorphism](https://citeseerx.ist.psu.edu/document?doi=c2002ca40d487b7c4f73b14bee95eb06736531ba&repid=rep1&type=pdf).

<a id="entry-151"></a>

### 151. Large-field sign constraints can use logarithmically many witness samples with number-theoretic oracles

Over an explicitly presented odd finite field \(\mathbf F_q\), a polynomial-time ordinary witness oracle plus integer factoring and finite-field discrete logarithms gives a randomized polynomial-time restricted search algorithm for all three prescribed determinant values. Query an ordinary witness, then draw independent uniform source stabilizer elements by blinding. Apply \(\chi\) to get elements in \((\mathbf F_q^\times)^3\). \(O(\log q+\log(1/\epsilon))\) images generate the whole image with probability \(1-\epsilon\), because a new uniform image lies outside any proper subgroup with probability at least \(1/2\), and a successful step doubles size. In a discrete-log coordinate system the target sign correction is a linear congruence in three coordinates modulo \(q-1\). Integer Smith or Hermite normal form finds exponents if it is attainable. Multiply the stored stabilizer elements to these exponents and verify. A generator of \(\mathbf F_q^\times\) can be sampled and tested using the factorization of \(q-1\). If \(q-1\) has \(k\) distinct prime divisors, the generator fraction is at least \(1/(k+1)\) by bounding the \(j\)-th smallest divisor below by \(j+1\). This avoids a rejection factor growing like \(q^3\). With Shor's algorithms it also yields a quantum polynomial-time transfer if the ordinary witness oracle is efficient there. [Shor, factoring and discrete logarithms](https://arxiv.org/abs/quant-ph/9508027).

<a id="entry-152"></a>

### 152. A single large-field determinant equation needs orders, without discrete logs

For a prescribed single multiplicative determinant character over \(\mathbf F_q\), the decision version of the preceding transfer needs only factorization of \(q-1\) and an ordinary witness solver. Take the orders of the sampled stabilizer character values by prime-division tests and form their least common multiple \(M\). The resulting subgroup of \(\mathbf F_q^\times\) is the unique subgroup of order \(M\). The required correction \(c\) lies there exactly when \(c^M=1\). A partial set of samples can only cause a false negative. Multiplicative correlations across several characters are not covered by separate order tests. This gives a distinct factorization-only oracle bound for the single-character decision model.

<a id="entry-153"></a>

### 153. Uniform stabilizer samples learn all determinant-character constraints

Given a feasible ordinary transporter and a uniform sampler of ordinary stabilizer witnesses, conditions of the form \(\ell_i(\chi(g))=\sigma_i\) over \(\mathbf F_3\) can be learned with at most three independent successful span increases. Suppose the correct stabilizer image has dimension \(r\), and draw \(s\) independent uniform stabilizer signs. The probability their span is proper inside the image is at most \((2^r-1)2^{-s}\), since failure means some nonzero linear functional vanishes on all draws. Solve the requested affine equations on the learned subspace, then combine stored generators and verify. The conclusion applies equally when only a specified family of determinant characters is queried, by projecting first. The sample bound controls one-sided errors in learning the projected character image.

<a id="entry-154"></a>

### 154. Compact exponent-three orientation has a distinct Cayley-table time bound

For special class-two exponent-three groups presented by full Cayley tables of order \(N\), even isomorphism can be tested in \(N^{\widetilde O(\sqrt{\log N})}\) time. Extract the alternating bimap on the elementary abelian central and quotient layers, each of dimension at most \(\log_3 N\). Linear-length AMSI-to-TI reductions with coset recovery produce an ordinary matrix stabilizer and a transporter within \(3^{\widetilde O((\log N)^{3/2})}\), using the underlying tensor coset algorithm. In compatible additive coordinates the parity of an isomorphism on the table is the product of its two determinant signs. In an additive ternary frame, transvections are even permutations and changing the sign of one coordinate is odd. A change from the input's table order gives an explicitly computable parity calibration. Then test the finite sign image of the stabilizer. This concerns actual table input size and does not furnish a polynomial algorithm for compact exponent-three input. [Grochow and Qiao, Theorem 1.10 and Remark 1.12](https://arxiv.org/html/2306.16317v2), [Ivanyos, Mendoza, Qiao, Sun and Zhang](https://chuanqizhang.com/assets/pdf/pdf/focs24.pdf).

<a id="entry-155"></a>

### 155. Coherent uniform orbit representatives are constructible with explicit postselection cost

For either \(G\) or \(K\), an indexed group of order \(M\) and a tensor \(T\) give a uniform pure orbit state by a polynomial-time postselected quantum circuit. Prepare \(r=\lceil\log_2 M\rceil\) fair coin qubits coherently and reversibly compute the legal-index flag and \(g_iT\) for each index \(i<M\), uncomputing all scratch registers. Postselect validity and then project the original index register onto the uniform Hadamard state. The remaining vector is proportional to \(\sum_{i=0}^{M-1}|g_iT\rangle\), so every orbit point has the same positive amplitude \(|\operatorname{Stab}(T)|\) before normalization. The combined success probability of both postselections is \(M^2/(2^{2r}|\mathcal O(T)|)\), by squaring this unnormalized output with its initial coefficient \(2^{-r}\). A swap test on two such normalized states accepts with probability one for equal orbits and \(1/2\) for disjoint orbits. This is an exact coherent representation, and its postselection cost can be exponential on large orbits.

<a id="entry-156"></a>

### 156. Existence of an odd stabilizer is an exact collision problem

Fix a public \(T\), the ordinary orbit map \(g\mapsto gT\), and a prescribed determinant ratio \(d\ne1\). Finding a collision \(gT=hT\) with \(\chi(g)\chi(h)^{-1}=d\) is deterministically equivalent to finding an element of \(G_T\) of sign \(d\). Return \(h^{-1}g\) from a collision, or compare a valid stabilizer element with the identity for the reverse direction. The determinant tuple condition excludes the ever-present scalar-kernel collisions when its tuples do not match \(d\). This is a graded collision formulation of an actual search task, with no cryptographic hardness assumption.

<a id="entry-157"></a>

### 157. Ordinary-YES promise prediction characterizes signed decision with ordinary oracle access

The following two assertions are equivalent: \(A\in\mathrm{BPP}^B\), and there is a uniform polynomial-time ordinary-oracle predictor that, for every ordinary-isomorphic but signed-nonisomorphic pair \(T_0,T_1\), predicts a fair hidden bit \(b\) from a uniform signed orbit draw \(kT_b\) with probability at least \(2/3\). For the forward direction compare the draw to \(T_0\) under signed TI. For the converse first use \(B\) to reject ordinary NO pairs. On the rest, estimate predictor accuracy from challenges with known \(b,k\). On a signed YES the draw is independent of \(b\) and accuracy is exactly \(1/2\). On a signed NO the guarantee supplies a constant gap. Exact uniform group sampling may be truncated with a separate rejection tag of small probability. This is a worst-case orbit-classification equivalence on the promise, distinct from distributional cryptographic hardness.

<a id="entry-158"></a>

### 158. Adaptive binary oracle access can be replaced by nonadaptive verification for bounded query witness search with randomized outputs

Suppose a randomized uniform algorithm outputs a verifiable signed transporter on each YES input with inverse-polynomial probability using at most \(O(\log L)\) adaptive binary answers from any fixed decision oracle. Then \(A\in\mathrm{RP}\) without that oracle. First sample its random tape. Enumerate all polynomially many possible answer transcripts for that tape and verify every resulting witness. The truthful transcript is included, while no invalid output survives. Amplifying on YES yields RP. Thus if \(\neg H\) and \(\mathrm P=\mathrm{RP}\), such a bounded-query randomized search algorithm is impossible even with SAT or exact-zero counting answers. This strengthens the earlier deterministic witness-transcript statement in a model where the outer computation is randomized.
