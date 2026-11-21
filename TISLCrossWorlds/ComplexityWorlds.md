# Fixed-field tensor isomorphism across complexity worlds

[Atlas complexity chapter](prior/earlier/baseline/expansion/Complexity.md) · [Ordinary aggregation](prior/earlier/baseline/baseline/LinearSwitchCompiler.md)

Write \(A=\mathrm{TI}_{\mathrm{SL}}(\mathbf F_3)\) and \(B=\mathrm{TI}(\mathbf F_3)\) for the two dense 3-tensor decision languages, with independently acting mode groups. Write \(H\) for \(A\le_m^{\mathrm P}B\). Zero-padding one line per mode gives the reverse reduction. Unless explicitly relativized, all complexity classes and reductions below are uniform and unrelativized. Oracle examples use the same two ordinary languages \(A,B\); the machines that compute reductions or recognize other languages obtain the external oracle. These are informal proofs.

## Algebraic proof systems

### W01. A small, constant-degree exact determinant-one presentation

For an \(N\)-dimensional mode, write \(e_{ij}(t)=I+tE_{ij}\) for \(i\ne j\). Fix a sequence of ordered pairs and variables \(t_s\), and impose
\[
  M_0=I,\qquad M_{s+1}=M_s e_{i_sj_s}(t_s).
\]
The final matrices in the three modes obey the usual cubic tensor action. The gate equations have degree at most two. Inverse witnesses can be included by adding the left and right inverse equations of degree two. Over \(\mathbf F_3\) one can include \(z^3-z=0\) for every variable.

A universal schedule of length \(O(N^4)\) suffices over every field \(F\). Gaussian elimination by row-addition shears needs \(O(N^2)\) shears plus a determinant-one diagonal matrix. In a nonzero pivot column a missing pivot can be repaired by adding a row with nonzero entry, so row swaps are unnecessary. The diagonal matrix is the product, over \(i<N\), of two-coordinate matrices \(\operatorname{diag}(t,t^{-1})\). Each is a product of six shears, since
\[
 \begin{pmatrix}1&t\\0&1\end{pmatrix}
 \begin{pmatrix}1&0\\-t^{-1}&1\end{pmatrix}
 \begin{pmatrix}1&t\\0&1\end{pmatrix}
 \begin{pmatrix}0&-1\\1&0\end{pmatrix}
 =
 \begin{pmatrix}t&0\\0&t^{-1}\end{pmatrix},
\]
and the last factor equals the first three with \(t=-1\). The \(N=1\) determinant-one group is trivial. Repeat the list of all ordered pairs for \(O(N^2)\) cycles, using at most one nontrivial shear in each cycle. A fixed \(O(N^2)\)-length prefix may be prepended to this schedule, since every prefix coefficient can be zero. The resulting degree-two and degree-three system has polynomial size and is satisfiable exactly when the signed instance is YES.

### W02. Low-degree ordinary-to-signed substitution through determinant-one shears

An ordinary mode of dimension \(n\) uses inverse witness matrices \(X,Y\) satisfying \(XY=YX=I\). Pad both tensors with \(n\) zero coordinates in each mode. In padded dimension \(2n\) choose the prefix of W01 so that the following four block factors can be assigned to it:
\[
 \widehat X =
 \begin{pmatrix}I&X\\0&I\end{pmatrix}
 \begin{pmatrix}I&0\\-Y&I\end{pmatrix}
 \begin{pmatrix}I&X\\0&I\end{pmatrix}
 \begin{pmatrix}0&-I\\I&0\end{pmatrix}
 =
 \begin{pmatrix}2X-XYX&XY-I\\I-YX&Y\end{pmatrix}.
\]
The first three block factors each decompose into \(n^2\) commuting scalar shears, and the constant fourth factor decomposes into three scalar shears per coordinate pair. Substitute the appropriate entries of \(X,Y\) and constants as coefficients, with zero coefficients in the universal suffix. Each partial prefix product has entries of ordinary-variable degree at most three. If padded inverse variables are included, substitute the reversed word with negated shear coefficients, also of degree at most three.

All substituted gate and inverse equations vanish identically. The first block column differs from \(\binom X0\) by entries of \(\binom{-(XY-I)X}{I-YX}\). The padded tensor action only uses the first block column in each mode. A three-factor telescoping identity therefore derives every substituted action equation from the ordinary action and inverse equations in degree at most nine. Over \(\mathbf F_3\) a substituted field equation \(p^3-p\) is derived in degree at most nine: Frobenius is additive and, for any monomial \(z_1\cdots z_r\), its cube minus itself is a telescoping sum with factors \(z_i^3-z_i\). Zero-padding reflects ordinary isomorphism because it preserves the intrinsic mode supports and an isomorphism of the supports extends to an invertible map of each original ambient mode.

### W03. Linear Polynomial Calculus degree over \(\mathbf F_3\), with every field axiom

The W01 signed presentation has NO instances of dimension \(N\) in each padded mode with Polynomial Calculus refutation degree \(\Omega(N)\). In particular, the lower bound survives explicit field axioms on *all* tableau and inverse variables.

Galesi, Grochow, Pitassi and She, §5, start with Boolean graph-isomorphism PC lower bounds and use degree-two variable substitutions in each of the two reductions in Propositions 5.4 and 5.5. The image of each ordinary tensor equation is derivable from the Boolean graph equations at bounded degree. Append the substitution of W02. The composed variable substitutions have degree at most twelve and the substituted signed relation axioms still have uniformly bounded-degree derivations. Every signed field axiom also does: after composition it is \(p^3-p\), which is derived from \(z^3-z=(z+1)(z^2-z)\) for the original Boolean variables, using Frobenius and the same telescoping identity. This uses Boolean axioms of the graph formulation explicitly.

For a degree-\(d\) PC derivation, substitute every line and simulate multiplication by a variable by multiplying by each monomial in its substitution and summing. If the substitution degree is \(k\), the resulting intermediate degrees are at most \(kd\), aside from the original bounded cost of axiom derivations. Thus \(d=\Omega(N)\) follows from the graph lower bound and the linear tensor dimension in their Theorem 5.2. Rectangular source instances can be padded to balanced instances before W02. Extend each ordinary witness pair by identity blocks for that padding in the same constant-degree substitution. This proves an unconditional bound for this presentation in either \(H\) branch. It is a degree bound for an explicit certificate system. [Galesi–Grochow–Pitassi–She, CCC 2023, §5](https://doi.org/10.4230/LIPIcs.CCC.2023.4)

### W04. Constant-factor comparison of minimum degree on concise padded pairs

Call a tensor concise if every mode flattening has full row rank in its declared dimensions. For concise ordinary inputs \(T,T'\), use the signed W01 presentation with padded inverse witnesses. Every degree-\(d\) ordinary refutation induces a signed refutation of degree at most \(\max(d,5)\). The converse from W02 costs only a constant factor and additive constant. This comparison is for the corresponding padded pairs.

To obtain the reverse interpretation, write the final signed matrices and their declared inverses in \(2\times2\) blocks of size \(n\). For mode \(i\), multiply the padded action identity by the two inverse matrices of the other modes. Then restrict to a bottom coordinate in mode \(i\) and to top coordinates in the other modes. The right tensor side is zero by its support in mode \(i\), and the left side is the bottom-left block of the mode matrix multiplied by the mode flattening of \(T\). The two inverse product equations give the cancellation in degree at most five. A constant right inverse of the flattening gives the vanishing of each bottom-left entry. To derive the vanishing of the bottom-left block of the mode-\(i\) inverse, multiply the forward action by just that inverse in mode \(i\). Its product equation cancels the mode-\(i\) forward matrix in degree at most four. Restrict to a bottom coordinate of the source in mode \(i\). The side obtained from \(T\) vanishes because \(T\) is supported in the top coordinates of that mode. The other side consists of the bottom-left inverse block contracted against the flattening of \(T'\), whose conciseness forces this block to vanish. The top-left blocks of the two product equations now give the corresponding inverse laws for the top-left matrices. Their tensor action is the top-coordinate portion of the padded action equation. Substitute those top-left variables in the ordinary proof.

### W05. Static Nullstellensatz and SOS certificates inherit the transfer

The signed field-axiom systems of W03 require Nullstellensatz refutation degree \(\Omega(N)\). A Nullstellensatz identity of degree \(d\) can be expanded as a PC derivation in degree \(d\), since each monomial multiplier is built by variable multiplications before taking the final linear combination.

For real signed tensor isomorphism over \(\mathbf R\) with the same W01 presentation and without finite-field axioms, there are also \(\Omega(N)\) Sum-of-Squares degree lower bounds. Start with the \(\mathbf R\) lower bound and degree-preserving reductions in Galesi–Grochow–Pitassi–She §5. Substitute W02 in a hypothetical SOS refutation. Substitution carries each square to a square and the substituted axioms are bounded-degree ideal combinations by explicit telescoping. Therefore the degree cost is bounded by a constant factor plus a constant. This real statement concerns a different decision language from fixed-field \(H\). [Galesi–Grochow–Pitassi–She, Theorem 5.2](https://doi.org/10.4230/LIPIcs.CCC.2023.4)

### W06. Circuit-represented algebraic refutations simulate across padding

For the W02 substitution, any algebraic Ideal Proof System refutation of the signed system can be transformed into an IPS refutation of the ordinary one with polynomial circuit-size overhead, including over \(\mathbf F_3\) with field axioms. This does not assert a Polynomial Calculus monomial-size lower bound. Let the ordinary equations be \(f_j(x)=0\) and the signed equations \(g_i(u)=0\). The substitution \(\phi\) satisfies
\[
 g_i(\phi(x))=\sum_j h_{ij}(x) f_j(x)
\]
with uniformly constructible polynomial-size circuits for each \(h_{ij}\), by the telescoping identities and bounded-degree expansions of W02. If \(C(u,v)\) witnesses \(C(u,0)=0\) and \(C(u,g(u))=1\), use
\[
 C\left(\phi(x),\left(\sum_j h_{ij}(x)y_j\right)_i\right).
\]
The two polynomial identities follow immediately. The converse composition works for the concise pairs of W04 with its bounded-degree ideal combinations as well. [Grochow–Pitassi, Ideal Proof System](https://arxiv.org/abs/1404.3820)

### W07. Low-degree refutation search gives a tractable subproblem in either branch

Over fixed \(\mathbf F_3\), deciding whether a given W01 system has a degree-\(d\) PC refutation is deterministic in time polynomial in the input size and \(\binom{v+d}{d}\), where \(v\) is the total number of variables. Work in the vector space of polynomials of degree at most \(d\), start with the eligible axioms, and close the current row space under linear combination and multiplication by each variable on its intersection with the subspace of degrees at most \(d-1\). Each strict step increases dimension and the necessary intersections and spans use finite-field linear algebra. A degree-\(d\) derivation exists exactly when the closure contains 1. Hence constant \(d\) gives polynomial time and \(d=O(\log v)\) gives quasipolynomial time, even if \(H\) is false. W03 supplies NO cases on which this particular refutation search cannot succeed within logarithmic degree.

## Derandomization and uniform reductions

### W08. Polynomial spectral norm of the seed predicates suffices for equality

Suppose there is a bounded-error randomized many-one reduction \(R(x;s)\) from \(A\) to \(B\). Pad its seed to a fixed polynomial length \(r=r(|x|)\). For each input define the real Boolean function \(f_x(s)=1_B(R(x;s))\). If for some fixed \(c\) every \(f_x\) has Fourier spectral norm \(\sum_U|\widehat f_x(U)|\le |x|^c\), then \(H\) holds. The bound may hold without an algorithm producing the Fourier coefficients.

An explicit small-bias distribution suffices. Choose \(a,b\) uniformly in \(K=\mathbf F_{2^m}\) and use the bits \(s_i=\operatorname{Tr}_{K/\mathbf F_2}(ab^i)\) for \(0\le i<r\). Each nontrivial parity has bias at most \((r-1)/2^m\), since its expected sign is the zero probability of a nonzero polynomial of degree at most \(r-1\). Take \(2^m\ge 12r\max(1,|x|^c)\). Construct \(K\) by exhaustive search for irreducible degree-\(m\) polynomials over \(\mathbf F_2\), with deterministic polynomial-time irreducibility tests or exhaustively checking all possible factors up to degree \(\lfloor m/2\rfloor\). Enumeration of all \(a,b\) is polynomial in \(|x|\). The expectation error is at most \(1/12\) by the Fourier expansion. The majority of the resulting ordinary TI answers therefore determines \(A\).

The atlas’s uniform monotone-majority compiler uses a logarithmic-depth sorting network, writes its comparator gates as AND and OR, unfolds the desired output wire as a polynomial-size positive formula, and compiles that formula into one ordinary TI query. Apply this compiler to the enumerated seeds. Consequently under \(\neg H\), every randomized many-one reducer has, for each fixed polynomial bound, infinitely many inputs whose seed acceptance function exceeds that bound. Finite exceptions could be hardcoded. [Ajtai–Komlós–Szemerédi, logarithmic-depth sorting](https://doi.org/10.1145/800061.808726)

### W09. Unknown logarithmic seed dependencies can still be enumerated uniformly

A randomized reduction whose resulting ordinary TI answer depends on at most \(C\log |x|\) among its polynomially many seed coordinates already implies \(H\). This is a semantic dependence condition, applicable when the reduction writes all seed coordinates into its output and the ordinary TI answer reveals only a small unknown subset. A Boolean function of \(k\) coordinates has at most \(2^k\) nonzero Walsh coefficients. Parseval and Cauchy–Schwarz give spectral norm at most \(2^{k/2}\), so W08 supplies a single deterministic seed schedule for every such subset.

The same conclusion holds if each Boolean acceptance function has bounded Fourier degree, with the degree bounded by an input-independent constant. In that case there are polynomially many possible Fourier supports and again Parseval gives a polynomial norm bound. Both criteria are bounds on the seed *answer* after invoking membership in ordinary TI, even if the transformation itself has many active seed coordinates.

### W10. Spectral control yields deterministic verifiable search without a target decision oracle

Let a randomized algorithm output a candidate signed transporter on every input, with verifiable success probability at least \(2/3\) on YES instances. Its random seed may implement arbitrary source/target group blinding. If the verifier-success Boolean function of the seed has polynomial spectral norm uniformly over inputs, then deterministic polynomial-time signed witness search, and hence \(A\in\mathrm P\), follows. Use W08 to enumerate biased seeds and check each candidate directly. On YES the biased acceptance expectation is positive, and on NO no witness verifies. This version obtains a deterministic search algorithm and does not use the majority compiler.

In the \(\neg H\) world this excludes a randomized signed-search algorithm of that spectral class. It also excludes a randomized ordinary witness algorithm whose *derived* signed-search algorithm in the atlas has that spectral bound including all private blinding randomness. A spectral bound on the ordinary verifier alone is insufficient for this latter inference.

## Explicit oracle comparisons

### W11. Equality can coexist with forward one-way permutations and a UP separation

Join a fixed SAT oracle with a sequence of independent uniform forward permutations \(\pi_n\) of \(\{0,1\}^n\), accessing forward evaluations through ordinary bit queries. Relative to \(\Omega=\mathrm{SAT}\oplus\pi\), the fixed languages \(A,B\) are in \(\mathrm P^\Omega\), so \(H^\Omega\) holds. Give the adversary whole forward values per query to upper bound inversion. Conditional on a random challenge output and any transcript that has not queried its preimage, the preimage is uniform among unqueried points of that block. A \(q\)-query machine therefore has expected inversion probability at most \((q+1)/2^n\), including its final guess. Other blocks and SAT can be conditioned on for this bound. For every fixed polynomial-clock probabilistic machine, Markov's inequality and summability imply that almost surely its inversion success is at most \(2^{-n/3}\) for all sufficiently large \(n\). Intersect over the countable list of machines. Thus almost every such \(\Omega\) has relative one-way permutations.

For the same \(\Omega\), the language \(\{(y,i):\pi_{|y|}^{-1}(y)_i=1\}\) belongs to \(\mathrm{UP}^\Omega\cap\mathrm{coUP}^\Omega\) using the unique preimage as the witness to either answer. A \(\mathrm P^\Omega\) algorithm for that language would invert by recovering all bits. Hence the inclusion of \(\mathrm P^\Omega\) in this intersection is strict.

### W12. Equality can also coexist with absence of every relative one-way function

Take \(\Omega\) to be a PSPACE-complete language with polynomial-time many-one reductions. Then \(\mathrm P^\Omega=\mathrm{NP}^\Omega=\mathrm{PSPACE}\). It follows that \(H^\Omega\) holds. Every polynomial-time oracle function has a polynomial-time oracle preimage search on its range, given the original input length in unary. For candidate prefix \(p\), ask whether some string of the specified length extending \(p\) maps to the given value. This is an \(\mathrm{NP}^\Omega\) predicate and hence is decidable in \(\mathrm P^\Omega\). Bitwise search succeeds with probability 1. Thus every candidate relative one-way function fails. This and W11 exhibit both cryptographic behaviors with equality in explicit relativized settings.

### W13. A fair random oracle gives a quantum-resistant classical one-way function

Let \(O\) be a uniform fair bit oracle. Its independent blocks specify maps \(F_n: \{0,1\}^n\to\{0,1\}^{3n}\) by reading \(3n\) bits at fixed, efficiently indexed addresses for each input. Almost surely \(F_n\) is injective for all sufficiently large \(n\), as the probability of any collision at length \(n\) is at most \(2^{-n}\). The family is one-way even for uniform quantum polynomial-time adversaries with coherent oracle access.

For the query bound, choose independent uniform \(x\in\{0,1\}^n,y\in\{0,1\}^{3n}\) and plant \(F_n(x)=y\) into a fresh random oracle. This has the real challenge distribution. In the unplanted computation on \(y\) the query magnitude on addresses belonging to \(x\), averaged over \(x\), is at most \(2^{-n}\) at every query. If the magnitudes are \(p_t(x)\), the standard hybrid Euclidean distance between final states is at most \(2\sum_{t=1}^q\sqrt{p_t(x)}\): compare planted and unplanted query operators on the unplanted intermediate states. By Cauchy–Schwarz the expected squared distance is at most \(4q^2 2^{-n}\). The squared norm of the component producing output \(x\) is at most twice its unplanted squared norm plus twice the squared distance. Its expectation is therefore at most \((2+8q^2)2^{-n}\). The chance of another preimage of \(y\) in the planted model is at most \(2^{-2n}\). Markov, summability, and a countable intersection prove the almost-sure security claim. Independent, fixed oracle components such as SAT can be added without affecting this argument. [Bennett–Bernstein–Brassard–Vazirani, quantum query hybrid](https://arxiv.org/abs/quant-ph/9701001)

### W14. The randomized Karp branch controls equality in the random-oracle cryptographic world

Write \(H_{\mathrm R}\) for the existence of a uniform bounded-error randomized one-output reduction from \(A\) to \(B\). If \(H_{\mathrm R}\) is false, then almost surely a fair random oracle \(O\) gives the following simultaneous properties:
\[
 A\not\le_m^{\mathrm P^O}B,\qquad
 \mathrm P^O=\mathrm{BPP}^O,\qquad
 \mathrm{PH}^O\text{ is infinite},\qquad
 \text{quantum-resistant one-way functions exist relative to }O.
\]
If \(H_{\mathrm R}\) holds, the same last three properties hold almost surely and \(A\le_m^{\mathrm P^O}B\). Ordinary tensor instances are unchanged by the oracle.

For strictness, if some deterministic clocked oracle reducer works for all inputs on a positive-measure set of oracles, choose a finite cylinder of conditional success measure above \(2/3\) by the density theorem. Hardcode its fixed prefix and lazily sample the other oracle bits. This is an unrelativized randomized reduction. Conversely amplify an \(H_{\mathrm R}\) reducer by independent repetition and compile the majority of the ordinary answers into one ordinary instance as in W08. The resulting error probabilities can be made to sum to less than 1 over all inputs. Encode independent amplification seed blocks in a random oracle. Then it works on every input with positive probability, and existence of some successful deterministic polynomial-time oracle reducer is invariant under finite oracle changes by hardcoding the exceptions. The zero-one law gives probability 1. The other properties hold simultaneously by intersecting the probability-one events from W13, Bennett–Gill and Rossman–Servedio–Tan. Thus this gives a conditional relative witness for strictness and quantum-resistant one-way functions under the *stronger* negative hypothesis \(\neg H_{\mathrm R}\). [Bennett–Gill](https://doi.org/10.1137/0210008), [Rossman–Servedio–Tan](https://arxiv.org/abs/1504.03398)

### W15. Quantum many-one reductions also have an exact positive-measure oracle criterion

Define a quantum many-one reduction as a uniform polynomial-time quantum algorithm producing a *classical* ordinary instance \(y\) with \(\Pr[1_B(y)=1_A(x)]\ge 2/3\). Such a reduction exists unrelativized if and only if the set of fair bit oracles relative to which such a reduction exists has positive measure. If it has positive measure it in fact has measure 1, by the unrelativized reduction ignoring its oracle.

For the substantive direction, fix a single polynomial-clock quantum reducer that works on a positive-measure set of oracles. Hardcode a finite cylinder with conditional success measure at least \(0.99\). For each input, if \(q\) bounds the number of oracle gates, simulate the remaining random bits by a \(2q\)-wise independent Boolean truth table on all possible query addresses. Such a table is generated by choosing a uniform degree-\((2q-1)\) polynomial over \(\mathbf F_{2^m}\), embedding addresses of bounded length as distinct field elements, and taking one fixed nonzero binary linear functional of its values. The field and polynomial take polynomial time to construct. One may sample an irreducible polynomial and use bounded repetitions with negligible failure, using the count of irreducibles and the standard gcd irreducibility test. The simulated bit queries have a polynomial-size reversible implementation.

The success probability, as a function of oracle bits, is multilinear of degree at most \(2q\), by expanding amplitudes and squaring. The membership condition on the classical output is just a sum over a fixed set of outputs, so it imposes no extra oracle queries. Hence its expectation is the same for the limited-independent simulation as for a genuinely random completion, ignoring the negligible field-construction abort probability. The success lower bound is initially \(0.99(2/3)\), bounded away from \(1/2\). Amplify and use ordinary TI majority compilation to regain a single output with error at most \(1/3\). Equivalently, even coherent access to fair bits cannot create a quantum reduction on a positive-measure set when the unrelativized quantum reduction fails to exist. [Beals–Buhrman–Cleve–Mosca–de Wolf, quantum polynomial method](https://arxiv.org/abs/quant-ph/9802049)

### W16. Equality, \(P=BPP\), and quantum-resistant one-wayness coexist in one relative world

Let \(\Omega=\mathrm{SAT}\oplus O\), for fair random \(O\). Both tensor languages belong to \(\mathrm P^\Omega\), so \(H^\Omega\) holds, and W13 supplies relative quantum-resistant one-way functions. For completeness, \(\mathrm P^\Omega=\mathrm{BPP}^\Omega\) almost surely, with the following direct argument valid for any fixed oracle joined to \(O\).

Fix a clocked randomized oracle machine \(M\), amplify its \(2/3\) versus \(1/3\) gap to error at most \(2^{-3n}\) on length \(n\), and take a polynomial upper bound \(t(n)\) on amplified query lengths and random bits. Supply its simulated coins from distinct, efficiently indexed addresses in \(O\) of length exceeding \(t(n)\). Conditional on every shorter oracle bit and the fixed oracle, these are independent fair bits. For each \(x\), the event that a genuine gap is present but the simulation makes the wrong decision has unconditional probability at most \(2^{-3n}\). The union bound over lengths and inputs is summable. Almost surely only finitely many lengths have any incorrect simulation on a gap input. A machine recognizing a \(\mathrm BPP^\Omega\) language has the gap on every input, so a deterministic oracle machine hardcodes those finitely many exceptions. Intersect over the countable list of machines.

In this same world, \(\mathrm{NP}^\Omega\nsubseteq\mathrm{BQP}^\Omega\): if the inclusion held, the \(\mathrm{NP}^\Omega\) predicate for existence of a preimage extending a given prefix would have a bounded-error quantum algorithm. Repeated, amplified prefix queries would invert W13 with bounded error, contradicting its quantum security. This supplies an unconditional relative witness with fixed-language equality, classical derandomization, and a quantum search hardness separation.

### W17. Equality with an infinite polynomial hierarchy after a fixed oracle join

For every fixed language \(D\), \(\mathrm{PH}^{D\oplus O}\) is infinite for almost every fair \(O\). The following depth argument allows arbitrary fixed \(D\), including SAT.

Fix \(k\ge 0\) and put \(d=k+3\). Define an oracle language whose input supplies \(1^n\) and \(d\) gate fan-ins at most \(2^n\), encoded in binary. Evaluate an alternating depth-\(d\) complete level-regular AND/OR tree (root OR when \(d\) is even and AND when \(d\) is odd) on independent oracle bits \(O(n,\mathrm{fan\mbox{-}ins},i_1,\ldots,i_d)\), indexed by the root-to-leaf choices, with a fixed injective binary encoding of length at least \(n\). Each level is evaluated by an existential or universal choice of an \(n\)-bit index into the specified child range, with out-of-range choices treated as the neutral bit of the gate. The language belongs to \(\mathrm{PH}^{D\oplus O}\). The fan-ins are explicit input data, allowing us to choose the width parameter of the Rossman–Servedio–Tan Sipser formula in each hardness comparison without computing those widths as part of the language algorithm.

For any fixed \(\Sigma_k^{\mathrm P,D\oplus O}\) machine, select arbitrarily large \(n\) and fan-ins of a hard Sipser formula from their Theorem 1, with \(n\) chosen as the bit length needed by the largest child index. The number \(N\) of active variables is \(2^{\Theta(n)}\). Condition on all \(O\)-bits outside the active block and hardwire the answers from \(D\). For fixed quantified strings, expand the deterministic polynomial-time matrix predicate into a DNF of accepting oracle answer transcripts. Each transcript contributes one conjunction specifying the active bits it reads, and there are at most \(2^{\operatorname{poly}(n)}\) transcripts and string tuples. Including the quantifiers yields a circuit of depth at most \(k+2=d-1\) and size \(2^{\operatorname{poly}(n)}\). Its conditional probability of the correct answer on this input is then at most \(1/2+o(1)\), uniformly in the hardwired bits. Any fixed finite cylinder is disjoint from the active block when \(n\) is sufficiently large. Consequently a positive-measure event of this machine being correct on all inputs would give a finite cylinder of conditional correctness measure exceeding \(3/4\), contradicting the single-input upper bound. Take the countable intersection over \(k\) and clocked machines. This proves the infinite hierarchy claim.

With \(D=\mathrm{SAT}\), this gives an actual relative model with \(H^\Omega\), infinite \(\mathrm{PH}^\Omega\), and all the properties in W16. [Rossman–Servedio–Tan, §§2, 6 and Theorem 1](https://arxiv.org/abs/1504.03398)

## A quasipolynomial-time comparison

### W18. Small constant-depth seed predicates give a deterministic quasipolynomial reduction

Suppose that for a randomized Karp reducer \(R(x;s)\) every \(f_x(s)=1_B(R(x;s))\) is computable by an \(\mathrm{AC}^0\) circuit of depth at most a fixed \(d\) and size at most \(|x|^c\) for fixed \(c\). The circuits need not be given. Then there is a deterministic quasipolynomial-time many-one reduction from \(A\) to \(B\).

Braverman's theorem allows the uniform seed to be replaced with any \(k=(\log |x|)^{O_d(1)}\)-wise independent distribution at expectation error at most \(1/12\). Use the usual degree-\((k-1)\) polynomial-evaluation construction over \(\mathbf F_{2^m}\), with \(m=O(\log |x|)\) large enough for the seed addresses. Enumerate its \(2^{km}=2^{(\log |x|)^{O_d(1)}}\) coefficient tuples. The enumeration yields a correct majority of ordinary queries, and the same monotone-majority compiler as in W08 creates a single quasipolynomial-length instance in quasipolynomial time. This conclusion concerns the quasipolynomial reduction class. [Braverman, bounded independence for \(\mathrm{AC}^0\)](https://eccc.weizmann.ac.il/eccc-reports/2009/TR09-011/)

## Scope

W01–W07 establish proof-system statements for the specified presentations. W08–W10 give sufficient conditions for unrestricted decision reductions or algorithms under explicitly quantified hypotheses. W11–W17 compare actual or conditional relative models. W18 gives a sufficient condition for a deterministic quasipolynomial reduction. None of the relative witnesses decides unrelativized \(H\). In particular \(\neg H\) alone is insufficient for the negative direction of the random-oracle criterion here, which requires \(\neg H_{\mathrm R}\).
