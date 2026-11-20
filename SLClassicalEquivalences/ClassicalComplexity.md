# Classical complexity consequences for finite-field special-linear tensor isomorphism

## Setting and established results

The inputs are two dense three-tensors of the same format, over a fixed finite field or over a finite field supplied by its prime characteristic and a polynomial-basis presentation. All reductions below are uniform bit-model reductions. A same-field reduction outputs an instance over its input field. The determinant-one group is the product of the three special linear groups. Denote ordinary and determinant-one decision by $L_{\rm GL}$ and $L_{\rm SL}$. The question is whether $L_{\rm SL}\le_m^P L_{\rm GL}$. [Chen, Grochow, Qiao, Tang and Zhang, Open Question 1.9](https://arxiv.org/html/2306.03135v2#S1.SS5).

The results here are
$$
\begin{gathered}
 \mathrm{GI}\le_m^P L_{\rm GL}\le_m^P L_{\rm SL},
 \qquad L_{\rm GL},L_{\rm SL}\in\mathrm{NP}\cap\mathrm{SZK},\\
 L_{\rm GL},L_{\rm SL}\in\mathrm{ZPP}^{\mathrm{MKTP}}
                 \cap\mathrm{RP}^{\mathrm{MCSP}},\\
 \mathrm{BPP}^{L_{\rm SL}}\subseteq\mathrm{AM}\cap\mathrm{coAM}.
\end{gathered}
$$
Here MKTP is Minimum KT Problem and MCSP is Minimum Circuit Size Problem. The randomized oracle containments are Turing reductions. The resulting conditional reductions, hierarchy implications, and oracle counterexample to a converse are proved below.

## The direction from ordinary isomorphism and the graph-isomorphism comparison

Pad each tensor mode by a one-dimensional null summand. Every ordinary witness $(g_i)_i$ extends on the $i$-th new line by multiplication by $(\det g_i)^{-1}$. This gives a determinant-one witness of the padded pair.

For reflection, the support in the $i$-th mode is the span of all contractions in the other two modes. A transporter maps each source support onto the corresponding target support, by functoriality of contraction and invertibility in every other mode. A tensor belongs to the tensor product of its three supports, as one sees by using bases extending each support and inspecting the coefficients outside it. The padded supports lie in the original mode spaces. Restrict each padded map to its support and extend that linear isomorphism arbitrarily to the original mode dimensions. The extensions transport the original tensors. This proves $L_{\rm GL}\le_m^P L_{\rm SL}$ including degenerate and zero tensors.

The known graph-to-tensor reduction works over arbitrary fields and thus composes with this padding over any chosen finite field. A polynomial-time algorithm for either tensor language therefore gives one for GI. A reduction $L_{\rm SL}\le_m^P\mathrm{GI}$ would establish equality of all three many-one degrees and give a quasipolynomial-time algorithm for the tensor languages. A reduction $L_{\rm GL}\le_m^P\mathrm{GI}$ together with the sought reverse tensor reduction would have the same consequence. [Grochow and Qiao, Section 3.2](https://arxiv.org/html/1907.00309#S3.SS2), [Babai, *Graph Isomorphism in Quasipolynomial Time*](https://arxiv.org/abs/1512.03547).

## Uniform implementation of the finite matrix-group samplers

For $K=\mathbf F_q$ in polynomial-basis representation, an integer from $0$ to $q-1$ indexes a field element by its base-characteristic digits. Field arithmetic, Gaussian elimination, and determinant computation take polynomial bit time in the relevant matrix dimensions and $\log q$.

There is a deterministic polynomial-time bijection from the integers $0,\ldots,|\operatorname{GL}_d(K)|-1$ to the invertible matrices. Decode the index in mixed radix, with one digit per row and radix $q^d-q^i$ after $i$ independent rows are chosen. Complete the chosen rows to an ambient basis by scanning standard basis vectors. In those basis coordinates a new admissible row is an arbitrary vector in its first $i$ positions and a nonzero vector in its remaining $d-i$ positions. Use radix $q^i$ for the unrestricted part and $q^{d-i}-1$ for the nonzero part. Every independent row choice occurs once.

For $\operatorname{SL}_d(K)$, use the same first $d-1$ row choices. At the last stage, the determinant as a linear function of the last row vanishes exactly on the span of the previous rows. If the chosen complementary basis vector yields a determinant $c\ne0$, its coordinate in the last row is set to $c^{-1}$. The other coordinates range freely and yield the last radix $q^{d-1}$. This covers $d=1$, when the only matrix is $(1)$. The orders are
$$
 |\operatorname{GL}_d(K)|=\prod_{i=0}^{d-1}(q^d-q^i),\qquad
 |\operatorname{SL}_d(K)|=|\operatorname{GL}_d(K)|/(q-1).
$$
One obtains the order and indexing of a product of three groups by a further mixed radix. All integer arithmetic here is on bit lengths polynomial in the dense tensor input.

For an approximately uniform bounded-bit sampler on a group of order $N$, choose a uniform $k$-bit integer, reduce it modulo $N$, and apply this bijection. Each group element receives either $\lfloor2^k/N\rfloor$ or $\lceil2^k/N\rceil$ preimages. For $0<\delta\le1/2$, taking $2^k\ge 2N/\delta$ gives probability for each group element within a multiplicative factor $1+\delta$ of $1/N$. The sampler uses $O(\log N+\log(1/\delta))$ random bits and is a deterministically constructible polynomial-size Boolean circuit. Its statistical distance from uniform is at most $\delta$. The same implementation applies to the two relevant product groups.

## Statistical zero knowledge and a hierarchy consequence

A proposed transporter is an NP certificate. Check its invertibility or its explicit determinants, and evaluate its tensor action.

For either product group $G$, let $C_T$ be the circuit that samples an approximately uniform $g\in G$ as above with $\delta=1/20$ and outputs the coefficient encoding of $gT$. The exactly uniform group sample induces the uniform distribution on the orbit, since every element of the orbit has the same number of preimages. Isomorphic inputs therefore induce the same ideal distribution. By the triangle inequality the circuits' distance on isomorphic inputs is at most $2\delta<1/3$. On nonisomorphic inputs the supports are disjoint, so the distance is $1>2/3$, even with these approximate samplers. This is a deterministic many-one reduction of the complement of either tensor language to the Statistical Difference promise problem. On malformed encodings reject the tensor input and output any fixed pair in the far case. The field can be validated by deterministic primality testing and the finite-field polynomial irreducibility test using Frobenius powers and gcd computations. Sahai and Vadhan prove completeness of Statistical Difference, closure of SZK under complement, and $\mathrm{SZK}\subseteq\mathrm{AM}\cap\mathrm{coAM}$. [Sahai and Vadhan, Theorem 3.1 and Corollaries 4.4 and 4.5](https://web.cs.ucla.edu/~sahai/work/web/2003%20Publications/J.ACM2003.pdf).

For any total language $A\in\mathrm{AM}\cap\mathrm{coAM}$, one has $\mathrm{BPP}^{A}\subseteq\mathrm{AM}\cap\mathrm{coAM}$, even allowing adaptive oracle calls. Here is a public-coin transcript proof. Fix an oracle algorithm with query-string lengths bounded by a polynomial $p(n)$ and amplify its correctness with the true oracle to $7/8$. Use a single common public random tape for an amplified two-message protocol for $A$, and a separate one for its complement. Pad the protocol randomness to a common length for query strings of length at most $p(n)$. Amplify both proof protocols until the failure probability for each fixed query and each claimed true or false membership is at most $2^{-p(n)-6}$. The failure here is either that no certificate exists for a true claim or that some certificate exists for a false claim. Independent repetitions with a majority threshold give this guarantee even when certificates are chosen after seeing all repetitions. By the union bound over every string of length at most $p(n)$ and both claims, with probability at least $15/16$ the public tapes allow exactly the true claim on every possible query string. This bound precedes Merlin's choice of the transcript, so it controls adaptive queries.

Arthur also sends the original algorithm's random tape. Merlin replies with its proposed accepting transcript including all queries, claimed responses, and membership or nonmembership certificates as appropriate. Arthur checks the deterministic simulation given those responses and checks each certificate against the public randomness. With good proof tapes this is exactly the behavior of the randomized algorithm with the true oracle, which proves the AM completeness and soundness gaps. Apply the same construction to the complemented oracle algorithm to obtain coAM. Combining with the preceding tensor inclusion proves the stated result for both tensor oracles.

In particular, if SAT has a bounded-error randomized polynomial-time Turing reduction to either tensor language, then $\mathrm{NP}\subseteq\mathrm{coAM}$ and $\mathrm{coNP}\subseteq\mathrm{AM}$. The Boppana–Håstad–Zachos theorem then gives $\mathrm{PH}=\Sigma_2^P$. This conclusion also applies to the narrower deterministic and many-one notions of NP-hardness. [Boppana, Håstad and Zachos, *Does co-NP have short interactive proofs?*](https://doi.org/10.1016/0020-0190(87)90232-8).

## Consequences for P versus NP and an oracle counterexample to the converse

If $L_{\rm SL}\in\mathrm P$, decide the input and return a fixed ordinary yes or no pair over the same field. The one-entry tensor pairs $(1,1)$ and $(1,0)$ suffice. Thus
$$
 \mathrm{P}=\mathrm{NP}\cap\mathrm{SZK}
   \ \Longrightarrow\ L_{\rm SL}\le_m^P L_{\rm GL}.
$$
In particular $\mathrm P=\mathrm{NP}$ implies the desired reduction. An unconditional failure of the reduction would separate $\mathrm P$ from $\mathrm{NP}\cap\mathrm{SZK}$, and therefore from $\mathrm{NP}$. The same constant-output argument shows that a lower bound against even nonuniform polynomial-size many-one reductions would imply $L_{\rm SL}\notin\mathrm{P/poly}$, and hence $\mathrm{NP}\not\subseteq\mathrm{P/poly}$.

The converse $L_{\rm SL}\le_m^P L_{\rm GL}\Rightarrow\mathrm P=\mathrm{NP}$ fails under a natural external-oracle interpretation. Keep the tensor languages fixed and grant the same auxiliary oracle to the machines computing reductions and to the machines defining the complexity classes. There is a recursive oracle $\Omega$ such that both tensor languages are in $\mathrm P^\Omega$ while $\mathrm P^\Omega\ne\mathrm{NP}^\Omega$. In particular the same-field equivalence of the two fixed languages holds in this oracle world.

To construct $\Omega$, take $\Omega=\mathrm{SAT}\oplus B$ with separate prefix tags. The fixed SAT part decides each of the original NP languages in deterministic polynomial time by the Cook–Levin reduction. For separation let
$$
 M_B=\{1^n: \text{some binary word of length }n\text{ belongs to }B\}.
$$
It lies in $\mathrm{NP}^\Omega$ by guessing that word. Enumerate deterministic oracle machines with explicit polynomial clocks. At the stage for machine $i$ and clock $p_i$, choose $n$ exceeding all previously fixed word lengths and with $2^n>p_i(n)$. Simulate the machine on $1^n$ with its SAT answers fixed and all currently unassigned $B$-queries answered negatively. If it accepts, set all $n$-bit words absent from $B$. If it rejects, put one unqueried $n$-bit word into $B$, which exists by the clock bound. Preserve all queried $B$-answers and extend the fixed initial segment of lengths past every query length and past $n$, setting the remaining positions in that segment to zero. This makes the unchanged machine computation incorrect on $1^n$. The construction is effective because SAT is computable and each stage is finite. It proves $M_B\notin\mathrm P^\Omega$ and thus the separation. The argument excludes a converse that holds in every external-oracle world of this kind. [Baker, Gill and Solovay, *Relativizations of the P =? NP Question*](https://doi.org/10.1137/0204037).

## Minimum circuit size, minimum KT, and derandomization

Apply the circuit inversion theorem of Allender and Das directly to the orbit samplers. Given $C_T,C_S$, draw $y=C_T(u)$ with $u$ uniform, run the $\mathrm{MCSP}$-oracle inverter on $C_S,y$, and accept only if it returns a string $v$ with $C_S(v)=y$. A negative pair has disjoint supports, so cannot be accepted. For a positive pair both output distributions approximate the same uniform orbit distribution pointwise within the multiplicative factor $1+\delta$, by summing the group-level guarantees over fibers. Thus the success probability on $C_T(u)$ is at least $(1+\delta)^{-2}$ times its success on $C_S(u)$, and the circuit inversion theorem gives an inverse-polynomial bound for the latter. Independent repetitions amplify to constant success. This proves $L_{\rm GL},L_{\rm SL}\in\mathrm{RP}^{\mathrm{MCSP}}$ using Theorem 1. General SZK membership alone gives the two-sided bound of Theorem 4. In particular $\mathrm{MCSP}\in\mathrm P$ together with $\mathrm{RP}=\mathrm P$ suffices for the desired same-field deterministic reduction. This consequence uses a randomized Turing reduction to MCSP before derandomization. [Allender and Das, *Zero Knowledge and Circuit Minimization*](https://www.cs.rutgers.edu/~allender/papers/szk.mcsp.pdf).

The generic isomorphism theorem of Allender, Grochow, van Melkebeek, Moore and Morgan gives the separate stronger error guarantee $L_{\rm GL},L_{\rm SL}\in\mathrm{ZPP}^{\mathrm{MKTP}}$. The conditions have explicit implementations. The sampler above gives bounded-bit multiplicative approximation to uniform, and the group action, products, and inverses are deterministic polynomial-time matrix operations. For the complete universe invariant use the unique coefficient encoding of each tensor, and for the complete group invariant use the unique matrix-tuple encoding. If the underlying group action is required to be faithful, adjoin an abstract tagged regular group orbit to the action universe. Let the group act on that separate orbit by left multiplication. Faithfulness follows from its action at the identity, and the given tensor orbit and its decision problem are unchanged. The additional universe elements also have unique encodings. Use the exact orders above, or round their logarithms upward within the theorem's deviation, for the group size estimator. This checks the hypotheses of Theorem 5.7. In particular $\mathrm{MKTP}\in\mathrm P$ together with $\mathrm{ZPP}=\mathrm P$ suffices for the desired deterministic reduction. [Allender, Grochow, van Melkebeek, Moore and Morgan, Theorems 5.2 and 5.7](https://pages.cs.wisc.edu/~dieter/Papers/gi-mktp-sicomp.pdf).

For either implication the stronger common assumption $\mathrm{BPP}=\mathrm P$ is sufficient for the indicated derandomization. This assumption itself follows if some language in $\mathrm E=\mathrm{DTIME}(2^{O(n)})$ has circuit complexity at least $2^{cn}$ on every sufficiently large length for some $c>0$. [Impagliazzo and Wigderson, *P = BPP if E Requires Exponential Circuits*](https://www.math.ias.edu/~avi/PUBLICATIONS/MYPAPERS/IW97/proc.pdf).

There is also a nonuniform consequence. For a language $A\in\mathrm{P/poly}$, a $\mathrm{BPP}^A$ machine on inputs of length $n$ can hardwire the oracle circuits at each possible query length up to its polynomial bound. Their total size is polynomial in $n$. This gives a polynomial-size randomized circuit, even for adaptive queries. Amplify its error below $2^{-n}$. By the union bound there are fixed random bits that make it correct on every length-$n$ input, so $\mathrm{BPP}^A\subseteq\mathrm{P/poly}$. Apply this either to the MKTP reduction or to the MCSP reduction. If either MKTP or MCSP has polynomial-size Boolean circuits, then the tensor languages do as well and the constant-output approach gives a nonuniform same-field many-one reduction. Thus a lower bound against polynomial-size Boolean circuits that compute reductions would separately imply $\mathrm{MKTP}\notin\mathrm{P/poly}$ and $\mathrm{MCSP}\notin\mathrm{P/poly}$.
## Distinguishing finite-field orbit equality from the PIT-related geometric variants

There are two separate changes of decision problem in passing to geometric orbit closure intersection. One is scalar extension to an algebraic closure. The other is taking orbit closures. Each changes answers on $2\times2\times2$ examples.

For scalar extension, let $A(x,y)=xI_2+yN$, where $N=\begin{pmatrix}0&1\\0&0\end{pmatrix}$, and let $B(x,y)=D A(x,y)$ for a fixed $D$ of determinant $\delta$ nonsquare in an odd-order finite field. A determinant-one transporter would force $\delta (a x+b y)^2=x^2$ in $K[x,y]$ for the first row $(a,b)$ of its label map. This forces $b=0$ and $\delta a^2=1$, impossible over $K$. Over $\overline K$ choose $a$ with $\delta a^2=1$, and let
$$
 P=\operatorname{diag}(a,a^{-1}),\quad
 G=\operatorname{diag}(a^{-1},a),\quad H=aDG.
$$
All determinants are one, and $B(Pw)G=HA(w)$ follows by direct substitution.

For the closure change, let $T=e_1\otimes e_1\otimes e_1$ and compare it to zero. They have different special-linear orbits because every factor map is invertible. Over the algebraic closure, $\operatorname{diag}(t,t^{-1})$ in the first factor sends $T$ to $tT$ for every $t\ne0$. The orbit thus has zero in its Zariski closure. Invariant-based results for algebraic orbit-closure intersection apply to a different decision relation from the one treated here. [*Fixed-Parameter Degree Bounds and Complexity of the Orbit Closure Intersection Problem for Tensors*](https://doi.org/10.4230/LIPIcs.CCC.2026.32).

Ordinary arithmetic PIT tests whether a circuit computes the zero formal polynomial. The known connection between its derandomization and circuit lower bounds is conditional on such a PIT algorithm. The equalities and containments proved here concern exact finite-field orbit decisions. A classical equivalence through PIT would require an explicit reduction preserving that exact rational orbit condition and the relevant model of computation. [Kabanets and Impagliazzo, *Derandomizing Polynomial Identity Tests Means Proving Circuit Lower Bounds*](https://www2.cs.sfu.ca/~kabanets/papers/short_poly_derand.pdf).

## Verification and scope

The orbit sampler, padding argument, adaptive-oracle hierarchy implication, and external-oracle construction are given as informal proofs. The MKTP and MCSP results are applications of the cited theorems with the required instances identified. These results establish implications and a relativized obstruction. The unrestricted same-field many-one reduction and an unrelativized equivalence to a classical open problem remain open here.
