# Linear algebra, coupled comparisons, and counting

Let \(H\) denote the deterministic polynomial-time many-one reduction from determinant-one to ordinary dense three-tensor isomorphism over \(\mathbb F_3\). These results use the [ordinary linear switch compiler](../baseline/LinearSwitchCompiler.md). A complementary query pair consists of two constructed ordinary TI instances with exactly one YES on the stated domain. Complement TI reducing to TI is one sufficient premise for supplying these pairs globally.

## Input-dependent linear algebra

<a id="entry-201"></a>

### 201. Linear systems with query-dependent coefficients

One ordinary TI instance tests consistency of a linear system over an explicitly tabulated finite ring of polynomial cardinality when each coefficient is a specified linear combination of complementary query bits. Use the additive group of the ring. For a term \(b x\), use two variables \(p,q\) in this group, permitted by the true and false rails respectively, and impose \(x=p+q\). Then \(p=bx\), with \(b\) regarded as 0 or 1. Multiplication by a specified coefficient is an additive homomorphism. The construction also handles query-dependent right hand sides by supplying a fixed unit and splitting it in the same manner. All equations can coexist in one instance.

<a id="entry-202"></a>

### 202. Nonsingularity by a right inverse

For a square matrix \(M\) over a finite commutative ring with such query-dependent entries, add unknown columns \(x_j\) and impose \(Mx_j=e_j\) simultaneously. A right inverse implies \(\det M\) is a unit by multiplicativity and hence implies invertibility. Over a field this also tests full row rank for a rectangular matrix. The ordinary query is built without computing the input bits or a determinant.

<a id="entry-203"></a>

### 203. Determinant residues over explicit finite rings

Equality \(\det M=a\) over a finite commutative ring of polynomial cardinality is one TI comparison under [Entry 201](#entry-201). Use the division-free signed algebraic branching program for determinant, whose layers track heads, current vertices and lengths of clow sequences. Every edge weight is a constant or a signed matrix entry. Put an additive variable at each state, initialize the start to one, and require each variable to equal the sum of predecessor values times edge weights. Use [Entry 201](#entry-201) for each query-dependent factor. A topological induction evaluates the branching program. The terminal equation specifies the desired residue. Inequality to a residue is a balanced disjunction over other polynomially many values. [Mahajan and Vinay, determinant via clow sequences](https://repository.ias.ac.in/127977/)

<a id="entry-204"></a>

### 204. Rank thresholds via explicit compression

Under [Entry 201](#entry-201) one ordinary comparison tests any rank threshold over a fixed finite field. Let \(C_{r,a}(t)_{ij}=t^{ij}\) for \(1\le i\le r\), \(0\le j<a\). For \(r\) independent columns of an \(a\)-row matrix, represent the columns by coordinate polynomials and change basis to strictly increasing degrees. In the determinant of evaluations at \(t,t^2,\ldots,t^r\), the rearrangement inequality gives one term of greatest degree with nonzero coefficient. Its degree is at most \((a-1)r(r+1)/2\). Thus one left compression from an explicit field of larger order preserves their rank. Apply the same argument to the transpose for right compression. Rank at least \(r\) is equivalent to at least one of the polynomially many \(C_{r,a}(t)M C_{r,b}(s)^{\mathsf T}\) being invertible. Use [Entry 202](#entry-202) and balanced OR. Rank below \(r\) requires all compressed determinants to be zero, using [Entry 203](#entry-203). Field extension preserves rank. An extension of polynomial cardinality is obtained by enumerating monic polynomials of logarithmic degree over the base field and testing irreducibility. Impossible thresholds and \(r=0\) are constant cases.

<a id="entry-205"></a>

### 205. Intersection dimensions without chosen bases

For query-dependent spanning matrices \(U,V\), test a requested value or bound for \(\dim(\operatorname{im}U\cap\operatorname{im}V)\) using \(\operatorname{rk}U+\operatorname{rk}V-\operatorname{rk}[U\ V]\). Enumerate the polynomially many rank triples satisfying the numerical condition, assert each triple by [Entry 204](#entry-204), and disjoin. Equality, containment and directness of two implicitly selected subspaces can therefore be checked without extracting bases.

<a id="entry-206"></a>

### 206. Characteristic polynomials and cospectrality

Equality of the characteristic polynomial of a query-dependent matrix to a supplied polynomial, or to that of another such matrix, has one ordinary comparison. Evaluate both at one more than their degree bound in an explicit extension and compare determinants through [Entry 203](#entry-203). Equality of two residues is a disjunction over their common possible value. For polynomial-bit integers, use small primes whose product exceeds twice a coefficient bound and interpolate over each residue field or an extension. Coefficient bit bounds follow from the permutation expansion. This also tests cospectrality of graphs whose edges are supplied by complementary ordinary queries.

<a id="entry-207"></a>

### 207. Polynomial identities for matrix pencils with a fixed number of parameters

Given query-dependent matrix pencils in a fixed number of variables, with polynomial individual degrees, equality of their determinant polynomials reduces to ordinary TI. Each individual degree stays polynomial, so compare determinants using [Entry 203](#entry-203) on a polynomial-size product grid over an extension larger than that degree bound. Repeated univariate interpolation makes the grid a hitting set. This tests formal polynomial equality even when evaluating only at the base-field points would lose information.

<a id="entry-208"></a>

### 208. Testing a claimed minimal polynomial

For a query-dependent matrix \(M\) and a supplied monic \(f\) of degree \(d\), track the flattened matrices \(I,M,\ldots,M^d\) by linear recurrences \(v_{j+1}=Mv_j\) on each basis column. The equation \(f(M)=0\) is linear. To prove independence of \(I,\ldots,M^{d-1}\), use the left rank condensers of [Entry 204](#entry-204). For a fixed condenser, assert a right inverse of the compressed matrix as follows. For each asserted inverse column and each exponent \(j<d\), initialize a separate matrix track at \(a_j I\) with unknown scalar \(a_j\), apply \(M\) exactly \(j\) times columnwise, then sum and compress the terminal tracks. Require the sum to be the requested standard basis vector. This realizes the linear combination with coefficients \(a_j\) without multiplying two unknown variables. Disjoin over the polynomially many condensers, and conjoin \(f(M)=0\). The monic polynomial of least degree that annihilates \(M\) is unique. Degree zero is an immediate test of the zero-dimensional case.

<a id="entry-209"></a>

### 209. Exact finite-horizon linear reachability

For explicitly many query-dependent matrices \(A_i,B_i\) over a finite ring, existence of a trajectory \(x_{i+1}=A_i x_i+B_i u_i\) with supplied affine restrictions on the initial, intermediate and final states has one ordinary comparison by [Entry 201](#entry-201). Include all states and controls as additive variables in that system. This tests observations on an actual common trajectory, including when transition matrices change with time.

<a id="entry-210"></a>

### 210. Controllability by parallel trajectories

Over a field, controllability from zero of the system in [Entry 209](#entry-209) has one ordinary comparison. The attainable endpoints form a subspace, so run independent trajectories initialized at zero and require them to hit every basis endpoint. For containment of a given target subspace, request only its supplied spanning list. The construction avoids evaluating the implicit matrices or forming a symbolic controllability matrix.

<a id="entry-211"></a>

### 211. Rational rank and rational consistency

For polynomial-bit integer matrices with complementary query bits, rational rank at least \(r\) holds exactly when the modular rank is at least \(r\) for some prime from a fixed polynomial list. Choose the list so its product exceeds the magnitude bound for integer \(r\)-minors. A nonzero minor survives at some prime, and a modular nonzero minor was nonzero over the rationals. Apply [Entry 204](#entry-204) and disjoin, using an extension of polynomial cardinality over each polynomial-size residue field as needed. Compare coefficient and augmented ranks for rational consistency.

<a id="entry-212"></a>

### 212. Exact rational linear statistics

For an implicitly selected integer matrix \(M\), right hand side \(g\), and nonzero \(b\), test whether \(M\) is invertible over \(\mathbb Q\) and \(\ell^{\mathsf T}M^{-1}g=a/b\). Require \(\det M\ne0\) and use
\[
-b\,\det\begin{pmatrix}M&g\\\ell^{\mathsf T}&0\end{pmatrix}=a\,\det M.
\]
Integer determinant equalities and inequalities reduce via [Entry 203](#entry-203) over enough distinct small primes. Their product exceeds twice a polynomial-bit magnitude bound. This avoids inverting the matrix modulo a prime that divides its determinant, and the right hand side and row vector can depend on query bits.

## Combinatorial applications

<a id="entry-213"></a>

### 213. Exact spanning tree and forest counts

The integer determinant of a reduced Laplacian counts spanning trees of a graph selected by complementary queries. Its entries are linear combinations of availability bits, so [Entry 203](#entry-203) and CRT compare its integer value to a supplied target. Using \(\det(L+tI)\) and interpolation also compares coefficients of the rooted spanning forest enumerator. These are count predicates beyond connectivity and allow integer edge weights of polynomial bit length. [Chaiken, all minors matrix-tree theorem](https://doi.org/10.1137/0603033)

<a id="entry-214"></a>

### 214. Rooted arborescences with oriented query edges

For a directed host and specified root, delete its row and column in the outgoing-degree row Laplacian. Its determinant is the sum of weights of arborescences directed into the root. A modular suite using [Entry 203](#entry-203) tests exact count or existence when unweighted. This uses directed edges as given and never symmetrizes their availability. [Chaiken, all minors matrix-tree theorem](https://doi.org/10.1137/0603033)

<a id="entry-215"></a>

### 215. Exact planar matching counts

For a fixed embedded planar host with query-selected edges, compute a Pfaffian orientation of the host. Matchings of any selected subgraph are host matchings, so their nonzero Pfaffian terms retain the common sign. Zeroing absent edges gives a skew matrix whose integer determinant is the square of the selected perfect-matching count. Compare it to the square of a nonnegative target by [Entry 203](#entry-203) and CRT. This also tests existence, including on subgraphs whose planar faces differ from the original host's. [Kasteleyn, planar Pfaffian method](https://doi.org/10.1063/1.1703953), [Kenyon, dimer formulas](https://arxiv.org/abs/0910.3129)

<a id="entry-216"></a>

### 216. Randomized maximum matching threshold

For an arbitrary graph selected by complementary queries, a one-sided randomized many-one map to ordinary TI tests whether the maximum matching size is at least \(k\). Sample the entries of the symbolic skew Tutte matrix in a polynomial-size odd field and apply [Entry 204](#entry-204) with threshold \(2k\). Over the rational function field an alternating form has rank at least \(2k\) iff a principal \(2k\)-minor is nonsingular, by skew elimination. That Pfaffian is nonzero exactly when those vertices have a perfect matching, since different matchings give distinct monomials with coefficients \(\pm1\). Thus a NO input can never pass, and a YES input passes with constant high probability by Schwartz–Zippel in a polynomial-size choice of field.

<a id="entry-217"></a>

### 217. Randomized common bases in two linear matroids

For fixed-field \(r\times m\) matrices \(U,V\), use the polynomial
\[
\det(U\operatorname{diag}(x_i)V^{\mathsf T})=
\sum_{|S|=r}\det(U_S)\det(V_S)\prod_{i\in S}x_i .
\]
Set unavailable \(x_i=0\) using complementary ordinary comparisons, sample the rest in a polynomial-size extension, and apply [Entry 202](#entry-202). Cauchy–Binet shows the polynomial is nonzero exactly when a selected common basis exists. Distinct witness sets have distinct monomials. The randomized one-output map has one-sided soundness.

<a id="entry-218"></a>

### 218. Deterministic sign-compatible common bases

For integer \(U,V\), suppose the products \(\det(U_S)\det(V_S)\) have the same weak sign, as for two totally nonnegative matrices with the same column order. Set available \(x_i=1\). The Cauchy–Binet sum cannot cancel, so [Entry 203](#entry-203) and CRT give a deterministic one-output compiler. It additionally compares the weighted total of common bases, with weights \(|\det(U_S)\det(V_S)|\), to a given integer. The sign agreement is a promise.

<a id="entry-219"></a>

### 219. Effective resistance from implicit edges

For a connected graph with positive integer conductances and edges selected by complementary queries, ground one vertex and take the reduced Laplacian \(M\). With \(g\) the reduced unit source-sink vector, the effective resistance is \(g^{\mathsf T}M^{-1}g\). [Entry 212](#entry-212) tests equality to an exact rational. Explicitly requiring a nonsingular reduced Laplacian also rejects disconnected inputs.

## Counting normalizations and sign data

<a id="entry-220"></a>

### 220. Polynomial ambiguity gives an exact SPP indicator

On a domain with at most \(M(L)\) transporters per comparison for a fixed polynomial \(M\), write \(t\) for the canonical witness count. The GapP function
\[
 \sum_{i=1}^{M(L)}(-1)^{i+1}\binom{t}{i}
\]
is zero on NO and one on YES. Each binomial counts sorted lists of \(i\) distinct valid witnesses, and the identity follows from the binomial theorem. This proves an SPP language if the domain is polynomial-time recognizable, by rejecting off-domain inputs. Otherwise it proves the promise version.

<a id="entry-221"></a>

### 221. A short list of possible counts yields LWPP

Suppose the nonzero counts at length \(L\) belong to a polynomial-time constructible list \(S_L\) of polynomially many positive polynomial-bit integers. Put \(D_L=\prod_{s\in S_L}s\). The GapP function \(D_L-\prod_{s\in S_L}(s-t)\) is exactly \(D_L\) on YES and zero on NO. This is LWPP on recognizable domains and its promise analogue otherwise. The condition allows exponentially large witness counts, for example powers of a fixed prime with polynomial exponents. An input-dependent list gives the WPP version.

<a id="entry-222"></a>

### 222. Exact-gap lowness on recognizable bounded-count domains

For either tensor action restricted to a recognizable domain as in [Entry 220](#entry-220), eliminate adaptive oracle calls from any GapP computation by guessing the transcript and weighting each call by the exact SPP indicator for the guessed answer. Use one minus that indicator for a guessed NO. Incorrect transcripts contribute zero while the correct one contributes verbatim. GapP as a function class is unchanged, as are PP and exact-zero GapP decision. [Fenner, Fortnow and Kurtz, SPP lowness](https://www.cse.sc.edu/~fenner/papers/gaps.pdf)

<a id="entry-223"></a>

### 223. Unconditional postselection decision

Ordinary and signed tensor isomorphism each have one-sided randomized decision with postselection. Draw a fair bit and three fixed-length candidate matrix encodings. Postselect on a valid stabilizer witness when the bit is zero and a valid transporter witness when it is one. The identity makes the event positive. On YES the witness counts are equal, so accepting when the bit is one succeeds with conditional probability \(1/2\). On NO that probability is zero. Accepting if at least one bit is one in two independent trials conditioned on both events gives probability \(3/4\) on YES. This adds a postselection upper bound to the existing complexity comparison. The event can have exponentially small probability.

<a id="entry-224"></a>

### 224. Signed decision by conditioning on ordinary transporters

On the ordinary-YES promise, postselect a canonically encoded ordinary transporter drawn from uniformly random bits. On signed YES, probability of all-positive determinant is exactly \(1/|\chi(G_x)|\ge1/8\); on signed NO it is zero. Independent draws with separate postselection give independent exact uniform transporters. This shows how to implement a signed postselection test using a conditioning event that makes no determinant selection. It makes no efficient unconditional sampling claim.

<a id="entry-225"></a>

### 225. Walsh transforms of transporter counts

Let \(D=\{\pm1\}^3\) and suppose a ternary ordinary comparison has total count \(t>0\) and determinant coset \(dS\subseteq D\). For every character \(\psi\), its integer weighted transporter count is \(t\psi(d)\) when \(\psi|_S=1\), and zero otherwise, by character cancellation over the equal fibers. This defines eight GapP functions whose discrete Fourier inversion gives every prescribed signed count, with denominator eight. A single weighted overlap therefore belongs to \(\{0,\pm t\}\), revealing whether its character retains orientation information.

<a id="entry-226"></a>

### 226. Recovering all signs using only stabilizer character-kernel counts

Given any ordinary transporter, the full signed profile follows from the ordinary source stabilizer order and its seven restrictions to character kernels. Each kernel count equals the total if the character is trivial on the stabilizer and is exactly half otherwise. Intersect the kernels of the characters in the first category to recover the sign subgroup, then translate by the supplied transporter's determinant. This uses only self-counts and a reference transporter, with no cross-pair signed count.

<a id="entry-227"></a>

### 227. Normalized odd-prime modular witnesses

For ternary tensors and any odd prime \(p\), the signed and ordinary source stabilizer orders have the same \(p\)-adic valuation \(v\), since their index is a power of two. The signed cross-count modulo \(p^{v+1}\) is zero exactly when the signed comparison fails. This criterion uses \(v\) as supplied data. In particular, if the ordinary source stabilizer order is coprime to a fixed \(p\), its signed comparison on that domain is directly a \(\mathrm{Mod}_p\mathrm P\) predicate using the witness count. An uncorrected use of the ordinary valuation at \(p=2\) can fail.

## Coupled comparisons and limits

<a id="entry-228"></a>

### 228. Bounded-treewidth networks of compatible local witnesses

Take local transporter problems whose only overlap requirements are assignments to finite interface variables. Suppose each local scope is contained in a bag of a supplied constant-width tree decomposition, the interface alphabet is fixed finite, and each specified assignment on a scope has an ordinary TI local test. The existence of a compatible family has one ordinary TI comparison.

Assign each local constraint to a bag. Choose a centroid bag, disjoin over its finitely many assignments compatible with existing pins, and for each choice conjoin its tests with recursive tests on the remaining bag-tree components. Running intersection ensures that every interface shared between components is already pinned. Each root-to-leaf route is logarithmic in the number of bags with constant assignment branching, so total formula size is polynomial. Balance the resulting positive formula by separating a subformula of between roughly one third and two thirds of its size and writing its monotone context as \(C(0)\lor(Y\land C(1))\); recursively balance the subformula and both smaller contexts. Then compile the resulting logarithmic-depth positive formula using ordinary TI's AND and OR constructions.

<a id="entry-229"></a>

### 229. Polynomial-state branching with exactly one true transition

Consider a layered directed graph of polynomially many states and ordinary TI edge labels. Promise exactly one outgoing true edge at every nonterminal state. Each edge has a complementary comparison given by the disjunction of its competitors at that state. The earlier exact path-count compiler with complementary pairs therefore tests reachability of an accepting terminal in one ordinary comparison, without a hypothesis about complement TI. This allows polynomial rather than fixed interface size for the explicit layered graph. The exactly-one promise includes existence.

<a id="entry-230"></a>

### 230. Local tests with actual framed linear restrictions

In an ordinary tensor comparison, prescribe a given map on a supplied framed subspace of a mode by placing the source basis vectors and prescribed images as order-one marks on the common named mode. Dependencies can be checked before packing the typed system. Thus [Entry 228](#entry-228) applies to ordinary comparisons whose overlaps are constant-dimensional framed subspaces with actual shared restrictions, not just profiles of independent request bits. For signed local tests the fixed-field character compiler of the prior atlas handles the same typed marks under \(H\). The resulting interface compiler requires that agreement on all supplied restrictions really describes the global witness requirement.

<a id="entry-231"></a>

### 231. Affine homomorphic witness projections cannot realize a Boolean product

If a gadget's valid transporters form a coset and it exports data by a group homomorphism into an abelian group, its entire exported relation is a subgroup coset. Intersections with fixed coset conditions and homomorphic projections retain this property when nonempty. In particular the relation \(\{(x,y,xy):x,y\in\mathbb F_2\}\) cannot be exported exactly since its points \((1,0,0),(0,1,0),(0,0,0)\) have odd sum \((1,1,0)\) outside the relation. This constrains exact witness-preserving Boolean simulation in this model. The linear compiler [Entry 201](#entry-201) uses query bits that are fixed by the input comparisons, so it does not assert such an exported product of jointly unknown bits.

<a id="entry-232"></a>

### 232. Polynomial unions of affine sign relations

An explicitly given polynomial union of affine sign cosets can be handled at decision level once every local determinant profile has ordinary tests. For each coset solve its linear equations using the switch compiler, then use balanced OR across the cosets. Over the binary sign group a basis for each annihilator supplies the equations by Gaussian elimination. This permits nonaffine sign policies with efficient affine decompositions while making no claim that the combined relation is itself a homomorphic image of the output transporter.

<a id="entry-233"></a>

### 233. Dual certificates for unavailable spans

Over a fixed field, \(b\) lies outside the span of available columns \(a_i\) exactly when there is a covector \(y\) with \(y(b)=1\) and \(y(a_i)=0\) for every available column. Given complementary tests for each column, require \(y(a_i)\) to equal an auxiliary variable available only on the false rail. This compiles a separating functional to one ordinary comparison. Consequently an ordinary span decoder and its complement can both be compiled when the elementary tests have paired rails, without using a global complement hypothesis.

<a id="entry-234"></a>

### 234. Substitution of span programs by unrolling their uses

When one outer allowable coefficient is enabled by an inner span predicate with target \(t\), inline a private copy of the inner constraints with target equal to that coefficient times \(t\). If \(t\) is unreachable only the zero coefficient can satisfy the constraints. If \(t\) is reachable all coefficients can. Thus polynomial-size unfolding is sufficient for composing span programs without a complement assumption, including a fixed number of polynomial-size layers. Separate occurrences use separate coefficients, even when their availability questions are identical.

These are written proofs. The independent Lean and finite controls included with the atlas support particular steps, including the exact complementary-channel identity.
