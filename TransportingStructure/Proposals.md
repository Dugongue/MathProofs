# Twenty research proposals on transporting structure

Grochow and Qiao organized several independently motivated equivalence problems into a common complexity class. That is the standard for this list. Each proposal changes what an algorithm must find, preserve, or pay for, and gives an example or a first result that would justify studying it. The titles are provisional. The source comparisons establish precedents and scope. They are not a priority determination. [Grochow–Qiao, Part I](https://arxiv.org/abs/1907.00309)

Write `Iso(T,S)` for the set of changes of basis carrying one object to another. This set is empty or a coset of the source automorphism group. For ordinary 3-tensor isomorphism, the changes of basis are one invertible matrix per mode.

## Reductions and what they preserve

### 1. Character-Carrying Reductions

A gadget has boundary copies of the original mode spaces and auxiliary spaces. Every gadget isomorphism restricts to an original transporter. Require that its image on the boundary be exactly the transporters with a specified value of a group character, such as the product of mode determinants. Count the explicit size, arity, and largest auxiliary dimension required to realize that image from raw tensors. For an objectwise formulation, one may mark a source and target element in an auxiliary one-dimensional representation, so their ratio sets the character value.

Independent gadgets with a common boundary compose by intersection of their allowed transporter sets. Any shared original transporter lifts to each gadget independently, so it lifts to the joined system. This makes it possible to check local character mechanisms separately before compiling the combined system. The hard target is a polynomial-size construction for every raw tensor over a fixed odd finite field. For each determinant separately this would give an approach to SL-TI via one ordinary TI instance, provided the tensor-system compiler preserves the marked boundary and has polynomial overhead. In physical model comparison, the analogous requirement prevents an alignment from reversing a measured orientation. Ordinary determinant circuits alone do not establish this lifting property. [Tensor-system gadgets](https://arxiv.org/abs/1810.09219) · [Symmetric determinant circuit lower bounds](https://arxiv.org/abs/2107.10986)

### 2. Orbit-Image Decoders

Given a fixed reduction `E`, supply a total algorithm that recognizes whether a raw target object is isomorphic to any `E(x)`. On acceptance it outputs the source object and an explicit target isomorphism to its encoding. Study image recognition time separately from the source isomorphism time.

An example to build from is the existing graph encoding as a matrix space spanned by a hidden diagonal space and one adjacency matrix. In the checked informal proof, intrinsic minor equations recover the diagonal space, its multiplier algebra yields the coordinate lines, and support plus exact scale checks recover the graph. The first research target is a single efficient recognizer for a wider graph or code embedding with substantially weaker structural hypotheses. In a code or algebra database the decoder would identify when a generic solver can safely dispatch a raw instance to a specialist and return the actual basis changes. [TI-completeness reductions](https://arxiv.org/abs/1907.00309)

### 3. Transporter Indexes

Fix a source object `T`. Preprocess it into a reusable data structure supporting two query types. A target object `S` asks for one transporter or an exact rejection. A target plus a constraint asks whether any transporter in `Iso(T,S)` satisfies that constraint. Measure preprocessing time and space and the marginal query time separately. A bank of all transformed copies is a baseline.

The first useful result is a provable reduction in query time for a defined tensor class when the source has many repeated automorphism components and queries carry changing determinant constraints or anchors. A realistic benchmark is many candidate rank-metric codes against a standardized or archived reference code. Existing streaming graph canonization instead treats a sequence on a changing graph. [Streaming graph canonization](https://www.dcc.fc.up.pt/~pribeiro/pubs/COMPLENET2018.html) · [Rank-metric code equivalence](https://arxiv.org/abs/1304.0501)

### 4. Minimum Orientation Anchors

Given an ambiguity group `H`, a character `chi` to be determined, and a menu of physically observable marks, minimize the cost of selected marks subject to their common stabilizer lying in the kernel of `chi`. The remaining symmetry can be arbitrarily large. This models the cost of knowing handedness while leaving nuisance coordinates free.

There is an exact coding-theoretic test family. For `H = F_2^d`, each mark can have stabilizer the kernel of one linear form, realized by a two-point action. The selected marks determine the sign exactly when their linear forms span `chi`. Minimum number of marks is therefore minimum-weight syndrome decoding for unrestricted menus. A meaningful positive result would identify physically occurring menus or tensor-derived menus where the optimum can be found efficiently. Matching marked instruments or sensor frames is the immediate use. [Syndrome decoding hardness](https://authors.library.caltech.edu/records/aw9vs-ann16)

### 5. Condition-Bounded Orbit Comparison

For real or complex tensors, report the best attainable residual at each budget `K`, minimizing over transporters with operator norms of every mode matrix and inverse at most `K`. This keeps both amplifications and attenuations bounded. Pair this with a certificate from a readily checkable lower bound.

Even two matrices illustrate the difference. With `T = I`, `S = diag(1,epsilon)` and `0 < epsilon < K^(-2)`, the smallest achievable operator-norm residual is `K^(-2) - epsilon`. The product of the two allowed mode factors has smallest singular value at least `K^(-2)`, and two diagonal factors attain equality. A first tensor theorem should give two-sided computable residual bounds under a tractable structural hypothesis. Calibration and simulation model exchange need this boundary to distinguish a mathematically exact match from one requiring unphysical gains. [Tensor scaling and moment polytopes](https://arxiv.org/abs/1804.04739)

## Discrete symmetry and decomposition

### 6. Shared-Core Tensor Matching

Suppose each tensor is assembled from bags with private direct-sum components and a shared central block. Fix the permitted action on the shared block. For a potential match of two bags, retain the possible additive differences on that block induced by valid local transporters, after their non-core pieces have matched. In the model where the private mode maps can be chosen independently, a global transporter is exactly a perfect matching with a choice of edge labels summing to the required central difference.

For explicit edge-label sets in a finite abelian group `A`, assign independent variables to edge-label choices and compute a division-free determinant over the group algebra. The desired group coefficient contains one distinct signed monomial per valid choice. Randomized identity testing over an adequately large field gives a polynomial-time decision algorithm in the explicit input and `|A|`. Verifying a recovered matching gives a witness. The tensor frontier is to recognize such bag decompositions in arbitrary coordinates and avoid enumerating a large core group. The application is reconciling anonymous subsystems whose independently valid relabelings have to agree on a shared calibration term. [Randomized matching methods](https://ics.uci.edu/~vazirani/NSV.pdf)

### 7. Square-Zero Congruence Defects

In an algebra with involution and a stable square-zero ideal `J`, lift a self-adjoint unit `h` from the quotient. Congruence by `1 + x` for `x in J` sends the correction `v` in `h + v` to `v + x* h + h x`. Thus the exact residual space for these congruences is the self-adjoint part of `J` modulo the image of that linear map. Residue isometries act on it by affine maps, using any lifts.

In characteristic two with trivial involution, `h = 1` and `J = (epsilon)` in the dual numbers, the correction `epsilon` survives every congruence by `1 + J`. A common quotient form alone misses it. The algorithmic objective is to partition the affine action into inexpensive linear directions and a small residual orbit problem, including for isometries of structured codes over small rings. This is a congruence counterpart to extension-based classification for similarity. [Matrix similarity over length-two rings](https://arxiv.org/abs/1212.6157)

### 8. Affine Row Boundary Counting

Row `i` of a proposed transporter ranges independently over an affine space `a_i + V_i`. Supply a tree grouping the rows. At a split, let the boundary be the intersection of the linear envelopes on its two sides. Count independent row selections by recording how the span of the chosen rows meets that boundary.

For child states, linear dependence between the two chosen spans is detected by the intersection of their recorded subspaces, because every vector in both spans belongs to both child boundaries. A vector in the new boundary decomposes into child contributions that lie in their respective child boundaries. These give exact dynamic programming transitions and a `q^{O(w^2)}` state bound over a field of size `q) when all boundary dimensions are at most `w`. At a leaf one counts affine intersections with the boundary and groups the remaining nonzero choices into one state. A chain with `V_i = span(e_i,e_{i+1})` has small width although the row spaces are incomparable. This can count invertible solutions in structured matrix completion and partially fixed tensor transporters. The existing width parameter comes from subspace arrangements. The proposed research target is the affine counting and transporter application. [Branch decompositions of subspace arrangements](https://arxiv.org/abs/1711.01381)

### 9. Subnormal Anchor Extension

Given explicit groups `G,H`, a subnormal subgroup `P` of `G`, and a supplied epimorphism `P -> H`, study all extensions to `G`. Along a subnormal tower, each stage forces the next map modulo one more term of the upper central series of `H`. An element of the next group must induce the prescribed conjugation of the image of the previous group. Since that image is onto the current quotient, two elements inducing the same conjugation differ by its center.

For centerless `H` this gives a polynomial-time test for explicit Cayley tables. At each stage scan `H) for the required conjugating elements, use uniqueness, and check the resulting map's multiplication table. When the final central kernel is abelian, a next step is to compare exact affine section constraints for counting all extensions and to bound the cost for compact group presentations. In a computational group database this answers whether a correspondence already validated on a subsystem extends to the full system. [Group isomorphism and tensor search reductions](https://arxiv.org/abs/2306.16317)

### 10. Bounded-Degree Shift Compatibility

On a binary vector space, given a family of linear probe matrices `M(u,w)` and observations `b(u,w)`, require one shift map `P` satisfying `P(0)=0` and `M(u,w)(P(z+w)+P(z))=b(u,w)` for all `u,z,w`. For bounded probe and shift degrees and inputs given by Boolean polynomial coefficients, represent `P` with unknown coefficients. Multiply and reduce by the Boolean relations, then equate coefficients. This gives a polynomial-size linear system and exact infeasibility certificates, with no enumeration of all observations.

For a scalar probe equal to one, observations at two basis vectors and their sum can prescribe differences 0, 0, and 1. Each shift is separately achievable, and no common shift map satisfies all three. This is a way to verify correlated adjustments to families of binary models stored as sparse formulas. Our colored-group shear examples suggest one TI-related application. The open challenge is to recover both the shear ansatz and the small degree from raw tensors. Cellular sheaves give the general linear consistency precedent. The additional resource here is the succinct description by low-degree coefficients. [Cellular sheaves](https://arxiv.org/abs/1808.01513) · [Grochow–Levet's pebble games](https://arxiv.org/abs/2209.13725)

## Measurement and imperfect data

### 11. Minimum-Cost Sign-and-Amplitude Masks

Assume that diagonal gains act on a tensor of known nonzero support. Include one row per supported entry, with an incidence column for each gain. For the observed entries to determine all gain ratios on the support, their incidence rows must span the full support row space over both the rationals and the two-element field. Log magnitudes give the first requirement and sign bits give the second. Minimize the total cost of the observations.

After contracting the already observed rows, chosen rows span both matroids exactly when the omitted rows are independent in both dual matroids. Weighted matroid intersection therefore finds the optimum. In a binary cube the mask with entries 000, 011, 101, and 110 determines all positive ratios. Flipping the second-level signs in all three modes leaves the mask unchanged and flips every omitted ratio. This gives a sensor placement or tensor completion criterion once the diagonal action is exposed. In TI it suggests a route from recovered coordinates to optimal extra measurements. Conditioning and sign error resilience add separate resource questions. [Rank-one tensor completion](https://arxiv.org/abs/1605.01678) · [Verified matroid intersection](https://drops.dagstuhl.de/storage/00lipics/lipics-vol352-itp2025/html/LIPIcs.ITP.2025.2/LIPIcs.ITP.2025.2.html)

### 12. Odd-Cycle Cross-Calibration

With invertible cross-view measurements `M_ij = A_i A_j^T` on a connected sensor graph, take an alternating product of edge blocks and reversed inverse blocks around an odd cycle. At its root the product equals `A_i A_i^T`. Recover a root factor and propagate it along the graph, checking all edges. The remaining simultaneous transformations are one common orthogonal matrix. A bipartite graph instead admits an arbitrary invertible change on one side and its inverse transpose on the other.

The immediate design decision is which new measurement will close an odd cycle, and which available cycle gives the best noise conditioning. In tensor alignment with these cross-view observations, this reduces general linear gauges to a shared orthogonal gauge. The first deeper result should treat also missing, singular or noisy cross-view measurements with provable recovery bounds. [Multiview whitening](https://jmlr.org/papers/v15/anandkumar14b.html)

### 13. Character Certificates for Inconsistent Alignments

Let each edge of a network of partially aligned models require the relative gauge difference to lie in a coset `t_e + H_e` of a finite abelian group. Exact synchronization means solving all these constraints simultaneously. Use Smith normal form for decision and recovery. A certificate of failure is an edge character in each quotient by `H_e`, with signed incident products trivial at all vertices, whose product evaluated on the edge offsets is nontrivial.

The certificate follows by dualizing the image of the incidence map into the product of quotient groups. In a theta graph, three paths can require `x=0`, `y=0`, and `x+y=1` respectively. Each pair is compatible and the full system is inconsistent. This is a diagnostic for phase-ambiguous distributed instruments. For TI the relevant question is whether local transporter characters and their subgroup images can be computed cheaply enough to construct these certificates on raw inputs. The underlying cokernel is a special case of cellular sheaf synchronization. [Cellular sheaves](https://arxiv.org/abs/1808.01513) · [Synchronization and holonomy](https://arxiv.org/abs/1610.09051)

### 14. First-Variation Transporter Classes

Compare two fitted tensors that vary with a parameter. Over the dual numbers, fix a transporter at parameter zero. The change in its first-order adjustment ranges through the image of the Lie algebra acting on the fitted base tensor. The first-order terms must therefore agree in the normal-space quotient after the permitted base stabilizer action. Testing an individually prescribed base transporter is one linear solve.

The matrices `diag(1,t)` and `diag(1,t^2)` are equivalent at every real parameter value, including zero, but fail the first-order comparison at zero. The tangent image at `diag(1,0)` misses the lower-right entry. This distinguishes two swept-parameter models whose pointwise alignment cannot extend smoothly through calibration loss. The research target is exact algorithms across multiple parameter levels, with a concise description of the base transporters that lift. The first-order calculation is standard deformation theory. [Tensor isomorphism over commutative rings](https://arxiv.org/abs/2611.00735)

### 15. Protected-Copy Rank Decoding

Repeat a tensor on the labeled diagonal blocks of two modes, sharing the third mode. Protect the copy structure by supplying the matrix-unit operators on the copy indices. Allow arbitrary simultaneous additive error of flattening rank at most `r` and arbitrary basis changes applied jointly to the data and the protected operators. With `m >= 2r+1` copies there is deterministic exact decoding to the original tensor in the recovered base coordinates.

To decode, recover compatible bases for the copy spaces by applying the operators `P_i1` to a basis for `im P_11`. Each individual clean entry `a` then appears as a block `a I_m` on its repeated row and column copies. Write the corrupted block as `Y = a I_m + E`, where `rank(E) <= r`. At least `m-r` invariant factors of `xI-Y` contain `x-a`, as its eigenspace has dimension at least `m-r`. For every other eigenvalue the eigenvectors lie in the image of `E`, so its geometric multiplicity is at most `r`. Therefore the `(r+1)`st invariant factor in increasing divisibility order is `x-a`. If its exponent were two or more, the invariant factors would have total degree exceeding `m`. At `m <= 2r`, a suitable diagonal matrix with zeros and ones is within rank `r` of both zero and the identity, so the threshold is sharp in this model.

This protects multi-trial data when a common low-dimensional interference term can be large. The TI connection is an exact wrapper that decodes two observations before comparing them. The application assumes reliable structural markers and a joint rank bound, which should be measured on actual calibration data. [Rank-metric error control](https://arxiv.org/abs/0711.0708)

## Algebraic resources for verification and search

### 16. Frobenius Spectra of Transporters

For each determinant value over a fixed finite field, record the degrees of the extensions over which an exact transporter exists with that value. On a nonempty geometric transporter fiber, Frobenius permutes its geometric connected components. The allowed degrees are the union of the sets of multiples of the cycle lengths. Indeed, a rational point must lie in a fixed component, and a fixed component is a torsor under a connected smooth group, so Lang's theorem supplies a point. One can use the reduced geometric subgroup over the perfect finite field for the point-set statement.

The model already distinguishes a square root of a nonsquare, whose extension spectrum consists of the even degrees. An algorithm that extracts the component action for structured tensor stabilizers would predict the smallest field supporting a valid alignment, which is relevant to changing the field of a code or a symbolic computation. This is a computational use of classical descent. The problem of finding a compact presentation of the components is substantive. [Lang's theorem](https://doi.org/10.2307/2372673) · [An algorithm for connected Lang maps](https://arxiv.org/abs/math/0506068)

### 17. Pole Budgets for Transport Certificates

Given a proposed parameterized transporter with entries in the function field of a smooth projective curve, use pole divisors to budget how many Taylor coefficients verify all identities of a prescribed degree. For entries bounded by the pole divisor `D`, a nonzero polynomial expression of degree at most `b` has pole degree at most `b deg(D)`. Its order of vanishing at any rational regular point cannot be larger, by equality of the degrees of zeros and poles.

The research problem is to find low-pole witness models and matching lower bounds in families of tensors, and to measure whether this beats expanding rational-function numerators. A supplied symbolic calibration or change of coordinates can already use the underlying bound. Its relevance to TI is a finite verification strategy once a proposed structured transporter and its pole budget are available. [Function-field valuations and divisors](https://stacks.math.columbia.edu/tag/02RS)

### 18. Divisor Spacing of Algebraic Oracles

For a decoder using succinct rational-function answers, treat the products of those answers that occur in its expansion as projective monomials. Inspect their pairwise differences in valuations at irreducible divisors. The minimum nonzero difference measures how hard it is for low-degree coefficients to cancel genuinely distinct products.

One starting point is a characteristic-zero univariate Wronskian bound. In a minimal relation on `r` distinct rational-function products with polynomial coefficient degrees at most `B`, clear common denominators and divide out the common gcd of the products. If the remaining products have maximum degree `D`, every nonzero valuation of a product is at least the spacing `s`. The Wronskian omitting any one term is the same up to nonzero scalar. At a prime choose an omitted term whose product has valuation zero there and bound the derivative loss by `r-2` per vanishing product. Comparing degrees gives `D <= r(r-2)D/s + (r-1)B`. Distinct projective products give `D >= s`, so `s > r(r-2)+(r-1)B` excludes the relation. The proposed use is a quantitative audit of attempted algebraic reductions that rely on cancellation or on hiding a root in successive queries. Turning this into a new TI algorithm requires an explicit small useful encoding. [Algebraic oracle reductions](https://arxiv.org/abs/2112.00792)

### 19. Ordered Specialization Certificates

For a finite list of rational-function matrices, scalar inequalities, and equalities over the rationals, look for one explicitly described Kronecker specialization preserving the required signs and zeros of all designated tests. For positive lexicographically separated infinite parameters, signs are leading-term signs. Pick exponents that separate the bounded monomials and a base large enough that the leading term dominates after denominators are cleared.

For a symmetric matrix the characteristic-coefficient signs suffice to preserve inertia. After removing zero roots, apply Descartes' bounds to the polynomial and to its variable negation, adjusted by the leading sign. All roots are real in the real closure, so the two upper bounds sum to the polynomial's degree and are exact. A practical target is verification of simultaneous covariance, positivity, matrix-rank, and gauge constraints from circuit representations without materializing large evaluated constants. Bit-size bounds for supplied circuit families and actual verifier speed remain research questions. [Noncommutative optimization and quantitative specialization context](https://arxiv.org/abs/1910.12375)

### 20. Algebraic Degree of a Transporter

For isomorphic inputs defined over a field `F`, measure the minimum degree of an extension that contains every coordinate of one exact transporter. More broadly, ask for the minimum size of a symbolic representation of one witness and distinguish it from the degree of the common field. This is a resource for exact search even when a decision oracle is free.

There is a factorial example for ordinary side-`m` tensor isomorphism. Choose distinct real numbers `r_1,...,r_m` algebraically independent over a fixed field of machine constants. Let `F` contain the constants and the elementary symmetric functions of the roots, with no further generators. Put `P(X) = product (X-r_i)`. Compare the multiplication tensors of `F[X]/(P)` and `F^m`. Both become isomorphic over the reals. If the three mode maps form an isotopy with `h(xy)=f(x)g(y)`, then `f(1)` and `g(1)` are units by bijectivity, and dividing `h` by their product gives an algebra isomorphism. The image of the source generator then has `m` distinct coordinates, since it generates the split algebra. Those coordinates are precisely the roots of `P`. Thus any field containing a transporter contains the splitting field. Its degree is `m!` by the symmetric group permuting the independent roots and the standard upper bound for a splitting field. Evaluation at the roots attains this degree.

On this family, exact TI search and outputting all roots of a split squarefree polynomial reduce to one another by field operations. Deciding if the source is split is polynomial-time in real field operations with comparisons. Test positive definiteness of the trace form `(x,y) -> Tr(m_xy)` via its Gram matrix. Nilpotents lie in its radical, a complex factor contributes the indefinite quadratic form `2 Re(z^2)`, and a real factor contributes a square. A real machine with only field operations and yes/no oracles cannot always output the coordinates from the coefficients, even with an ordinary TI decision oracle. A symbolic solver can still use a compact polynomial and isolating data. This makes the candidate a benchmark for exact algebra software and a precise question about the output contract of TI search-to-decision reductions. The normalization of unital algebra isotopies and the splitting-field facts are classical. The proposed contribution is measuring and separating these resources on explicit ordinary TI instances. [TI and real computation models](https://arxiv.org/html/2306.03135v2#S2) · [Hermite matrices](https://arxiv.org/abs/2110.10313) · [Computability over the reals](https://arxiv.org/abs/1105.1380) · [Albert on isotopy](https://doi.org/10.2307/1968960)

## Which programs can earn a name?

Transporter-preserving reductions have the broadest unifying target. The first paper should show what happens to actual witness sets under reductions between at least two of groups, tensors, and matrix codes, prove a composition or tradeoff theorem, and produce a size or runtime gain on a meaningful family. Character-Carrying Reductions, Orbit-Image Decoders, and Shared-Core Tensor Matching are the most directly relevant pieces.

Algebraic Degree of a Transporter makes the strongest immediate theoretical case on its own. It separates a decision answer, exact coordinates, and symbolic witnesses on an explicit 3-tensor family. Protected-Copy Rank Decoding and Minimum-Cost Sign-and-Amplitude Masks give the strongest immediate experiments. The former warrants testing whether interference really has low joint flattening rank. The latter has a concrete optimum for the strict observation model and can be compared with designs built using real-valued rank alone. The names and proofs in this note are informal. A new use of a classical tool is credited as such.
