# Exact tensor network descent over coefficient rings

Ten informal theorems growing out of the MathProofs tensor-rank-to-circuit bridge. The main algorithm starts with compressed input over a rational-function field and returns polynomial cores of minimum width on the same tree. The rank guarantee holds separately at every edge.

## Setup

Let R be a commutative integral domain and K its fraction field. A finite tree has a nonempty finite alphabet A_v at each vertex v. Each edge e carries a finite free internal index of size w_e. For a label a in A_v the core at v is a tensor with one index per incident edge. Summing products of core entries over internal indices defines a coefficient tensor T on the product of the physical alphabets. A chain is a tensor train. An internal vertex can have a singleton alphabet, so the convention includes ordinary leaf-labeled tree networks.

We take T nonzero, allowing an arbitrary all-zero realization when T is zero. For each oriented edge choose one side X and the other Y. Here X and Y also denote the sets of physical assignments on the respective sides. The rows of the cut matrix are the vectors T(y,·) in R^X. Write L_X for their R-span, U_X for their K-span, S_X = U_X ∩ R^X for the saturation, and r_e = dim_K U_X for the cut rank. The rank is unchanged by reversing the edge. Root the tree and use the descendant side as X at each edge.

Every realization factors each cut matrix through the free module on its edge index. Thus w_e ≥ r_e. In particular, simultaneous attainment of the r_e gives componentwise minimum widths.

If x_(v,a) are physical variables, the polynomial associated to T is the sum over all labelings a of T(a) times the product of x_(v,a_v). To evaluate it, multiply the local cores by their physical variables and sum over the physical label. Contract the resulting tree from the leaves. Each vertex contraction costs at most a constant times |A_v| times the product of its incident widths times (1 + degree(v)) scalar arithmetic operations. This follows by enumerating the local index tuples and multiplying the child messages, accumulating into the outgoing vector. This replaces the single large CP rank cost in candidate #71 by local products of widths. A path gives an ordered algebraic branching program.

## 1. The exact rank factorization criterion at one cut

**Theorem.** A matrix M over R of fraction-field rank r admits a factorization M = AB with inner width r if and only if its row lattice L and saturation S contain an intermediate free lattice W of rank r, with L ⊆ W ⊆ S. If L = S, such a factorization exists exactly when S is free.

**Proof.** In a width-r factorization both factors have rank r over K. The rows of B are therefore independent over K and span the same K-space as the rows of M. Their R-span is the required W. Conversely take a basis of W for the rows of B and put the R-coordinates of the rows of M into A. When L = S the sandwich has only one choice.

## 2. Matrix descent implies simultaneous descent on every tree

**Theorem.** For a Noetherian normal domain R the following are equivalent.

1. Every finite matrix over R admits a factorization of inner width equal to its K-rank.
2. Every saturated submodule of a finite free R-module is free.
3. Every finite R-valued tensor on every specified tree has a realization over R at all its fraction-field cut ranks simultaneously.

**Proof.** For (1) ⇒ (2), take a matrix whose rows generate the saturated submodule. Noetherianity gives a finite set of generators and Theorem 1 forces its row saturation to be free. A tree with two vertices gives (3) ⇒ (1). It remains to construct the realization for (2) ⇒ (3).

We use a slightly stronger module statement for later use. Suppose each S_X for the descendant cuts in question is finite projective. When X is a descendant component below a vertex v, let its child components be X_1,…,X_k. Over K we have
```
U_X ⊆ K^(A_v) ⊗ U_(X_1) ⊗ ... ⊗ U_(X_k).
```
For each child, the definition of the cut span places T in U_(X_j) tensored with the whole complementary coordinate space. Choose K-linear complements in the child factors. The decomposition into the resulting direct sums shows that intersecting the child conditions imposes every child factor at once. Taking the slices outside X gives the displayed inclusion. At the root the same argument applies to T itself.

Put P = R^(A_v) ⊗ S_(X_1) ⊗ ... ⊗ S_(X_k), embedded in the full free physical coordinate module F_X. The embedding is injective because the factors and the ambient coordinate modules are flat. In fact P is saturated. At every height-one prime p of R the ring R_p is a DVR. Each localized S_(X_j) is saturated in its ambient free module and hence is a direct summand there, since the quotient is a finitely generated torsion-free module over a PID. Tensoring their decompositions shows P_p = (P ⊗ K) ∩ (F_X)_p. A finite projective module is the intersection of its height-one localizations inside its K-span. To see this, embed it as a direct summand of a free module and apply R = ∩ R_p coordinatewise, then apply its idempotent projector. These facts give P = (P ⊗ K) ∩ F_X. If R is a field the saturation assertion holds directly.

It follows that the inclusion over K restricts to a map S_X → P over R, and at the root T lies in the tensor product of the root physical coordinates and the child modules. These maps compose to the original inclusion into the physical tensor space. Under (2) all the S_X have bases. Writing the maps and the root vector in those bases gives the cores, of widths r_e. This proof also gives a projective state module realization when the S_X are projective but nonfree.

## 3. Two coefficient parameters suffice for exact tree descent

**Theorem.** Over k[s,t], for every field k, an arbitrary polynomial coefficient tensor has a denominator-free tree network at every minimum k(s,t) edge width on the same tree. The same conclusion holds over every PID, including Z and k[s].

**Proof.** For k[s,t], let S be a saturated submodule of R^n. The quotient R^n/S is finitely generated torsion-free and embeds into some R^m by choosing fraction-field coordinates and clearing denominators. Thus S is the kernel of a map between two finite free modules. Since k[s,t] has global dimension at most two, such a kernel is projective. For example, dimension shifting in 0 → S → R^n → R^m → C → 0 identifies Ext^1(S,−) with Ext^3(C,−), which vanishes. Quillen–Suslin gives freeness. Apply Theorem 2. For a PID the submodule S is free by the module structure theorem.

This extends the matrix rank-factorization theorem of Cohn to simultaneous tree widths. Cohn's matrix result already implies the conclusion when the tree has two vertices.

## 4. Homogeneous descent preserves the total parameter degree

**Theorem.** In Theorem 3 over k[s,t], suppose every nonzero entry of T is homogeneous of one total degree D. Assign each internal edge basis state a weight between 0 and D. One can realize T at all the minimum widths so that every nonzero core entry at a nonroot vertex is homogeneous of degree
```
weight of its outgoing state − sum of the weights of its child states.
```
At the root use D in place of the outgoing weight. In particular all nonzero core entries have degree at most D and every nonzero product in the contraction has total degree D.

**Proof.** At a cut take r independent homogeneous rows of degree D from T. Choose a nonzero r-by-r column minor. Solving for the other coordinates of a vector in their span by the adjugate gives linear equations whose coefficients are homogeneous of degree rD. Thus S is graded. It is free by Theorem 3. Lift a homogeneous k-basis of S/(s,t)S to homogeneous elements. Graded Nakayama shows that they generate. Their number is r, since the underlying ungraded module is free of rank r. The resulting surjection from a graded free module of rank r has kernel zero after tensoring with K, and that kernel is torsion-free. These lifts are a homogeneous basis. All have degree at most D. Otherwise the homogeneous rows of degree D would have zero coordinates in a higher-degree basis direction, contradicting that the rows span after tensoring with K.

Use these bases in the construction of Theorem 2. The inclusion maps preserve total degree in physical coordinates. Uniqueness of a graded basis expansion gives the asserted degree of each coefficient. The degree sum along each contracted product telescopes to D. The argument includes D = 0 and vertices with no children.

## 5. Minimum-width homogeneous descent in polynomial time from compressed input

**Theorem.** The input is a tree with explicit dense local cores over k(s,t), each scalar given by a pair of dense bivariate polynomials with nonzero denominator. There is a deterministic algorithm using polynomially many field operations in this compressed input size which does the following.

- It detects the zero tensor.
- It decides whether the tensor has entries in k[s,t] that are all zero or homogeneous of one common degree D.
- In that case it returns a tree realization over k[s,t] with exactly the K-rank at every edge, all degrees and weights as in Theorem 4.

For k = Q the algorithm has polynomial bit complexity in the dense binary input encoding. A vertex may have arbitrary degree. The algorithm never expands the full physical tensor.

**Proof.** Multiply each core by the product of its entry denominators, obtaining polynomial cores. Their contraction is Q T, where Q is the product of all the local denominators. Let E be the sum of the maximum total degrees of the cleared cores, with the maximum taken over nonzero entries and zero used for an all-zero core. Q and all partial products have degree polynomial in the input. We use polynomials of degree at most E as coefficient vectors over k.

**Compressed side messages.** For an oriented edge, the message of a physical assignment on its side is the w_e-vector obtained by contracting the cleared cores on that side, leaving the edge index open. Find a k-basis of all such messages consisting of actual assignment messages. At a vertex, fix a physical label and begin with its cleared local tensor. For each incoming edge in turn contract it with each basis message for that edge. At each step retain an independent subset of resulting coefficient vectors over k. All partial assignments in different components can be combined independently. Multilinearity shows inductively that the retained list spans precisely the partial messages for the fixed label. Take the span across labels at the end. Every retained vector comes with a physical assignment, because elimination only selects representatives. Two sweeps compute both orientations of all edges. The same operation at the root with no outgoing edge gives a basis of the scalar numerator polynomials for all full assignments.

The local intermediate tensor has at most as many entries as the explicitly supplied core. Its polynomials have degree ≤ E. Therefore the number of retained partial vectors at every step, and the cost of the next contraction and span computation, are polynomial, even at vertices of unbounded degree. The test for zero is that the final scalar span has dimension zero.

**Checking the coefficient promise.** For each nonzero basis numerator N at the root, test N = Qh for a homogeneous polynomial h. The only possible degree is deg N − deg Q, by degree additivity in the domain. Test divisibility and homogeneity by coefficient comparison in that homogeneous space. Require all these degrees to agree. The scalar numerator span uses k-linear combinations, so success is equivalent to the assertion for every physical coefficient. Failure is witnessed by one or two full assignments from the basis. If successful, D ≤ E.

**Short coordinate space at a cut.** For the descendant side X, use the assignments b_1,…,b_m whose messages span all X messages over k. Restricting a slice to these coordinates identifies U_X with a subspace of K^m. For each X-assignment b, its message is a k-linear combination of these m messages. The same linear combination recovers evaluation at b for every vector of U_X. Hence restriction is injective, and integrality and homogeneity are equivalent to those of the short coordinate vector. In particular it identifies S_X with U_short ∩ R^m, where R = k[s,t]. The opposite message basis supplies enough actual rows to span U_short over K. Their entries are dot products of the two messages divided by the same Q, and can be computed by the exact polynomial division already justified by the promise test.

**Computing short bases.** In the small row matrix find a maximal nonzero minor with independent rows and columns. This can be done by starting with an empty minor and testing all one-row one-column extensions of the current nonzero minor. The Schur complement over K proves that there is a nonzero extension unless the current rank is maximal. Determinants can be computed by division-free characteristic-polynomial arithmetic, for example Berkowitz, using dense bivariate polynomials of polynomial degree. The same adjugate equations as in Theorem 4 describe the short saturation. For each j ≤ D solve the linear system obtained by asking for homogeneous coordinates of degree j and comparing coefficients. In degree j select a complement of s S_(j−1) + t S_(j−1) in S_j, using S_(−1) = 0. These complements give precisely the homogeneous basis constructed in Theorem 4. Compute each kernel S_j from the original equations, rather than by iterating substitutions through previously computed bases.

**Recovering the cores.** For each child module select r_e sample coordinates on which its r_e basis elements form an invertible matrix over K. For a fixed physical label at the parent, take the Cartesian product of those sample sets across the children. Its size is the product of the r_e, at most the number of internal index tuples in the input core at this vertex. Evaluate the parent basis vector at each of those assignments by expressing the resulting actual message in its own short side message basis. At the root evaluate T directly by contracting the input for each such assignment. The equations for the output core coefficients on these samples are injective over K because the product of the child evaluation matrices is their invertible tensor product. Theorems 2 and 4 give a solution with each coefficient homogeneous of its prescribed degree. Find it by coefficient comparison over k. This both produces and uniquely specifies the output cores. Equality for all assignments follows from the module realization, with the sample equations used only to recover its coefficients.

For the bit bound over Q, a common integer denominator for the input scalars' rational coefficients has bit length at most the total input coefficient bit length. Products and sums in an actual partial assignment message have polynomial height. More explicitly, after clearing the coefficient denominators, every numerator coefficient is a sum of products of at most one entry per vertex. The logarithm of the number of terms is bounded by the sum of the logarithms of the internal widths and the logarithms of the monomial counts at the vertices. Products, determinant coefficients, and linear systems in the algorithm therefore have polynomial dimension, degree and coefficient bit length. Exact rational linear algebra, with fraction-free elimination or minor bounds, gives polynomial bit complexity for each system. The span routines keep original messages. Short kernel bases and all local recovery systems are formed from input messages and independent kernel computations, so bit bounds do not recurse through output cores along the tree. This completes the polynomial bound in the compressed encoding.

## 6. The threshold fails over three parameters at width two

**Theorem.** For every field k and every m ≥ 3 there is a polynomial tensor over k[s,t,u,…] on a two-vertex tree whose fraction-field width is 2 and whose minimum polynomial width is 3. It can be placed across any specified edge by using singleton alphabets and identity cores elsewhere. All its specialized field matrices have rank at most 2.

**Proof.** Use the classical Cohn matrix
```
[  0   u  -t ]
[ -u   0   s ]
[  t  -s   0 ].
```
It has rank 2 over the fraction field, and its rows generate the kernel of the functional with coordinate vector (s,t,u), by exactness of the Koszul complex on the regular sequence s,t,u. The kernel is saturated because its quotient embeds in the domain. At the maximal ideal generated by the parameters it needs three generators. Indeed the Koszul presentation of this kernel has three generators and the next differential has entries in that maximal ideal. Reduction of the presentation modulo the maximal ideal gives a three-dimensional vector space. Thus it is not free of rank 2. Theorem 1 rules out width 2, and the factorization through the full three-coordinate space gives width 3. The determinant vanishes identically, which gives the specialized field claim. The example and obstruction at matrix size three are classical. The transfer applies them to tree edges and to any arbitrary-order chain by insertion of singleton modes.

## 7. Dedekind domains cost at most one extra state per edge

**Theorem.** Over any Dedekind domain, every tensor on any tree has a realization using free edge indices of widths at most r_e+1. At every edge with free saturation, width r_e can be used in the same realization. Here the cores have entries in R and each index is an ordinary finite free index.

**Proof.** The saturations are finitely generated torsion-free, hence projective. Theorem 2 gives the projective module realization. The Steinitz classification writes a rank-r projective module S as R^(r−1) ⊕ I for an invertible ideal I up to isomorphism. Thus S ⊕ I^(-1) is free of rank r+1. For free S use S directly. In each case let F_e be the chosen free module, with inclusion S_e → F_e and projection F_e → S_e composing to the identity. Precompose the projective map at each nonroot vertex with the projection for its outgoing edge and postcompose its child factors with the respective inclusions. The root uses just the inclusions. The projections cancel the inclusions in contraction, so the output remains T. Choosing bases of the F_e yields the claimed widths.

## 8. Exact class-group test for minimum width in the matrix case

**Theorem.** For a nonzero matrix over a Dedekind domain let L ⊆ S be its row lattice and saturation. For each nonzero prime ideal p let m_p = length_(R_p)((S/L)_p). Its minimum inner width is r if and only if there are integers 0 ≤ e_p ≤ m_p with
```
[det S] · product_p [p]^(e_p) = 1
```
in the ideal class group. Otherwise its minimum inner width is r+1.

**Proof.** A free intermediate W exists exactly when there is an intermediate W whose determinant has trivial ideal class, by Steinitz. At p the index of W_p in S_p has some length e_p between 0 and m_p. Smith normal form over the DVR gives det W_p = p^(e_p) det S_p as lattices. Conversely a composition series of the finite-length module (S/L)_p has submodules of every possible length. The torsion module S/L splits into its finitely many primary components, so one may choose the local index lengths independently and take the inverse image of the resulting submodule of S/L. This constructs every listed determinant class. Apply Theorem 1 for width r and Theorem 7 for the upper bound r+1.

For example, if the nonzero prime factors and their classes are supplied, the condition is a finite group computation over the indicated intervals. This is a characterization and does not assume a polynomial-time ideal factorization algorithm.

## 9. Primitive cuts have an exact width profile and periodic stabilization

**Theorem.** Call a descendant cut primitive if L_X = S_X. If all cuts of a tree tensor over a Dedekind domain are primitive, there is a simultaneous minimum free width profile
```
w_e = r_e + 1 if [det S_X] ≠ 1, and r_e otherwise.
```
For the block direct sum of k copies on the same tree, with disjoint labels at every vertex and nonzero entries allowed only for uniform copy labels, the minimum profile is k r_e plus 1 exactly at edges where [det S_X]^k ≠ 1.

**Proof.** At a primitive cut Theorem 1 rules out width r_e if the saturation is nonfree, and a cut in any realization gives the necessary matrix factorization. Theorem 7 attains every lower bound simultaneously. A block sum of copies has block diagonal cut matrices after ignoring the all-zero rows and columns from mixed copy labels. Both the row lattice and its saturation are direct sums, so primitivity persists, ranks add, and determinant classes multiply. Apply the first part.

An explicit sharp example uses R = Z[a], a² = −5, its quadratic integer ring, and I = (2,1+a). The quotient R/I has two elements. A principal ideal of that norm would require an integer solution of x²+5y²=2, which does not exist. Moreover I²=(2), as follows from its generators 4, 2(1+a), and −4+2a. Let u = (2,1+a) and v = (1,(1+a)/2). Their entries generate I and I^(-1) respectively, so the integral matrix u^T v has row lattice I v. Its saturation is also I v since λ v is integral exactly when λ lies in I. One copy has rank 1 and needs width 2. Two copies have rank 2 and admit width 2. Concretely, the columns of the matrix
```
[ 2      1+a ]
[ 1+a    a−1 ]
```
lie in I ⊕ I and form an R-basis of it. The determinant is 2 and the inverse has entries in I^(-1), proving the basis assertion. The example extends along chains by inserting identity cores.

## 10. A small prime preserving every integer tree width

**Theorem.** Given a nonzero integer tensor in explicit dense tree network format, one can deterministically find a prime p of magnitude polynomial in the input bit length such that every cut rank over F_p equals its rank over Q. The algorithm runs in polynomial bit time in the compressed encoding and outputs a nonvanishing minor witness for each cut. All but at most floor(log₂ |Δ|) primes work, where Δ is the product of the chosen nonzero integer minors, including one nonzero tensor entry to certify nonzeroness even for a one-vertex tree.

**Proof.** Use the side message basis algorithm of Theorem 5 over Q with coefficient degree zero, keeping actual integer assignment vectors. At a cut, the dot products of opposite basis messages give a small matrix having the full cut rank. Indeed all actual rows and columns are generated by these messages over Q. Gaussian elimination chooses a square minor of size r_e with nonzero determinant in this matrix. The selected assignments make it an actual minor of the full tensor flattening. The scalar message algorithm also finds a nonzero actual entry.

Every higher-size integer minor vanishes already over Z and so still vanishes after reduction. A prime not dividing Δ preserves the lower bound simultaneously via the chosen witnesses. The bit length of Δ is polynomial by the actual-message height bound from Theorem 5 and Hadamard's bound on determinants. A nonzero integer has at most floor(log₂ |Δ|) distinct prime divisors. Sieve the first 1+floor(log₂ |Δ|) primes, whose largest is polynomial in that count by the standard upper bound on the nth prime, and take the first that does not divide Δ. Integer arithmetic, sieve, and all rank tests take polynomial bit time. By Theorem 3 over Z a minimum-width integer realization exists. Its specialization at the chosen prime is minimum-width over F_p at every edge.

## Attribution and scope

The source crossover joins the tensor rank ceiling to arithmetic evaluation in MathProofs, Candidate 71. The relevant project declarations are `DTensorRankCeiling20260902.hasRankLEd_pow` and `DTensorVPBridge20260902.circuitComplexity_multilin_le`. The new comparison is between a global rank-one decomposition and the collection of edge ranks on a specified tree. The latter can give polynomial arithmetic evaluation for bounded-degree trees with polynomial bond widths, even when the global rank bound from Candidate 71 is exponential. This is a sufficient structured-input criterion.

- P. M. Cohn, [Free Ideal Rings and Localization in General Rings](https://webhomes.maths.ed.ac.uk/~v1ranick/papers/cohnfr.pdf), Section 5.5 and Corollary 5.5.5, establishes the two-variable matrix case and gives the three-variable matrix counterexample.
- J. Jovcheva, T. Seynnaeve and N. Vannieuwenhoven, [Minimality of Tree Tensor Network Ranks](https://arxiv.org/abs/2509.09463), give the field setting for tree network ranks. R. Vilmart, [A Unique Normal Form for Tensor Trains over Arbitrary Fields](https://arxiv.org/abs/2607.06271), gives polynomial-time normalization over fields.
- Q. Aristote, S. van Gool, D. Petrişan and M. Shirmohammadi, [Learning Weighted Automata over Number Rings](https://arxiv.org/abs/2504.16596), develop module realizations and number-ring automata algorithms. These are close prior work for the chain and projective-state ideas.
- T. Cortadellas Benitez, C. D'Andrea and E. Montoro, [Bounds for degrees of syzygies of polynomials defining a grade two ideal](https://arxiv.org/abs/2012.08137), give relevant effective Quillen–Suslin context. The homogeneous construction here uses bounded linear systems instead of a general effective Quillen–Suslin algorithm.

The most distinctive claim is Theorem 5, which combines exact polynomial-ring descent, degree control and compressed input. The literature check located the matrix theorem and the field network algorithms. Priority for their tree and compressed homogeneous combination is provisional. These proofs are informal. The claims concern a specified tree, dense core encoding, exact coefficient arithmetic, and the stated rings.
