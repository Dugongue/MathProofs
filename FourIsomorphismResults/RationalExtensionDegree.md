# The least number-field degree for tensor isomorphism is NP-hard

For two explicit three-tensors T and S over Q, write d_min(T,S) for the least degree of a number field K over Q such that T and S are ordinarily isomorphic over K, and set this value to infinity when there is no such field. Ordinary isomorphism permits three independent invertible linear maps. We prove the following results.

1. Given T, S and a bound D in binary, deciding d_min(T,S) ≤ D is NP-hard. The reduction always produces pairs isomorphic over a finite real extension of Q.
2. On a polynomial-time recognizable family of canonical raw inputs, the decision problem is NP-complete. On that same family, deciding whether **some** real number field of a specified binary degree d works is deterministic polynomial time, without constructing the field.
3. For a fixed ε > 0, approximating the finite minimum degree within 2^(L^ε) is NP-hard, where L is the binary length of the input tensors, on the same family. This applies even to estimates allowed a multiplicative error in both directions.

The proof also gives an exact extension spectrum. Given a graph G and arbitrary pairwise coprime integers m_i > 1 written in binary, there is a polynomial-time construction of a tensor pair for which degree d is possible exactly when the vertices with m_i dividing d form a vertex cover. When such a degree is possible, the real pure radical field Q(2^(1/d)) works. Graph encoding, elementary tensor gates and pure radicals serve different roles. Only the selection of the degree is hard on the constructed family. Proof status is informal and publication priority is unverified. The finite-field analogue for recognizable tensors is already in the earlier MathProofs descent work.

## 1. Succinct power equations as tensor isomorphism

For m ≥ 1, choose a strict addition chain 1 = m_0, ..., m_R = m, where m_j = m_a + m_b for indices a,b < j. Binary doubling and adding 1 gives R = O(log(1+m)). We use a constant signature of vector spaces and multilinear maps over Q. In the system put the following objects.

- A scalar line Q with its multiplication. Its invertible linear automorphism is necessarily the identity.
- The coordinate algebra A = Q^(R+1) with its multiplication and a linear map N with N(e_j) = e_(j+1) for j < R and N(e_R) = 0, where e_j are its coordinate idempotents.
- The module V = Q^(R+1) with coordinate action of A and basis v_0, ..., v_R.
- The bilinear map B from V × V to V whose j-th output coordinate for j ≥ 1 is x_a y_b for the chosen addition-chain pair a,b. Its zeroth output coordinate is zero.
- A linear map from the scalar line to V, sending 1 to v_R in the source and to 2v_R in the target.

Use the same tensors of all other maps. Over every extension field K of Q, an automorphism of A_K permutes its primitive coordinate idempotents. Commutation with the directed shift N fixes the sole terminal vertex and its predecessors, so the action on A is identity. The action on V is then diagonal, with nonzero multipliers u_j. Preservation of B requires u_j = u_a u_b. Preservation of the last map requires u_R = 2. Induction down the chain shows equivalence to u_0^m = 2. Conversely such a root defines every multiplier and all other actions can be chosen as identity.

Compile this system to one ordinary tensor comparison using the constant-signature triangular construction in [SliceModuleKernel.md, Section 3](SliceModuleKernel.md#3-one-compressed-tensor). That construction uses a fixed number of role copies, distinct diagonal ranks, and scalar products, and works over any field. Forming its structure constants commutes with scalar extension. This proves the atom equivalence over every K simultaneously. The earlier MathProofs power-equation construction used partition removal and gives the same atom. [Tensor systems, Part III](https://arxiv.org/html/2306.03135v2#S4) · [Partition removal, Part IV](https://arxiv.org/html/2306.16317#S5)

## 2. Field-uniform conjunction and disjunction

We give explicit gates so that all comparisons are evaluated over the same unspecified extension. A tensor is concise if its three contraction supports are full. Compact each input to its supports first, using linear algebra over Q, which preserves comparison over every extension field. Support dimensions are unchanged by extending the field. In the application each pair is geometrically isomorphic, so side lengths coincide after compaction and the tensors are nonzero. Compaction may be implemented by coordinate projection to a row-pivot set on each support, which selects a subtensor in the fixed raw coordinates and prevents coefficient growth.

We use the following wrapper. Present a concise tensor as a slice map M from W to Hom(V,U). Put C = Q² and E = U ⊗ C*. For c = (x,y), let G(c) be the block diagonal pencil with blocks x I_b, y I_b and (x+y) I_b, where b > dim U. Its domain B_0 and codomain A_0 have dimension 3b. Form the tensor with label space W ⊕ C, input V ⊕ E ⊕ B_0, and output U ⊕ A_0 and slice

    Mhat(w,c) = [ M(w)  eval_c   0    ]
                [  0       0    G(c) ].

Here eval_c maps u ⊗ f to f(c)u. The input can be recovered by invariant flags. Labels with rank at most dim U form W, since every nonzero c makes at least two of x,y,x+y nonzero. Their common kernel is E ⊕ B_0, and the span of their images is U. Thus the restricted pencil on W and the quotient by that kernel recovers M. Conversely an isomorphism of the original pencils lifts with identity on C and the G(c) spaces, and with its U action tensored with the identity on C* for E. Identically chosen b ensures comparable wrappers. The wrapper is concise because M is concise, the evaluation pencil has no common kernel on E, and the G(c) slices have no common kernel and span the target A_0.

For disjoint-sum matching it is useful that the wrapper has scalar centroid over every extension. A centroid triple (L,R,H) satisfies

    H Mhat(w,c) = Mhat(L(w,c)) = Mhat(w,c) R.

The rank test implies L(W) ⊆ W, because multiplying a matrix by H cannot increase rank. The equations on the W slices imply H(U) ⊆ U and R(E ⊕ B_0) ⊆ E ⊕ B_0. Restricting those equations on E for all c and projecting the output to A_0 also gives R(E) ⊆ E. Comparing H_U eval_c and eval_(Lbar(c)), where Lbar is the quotient map of L on C, forces H_U and Lbar to be the same scalar. Indeed testing rank-one elements u ⊗ f gives H_U(u) f(c) = u f(Lbar(c)) for all u,f,c. Subtract that scalar from all three maps. Now H annihilates U and Lbar = 0. Injectivity of M gives L|_W = 0. The G(c) images span A_0, so the projection of H to A_0 vanishes. The two remaining expressions H Mhat(w,c) and Mhat(L(w,c)) are supported on disjoint domain summands B_0 and V. Their equality kills both. Conciseness then gives H = L = R = 0 for the scalar-subtracted triple.

For a direct sum of concise tensors the centroid is the product of their centroids. To see this in the same slice convention, apply the centroid equations to a label supported in one summand. The output of the slice is in that summand and the slice vanishes on all the other input summands. Equality of the left and middle expressions forces the label map to preserve summands by injectivity and the output map to preserve summands by the span of images. Equality with the right expression forces the input map to preserve summands by the zero common kernel. The equations then hold separately on each block. For a direct sum of wrapped tensors the primitive centroid idempotents therefore identify precisely its displayed summands, and any isomorphism permutes them. An isomorphism of matched summands can be summed to give the converse.

For an ordered tuple of two tensors, wrap each entry and take the direct sum. Use b_1 = 1+L_0 and b_2 = 2(1+L_0) for a common upper bound L_0 on all the original sides. The output dimensions of the two wrappers are distinct, so the tuple compares componentwise. This gives conjunction.

For disjunction of T_0 ≃ T_1 and S_0 ≃ S_1, compare the two unordered sums of individually wrapped ordered tuples

    { (T_0,S_0), (T_1,S_1) }    and    { (T_0,S_1), (T_1,S_0) }.

The outer wrapper has the same parameter for all four tuples. The matching that preserves the tuple positions holds exactly when S_0 ≃ S_1. The cross matching holds exactly when T_0 ≃ T_1. The centroid argument gives all possibilities, so the gate implements disjunction.

These operations hold over every extension, with no decision calls during construction. Each binary gate increases the largest side by at most a fixed constant multiple plus a constant. Hence a balanced conjunction of polynomially many binary disjunctions has polynomial output size. This is the ordinary conjunction and disjunction construction already used in MathProofs with the scalar-centroid glue. The pencil above uses only its field-uniform ordinary-isomorphism part.

## 3. Transfer Vertex Cover to simultaneous field selection

Choose pairwise coprime integers m_i > 1. Atom i asks for isomorphism of the pair from Section 1 with exponent m_i. For every finite extension K of Q, this is equivalent to having a solution to x^(m_i) = 2 over K. If such a solution x exists, Eisenstein's criterion at 2 gives [Q(x):Q] = m_i, hence m_i divides [K:Q].

For a graph G, combine the disjunction of the two incident atoms for every edge, and conjoin all edge predicates. Use a fixed equal pair if the edge list is empty. Every isomorphism over a degree-d field thus implies that {i : m_i divides d} is a vertex cover.

Conversely, if the latter set covers every edge, put K = Q(2^(1/d)), choosing the positive real root. By Eisenstein this number field has degree d. For every m_i dividing d, the (d/m_i)-th power of that positive root solves the corresponding atom. This one field therefore simultaneously supplies all covering atoms. It works for the entire tensor pair by the gates. Taking d = ∏_i m_i always supplies a real splitting field. Since the m_i are pairwise coprime, the minimum extension degree is exactly

    min over vertex covers C of ∏_(i in C) m_i.

The same construction works for any monotone formula of logarithmic depth using divisibility atoms: evaluate the formula on {i : m_i divides d}. Necessity follows from the tower law for every true atom, and sufficiency follows from the same single real field. The length of the formula and the bit lengths of all exponents control the construction time.

## 4. Encode the cardinality bound and the approximation gap

Use n = |V(G)| ≥ 2 and a bound 0 ≤ k ≤ n. Find n distinct primes p_i in increasing order by sieving through a polynomial bound in n, and put P = max_i p_i. The elementary polynomial bound on the n-th prime suffices. Choose C = n² + n ceil(log_2 P) + 1, and let m_i be the smallest power of p_i that is at least 2^C. All these operations use binary arithmetic in time polynomial in n. Thus

    2^C ≤ m_i < P 2^C.

Set D = (P 2^C)^k. A cover of size at most k gives an admissible degree at most D. If every cover has size at least k+1, every admissible degree is at least 2^((k+1)C). Its ratio to D is at least 2^(C-k log_2 P) > 2^(n²). The reduction has polynomial output length. This proves the stated decision hardness from Vertex Cover. [Karp, Reducibility Among Combinatorial Problems](https://people.seas.harvard.edu/~madhusudan/courses/Fall2020/Lectures/L19-after.pdf)

The gap also proves the approximation theorem. For some fixed B and all sufficiently large n the written tensor pair length L is at most n^B. Choose any ε > 0 with Bε < 1. In a positive instance a two-sided factor-2^(L^ε) estimate is at most D 2^(L^ε). In a negative instance it is greater than D 2^(n²-L^ε). Use the integer threshold D 2^n to distinguish them. Handling finitely many smaller n directly yields a deterministic polynomial-time Vertex Cover decider from any purported deterministic polynomial-time approximation algorithm at this factor.

## 5. Recognizing a raw family and the NP upper bound there

For this assertion a raw family is chosen explicitly. All compiler choices, as well as prime and exponent choices, are deterministic, and the output of the last gate is wrapped once more. Use the labelled vertex order 1,...,n. In a separate direct summand, include the common header tensor of format 1 × 1 × (n²+1) whose entries are the integer n followed by the adjacency matrix in row-major order. Put this common block first in each coordinate, ahead of the main tensor. The header has one-dimensional support in each mode, so after support compaction it is a 1 × 1 × 1 tensor. It never exchanges with the final main wrapper, whose dimensions are larger and whose centroid is scalar. The extra summand therefore leaves every extension comparison unchanged.

The raw language takes only exactly these generated pairs. Parse the leading header entry as an integer n and check the format and data length before any allocation. Verify the two adjacency words agree and describe a simple graph. Regenerate the tensor pair and compare all raw arrays to the input pair. This tests membership in polynomial time. In particular it is a test on the raw arrays and does not require a supplied isomorphism to the family. This choice concerns the canonical generated pairs. It does not assert a recognition algorithm for all their arbitrary GL rebases.

Once the graph is recovered, the degree-d predicate is polynomial time in the tensor input length and log(1+d) by testing the divisibilities and the cover condition. Guessing one binary d with 1 ≤ d ≤ D gives the NP upper bound on the recognizable family. No polynomial upper bound for the degree or for the witness matrices is needed.

## 6. Other coefficient fields

The same proof gives the decision, specified-degree and approximation statements over every fixed number field, with finite extensions measured by their degree over that field. Replace 2 throughout by an element π of valuation exactly one for any chosen non-Archimedean discrete valuation of the base field. Eisenstein for that discrete valuation proves irreducibility of x^m−π, and the root extension defined by x^d−π gives all necessary simultaneous roots for degree d. The compiler uses constants already in the fixed base field and its ordinary exact arithmetic. For an ordering in which π is positive, the pure radical witness can be taken inside a real closure for that ordering. The same arithmetic argument applies to any fixed field with exact polynomial-time coefficient arithmetic, efficient support compaction, and a fixed element of valuation one. The number-field case satisfies these conditions.

## 7. Scope

The finite-field minimum-degree result and power-equation atoms already appear separately in earlier MathProofs work. The result here uses the power-equation atoms to recover an exact least-degree optimization problem over Q, including polynomial-time testing at a specified degree on the raw canonical family and a stretched-exponential approximation gap. The input can be promised geometrically isomorphic. The construction does not give a general algorithm for rational TI, an NP upper bound for unrestricted bounded-degree rational TI, or a resolution of cross-characteristic or special-linear TI. A focused literature search found the published forms discussion and tensor compilers but did not locate this degree-selection result over Q. No claim of a solved published open question is made. The integer threshold and gap formulas were also checked against every labelled graph on two through five vertices. Those finite controls check the arithmetic and do not replace the construction proof. [Grochow and Qiao, change of fields and the forms problem](https://arxiv.org/html/1907.00309#S10.SS2)
