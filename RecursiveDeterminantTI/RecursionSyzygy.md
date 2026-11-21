# Recursive determinant lines from cube-kernel splits

All vector spaces and tensor isomorphisms in this note are over F₃. The input is a surjective symmetric bimap β on U with label space W, given in coordinates, and the desired transporter satisfies hβ_A(x,y) = β_B(px,py). The prescribed sign is (det p)^a(det h)^b for a,b in {0,1}. The case a = b = 1 is the radical determinant on the two-step local algebra k ⊕ U ⊕ W. A relation bimap has input U* and label space K*, where K = ker(Sym²U → W), using the canonical symmetric pairing in odd characteristic.

**Theorem.** Fix an integer c ≥ 0. A deterministic polynomial-time class test and one ordinary TI reduction recover either sign on the recursively accepted class below. At each proper cube-kernel split the process may use either the mixed relation or its quotient if its dimension is at most c log₂(2 + L), where L is the explicit input length. The process permits one dual operation at each node and may recurse to unbounded depth. All typed witnesses use one original transporter, and every original transporter of the requested sign extends. There are explicit unbounded-depth instances in the even-U, odd-W, both-scalar-centroid domain with no automorphism of negative combined sign. Their two bimaps have zero common radical.

This is a polynomial-size sufficient theorem about a tested class. The stated construction handles any bimap in that class, including outputs of intermediate nodes with nontrivial centroid or common radical.

## 1. Exact split and calibration

Let X be a transporter-invariant subspace of U and put V = U/X, n = dim X, r = dim V and N = n + r. Let A_X = Sym²X, let M = ker(Sym²U → Sym²V), and form
\[
K_X=K\cap A_X,\quad H=(K\cap M)/K_X,\quad G=\operatorname{im}(K\to\operatorname{Sym}^2V).
\]
The canonical identification M/A_X ≅ X ⊗ V sends the class of x times a lift of v to x ⊗ v, and therefore identifies H with a subspace of X ⊗ V. Put D = (X ⊗ V)/H. The children are the symmetric quotients on X and V with respective label spaces W_X = Sym²X/K_X and W_V = Sym²V/G. The asserted identification follows by splitting U as a vector space for the dimension and checking lift-independence in the displayed description. An original transporter induces the maps p_X, p_V, p_H, p_D and the child label maps h_X and h_V. Every use of these symbols refers to those induced maps.

Write χ(p,h;a,b) = (det p)^a(det h)^b, with all exponents reduced modulo 2. There are explicitly computable signs c_H(A,B) and c_D(A,B), each a ratio of scalars computed separately from the inputs, for which
\[
\begin{aligned}
\chi(p,h;a,b)&=c_H(A,B)\,
 \chi(p_X,h_X;a+rb,b)\,\chi(p_V,h_V;a+nb,b)(\det p_H)^b,\\
\chi(p,h;a,b)&=c_D(A,B)\,
 \chi(p_X,h_X;a,b)\,\chi(p_V,h_V;a,b)(\det p_D)^b.
\end{aligned}
\tag{1}
\]
In particular, b = 0 needs no mixed line. A mixed space of dimension zero carries the identity line.

For the calibration, choose bases by deterministic linear algebra. On each input I let s_I be the determinant in the written U basis of the concatenation of the X basis and lifts of the V basis. Choose the written K basis by concatenating a K_X basis, lifts of the written H basis, and lifts of the written G basis. Let d_I be the determinant in the monomial basis of Sym²U of that K basis followed by lifts of the written W basis. Define d_{X,I}, d_{V,I} analogously for the written kernel and label bases of the two children. Let t_I be the determinant of an H basis followed by lifts of the D basis in the tensor product basis of X ⊗ V. Then, with d_{X,I}d_{V,I} abbreviated as f_I,
\[
c_H(A,B)=(s_B/s_A)^{a+(N+1)b}(d_A/d_B)^b(f_B/f_A)^b,
\qquad
c_D(A,B)=c_H(A,B)(t_B/t_A)^b.
\]
Every relative determinant is 1 for a zero-dimensional space. Different auxiliary bases give the same character in raw input coordinates.

Indeed, det p = (s_B/s_A) det p_X det p_V. The determinant of Sym²p is (det p)^{N+1}, as follows by triangularizing over an algebraic closure and counting each diagonal entry among all degree-two monomials. The exact sequence for K and W gives det h = (d_A/d_B)(det p)^{N+1}/det(p|_K). The two-step flag of K gives det(p|_K) = det p_{K_X} det p_H det p_G in the concatenated K basis. Eliminating p_{K_X} and p_G by the analogous child exact sequences proves the first equation. The tensor product and mixed exact sequence give det p_H = (t_A/t_B)(det p_X)^r(det p_V)^n/det p_D. Substitution proves the second equation over F₃.

## 2. Dual step and intrinsic recursion

The relation bimap on U* is the map to K* given by evaluating symmetric bilinear forms in K. The symmetric pairing is defined by evaluating the quadratic monomial uv on x,y as (x(u)y(v) + x(v)y(u))/2. An original transporter induces (p^{-T}, (p|_K)^{-T}). The exact sequence above shows that the dual character with exponents (a + (N + 1)b, b) equals the original character after multiplication by (d_A/d_B)^b. Here d_I uses the written K basis of the dual step, with lifts of the written W basis. Thus this dual step preserves the same problem on the same transporter. Its induced action can be required by the evaluation tensors and the map K → Sym²U. The double relation construction recovers the original quotient up to the canonical evaluation identifications.

For any node compute
\[
X=\ker\bigl(U\longrightarrow \operatorname{Sym}^3 U/(UK),\ u\longmapsto u^3 \bigr).
\]
Cubing is linear over F₃, and UK is the linear span of products, hence X is computed by elimination and is carried to X by every transporter. Split when 0 < dim X < dim U and the requested character satisfies the mixed condition of the theorem. Use the first formula of (1) for a small H and the second for a small D, with a fixed preference if both pass. Where b = 0 take the first formula with no mixed line. Use the following terminal alternatives.

- All spaces whose determinants appear may be small. An explicit truncated exterior algebra and its degree-one inclusion expose each required line whenever the space has dimension at most c log₂(2 + L). When both exponents are zero the line is free of vector-space determinants.
- The previously proved compact syzygy record for the requested character may be used when its applicable hypotheses and its polynomial size bound pass. For example the perfect-syzygy cube-kernel record in [Cube Kernel Syzygies](CubeKernelSyzygies.md) gives the combined character. Such a terminal provides an unpinned line for the actual induced map on every transporter.

Fix priorities among terminal choices. On a node try terminal and split rules, then try the same rules on the dual once if neither applies. Recurse only after a found split. If a needed leaf has no successful rule, the input is outside the asserted class. Use a common L, for example the maximum of the two input lengths in a two-input class test. The records use the basis-free dimensions, ranks, and parity tests of the stated rules, so any difference in the resulting rule shapes for accepted inputs certifies ordinary nonisomorphism. Acceptance is independent of the requested sign value, and every testing step uses only field arithmetic on explicit matrices. The scope may depend on the exponents a and b.

For the exact witness statement, include β, the symmetric products through degree 3, the quotient maps, all restricted inclusions for K, X and the split diagram, and the child products. Record X ⊗ V by its surjective bilinear product and record its actual quotient D or subspace H. Symmetric powers and tensor product actions are forced by their generators. Each restricted map is forced by commuting with its inclusion or quotient, so all maps of the record are determined by one root transporter. At the leaves and on the small mixed spaces impose the exterior product and degree-one inclusion. Multiplying vectors from one-dimensional lines can be encoded as a nonzero bilinear map to their tensor product line. Use such products to combine the lines according to (1) and use the two written scalar factors of each calibration in that multiplication. Pin the root line with the requested relative sign. Every root transporter extends along the diagrams and product lines, and it preserves the pin exactly when its determinant has the requested value. In particular this procedure works without an independent existence claim about any child transporter.

The proper splits have positive ambient dimensions whose sum is the parent dimension, so there are at most 2 dim U − 1 nodes, with one additional dual operation per node. The symmetric powers have dimension O((dim U)^3), and an exterior algebra for a space of dimension d has dimension 2^d. Thus the number and total dimension of all spaces and tensor entries are polynomial in L for fixed c. The same is true if compact terminals are used with a checked uniform polynomial bound.

## 3. Packing into one ordinary TI instance

The number of spaces and maps above can grow, so first pack their typed tensors into a system with a constant number of tensor types and tensors. Give each role and each occurrence copy of a role its own coordinate idempotent in one algebra F₃^m. Include its multiplication and its action on an auxiliary module where the m coordinate idempotents have mutually distinct positive ranks 1 through m. The latter forces every idempotent to be fixed. Include this algebra's action on the direct sum of roles and on the direct sum of occurrence copies. Add the linear map from the occurrence sum to the original role sum whose restriction to each occurrence copy is the identity identification with its underlying role. Thus its commuting condition ties the occurrence action to the role action. Contravariant slots act by the dual inverse. Pad tensors of lower order with occurrence copies of a scalar line whose nonzero vector is named. Put each padded tensor on its own occurrence blocks in an array associated with its covariant and contravariant slot pattern. This uses at most eight arrays, and the other encoding tensors are a constant-sized system. Every isomorphism carries the blocks with fixed indices and therefore preserves each original tensor, and every typed system isomorphism extends through the auxiliary algebra and module. The auxiliary dimensions are polynomial. Apply the linked tensor-system to ordinary 3-TI compiler of Chen, Grochow, Qiao, Tang and Zhang, Section 4, over the same field. A fixed negative instance can use a zero and a nonzero scalar tensor. [Primary source, Section 4](https://arxiv.org/html/2306.03135v2#S4)

## 4. An arbitrary-depth family with both centroids scalar

For a seed take the n = 7, r = 1 perfect-syzygy example of the cube-kernel construction. Its ambient dimension is 8, its label dimension is 23, and the rank of cubing modulo cubic relations is 1. Both centroids are scalar, both common radicals are zero, and every automorphism has combined sign +1. The seed can be fixed deterministically by finite search in dimension 7 using the existence bound and tests in that construction.

Suppose the previous stage is on X with kernel K_X and label W_X, and the rank s of cubing modulo X K_X is in [1,8]. Choose v₁,…,v_s in X whose cube classes form a basis of the image. Put q_j = v_j² and write its image in W_X as q̄_j. The image q̄_j is nonzero because otherwise v_j³ vanishes in the cubic quotient. Adjoin E = F₃⁸ with basis e₁,…,e₈. On these eight vertices take the graph whose edges are a complete bipartite graph on two quartets with a matching removed, together with a cycle on the second quartet. It has 16 edges, and every vertex has odd degree, either 3 or 5. Partition its edges into eight pairs. Assign q₁,…,q_s to the first s pairs and q₁ to any remaining pair. Denote the assignment by q_{ij} on an edge, and put q_{ij} = 0 away from edges. In U = X ⊕ E set
\[
K=K_X\oplus XE\oplus\left\langle e_i e_j+q_{ij}\ :\ i<j\right\rangle \ \subset\ \operatorname{Sym}^2U.
\tag{2}
\]
Thus the new symmetric quotient has label space W = W_X ⊕ W_E with W_E on eight independent vectors w_i = e_i² mod K. The mixed product is zero. The off-diagonal product of e_i and e_j is −q̄_{ij} in W_X.

**Cube kernel.** The cubic relations kill every mixed cubic containing a variable from X and a variable from E. Multiplying the last relations in (2) by X consequently kills each Xq_j, and multiplying them by E kills every off-diagonal cubic in E. In the old pure X summand, the surviving space is Sym³X modulo X K_X and the subspaces Xq_j, which kill the full old cube image. No relation has a nonzero coefficient on any pure e_i³. The new cube image therefore has dimension 8, with those eight cube classes its basis, and the cube kernel is exactly the previous X. At that split H is the full mixed space and D = 0. The quotient child on E has eight input and eight label coordinates, with diagonal bimap e_i² = w_i. The dimensions of U and W each grow by 8. Every stage accepts with a fixed bound such as c = 1, since the quotient child is bounded and the seed is a compact terminal. The explicit bimap entries are computed in polynomial time in the final dimension by linear algebra at each extension.

**Two centroids.** Write an input centroid operator of the new quotient bimap as
\[
T=\begin{pmatrix} P & B\\ C & R\end{pmatrix}
\]
on X ⊕ E, and let its label operator be J. The centroid equalities are β(Tu,v) = β(u,Tv) = Jβ(u,v). Test u in X and v in E. Their product is zero, and the projection of β(Tu,v) to W_E is the diagonal product of Cu and v. This yields C = 0. The same test for β(u,Tv), using zero old common radical, yields B = 0. The products of X span W_X, so J preserves W_X and the old scalar centroid gives P = a I and J|_{W_X} = a I. On e_i,e_j for i ≠ j, balancing and projecting onto W_E gives R_{ji}w_j = R_{ij}w_i, which makes R diagonal. For an edge with q̄_{ij} nonzero, comparison with Jβ(e_i,e_j) gives both adjacent diagonal entries of R equal to a. Every vertex is incident to an edge, so R = a I, and by surjectivity J = a I. The common radical is zero by testing first against E in W_E and then against X in W_X.

For the relation bimap the symmetric relation matrices include
\[
Q_M=\begin{pmatrix}0&M\\ M^{\mathsf T}&0\end{pmatrix}
\]
for all rectangular M, by the mixed summand of (2). A balanced input operator T in the same block notation on X* ⊕ E* satisfies Q_M T = T^{\mathsf T}Q_M. Its first diagonal block M C and second diagonal block M^{\mathsf T}B must be symmetric for every M. Since both input blocks have dimension at least two, take M supported on a single row to force C = 0, and M supported on a single column to force B = 0. The mixed block identity P^{\mathsf T}M = M R for every matrix unit gives P and R equal scalars. This suffices for the centroid by surjectivity of the relation bimap. The common radical is zero since all the forms Q_M have common radical zero.

**No negative automorphism.** Any automorphism preserves X by the cube-kernel calculation and induces an automorphism on the diagonal bimap on E. Hence its matrix on E modulo X is monomial: off-diagonal products of pairs of columns vanish, each output coordinate square has an independent label, and invertibility gives exactly one nonzero entry per row and column. Write p(e_i) = u_i + α_i e_{π(i)}. The zero products between X and E force u_i = 0 by zero old common radical. The resulting permutation π preserves the support graph, and the old label map satisfies
\[
h_X(\bar q_{ij})=\alpha_i\alpha_j\bar q_{\pi(i)\pi(j)}.
\tag{3}
\]
In particular, it permutes the projective lines spanned by the edge labels. Choose a representative for each such line. In these representatives write each edge label as its nonzero scalar times its representative, and write the multiplier for h_X on each line as a sign. Each line has an even number of occurrences, since assignments were made in pairs. Multiply (3), in scalar coordinates, over all edges. The line multipliers disappear by their even multiplicities, and the individual label scalars cancel under the edge permutation. What remains is ∏_i α_i = 1 because all vertex degrees are odd. The diagonal quotient label map permutes the w_i with coefficients α_i² = 1. Thus the induced combined sign on E and W_E is \((\operatorname{sgn}\pi)^2\prod_i\alpha_i=1\). By (1) with D = 0 and identical endpoints, the parent combined sign is the old combined sign, which is +1 by induction.

The family has recursive chains of unbounded length with ambient dimensions 8,16,24,… . For the rules in Section 2 using the compact terminal named there, intermediate parent stages fail that terminal's test because H is full and nonzero. At the logarithmic cutoff, only O(log L) levels can fit into the small terminal, so the deterministic chain itself has unbounded depth. Reflecting one written label basis vector at any stage yields an ordinarily isomorphic pair whose every transporter has sign −1, because the automorphism character is trivial. The ternary even-dimensional rectangular multiplication cubic transfers this sign to the corresponding local-algebra cubic family. [Exact cubic orientation](ExactCubicOrientation.md)

Status: written proof.
