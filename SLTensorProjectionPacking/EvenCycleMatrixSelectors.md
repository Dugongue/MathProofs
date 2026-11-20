# Exact sign profiles on even cycles of matrix blocks

Work over \(\mathbb F_3\) with explicitly given three-tensors. This is an informal extension of [the Lie-stabilizer selector](LieGraphSelectors.md). The tensor modes may contain arbitrarily large intrinsic blocks. On the following raw-recognizable family, the entire determinant-sign profile of any pair is computable in deterministic polynomial time. In particular the upper gap reduces to one two-sign comparison.

## Recover the blocks and graph

Compute the Lie stabilizer by the three-term linear equation in the companion note. Its bracket is the componentwise commutator. Compute its center by solving the linear commutator equations on a basis. In each mode the center acts by a commuting family. Require every projected basis matrix to split over \(\mathbb F_3\), and refine their primary decompositions to their simultaneous generalized eigenspaces. These subspaces are independent of the choice of basis of the center. On a common primary block every projected operator is a scalar plus a nilpotent, and the nilpotent parts commute. Thus each block corresponds to an entire linear eigenvalue functional on the center. Conjugation by any ordinary transporter carries this block decomposition to the corresponding one. The primary decompositions use kernels of powers of \(A-\lambda I\) for \(\lambda\in\mathbb F_3\), so the extraction is deterministic polynomial time.

Express the tensor in chosen bases of the blocks and take one vertex for each nonzero block component. Require each block to occur in exactly two support components and that the associated cubic three-edge-colored graph be simple. The dimensions of the blocks are edge marks. A support vertex must have one of two types.

- Its three incident blocks are lines.
- It has one line and two equally sized blocks of dimension \(m>1\). In a frame of the line, its local tensor on the two large blocks is an invertible matrix.

The edges of dimension greater than one therefore form disjoint cycles, and dimension is constant on each cycle. Require those cycles to have even length. All conditions are invariant under arbitrary ordinary transporters and verifiable in polynomial time.

## A fixed connected graph isomorphism

For two connected support components, enumerate all color- and dimension-preserving graph isomorphisms by the image of one root and propagation along the three unique incident colors. For any one of those graph isomorphisms, a transporter must map each block to its designated target block. Use a bit \(x_e\) for the scalar sign on every thin edge. On an all-thin vertex the local tensor equation is a linear parity equation for its three incident bits.

On one large-edge cycle orient the traversal, and at a vertex \(v\) use invertible matrices \(M_v,M'_v\) for the source and target local tensors, in bases with the incoming large block as domain and outgoing large block as range. Transpose both matrices if necessary to use that convention. Write \(G_i,G_j\) for the two successive large block maps and \(s_v=(-1)^{x_{\ell(v)}}\) for the thin scalar. The local equation becomes
\[
 G_j=s_v M'_v G_i^{-\mathsf T}M_v^{-1}.
\]
In particular in determinant bits it gives
\[
 \operatorname{detbit}G_j+\operatorname{detbit}G_i
     =(m\bmod 2)x_{\ell(v)}+
       \operatorname{detbit}M'_v+\operatorname{detbit}M_v.
\]
Composing the actual maps around the cycle alternates inverse-transpose and cancels it after an even number of steps. The closing relation for the first map \(G\) is
\[
 A G=(-1)^\sigma G B^{-1},\qquad
 \sigma=\sum_{v\ {\rm on\ this\ cycle}}x_{\ell(v)}.
\]
Here \(A,B\) are explicit invertible matrix products depending on the source and target frames, obtained by composing the displayed transfer maps with \(s_v=1\). Every admissible \(G\) and thin assignment gives a unique sequence of big block maps satisfying all original equations. A thin edge whose two endpoints lie on the cycle appears twice in the sum, as required.

For each \(\sigma\), use ordinary matrix similarity to find a conjugator or reject. If a conjugator exists, the determinant possibilities are its bit plus the determinant image of the centralizer of \(A\). This image is computable directly from the primary cyclic lengths of \(A\): it is nonzero precisely when some cyclic primary length is odd. For completeness, on the \(f\)-primary module the centralizer is the endomorphism algebra of a direct sum of \(\mathbb F_3[t]/(f^k)\) blocks. The multiplicity matrices of equal lengths modulo \(f\) form the quotient \(\prod_k M_{n_k}(\mathbb F_3[t]/f)\). A same-length return through a different length is divisible by \(f\), so this quotient map is multiplicative. In its kernel, modulo \(f\), the action is strictly triangular by lengths. Repeated application puts the image in \(f\) times the module, then in progressively higher powers, so every kernel element is nilpotent. The kernel units have determinant one. For a length \(k\) quotient factor, lift a unit on its own equal-length blocks. Its determinant on each of the \(k\) successive \(f\)-layers is the field norm of the multiplicity determinant, yielding the \(k\)-th power of that norm on the whole module. Every norm sign is attained by surjectivity of the norm of a finite field extension. Ordinary rational canonical forms, conjugators and the primary lengths are computable by polynomial-time module operations over the fixed field.

The finite relation of possible \((\sigma,\operatorname{detbit}G)\) pairs is empty or affine. Indeed relative to one solution \((\sigma_0,G_0)\), write \(H=GG_0^{-1}\) and \(u=\sigma+\sigma_0\). The requirements are \(AH=(-1)^uHA\), which define a subgroup of \(\mathbb F_2\times\mathrm{GL}_m(\mathbb F_3)\). Its sign image is a subgroup of \(\mathbb F_2^2\). The pair relation from the two similarity tests therefore has an explicit binary linear description.

Combine that description for every large-edge cycle with the thin bits shared between their true incident vertices. Include each cycle's sign transfers above. All constraints are affine over \(\mathbb F_2\). The three overall determinant bits are affine in these variables by taking the sums on each mode, adding the signs of the permutations of blocks of their given widths and calibrating the chosen frames to the raw frames. Every solution of the linear system lifts to actual block maps because the cycles then have admissible closing maps and their transfer equations preserve the same thin variables throughout. Conversely an actual transporter satisfies the system. This computes the exact sign profile on the chosen graph isomorphism. Union over the polynomial list for a connected component.

For disconnected inputs use the component matching and exchange proof of the companion note. Ordinary matches and local automorphism sign images are already computed by the connected algorithm. Exchanging two equivalent components contributes only their common dimension parity in each mode. These exchanges and embedded component automorphisms generate the exact global stabilizer sign image. An ordinary matching and one possible local sign vector on each of its edges furnish a point of the global profile. Taking its coset by that sign image gives the full profile. On a negative signed comparison choose a nonzero vector outside that profile; on any other comparison use any direction. This is a safe projection and compiles to one two-sign instance.

## Unbounded raw examples

Take the bipartite cubic graph with shift matchings \(0,1,3\) from the companion note, with \(n\ge8\), \(4\mid n\) and \(3\nmid n\). Give edges of colors 0 and 1 block dimension \(m>1\), where \(3\nmid m\), and give color 3 line blocks. The large edges form one even Hamiltonian cycle. Put the identity matrix at each support vertex except one, where the matrix is a single regular unipotent Jordan block \(J_m\).

The raw primary extraction recovers the stated blocks. The same off-diagonal support argument used for lines works here for the linear equation on the Lie stabilizer. At the isolating location an off-diagonal block map acts in just one slot of a concise local tensor, so its vanishing forces that block map to be zero. Therefore the Lie action preserves each of the chosen blocks. Writing its local equations in compatible cycle orientations gives the additive recurrence
\[
 A_j=-M_v A_i^{\mathsf T}M_v^{-1}-a_{\ell(v)} I.
\]
Closing the even cycle imposes \(A_0=U A_0 U^{-1}+cI\), where \(U\) is \(J_m\), its inverse transpose, or a conjugate depending on the starting edge. This follows by composing two adjacent recurrences, which cancels their transposes, and using the identity choices at all but one vertex. Taking traces gives \(mc=0\), hence \(c=0\). A regular unipotent Jordan block has polynomial centralizer, with just a scalar eigenvalue and a nilpotent part in every element. All Lie matrices on the first big block are therefore polynomials in one Jordan block, and the others are their conjugates or transposes with scalar shifts. The projected Lie action commutes on every block and has split primary subspaces. The scalar block actions in the Lie stabilizer solve the original graph's oriented flow equations after changing signs on one bipartition. These flows separate distinct edge coordinates because the graph is 3-edge-connected, as proved in the companion note. The simultaneous primary refinement thus separates exactly the intended blocks, even after arbitrary rebasings of the input.

Both large modes have dimension \(nm\), the thin mode has dimension \(n\), and \(m\) can grow polynomially with \(n\). The weight blocks need not have small width. The proof relies on the precise matrix-block support and even-cycle hypotheses. Arbitrary raw tensors are outside its conclusion. The [AgentAlphaXiv step verification study](https://huggingface.co/datasets/alphaXiv/AgentAlphaXiv/resolve/a63f46066ac16fcb470f41933415e175825b6bcc/papers/01a1b00f-3a81-791c-98fd-c5daefe85ff8.pdf) motivates composing exact local transfers on shared data; the cycle closing and sign calculations above supply the mathematical proof.