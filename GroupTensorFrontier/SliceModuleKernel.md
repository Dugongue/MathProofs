# A polynomial kernel for tensor isomorphism by removing repeated slice modules

This is an informal theorem about explicit dense three-tensors over a fixed finite field F with q elements. The three modes are ordered.

View a tensor as a linear family A of maps from U to V, with parameter space W, so A(w) is linear in w. For each of the three choices of label mode W, take a basis of W and treat the slices as the arrow maps of a two-vertex Kronecker quiver with dim W arrows. Decompose its representation into indecomposables. Write r for the sum of the two vertex dimensions of **one copy of each distinct indecomposable type**, taken after support compaction. A change of basis of W preserves direct sums and is an invertible operation on the category of slice representations. In particular r is an ordinary-isomorphism invariant and needs no canonical basis of W.

**Theorem.** In deterministic polynomial time, arbitrary raw tensor pairs can be reduced to one ordinary three-tensor pair of side O(r + dim W), where the two compacted input parameters agree on any yes instance. In particular this is a polynomial kernel with side O(r² + 1) and O((r + 1)^6) entries. One can use the best of the three label modes. A witness for the smaller pair yields a witness for the original pair in polynomial time. More precisely the weighted compressed data and the original data have exactly the same feasible changes of basis in W.

There is also a deterministic search algorithm on the weighted compressed data taking

    q^min{u₀², v₀², (dim W)²} · poly(L),

where u₀ and v₀ are the trimmed vertex dimensions and L is the written input length. This gives polynomial time when one trimmed matrix mode has dimension O(sqrt(log L)), with no restriction on the original matrix dimensions or the common label dimension. The compression can also be used with any solver on the resulting single comparison.

## 1. Compute the weighted data

Check the three original dimensions and all three flattening ranks. If dimensions or ranks differ between the two inputs, return a fixed negative pair. Compact to the supports by choosing and saving bases. An isomorphism of the compacted inputs extends across complements, since their original dimensions agree. Zero inputs can be decided directly. In the remaining cases the map W → Hom(U,V) is injective.

Compute the algebra

    E = { (a,b) in End(U) × End(V) : b A(w) = A(w) a for every w }.

All its basis equations are linear. It acts as a matrix algebra on U ⊕ V. Compute its radical and an explicit semisimple quotient, using the finite-field algebra structure algorithm. Its deterministic running time is polynomial in the characteristic and the input size, sufficient over any fixed field. [Ivanyos and Qiao, Theorem 18](https://arxiv.org/html/1708.03495#Thmtheorem18)

For each diagonal matrix unit in a simple quotient factor, lift it into the remaining orthogonal corner of E and take a sufficiently high q-power. This yields an idempotent because the lift x satisfies x² − x in the nilpotent radical and the two powers of x commute. Explicitly, if J^h = 0 and q^k ≥ h, then (x² − x)^(q^k) = 0, so (x^(q^k))² = x^(q^k). If working in a corner, the quotient map for that corner is still onto its quotient corner by compressing a preimage with the corner idempotent. Remove each lifted idempotent before lifting the next. The leftover idempotent maps to zero and is therefore zero. Every lifted idempotent is primitive, since a nontrivial splitting would split its primitive residue or give a nonzero idempotent in the radical. Its image on the two vertices is an indecomposable slice representation, since any decomposition of that image would split its endomorphism idempotent. This explicitly computes an indecomposable decomposition in polynomial time.

Use constructive module isomorphism to compare these fixed-arrow summands, retaining a representative of each type and the number of copies. This module test takes the two vertex projections on U ⊕ V and the slices as a matched list of operators. By preserving the projections and the slices it is exactly the two-vertex quiver test. [Brooksbank and Luks, Testing isomorphism of modules](https://ix.cs.uoregon.edu/~luks/ModIso.pdf)

On each side form the trimmed representation A₀ by taking the direct sum of retained copies. Partition its vertex spaces U₀ and V₀ by the common multiplicity of their summands. A summand that vanishes on one vertex contributes no dimension there. Record which actual multiplicities occur and the two dimensions for each. If the descriptions disagree, return a fixed no instance. The number c of distinct multiplicities is at most r. Sort their integer labels and use the same order on both sides.

## 2. Why one shared label map suffices

For an invertible map s on W between the endpoints, compare A(w) with A′(sw) at fixed labels. Replacing A′ by A′ composed with s does not change its decomposition into vertex summands as vector spaces. It does not create new direct summands or change fixed-label equivalence of two constituents, because s is invertible. Thus Krull–Schmidt gives the following equivalence for **each given s**.

- The two original slice representations are equivalent after applying s to the labels.
- The two trimmed slice representations are equivalent after applying s to the labels, by maps preserving the multiplicity partitions.

In the forward direction, match indecomposable summands of the same fixed-label type after the substitution and use any isomorphism on the two retained representatives of a matched type. Krull–Schmidt matches the multiplicities. In the reverse direction, apply Krull–Schmidt inside each multiplicity part separately and repeat each matched indecomposable according to its shared positive multiplicity. Direct summing the resulting witnesses gives an original transporter with exactly that s. Even if the given maps on the compressed spaces mix the chosen indecomposables, re-running the polynomial-time fixed-label module-isomorphism search on the original slices recovers an original witness with that s.

The common kernel of the slices as a family on W is unchanged by trimming. Indeed a slice is zero on the original representation exactly when it is zero on every copy of every type. So W still embeds into Hom(U₀,V₀) and dim W ≤ u₀v₀. Consequently the side estimate O(r + dim W) implies O((r + 1)²).

## 3. One compressed tensor

Build a linked system of four spaces U₀, V₀, W and D = F^c. It has the bilinear map W × U₀ → V₀ from the trimmed slices, componentwise multiplication on D, the actions of D projecting U₀ and V₀ onto their multiplicity parts, and a unary nilpotent shift on D. The shift sends the ith coordinate idempotent to the next, and the last to zero. An automorphism of the split algebra D permutes its coordinate idempotents. Commuting with this shift fixes the last one and then every predecessor. Hence the multiplicity parts remain fixed. The data have constant signature, and isomorphisms are precisely the trimmed transporters with a common s and these partition constraints.

For the linear side bound use the following explicit variant of the earlier triangular algebra compiler. It works over F and for any constant list of bilinear maps, with unary maps written bilinearly using a distinguished scalar role. For each role X take a copy W_X in the common corner O → P. For each bilinear map f from X × Y to Z use a middle vertex M with arrows F e ⊕ X from O to M and F h ⊕ Y from M to P. Their four products are eh = l, xh = x in W_X, ey = y in W_Y, and xy = f(x,y) in W_Z. Here l spans the common scalar role in the corner. For the first arrow, use two outgoing scalar arrows to private right vertices with products equal to the two coordinate projections of F e ⊕ X. Use two incoming scalar arrows from private left vertices for the second arrow with its two projection products. For each W_X, including the scalar role, add a private middle vertex with arrows X and F whose product is scalar multiplication onto W_X. All unlisted cross products vanish.

At each vertex place a different truncated univariate algebra of constant dimension. Its positive powers annihilate cross corners, and its identity acts on incident corners. The radical is the positive diagonal degrees plus all cross corners, since that ideal is nilpotent and the quotient is a product of copies of F. Associativity follows because all products of two radical cross arrows go from a left vertex to a right vertex, so every triple of radical cross arrows vanishes. For any algebra isomorphism, first conjugate by a unit congruent to one modulo the radical to align the two systems of lifted idempotents. Explicitly, if u_i and e_i are the two orthogonal idempotent systems congruent termwise after permuting, z = Σ_i u_i e_i is a unit with u_i z = z e_i. Distinct diagonal dimensions then force every vertex to keep its role. This normalization is constructive.

The projection products split the distinguished lines from X and Y by their kernels. The private middle probes pin each W_X as an image. Write λ for the nonzero scale on l and c_X for the map on W_X. If the anchor lines in a particular map scale by α and β, preservation of eh gives αβ = λ. The maps on its two variable arrow blocks are β⁻¹c_X and α⁻¹c_Y by the products with the anchors. The fourth product gives

    c_Z f(x,y) = λ⁻¹ f′(c_X x,c_Y y).

Thus the system maps are g_X = λ⁻¹c_X, with identity in the scalar role. Conversely every system isomorphism extends by setting the anchor scales, projection-arrow scales and scalar probe scales to one. This proves both directions, and the construction uses only a constant number of copies of every linked space. Its algebra has dimension O(u₀ + v₀ + dim W + c + 1).

Take the multiplication tensor of this unital associative algebra. An isotopy p(x)q(y)=r(xy) of unital associative algebras normalizes to the unital isomorphism φ = L_(p(1))⁻¹p = R_(q(1))⁻¹q. Evaluation at the source unit gives the two identities and proves these multipliers are units, since their left or right multiplication is invertible. Multiplicativity then follows by substitution. Any algebra isomorphism itself gives a multiplication-tensor isomorphism. Dualize the two input slots in the coordinate convention for ordinary tensors. Thus the output is a single ordinary comparison, with the announced side and constructive recovery. Related sources include [tensor systems, Chen–Grochow–Qiao–Tang–Zhang](https://arxiv.org/html/2306.03135v2#S4) and [triangular algebras for bilinear maps](https://arxiv.org/html/2611.18084v1#S4). Our earlier one-sign compiler supplies the multi-map version of the triangular construction.

## 4. Direct parameterized search

Choose a smallest role among U₀, V₀ and W. Enumerate its invertible maps. When choosing U₀ or V₀, discard maps failing to preserve all multiplicity parts. Substituting the selected map into the trimmed tensor leaves a fixed list of linear maps acted on by the two remaining roles, with the remaining color conditions imposed by unary projections. For example, fixing the U₀ map gives a list of maps W → V₀ indexed by a basis of U₀ and a projection for every multiplicity part of V₀. Fixing V₀ instead can be treated by dualizing the bilinear map to use V₀* as a slice role. Fixing W gives a list of maps U₀ → V₀ and the unary projections on both vertices. In each case the remaining simultaneous equivalence test is the constructive module test, encoding each space by its projection in the direct sum of the two roles. This proves the stated bound. The resulting s and a second fixed-label test on original data recover all three original maps.

## 5. Scope and novelty

The saving arises from eliminating **isomorphic copies of indecomposable fixed-label modules**, rather than splitting the tensor into independent centroid summands. All trimmed modules still share a single variable label map. The preprocessing handles nonsemisimple endomorphism algebras and requires no decomposition in the input. A tensor with every fixed-label constituent different may receive no size advantage. A large multiplicity can give arbitrarily large savings, for example by repeating every constituent of a fixed family by a common growing factor.

This theorem combines standard module algorithms and Krull–Schmidt with an explicit ordinary-TI kernel retaining multiplicity data. Related prior MathProof work used Kronecker cancellation and decomposition to analyze determinant signs. The kernel statement and its complexity consequences are the contribution here. A targeted literature check did not certify priority, and the proof does not assert a general improvement in the worst-case runtime of tensor isomorphism.

## 6. Exact counting and uniform transporters

The kernel also reduces exact counting of original transporters to exact counting of transporters for the same single smaller pair, followed by polynomial-time arithmetic. In the nonzero compacted input, once s is fixed and feasible, original fixed-label witnesses form a torsor under E^×. In the trimmed linked system the corresponding group has order b = ∏_m |E_m^×|, where E_m is the fixed-label endomorphism algebra of the trimmed multiplicity-m part. All these orders are computable. For any such algebra, with radical J and quotient ∏_i Mat_(a_i)(F_(q^d_i)), its unit group has order

    q^dim_F(J) · ∏_i ∏_(j = 0,…,a_i−1) (q^(d_i a_i) − q^(d_i j)).

This uses surjection on units and kernel 1+J. Every feasible s contributes the same number of witnesses in either system.

For the actual output tensor, the overhead is also computable. Let v be the number of vertices in its triangular algebra, z the sum of dimensions of cross corners, t the number of bilinear map gadgets, and b₀ the number of role probes. For each isomorphism of the linked systems the count of normalized, vertex-preserving algebra isomorphisms is

    (q−1)^(1+5t+b₀) · ∏_i a(N_i),

where a(1)=1 and a(N)=(q−1)q^(N−2) for N≥2. Indeed the anchor λ is free, each bilinear gadget has one free anchor and four free scalar projection arrows, each probe has one free scalar, and each truncated polynomial diagonal corner is independent. Its generator may go to any polynomial with zero constant coefficient and invertible linear coefficient. Every remaining cross-corner map is forced by the products in the construction. There are q^z choices of the complete lifted vertex system, because conjugation by 1+J acts transitively and the stabilizer consists of the diagonal radical units. Finally, the two unit multipliers in an isotopy multiply the count by |R^×|², with |R^×|=(q−1)^v q^dim_F(J). This establishes a constant, explicitly computed fiber size over every feasible linked-system isomorphism.

If the input was initially nonconcise, multiply the compacted input count by the number of extensions across complements of its three support spaces. For a mode of dimension n and support dimension d this is |GL_(n−d)(F)| q^(d(n−d)). A zero/zero input has ∏_i |GL_(n_i)(F)| transporters and can be handled directly. Consequently a single count on the smaller pair suffices, with exact integral divisions before multiplying the original factors. Computing all factors uses matrices and integers with bit length polynomial in the input length.

Given a uniform output transporter, its label component s is uniform over the feasible label maps by the constant fiber counts. To sample a uniform original transporter, compute any original fixed-label witness for that s and compose with a uniform E-unit. Sample a uniform invertible matrix in each quotient factor by choosing its columns successively outside their previous span. Take a deterministic lift of the resulting quotient unit and multiply it by a uniform element of 1+J. This produces a uniform E-unit. Extend across unused complements by independent uniform invertible quotient maps and uniform off-diagonal blocks. All sampling is exact and takes expected polynomial time with unbiased random bits.

## 7. Example showing why the weights are necessary

Over F₂ take four distinct one-dimensional slice module types with nonzero scalar slices labelled by x, y, x+y and z on a three-dimensional label space. In one input duplicate the x-type and in the other duplicate the z-type. The two unweighted trimmed representations coincide, and both have the same multiset of multiplicities. However z is the unique label functional whose removal lowers the span dimension. Any feasible common label map preserves this feature. Hence it cannot move the double multiplicity from x to z. The original pair is no, and the weighted kernel correctly retains this distinction.
