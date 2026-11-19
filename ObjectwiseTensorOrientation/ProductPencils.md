# An objectwise lock for products of intrinsic coefficient fields

**Theorem.** Over F = F₃, suppose a raw tensor yields a deterministic polynomial-time computable, covariant space B of alternating forms on one tested mode V. Suppose the pencil is a direct sum of pencils on subspaces V_i, each pencil consisting of the alternating forms obtained from one nonsingular form J_i by multiplying one argument by elements of a finite field E_i acting on V_i. Require that each E_i acts self-adjointly for J_i and that B is the full independent direct sum of these field lines. Put dim_(E_i) V_i = 2m_i. Assume that for each type (degree of E_i/F, m_i) there are at most a fixed constant number of factors with m_i odd. There is a deterministic polynomial-time objectwise two-sign to one-sign reduction on this raw family, with the other tested mode unrestricted. If all m_i are even, there is no bound on the number of equal factors. Neither the block decomposition nor any generator of a pencil is supplied.

## Recover all fields and blocks from linear equations

From B compute the space of pairs (a,b) of operators on V satisfying

    J(a x,y) = J(x,b y)    for every J in B.

These are linear equations on matrix entries. Its projection C to the first operator is a unital algebra, since the corresponding second operators multiply in reverse order. On the promised family C is the centralizer of A = ∏ E_i in End(V). To prove this take the block diagonal form J₀ = ⊕ J_i, which lies in B and is nonsingular. At J₀ the second operator is forced to be the ordinary adjoint of a. Substituting J₀(c x,y) for c∈A then gives ca=ac. Conversely the adjoint of a commuting with A also commutes with its self-adjoint field action and the required equations hold. Consequently C is the product of the full E_i-linear endomorphism algebras of V_i. Its center is precisely the represented A.

Compute that center by commutator equations, and decompose it into its finite-field factors using the standard algebra algorithms in fixed characteristic. The primitive idempotents recover the actual V_i. The result is intrinsic. This can also be used as an exact recognition procedure inside the class of tensors with the given covariant rule B. Check that the recovered center is a product of fields, that B has no cross-block forms and contains every isolated projection of each of its forms, and on each block that a nonzero basis element J_i is nonsingular, the field acts self-adjointly, and the block pencil is exactly E_i J_i. In the displayed class every nonzero element of a block pencil is nonsingular, so the first basis element works. These conditions are ordinary linear algebra after the field decomposition, and precisely certify the structure used below. On a block, self-adjointness in the trace pairing realizes J_i as the field trace of a nondegenerate E_i-bilinear alternating form. Its E_i-dimension is therefore even. [Finite-field algebra algorithms](https://arxiv.org/abs/1708.03495)

## Read the determinant after the blocks are permuted

Choose arbitrary ordered F-bases of the V_i and let C_T be the matrix whose columns are those bases concatenated in an arbitrary order. Let

    p(T) = (∏ Pf(J_i in its block basis)) / det C_T.

Every physical transporter g:T→S permutes these canonical blocks, sending the respective field actions by field isomorphisms. If g maps block i to block j, the pullback of J'_j to V_i is μ_i J_i for a nonzero μ_i∈E_i. The Pfaffian on the E_i-pencil obeys

    Pf(μ_i J_i) = Pf(J_i) Norm_(E_i/F)(μ_i)^m_i.

Indeed, write the E_i-alternating trace form in a symplectic basis. Multiplying one vector in each of its m_i hyperbolic pairs by μ_i pulls J_i back to μ_i J_i and has F-determinant Norm(μ_i)^m_i. This verifies the identity in every raw basis. Using it in the Pfaffian congruence formula gives the block determinant. Permuting the concatenated blocks has sign one because they all have even F-dimension. Taking the product and converting from the block frames to the raw frames gives

    det g = [p(T)/p(S)] · ∏_(i with m_i odd) Norm_(E_i/F)(μ_i).

Thus large collections of even-multiplicity field blocks need only an explicit scalar calibration. There is no choice of matching for them and no need to pin any of their form generators.

## Encode just the norms that matter

Use the ordinary tensor system containing T, the recovered field action A, its idempotents as an unordered set, and the actual form evaluation of B. A transporter induces the precise maps on these data and extends to them. For each block with odd m_i, extract a one-dimensional F-line whose induced multiplier is Norm(μ_i), using the field-line norm construction. In detail, take successive copies of the E_i-line B_i linked by the F-linear maps x↦x^(3^j) in its chosen E_i coordinates. Semilinear maps on the copies have multipliers which are the respective powers of the original multiplier. Couple these copies by bilinear products in their chosen coordinates. The resulting multiplier lies in F×, so restrict the output line to its F-span of 1. From forward rather than pullback convention one obtains the inverse multiplier, which is identical in F×. Attach the needed intermediate line action to the same E_i isomorphism as the original pencil. This uses polynomial dimension even when the fields have exponentially many elements. [Single coefficient-field construction](FieldPencils.md)

Within each odd type, use all orderings of its bounded number of block labels. Index these orderings by a split coordinate algebra, and include the linear maps taking a primitive coordinate to each of its ordered component labels. Multiplication maps for the successive norm lines are attached for each ordering, with a single common output F-line for that type. These products are formed in fixed raw coordinates, so their induced multiplier is the product of the selected norm multipliers. Every ordering gives the same product. Thus there is no requirement to preserve a selected order of indistinguishable blocks. This diagram can be written with one sort per sum of intermediate spaces and linear incidence maps, or by attaching each product chain on its own tagged occurrence and permuting occurrences via the ordering algebra. There are only a constant number of orderings per type. The allowed permutation of the primitive idempotents of this algebra is forced to be the permutation of the actual ordered tuples, because each of their slots is recovered by the included incidence maps. This proves both that every valid base map extends and that no spurious multiplier arises.

Order the different types by their two integer invariants, and multiply their product-line scalars by ordinary bilinear maps. An empty product uses an identity F-line. On the final F-line mark the raw coordinate p(T) in a chosen basis. Its induced multiplier times p(T) must equal p(S). By the determinant identity this is exactly det g=1. All input-side choices, including the form generators and block frames, are made from T alone. There is no comparison-dependent selection.

Finally apply the objectwise signed tensor-system compiler with the other physical tested mode designated. The form, field and norm data use only explicit bounded-order tensor data of polynomial total size. The compiler now retains exactly the other determinant condition on the same transporter. This proves the requested kernel reduction on the stated class. The proof is informal, with publication priority for this branch unverified. [Objectwise signed compiler](RetainedKernel.md)
