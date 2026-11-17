# Deterministic signed comparisons for cube-zero multiplication with small square

Work over F₃ throughout. An odd automorphism test asks whether an order-three tensor has a stabilizer whose map on a designated mode has negative determinant. A one-sign comparison asks for a transporter with positive determinant in one designated mode.

**Theorem.** Fix a constant C. Consider raw tensors isotopic to multiplication tables of local unital associative algebras R with scalar residue R/J=F₃ and J³=0, where J is the radical. If w=dim J² is at most C sqrt(log(2+L)), with L the written input length, both the relative one-sign comparison and the odd-automorphism test can be decided deterministically in polynomial time. The two algebra inputs in a relative comparison may have independent raw frames. There is no bound on dim J/J². Consequently, when either input belongs to this family, the conjunction of an arbitrary relative one-sign comparison and an independent odd-automorphism test reduces to a single one-sign instance. This is an informal proof.

## 1. Recover and enumerate only the square of the radical

Use constructive fixed-label module isomorphism to recover multiplication and its three calibrated frames, as in the companion result. Compute J and J² and check the stated conditions. Write W=J², and V=J/J². Since J³=0, products in J factor uniquely through a bilinear map b:V×V→W, and this map has image spanning W. In choice of complements the algebra is F₃1⊕V⊕W, with its only radical products given by b. All statements preserve arbitrary noncommutative b.

An algebra isomorphism induces invertible g:V→V′ and h:W→W′, satisfying b′(gx,gy)=h b(x,y). Conversely every such pair extends by its block actions and the identity on the unit. The determinant of the algebra isomorphism in the lifted filtration basis is det(g)det(h), regardless of any shears. An isotopy of unital associative multiplication consists of an algebra isomorphism and independent unit multiplications on the left and right. In a local scalar-residue algebra a unit acts on each radical grade by its residue scalar. If dim R is even, each such action is positive. If it is odd, a scalar −1 unit supplies either sign in any single designated mode. Include the product of the source/target raw frame determinants on the tested mode.

For equal w, enumerate the at most 3^(w²) invertible matrices h. Turn b′(gx,gy)=h b(x,y) into a fixed-label tuple congruence problem over F₃ by taking coordinates of W′, with h b as the other tuple. Apply the next section to obtain the exact determinant image of g on every feasible h. This decides all ordinary and signed possibilities, with the appropriate raw basis correction. The odd automorphism test is the same computation on a self-pair with the requested sign negative.

## 2. Determinant-sensitive simultaneous congruence

This step takes two arbitrary same-length tuples of square matrices B_i and C_i, including nonsymmetric matrices. It finds an isometry between the tuples if one exists and computes all determinant signs of their isometries. The field is fixed. Mismatched dimensions or bilateral common radical dimensions reject. The bilateral common radical is the intersection of all the kernels of B_i and B_iᵗ, and analogously on the target. On equally sized radical quotients continue with the nondegenerate tuple of all B_i and B_iᵗ. Any quotient isometry lifts across the radical, by choosing bases and arbitrary maps on the radical. When its dimension is positive the two determinant signs are both possible, independently of the reference quotient witness. Thus only the zero-common-radical case needs an isometry sign calculation.

### Obtain one reference solution

Find invertible P,Q with

    Pᵗ B_i Q = C_i,    Pᵗ B_iᵗ Q = C_iᵗ

for every i, using ordinary constructive fixed-label left-right equivalence. This is a two-vertex module isomorphism with all original and transposed arrows listed. A congruence would give such a pair. If the pair exists, put D=Q P⁻¹ and let E be the adjoint algebra of the transpose-closed source tuple. Its first projection is the algebra of matrices z having a partner z* with (z*)ᵗ B_i=B_i z and (z*)ᵗ B_iᵗ=B_iᵗ z. Both projections are faithful, because a vanishing projection would force the other to act trivially against the entire transpose-closed tuple. The partner is unique. Closure under multiplication and transpose of the equations give an involution on this represented algebra. Transposing the second left-right equation gives Dᵗ B_i=B_i D, and transposing the first gives the corresponding equation for B_iᵗ. Thus D is a self-adjoint unit in E.

An isometry g from the C-matrices to the B-matrices has gᵗ B_i g=C_i. With z=gP⁻¹ this becomes zᵗ B_i z=B_iD and zᵗ B_iᵗ z=B_iᵗD. These equations give z∈E with z*=Dz⁻¹. Conversely a solution z∈E of z*z=D gives the isometry g=zP. This keeps the same sign on all tuple entries.

Compute the radical N of E and its represented semisimple quotient. It has the induced involution. For a pair of simple factors exchanged by the involution the equation z*z=D is solved by choosing the first component invertible and solving for the second. Each remaining fixed factor is orthogonal, symplectic, or unitary over a finite field and gives the corresponding nondegenerate classical form isometry problem. These problems are deterministic polynomial time in fixed characteristic, with explicit isometries. The lifting algorithm for the norm equation then finds a solution in E if and only if it found one in the quotient. This uses the finite-field algebra construction and norm lifting of Ivanyos and Qiao. The mixed tuple has been handled by the transpose-closed derivation above, so the hypothesis of a preexisting congruence theorem for tuples of mixed types is unnecessary. [Ivanyos and Qiao, Theorem 18, Proposition 23 and the semisimple form algorithms](https://arxiv.org/html/1708.03495)

### Compute the attainable sign changes

The isometry group of the B-tuple is precisely the set of E-units u with u*u=1. Its image is the entire unitary group of the semisimple quotient. In fact lift a quotient unit to x. Then x*x lies in 1+N. If (x*x−1) has nilpotence index r, choose 3^k≥r. The unit x*x has order dividing 3^k, so its inverse square root is an integer power of x*x and is self-adjoint. Right-multiply x by this inverse square root and it becomes unitary with the same quotient image. The kernel lies in 1+N and has determinant one, because all radical elements act nilpotently on the represented space.

On the radical filtration of the represented space, record the multiplicity m_i of the natural simple module of each factor Mat_(d_i)(K_i) in E/N, summed over all grades. These are computable integers. A quotient unit z_i contributes Norm_(K_i/F₃)(det_(K_i) z_i)^(m_i). This follows by choosing bases on the semisimple grades and using block triangularity.

* On an exchanged pair of factors, the two norm determinants are inverse, since the anti-isomorphism of field matrix algebras preserves the ground-field norm determinant. There is an odd contribution exactly when m_i+m_j is odd, because the finite-field norm is onto.
* On a fixed orthogonal factor the determinant over K_i can be either sign. A reflection of a vector of nonzero norm gives the negative one. Its ground-field contribution is odd exactly when m_i[K_i:F₃] is odd.
* A fixed symplectic factor has determinant one. On a fixed unitary factor the determinant has norm one to the fixed field, hence to F₃. Both contributions are positive.

The quotient factors and their involution types are available from the same fixed-characteristic algebra algorithms. This gives an exact odd-isometry test. The whole set of relative signs is the sign of one reference solution multiplied by this character image, by composition with source isometries. All polynomial bounds are in the explicit tuple size. [Classical factor types and finite-field algorithms](https://arxiv.org/html/1708.03495)

## 3. Consequences for one query

The runtime of the whole local-algebra decision procedure is 3^(w²) times a polynomial in L, so it is polynomial in the asserted range. The reduction can decide either eligible input before constructing its output. If the eligible input is the automorphism condition and it is true, return the other input. If the eligible input is the ordinary relative one-sign condition and it is true, use the unrestricted odd-automorphism test as a one-sign self-pair with reflected target. In both cases a false eligible input gives a fixed negative one-sign instance. All maps use the same raw frame sign conventions as the original problems.

This applies to cube-zero algebras whose tangent quotient dimension grows arbitrarily. For example, every scalar-valued bilinear radical multiplication is included, regardless of radical degeneracy or symmetry. The general cube-zero encoding of the unrestricted odd-automorphism problem allows J² to grow far beyond the bound above. The determinant-sensitive fixed-label procedure does not give a polynomial enumeration of the full output action there. [Raw multiplication recognition and the cube-zero reduction](OddAutomorphisms.md)
