# A Koszul determinant test for one-sign tensor isomorphism

Work over F₃. Let T and S belong to U⊗V⊗W, with dimensions u,v,w and with fixed coordinate frames. Suppose

    u ≡ 1 (mod 4),   v=(u−1)w/2.

The tested determinant is on V. For every fixed constant C, on the input class below this signed comparison reduces to one ordinary tensor isomorphism instance. The input arrays are explicit and require no chosen transporter or auxiliary data.

## The square map and its relative character

Define F_T: V*⊗U → W⊗Λ²U by contracting T against the V covector and wedging its U output with the U input. The map is square since uv=w·binom(u,2). If (g_U,g_V,g_W) transports T to S, then F_S g_D = g_C F_T, where

    g_D = g_V^(−transpose) ⊗ g_U,
    g_C = g_W ⊗ Λ²g_U.

By the determinant formulas for tensor and exterior powers,

    det(g_C)/det(g_D)
       = det(g_V)^u · det(g_W)^binom(u,2) · det(g_U)^((u−1)w−v)
       = det(g_V)  over F₃.

Indeed u is odd and the other two exponents are even. If F_T and F_S are invertible, precompute their determinants. The ratio of the raw values is the tested sign of every transporter. Reject if it is negative and otherwise use the ordinary comparison. Different ranks can be rejected because of covariance.

## Extend to logarithmic corank

Write K_T=ker F_T and Q_T=coker F_T. They have a common dimension k, the corank of F_T. Compute a basis of K_T, a basis I_T of im F_T, lifts J_T of I_T in the domain, a basis of Q_T, and lifts L_T of that basis in the codomain. Use concatenated bases [K_T,J_T] and [I_T,L_T] and set

    γ_T = det[I_T,L_T] / det[K_T,J_T],

with the determinants measured in the fixed ambient frames. Compute the corresponding γ_S. A transporter of the original tensors induces K and Q maps. The common image map cancels in the block triangular determinants, giving

    det(g_V) = (γ_S/γ_T) · det(g_Q)/det(g_K).

Over F₃ the ratio of the last two determinants equals their product. Include the original tensor in an ordinary typed tensor system, with its dual, wedge-square and tensor-product maps linked by the evaluation, multiplication and wedge bilinear maps. Include F, the kernel inclusion, the quotient projection, and the exterior ladders for K and Q. The equation on F now forces the induced K and Q maps to be those of the original transporter. Their top exterior lines have one-dimensional tensor product. Mark the vector of coordinate γ_T in that line at the source and γ_S at the target. A transporter extends to the marked diagram exactly when det(g_V)=1. In corank zero use the preceding direct computation.

If k ≤ C log₂(2+L) for explicit input length L, the wedge ladders have at most 2^k total dimension each. Their dense structure constants and all remaining marks have polynomial size and tensor order at most three. The ordinary tensor-system compiler gives one explicit ordinary pair. No branch may substitute a different original transporter for the one respecting the orientation mark. [Ordinary tensor-system compiler](https://arxiv.org/html/2306.03135v2#S4) · [Prior exterior locks](https://github.com/Dugongue/MathProofs/blob/main/TensorSignIntermediateProblems/Width.md)

## An infinite full-rank family

Take w=2 and v=u−1. With coordinate bases write

    T = Σ_{i=1}^{u−1} v_i ⊗ (e_i⊗f₁ + e_{i+1}⊗f₂),

up to reordering the roles. A kernel element of F_T has columns x_i∈U, and satisfies Σ_i e_i∧x_i=Σ_i e_{i+1}∧x_i=0. Its coefficient matrix X has zero first and last rows. The upper square block and the lower square block are symmetric, the latter after subtracting one from its row index. For j≤u−1 and i≥2 the two symmetries imply X_{j,i}=X_{j+1,i−1}. The first column vanishes by the upper symmetry and the zero first row, and the last row vanishes as well. Induction along the recurrence gives X=0. Thus the square map is invertible. For any even w, partition W into two-dimensional summands and V into corresponding (u−1)-dimensional summands, then take the sum of these tensors with U shared. The map F_T decomposes into the invertible maps just checked. This yields full-rank examples with all three modes unbounded.

This is an informal proof on the stated shape and corank regime. It supplies no universal change of shape or rank.
