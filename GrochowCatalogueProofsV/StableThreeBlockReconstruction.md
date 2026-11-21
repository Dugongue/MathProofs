# Stable reconstruction of identifiable three-block depth-three circuits

## GP-0561

Let a real set-multilinear degree-three circuit have coefficient tensor $T=\sum_{h=1}^r u_h\otimes v_h\otimes w_h$. Supply index sets $I,J$ of size $r$ in the first two blocks and third-block coordinates $k_0,k_1$. In some scaling of the decomposition assume $(w_h)_{k_0}=1$ for all $h$. The matrices $U,V,W$ of factors have operator norm at most a supplied $B\ge2$, the smallest singular values of $U_I,V_J$ are at least $B^{-1}$, and the numbers $(w_h)_{k_1}$ have pairwise separation at least $B^{-1}$. Then approximate evaluations at polynomial bit precision suffice for deterministic bit-polynomial recovery to final precision $\epsilon$ in a specified scaling, up to permutation. The time is polynomial in the tensor format size $N$, $r$, $\log B$, and $\log(1/\epsilon)$. This is an identifiable three-block model, with the two observable slice indices supplied.

Each coefficient is one evaluation, with one unit vector in each block. Let $A_k=T_{I,J,k}$ and $A_0=A_{k_0}$. Put $M=A_{k_1}A_0^{-1}$. Then $A_k A_0^{-1}=U_I\operatorname{diag}((w_h)_k)U_I^{-1}$ and the eigenvalues $\lambda_h$ of $M$ are $(w_h)_{k_1}$. Its rank-one projectors are
$$
P_h=\prod_{j\ne h}\frac{M-\lambda_j I_r}{\lambda_h-\lambda_j}.
$$
Thus $(w_h)_k=\operatorname{tr}(P_h A_k A_0^{-1})$. With $C_0=T_{*,J,k_0}$ and $D_0=T_{I,*,k_0}$, the first-two-mode matrix is
$$
R_h=C_0 A_0^{-1} P_h D_0=u_hv_h^{\mathsf T}.
$$
These identities follow by substituting $P_h=U_I E_{hh}U_I^{-1}$ and $A_0=U_I V_J^{\mathsf T}$.

If the error in each coefficient is at most $\delta$, every perturbed slice differs in norm by at most $N\delta$. Since $\|A_0^{-1}\|\le B^2$, the perturbed reference inverse has norm at most $2B^2$ for $N\delta B^2\le1/2$, and its difference from the reference inverse is at most $2N\delta B^4$. Conjugate the perturbed pencil matrix $\widetilde M$ by $U_I$. It differs from the exact diagonal matrix by at most $\operatorname{poly}(N,B)\delta$. Gershgorin's theorem gives disjoint disks about the true eigenvalues of radius $\operatorname{poly}(N,B,r)\delta$, each containing one simple eigenvalue, for sufficiently small $\delta$. Each eigenvalue is real because the perturbed matrix is real and the disks are invariant under conjugation. Compute the rational characteristic polynomial and isolate its real roots to error at most $\delta$ by polynomial-bit root isolation. Sorting matches them to the exact eigenvalues.

The denominators in the projector formula have magnitude at least $1/(2B)$. A telescoping expansion of its products bounds each projector error by $(N+B+r+2)^{O(r+1)}\delta$: each changed factor has error at most a polynomial times $\delta$, and each other factor has polynomial norm. Traces and the $R_h$ formulas preserve this bound. Taking a greatest-magnitude entry of the computed $R_h$ gives a pivot of exact magnitude at least $B^{-2}/(2N)$, since each exact $u_h,v_h$ has norm at least $B^{-1}$ and sufficiently small errors preserve a pivot of this size. Use the pivot column and the pivot row divided by the pivot as the recovered first two factors. This division adds only a polynomial error factor. Consequently $\delta=\epsilon(2+N+B+r)^{-C(r+1)}$ for a sufficiently large absolute constant $C$ suffices for factor and term accuracy $\epsilon$. All intermediate rational computations have polynomial bit lengths, using common denominators per matrix and telescoping the bounds on numerators of products of at most $r$ matrices. This gives the claimed bit complexity with a precision-parameterized evaluation oracle.

The argument makes the spectral separation and slice conditioning explicit. [Low-rank tensor reconstruction context](https://arxiv.org/abs/2105.01751) · [Prior orbit-distance and spectral estimates](https://github.com/Dugongue/MathProofs/blob/f1a463ce1a77aa494b7d33b81a4cbaac5dcb708b/GrochowCatalogueProofsIV/OrbitDistanceHardness.md)
