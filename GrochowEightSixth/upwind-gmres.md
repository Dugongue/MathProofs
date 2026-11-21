# GMRES for one-way coupled transport channels

[Simons Workshop Problem 2.13](https://arxiv.org/html/2602.05394v3#S2.SS5) asks for a nonsymmetric model in which spectral clustering predicts GMRES convergence. The following one-way coupled upwind discretization has m eigenvalue clusters and a uniform m-step residual contraction, including defective matrices.

Let S be the down-shift on N spatial grid points with an inflow boundary, and T=I−σS for 0<σ≤1. Take m channels. In their block ordering let the diagonal blocks be T(λ_i I+E_i), with distinct positive λ_i, and let the off-diagonal blocks be TC_ij for j>i, with all others zero. This is an upwind sweep in each channel with one-way coupling and a small within-channel perturbation. Applying diag(T,…,T)⁻¹ uses m forward substitutions. The preconditioned matrix is B=B₀+E, where B₀ is block upper triangular with scalar diagonal blocks λ_i I and E=diag(E_1,…,E_m). If ‖E‖≤η, the eigenvalues lie in disks of radius η about λ_i by block triangularity. Disjoint disks each contain N eigenvalues, with multiplicities.

The polynomial p(z)=∏_i (1−z/λ_i) annihilates B₀. The first i block coordinates form an invariant filtration, and B₀−λ_i I lowers its i-th level. Apply the factors from i=m down to 1, using their commutativity. For the perturbed matrix, set L=‖B₀‖+η and telescope products one factor at a time. Each factor has norm at most 1+L/λ_i, and each replaced factor differs by at most η/λ_i. Thus
$$
\|p(B)\|\le\eta\sum_{i=1}^m\lambda_i^{-1}\prod_{j\ne i}(1+L/\lambda_j).
$$
Whenever the right side is below θ<1, GMRES reduces every left-preconditioned residual by factor θ in m steps. Taking powers of p, or restarting GMRES every m steps, gives a geometric bound per cycle. Norm bounds independent of N therefore give convergence independent of the grid size. In the unperturbed model, a residual with nonzero component at every eigenvalue requires at least m steps by the root count. The invariant filtration, with one scalar action on each successive quotient, accounts for the relation between clusters and the convergence guarantee.

# The GMRES transition in an upwind model with reaction

For the following one-dimensional convection–diffusion–reaction model, [Workshop Problem 2.14](https://arxiv.org/html/2602.05394v3#S2.SS5) has an exact residual curve and an identifiable transition from algebraic to geometric decay. Let a>b≥0 and γ≥0. Take an N-point tridiagonal matrix A with diagonal c=a+b+γ, subdiagonal −a, and superdiagonal −b. Start GMRES from zero with right-hand side e₁.

The nonzero subdiagonal implies that the Krylov space in step k is spanned by e₁,…,e_k for k<N. The images of these k coordinates are independent and lie in the first k+1 coordinates. Their perpendicular in that space is spanned by w with w₀=0 and w₁=1, where
$$
a w_{j+1}=c w_j-b w_{j-1},\qquad
\|r_k\|_2=\left(\sum_{j=1}^{k+1} w_j^2\right)^{-1/2}.
$$
The residual formula follows by projecting e₁ onto this line. Write r₊>r₋ for the roots of a r²−c r+b=0. Then w_j=(r₊^j−r₋^j)/(r₊−r₋), with r₊≥1 and 0≤r₋/r₊≤b/a. Thus, for b/a bounded away from one,
$$
\|r_k\|_2\asymp\left(\sum_{j=0}^{k}r_+^{2j}\right)^{-1/2},
$$
with constants independent of the grid size. Before (k+1) log r₊ reaches one, the residual behaves as (k+1)^(−1/2). Afterward it behaves as √(1−r₊^(−2))r₊^(−k). When γ=0, r₊=1 and the algebraic phase persists until exact termination. When γ>0, the relation a(r₊−1)(r₊−b/a)=γ r₊ gives γ/a≤r₊−1≤γ/(a−b). For small γ/(a−b) with b/a bounded away from one, the crossover is therefore at order (a−b)/γ steps if the grid is long enough. The matrix is nonsingular. For b>0 it is similar by a diagonal scaling to the symmetric tridiagonal matrix with off-diagonals −√(ab), which has positive spectrum since a>b. The case b=0 is triangular with positive diagonal.

Eigenvalues and the best eigenbasis condition number together do not determine this residual behavior. Take b>0 and γ=0 and compare A with A-transpose for the same inflow right-hand side. Reversing coordinates gives an orthogonal similarity, so their eigenvalues and eigenbasis conditioning agree. The roots for A are 1,b/a and the phase is algebraic. For the transpose they are a/b,1, giving geometric decay by the same exact recurrence. The alignment of the right-hand side with the directional stencil matters. The result concerns this explicit upwind model. The separate SUPG configuration cited by the workshop has other parameters and boundary conditions.
