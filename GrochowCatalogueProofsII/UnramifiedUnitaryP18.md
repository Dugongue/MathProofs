# GP-0103 · Unitary P18 recovery over unramified quadratic local rings

**Theorem.** Let $R=\operatorname{GR}(p^e,2)$ be the unramified quadratic extension of $\mathbb Z/p^e\mathbb Z$, given in polynomial-basis coordinates with its nontrivial involution. For tensors with all modes at least two and median side $b$ above an absolute cutoff, there is a polynomial-time recognizable source class of density $1-O((1+\log b)/\sqrt b)$ under uniform sampling. The estimate is uniform in $p,e$, including $p=2$. For any recognized source and any target the standard product-unitary orbit problem has a deterministic polynomial-bit-time algorithm returning a transporter when one exists. All arguments for ring precision are written proofs.

## Unit scalar norms and Hermitian frame images

Write $\dagger$ for the conjugate transpose, and $k=\mathbb F_{p^2}$ for the residue field. Its trace $\operatorname{Tr}_{k/\mathbb F_p}(x)=x+\bar x$ is onto. The norm on residue units is onto. For odd $p$, take a nonzero trace-zero generator obtained by subtracting the conjugate of the supplied quadratic generator from it. Its square $\delta\in\mathbb F_p^\times$ is a nonsquare. Van de Woestijne's deterministic algorithm for a ternary diagonal quadratic gives a nonzero solution of $x^2-\delta y^2-d z^2=0$ in time polynomial in $\log p$. Since the binary norm is anisotropic, every nonzero solution has $z\ne0$. Divide through by $z$ to solve the desired norm equation. At $p=2$ the residue field is fixed. A solution of the norm equation modulo $p^t$ lifts to the next digit by multiplication by $1+p^t z$. Its norm is multiplied by $1+p^t\operatorname{Tr}(z)\bmod p^{t+1}$. Solve the resulting linear trace condition at each step. This proves constructive norm surjectivity at all precisions.

For any same-sized $H,D$ over $R$, consider $QH=D$ with $Q^\dagger Q=I$. Smith elimination on $H$ gives an invertible column transformation and a basis $u_i$ of its row-coordinate space with nonzero columns $p^{a_i}u_i$, $0\le a_i<e$, in transformed coordinates. Apply the column transformation to $D$, require zero at every paired zero and divisibility by $p^{a_i}$ at each paired nonzero column. Divide, and call the resulting marked vectors $v_i$ with required precisions $b_i=e-a_i$. Their lifts are arbitrary subject to those precisions. Require
$$
u_i^\dagger u_j\equiv v_i^\dagger v_j \pmod {p^{\min(b_i,b_j)}}
$$
for every pair. Also require that the $\bar v_i$ are linearly independent. These are necessary and sufficient tests.

Over the residue field the marked map $\bar u_i\mapsto\bar v_i$ therefore extends to a unitary matrix. A constructive proof splits off a nonsingular part of the restricted Hermitian form and treats the radical as a totally isotropic span. Pick partners of a basis of that span by solving the linear pairing equations. Adjust the partners inside the span to make their mutual Gram matrix zero, solving an equation $Z^\dagger+Z=W$ for the prescribed Hermitian matrix $W$. Choose off-diagonal entries one pair at a time and use the onto trace on the diagonal. This builds paired hyperbolic frames inside the two ambient orthogonal complements. Their remaining nonsingular Hermitian complements are isometric by Hermitian diagonalization and norm normalization, which also yields a matrix witness. Diagonalization finds a nonzero-norm vector in a basis or a two-basis-vector span. In the latter case a nonzero cross-pairing and the onto trace guarantee a suitable coefficient. All steps use linear algebra and the unit norm solver above.

Given a unitary residue lift $A$ solving the marked conditions to precision $p^t$, consider $A(I+p^tZ)\bmod p^{t+1}$. Let $E=(A^\dagger A-I)/p^t\bmod p$. The next unitary equations are
$$
Z^\dagger+Z=-E,\qquad
Z\bar u_i=(A^{-1}v_i-u_i)/p^t\bmod p\quad (b_i\ge t+1).
$$
On active vectors the prescribed columns determine the corresponding columns of the sesquilinear form $x^\dagger Zy$. Its adjoint equation determines the corresponding rows. Compatibility on the overlap is exactly the displayed pairwise Gram congruence at precision $p^{t+1}$. On all free off-diagonal pairs choose one entry and solve for the other. On each free diagonal solve the trace equation. Thus every previous lift has a next lift satisfying the active conditions. No extra digit of norm precision is required, even at $p=2$, because the involution is nontrivial on the residue field. Conditions at older precisions remain unchanged. Iteration constructs the exact requested $Q$.

## The tensor reduction

Order the mode sizes $a\le b\le c$, and write $A_i$ for the $a\times c$ middle-mode slices of the source tensor. Let $F_c$ be its $c$-mode flattening, and $X_b$ its $b$-mode flattening with columns ordered by $(a,c)$. Form the two lists
$$
R_t=X_b(I_a\otimes ((F_cF_c^\dagger)^t)^\top)X_b^\dagger
\quad(0\le t<c),\qquad Z_{ij}=A_iA_j^\dagger .
$$
The first list is the transpose-adjusted partial-trace contraction of $F_c^\dagger(F_cF_c^\dagger)^tF_c$. On residue it is exactly the list in the existing P18 source predicate. The second list is the existing cross-Gram family. The source test is that the reductions generate the full matrix algebras of sizes $b$ and $a$, respectively. The prior P18 density proof for this exact predicate gives the stated uniform bound, since uniform tensors over $R$ reduce uniformly to the residue field. Its two relevant declarations are Mathproof.Problem18LargeRootPredicate20261001.RawGood and Mathproof.Problem18LargeRootDensity20261001.large_density_package. Generation is checked by expanding the linear span of words until stable, inside a matrix space of polynomial dimension. A residue basis of matrix words also forms a basis over $R$ by its unit determinant. The new lift uses these checked field ingredients and does not claim a Lean proof of the local-ring theorem.

For unitary changes $P,Q,S$ on the $a,b,c$ modes, the first list transforms by $R_t\mapsto QR_tQ^\dagger$. Indeed $X_b$ changes by $QX_b(P\otimes S)^\top$, and the inserted Gram transforms by $S(F_cF_c^\dagger)S^\dagger$. These factors cancel across the product using $P^\top\overline P=S^\top\overline S=I$. The cross-Gram list transforms by conjugation by $P$ and invertible mixing of the $i,j$ labels. Thus the test is unitary-invariant.

Solve all ordered first-list intertwining equations $X R_t(A)=R_t(B)X$ over $R$. They are linear congruences with polynomial-size solutions in the displayed ring coordinates. Test solution-module generators for a nonzero residue. Every nonzero residue solution is invertible because its kernel is invariant under the full source matrix algebra. If no solution generator has a nonzero residue, there is no invertible transporter. Any chosen invertible solution $X$ gives $X^\dagger X=d_b I$ for a fixed unit $d_b=\bar d_b$, because each $R_t$ is Hermitian and the commutant of the source algebra consists of scalars. Any other invertible solution differs by a unit scalar. Undo $X$ on the $b$ mode of the target and call the resulting slices $Y_i$. For an actual unitary transporter with $b$-factor $\beta X$ we have $\bar\beta\beta=d_b^{-1}$ and
$$
d_bY_iY_j^\dagger=PZ_{ij}P^\dagger .
$$
Solve the corresponding ordered intertwining equations for $P_0$. The same full-generation argument produces an invertible solution or rejects. Taking conjugate transpose exchanges the $i,j$ equations, so every invertible solution is a scalar multiple of $P_0$ and $P_0^\dagger P_0=d_aI$.

Choose scalar norm roots $\bar\alpha\alpha=d_a^{-1}$ and $\bar\beta\beta=d_b^{-1}$ as above. The remaining transporter equation is precisely a frame problem on the $c$ mode, after applying $\alpha P_0$ and $\beta X$ in the first two modes of the source. Other allowed choices of scalar roots have ratios of norm one, which can be absorbed into the $c$-factor. Hence this fixed choice loses no transporter. Apply the frame algorithm, then check the resulting three matrices and tensor identity directly. The matrix linear solves, field and ring arithmetic, and number of precision stages have polynomial bit complexity.

[Lean-checked P18 finite-field source and density](https://github.com/Dugongue/MathProofs/tree/ef3248c44a28fcc2e97f90392942083b33dce716/Problem18) · [Earlier bilinear dyadic precision lift](https://github.com/Dugongue/MathProofs/blob/ef3248c44a28fcc2e97f90392942083b33dce716/Problem18FurtherExtensions/DyadicPrecisionOrthogonalTensorIsomorphism.md) · [Primary finite-field problem](https://arxiv.org/html/2604.00591v2)

[Van de Woestijne, deterministic diagonal equation solving](https://math.leidenuniv.nl/scripties/Woestijne.pdf)
