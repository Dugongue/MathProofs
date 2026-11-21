# Two scalar probes reduce ambient orientation on a class of square-zero spaces

[Earlier square-zero equivalence](earlier/SquareZeroClosure.md) · [Prior weighted carrier](earlier/baseline/baseline/earlier/CubeZeroAndExtensions.md) · [Earlier ordinary compilation](earlier/baseline/baseline/LinearSwitchCompiler.md)

Take the square-zero carrier \(\mathcal S(A_\beta)\) on \(A_\beta^2\oplus A_\beta\) with \(A_\beta=\mathbf F_3 1\oplus X\oplus Z\), \(xy=\beta(x,y)\) on \(X\), and \(JZ=0\). The input uses the displayed based form, \(\beta\) is symmetric with spanned output and zero common radical, \(\dim X\) is even, and \(\dim Z\) is odd. The carrier's ambient determinant equals the determinant of the induced algebra isomorphism, because regular multiplication by units has determinant one in the even algebra dimension. On the two radical grades the determinant is \(\det g\det h\), where \((g,h)\) is one bimap equivalence \(h\beta(x,y)=\beta'(gx,gy)\). Each bimap equivalence lifts by fixing the unit, and changing the grade lifts only creates shears of determinant one. This work gives deterministic one-query compilers on additional explicit classes. It does not settle the unrestricted square-zero question.

## A one-query criterion with logarithmic output and selected primary multiplicities

Let \(L\) be the input bit length. Suppose \(\dim Z=O(\log L)\) and there are covectors \(\alpha,\gamma\in Z^*\) such that \(q_0=\alpha\beta\) is nonsingular. Define the self-adjoint operator \(D=q_0^{-1}q_1\), where \(q_1=\gamma\beta\) and matrices are written so \(q_1(x,y)=q_0(Dx,y)\). For each irreducible factor \(f\) of the characteristic polynomial of \(D\), put \(E_f=\mathbf F_3[t]/(f)\). On its primary space, require that the number of indecomposable blocks of length \(j\) is \(O(\log L)\) whenever \(\deg f\) and \(j\) are both odd. There is no bound on even-degree primary multiplicities, even-length multiplicities, individual field extension degrees or ambient dimension. On this recognizable domain, ambient determinant-one conjugacy of the square-zero carrier deterministically reduces to **one** ordinary TI comparison.

Choose qualifying source covectors by enumerating pairs and factoring their operators. Fixed-field polynomial factorization and module calculations are deterministic in polynomial time. For every pair of target covectors \(\alpha',\gamma'\), form an ordinary pinned comparison
\[
 h\beta=\beta'(g,g),\qquad \alpha'h=\alpha,\qquad\gamma'h=\gamma .
\]
A true comparison forces \(g\) to be a simultaneous isometry of the two ordered scalar forms and to intertwine their operators \(D,D'\). Reject trivially incompatible types. Each matrix of a bilinear form and covector equation is of order at most three as a typed tensor, so these are ordinary comparisons with the original actual \(g,h\) shared. A true ordinary witness occurs in exactly the branch corresponding to the transported input covectors. The following refinements impose \(\det g\det h=1\) within each branch. [Berlekamp, factoring polynomials over finite fields](https://doi.org/10.1090/S0025-5718-1967-0220736-1).

### Intrinsic filtration of a primary space

For one primary factor \(f\), write \(F=f(D)\) on \(X_f\). Define
\[
 W_{f,j}=\frac{\ker F^j}{\ker F^{j-1}+F\ker F^{j+1}}.
\]
This is canonically an \(E_f\)-space. Indeed \(D\) acts, and \(f(D)\) acts trivially. In a cyclic module decomposition over \(\mathbf F_3[t]\) this quotient keeps exactly one copy of \(E_f\) for each summand \(\mathbf F_3[t]/(f^j)\), while shorter and longer summands contribute zero. Thus \(m_{f,j}=\dim_{E_f}W_{f,j}\) is exactly the multiplicity of length \(j\). The quotient and the \(E_f\)-action are obtained by ordinary linear algebra.

For every \(u\ge0\) filter \(F^uX_f/F^{u+1}X_f\) by the images of \(F^u\ker F^j\) for increasing \(j\). For \(j>u\), the successive quotient at \(j\) is canonically identified with \(W_{f,j}\) by \(F^u\). To verify well-definedness and injectivity, test on \(\mathbf F_3[t]/(f^\ell)\). If \(\ell<j\), its image is already present at \(j-1\). If \(\ell>j\), its contribution lies in \(F^{u+1}X_f\). For \(\ell=j\) the induced map is the canonical copy \(E_f\to f^u/(f^{u+1})\) and is an isomorphism for \(u<j\). For \(j\le u\) there is no contribution. These identities verify the canonical map without making any choice part of the constraint.

It follows that for any intertwiner \(g\) matching primary structures,
\[
 \det_{\mathbf F_3}(g)
  =\kappa_X
    \prod_f\prod_{j\ge1}
       N_{E_f/\mathbf F_3}\!\left(\det_{E_f}g_{f,j}\right)^j ,
 \tag{1}
\]
where \(g_{f,j}:W_{f,j}\to W'_{f,j}\) is the induced \(E_f\)-linear map. Use the same chosen \(E_f\) model and basis on the two endpoints. The calibration \(\kappa_X\) is the ratio of the determinants of the raw ordered adapted bases. It is computable without a witness by taking lifts in the displayed primary and quotient filtrations, using \(F^u\) of the chosen bases of \(W_{f,j}\) on every repeated grade. Block triangular determinants multiply along the filtrations, each \(W_{f,j}\) occurs \(j\) times, and the prime-field determinant of an \(E_f\)-linear map is the norm of its \(E_f\) determinant. Even \(j\) therefore contribute \(+1\) in (1).

### Even extension degrees give fixed signs, regardless of multiplicity

Distinct primary spaces are \(q_0\)-orthogonal. For \(x\in X_f,y\in X_{f'}\), \(f\ne f'\), a large power of \(f(D)\) kills \(x\) and is invertible on \(X_{f'}\). Move that self-adjoint operator across the pairing to get zero. Consequently the restriction of \(q_0\) to \(X_f\) is nonsingular.

The bilinear form
\[
 b_{f,j}([x],[y])=q_0(F^{j-1}x,y)
\]
is well-defined, symmetric and nonsingular over \(\mathbf F_3\) on \(W_{f,j}\). Terms from \(\ker F^{j-1}\) pair to zero. For a term \(Fv\) with \(v\in\ker F^{j+1}\) the relevant form becomes \(q_0(F^jv,y)=q_0(v,F^jy)=0\). To check nonsingularity, the condition \(q_0(F^{j-1}x,\ker F^j)=0\) is \(F^{j-1}x\in\operatorname{im}F^j\) by self-adjointness and nonsingularity. If \(F^{j-1}x=F^jv\), then \(F^{j+1}v=F^jx=0\) and \(x-Fv\in\ker F^{j-1}\). This is exactly the stated denominator.

Because \(D\) is self-adjoint, \(b_{f,j}\) is balanced for the \(E_f\)-action. There is a unique \(E_f\)-bilinear nonsingular symmetric form \(B_{f,j}\) defined by
\[
 \operatorname{Tr}_{E_f/\mathbf F_3}\bigl(aB_{f,j}(v,w)\bigr)
    =b_{f,j}(av,w)\quad(a\in E_f).
\]
Trace nondegeneracy gives uniqueness and construction, and balance implies symmetry and bilinearity. Nonsingularity follows from that of \(b_{f,j}\). The induced map \(g_{f,j}\) is an isometry of these \(E_f\)-forms. In chosen \(E_f\)-bases, let \(R_{f,j}\) be the determinant of the source Gram matrix divided by that of the target. Thus \((\det_{E_f}g_{f,j})^2=R_{f,j}\). For \(e=\deg f\) even,
\[
 N_{E_f/\mathbf F_3}(\det_{E_f}g_{f,j})
    =R_{f,j}^{(3^e-1)/4}.
 \tag{2}
\]
In particular this is computable from endpoint tables, including at unbounded \(m_{f,j}\). If the determinant ratio is a nonsquare, the branch has no isometry and can be discarded. Equations (1)–(2) are frame exact, and no square-root choice is used.

### Ordinary tensor-system implementation

For odd \(e\) and odd \(j\), include the quotient fibers \(W_{f,j}\), the projection maps from the kernels, and the \(E_f\)-action. These are based computed spaces and actual intertwiner constraints, so their induced maps are forced by the same \(g\). Their \(E_f\)-ranks are \(O(\log L)\). Attach \(\Lambda^*_{E_f}W_{f,j}\) by exterior multiplication and a degree-one link. Its dimension over \(\mathbf F_3\) is \(e\,2^{m_{f,j}}\), polynomial even for large extension degree. The top line moves by multiplication by \(d=\det_{E_f}g_{f,j}\), in chosen endpoint frames. Create copies of that line linked by \(z\mapsto z^{3^r}\) for \(0\le r<e\), all \(\mathbf F_3\)-linear maps. Then use ordinary bilinear multiplication chains to combine all copies, forcing the product line to move by \(\prod_{r<e}d^{3^r}=N(d)\). Restrict that line to its \(\mathbf F_3\)-subspace using an inclusion map, which is respected because the norm is in \(\mathbf F_3^\times\). This extracts a one-dimensional sign. Fixed field identifications across the endpoints are used because the probes fix the operator \(D\), hence preserve its specified \(E_f\)-action itself. There is no additional semilinear ambiguity.

Attach the exterior algebra of the small \(Z\)-space to extract \(\det h\). Multiply these sign lines, pinning the prescribed scalar given by the inverse of the known \(\kappa_X\) and (2) factors. A scalar line with multiplication fixes its unit. Linking that unit to the last sign line with the appropriate endpoint scalar imposes the condition, so every auxiliary map is an ordinary change of basis. All required tensors have order at most three and polynomial total description length, even if the number of primary factors and lengths varies. The atlas's polynomial packing of typed systems applies, followed by its balanced OR across the polynomially many target probe pairs. A signed bimap equivalence lifts to its actual branch with all these signs. A typed YES witness retains the original bimap comparison and equation (1) forces its total sign. This proves both directions and the stated one-output bound. [Tensor-system comparison](https://arxiv.org/html/2306.03135v2#S4).

**Unbounded multiplicity example.** Take \(X=\mathbf F_9^r\), \(Z=\mathbf F_3^3\), and let \(q_0(x,y)=\operatorname{Tr}_{\mathbf F_9/\mathbf F_3}\sum x_i y_i\), \(q_1(x,y)=q_0(\omega x,y)\) for \(\omega\notin\mathbf F_3\). Add the third scalar form \(q_2(x,y)=\lambda(x)\lambda(y)\) for a nonzero ternary linear functional \(\lambda\), and set \(\beta=(q_0,q_1,q_2)\). Their span has dimension three since each nonzero combination of \(q_0,q_1\) is nonsingular, and \(q_2\) has rank one. This bimap has zero common radical and spanned output and meets the carrier's parity conditions. The pure degree-two, length-one primary of \(D\) has multiplicity \(r\), which need not be logarithmic. Equation (2) avoids introducing its exterior algebra.

## A separate determinant-line criterion from the graded Koszul complex

For fixed \(s\ge2\), the bimap defines an equivariant complex
\[
 \Lambda^s X\longrightarrow X\otimes\Lambda^{s-1}X
       \longrightarrow Z\otimes\Lambda^{s-2}X
\]
with the standard alternating Koszul differentials, the second using \(\beta\) on the first factor. The composite is zero by symmetry of \(\beta\), and the first map is injective because the sets of nonzero basis positions of the images of distinct basis wedges are disjoint. Write \(H_\mathrm{mid}\) and \(H_\mathrm{end}\) for the middle and terminal homology. With \(n=\dim X\) even and \(\dim Z\) odd, the alternating determinant line of this complex has character
\[
 (\det g\det h)^{\binom{n}{s-2}\bmod2}.
\]
For \(s=2\) omit the zero exponent \(\binom{n-1}{-1}\). To check the formula for all \(s\), use \(\det(\Lambda^r g)=(\det g)^{\binom{n-1}{r-1}}\) and \(\det(P\otimes Q)=\det(P)^{\dim Q}\det(Q)^{\dim P}\), reducing exponents modulo two. The \(h\)-exponent is \(\binom{n}{s-2}\). The \(g\)-exponent is
\(\binom{n-1}{s-1}+\binom{n}{s-1}+\binom{n-1}{s-3}=\binom{n}{s-2}\pmod 2\)
by Pascal's rule. Exact sequences splitting the kernels, images and homologies express the alternating determinant as the product of the signs on \(H_\mathrm{mid},H_\mathrm{end}\), up to a computable endpoint frame ratio.

Thus whenever \(\binom{n}{s-2}\) is odd and both homology groups have dimension \(O(\log L)\), the ambient sign is compiled into one ordinary TI query without bounding \(\dim Z\). Compute the homology spaces by Gaussian elimination and force their induced maps by typed inclusions and projections. For fixed \(s\), all required exterior spaces of \(X\) and wedge multiplications through degree \(s\) have polynomial dimensions. Attach the top-volume lines of the two small homologies and pin their required product relative to the frame ratio. This is a sufficient criterion, with the \(s=2\) case reducing to the low-dimensional quadratic relation space. For \(s=4\) the parity condition holds when \(n\equiv2\pmod4\). This paragraph establishes the implication from small homology, without asserting an asymptotic supply of such algebras for \(s\ge4\).

## Recovering bases from unframed square-zero coefficient spaces

The same two criteria apply if the input gives raw ambient matrices promised conjugate to spaces of the displayed form, without providing the direct-sum coordinates. Compute \(W\) as the common kernel, and put \(U=V/W\). Since every original operator vanishes on \(W\) and maps into \(W\), obtain the row space \(\mathcal M\subseteq\operatorname{Hom}(U,W)\) by linear algebra. Solve the linear equations for its left idealizer \(R\subseteq\operatorname{End}(W)\). In the promised form this is the regular copy of the local algebra \(A_\beta\). Compute its radical \(I\) by deterministic finite-algebra routines. Pick any \(w\notin IW\). In the regular module this is a unit by the local-ring hypothesis, so \(R\to W\), \(a\mapsto aw\), is an isomorphism of \(R\)-modules and furnishes a regular frame.

The row space \(\mathcal M\) is a free \(R\)-module of rank two under postcomposition. Lift a basis of its two-dimensional quotient modulo \(I\mathcal M\) to two rows \(\rho_1,\rho_2\). They form an \(R\)-basis of \(\mathcal M\): in the unknown standard coordinates their coefficient matrix is invertible modulo \(I\), hence invertible over the local ring. It follows that \(u\mapsto(\rho_1u,\rho_2u)\) is a linear isomorphism \(U\to W^2\). Use its inverse on the regular basis of \(W^2\) to form quotient bases. Pick arbitrary lifts to the ambient \(V\) and append the regular basis of \(W\). The resulting raw frame turns the given matrix space into the displayed square-zero carrier. Any two lift choices differ by an ambient shear of determinant one. For the recovered \(R\), split \(I/I^2\) by any linear section and use \(I^2\) for \(Z\) to read \(\beta\). These choices preserve the typed graded orientation through an explicit basis calibration. Multiply the endpoint frame determinants when moving between prescribed raw ambient sign and the sign in the displayed algebra coordinates. Thus the output sign condition can be set before any ordinary conjugator is known. [Friedl and Rónyai, finite-algebra radical routines](https://doi.org/10.1145/22145.22162).

## Limits encountered

The earlier exact entry-pin obstruction persists on endomorphism spaces of the carrier's free algebra example. In even tangent dimension \(n\) its automorphism group surjects onto \(\mathrm{GL}_n(\mathbf F_3)\). Requiring just the first diagonal entry of that induced map to be one selects a set of relative size \(3^{n-1}/(3^n-1)\). The total number of invertibles with first column fixed is constant, and precisely \(3^{n-1}\) nonzero columns have first coordinate one. The reciprocal of the fraction is not an integer for \(n\ge2\), so the set cannot be a subgroup coset. An exact typed-system projection onto the actual quotient action of the old witness cannot implement this partial constraint. This does not apply to arbitrary decision-only gadgets. The primary construction instead pins only honest covectors and uses exact induced module actions. It does not bound the output dimension or the problematic odd-degree multiplicities on arbitrary inputs.

Written proofs only. No Lean verification was run.
