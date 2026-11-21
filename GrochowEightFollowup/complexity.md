# Polynomial calculus for matrix conjugacy in small characteristic

## Exact degree four and a reduction of the worst case

Work in characteristic \(p>0\). Let \(D_p(a,b)\) be the minimum ordinary PC refutation degree for
\[
UV=I_a,\quad VU=I_b,\qquad U\in\mathrm{Mat}_{a,b},\quad V\in\mathrm{Mat}_{b,a}.
\]
Let \(C_p(N)\) be the worst-case minimum degree of the standard infeasible conjugacy systems for \(N\)-square matrices over an algebraically closed field of characteristic \(p\), with equation \(XM=M'X\) and both inverse equations. Then
\[
\max_{\substack{a,b\ge1,\ a\ne b\\a+b\le N}}D_p(a,b)
\ \le C_p(N)\ \le\
\max\!\left(3,\ \max_{\substack{0\le a,b\le N\\a\ne b}}D_p(a,b)\right).
\]
The left bound is omitted when its index set is empty, and a zero smaller side has \(D_p(a,b)=0\). If \(a,b\ge2,\ a\ne b\) and \(p\mid(a-b)\), then \(D_p(a,b)\ge4\). For \(p=2\) and \(a-b\equiv2\pmod4\), the bound is exact. The corresponding conjugacy instances also have degree exactly four, including examples in every dimension at least six by padding. The final lower-bound argument proves the matching linear worst-case order for every fixed prime. The exact degree-four family covers the first multiplicity-difference stratum invisible to binary trace. [Catalog GP157](https://github.com/Dugongue/MathProofs/blob/main/GrochowOpenProblems/COMPLEXITY.md#gp157) · [Galesi–Grochow–Pitassi–She, Open Question 7.3](https://arxiv.org/html/2305.19320#S7.SS3)

### The rectangular degree-three lower bound

Put \(U=(x_{ij})\), \(V=(y_{ji})\), \(A=UV-I_a\) and \(B=VU-I_b\). The span of the axioms has no nonzero constant. Choose a table \(w_{ij}\) with all row and column sums equal to one. Such a table exists since \(a=b\) in the field. Set \(w_{i,b}=1\) for \(i<a\), \(w_{a,j}=1\) for \(j<b\), \(w_{a,b}=2-b\), and other entries zero. The degree-two linear functional sending \(1\) to \(1\), \(x_{ij}y_{ji}\) to \(w_{ij}\), and every other nonconstant monomial to zero annihilates all the axioms.

Let \(L\) be the span of the axioms and their single-variable multiples. The axioms have degrees zero and two, and their multiples have degrees one and three. To see that no combination of multiples can leave a nonzero linear term, grade the variables by independent formal row and column weights. Give \(x_{ij}\) weight \(s_i/t_j\) and \(y_{ji}\) weight \(t_j/s_i\). Fix \(x_{uv}\). The multiples of its weight have a general combination
\[
x_{uv}\sum_i c_i A_{ii}+x_{uv}\sum_j d_j B_{jj}
+\sum_{i\ne u}e_i A_{ui}x_{iv}+\sum_{j\ne v}f_j x_{uj}B_{jv}.
\]
With \(e_u=f_v=0\), the coefficient of \(y_{ji}\) in its cubic part is
\[
(c_i+d_j)x_{uv}x_{ij}+(e_i+f_j)x_{uj}x_{iv}.
\]
If \(i\ne u\) and \(j\ne v\), the monomials are distinct. Cancellation forces \(c_i=c,\ d_j=-c,\ e_i=e,\ f_j=-e\) on these indices. The cases \(i=u,\ j\ne v\) and \(i\ne u,\ j=v\) then give \(c_u=c+e,\ d_v=-c-e\). The linear remainder is \(-(a-b)c\,x_{uv}=0\). Interchanging \(U,V\) gives the result for \(y_{ji}\). All weight components are independent.

It follows that the intersection of \(L\) with the degree-at-most-two space is exactly the axiom span. Every line in a degree-three PC proof belongs to \(L\), by induction. In the multiplication rule the input must have degree at most two, hence is in the axiom span. The constant \(1\) is outside \(L\).

### Exactness at the first binary stratum

Let \(E_2(W)\) be the sum of principal \(2\)-minors of \(W\). Cauchy–Binet gives \(E_2(UV)=E_2(VU)\). Replacing each quadratic entry in each term successively by the corresponding identity-matrix entry yields PC derivations of \(E_2(UV)=\binom a2\) and \(E_2(VU)=\binom b2\) in degree at most four. Each replacement uses an axiom times a polynomial of degree at most two, expanded into its monomials. If \(p=2\) and \(a-b\equiv2\pmod4\), the two binomial coefficients differ modulo two.

Use \(M=\operatorname{diag}(I_a,0_b)\) and \(M'=\operatorname{diag}(I_b,0_a)\). The homogeneous linear substitution \(X=\operatorname{diag}(V,U)\), \(Y=\operatorname{diag}(U,V)\) annihilates the forward intertwiner equations. The inverse equation families specialize to the two rectangular families and zero equations. Thus any conjugacy refutation transfers to a rectangular refutation in the same degree. The opposite transfer uses the two eigenspace blocks. The original equations derive the reverse intertwiner \(YM'=MY\) in degree three by expanding \(Y(XM-M'X)Y\) and applying the two inverse equations. Both intertwiners set the cross blocks to zero. Applying their linear equations to the inverse equations exposes the two rectangular inverse identities on each eigenspace block in degree at most three. Hence both degree-four bounds pass to these pairs. Additional equal zero blocks allow the identity on the padding in the lower-bound substitution, and the upper bound still uses the rectangular pair on the 1-eigenspaces.

### Reduction from arbitrary matrix conjugacy

For a module \(H\) with matrix \(M_H\), an eigenvalue \(\lambda\), and an integer \(\ell\ge1\), put \(N_H=M_H-\lambda I\) and form
\[
J_{\lambda,\ell}(H)=
\frac{\ker N_H^\ell}{\ker N_H^{\ell-1}+N_H\ker N_H^{\ell+1}}.
\]
Intertwiners induce linear maps on this quotient, compatibly with identities, compositions and linear combinations. A Jordan block at \(\lambda\) contributes one dimension precisely when its size is \(\ell\). For smaller blocks the term \(\ker N_H^{\ell-1}\) fills the numerator, and for larger blocks the term \(N_H\ker N_H^{\ell+1}\) does. Blocks at other eigenvalues contribute zero. Nonconjugate matrices have distinct dimensions \(a,b\) for at least one such quotient.

Derive the reverse intertwiner at degree three. Project each witness linearly onto its intertwiner space. Its difference from the projection is a linear combination of intertwiner equations. The projected inverse identities follow in degree at most three by using those linear equations in the original inverse equations. Apply the linear quotient maps to those projected identities, using compatibility with compositions, to obtain \(UV=I_a,\ VU=I_b\) on \(J_{\lambda,\ell}\). A rectangular refutation transfers back using homogeneous linear substitution. This gives the asserted upper inequality. The projector examples and their padding give the lower inequality.

Using principal \(p^{v_p(a-b)}\)-minors gives the previously known bound \(D_p(a,b)\le2p^{v_p(a-b)}\) for positive unequal \(a,b\); the base-\(p\) binomial digits detect the difference. The weight calculation here proves a uniform degree-four lower bound when ordinary trace vanishes. The next sections bound the higher \(p\)-adic strata. [Earlier positive-characteristic upper bound](https://github.com/Dugongue/MathProofs/blob/main/TensorAndAlgebraOpenQuestions/Positive-Characteristic-PC.md)

### A descending-minor refutation and a sharper worst-case upper bound

There is also a degree-\((b+2)\) refutation from the one-sided identity \(UV=I_a\) whenever \(a>b\). All \((b+1)\)-minors of \(U\) are zero by column count. Suppose all \(r\)-minors of \(U\) vanish, starting with \(r=b+1\). Select \(r\) rows, \(r-1\) columns of \(U\), and a selected row index \(j\). Append the restriction of \((UV)_{\cdot,j}\) to the \(r-1\) columns. The determinant of this augmented matrix expands as a linear combination of \(r\)-minors of \(U\) with coefficients from column \(j\) of \(V\). Repeated columns give zero. It therefore vanishes by the inductive lines, with multiplication degree at most \(r+1\). The equations \(UV=I_a\) let us replace the last column by the restriction of \(e_j\). This difference is a linear combination of equations of degree two with multipliers that are \((r-1)\)-minors, so the replacement also has degree at most \(r+1\). Expanding along \(e_j\) gives the selected \((r-1)\)-minor, up to sign. Every \((r-1)\)-minor is obtained by adjoining one new row, since \(a>b\). Descending to \(r=1\) gives the empty minor \(1=0\). Thus \(D_p(a,b)\le \min(a,b)+2\) for positive unequal sides. In particular, the preceding lower bound is exact over every prime when \(\min(a,b)=2\) and \(p\mid(a-b)\).

For arbitrary nonconjugate \(N\)-square matrices, let \(q=p^k\) be the least \(p\)-power among \(p^{v_p(a-b)}\) over their differing Jordan multiplicities \(a,b\). The compound upper bound on one quotient and the degree-three readout give an upper bound of \(\max(3,2q)\). There is a positively differing type and a negatively differing type, since both matrices have total dimension \(N\). If the smaller multiplicities for these types are \(s,t\), the first matrix already has total dimension at least \(q+s+t\). One of the two smaller multiplicities is therefore at most \(\lfloor(N-q)/2\rfloor\). Using the descending-minor argument on that quotient yields
\[
C_p(N)\ \le\
\max\left(3,\ \max_{\substack{q=p^k\\q\le N}}
\min\left(2q,\ \left\lfloor\frac{N-q}{2}\right\rfloor+2\right)\right)
\ \le\ \max\left(3,\frac{2(N+4)}{5}\right).
\]
The last inequality follows by comparing the increasing and decreasing bounds at \(q=(N+4)/5\). The next section gives the matching asymptotic order.

### Matching-order lower bounds for every \(p\)-adic gap

For positive unequal sizes \(a>b\), put \(q=p^{v_p(a-b)}\) and \(H=\min(q,\lfloor b/2\rfloor+1)\). Then the rectangular inverse system satisfies
\[
 H\ \le D_p(a,b)\ \le\min(2q,b+2)\ \le 2H+1.
\]
This locates its degree to within a constant factor uniformly in the characteristic, the gap, and the smaller side.

The lower bound uses Riis's ordinary PC rectangle obstruction. Introduce one variable \(z_{ij}\) per cell of an \(a\)-by-\(b\) board, with Boolean equations, row and column collisions \(z_{ij}z_{i\ell}=z_{ij}z_{hj}=0\) for distinct indicated indices, and every row and column sum equal to one. After transposing the board to the notation of the cited lemma, that system has no degree-\(D\) ordinary PC refutation if \(2D\le b,\ D<q\), and \(q\mid(a-b)\). The lemma explicitly handles degree falls in PC. [Riis, Lemma 14.1](https://arxiv.org/pdf/2611.07280#page=62)

Substitute \(U_{ij}=V_{ji}=z_{ij}\). Each off-diagonal entry of \(UV-I_a\) or \(VU-I_b\) becomes a sum of collision equations. Each diagonal entry is a row or column totality equation plus the sum of its Boolean equations \(z_{ij}^2-z_{ij}\). Thus all substituted premises are derivable in degree at most two. Multiplication by a variable in any rectangular proof specializes to multiplication by one board variable, so a rectangular refutation of degree at most \(H-1\) would give a Boolean rectangle refutation of that degree if \(H-1\ge2\). Riis's hypotheses hold with \(D=H-1\), a contradiction. When \(H-1<2\), the stated bound already follows because no rectangular axiom has degree below two and ordinary PC has no source for a degree-one proof. The upper bounds are the compound and descending-minor arguments. If \(H=q\) the last comparison is immediate; otherwise \(b+2\le2H+1\).

Take \(a=3q,\ b=2q\) with \(q\) a power of \(p\), and use the projector pair above in dimension \(5q\). Padding yields examples in every larger dimension. For \(N\ge5p\) take the greatest \(p\)-power \(q\le N/5\). Then
\[
 \frac{N}{5p}<q\ \le C_p(N)\ \le \max\left(3,\frac{2(N+4)}5\right).
\]
In particular \(C_p(N)=\Theta_p(N)\) for every fixed prime, for the original conjugacy equations without field equations. This gives the sharp asymptotic order requested by GP157. It also quantifies how large \(p\)-divisibility of Jordan multiplicity differences can force large degree on explicit nonconjugate projector pairs. Riis's lower bound is a arXiv preprint dependency, and its transfer to these conjugacy equations uses the substitutions and quotient computations above.

## Recognizing characterization by linear symmetries

Let \(f\ne0\) be a homogeneous polynomial over \(\mathbb Q\), given by its full degree-\(d\) coefficient list. Let \(W\) be the space of degree-\(d\) forms in those variables, \(N=\dim W\), and \(G=\operatorname{Stab}_{\mathrm{GL}(\mathbb C)}(f)\). Given \(1\le k\le N\), deciding whether \(\dim W^G\le k\) reduces in polynomial time to feasibility of quadratic equations over \(\mathbb C\). In particular the symmetry-characterization problem is in \(\exists\mathbb C\) and PSPACE, and it is in AM under GRH. Binary search computes the dimension with \(O(\log N)\) feasibility queries. These are complexity upper bounds for GP076. [Grochow–Urisman, question after Open Question 1.9](https://arxiv.org/html/2606.26244v2#S1.SS3)

If \(\dim W^G\le k\), start at \(W\) and intersect with fixed spaces of individual elements of \(G\). Whenever the current space has dimension greater than \(k\), it has a vector not fixed by some element of \(G\), so the intersection can be made strictly smaller. At most \(N-k\) elements suffice to cut to dimension at most \(k\). Conversely, such a finite witness implies the fixed space of \(G\) has dimension at most \(k\).

Guess the matrices \(g_i\), their inverses and the identities \(f(g_i x)=f(x)\) as coefficient equations. Stack the matrices of \(\rho(g_i)-I_W\) into \(B\), where \(\rho(g_i)\) is the action by substitution. The remaining requirement is \(\operatorname{rank}(B)\ge N-k\). This holds exactly when there are rectangular \(L,R\) with \(LBR=I_{N-k}\). To encode the coefficients of the action, use successive multiplication of dense coefficient arrays truncated above degree \(d\). For \(d>0\) in \(n\) variables, the total array length \(\binom{n+d}{d}\) is at most \((n+1)\binom{n+d-1}{d}\). When \(n\ge2\), \(d\) is at most the number of coefficients. When \(n=1\), the invariant space is one-dimensional for every nonzero form and there is nothing to compute. The cases \(d=0\) and \(k=N\) are immediate. Encoding each ordinary arithmetic gate by one variable and its defining equation gives a polynomial-size quadratic system. Clear rational denominators equationwise. This is the usual Hilbert Nullstellensatz feasibility problem. [Koiran, Hilbert's Nullstellensatz is in the Polynomial Hierarchy](https://doi.org/10.1006/jcom.1997.0451)

For the connected stabilizer \(G^\circ\), there is also an unconditional deterministic polynomial-time algorithm. The Lie algebra of the complex stabilizer is the kernel of the derivative of substitution on \(f\), so its basis is found by rational linear algebra. For each basis vector \(A_j\) of that kernel, impose the linear equation \(d\rho(A_j)w=0\) on the coefficient vector \(w\in W\). The solution space is exactly \(W^{G^\circ}\). A vector satisfying those equations has a stabilizer inside \(G^\circ\) with the entire Lie algebra, hence full dimension. The connected complex algebraic group is irreducible, and its closed full-dimensional subgroup is the whole group. This algorithm computes the connected fixed space even in examples where finite components further shrink the full fixed space. [Grochow's thesis, continuous stabilizers](https://home.cs.colorado.edu/~jgrochow/grochow-thesis.pdf)

These are paper proofs. The worst-case growth in GP157 is linear for every fixed prime. The exact minimum degree in all higher strata is an additional question. The full finite-component recognition problem in GP076 has the stated upper bounds.
