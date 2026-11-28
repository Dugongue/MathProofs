# Counting homomorphisms from closed hyperbolic three-manifolds to \(D_8\)

This paper gives a direct single-query reduction from Boolean circuit counting to unmarked homomorphism counting on closed hyperbolic three-manifolds, with first Betti number linear in circuit size. The \(D_8\) hardness question in [Samperton–Weiß, Section 1.6](https://arxiv.org/pdf/2602.02885) already has a Turing-hardness answer from [Galindo, Theorem 1.2](https://arxiv.org/abs/2605.06984v2), by taking the spherical category \(\mathrm{Vec}_{D_8}\) and using \(\mathrm{TV}_{\mathrm{Vec}_G}(M)=|\operatorname{Hom}(\pi_1M,G)|/|G|\). That route uses a graph-manifold partition function. The construction below encodes the marked fiber into one unmarked count using a local modification of the triple cup form, with an explicit decoder and linear cohomological size. Section 3 combines this with the epoch decomposition.

## 1. An unmarked counting theorem

**Theorem 1.** Fix a finite field \(k=\mathbb F_q\), let \(H(k)=\mathrm{UT}_3(k)\), and let \(M\) be an input triangulated orientable closed three-manifold. Computing \(|\operatorname{Hom}(\pi_1M,H(k))|\) is \(\#\mathrm P\)-complete under polynomial-time metric reductions, meaning one query followed by polynomial-time arithmetic. The reduction produces closed hyperbolic three-manifolds. In particular this holds for \(H(\mathbb F_2)=D_8\), the dihedral group of order eight. For \(k\) a prime field the same hardness holds for counting *surjective* homomorphisms, again through one query. From a Boolean circuit with \(s\) inputs and gates, the reduction maintains \(b_1(M;k)=O_q(s)\). The polynomial reduction to hyperbolic instances and that to arbitrary closed instances have the same decoding formula.

### Triple Fourier formula

Start with any closed orientable three-manifold with free integral first homology of rank \(h\). Write \(V=H^1(M;k)\) and \(\mu:V^3\to k\) for its alternating triple cup form. The formula for the central lift of a homomorphism to \(H(k)\) says that the two quotient characters \(u,v\in V\) lift exactly when \(u\smile v=0\). The coefficient-change and Poincaré duality argument applies even before hyperbolization, as in [the marked construction](GeometryTransfer.md). Every liftable pair has \(q^h\) lifts. Let \(\chi:k\to\mathbb C^\times\) be any nontrivial additive character. Summing over a third character gives
\[
Z(\mu):=|\operatorname{Hom}(\pi_1M,H(k))|
=\sum_{u,v,w\in V}\chi(\mu(u,v,w)).
\tag{1}
\]
Indeed the inner sum is \(q^h\) for a zero linear functional on \(V\), and zero for any nonzero \(k\)-linear functional, which is onto \(k\). The same cancellation shows that a restriction depending on \(u,v\) alone can be inserted on both sides. This observation permits a marked count to be encoded indirectly in the unmarked count.

Choose labeled basis elements \(a,b\) of the integral \(H^1\), and write \(a^*,b^*\) for their coordinate linear forms. For each triple \(u,v,w\), form the three-by-two matrix \(A\) with columns \((u_a,v_a,w_a)^{\mathsf T}\) and \((u_b,v_b,w_b)^{\mathsf T}\). Let \(U_j(\mu)\) be the sum on the right of (1) with \(\operatorname{rank} A=j\). For any two fixed ordered full-rank pairs of columns there is a matrix in \(\mathrm{SL}_3(k)\) taking one to the other. Extend each pair to a determinant-one basis to see this. Apply this matrix to the three rows \(u,v,w\) simultaneously. Alternation preserves \(\mu(u,v,w)\), so the sum over the remaining coordinates is independent of the fixed full-rank pair.

The marked commutator \([g_a,g_b]\) with central image \(1\) requires the determinant of the top two rows of \(A\) to be one. There are \(|\mathrm{SL}_2(k)|q^2\) such matrices \(A\), out of \((q^3-1)(q^3-q)\) full-rank matrices. Thus the marked homomorphism count is
\[
Z_{\mathrm{mark}}(\mu)=\frac{q^2}{q^3-1}U_2(\mu).
\tag{2}
\]
This holds over arbitrary finite fields, including when the trace character has a nontrivial kernel. The Fourier sum varies a linear functional through its entire image.

For example, appending just one coordinate \(r\) and term \(a^*\wedge b^*\wedge r^*\) produces \(\mu'\) with
\[
Z(\mu')=q^3(U_0(\mu)+U_1(\mu)).
\tag{3}
\]
For fixed \(A\), summing the new three coordinates is a linear character sum with coefficients the two-by-two minors of \(A\). This gives a two-query reduction immediately. The next construction gives the stronger one-query result.

### Encoding all ranks by one query

With three new labels \(x,y,z\), attach
\[
a^*\wedge x^*\wedge y^*+b^*\wedge x^*\wedge z^* .
\tag{4}
\]
For a fixed \(A\), its contribution is \(\sum_{X,Y,Z}\chi(\det[A_a,X,Y]+\det[A_b,X,Z])\).
Summing over \(Y,Z\) gives \(q^6\) exactly when
\[
\det[A_a,X,-]=\det[A_b,X,-]=0.
\]
Otherwise it gives zero. If \(\operatorname{rank}A=2\), the two lines intersect only in zero, so the full sum is \(q^6\). If \(\operatorname{rank}A=1\) the eligible \(X\) form the line of the nonzero columns, giving \(q^7\). If rank is zero, all \(q^3\) choices are eligible, giving \(q^9\). This proof uses only the coefficients \(1\) and \(-1\) of an integral alternating form and is uniform in \(q\).

Use \(K=3h+1\) independent copies of (4). Write \(\mu^\star\) for the enlarged form. The copies share only the anchors so their sums multiply. Hence
\[
q^{-6K}Z(\mu^\star)=U_2(\mu)+q^K U_1(\mu)+q^{3K}U_0(\mu).
\tag{5}
\]
Each \(U_j\) is an integer. For a sector \(j\), multiply the entire first row by any element of \(\mathbb F_p^\times\), where \(p=\operatorname{char} k\). This permutes the sector and shows that the multiplicities of all nontrivial \(p\)-th roots of unity in its sum are equal. Their sum is \(-1\). Also \(U_2\) is nonnegative by (2) and \(|U_2|\le q^{3h}<q^K\). Consequently the least residue modulo \(q^K\) of (5) is exactly \(U_2\). Formula (2) recovers the marked count using exact integer arithmetic.

### Hardness, hyperbolicity and surjections

Apply the marked affine scheme construction to the satisfying-assignment scheme of a Boolean circuit. It yields an integral form \(\mu\) with \(h=O(s)\), sparsely described by \(O(s)\) signed unit coefficients, and a marked extension count equal to the satisfying-assignment count times a known positive integer. Append (4) as above. The integral form \(\mu^\star\) still uses \(O(s)\) coordinates and signed unit terms. Invoke the explicit polynomial surgery construction in [the marked realization](GeometryTransfer.md) to obtain a closed orientable manifold with free integral first homology and this form. Use the efficient Heegaard hyperbolization in that proof. Its twists, with powers divisible by the exponent of \(H(k)\), preserve the full based homomorphism set and its homomorphism images. In particular they preserve its ordinary count. Equation (5) followed by (2) and division by the known marked factor recovers \(\#\mathrm{SAT}\). The integer decoding uses polynomially many bits. A homomorphism into a fixed finite group is counted in \(\#\mathrm P\) by recording one label per oriented edge outside a maximal tree and checking every face relation. These witnesses work for every closed input and in particular on the hyperbolic promise.

For \(q=p\) prime, a homomorphism is onto \(H(\mathbb F_p)\) precisely when its two characters are independent. If they are independent, the quotient image is \(\mathbb F_p^2\), and the commutator of lifts of a quotient basis generates the additive center. If they are dependent, the quotient image is contained in a line and the map is not onto. In the preliminary free-homology construction every dependent pair is cup-zero by alternation. At first Betti number \(h^\star=h+3K\) the number of non-surjective maps is therefore
\[
q^{h^\star}\bigl(q^{h^\star}+q(q^{h^\star}-1)\bigr).
\]
Add this known integer to the surjection-oracle output before applying (5). The Heegaard modification preserves images, so the same decoding works on the hyperbolic output. It also preserves \(b_1(-;k)\), as its homomorphism comparison applies to the additive group of the coefficient field or to its prime-field components. This proves the size claim and the surjection assertion. \(\square\)

## 2. An intrinsic algorithm when the cup form is sparse

**Theorem 2.** Fix \(k=\mathbb F_q\). Suppose the input is a triangulated closed orientable three-manifold with \(h=b_1(M;k)\), together with a basis of \(H^1(M;k)\) by simplicial cocycles whose triple cup tensor has \(O(h)\) nonzero unordered triples in this basis, including triples with repeated indices. The exact number of homomorphisms to \(H(k)\) is computable deterministically in
\[
2^{O_q(h/\sqrt{\log(h+16)})}\operatorname{poly}(L),
\]
where \(L\) is the full input length. The same bound applies if the full triple form in such a basis is already supplied. For a prime field it also counts the surjections. This uses the sparsity of the intrinsic form in the given basis and needs no circuit witness presentation of the manifold.

Compute the triple coefficients by evaluating simplicial cup products on the oriented fundamental cycle. Given \(u,v\in k^h\), one equation \(\mu(u,v,e_i)=0\) for each basis vector checks the lift by the cup obstruction and Poincaré duality, with no torsion hypothesis. Each nonzero unordered triple contributes at most six scalar products of coordinates over all these equations, using graded commutativity to account for permutations. Introduce a running sum in each equation and wire every term to the adjacent running sums. Over the explicitly fixed finite field, each field operation is a constant-arity Boolean circuit relation after coding field elements. The canonical running sums are forced, with no extra multiplicity. By sparsity there are \(O(h)\) variables and \(O(h)\) total incidences. The exact counting form of [Strassle–Subercaseaux, Fact 1.3 and Section 6](https://arxiv.org/pdf/2611.11832) counts these assignments in the asserted bound. Multiply by \(q^h\) to count all lifts. For prime-field surjections subtract the lift count for dependent pairs. Write \(j\) for the dimension of the kernel of \(u\mapsto u\smile u\), which is linear over a prime field. The cases \(u=0\), \(u\ne0,v=0\), and \(u\ne0,v=\lambda u\) for \(\lambda\ne0\) give \(q^h\), \(q^h-1\), and \((q-1)(q^j-1)\) pairs respectively. This contribution is multiplied by \(q^h\) and computed by linear algebra. \(\square\)

## 3. A transfer from unmarked manifold counters to nondeterministic simulation

**Theorem 3.** Fix \(k=\mathbb F_q\). Suppose unmarked homomorphism counts into \(H(k)\) from closed hyperbolic three-manifolds can be computed in time
\[
2^{O(N/\log^\alpha(N+2))}\operatorname{poly}(L)
\]
for \(N=b_1(M;k)\), \(L\) the triangulation size and some fixed \(\alpha>0\). Then nondeterministic multitape time \(t\ge n\) has a deterministic simulation running in
\[
2^{O(t\log\log(t+4)/\log^\alpha(t+2))}\operatorname{poly}(t).
\]
For \(k\) prime the same conclusion follows from a solver for unmarked surjection counts.

By [Strassle–Subercaseaux, Lemma 2.1](https://arxiv.org/pdf/2611.11832), for block size \(b\) there are \(2^{O(t/b)}\) circuit-CSPs of total gate count \(O(t\log b)\) each, with a satisfiable member exactly when the computation accepts. Convert each instance into a single Boolean circuit using \(O(t\log b)\) gates. Apply Theorem 1 with the one-query decoder. This takes polynomial time per instance and gives \(N=O(t\log b)\), with a recoverable exact assignment count. Choose \(b=\lceil\log^\alpha(t+2)\rceil\), truncated at \(t\). The cost of enumerating head patterns then stays inside the stated bound. The per-instance cost gives the iterated logarithm, using eventual monotonicity of \(N/\log^\alpha(N+2)\). The reduction only tests if any decoded count is positive and works without a path-count preserving conversion of the underlying machine. \(\square\)
