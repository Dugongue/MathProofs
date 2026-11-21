# A polynomial-degree rigidifier for an arbitrary finite quotient

**Theorem.** Given a finite group \(C\) of order \(m\) by multiplication table, construct an extension \(D\) with an elementary abelian kernel \(A\) and quotient \(D/A=C\), represented faithfully on three distinguished transitive point orbits. Its total degree is \(O(m\log(m+1))\). The image on \(C\) of the permutation normalizer that preserves the distinguished orbits is exactly \(\operatorname{Inn}(C)\). The running time is polynomial in the table size, including explicit permutation generators.

Pettet's characterization gives abstract finite extensions that obstruct the lift of outer automorphisms. The construction below uses a small permutation degree and forces the quotient behavior by three concrete stabilizers. It uses the Cayley color graph mechanism that appears in Sambale's proof. [Sambale's proof of Pettet's theorem](https://arxiv.org/html/2405.02992v1#S2).

**Construction.** Greedily choose generators \(c_1,\ldots,c_d\) outside the preceding subgroups. There are at most \(\log_2 m\) of them and none equals \(c_0=1\). Choose a prime \(p>d+2\) of size \(O(d+2)\). Put \(A=\mathbb F_p^{C}\), and let \(C\) act by left translation of the coordinate indices. Form \(D=A\rtimes C\). Write \(e_x^*(v)=v_x\) for coordinates. Use the following \(D\)-sets:
\[
D/A,\qquad D/K_0,\qquad D/K,\qquad
K_0=\ker e_1^*,\quad K=\ker\!\left(\sum_{j=0}^d(j+1)e_{c_j}^*\right),
\]
where \(K_0,K\) are subgroups of \(A\). Their sizes are \(m,pm,pm\). The \(D/K_0\) action is faithful, since the intersection of all \(C\)-translates of \(K_0\) is zero. In either larger orbit, index its points by \((x,u)\in C\times\mathbb F_p\), with \(u\) the translated functional on \(A\). For \(K\), put \(\ell_x=\sum_j(j+1)e_{xc_j}^*\). Then \((a,g)\) sends \((x,u)\) to \((gx,u+\ell_{gx}(a))\). For \(K_0\) use \(\ell_x=e_x^*\). The quotient orbit is left translation by \(g\). These formulas construct the arrays without enumerating \(D\). One coordinate vector of \(A\) and the \(c_j\) generate \(D\).

**Rigidity.** A marked permutation normalizer induces an automorphism \(\delta\) of \(D\). Preserving \(D/A\) preserves its kernel \(A\). Write \(\alpha\) for the induced automorphism of \(C\) and \(F\) for the restriction to \(A\). Preserving \(D/K_0\) gives a permutation \(\sigma\) of the coordinate hyperplanes since their \(D\)-translates are exactly all coordinate hyperplanes. The action on \(A\) satisfies \(F L_g=L_{\alpha(g)}F\), where \(L_g\) translates the coordinate indices. The \(A\)-part of any lift of \(g\) has no effect on conjugation of \(A\), since \(A\) is abelian. Thus
\[
\sigma(gx)=\alpha(g)\sigma(x).
\]
Each coordinate of \(F\) is a nonzero scalar on its indicated input coordinate. The same relation, and transitivity of the left translation, show that those scalars are all equal.

Preserving \(D/K\) makes \(F(K)\) one of its translates, say the hyperplane indexed by \(x\). Its unordered coefficient list after a common scaling must be the list \(1,\ldots,d+1\). Their sum \((d+1)(d+2)/2\) is nonzero in \(\mathbb F_p\). Therefore any scale relating these two lists after the common coordinate scalar is removed is \(1\). All the coefficients are distinct, so \(\sigma(c_j)=xc_j\) for each \(j\), including \(\sigma(1)=x\). Equivariance now gives \(\alpha(c_j)=x c_jx^{-1}\), hence \(\alpha=\operatorname{inn}(x)\). Conversely conjugation by a lift of any \(x\in C\) is realized on the marked permutation action by a group element and induces that inner automorphism.



**Unmarked form at the same asymptotic degree.** Add an independent \(C_2\) factor acting trivially on the first two orbits and regularly on a second coordinate of the third. The resulting three orbit sizes are \(m,pm,2pm\), so every permutation normalizer preserves them. The kernel on the faithful coordinate orbit of \(D\) is exactly the extra \(C_2\), which is therefore preserved. Taking its orbits on the enlarged third orbit recovers \(D/K\) and the same induced quotient automorphism as on the other two orbits. The argument above gives exactly the inner automorphisms in the unmarked normalizer as well. The kernel over \(C\) is the abelian group \(A\times C_2\).


## Partial quotient maps in an ordinary conjugacy query

Let \(G,H\) act faithfully by permutations. Suppose we have paired small quotients \(q:G\twoheadrightarrow C\), \(q':H\twoheadrightarrow C'\), both enumerated. We want a conjugator inducing an isomorphism \(\alpha:C\to C'\) such that its restriction to \(S\le C\) agrees with a supplied injective homomorphism \(f:S\to C'\) up to one inner conjugation. Other constraints may prescribe point-orbit matches or identify kernels of small quotient maps. A polynomial number of these partial-map conditions can be submitted in **one uncoloured conjugacy decision query**.

For this condition add the same independent factor \(D(C')\) to the two permutation groups, acting on its three marked orbits above. Append to the source a transitive orbit for \(C\times C'\) with stabilizer \(\{(s,f(s)):s\in S\}\), viewed using the quotient of \(G\) and the quotient of \(D(C')\). On the target use the \(C'\times C'\) orbit with stabilizer \(\{(u,u):u\in f(S)\}\). Mark the correspondence of these added orbits. If the small quotient kernels must first be identified, attach their paired marked regular quotient actions. A conjugator preserving such a pair induces exactly an isomorphism of the quotient maps, since the kernels of the added actions are the original kernels.

Under a marked conjugator of the enlarged groups the original factor and each auxiliary factor are respected individually. The original domain is the complement of the marked new orbits. Its action is faithful on the original factor, and the distinguished coordinate orbit of each auxiliary factor is faithful on that factor. The kernels of these projections recover the factors by intersections. The auxiliary quotient map on \(C'\) is inner by the theorem. Equivalence of the graph orbits means that the image of the source stabilizer is conjugate to the target stabilizer in \(C'\times C'\). Surjectivity of both quotient projections makes this exactly the usual conjugacy condition for transitive coset actions. If the two conjugating elements are \(a,b\in C'\) and the auxiliary map is \(\delta'\), this condition says, simultaneously for all \(s\in S\),
\[
a\alpha(s)a^{-1}=b\delta'(f(s))b^{-1}.
\]
It follows that \(\alpha|_S=\operatorname{inn}(c)f\) for some common \(c\). Conversely, for such an \(\alpha\), take the auxiliary isomorphism to be identity and apply the relevant first-coordinate conjugation to match the graph stabilizers. Each extra marked action then has the required equivariant bijection.

The graph orbits have at most \(|C||C'|\) points. The anchor itself need not have polynomial order, since its explicit action has polynomial degree. The existing prime-marker construction converts the prescribed point-orbit matches on the entire expanded action to ordinary uncoloured conjugacy. This reduction preserves the required matching on all original and auxiliary orbits. [Prime orbit-marking reduction](https://github.com/Dugongue/MathProofs/blob/main/GrochowEightEleventh/orbit-marking-lemma.md).
