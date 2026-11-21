# Odd modular dihedral moments and core reconstruction from Gram graphs

The results below are informal proofs.

## Sharp odd modular dihedral moment cutoffs

Let \(K\) be an infinite field of odd characteristic \(p\) and suppose \(p\mid n\). For the natural action of the order-\(2n\) group \(D_n\), use the unnormalized group-sum tensors
\[
 T_d(x)=\sum_{g\in D_n}(gx)^{\otimes d}.
\]
The entries through order three generate the invariant field for every \(n\ne3\), and three is the exact generic geometric separation cutoff. For \(n=p=3\) the cutoff is exactly four. This answers the odd modular part of the question about polynomial invariant tensors. [Edidin and Katz, §5.2](https://arxiv.org/html/2408.09599v4#S5.SS2)

### Group-algebra form of the data

Write \(X(z)=\sum_{i=0}^{n-1}x_i z^i\) in \(K[z]/(z^n-1)\), and let \(X^*(z)=X(z^{-1})\). Rotation multiplies \(X\) by \(z\), and reflection is \(*\). Orders one and two give \(X(1)\) and \(XX^*\), since the coefficient of \(z^r\) in \(XX^*\) is \(\sum_i x_i x_{i+r}\), and the group-sum coefficient is twice this. The order-three entries at positions \((0,i,j)\) are the coefficients of
\[
 A+B,\qquad A=X(z)X(w)X((zw)^{-1}),\quad
 B=X(z^{-1})X(w^{-1})X(zw).
\]
For example the rotation sum at \((0,i,j)\) is \(\sum_l x_lx_{l+i}x_{l+j}\), which is the coefficient of \(z^i w^j\) in \(A\); reflection adds the coefficient from \(B\). For an invertible group-algebra element \(F\), put \(\delta F=F(z)F(w)/F(zw)\). On the generic locus all relevant \(X\)'s are units. For a candidate \(Y\) with the same data, set \(U=Y/X\) and \(R=X^*/X\). The quadratic data give \(UU^*=1\). Comparing the cubic data, with \(\nu=\delta U\), gives the equation
\[
 (\nu-1)(\nu-\delta R)=0. \tag{1}
\]

### The prime-power calculation

Put \(n=q=p^r\ge5\). Use coordinates \(z=1+T,\ w=1+W\), so the one-variable ring is \(K[T]/(T^q)\) and the two-variable ring is \(K[T,W]/(T^q,W^q)\). Write \(T\oplus W=T+W+TW\). Work with \(X(1)\ne0\). There is a unique square root \(E\) of \(XX^*\) with constant term \(X(1)\), found by triangular coefficient recursion since \(2X(1)\ne0\). Uniqueness gives \(E^*=E\). Set \(F=X/E\). It has constant term one and satisfies \(FF^*=1\). Dividing the cubic data by \(E(z)E(w)E(zw)\) gives \(V+V^{-1}\) for \(V=\delta F\). Since \(V(0,0)=1\), the Cayley transform \(J=(V-1)/(V+1)\) is defined and these data are equivalent to knowing \(J^2\). Indeed \(V+V^{-1}=2(1+J^2)/(1-J^2)\).

We use the following description of the first nonzero homogeneous term of \(\delta H-1\) for any \(H(0)=1,\ HH^*=1\). Characters are the elements \((1+T)^e\), with \(e\) an integer modulo \(q\). If \(H\) is a character then \(\delta H=1\). Otherwise its leading discrepancy is a nonzero scalar times one of
\[
 L_k(T,W)=T^k+W^k-(T+W)^k
 \quad(3\le k\le q-2,\ k\text{ odd and not a }p\text{-power}),
\]
\[
 C_p(T^{p^s},W^{p^s})
 \quad(0\le s<r),\qquad
 C_p(T,W)=\sum_{i=1}^{p-1}\frac{T^iW^{p-i}}{i!(p-i)!}.
 \tag{2}
\]
To prove this, repeatedly remove an actual character when the first nonconstant term is \(aT^{p^s}\) with \(a\in\mathbb F_p\), using \((1+T)^{a p^s}\) with \(a\) interpreted as an integer representative. This does not change \(\delta H\), and it raises the first possible nonzero degree. If the first remaining term is \(aT^k\) with \(k\) not a \(p\)-power, the norm equation and \(T^*=-T/(1+T)\) force \(k\) odd, and the leading discrepancy is \(aL_k\). The polynomial \(L_k\) is nonzero for such \(k\): if \(k=\sum k_jp^j\), the expansion of \((1+T)^k\) as \(\prod(1+T^{p^j})^{k_j}\) contains a nonzero intermediate coefficient unless \(k\) is a \(p\)-power.

If instead the leading term is \(aT^k\) with \(k=p^s\) and \(a\notin\mathbb F_p\), compare with the truncated binomial \(\sum_{i=0}^{p-1}\binom ai T^{ki}\). Its norm is one through degree \(kp-1\). Its leading multiplicative discrepancy is of total degree \(kp\) and equals \((a^p-a)C_p(T^k,W^k)\). To see this, first take \(k=1\). The formal binomial identity through degrees less than \(p\) is valid modulo \(p\) because its denominators are invertible. At total degree \(p\) and at mixed exponent \(i,p-i\), the omitted term \(\binom ap(T+W+TW)^p\) contributes
\(\prod_{j=0}^{p-1}(a-j)/(i!(p-i)!)\), whose reduction is the displayed coefficient. This argument uses formal identities over the localization of \(\mathbb Z[a]\) at integers prime to \(p\), since the mixed coefficient has that displayed invertible denominator. Substitute \(T^k,W^k\) and use \((T\oplus W)^k=T^k\oplus W^k\). A first discrepancy of the ratio from this model in a degree strictly between \(k\) and \(kp\) has odd degree by the norm condition, and cannot be a \(p\)-power. It contributes the first type in (2). A discrepancy at degree \(kp\), if present, contributes zero at that degree since \(kp\) is a \(p\)-power. Higher discrepancies cannot affect the leading term. This proves (2).

Generically the leading term of \(J\) is a nonzero multiple of \(P=TW(T+W)\). For \(p\ge5\), no discrepancy has degree less than three and \(L_3=-3P\); a nonzero cubic parameter is realized by the norm-one element \((1+cT^3)/(1+c(T^*)^3)\). For \(p=3\) and \(q\ge9\), the degree-three discrepancy is a multiple of \(C_3(T,W)=P/2\) with scalar \(a^3-a\), where \(a\) is the linear coefficient of \(F\). This scalar is generically nonzero because \(a\) varies freely on the norm-one units, as seen by using \((1+cT)/(1+cT^*)\).

The product of \(P\) with every possible leader in (2) is nonzero in \(K[T,W]/(T^q,W^q)\). If the product has total degree less than \(q\) this is immediate. For \(L_{q-2}\), the coefficient of \(T^{q-2}W^3\) is, up to sign, \(k+\binom k2=k(k+1)/2\) with \(k=q-2\), which is nonzero in odd characteristic. For a second-type leader of degree \(q\) with \(r=1\), \(p=q\ge5\). The coefficient of \(T^4W^{p-1}\) is \(c_2+c_3=c_2/3\ne0\), with \(c_i=1/(i!(p-i)!)\), and both exponents are below \(p\). If \(r>1\), take the term \(T^{p^{r-1}}W^{(p-1)p^{r-1}}\) and multiply it by \(TW^2\). Both exponents are below \(q\) since \(p^{r-1}\ge3\), and their residues modulo \(p^{r-1}\) distinguish this contribution from multiplication by \(T^2W\). Second-type leaders below degree \(q\) have degree at most \(q/p\), whose sum with three is below \(q\) in the applicable cases.

Now let \(F'\) be a candidate, with Cayley transform \(J'\). Because \(P^2\) survives in the truncated ring, equality \(J'^2=J^2\) determines the leading scalar of \(J'\) up to sign. Reflect the candidate if needed to make the scalars equal. The leading term of \(J'+J\) is then twice that of \(J\). If \(H=F'/F\) is not a character, the leading term of \(J'-J\) is a nonzero scalar times the leader of \(\delta H-1\): the difference of the Cayley transforms is \(2(V'-V)/((V'+1)(V+1))\). By the product calculation, \((J'-J)(J'+J)\ne0\), a contradiction. Hence \(H\) is a character, which is exactly the rotation ambiguity. This proves cubic separation for \(q\ge5\).

The same argument gives an injective differential. Over dual numbers a tangent candidate replaces \(F\) by \(F(1+\varepsilon h)\) with \(h(0)=0\) and \(h+h^*=0\). The leader classification still applies to a nonzero \(h\), with its leading scalar carried by \(\varepsilon\). There are no nonzero removable scalar characters, and in the binomial step the coefficient \((\varepsilon a)^p-\varepsilon a=-\varepsilon a\) is nonzero. The nonzero product above contradicts equality of squares to first order. The square root \(E\) was determined by the quadratic data, so the differential kernel of the full moment map is zero.

### Adding the prime-to-characteristic factor

Write \(n=q m\), where \(q=p^r\), \(p\nmid m\). Work in a splitting field of \(z^m-1\), with local coordinates \(z=\eta(1+T)\) at \(\eta\in\mu_m\). Each component is \(K[T]/(T^q)\), and multiplication of two local arguments takes \((\eta,T),(\theta,W)\) to \((\eta\theta,T\oplus W)\). Use subscripts \(\eta\) for local components and write \(L_F=(1+T)(\partial_TF)/F\) for the logarithmic derivative of a unit. We use the open conditions that \(L_{R_1}(0)\ne L_{R_\eta}(0)\) for \(\eta\ne1\), and each normalized \(R_\eta/R_\eta(0)\) is not a local character. These are generic. The linear coefficient of \(R_\eta=X^*_\eta/X_\eta\) depends on the independent coefficients at the roots \(\eta,\eta^{-1}\), and at a self-inverse root it is minus twice the normalized linear coefficient of \(X_\eta\). Each can thus avoid the finitely many character values, and the coefficient at \(1\) can vary independently from any other inversion pair. We also retain the prime-power open condition that \(\delta R_1-1\) has a nonzero degree-three term for \(q\ge5\), which follows from the calculation for \(F\) since \(R_1=F^{-2}\).

For \(q\ge5\), the prime-power calculation in the component at \(1\) lets us reflect and rotate the candidate so that \(U_1=1\). On the component \((\eta,1)\), both \(\nu-1\) and \(\delta R-1\) are divisible by \(W\). After canceling the two explicit powers of \(W\) in (1), work modulo \(W^{q-2}\). The divided factors differ by a unit because the coefficient of \(W\) in \(\delta R-1\) has nonzero constant term at \(T=0\). Since this is a local ring, one factor must be a unit and the other must vanish. Thus \(\nu\equiv1\) or \(\nu\equiv\delta R\bmod W^{q-1}\). The first congruence gives \(U_\eta(T\oplus W)=U_\eta(T)\bmod W^{q-1}\). By setting \(T=0\), the only possible nonconstant term in \(U_\eta\) is \(aT^{q-1}\), and the coefficient of \(W\) in the congruence then forces \(a=0\). For the second congruence put \(H_\eta=U_\eta/R_\eta\). It says \(H_\eta(T)/H_\eta(T\oplus W)=R_1(W)\bmod W^{q-1}\). At \(T=0\) this identifies \(H_\eta(W)\) with \(H_\eta(0)/R_1(W)\) through degree \(q-2\). Substituting that information back through total degree three forces \(R_1(T\oplus W)=R_1(T)R_1(W)\) through that degree, contradicting the generic degree-three term. Thus each \(U_\eta\) is constant.

For \(q=3\) and \(m\ge2\), apply the same divided-factor calculation at \((\eta,1)\) for \(\eta\ne1\), without first normalizing \(U_1\). Write \(d=L_{U_1}(0)\), \(r_0=L_{R_1}(0)\). Comparison of the coefficients of \(W\) now gives one of the two exact one-variable identities
\[
 L_{U_\eta}=d,\qquad L_{U_\eta/R_\eta}=d-r_0.
\]
The derivation \((1+T)\partial_T\) on the local ring is diagonal on the basis \((1+T)^j\), \(j=0,1,2\), with eigenvalues \(0,1,2\). A unit with constant logarithmic derivative is therefore a scalar times one of these characters, and its logarithmic derivative lies in \(\mathbb F_3\). Generically \(r_0\notin\mathbb F_3\), so the two kinds of identities cannot occur for different \(\eta\). In the first case all the \(U_\eta\)'s away from \(1\) are scalar times one common character. In the second, all the \(U_\eta/R_\eta\)'s have this property. At \(1\), either \(U_1\) or \(U_1/R_1\) respectively has constant term one and norm one. Such a length-three unit is determined by its linear coefficient: the quadratic coefficient is forced by multiplying by its star. It is therefore the same character at \(1\). Replacing \(X\) by \(X^*\) in the second case and rotating the candidate in either case reduces again to constant \(U_\eta\)'s.

With \(U_\eta=c_\eta\), on any component \((\eta,\theta)\) the value of \(\nu=c_\eta c_\theta/c_{\eta\theta}\) is a nonzero constant. Equation (1) forces \(\nu=1\) unless \(\delta R\) is constant on that component. In the latter event, after dividing each local \(R_\eta\) by its constant, setting \(T=0\) and \(W=0\) identifies the three normalized units at \(\eta,\theta,\eta\theta\) and makes their common value multiplicative under \(\oplus\). Such a group-like unit is a character: expanding in the basis \((1+T)^j\), \(0\le j<q\), the multiplicativity identity has only diagonal terms on its comultiplication side and forces exactly one coefficient to be one, all others zero. This contradicts the generic condition. Thus the \(c_\eta\) form a character of \(\mu_m\), and the Chinese remainder theorem realizes it by a rotation whose exponent is zero modulo \(q\). Cubic separation follows for all \(n\ne3\) in the claimed range.

For completeness the moment map is also separable in the mixed case. Write a tangent candidate as \(U=1+\varepsilon h\). For \(q\ge5\) the root-\(1\) calculation gives \(h_1=0\). On \((\eta,1)\) the divided second factor of (1) is a unit modulo \(W^{q-2}\) by the same nonzero derivative condition, so the first factor vanishes there. For \(q\ge5\) the first-branch argument gives \(h_\eta\) constant. For \(q=3\) it gives \((1+T)\partial_T h_\eta=((1+T)\partial_T h_1)(0)\) for every \(\eta\ne1\). The diagonal derivative on the character basis has image with zero coefficient at the constant character. Therefore the common right-hand side is zero and the \(h_\eta\) are constant. At \(1\) the tangent norm condition and the vanishing linear coefficient then give \(h_1=0\). Finally (1) with constant \(h_\eta\)'s and nonconstant \(\delta R\) forces \(h_{\eta\theta}=h_\eta+h_\theta\) for every pair. The additive group has no nonzero \(m\)-torsion, so these constants vanish. This proves injectivity of the differential.

The rational field extension induced by the moment entries is finite by geometric generic separation, and separable by the differential calculation. Its degree is consequently the size of the generic geometric fiber, which is \(2n\), the degree over the fixed field. Thus the moment-data field equals the fixed field. Formation of invariant polynomial spaces and of polynomial spaces spanned by moment entries commutes with scalar extension, because their defining equations are linear over the original field. Taking fraction fields, and clearing an invariant denominator by an orbit product for rational invariants, descends the equality from the finite splitting field to \(K\).

### Sharpness and the modular triangle

The quadratic information has transcendence degree at most \(\lfloor n/2\rfloor+1<n\), because \(XX^*\) is fixed by star and \(X(1)^2=(XX^*)(1)\). Therefore degree two does not even give a finite generic fiber. For \(n=p=3\) the group is \(S_3\). Write \(e_i\) for the elementary symmetric polynomials and \(p_j\) for the sums of \(j\)-th powers. Orders one and two recover \(e_1,e_2\), and cubic traces add nothing: the possible monomial types give \(2p_3=2e_1^3\), \(e_1e_2-3e_3=e_1e_2\), and \(6e_3=0\). Order four includes the trace of \(x_1^3x_2\), namely \(p_3p_1-p_4=e_2p_2-e_1e_3\) by Newton's identities. This recovers \(e_3\) generically, establishing the sharp cutoff and field generation also in this case.

## One generic real Gram graph recovers core operations and a canonical subgroup action

Let \(G\) be a finite faithful real orthogonal group and take a generic orbit with its Gram graph. The graph determines the group's core quandle on the observed vertices, under any identification of a vertex with the identity. In particular it determines each element's order and all its powers. If the representation contains no four-dimensional irreducible of quaternionic type, the graph also recovers the actual regular action of \(G' Z(G)^2\), where \(G'=[G,G]\) and \(Z(G)^2=\{z^2:z\in Z(G)\}\). Every odd-order group meets this representation hypothesis, so in odd order the recovered subgroup is \(G'Z(G)\). Moreover for every finite odd-order group with \(C_G(G')=1\), the graph recovers the whole multiplication table and the actual regular action, even among arbitrary competing generic real orthogonal representations. This gives a case of the real one-orbit conjecture without requiring its Gram colors to distinguish inverse pairs. [Mixon and Vose, Theorem 2.5, Conjecture 2.7 and §4](https://arxiv.org/html/2411.17434#S2) · [Bergman, core quandles](https://arxiv.org/abs/2006.00641)

### Recovering the core directly from the Gram data

Fix a generic seed \(v\), labeling the orbit by \(g\mapsto gv\). It is free. For every two operators \(h,k\in G\) having different symmetric parts, the quadratic forms \(v^{\mathsf T}h v\) and \(v^{\mathsf T}k v\) are different polynomials, so they are unequal at a generic \(v\). This is a finite collection of open conditions. Thus a color at a vertex \(x=gv\) consists exactly of a collection of vertices \(ghv\) whose differences \(h\) all have the same symmetric operator \(h+h^{-1}=S\). This collection is stable under \(h\mapsto h^{-1}\). For each of its vertices \(y=ghv\),
\[
 y+gh^{-1}v=gSv.
\]
Its centroid is therefore \(gSv/2\). The graph determines this centroid in the Euclidean realization of the point configuration from its Gram matrix. More directly, testing a candidate sum against twice the centroid uses only the squared norm of a linear combination, calculated from the Gram entries. The unique vertex obtained from \(y\) by reflection across the centroid is \(gh^{-1}v\). Consequently the graph constructs the permutation \(J_x\) of the vertices given in group labels by
\[
 J_g(k)=g k^{-1}g.
\]
This is the core operation. For any selected identity, the iterates \(g^0=1,g^1=g\) and \(g^{j+1}=J_{g^j}(g^{j-1})\) give all the powers and the order of \(g\).

### Recovering a group of permutations of the orbit

Use a selected basepoint labeled \(1\) and let
\[
 \mathcal D=\langle J_gJ_1:g\in G\rangle.
\]
Write \(L_a\) and \(R_a\) for left and right multiplication by \(a\), respectively, and use the homomorphism \((a,b)\mapsto L_aR_{b^{-1}}\) on \(G\times G\). Since \(J_gJ_1=L_gR_g\), the group \(\mathcal D\) is the image of the subgroup generated by \((g,g^{-1})\) for all \(g\). This subgroup is exactly
\[
 \{(a,b)\in G\times G:ab\in G'\}.
\]
Containment follows by abelianizing. For the converse, the product of the generators at \(g,h\) and the inverse of the generator at \(gh\) is \((1,g^{-1}h^{-1}gh)\). Hence \(1\times G'\) is contained, and symmetry of the generators also gives \(G'\times1\). Together with the generators' images on the abelianized factors this proves equality. In particular \(|\mathcal D|\le |G|^2\).

A permutation \(L_aR_{b^{-1}}\) preserves Gram colors exactly when conjugating every difference \(u\) by \(b\) preserves its symmetric part. Indeed the new difference is \(bub^{-1}\), and the chosen generic seed distinguishes all distinct symmetric parts. Thus the criterion is that \(b\) commute with every operator \(u+u^{-1}\). The real image algebra of \(G\) is the linear span of its operators, so its self-adjoint part is the span of these symmetrized operators. The real Artin–Wedderburn decomposition expresses this image algebra as a product of matrix rings \(M_j(\mathbb R)\), \(M_j(\mathbb C)\), and \(M_j(\mathbb H)\), with the adjoint given by conjugate transpose on each simple factor in compatible orthonormal models. Here the factors correspond to the distinct real irreducible constituents. For \(j\ge2\), an element centralizing every self-adjoint matrix is scalar and central: the diagonal projections force it to be diagonal, the real symmetric off-diagonal units force equal entries, and the self-adjoint matrices with arbitrary conjugate entries off diagonal force the common entry to commute with the division ring. The same conclusion holds in the one-dimensional real and complex factors because they are commutative. The exceptional factor \(M_1(\mathbb H)\) corresponds to a four-dimensional real quaternionic constituent.

Under the stated hypothesis the criterion for color preservation is therefore \(b\in Z(G)\), using faithfulness. If \(b\) is central and \(ab\in G'\), then \(L_aR_{b^{-1}}=L_{ab^{-1}}\) and \(ab^{-1}\in G' Z(G)^2\). Conversely for every \(c\in G' Z(G)^2\) there are \(a,b\) with \(b\) central, \(ab\in G'\) and \(c=ab^{-1}\). Thus intersecting the reconstructed \(\mathcal D\) with the graph's color-preserving permutations gives exactly \(L_{G' Z(G)^2}\). Odd-order groups have no quaternionic constituents: on a finite odd-order group squaring is a bijection, so the Frobenius–Schur indicator of any nontrivial irreducible complex character equals the average of that character and is zero. The trivial character has indicator one. Also squaring is a bijection on their centers, so \(Z(G)^2=Z(G)\).

### Reconstructing the whole group when its commutator centralizer is trivial

Suppose \(|G|\) is odd and \(C_G(G')=1\), so in particular \(Z(G)=1\). The reconstructed left subgroup is \(L_{G'}\), and conjugating it by \(J_1\), the inversion permutation, gives the right subgroup \(R_{G'}\). For each vertex \(g\), compute the conjugation action of \(J_gJ_1\) on this right subgroup. In group notation it sends \(R_h\) to \(R_{g^{-1}hg}\), because \(J_gJ_1=L_gR_g\). These actions are distinct as \(g\) varies, by the centralizer hypothesis. Taking their inverses gives an injective homomorphism from \(G\) into the automorphism group of the reconstructed subgroup. Composition of these explicitly known maps thus recovers the group law on the observed vertices and hence their actual regular action.

Any competing faithful generic representation has a free orbit, so its group \(H\) has the same odd order. Its recovered right subgroup by the preceding theorem is \(R_{H'Z(H)}\). The same maps read from the graph are then induced by conjugation in \(H\) on \(H'Z(H)\). There are still as many distinct maps as vertices, so composition recovers its multiplication identically. The computations are polynomial time on an exact Gram matrix in the real arithmetic model. One enumerates at most \(|G|^2\) permutations of \(\mathcal D\), tests them directly against the Gram labels, and represents each conjugation map by its action on the recovered elements. This does not require computing the full automorphism group of an arbitrary colored graph.

The class of odd-order groups in this last assertion is nonempty. For example, let \(B=C_7\rtimes C_3\) with the nontrivial order-three action on \(C_7\), and let \(A=\mathbb F_{29}^3\). The group \(B\) acts faithfully by a cyclic coordinate permutation of length three and a diagonal order-seven matrix with eigenvalues \(\lambda,\lambda^2,\lambda^4\) for a primitive seventh root in \(\mathbb F_{29}\), choosing the permutation orientation to realize the prescribed order-three action. Then \(B'=C_7\), \(A^{B'}=0\), and \([A,B]=A\). In \(G=A\rtimes B\), the derived subgroup is \(A\rtimes B'\). Any element centralizing it must lie in \(A\), by faithfulness on \(A\), and must then be fixed by \(B'\). Hence its centralizer is trivial.
