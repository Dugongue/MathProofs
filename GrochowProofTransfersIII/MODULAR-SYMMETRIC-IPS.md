# Exact modular placeholder degree in symmetric IPS

Let \(K\) be a field of characteristic \(p>0\), and let a finite group \(G\) permute the variables \(X=(x_i)\) and the indexed equations \(F=(f_j)\), compatibly with \(g f_j=f_{g j}\). Each \(x_i\) ranges over a nonempty finite set \(A_i\subset K\), with \(A_{g i}=A_i\). Put \(q_i(x_i)=\prod_{b\in A_i}(x_i-b)\). Assume no point of the product grid is a common zero of \(F\).

An IPS certificate here is a polynomial \(C(X,Y,Z)\) with \(C(X,0,0)=0\) and \(C(X,F(X),q(X))=1\). The indexed placeholders \(Y_j\) stand for the main equations \(f_j\), and \(Z_i\) stand for the grid equations \(q_i\). Symmetry refers to the simultaneous permutations of all three families of variables. The degree measured in the first theorem is degree **in \(Y\) alone**, including every monomial of the output polynomial. The theorem also applies to certificates represented by syntactically symmetric circuits.

## The exact degree over any finite grid

For a grid point \(a\), let \(H_a=G_a\) be its stabilizer and \(P_a\) a Sylow \(p\)-subgroup of \(H_a\). Then the minimum \(Y\)-degree of a symmetric IPS certificate is exactly
\[
\max_a \min_{j:f_j(a)\ne0}|P_a\cdot j|.
\tag{1}
\]
The inner minimum equivalently minimizes the \(p\)-part of \(|H_a\cdot j|\). This makes (1) independent of Sylow choices. For an \(H_a\)-orbit, \(|P_a\cdot j|=[P_a:P_a\cap (H_a)_j]\) is at least the \(p\)-part of \(|H_a\cdot j|\). Equality is attained at a conjugate of \(j\), by containing a Sylow subgroup of \((H_a)_j\) in a Sylow subgroup of \(H_a\) and conjugating the latter to \(P_a\).

**Lower bound.** Specialize at \(X=a,Z=0\). The remaining \(H_a\)-invariant polynomial in \(Y\) has zero constant term and takes value one at \(Y=F(a)\). Partition its monomials into \(H_a\)-orbits. Every monomial on an orbit has the same coefficient and evaluation, because \(F(a)\) is \(H_a\)-fixed. Some orbit has nonzero contribution, so its length is prime to \(p\) and all its variables correspond to active equations. A monomial stabilizer on this orbit contains a Sylow subgroup. Conjugate the monomial to be \(P_a\)-fixed. Its nonempty support contains a full \(P_a\)-orbit of an active equation, and its degree is at least the length of that orbit.

**Construction on the grid.** For each orbit representative \(a\), take a shortest \(P_a\)-orbit of active equations, and form the squarefree monomial on those placeholders. This monomial is \(P_a\)-fixed, so its \(H_a\)-orbit length is prime to \(p\). Sum the distinct monomials on the orbit and divide by its nonzero value at \(F(a)\). This gives an invariant polynomial \(U_a(Y)\) of the required degree, with no constant term and value one at \(F(a)\). Translate this choice equivariantly to all points in the \(G\)-orbit. Let \(E_a(X)\) be the product of the univariate Lagrange point indicators. Then \(Q(X,Y)=\sum_a E_a(X)U_a(Y)\) is \(G\)-invariant and \(Q(X,F(X))\) is one on the grid.

## Exact lift off the grid

Write \(d_i=|A_i|\). The products \(x^\beta\prod_i q_i(x_i)^{\alpha_i}\), for \(0\le \beta_i<d_i\), form a basis of \(K[X]\). Their leading monomials have exponent vectors \((\beta_i+d_i\alpha_i)_i\), each vector occurs once, and all other terms have smaller total degree. Thus triangular reduction computes the basis expansion. Permutations preserving the grid act by permuting the coordinates of these indices. The \(\alpha=0\) part of any polynomial in the basis agrees with it on the grid. Multivariate interpolation shows that this part vanishes identically when the polynomial vanishes on the grid.

Apply this expansion to \(R(X)=Q(X,F(X))-1\). Only terms with \(\alpha\ne0\) remain. In each such term replace every \(q_i(x_i)\) by \(Z_i\). The resulting \(L(X,Z)\) is invariant, vanishes at \(Z=0\), and substitutes back to \(R\). Hence \(Q-L\) is a symmetric IPS certificate attaining (1). Every invariant polynomial has a syntactically symmetric sum-of-monomials circuit, by indexing product gates by the distinct monomials and using the same gate shape on each orbit. Repeated factors can use separate copies of the input gate. This supplies circuit symmetry without an efficiency claim.

The correction admits a separate exact \(Z\)-degree formula. For a fixed invariant grid-vanishing residual \(R\), write \(c_{\beta,\alpha}\) for its canonical coefficients. Write \(P_{\beta,\alpha}\) for a Sylow \(p\)-subgroup of the stabilizer of the index pair \((\beta,\alpha)\). Among invariant corrections \(L(X,Z)\) with \(L(X,0)=0\) and \(L(X,q(X))=R(X)\), the least \(Z\)-degree is
\[
\max_{(\beta,\alpha):c_{\beta,\alpha}\ne0}\ \min_{i\,\colon\,\alpha_i>0}|P_{\beta,\alpha}\cdot i|,
\tag{2}
\]
with maximum zero for \(R=0\).

Indeed, use the basis \(x^\beta q(X)^\lambda Z^\gamma\), where \(\beta_i<d_i\). For a residual index \((\beta,\alpha)\), its coefficient after substitution is the sum over \(0<\gamma\le\alpha,\ \lambda=\alpha-\gamma\), where \(0<\gamma\) means nonzero. The stabilizer \(H_{\beta,\alpha}\) permutes these markings. Invariant coefficients are constant on every orbit. To produce a nonzero residual coefficient, a marking orbit of size prime to \(p\) must contribute. A marking on that orbit can be conjugated to be \(P_{\beta,\alpha}\)-fixed, so its degree is at least the shortest \(p\)-orbit in the support of \(\alpha\). Conversely mark one shortest orbit by taking its indicator as \(\gamma\). The marking orbit has size prime to \(p\). Assign to each term on it the target coefficient divided by the orbit size, then propagate that sum to all residual indices in its \(G\)-orbit by equivariance. This constructs a lift of degree (2). Formula (2) concerns a fixed residual. Optimizing the total degree in both placeholder families can also depend on the interpolant.

## The modular pigeonhole principle

Take \(N\ge2\), with \(N\) pigeons and \(N-1\) holes. Use the Boolean grid and the main equations of Definition 19 in Dawar–Grädel–Kullmann–Pago,
\[
f_i=\sum_j x_{ij}-1,\qquad f_{\{i,i'\},j}=x_{ij}x_{i'j}\quad(i\ne i').
\]
The acting group is \(S_N\times S_{N-1}\). The equations are unsatisfiable on the grid in every characteristic. If the row equations all vanish, every row has at least one entry equal to one. The absence of collisions would then require at least \(N\) distinct holes.

The minimum \(Y\)-degree of symmetric IPS is exactly the largest power \(s\) of \(p\) with \(s\le N\). This gives a fixed lower bound even if the Boolean placeholders have arbitrary degrees.

**Attaining the local maximum.** Leave \(s\) rows empty and assign the other \(N-s\) rows injectively to holes. Only the empty-row equations are active. The permutation of the empty rows gives a full \(S_s\) factor of the stabilizer, since those rows are distinct as a set from nonempty rows and every permutation of the empty rows extends while fixing everything else. Its Sylow subgroup is transitive on \(s\) points: an \(s\)-cycle generates a \(p\)-subgroup and lies in some Sylow subgroup. Hence the local minimum is \(s\).

**Bounding every point.** Let \(P\) be a Sylow \(p\)-subgroup of the stabilizer of a Boolean matrix. If a row equation is active, its \(P\)-orbit has \(p\)-power size at most \(N\), hence at most \(s\). Otherwise every row degree is \(1\) modulo \(p\). The row stabilizer \(P_i\) acts on its neighbors and has a fixed neighbor, since its other orbits have size divisible by \(p\). Choose such a neighbor for each representative of the \(P\)-orbits of rows and extend equivariantly. This gives a \(P\)-equivariant function \(\phi\) from the rows to the holes using only edges of the matrix.

The function is noninjective. If it is injective on each row orbit, two such orbits map onto a common hole orbit. Choose two preimages at one hole \(j\), one from each orbit. The stabilizer \(P_j\) fixes both by injectivity on their orbits. The collision label thus has orbit size at most the size of one row orbit.

Otherwise take a row orbit on which \(\phi\) is noninjective, fix a hole \(j\) in its image, and let \(B\) be its fiber at \(j\). The group \(H=P_j\) is transitive on \(B\). At \(i\in B\), let \(J=H_i<H\), and take an overgroup \(J\le K\le H\) with \([K:J]=p\). To see such a \(K\) exists, let \(J\) act on \(H/J\). Its fixed cosets are precisely \(N_H(J)/J\). The number of fixed cosets is a multiple of \(p\) and at least one, so the normalizer quotient contains a subgroup of order \(p\), whose inverse image gives \(K\). The action of \(K\) on its orbit of \(i\), which has size \(p\), has image of order at most \(p\) in \(S_p\). Any pair of distinct rows in this block has \(K\)-orbit of size at most \(p\). Its \(H\)-orbit therefore has size at most \([H:K]p=|B|\). The full \(P\)-orbit of the corresponding collision at \(j\) has size at most \(|P\cdot j|\,|B|\), the size of the original row orbit, hence at most \(s\). In every case there is an active equation with orbit size at most \(s\). Formula (1) proves the claim.


In characteristic zero the same interpolation and correction give minimum \(Y\)-degree one. For each assignment, a single active equation suffices to obtain an orbit sum with nonzero value because the orbit length is nonzero in the field. In positive characteristic \(p>N\), the pigeonhole formula also gives one, since \(p\) exceeds every prime divisor of the acting group's order.

## An explicit two-pigeon certificate

For two pigeons and one hole, write \(X=(x,y)\), \(Y=(u,v,w)\) and \(Z=(a,b)\). The interpolant has the exact corrected form
\[
(1-x)(1-y)uv-x(1-y)v-(1-x)yu+xyw-(1+y)a-(1+x)b-2ab.
\]
It is invariant under simultaneously swapping \(x,y\), \(u,v\), and \(a,b\). It vanishes when all five placeholders vanish, and substituting \((u,v,w,a,b)=(x-1,y-1,xy,x^2-x,y^2-y)\) gives one over any commutative ring. In characteristic two the last term vanishes.

## Verification

The general degree formulas and the pigeonhole application are proved above. The accompanying Mathlib-only Lean file checks the equivalence between prime-to-\(p\) orbit size and existence of a representative fixed by a chosen Sylow subgroup, the characteristic-\(p\) normalization of orbit sums, and the three identities for the two-pigeon certificate. The audit reports the exact source hash and axioms. The general polynomial expansion, degree optimization, and pigeonhole group argument are given as mathematical proofs.

The Python regression enumerates all \(4+64+4096\) matrices for \(N=2,3,4\) and evaluates the local formula in characteristics \(2,3,5\). It independently searches and evaluates invariant squarefree orbit sums for \(N\le3\). These finite checks bear on those cases of the theorem.

## Relation to earlier work

Dawar, Grädel, Kullmann and Pago introduced this symmetric IPS setting, proved symmetric completeness by a full orbit product, and exhibited a modular obstruction to symmetric linear IPS. Their bounded-degree symmetrization theorem assumes characteristic zero or characteristic prime to the group order. The exact formulas above allow the modular case and separate the main-placeholder cost from the cost of correcting by coordinate equations. The Boolean pigeonhole calculation uses their equation family.

The method adapts the order of operations in the Davis–Astra treatment of Spivey's multiplayer War conjecture. The War proof determines a quotient by classes of cards and uses a slot permutation to lift the exact finite dynamics. Here the quotient is by stabilizer orbits, and equivariant monic division lifts exact finite-grid identities to polynomial identities. The uses of Sylow subgroups, monomial markings and polynomial division are part of the present argument.

- Anuj Dawar, Erich Grädel, Leon Kullmann and Benedikt Pago. [Symmetric Proofs in the Ideal Proof System](https://doi.org/10.4230/LIPIcs.MFCS.2025.40), MFCS 2025. See Theorems 5 and 7, Example 6, and Definition 19.
- Joshua A. Grochow and Toniann Pitassi. [Circuit Complexity, Proof Complexity, and Polynomial Identity Testing](https://arxiv.org/abs/1404.3820).
- Davis–Astra proof collection. [Spivey's multiplayer War conjecture, pinned proof](https://github.com/1337isnot1337/solved-conjectures/blob/892c0404/results/spivey-multiplayer-war/PROOF.md).
