# Counting epimorphisms onto nilpotent groups with a bounded-generator central quotient

Fix constants \(c,d\). Given Cayley tables for an arbitrary finite group \(G\) and a nilpotent group \(H\) of class at most \(c\) such that \(H/Z(H)\) is at most \(d\)-generated, one can compute the exact number of epimorphisms \(G\to H\) in deterministic polynomial time. The same algorithm returns an epimorphism if the count is positive. All primes and prime-power exponents are allowed. There is no generator bound on the center. This answers the bounded-generator target question in Grochow–Srivastava–Thakkar Open Question 3(2) for nilpotent targets of any fixed class, and gives an exact counting algorithm on the larger stated class, a restricted case of Open Question 2. [Open Questions 2 and 3(2)](https://arxiv.org/html/2609.07429v1#S7)

## 1. Enumerating the small-generator quotient maps

Every homomorphism to \(H\) factors through \(G/\gamma_{c+1}(G)\), since its image has class at most \(c\). The lower central subgroups and the quotient are constructible from the table by commutators and subgroup closure. Thus the source may be assumed nilpotent too. Both groups decompose as direct products of their Sylow subgroups, which can be found by the orders of the elements in the tables. Maps to a target Sylow subgroup of prime \(p\) are trivial on all other source Sylow subgroups. Counts therefore multiply and witnesses assemble independently over the primes. A trivial target has exactly one epimorphism from any source. It suffices to give the algorithm for a pair of finite \(p\)-groups.

First consider a generic central extension \(1\to Z\to Y\to Q\to 1\) and a specified homomorphism \(h:G\to Q\). For each \(g\in G\), choose a representative \(u_g\in Y\) of \(h(g)\). Every lift has the form \(f(g)=u_g z_g\) with \(z_g\in Z\). Its homomorphism equations are
\[
 z_{gg'}-z_g-z_{g'}=u_{gg'}^{-1}u_g u_{g'},
\]
where the right hand side belongs to \(Z\) and is written in its additive coordinate system. These are finite abelian linear equations, one for each pair of source elements. In cyclic coordinates for \(Z\) they are ordinary systems of congruences, solvable in polynomial time using integer normal forms. Such coordinates, with maps from the table elements, can themselves be found using Smith normal form from a presentation with one generator per element and one relator per multiplication table entry. If a lift \(f_0\) exists, the set of all lifts is a torsor for \(\operatorname{Hom}(G/[G,G],Z)\). Indeed, the quotient of any two lifts is a pointwise central difference and is a homomorphism, and each such homomorphism gives a lift. [Polynomial-time integer normal forms](https://doi.org/10.1137/0208040)

Write \(D=H/Z(H)\). It has nilpotency class at most \(c-1\) and at most \(d\) generators. Each lower central factor \(\gamma_i(D)/\gamma_{i+1}(D)\) has at most \(d^i\) generators. Iterated simple commutators in the marked generators span that abelian factor, by commutator additivity modulo the next term. Every subgroup of an abelian \(p\)-group of generator rank \(r\) has generator rank at most \(r\). Intersecting a subgroup with the lower central series, or using the images of that series in a quotient, shows that every subgroup of every quotient of \(D\) has rank at most \(r=\sum_{i=1}^{c-1}d^i\). The same applies to upper central factors of \(D\) in its successive quotients.

Enumerate all maps \(G\to D\) by starting with the trivial quotient and successively solving the central lifting equations along this upper central series. At each step the central kernel has at most \(r\) cyclic factors. For a finite abelian group \(A\) and a cyclic group \(C_m\), one has \(|\operatorname{Hom}(A,C_m)|\leq|A|\), since on a source cyclic summand of order \(a\) there are \(\gcd(a,m)\) choices. Each lift therefore has at most \(|G|^r\) variants, which can be listed using the cyclic coordinates and the chosen base lift. There are at most \(c-1\) layers. All quotient maps can therefore be enumerated in polynomial time, with at most \(|G|^{r(c-1)}\) branches. Keep only surjections \(G\to D\), since an epimorphism to \(H\) must induce one.

## 2. The last central lift and the Frattini quotient

Fix a surviving map \(h:G\twoheadrightarrow D\), and solve the central lifting equations into \(H\). Skip this branch if there is no lift. Put \(A=G/[G,G]\), \(Z=Z(H)\), and let \(f_0\) be a base lift. All lifts are obtained by multiplying \(f_0\) by a central homomorphism \(z:A\to Z\). The number of such homomorphisms can be too large to enumerate. Instead, let
\[
 F=G/\Phi(G)=A/pA,\qquad E=H/\Phi(H),\qquad B=\operatorname{im}(Z\to E),
\]
where \(\Phi(K)=K^p[K,K]\) for a finite \(p\)-group \(K\). Burnside's basis theorem says that \(f:G\to H\) is surjective if and only if its induced linear map \(F\to E\) is onto. Each central homomorphism adjusts the base linear map by a map into \(B\). The criterion follows because each maximal subgroup of a finite \(p\)-group has index \(p\), and every proper subgroup is contained in a maximal subgroup. The maximal subgroups are the inverse images of the hyperplanes of the elementary abelian quotient by \(K^p[K,K]\).

Choose cyclic bases \(a_j\) of \(A\), of orders \(p^{s_j}\), and \(z_i\) of \(Z\), of orders \(p^{e_i}\). Let \(b_i\) be the image of \(z_i\) in \(E\). The possible adjustments contributed by the target cyclic factor \(\langle z_i\rangle\) have the form \(b_i\ell\), where \(\ell\) lies in the following subspace of \(F^*\):
\[
 L(e_i)=\{\ell\in F^* : \ell(\bar a_j)=0\text{ whenever }s_j<e_i\}.
\]
If \(s_j<e_i\), an image of \(a_j\) in this factor is divisible by \(p\), so the coordinate contributes zero modulo \(\Phi(H)\). If \(s_j\geq e_i\), its coefficient modulo \(p\) is arbitrary. Choices on separate source and target cyclic factors are independent. Also \(L(e)\) decreases as \(e\) increases.

Scan the \(b_i\) in increasing order of \(e_i\), keeping one exactly when it extends their span. They give a basis \(b_{i_1},\ldots,b_{i_t}\) of \(B\). Each discarded \(b_i\) is a combination of earlier kept vectors and its allowable space \(L(e_i)\) is contained in every corresponding kept allowable space. Thus the space of all possible adjustments \(F\to B\) is exactly
\[
 \bigoplus_{j=1}^t b_{i_j} L(e_{i_j}).
\]
The directness follows from the independence of the chosen \(b_{i_j}\), and every adjustment in this displayed space is realized by using only the kept cyclic target coordinates. Hence each distinct adjustment has the same number of central homomorphisms above it, namely
\[
 \frac{|\operatorname{Hom}(A,Z)|}{p^{\sum_j \dim L(e_{i_j})}},
 \qquad
 |\operatorname{Hom}(A,Z)|=p^{\sum_{i,j}\min(e_i,s_j)}.
\]

## 3. Counting independent affine rows

Extend the kept \(b_{i_j}\) to a basis of \(E\). In the resulting coordinates, the Frattini map for any lift has fixed row vectors on the complementary basis positions, and independently selectable rows \(r_j+L_j\) on the \(B\) positions, where \(r_j\) is the corresponding base row and \(L_j=L(e_{i_j})\). Onto is equivalent to independence of all rows. If the fixed rows are dependent, the number is zero. Process the adjustable rows in order of increasing subspace inclusion. This is possible because the \(L_j\) are nested.

Suppose \(k\) independent rows have already been selected, counting the fixed rows. For the next row \(r_j+L_j\), let \(P_j\) be the span in \(F^*/L_j\) of the projections of the fixed rows and of the earlier base rows. Since all earlier adjustment spaces lie in \(L_j\), this quotient span is independent of all earlier choices. If \(\bar r_j\notin P_j\), no point of \(r_j+L_j\) lies in the span of the earlier selected rows. If \(\bar r_j\in P_j\), the intersection is a coset of the kernel of that projection on the earlier selected span. It has exactly \(p^{k-\dim P_j}\) elements. Thus the number of choices that extend independence at this step is
\[
 p^{\dim L_j}-\begin{cases}
 p^{k-\dim P_j}&\bar r_j\in P_j,\\
 0&\bar r_j\notin P_j.
 \end{cases}
\]
The number is the same for every independent choice made so far. Multiply these numbers across the row positions, with zero factors ending the branch. Multiplying by the constant fiber size in Section 2 counts all surjective lifts above \(h\).

For a witness, choose any extending row at each positive step. Enumerating its affine row set takes at most \(|F|\leq|G|\) trials, and the product calculation guarantees that no such choice spoils later steps. Convert the chosen adjustment back to a central homomorphism using the kept cyclic generators. When \(s_j\ge e_i\), lift each selected coefficient on \(\bar a_j\) to an integer modulo \(p^{e_i}\). When \(s_j<e_i\), set that coefficient to zero. Multiplying this homomorphism into \(f_0\) gives the required witness. The count is summed over the different maps \(h\), with no double counting because the induced map to \(H/Z(H)\) is unique.

The algorithm uses table operations, finite abelian linear systems, and finite-field ranks. All are polynomial in the table sizes for the fixed constants \(c,d\). Counts have polynomial bit length since each map is specified by the images of at most \(\log_2 |G|\) generators. This is a paper proof.
