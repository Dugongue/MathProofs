# Free three-tensor isomorphism with a residue-field exponential bound

**Theorem.** Let $R$ be a finite commutative local ring with maximal ideal $\mathfrak m$ and residue field $k=\mathbb F_q$. Assume polynomial-bit-time arithmetic, reductions, lifts, and residue coordinates in the successive quotients $R/\mathfrak m^a$, with polynomially many layers. For explicit free three-tensors of side lengths $n_i$, their full isomorphism coset is computable deterministically in $q^{O(n_1+n_2+n_3)}\operatorname{poly}(L)$ bit time, including the ring encoding in $L$. A nonempty output consists of a transporter and source stabilizer generators. This is conditional on Theorems 8.1 and 8.10 of [Qiao–Zhang](https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1723.pdf).

For binary-encoded modulus $p^e$ and side length $n$, the bound over $\mathbb Z/p^e\mathbb Z$ is $p^{O(n)}\operatorname{poly}(L)$ for arbitrary $e$, on every input. Standard Galois rings have the same bound in $q$. The [finite-rings follow-up, Corollary 4.3](https://arxiv.org/html/2611.18084v1#S4.SS2) gives $|R|^{O(n_1+n_2+n_3)}\operatorname{poly}(L)$ through full tables. This proof handles the nilpotent layers at polynomial cost by tracking the full stabilizer, extending the scalar-stabilizer lifting method of our earlier four-tensor work.

## The obstruction at one level

Let $R_a=R/\mathfrak m^a$. Write $H_a$ for the stabilizer of $T_a$, $J_a$ for its residue image, $K_a$ for the kernel of $H_a\to J_a$, and $g_a$ for one transporter to $T'_a$. Retain generators of $K_a$ and generators of $J_a$ with lifts in $H_a$. The complete residue-field algorithm supplies the initial data, with $K_1=1$.

Put $I=\mathfrak m^a/\mathfrak m^{a+1}$, $V_i=k^{n_i}$, and $B=V_1\otimes_k V_2\otimes_k V_3$. At level $a+1$ the reduction kernel consists of tuples $1+X$, with $X_i$ matrices over $I$. As $I^2=0$ and $\mathfrak m I=0$, their action adds
$$
D(X)=\sum_i (1\otimes\cdots\otimes X_i\otimes\cdots\otimes 1)T_1
\quad\text{in } I\otimes_k B.
$$
The image of this explicit linear map is invariant under $J_a$ by conjugating the tuple $X$.

For $h\in H_a$ lift its matrices to $\widetilde h$ at level $a+1$. These lifts are invertible because their residue determinants are nonzero. Set
$$
W=(I\otimes_k B)/\operatorname{im}D,\qquad
\gamma(h)=[\,\widetilde h T_{a+1}-T_{a+1}\,]\in W .
$$
Changing the lift changes the displacement by an element of $\operatorname{im}D$. Multiplying lifts proves $\gamma(hh')=\gamma(h)+\overline h\,\gamma(h')$. The linear action on $K_a$ is trivial under reduction, so $\gamma|_{K_a}$ is a homomorphism to the additive group of $W$. Its image $P_a$ is the $\mathbb F_p$-span of its generator values for $p=\operatorname{char}k$. The cocycle identity gives $\gamma(hkh^{-1})=\overline h\,\gamma(k)$, hence $P_a$ is $J_a$-invariant. Thus $\beta(\overline h)=\gamma(h)+P_a$ is a well-defined cocycle in $W/P_a$, with values on generators computed using their stored lifts. These calculations use the square-zero layer and apply in mixed characteristic.

Choose a lift $\widetilde g_a$ and put $y=[\,\widetilde g_a^{-1}T'_{a+1}-T_{a+1}\,]\in W$. The affine $J_a$-action $z\mapsto \overline h z+\beta(\overline h)$ sends $0$ to $y+P_a$ exactly when a transporter exists at level $a+1$. An actual transporter reduces to $g_a h$ with $h\in H_a$, so it gives the specified class. Conversely use a word for a successful $\overline h$ in the retained generators to recover $h\in H_a$. The difference $y-\gamma(h)$ lies in $P_a$. Linear algebra over $\mathbb F_p$ expresses it as a combination of generator values. The corresponding product of powers gives $k\in K_a$ with $\gamma(kh)=y$. Lift $kh$ to level $a+1$, correct its remaining displacement by a $1+X$ on the left using $D$, and compose on the left with $\widetilde g_a$.

## Applying the cubic transporter theorem

A basis of $I$ over $k$ represents the layer as a direct sum of copies of $B$. Each $B$ is the natural equivariant quotient of $V_1\otimes_{\mathbb F_p}V_2\otimes_{\mathbb F_p}V_3$ by the $k$-balancing relations. The preimage of $P_a$ under the quotient by $\operatorname{im}D$ gives explicit invariant relations in this direct sum. The result is precisely the degree-three quotient input of Definition 25 of Qiao–Zhang. The original representations are the three $V_i$ over $\mathbb F_p$, which together faithfully encode $J_a$. Their summed dimension is $(\log_p q)\sum_i n_i$. Multiplicity from $I$ has trivial action and changes only the input length. The cocycle identity is needed in the quotient, where it holds as proved above. Theorem 8.10 supplies the complete affine transporter with words.

When the transporter is nonempty, the affine stabilizer of $0$ is exactly $J_{a+1}$, by the same displacement argument with zero target. Take its output generators and lift each to $H_{a+1}$ by that argument. To keep descriptions bounded, trim the new residue list by retaining a candidate exactly when it is outside the group already generated. This takes polynomial time in the faithful permutation degree $\sum_i q^{n_i}$, using membership on the disjoint union of the three residue vector sets. At most $\log_2 |J_{a+1}|$ generators are retained, together with their actual lifted matrices. Words used in the lifting steps are evaluated against the current stored lifts. The retained lifts are represented by matrices at the current level.

## Computing the congruence kernel

The image of $K_{a+1}$ in $K_a$ is exactly $\ker(\gamma|_{K_a})$. Zero displacement class gives a lift by solving $D$, and an actual stabilizer has zero class. The kernel of $K_{a+1}\to K_a$ is the additive group $\ker D$ in the layer. Hence lifts of generators of $\ker(\gamma|_{K_a})$, together with a basis of $\ker D$ over $\mathbb F_p$, generate $K_{a+1}$.

Compute the first kernel without enumerating $K_a$. Form the graph subgroup generated by $(\gamma(k_j),k_j)$ inside the product of the additive space $W$ and the principal congruence group. Filter the ambient group by setting the $W$ coordinate to zero and then taking successively deeper congruence layers. The first proper grade thus consists of zero $W$ coordinate and arbitrary principal congruence matrices. Subsequent grades require congruence to the identity modulo successively higher powers of $\mathfrak m$. This is a central filtration with elementary abelian layers and explicit $\mathbb F_p$ coordinates. Commuting an element of a grade with an ambient element, or taking its $p$-th power, moves it at least one grade deeper. For the congruence grades this follows by computing modulo the next power of $\mathfrak m$, using $p\in\mathfrak m$.

Maintain pivots at each grade whose projections are independent in that layer. Sift a group element from shallow to deep. Clear its leading projection by multiplying powers of pivots if it lies in their span. Otherwise insert the residual as a new pivot there and stop. Insert the graph generators, then sift all pivot $p$-th powers and pairwise commutators, restarting these checks after adding a pivot. There are at most as many insertions as the total dimension of the layers. All operations have polynomial bit cost, using binary powering for the exponents.

The pivots generate precisely the input subgroup. Insertions preserve membership in that subgroup, and sifting expresses each input generator in the pivots. More precisely, in the group generated by pivots at grade $j$ or deeper, the next-grade subgroup is generated by the deeper pivots. Descending induction proves this. Checked commutators show that a grade-$j$ pivot normalizes the deeper subgroup, because each commutator with a deeper pivot sifts using only deeper pivots. The quotient is abelian of exponent $p$ by the other checked relations. Independence of the grade-$j$ projections then excludes any nontrivial reduced product of those pivots from the next ambient grade. In the graph subgroup, the pivots after grade zero therefore generate exactly the subgroup with zero $W$ coordinate. Projecting their matrix coordinates gives the desired generators of $\ker(\gamma|_{K_a})$.

The same procedure without $W$ trims the updated kernel generator list to a polynomial size. Its generators together with lifts of the residue image generate $H_{a+1}$, by the exact image and kernel computations. This maintains the induction. A failed affine comparison certifies inequivalence, and at the last level the transporter and all stabilizer generators give the full coset. Each layer has polynomial-size coordinate data and a polynomial-size retained list. The affine transporter and residue permutation-group operations cost $q^{O(\sum_i n_i)}\operatorname{poly}(L)$ per layer.

## Ring representations

In a standard Galois ring the characteristic modulus is given in binary and the layers are the $p$-power quotients. Reduction, ideal-layer extraction and lifts use ordinary arithmetic in its defining polynomial quotient. The number of layers is bounded by the binary modulus size. For a local ring given by explicit arithmetic tables, the maximal ideal is the nonunit set. The powers of this ideal, the residue field, and bases of its layers can all be found from the tables in polynomial time by generating the ideals and extracting vector-space bases. The powers decrease strictly until zero and there are at most $\log_2 |R|$ layers. For a general finite commutative ring with explicit tables, enumerate its idempotents, retain primitive idempotents, and split into local factors. Combining independent cosets by the Chinese remainder theorem gives time $\sum_i |k_i|^{O(\sum_j n_j)}\operatorname{poly}(L)$ for residue fields $k_i$.

This is an informal transfer theorem. Its input from Qiao–Zhang is the complete affine transporter on cubic invariant quotients, including generators and words. Publication priority for this extension has not been established.

## Nonfree modules over a chain ring

The same residue-field exponent applies to arbitrary three-tensor elements over a finite commutative chain ring $R$, with its generator $\pi$ and cyclic summand descriptions of the three modules supplied. For $U_i=\bigoplus_j R/(\pi^{d_{ij}})$, write $r_i$ for its number of nonzero summands. Given arithmetic and reductions for the cyclic quotients as above, the complete coset takes $q^{O(r_1+r_2+r_3)}\operatorname{poly}(L)$ bit time, even for variable chain length. Module types must match, after which use their cyclic descriptions to identify the source and target formats. This also applies componentwise to finite principal ideal rings presented by explicit tables, after extracting cyclic descriptions as in [the marked nonfree tensor construction](Finite.md).

Replace the free matrix algebra for mode $i$ by $A_i=\operatorname{End}_R(U_i)$ and the ideals by
$$
F^a A_i=\{f\in A_i:f(U_i)\subseteq\pi^aU_i\}.
$$
They are two-sided and $F^aF^b\subseteq F^{a+b}$. The ambient group at level $a$ is $\prod_i(A_i/F^a A_i)^\times$. Every unit lifts through these nilpotent ideals. Indeed one can lift its inverse and invert the errors by a finite geometric series. The ideal quotient $F^a/F^{a+1}$ is a residue vector space, giving the same square-zero action and the same congruence filtration. Use these ambient groups throughout, so a truncated mode map always represents an actual module automorphism at the full level.

All coordinate operations are explicit. An endomorphism entry from a cyclic summand of length $d_l$ to one of length $d_j$ is an element of $R/(\pi^{d_j})$ of valuation at least $\max(0,d_j-d_l)$. At level $a$ store it modulo $\pi^{\min(a,d_j)}$. Reductions, arithmetic and lifts follow from these entry conditions. As $a=1$, ordering the lengths increasingly gives block upper triangular matrices, invertible exactly when every equal-length diagonal block is invertible. This residue group has the usual block elementary and diagonal generators. It is a legitimate supplied subgroup for Theorem 8.1.

Put $\mathcal T=U_1\otimes_R U_2\otimes_R U_3$, using the cyclic length $\min(d_{1j},d_{2l},d_{3m})$ in each tensor coordinate. Work at level $a$ on $\mathcal T/\pi^a\mathcal T$. The residue representation on $V_i=U_i/\pi U_i$ acts on each layer via the equivariant surjection
$$
V_1\otimes_k V_2\otimes_k V_3\ \longrightarrow\
\pi^a\mathcal T/\pi^{a+1}\mathcal T,\qquad
\overline u_1\otimes\overline u_2\otimes\overline u_3
\longmapsto \pi^a(u_1\otimes u_2\otimes u_3).
$$
In cyclic coordinates it discards exactly the slots of length at most $a$. Combine these explicit relations with the tangent image and congruence translations in the cubic quotient data. The tangent map uses $X_i\in F^a A_i/F^{a+1}A_i$ and is computed by applying each $X_i$ to the source lift. Only its residue tensor contributes. Conjugation by a lift of a residue stabilizer proves invariance of the tangent image. The same graph-kernel computation works because the congruence layers still have their explicit central elementary abelian filtration. The final ambient units are the actual module automorphisms. The exponent charges $V_i$ of dimensions $r_i$ once at each call and does not charge the cyclic lengths.

## Counting and prescribed determinants

The full coset output counts transporters by the order of its source stabilizer. The residue image order is computed on its faithful permutation domain. The congruence kernel order is $p$ to the sum of its retained pivot ranks. Multiplying these orders gives the exact count. The output integer has polynomial bit length.

For free tensors we can also impose any prescribed determinant triple, including determinant one on each mode, with the same time bound. Compute the determinant images of the source generators and divide the desired triple by the determinant of the returned representative. The remaining task is membership in the subgroup these images generate in $(R^\times)^3$, with an expression for a correcting element. First enumerate the subgroup's residue image in $(k^\times)^3$, of size at most $q^3$, retaining lifted words; Schreier's formula gives generators in the kernel of this reduction. Test the remaining principal-unit discrepancy using the congruence sifting procedure on $1+\mathfrak m$, with the three coordinates in parallel. Tracking the generator operations as straight-line programs gives a source-stabilizer element with the required determinant. This works for binary-encoded high powers as well as full ring tables. It preserves the same residue-size exponential cost.

## Arbitrary nonfree modules given by tables

The chain-ring hypothesis can be dropped for explicit arithmetic and module tables. Over an arbitrary finite commutative local $R$, let $r_i=\dim_k U_i/\mathfrak m U_i$. The same argument gives $q^{O(r_1+r_2+r_3)}\operatorname{poly}(L)$ bit time for complete cosets. A tensor may be supplied as a sum of pure tensors in the module tables. To compare different module presentations, first use the diagonal-module isomorphism test described below and transport to common formats.

Here $F^a A_i$ is defined using $\mathfrak m^a U_i$ instead of $\pi^a U_i$. The residue image of $A_i$ is a represented unital $k$-subalgebra of $\operatorname{End}_k(U_i/\mathfrak m U_i)$, and its unit group is the residue image of the actual automorphisms by nilpotence of $F^1$. Compute generators of its unit group by Qiao–Zhang Lemma 3.2, which supplies the deterministic polynomial-in-$q$ bound for represented algebras. This is within the stated exponential budget. To align two modules of the same explicit order, compute the endomorphism algebra of their direct sum. Its automorphisms which exchange two specified diagonal idempotents exist exactly when the modules are isomorphic. This particular test can alternatively be done with the marked module gadget in [Finite.md](Finite.md), using the two modules as a single marked sort in two comparisons, one for each input, with no bilinear operations. That gadget computes a module isomorphism via Qiao–Zhang Theorem 9.1 in time polynomial in their full tables. For the free and explicit cyclic formats above, this step uses rank or cyclic length lists and does not need Theorem 9.1.

All required additive coordinates for $A_i$, its ideals and $\mathcal T=U_1\otimes_R U_2\otimes_R U_3$ can be computed without enumerating their elements. Present each additive module group using one generator per element and the addition relations, then use integer Smith normal form. Additive endomorphisms are described by homomorphism coordinates on cyclic generators. Commutation with the scalar multiplication maps from the ring table gives linear congruences on these coordinates. Requiring the images of generators to belong to $\mathfrak m^a U_i$ gives the congruences for $F^a A_i$. Thus bases, quotient maps, and lifts are obtained by integer normal forms with polynomially many entries and polynomial bit length. Composition is ordinary composition in the additive group coordinates. The tensor module has a presentation on triples of module elements, with additivity in each slot and $R$-balancing relations. The number of triples and relations is polynomial in the table input size. Relations, maps and subquotients can be transported to cyclic coordinates using the same normal form. Layer residue vector coordinates follow by choosing a maximal independent list via linear congruence membership.

Finally the layer presentation is the equivariant surjection
$$
(\mathfrak m^a/\mathfrak m^{a+1})\otimes_k
(U_1/\mathfrak m U_1)\otimes_k(U_2/\mathfrak m U_2)\otimes_k(U_3/\mathfrak m U_3)
\ \longrightarrow\
\mathfrak m^a\mathcal T/\mathfrak m^{a+1}\mathcal T ,
$$
obtained by scalar multiplication on pure tensors. The scalar layer has trivial action. All kernels are given by the explicit coordinate map and are invariant. The tangent/cocycle argument and generator bounds therefore carry over unchanged, charging only the three residue modules in the cubic exponent. Splitting a general finite commutative ring into local factors is polynomial in its full tables as before.
Alternatively, transport the two residue projections of the direct sum by conjugation in its residue unit group, a degree-two instance of Theorem 8.10. Lift a witness to a unit and call the transported first projection e and the second f. The unit fe+(1-f)(1-e) is the identity modulo the nilpotent reduction kernel and intertwines e and f, so it corrects the lifted witness to an actual summand isomorphism.
