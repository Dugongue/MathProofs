# Epimorphisms of quotients of field Heisenberg groups

**Theorem.** Given Cayley tables of two quotients of generalized Heisenberg groups over finite fields, one can decide in deterministic polynomial time whether the first surjects onto the second and produce a surjection on yes instances. The two fields and Heisenberg ranks can differ, and characteristic two is included. This covers the family studied by Lewis–Wilson, the reference in the first clause of Grochow–Srivastava–Thakkar Open Question 3(3). The literal BMW definition of genus one also includes Heisenberg groups over arbitrary finite commutative local rings, so that broader clause has further cases. [Lewis–Wilson, Lemma 3.2 and §6](https://arxiv.org/abs/1010.5466). [Open Question 3(3)](https://arxiv.org/html/2609.07429v1#S7). [Brooksbank–Maglione–Wilson, Definition 3.2 and §3.2(c)](https://joshmaglione.com/papers/Genus2.pdf).

## Recovering the field and the ratio space

A generalized field Heisenberg group $H_m(K)$ is the group of triples $(x,y,z)\in K^m\times K^m\times K$ with product
$$
(x,y,z)(x',y',z')=(x+x',y+y',z+z'+\textstyle\sum_j x_jy'_j).
$$
Its center equals its commutator subgroup. Each noncentral element has commutators ranging over the entire center, by nondegeneracy of the standard symplectic $K$-form. Consequently, a nonabelian quotient of $H_m(K)$ is a quotient by a subgroup of its center and still has center equal to its derived subgroup. An abelian quotient is elementary abelian. Trivial inputs are immediate, different primes have no nontrivial epimorphism, and abelian targets reduce to comparison of the abelianization rank over the common prime field. It suffices to treat a pair of nonabelian inputs of the same prime $p$.

Put $F=\mathbb F_p$. For $X=G,H$, compute $V_X=X/Z(X)$, $W_X=Z(X)=X'$, and the commutator map $b_X\colon V_X^2\to W_X$. Both spaces are elementary abelian and the operations and bases are recovered from the tables. Write $P_X=\{\lambda\circ b_X\mid\lambda\in W_X^*\}$ for the space of scalar forms. Each nonzero member of $P_X$ has the form $\operatorname{Tr}_{K/F}(a\eta)$, where $\eta$ is the nondegenerate alternating $K$-form on $K^{2m}$ and $a\ne0$. It is nondegenerate because for a nonzero vector $v$, $\eta(v,\cdot)$ runs over all of $K$ and the trace pairing is nondegenerate.

Choose a nonzero reference form $\beta_X\in P_X$. Define $T_\gamma$ by $\gamma(x,y)=\beta_X(T_\gamma x,y)$, and set
$$
U_X=\{T_\gamma:\gamma\in P_X\},\qquad L_X=F[U_X].
$$
For the coordinates coming from $H_m(K)$, these operators are scalar multiplications by ratios of the corresponding trace coefficients in $K$. Thus $L_X$ is a finite field, and $U_X$ is its explicit $F$-subspace containing $1$. Both are recovered by matrix operations: compute every basis ratio from the nonsingular reference form and close their linear span under multiplication until it is an algebra. This also explains why the ambient fields and their embeddings need not be supplied.

## The exact test

There is an epimorphism if and only if $\dim_F V_G=\dim_F V_H$ and there are
$$
a\in U_G\setminus\{0\},\qquad
\iota:L_H\hookrightarrow L_G\ \text{an $F$-embedding},\qquad
a\,\iota(U_H)\subseteq U_G.
\tag{1}
$$
To prove necessity, an epimorphism induces surjective linear maps $A:V_G\to V_H$, $B:W_G\to W_H$ with $b_H(Ax,Ay)=B b_G(x,y)$. Pullback of each nonzero member of $P_H$ is nonzero and belongs to $P_G$, so is nondegenerate. The kernel of $A$ is therefore zero. Write $A^*\beta_H=\beta_G(a\,\cdot,\cdot)$ with $a\in U_G\setminus\{0\}$. Pullback of the form corresponding to $T_\gamma\in U_H$ then has its ratio equal to $a A^{-1}T_\gamma A\in U_G$. Since $a$ is a unit of $L_G$, conjugation induces the required field embedding and containment.

For sufficiency when $p$ is odd, both $\beta_H$ and $\beta_G(a\,\cdot,\cdot)$ are balanced for $L_H$, acting on $V_G$ via $\iota$. In each case a basis of $L_H/F$ and the trace pairing recover a unique $L_H$-valued form $h$ such that $\operatorname{Tr}_{L_H/F}(c\,h(x,y))=\beta(cx,y)$ for every $c\in L_H$. The balance identity gives bilinearity, alternatingness follows since the field characteristic is odd and the form is skew-symmetric, and nondegeneracy follows from that of $\beta$. The two $L_H$-forms have equal dimensions and hence admit a constructive symplectic isometry $A$. Therefore $A^*\beta_H=\beta_G(a\,\cdot,\cdot)$ and $A^{-1}T_\gamma A=\iota(T_\gamma)$. Equation (1) gives $A^*P_H\subseteq P_G$. Dualizing defines a surjective $B:W_G\to W_H$ with the required commutator identity. The odd-prime class-two correspondence, using $x+y=xy[x,y]^{-1/2}$, gives a group epimorphism from $A,B$, because the input centers equal their commutator subgroups.

When $p=2$, the squares give a well-defined map $q_X:V_X\to W_X$, whose polarization is $b_X$. Write $q_0$ for the scalar coordinate with polar form $\beta_X$. Every $u\in U_X$ specifies exactly one scalar coordinate $q_u$ by its polar form, since the map from central linear functionals to $P_X$ is injective. There is a single nondegenerate hyperbolic $L_X$-quadratic form $Q_X$ with
$$
q_u(x)=\operatorname{Tr}_{L_X/F}(u Q_X(x)),\qquad u\in U_X.
\tag{2}
$$
Indeed, in the parent group the square map is $Q_K(x,y)=\sum_j x_j y_j$. If $a_0\ne0$ is the reference trace coefficient, use $Q_X=\operatorname{Tr}_{K/L_X}(a_0Q_K)$. The two complementary coordinate spaces are still isotropic over $L_X$. Nondegeneracy of the polar form follows from nondegenerate trace duality and $K$-bilinearity of the parent polar form. This proves hyperbolicity and (2). To reconstruct $Q_X$ without the parent, solve
$$
\operatorname{Tr}_{L_X/F}(c\,Q_X(x))=q_0(\sqrt c\,x)
$$
for a basis of $c\in L_X$. Square roots are unique in the field of characteristic two, and its action on $V_X$ is known from the polar ratios.

Given $a,\iota$ satisfying (1), view the source as an $L_H$-module using $\iota$ and transfer $aQ_G$ by $\operatorname{Tr}_{L_G/\iota(L_H)}$, interpreting the result over $L_H$. The transfer again has nondegenerate polar form by trace duality and still has complementary totally singular subspaces from the source. Its dimension over $L_H$ equals that of $Q_H$. A hyperbolic quadratic basis isometry therefore pulls each $q_{H,u}$ back to $q_{G,a\iota(u)}$. Dualizing gives a surjective $B$ with $q_H(Ax)=Bq_G(x)$, so the commutator identity holds by polarization.

To obtain a group epimorphism in characteristic two, choose a basis of $V_G$, map its chosen lifts to arbitrary lifts of their $A$-images, and send central elements through $B$. The relations that specify the center, basis-lift squares, and basis-lift commutators present the source: they reduce every word to a central element times a binary product of basis lifts, and the source has exactly this many elements. The constructed images respect all these relations. Their induced maps on the center and the quotient are surjective, hence so is the group map.

## Running time and further scope

Enumerate the nonzero elements of $U_G$ and the $F$-embeddings of $L_H$ by testing the roots in $L_G$ of a generating polynomial of $L_H$. A generator can be found by enumerating the field; its minimal polynomial is computed by linear algebra. Each field acts faithfully on a nonzero $V_X$, so its order is at most $|V_X|$, itself no greater than the given group order. Enumerations and linear tests are polynomial in the Cayley-table lengths. Quadratic basis construction over $L_H$ is also polynomial in this model: take a nonzero isotropic vector, find a partner of polar pairing $1$, add a suitable scalar multiple of the first vector to make the partner isotropic, and continue in the orthogonal complement. There are at most $|V_X|$ vectors to test. This proves the theorem.

For odd $p$, the nonabelian local test can also be applied to an arbitrary class-two exponent-$p$ target when the source is a quotient of a field Heisenberg group. A nonabelian epimorphic target must be a quotient of the original field Heisenberg group and therefore satisfies $Z=H'$. One can check the quotient property from the scalar forms: the existence of a nonsingular $\beta$ for which the resulting $F[U]$ is a field is equivalent to the bimap being a quotient of a field-symplectic form. To check the converse, note that each ratio is self-adjoint for $\beta$ and their field is commutative, so the field action is balanced. Lift via the trace pairing as above. Each scalar coordinate $\gamma$ is the trace of the lifted form times its ratio $u\in U$, showing that the original commutator map factors through the field-valued symplectic form.

The same odd-prime test works inside the orthogonal-decomposition algorithm of the companion coefficient-field theorem. In any directly indecomposable source factor of the field-Heisenberg quotient type, the local test above handles its maps to sums of target blocks, regardless of the dimension of its commutator space. The common abelianization-rank test in the assembly still uses the original groups. This gives a polynomial algorithm for arbitrary directly decomposable mixtures of these source factors and source factors of bounded coefficient-field genus, against arbitrary same-prime odd-exponent targets.
The odd-characteristic trace construction reuses the earlier [MathProofs field Heisenberg quotient argument](https://github.com/Dugongue/MathProofs/blob/d323f03/GroupIsomorphismAndEpimorphisms/HeisenbergQuotientEpimorphisms.md). The square-map test above covers the characteristic-two family. The mixed-factor result uses the [companion genus-two proof](PROOF.md). These are informal proofs.
