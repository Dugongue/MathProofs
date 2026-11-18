# Lifting unitary witnesses with arbitrary semisimple matrix blocks

Informal research theorem. Let $A$ be a finite-dimensional algebra over an explicitly presented finite field $F$ of characteristic two, with an $F$-linear involution $*$ and Jacobson radical $J$. Let $c=c^*\in A^\times$. All costs below refer to the structure-constant input and the explicit field presentation. Finite-algebra decomposition may use Las Vegas algorithms. The algorithms after decomposition are deterministic.

The previous commutative-quotient proof gives polynomial-time norm testing and exact counting when $A/J$ is a product of fields. Here we identify every graded obstruction for a general matrix quotient. We prove a larger polynomial-time case and an algorithm exponential only in the written matrix-block coordinates that remain active in those obstruction spaces. This retains the same quotient candidate through all radical layers.

## Exact new sufficient theorem

Write $S=A/J$ as a product of simple matrix algebras and partition the factors into involution orbits $i$. Let $C_i$ be the unitary group of one such orbit. For each $k\ge1$ define the graded defect space
$$
T_k=\frac{\{x\in J^k/J^{k+1}:x^*=x\}}
{\{x+x^*:x\in J^k/J^{k+1}\}}.
$$
Each $T_k$ is a binary vector space carrying the right action $x^s=s^*xs$ of $C=U(S,*)$. The decomposition in Section 1 expresses it as a direct sum over the involution orbits of $S$. Call an orbit active when one of its summands in some $T_k$ is nonzero.

Suppose every inactive noncommutative orbit group $C_i$ has no nontrivial homomorphism to the additive group $\mathbb F_2$. Suppose also that every active noncommutative orbit is assigned to an explicitly enumerated part. If the total number of bits needed to specify arbitrary elements of those enumerated matrix algebras is $b$, norm testing, construction of one norm witness and exact counting take
$$
2^b\operatorname{poly}(L)
$$
bit operations after the usual Las Vegas algebra preprocessing. In particular the result is polynomial if $b=O(\log L)$. The inactive matrix factors have arbitrary sizes, and the scalar factors and radical have arbitrary dimensions and nilpotency lengths.

When there are no active noncommutative factors, the algorithm is polynomial on every input satisfying the stated inactive-group hypothesis. That hypothesis holds, for example, for exchanged $M_n(E)$ pairs with $n\ge3$, and for first-kind symplectic factors $\operatorname{Sp}_{2m}(E)$ with $m\ge3$. Indeed $\operatorname{SL}_n(E)$ is perfect in the former case and the determinant quotient has odd order, while the latter symplectic groups are perfect in characteristic two. The property is about the finite residue groups. It does not assert that the residue algebra or its unit group is commutative.

A solution to the residue norm equation must first exist. This is the standard finite classical bilinear or Hermitian isometry problem, solved by elimination. Once one solution is found, choose a lift $a$ and replace $c$ by $(a^*)^{-1}ca^{-1}$, so $c\equiv1\bmod J$. A final normalized solution $w$ gives $wa$ for the original problem. All statements allow rejection at this first test.

## 1. The obstruction modules of a matrix quotient

Put $M=J^k/J^{k+1}$. Left and right multiplication by $S$ are well defined. Its central Peirce blocks $e_iMe_j$ are swapped by the involution as $(i,j)\mapsto(j^*,i^*)$. A pair of distinct swapped blocks contributes zero to the fixed-space quotient by traces. Its fixed vector is the trace of its part in one of the blocks. Thus only $e_iMe_{i^*}$ remains.

Let $E_i$ be the center field of the factor at $i$. Identify the opposite center at $i^*$ with $E_i$ by the involution, and decompose the block into
$$
M_\theta=\{x:xa^*=\theta(a)x\ \text{for all }a\in E_i\},
$$
for the automorphisms $\theta$ of $E_i$ over the prime field. The decomposition follows from the split factors of $E_i\otimes_{\mathbb F_2}E_i$. The involution takes the $\theta$ summand to the $\theta^{-1}$ summand and is $\theta^{-1}$-semilinear in left scalars. Distinct inverse twists again have no fixed/trace quotient. On a fixed nonidentity twist choose $a$ with $a+\theta(a)=1$. A fixed vector $x$ is then the trace of $ax$. Hence only $\theta=1$ survives.

Using matrix units, this surviving bimodule is a sum of copies of a matrix bimodule of size $n_i$. The involution, after a change of coordinates by the matrix defining the residue adjoint and by the center involution where applicable, is matrix transpose combined with an $E_i$-linear involution on its multiplicity space. This follows directly because composing with transpose makes the map commute with both matrix-unit actions. An involution on a vector space in characteristic two has Jordan blocks of size one or two. A size-two multiplicity block has fixed space equal to the trace image and contributes zero. Each size-one block leaves
$$
\operatorname{Sym}_{n_i}(E_i)/\operatorname{Alt}_{n_i}(E_i).
$$
The diagonal map identifies this quotient with $E_i^{n_i}$. Congruence by $g$ acts on a symmetric matrix's diagonal by the entrywise square of $g$, since the off-diagonal cross terms occur twice. If semilinear coordinates were used, apply the corresponding field automorphism as well. These are Frobenius twists of a natural or dual representation of $C_i$. For an exchanged pair the two fixed Peirce blocks give one natural and one dual action. The two actions are allowed to occur with multiplicity.

This proves that $T_k$ has a direct decomposition by the involution orbits of the semisimple algebra. Every factor acts trivially on all other summands. The assertion includes nonsplit residue fields and arbitrarily large matrix sizes. The transformations and quotient bases are computable by field-linear algebra on matrix units and prime-field linear algebra for field twists.

The dimension is also informative. An active orbit with matrix size $n_i$ and center of binary degree $e_i$ contributes at least $n_ie_i$ binary dimensions to $\bigoplus_kT_k$. For an exchanged orbit the two simple matrices have the same size and field. Thus, if every inactive noncommutative group has the no-order-two-quotient property, and $h=\sum_k\dim_{\mathbb F_2}T_k$, enumerating all active noncommutative matrices costs at most $2^{O(h^2)}$. This bound has polynomial preprocessing and polynomial work per enumerated candidate. It yields a parameterized sufficient algorithm independent of the dimensions of inactive matrix blocks.

## 2. Preserve the exact residue image through the radical

Let $U=1+J$. Its elements act trivially on each $J^k/J^{k+1}$. A chosen residue solution can therefore be lifted or rejected in polynomial time by successive additive defects. With target $c$, set
$$
K_k=\{v\in U:c^v\equiv c\bmod J^k\},\qquad
\delta_k(v)=c^v-c\bmod J^{k+1}.
$$
The map $\delta_k:K_k\to J^k/J^{k+1}$ is an additive homomorphism. Its image $R_k$ consists of fixed elements and contains every trace $x+x^*$, by using $v=1+x$ for $x\in J^k$. Its kernel is $K_{k+1}$.

Given the radical generators, group preimages and kernels are computed with a binary central-series generating sequence, obtained by refining the powers of $J$. The number of positions is at most $\log_2|J|$, so the subgroup order and the size of a nonempty fiber are computed in polynomial time too. Equivalently this is a unipotent vector transporter in the congruence representation. This mechanism is already present in Sun's Appendix A. [Sun, Lemma A.24 and Appendix A](https://arxiv.org/pdf/2611.05920).

Let $G$ be the preimage of the residue subgroup currently allowed. Define
$$
H_k=\{g\in G:c^g\equiv c\bmod J^k\},\qquad C_k=\operatorname{im}(H_k\to C).
$$
The kernel is $K_k$. Set $W_k=M^+/R_k$, a quotient of $T_k$. For $s\in C_k$, lift it to $g\in H_k$ and take the class of $\delta_k(g)$. This defines a right cocycle $d_k$ with
$$
d_k(st)=d_k(s)^t+d_k(t).
$$
It is independent of the chosen lift because the differences are in $R_k$. The subspace $R_k$ is invariant under $C_k$ by conjugation in $H_k$. A current source $a$ matching $c$ modulo $J^k$ advances exactly when
$$
e^s+d_k(s)=0\quad\text{in }W_k,\qquad e=a-c\bmod J^{k+1}.
$$
A solution is then corrected in $R_k$ by an actual element of $K_k$, computed by the unipotent routine. The next residue stabilizer is $\{s:d_k(s)=0\}$.

This description keeps the residue subgroup and the radical fiber coupled. The pointwise fact that every fixed residue fiber can be solved does not by itself give a polynomial search over all residues.

## 3. Omit invisible matrix groups, keep the scalar factors exactly

Let $K$ be the product of all inactive noncommutative orbit groups. It acts trivially on every $T_k$ and hence on every available $W_k$. Assume inductively that $K\subseteq C_k$. The restriction of $d_k$ to $K$ is an additive homomorphism, since its action on $W_k$ is trivial. The hypothesis $\operatorname{Hom}(K,\mathbb F_2)=0$ implies this restriction is zero. Thus every element of $K$ still has a lift at the next grade and $K\subseteq C_{k+1}$.

Moreover $K$ cannot change the affine feasibility condition, so one may choose the identity residue in all its coordinates during witness construction. Its full order multiplies the solution count. This is a sufficient criterion for retaining large matrix factors without enumerating them.

Fix one tuple of active noncommutative residue elements and lift it, then solve for all scalar residue coordinates while keeping the inactive coordinates implicit. Each fixed tuple has a unique disjoint residue label, so summing the fiber counts over these labels counts all solutions exactly. After this fixing, the varying quotient is $K$ times a product of scalar tori. The scalar torus acts on its fixed/trace modules by $u^2$ or $u^{-2}$ on one or two summands, just as in the commutative-quotient proof. The remaining noncommutative defect spaces are trivial modules for this varying group.

For completeness, the scalar selection argument works as follows. At each grade the image of the scalar quotient is a product in which a coordinate is either the whole original torus or identity. A nonidentity element of one free torus acts without nonzero fixed vectors on its corresponding summands and trivially on the other summands. Thus the projection to that component is a polynomial in this action minus identity. Invariance of $R_k$ implies the decomposition survives in $W_k$. A cocycle on a free torus component has the form $z^s-z$, recovered by inverting the action minus identity at one nonidentity torus element. On the trivial component every cocycle is zero, since the group has odd order and the vector space has characteristic two.

The affine feasibility equation is therefore $(e+z)^s=z$ independently on each free scalar factor. A nonzero vector determines at most one scalar parameter; zero vectors require matching zero vectors or leave that parameter free. The parameter is recovered by field-linear equations and the unique square root, then checked against all its marked components and the norm-one condition if present. The exchanged-field reciprocal characters split into inequivalent simple modules except at $\mathbb F_4$, where Frobenius identifies the two types; the $\mathbb F_2$ factor is trivial. A norm-one field torus spans its entire field, so its invariant subspaces are linear over that field. These facts make the scalar test polynomial without a multiplicative primitive-element oracle. The next stabilizer either pins each coordinate to identity or leaves it wholly free, preserving the induction.

Every finite residue tuple and final radical fiber is disjoint. The final count for a fixed enumerated label is
$$
|K_{\mathrm{final}}|\ |K|\ \prod_{\text{free scalar coordinates }i}|C_i|.
$$
All factors have polynomial bit length. The algorithm chooses one residue representative from any nonempty fiber and then uses the stored radical corrections to produce the norm witness.

## 4. A connected example without a stable semisimple section

Take $E=\mathbb F_4$, odd $n\ge7$, and $\ell\ge3$. Let
$$
S=M_n(E)\times E\times E
$$
with central idempotents $e_0,e_1,e_2$. Start with the following radical pieces. The blocks $e_1Je_1$ and $e_2Je_2$ are the nonunital ideals $tE[t]/(t^\ell)$, with their usual multiplication. Add a column module $e_0Je_1=E^n$, a row module $e_2Je_0=(E^n)^t$, and a one-dimensional block $e_1Je_2=E\eta$. All products involving one of these last three pieces and another radical piece are zero. The scalar constant terms act on those pieces in the usual way, and the matrix factor acts on the column and row by matrix multiplication. These prescriptions give an associative algebra $A=S\oplus J$. It is connected through its radical blocks, with radical length $\ell$.

Define an initial involution $\dagger$ by transpose on $M_n(E)$, exchange of the two scalar factors and their $t$-ideals, exchange of the column and row by transpose, and $\eta^\dagger=\eta$. These rules respect all products. Let $a=1+\eta$ and set
$$
x^*=a x^\dagger a^{-1}.
$$
Because $\eta^2=0$ and $a^\dagger=a$, this is an involution. It induces the same residue involution as $\dagger$ and agrees with $\dagger$ on $J$, since every product with $\eta$ and another radical element is zero.

The column and row give paired Peirce blocks and disappear from the fixed/trace quotient. The two diagonal $t$-ideals are likewise paired and disappear at every grade. The only defect module is $E\eta$ in the first grade. The matrix factor acts trivially on it; its unitary residue group is the isometry group of the nonalternating dot product, which for odd $n$ identifies with $\operatorname{Sp}_{n-1}(E)$. The characteristic vector has norm one and splits off a canonical fixed line with a nondegenerate alternating complement. This group is perfect for the stated dimensions. Thus the sufficient theorem handles every self-adjoint-unit norm target on these examples in polynomial time.

The example has no involution-preserving algebra section $S\to A$. To prove this, a residue unitary in the scalar pair has coordinates $(u,u^{-1})$. For its canonical lift $g$ with matrix coordinate identity,
$$
g^*g\equiv1+(1-u^{-2})\eta\pmod {J^2}.
$$
Every radical adjustment changes this defect by a trace. The trace on $E\eta$ is zero and $J^2$ has no $\eta$ component. Consequently this residue is liftable only when $u^2=1$, which over $E$ requires $u=1$. A section preserving the involution would lift every residue unitary, including either nonidentity element of $E^\times$. This contradiction proves the assertion.

The earlier sufficient hypothesis of a supplied involution-preserving semisimple section therefore does not cover this family. The new algorithm retains the unrestricted large symplectic factor while finding the pinned scalar coordinate, and it does so at every radical depth.
## 5. Return to ordered matrix tuples and the remaining scope

Given ordered tuples, close them under transpose and compute a left–right equivalence by module isomorphism. The standard adjoint algebra converts the problem into a norm equation. If $X^tA_iY=B_i$, set
$$
\mathcal A=\{(L,R):L^tA_i=A_iR\},\qquad
(L,R)(L',R')=(LL',R'R),\qquad (L,R)^*=(R,L).
$$
Its self-adjoint unit is $(YX^{-1},YX^{-1})$. Norm solutions correspond bijectively to isometries by $P=LX$, with inverse $(PX^{-1},YP^{-1})$. Thus the sufficient theorem and count transfer to the raw ordered tuple inputs after checking the adjoint quotient and its graded defects. [Ivanyos–Qiao](https://arxiv.org/abs/1708.03495), [finite algebra decomposition](https://doi.org/10.1016/S0747-7171(08)80017-X).

The arbitrary characteristic-two tuple question in Part V remains open in this document. The new extension handles arbitrary matrix factors which are invisible to every graded obstruction and have the stated no-order-two-quotient property, together with every scalar factor and every radical depth. The action on the active noncommutative blocks is a classical affine action on subquotients of Frobenius natural modules. A full proof would need to maintain and solve those affine stabilizers through every grade. At a first symplectic layer a quadratic-refinement cocycle can occur; after several layers the residue stabilizer can contain unipotent radicals and fixed marked subspaces. Independent fresh classical isometry tests would discard the accumulated lift constraints. The supplied theorem retains those constraints in its covered cases and makes no broader collapse assertion.
## Audit status and source attribution

The source question is the final paragraph of Part V, §1.4: polynomial-time matrix tuple isometry in characteristic two, including its finite-field case. The present conclusion is sufficient on the explicitly characterized adjoint class. It includes witness construction and count, and charges all coefficient-field and radical coordinates. No numerical experiments or Lean certification were used for this proof.

The radical-fiber mechanism and the need to retain quotient representatives are already explicit in Sun's November 2026 Appendix A. The graded matrix-bimodule calculation generalizes the earlier square-zero radical note to every radical grade. The independent-torus induction comes from the preceding commutative-quotient proof. The additional result here retains arbitrary large matrix factors exactly when they are invisible on all those defect modules and have no elementary abelian quotient of exponent two. The cited classical group cases give concrete sufficient examples. Priority of this restricted all-depth theorem has not been established.
