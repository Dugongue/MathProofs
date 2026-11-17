# Preserving all three base-field signs in cubic-extension norm TI

There is a deterministic polynomial-time encoding from arbitrary $\mathbb F_3$ tensor pairs to concise $\mathbb F_{27}$ tensor pairs with local centroid and residue $\mathbb F_{27}$. The exact base-field determinant signs $(d_U,d_V,d_W)$ of transporters become the exact norm signs
$$
              (d_U d_V d_W,\ d_V,\ d_U).
$$
This applies to the semilinear version allowing one common Frobenius in all three modes. In particular the map is invertible on the sign triple, even on arbitrary raw pairs.

Use the faithful balancing in [the scalar-centroid proof](ScalarCentroidGlue.md) to begin with concise tensors of even common side length. Adding a larger even determinant-trivial cubic path pencil, described in that proof, makes the common size $d$ divisible by eight without changing any sign set. Treat trivial zero or malformed cases directly. Regard the tensors as bilinear maps $\mu:U\times V\to W$; over $\mathbb F_3$ dualizing modes does not affect signs. Put $E=\mathbb F_{27}$. All spaces in the output have explicit bases, and all its structure constants will lie in $\mathbb F_3$.

## 1. Two graded commutative algebras

For a $d$-dimensional based space over $E$, define the local algebra $C_L$ with $L=3$ or $7$ by taking the polynomial algebra in $t,x_1,\ldots,x_d$, imposing $x_i^3=t^2x_i$, and discarding all degrees greater than $L$. A basis comprises the monomials of degree at most $L$ with $x_i$-exponents at most two. Indeed reduce $x_i^3$ to $t^2x_i$, an operation that terminates and commutes on different offending exponents. It preserves total degree. More formally the rules $x_i^3-t^2x_i$ have pairwise coprime leading monomials in graded order with $x_i$ preceding $t$, so they give these normal forms before truncation as well. The radical is the positive-degree ideal and its powers are the degree filtration. Truncated dimensions for $L=3,7$ are polynomial in $d$.

For any isomorphism on $C_L$ use its action on the associated graded algebra. In degree two the elements $a$ with $a C_{L,1}$ contained in the span of degree-three cubes are exactly $E t^2$. The cube span is $t^2 C_{L,1}$. To check the characterization, multiplication by $t$ first excludes all $x_i x_j$ terms in $a$, including squares; multiplying the remaining $t x_i$ terms by an $x_j$ then excludes those terms. Normal forms in degree three make the exclusions independent. Thus the degree-one action sends $t$ to $\lambda t'$, since in odd characteristic the square of any linear form with a nonzero $x_i$ coefficient contains a nonzero $x_i^2$ coefficient. Applying the cubic relations to the other degree-one images now forces every coefficient $b$ to satisfy $b^3=\lambda^2 b$. Hence the full degree-one action is $\lambda h$, with $h$ a base-field linear map fixing $t$. Denote its induced map on the $x$-quotient by $h_0$. Conversely such base-field actions $h$ and uniform scalars $\lambda$ preserve the homogeneous relations. In particular base-field maps on the $x$-coordinates extend while fixing $t$.

The norm of the determinant of a branch algebra map is exactly $\det_{\mathbb F_3} h_0$. Here is the parity calculation. The Hilbert series of the normal forms before truncation is $(1+z+z^2)^d/(1-z)$. Modulo two its coefficients up to degree seven are all one, since $8\mid d$. Both truncated dimensions are therefore even and uniform scaling contributes exponent $\sum_{j=0}^L j\dim C_{L,j}$, even for $L=3,7$. On $h$, transvections and adding $t$ to any $x_i$ contribute determinant norm one, by their order three. Together with one coordinate reflection these operations generate the group of base-field maps fixing $t$. A reflection on $x_1$ contributes sign $-1$ once for each basis monomial having $x_1$-exponent one. The parity of their number is
$$
 [z^{L-1}]\frac{(1+z+z^2)^{d-1}}{(1-z)^2}
     =[z^{L-1}]\frac{1}{(1+z)(1+z^3)}
       \quad\text{over }\mathbb F_2,
$$
for $L\le7$. This coefficient is one at $L-1=2$ and at $6$, because the numbers of choices of the power of $z^3$ are one and three, respectively. Norm carries $-1$ to $-1$ in the odd-degree extension $E/\mathbb F_3$. Higher-degree shears in the isomorphism give determinant one. This proves the formula.

## 2. A local algebra incorporating the tensor

Let $C_U=C_3$, using $U$ for the $x$-variables and call its tag $t$, and let $C_V=C_7$ with $V$ for the variables and tag $s$. Form a single unital algebra $A_\mu$ with radical
$$
       J_U\oplus J_V\oplus W_E\oplus Z,
       \qquad Z=zE[z]/z^{12}E[z],
$$
where $J_U,J_V$ are the positive-degree branches and $W_E=E\otimes W$. Each branch has its own usual multiplication, including $Z$. The only mixed product is the given oriented product $\mu$ from the $U$-variables in the first tangent space to the $V$-variables in the second; it lands in $W_E$. This product ignores both tag lines and all higher degrees. All products involving $W_E$ in the radical are zero. Associativity follows because any triple with radical terms from different branches vanishes under both associations, and each individual branch is associative. The algebra is local with residue $E$, since its radical is nilpotent. Put
$$
 I_U=J_V\oplus W_E\oplus Z,\qquad I_V=J_U\oplus W_E\oplus Z .
$$
These are ideals with quotients $C_U,C_V$. Their intersection is $W_E\oplus Z$, and $W_E$ is exactly the span of algebra commutators, by conciseness of $\mu$. Each branch algebra has even dimension, and $Z$ has odd dimension eleven. Since $\dim W$ is even, $A_\mu$ has even dimension.

Take an $E$-algebra isomorphism $\phi$ carrying both marked ideals to their corresponding target ideals. On the two branch tangent quotients modulo their tags it has maps $\lambda_U h_U,\lambda_V h_V$, with $h_U,h_V$ over $\mathbb F_3$. Commutators of representatives from the two marked branches induce the original bilinear equation. Specifically, by the preservation of $I_V$ and $I_U$ respectively, images of the original tangents have no tangent on the opposite branch, and all extras in higher degrees or tag variables are ignored by the mixed product. Thus on $W_E$ its map has the form $\lambda_U\lambda_V h_W$ with $h_W$ defined over $\mathbb F_3$, since the original products span $W$. The three $h$'s give an actual base-field transporter. Conversely every base-field transporter extends to an algebra isomorphism respecting both ideals and fixing $t,s,z$.

The determinant norm on $W_E$ is $d_W$, since its dimension is even. On $(I_U\cap I_V)/W_E=Z$ the determinant has trivial norm: a string automorphism with leading coefficient $a$ has determinant $a^{1+\cdots+11}=a^{66}$. The quotient $A_\mu/(I_U\cap I_V)$ is the fiber product of the two branch algebras over their scalar residue. Its determinant norm is the product of those on the two branches, since the map on their common residue is the identity. Therefore the determinant norm on $A_\mu$ is $d_Ud_Vd_W$.

## 3. Read the three signs by a single concise tensor

Use a pencil indexed by $a\in A_\mu$. Its matrix is block diagonal with two copies of regular left multiplication $L_a$, one block $K_U(a)$, and the transpose of one block $K_V(a)$. For either quotient $C=A_\mu/I$ use
$$
 K(a):E^2\to C,\qquad K(a)=\bigl[\bar a,\ \epsilon(a)e\bigr],
 \qquad e=t^2\text{ or }s^2,
$$
where $\epsilon(a)$ is the scalar residue. The regular block is fixed-label indecomposable because its endomorphism ring is the local algebra of right multiplications. The rectangular block is fixed-label indecomposable as well. Indeed a fixed-label endomorphism on its column space has matrix $\begin{pmatrix}p&q\\r&b\end{pmatrix}$. The second-column equation on the radical gives $q=0$. The first-column equation gives the row action $pI+r e\epsilon$; the second-column equation at $1$ gives $b=p$. Its endomorphism ring is local (the $r$-part is nilpotent). Every such unit has determinant norm one on both modes because $\dim C$ is even. The transposed block has the same conclusion. The three block types have different ordered dimensions, except for the two deliberately identical regular blocks. The pencil is concise in the label by the faithful regular blocks, and in the matrix modes because the rectangular blocks have zero common kernel and full image span, and so do the regular blocks.

Any transporter of pencils, with arbitrary label map $a\mapsto s_0(a)$, gives an isomorphism of the fixed-label quiver representations after relabeling by $s_0$. Krull–Schmidt ensures the comparison respects the three block types; one can choose block-diagonal maps for the given label map. Other choices with the same label differ by fixed-label automorphisms. These carry no determinants: each rectangular local factor has the trivial unit norm just proved, and regular pairs on two copies act by $A_\mu$-module units on a free rank-two module. Their determinants are powers with exponent $\dim A_\mu$, even, as can be read on the radical filtration. Off-diagonal radical terms in the endomorphism algebra are nilpotent and contribute determinant one. Equivalently the semisimple quotient of this endomorphism algebra is one $2\times2$ matrix block for the regular pair and two scalar factors for the rectangular blocks, by the standard Krull–Schmidt endomorphism-ring description.

The regular pair forces $s_0(a)=u\phi(a)$ with $u$ a unit and $\phi$ an algebra isomorphism, by the same action argument as [the regular sign encoder](CastlingAndConjunction.md). Its two matrix modes have trivial determinant norm. The label determinant norm is that of $\phi$, since left multiplication by a unit on an even-dimensional local algebra has determinant with trivial norm. The rectangular block's kernel in the label space is exactly its designated ideal. Hence $s_0$, and then $\phi$, preserve the two marked ideals as required.

For a rectangular comparison identify the quotient action as $s_C=u_C\phi_C$. With $P=\begin{pmatrix}p&q\\r&b\end{pmatrix}$ the column map, compare the two columns of $H K(a)=K'(s_0(a))P$. On the radical this gives $q=0$. The first column gives $H=p s_C+r\epsilon(u)e'\epsilon$. In degree two the second column at $1$ gives
$$
           p\,\epsilon(u)\lambda^2=b\,\epsilon(u),
$$
because $\phi_C(e)$ has leading term $\lambda^2 e'$. Thus $b/p=\lambda^2$, and the column determinant is a square. The row action has determinant norm equal to that of $\phi_C$, because $p^{\dim C}$ and the determinant of $u_C$ have trivial norm and the rank-one extra term contributes determinant one ($s_C^{-1} e'$ has zero residue). Conversely the isomorphisms built from an original base-field witness fix the tag lines exactly and extend on each rectangular block with identity column map. Transposing $K_V$ exchanges the row and column contributions; inverses do not affect norm signs. This proves that the exact sign triple of the pencil is $(d_Ud_Vd_W,d_V,d_U)$.

The centroid has local residue $E$. Over an algebraic closure, the label map $f$ of a centroid idempotent satisfies, in the diagonal block of any faithful regular copy, $L_{f(a)}=H_{LL}L_a$. At $a=1$ this gives $f(a)=f(1)a$. If $f$ is idempotent then $f(1)$ is an idempotent of the local algebra, hence zero or one. Conciseness forces every slot of the centroid idempotent to be the same trivial choice. Thus the tensor is geometrically indecomposable and its finite-field centroid has local residue $E$. This uses the fact that a finite residue extension splits into multiple components over the algebraic closure.

Every coefficient is in $\mathbb F_3$. A common Frobenius in all three modes has no effect on these coefficients and has determinant-one contribution over $\mathbb F_3$, since $E/\mathbb F_3$ has degree three. Thus the semilinear norm condition gives the same exact signs.

## 4. Equivalences with cubic norm problems

The previous trace construction gives the upper direction in each case.

* Candidates 15 and 18 are many-one equivalent to the base one-character class. The sign projection of the new label is the original total sign, and the product of all output signs is the original $W$-sign.
* Candidate 16 is many-one equivalent to the base two-fixed-orientations class (and hence to the common class of 4–6). Use the two output matrix modes for the tested orientations, permuting modes as needed. They read $d_U,d_V$.
* Candidate 17 is many-one equivalent to base SL-TI because all three signs are preserved by an invertible transformation.
* Candidate 20 is many-one equivalent to base SL-TI. Include the construction for 17 as its cubic block and append one common quadratic block comprising the regular left action of $E_2[t]/t^4$ on two copies of itself, where $E_2=\mathbb F_9$. Its three $E_2$-dimensions are $4,8,8$, and its centroid is the local algebra $E_2[t]/t^4$, by the regular-action centroid computation. An algebra automorphism acts triangularly on $t,t^2,t^3$, with diagonal factors $a,a^2,a^3$; its determinant is $a^6$, of norm one. As in the regular-action sign encoder, units and doubling add no norm signs. The tensor coefficients are in $\mathbb F_3$ and the even dimensions make quadratic Frobenius neutral as well. This fixed block therefore contributes no possible sign correction. It cannot exchange with the cubic block because its trace-centroid residue has different field degree.

The even extension $\mathbb F_9/\mathbb F_3$ sends both base-field signs to norm one, so this odd-degree encoding gives no reverse comparison for candidate 19. The conclusions here are informal proofs, with earlier building blocks credited in the linked notes.
