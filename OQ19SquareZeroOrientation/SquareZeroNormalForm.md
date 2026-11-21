# An exact square-zero normal form for the ternary one-sign question

Let $F=\mathbb F_3$. For based spaces of alternating forms $D,D'$ on based spaces $V,V'$, a congruence $Y:V\to V'$ induces $f(B)=Y^{-\mathsf T}BY^{-1}$ from $D$ to $D'$. Write $\chi(Y)=\det(Y)\det(f)$ in the supplied bases.

**Theorem.** The problem of deciding whether $\chi=+1$ is attainable reduces in deterministic polynomial time to the identical sign question for alternating pencils with the following properties.

- The ambient dimension is twice an odd integer $m$.
- The singular locus inside the pencil is a single linear hyperplane $J$, and its formal Pfaffian is a nonzero constant times the $m$-th power of a linear form.
- For any invertible pencil member $\Omega$, the normalized pencil $\Omega^{-1}D$ is a commutative local algebra $F1\oplus N$ with $N^2=0$, and $J=\Omega N$.
- The common radical of the form space $J$ is a Lagrangian subspace for $\Omega$.

On the constructed instances, the tested sign equals the determinant of the induced map on $J$ in the constructed bases. Consequently a polynomial many-one reduction to ordinary TI for that radical determinant test would settle the full one-sign problem and, with the existing character assemblies, close TI versus TI_SL over $F$. The normal form and its equivalence are proved below.

## 1. A large block with neutral sign

If the raw sizes differ, use the normal-form image of the fixed pair on a two-dimensional space with source form basis $b$ and target form basis $-b$, for a nonsingular alternating $b$. Every raw transporter of this pair has product sign $-1$ by Pfaffian covariance. Suppose first that $n=\dim V$ is even. Choose an odd $r$ with $2r>\max\{n,\dim D+3\}$. Append a new space $S$ of dimension $2r$ with a fixed nonsingular alternating form $b$ in standard coordinates. Replace $V$ by $V_0=V\oplus S$ and $D$ by
$$
D_0=D\oplus Fb\ \subseteq\ \bigwedge^2 V_0^*.
$$
Use the old ordered bases followed by the new ones on both inputs. The subset of $D_0$ of forms of rank at most $n$ is exactly the original $D$, because any nonzero $b$-component contributes rank $2r>n$. It is therefore carried to its target counterpart by every congruence. Let $R$ be the common radical of the raw $D$. The common radical of that low-rank subspace inside $V_0$ is $R\oplus S$. A congruence of padded spaces therefore induces a congruence between the spaces of forms descended to $V_0/(R\oplus S)=V/R$ and its target analogue.

When $R=0$ on both sides, the latter common radical identifies $S$ itself, so a padded congruence induces a genuine original congruence on $V_0/S$. If the induced scalar on the quotient $D_0/D$ in the fixed $b$ bases is $\mu$, restriction to $S$ gives a symplectic similitude whose determinant is $\mu^{-r}$ by the Pfaffian covariance formula. The extra contribution to the product character is exactly $\mu^{1-r}=1$. Thus every padded witness induces an original witness with the same sign, and every original witness extends by the identity on $S$ with the same sign.

When the raw common radicals have unequal dimensions, no padded congruence exists, since their dimensions after adjoining $S$ would also differ. For nonzero radicals of equal dimension, the induced congruence on $V/R$ lifts to the raw spaces by choosing any isomorphism between the two radicals and lifting a complement. That lift can be adjusted on the radical by a reflection, which changes $\det(Y)$ and fixes every form. Thus both signs are attainable for the original pair as soon as a padded congruence exists. Direct sum with the identity on $S$ still gives the forward implication. The degenerate case $D=0$ follows by the same argument, with a zero-dimensional ambient space having character one.

For odd $n$, first append one zero direction to the ambient space, keeping $D$ unchanged. The underlying ordinary congruence verdict is preserved by passage to the quotient by the common radical and arbitrary lift back. Before this step $-I$ on odd-dimensional $V$ makes both signs attainable whenever there is a congruence. After it, a reflection on the new direction gives the same property. We have therefore reduced to the even case above. The padded ambient dimension $n_0=n+2r$ is even, and $d_0=\dim D_0<n_0-1$.

## 2. Move the whole character onto a space of forms

Set $U=V_0\oplus Fe$ with $e$ the last basis vector. Write $L=Fe^*$ and $X=V_0^*$ in $U^*=X\oplus L$. Form the based space
$$
J=D_0\oplus (e^*\wedge X)\subseteq\bigwedge^2 U^* .
$$
Use the ordered basis of $D_0$ followed by the wedges of $e^*$ with the supplied basis of $X$. Recover $L$ intrinsically as
$$
L=\{u\in U^*: u\wedge U^*\subseteq J\}.
$$
Indeed $L$ satisfies the inclusion. For $u=x+ce^*$ projecting to $x\ne0$ in $X$, the inclusion would imply $x\wedge X\subseteq D_0$. This space has dimension $n_0-1>d_0$, a contradiction. The annihilator of $L$ in $U$ is $V_0$.

Every congruence $p:U\to U'$ of these spaces thus restricts to a map $a:V_0\to V'_0$, and on the quotient $J/(L\wedge U^*)$ its induced form map is the original form action of $a$ on $D_0$. To see this, restrict each form to $V_0$; its kernel on $J$ is exactly $L\wedge U^*$. The map on $L\wedge U^*\simeq L\otimes (U^*/L)$ has determinant $c^{n_0}(\det a)^{-1}$ if $c$ is its scalar on $L$. Since $n_0$ is even and $F^\times=\{1,-1\}$, this is $\det a$. Therefore
$$
\det(\rho_J(p))=\det(a)\det(\rho_{D_0}(a)).
$$
Conversely every padded congruence extends by fixing $e$ and carries $J$ to $J'$ with this determinant. The common radical of $J$ on $U$ is zero: if $u\ne0$ and $e^*(u)=0$, take $x\in X$ with $x(u)\ne0$; if $e^*(u)\ne0$, any nonzero $x\in X$ suffices. In each case some $(e^*\wedge x)(u,-)$ is nonzero.

## 3. Add an intrinsically detected symplectic quotient

Let $m=\dim U=n_0+1$, and put $W=U\oplus U^*$. Write $\Omega$ for the standard hyperbolic alternating form in that order. Regard $J$ as a space of alternating forms supported on $U$ via the quotient $W\to U$. Our final based pencil, with $\Omega$ first, is
$$
\widehat D=F\Omega\oplus J.
$$
Writing $j$ in its $U$ block, the matrix of $t\Omega+j$ is
$$
\begin{pmatrix}j&t I\\-t I&0\end{pmatrix}.
$$
It is invertible exactly when $t\ne0$. Its Pfaffian is $t^m\operatorname{Pf}(\Omega)$ because every vertex in the second block has to be paired with one of the first block's vertices. The common radical of the singular form space $J$ in $W$ is exactly $U^*$ by Section 2. Any congruence $Z:W\to W'$ therefore carries both $J$ and this radical to their target versions. It induces a congruence $p$ of $J$ on $W/U^*\simeq U$.

Let $\epsilon$ be the scalar on $\widehat D/J$ using the respective $\Omega$ classes. The Pfaffian formula in the chosen ambient bases and the same fixed value of $\operatorname{Pf}(\Omega)$ on the two sides imply $\det Z=\epsilon^{-m}$. In the constructed label bases, the determinant of the induced map on $\widehat D$ is $\epsilon\det(\rho_J(p))$. Since $m$ is odd and $\epsilon^2=1$, their product is exactly $\det(\rho_J(p))$. Conversely, any congruence $p$ of $J$ lifts to $p\oplus p^{-\mathsf T}$ on $W$, preserving $\Omega$ and inducing precisely its original action on $J$. The desired sign is attainable in the output exactly when it was attainable in the input, by the preceding two sections.

In the same coordinates $\Omega^{-1}j$ is supported on just one off-diagonal block, so the product of any two such operators is zero. Therefore the ratio algebra is $F1\oplus\Omega^{-1}J$ with square-zero nilradical. Changing the invertible normalization to $t\Omega+j$ multiplies the ratio algebra by one of its own units and leaves it the same subalgebra. Also $U^*$ is Lagrangian for each $t\Omega+j$ with $t\ne0$. This proves every claimed output property. The construction uses only block insertions and wedges with one marked basis vector. With $2r=O(n+\dim D+1)$, the output dense size is polynomial.

The normal form is recognizable by checking a nonsingular basis slice, computing its ratio algebra and testing that it is $F1$ plus a square-zero ideal of codimension one. Within this family any basis has a nonsingular slice, since nonunits comprise one proper hyperplane. If an explicit recognition test is needed, verify the algebra identities by multiplication tables, verify the dimension and square-zero property of the radical, and test the intersection of the kernels of the corresponding singular forms for the asserted Lagrangian property. The radical is computed by the kernel of Frobenius on the commutative ratio algebra in this square-zero case.

## 4. A specified anchor can be matched exactly

On these outputs an arbitrary congruence can be made to carry the displayed source $\Omega$ to the displayed target $\Omega'$ without changing the tested sign. To see this, suppose that its transported form is $\epsilon\Omega'+j$. Put $T=(\Omega')^{-1}j/\epsilon$. The square-zero ratio ideal gives $T^2=0$ and $T\,(\Omega')^{-1}J'=0$. The operator $T$ is self-adjoint for $\Omega'$, since $\Omega'T=j/\epsilon$ is alternating. The target shear $S=I-T$ has determinant one and inverse $I+T$. Its transport of the shifted form is
$$
S^{-\mathsf T}\bigl(\epsilon\Omega'(I+T)\bigr)S^{-1}
=\epsilon\Omega'(I+T)^3=\epsilon\Omega'
$$
in characteristic three. It fixes every element of $J'$ and induces the identity on the quotient by $J'$, so its label determinant is also one. If $\epsilon=-1$, the target transformation $I_{U'}\oplus(-I_{(U')^*})$ changes the sign on $\Omega'$ and fixes all of $J'$. Its ambient determinant and its label determinant are both $-1$ because $m$ is odd, so its product sign is one. Thus exact matching of the chosen anchors preserves all attainable product signs. After matching, the ambient map is symplectic and the determinant test is solely on the induced radical action. This removes the need to find matching nonsingular slices in this normal form, even though the unrestricted orienting test on the radical is still required.

The earlier square-zero extension for general matrix slices is a precedent for the ratio algebra construction. The new part here is the alternating congruence normalization and exact transfer of the combined sign to the radical, including arbitrary raw basis changes.

## Connection to the three-sign endpoint

The source one-sign predicate is the alternating-space congruence predicate reached by the existing ternary sign-preserving suspension reductions. Their castling transformations make the three flavors of one-character test equivalent, and the three determinant signs of any transporter lie in a coset of a subgroup of $\{1,-1\}^3$. The seven nonzero characters separate the identity coset, so seven independent one-character tests followed by fixed conjunctive packing suffice. [Chen–Grochow–Qiao–Tang–Zhang, Open Question 1.9](https://arxiv.org/html/2306.03135v2#S1.SS5)

The reduction above is a written complexity proof. It provides exact preprocessing to a fixed recognizable family even when the input Pfaffian is identically zero. The resulting radical determinant still refers to automorphisms of the represented square-zero algebra, linked to its action on $W$. Radical units and the action of algebra isomorphisms on the radical are different. In this normal form the latter action carries the entire source sign.
