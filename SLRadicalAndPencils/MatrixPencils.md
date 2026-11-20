# Deterministic polynomial-time special-linear equivalence of matrix pencils over finite fields

## Statement

Let the field $F=\mathbf F_q$ be explicitly represented in a polynomial basis. Given positive integers $m,n$, two $m$ by $n$ matrix pencils $A(x)=x_1A_1+x_2A_2$ and $B(x)=x_1B_1+x_2B_2$, and any $c,s,t\in F^\times$, there is a deterministic algorithm, polynomial in the input bit length, to decide whether there are
$$
 f\in\mathrm{GL}_2(F),\qquad g\in\mathrm{GL}_n(F),\qquad h\in\mathrm{GL}_m(F)
$$
such that $B(fx)g=hA(x)$, $\det f=c$, $\det g=s$, and $\det h=t$. It applies to rectangular, singular, and zero pencils, in every characteristic, with $q$ varying. It uses deterministic field arithmetic, polynomial and integer linear algebra, and module isomorphism. The algorithm need not output a witness.

The covariant tensor action $B(y)=H A(L^{\mathsf T}y)K^{\mathsf T}$ corresponds to $f=L^{-\mathsf T}$, $g=K^{-\mathsf T}$, and $h=H$. Thus the case $c=s=t=1$ is special-linear three-tensor isomorphism with a two-dimensional mode. This family has a same-field polynomial many-one reduction to ordinary tensor isomorphism by outputting fixed scalar yes and no instances according to the decision. The theorem also extends in a straightforward manner to a one-dimensional mode by testing its unique prescribed label map.

The ordered determinant-image algorithm proved next works for arbitrary label dimension. It also gives a polynomial-time test for any polynomial-size explicit list of prescribed label maps with one fixed determinant in the other two modes.

## Ordered equivalence with prescribed determinants

Fix the label map and incorporate it in the target arrows. Compute an ordered isomorphism $(g_0,h_0)$ if one exists. This is constructive module isomorphism on the direct sum of the two vertex spaces. Two vertex projectors and the zero-extended arrows form the list of operators whose simultaneous intertwiners are sought. The vertex projectors force block diagonal intertwiners. The Brooksbank–Luks algorithm uses a deterministic number of field operations polynomial in the input dimensions. [Brooksbank and Luks, Theorem 3.5](https://ix.cs.uoregon.edu/~luks/ModIso.pdf)

All ordered isomorphisms form the right coset of $(g_0,h_0)$ by the units in the source endomorphism algebra
$$
D=\{(a,b): A_i a=b A_i\text{ for every }i\}.
$$
This algebra is given by a linear system and represented faithfully as a matrix algebra on the direct sum. Compute its Jacobson radical $J$ deterministically with the Cohen–Ivanyos–Wales algorithm. Its semilinear steps over characteristic $p$ reduce to linear systems over $F_q$, since applying inverse Frobenius to a $p$-linear equation turns it into a linear equation. Computing the semisimple quotient $S=D/J$ and its center $Z$ then uses linear algebra. [Cohen–Ivanyos–Wales, §4.1](https://citeseerx.ist.psu.edu/document?doi=aa8d087d1a4b17eb1264065391e109e0ebdbf122&repid=rep1&type=pdf)

The finite semisimple algebra has a theoretical decomposition $S=\prod_j M_{u_j}(E_j)$ over finite fields $E_j$ extending $F$. For each of the two vertex spaces $V$, take the sum $\mathrm{gr}_J V$ of the successive quotients of $V\supset JV\supset J^2V\supset\cdots\supset 0$. Let $a_{V,j}$ be the total multiplicity of the simple $E_j^{u_j}$ across these quotients. An element acting by $U_j$ on this simple module has determinant over $F$ equal to $N_{E_j/F}(\det_{E_j} U_j)$. The determinant on $V$ is the product across its successive quotients. The map $D^\times\to S^\times$ is onto since $J$ is nilpotent, and each norm $E_j^\times\to F^\times$ is onto. Therefore the ordered stabilizer's image in $(F^\times)^2$ is precisely the image of the exponent matrix whose columns are $(a_{F^n,j},a_{F^m,j})^{\mathsf T}$.

One can compute the distinct columns without constructing the individual $E_j$. For each $Z$-module $Q$ among $S,\mathrm{gr}_J F^n,\mathrm{gr}_J F^m$, repeatedly choose a nonzero vector $v$ in the current quotient and compute $K=\operatorname{ann}_Z(v)$ by linear algebra. The cyclic submodule $Zv$ is $Z/K$. Since $Z$ is a product of fields, the support idempotent of $Z/K$ is the projection of $1$ to $\operatorname{ann}_Z K$ in $Z=K\oplus\operatorname{ann}_Z K$. Record this idempotent, quotient out $Zv$, and repeat. The dimension of a component of $Q$ over its corresponding field $E_j$ equals the number of recorded idempotents supported there. Refine the partition of $1_Z$ by simultaneously distinguishing every recorded idempotent from its complement, using multiplication in $Z$ and discarding zero parts. There are at most $\dim_F Z$ nonzero parts at any stage. On every part the three dimensions over the corresponding $E_j$ are constant and are respectively
$$
u_j^2,\qquad u_j a_{F^n,j},\qquad u_j a_{F^m,j}.
$$
Their integer square roots and quotients recover the desired columns. Repeated columns give the same subgroup.

Given an exponent matrix $C$ with two rows, its image on a product of copies of $F^\times$ is tested by integer Hermite and Smith normal forms. In detail, put $N=q-1$, adjoin the columns of $NI_2$ to $C$, and take a basis of the resulting full-rank column lattice. The extra columns evaluate to $1$ over $F^\times$. This lattice basis generates exactly the same multiplicative subgroup as the enlarged matrix, because both generating sets are integral linear combinations of one another. Smith normal form of the basis gives unimodular row and column transforms and diagonal entries $d_1,d_2$. Apply the row transform to the target pair as a monomial automorphism. Then the transformed coordinate $w_i$ is in the $d_i$-power image precisely when $w_i^{N/\gcd(N,d_i)}=1$. This uses cyclicity of the group, with no need to find a generator. All coefficient bit lengths and running times are polynomial. Divide the prescribed pair by $(\det g_0,\det h_0)$ before this test. The same test permits adding columns representing further independent monomial parameters. [Kannan and Bachem](https://epubs.siam.org/doi/10.1137/0208040)

## Arithmetic with several field components at once

We use finite étale $F$-algebras with explicit multiplication tables. For an element $z$ in such an algebra $R$, the kernel and image of multiplication by $z$ are complementary ideals. Projecting $1$ to these ideals computes the idempotents for the zero and nonzero parts of $z$. A scalar zero test in a field algorithm can therefore split the computation at the test. A scalar inverse on a nonzero part is computed by a linear system. Each field component follows its own field computation, and a polynomial bound on the field algorithm's path lengths gives a polynomial bound on the total work after multiplication by $\dim_F R$. Each nonempty branch has at least one field component. Separate case checks refer to this operation. A computation over an algebra known to be split runs only over copies of the original field.

The Frobenius-fixed algebra $R^{[q]}=\{z\in R:z^q=z\}$ is the kernel of an $F$-linear map. It is split over $F$, with one copy of $F$ for each field component of $R$. It can be computed by repeated squaring and linear algebra.

## Rank-drop directions

Put $M=\min(m,n)$. For $q\le 2M$ simply enumerate all $2$ by $2$ matrices over $F$, retain those of determinant $c$, and apply the ordered test. The explicit polynomial-basis encoding permits enumerating all field elements in time polynomial in $q$ and $\log q$. Assume henceforth that $q>2M$. The same encoding supplies the first $2M+1$ distinct elements in time polynomial in $M$ and $\log q$.

For each pencil, find its generic rank $k$ by testing $M+1$ distinct affine directions $(z,1)$. Some nonzero maximal minor has degree at most $M$, so one of these ranks attains $k$. A nonzero $k$-minor at such a sample point is interpolated as a polynomial in $z$. Use the resulting minor for each pencil to find a common affine non-drop direction among $2M+1$ samples. A common reparametrization sends this direction to infinity and conjugates the unknown label map, preserving its determinant. Recompute a nonzero maximal minor in the new chart. For generic rank zero use the constant minor $1$.

To remove multiplicities from a minor polynomial $d$, if $d'\neq 0$, take the least common multiple of $d/\gcd(d,d')$ and the recursively computed squarefree part of $\gcd(d,d')$. If $d'=0$ for a nonconstant polynomial, take its $p$th root by inverse Frobenius and recurse. The recursion stops at a constant, with squarefree part $1$. These steps recover the radical of the polynomial even when a multiplicity is divisible by the characteristic. Over the finite étale algebra defined by the resulting squarefree polynomial, evaluate $A(z,1)$ and compute rank with field-component splits. Retain exactly the parts where rank is less than $k$. Their algebra has an element $z$ whose multiplication characteristic polynomial is the product of the distinct irreducible polynomials of the retained directions. In a retained component this follows because its powers form a basis and its minimal polynomial has the full dimension. The empty algebra gives polynomial $1$. This constructs the reduced rank-drop polynomials $P_A,P_B$ in polynomial bit time.

A genuine label equivalence carries geometric rank-drop directions bijectively and preserves generic rank. Reject different generic ranks or reduced drop degrees. Infinity is a non-drop direction for both pencils.

## At least three geometric drop directions

Use the finite étale algebra generated by six coordinates $a_1,a_2,a_3,b_1,b_2,b_3$, each of the first three satisfying $P_A$ and each of the last three satisfying $P_B$. Its dimension is at most $M^6$. Retain the components where the coordinates within each triple are distinct. The unique projective transformation taking one triple to the other is represented there by $G_b^{-1}G_a$, where $G_a$ represents
$$
z\longmapsto \frac{(z-a_1)(a_2-a_3)}{(z-a_3)(a_2-a_1)}
$$
and $G_b$ uses the $b_i$. Normalize this matrix $U$ by its first nonzero entry and retain precisely the components where all four normalized entries satisfy $u^q=u$. The normalized entries belong to the split algebra obtained by taking Frobenius fixed points. This is precisely the rationality test for the projective matrix.

The lifts of a retained matrix with determinant $c$ are $\lambda U$ with $\lambda^2=c/\det U$. If the characteristic is odd, keep components where $v=c/\det U$ satisfies $v^{(q-1)/2}=1$ and adjoin a root of $X^2-v$. The resulting algebra is split because this polynomial has two distinct rational roots on each retained component. In characteristic two use the unique scalar $v^{q/2}$. Apply the ordered determinant test over the split algebra. Every actual label map occurs because it maps any chosen distinct triple of source drop directions to a distinct target triple and has the prescribed determinant. Every accepted candidate is a rational label map and passes the literal ordered equivalence test, proving soundness.

## At most two geometric drop directions

We use the classical Kronecker canonical form of a pencil under strict equivalence over its base field. Its discrete data consist of the two lists of minimal indices and the homogeneous regular primary elementary divisors. We give polynomial-time extraction of precisely the data needed here. [Van Dooren](https://perso.uclouvain.be/paul.vandooren/publications/VDooren79.pdf), [Sergeichuk](https://arxiv.org/abs/0709.2470)

For the right minimal indices, compute the dimension of polynomial solutions to $A(z,1)v(z)=0$ with $\deg v\le a$ by coefficient linear algebra. A right singular block of index $d$ contributes $\max(0,a-d+1)$ to this dimension, because its polynomial kernel is generated by a primitive vector of degree $d$. It has the monomial-coordinate shape $1,z,\ldots,z^d$ up to signs and ordering. A regular or left singular block has zero polynomial kernel. Second differences recover multiplicities of all right indices, including zero, using $a=0,\ldots,n+m$ and dimension zero at negative $a$. Transpose for the left indices.

Let $\theta$ be a drop direction in its field of degree at most two. Compute the nullity of $A(\theta+\epsilon,1)$ as a linear operator over that field, with entries acting on the truncated polynomial ring modulo $\epsilon^a$. The resulting integer minus $a(n-k)$ is
$$
\sum_\ell \min(a,\ell)
$$
over regular block lengths at $\theta$. Indeed, right singular blocks have a maximal minor which is a unit at $\theta$ and contribute exactly $a$ each. Left singular blocks and blocks for other directions have zero kernel. For a regular block of length $\ell$ at $\theta$ the determinant has order $\ell$ and an $(\ell-1)$-minor is a unit. Unit elimination reduces it to identity entries and a final scalar of order $\ell$, giving the stated nullity. Differences for $a=1,\ldots,n+m+1$ recover the lengths and their multiplicities. The polynomial systems here are bounded in dimensions polynomial in $m+n$ and include the zero pencil. For no drop directions there are no regular blocks, since a nonconstant homogeneous determinant in two variables has a projective root over an algebraic closure.

Compare minimal-index lists and compare regular lengths at matched drop directions throughout the cases below. These are necessary for a label equivalence: an invertible linear change of homogeneous variables preserves regular primary block lengths at the carried directions, and the singular block covariance proved below preserves both minimal-index lists. They are sufficient for constructing the displayed strict-equivalence models and using the stated label maps. Reject any failed comparison.

Write $L_d(x)$ for multiplication by $x_1X+x_2Y$ from the degree $d-1$ homogeneous binary polynomials to those of degree $d$ for $d\ge 1$. Use $L_d$, its transpose, and the corresponding one-sided zero blocks for the source and target singular models, with an identical block ordering. Use the actual coordinates $x$ in these models for singular blocks. The covariance for any $f$ is
$$
L_d(fx)\operatorname{Sym}^{d-1}(f)=\operatorname{Sym}^{d}(f)L_d(x).
$$
Here $f$ acts on the two-dimensional space of linear forms using the column convention for the coefficients of $x_1X+x_2Y$. For transposes the reference transports are the inverse transposes with the two spaces exchanged. Index zero uses identities. The elementary identity
$$
\det\operatorname{Sym}^{d}(f)=(\det f)^{d(d+1)/2}
$$
follows by triangularizing over an algebraic closure and multiplying the diagonal monomials. Thus the product of the two singular reference determinants depends only on $c$. Denote these fixed mode factors by $(s_{\rm sing},t_{\rm sing})$.

For each model below the actual pencil has the asserted strict-equivalence model by the canonical form and the extracted data. For the source compute an ordered isomorphism with $A_{\rm mod}(x)g_A=h_AA(x)$ and likewise with $g_B,h_B$ for the target. If the original prescribed pair is $(s,t)$, the model pair to test is
$$
(s_{\rm mod},t_{\rm mod})=
\big(s\det(g_B)/\det(g_A), t\det(h_B)/\det(h_A)\big).
$$
Compute the ordered stabilizer image of the source model by the ordered algorithm. For every fixed $f$ under consideration a reference model transporter exists, and all other ones differ on the right by the source ordered stabilizer. It suffices to compute the union of those determinant cosets over the allowed label maps.

### No drop direction

The models consist entirely of the displayed singular blocks. Every $f$ with determinant $c$ has the given reference determinant pair $(s_{\rm sing},t_{\rm sing})$, and such an $f$ exists, for instance $\operatorname{diag}(c,1)$. Test membership of the model determinant pair divided by this reference pair in the ordered image.

### One rational drop direction or two rational drop directions

For a direction $\theta$ put $v(\theta)=(\theta,1)^{\mathsf T}$. Choose frames $Q_A,Q_B$ whose first columns represent the matched directions and whose second columns represent the second matched directions if present. In the one-direction case use the common infinity vector $(1,0)^{\mathsf T}$ as the second column. In the two-direction case both root matchings can be considered in the split algebra $F[z,w]/(P_A(z),P_B(w))$. The other roots follow by subtraction from the negative linear coefficients. This avoids extracting roots even when $q$ varies. Use $x'=Q_A^{-1}x$ for the regular source model, $Q_B^{-1}x$ for the target, and the same block ordering after matching. A block of length $\ell$ at the first root has matrix $x'_2I+x'_1N_\ell$ and a block at the second root has matrix $x'_1I+x'_2N_\ell$, where $N_\ell v_j=v_{j+1}$ for the consecutive basis vectors and kills the last.

Any label map carrying the matched directions has form $f=Q_B\widetilde f Q_A^{-1}$ with $\widetilde f=\begin{pmatrix}a&b\\0&d\end{pmatrix}$ and $ad=\delta=c\det(Q_A)/\det(Q_B)$. If there are two roots, $b=0$. Conversely every such choice has the required root correspondence and determinant.

For a first-root block, set $T=a(dI+bN_\ell)^{-1}N_\ell$. Define the reference domain map by $g v_j=T^jv_0$ for $0\le j<\ell$, and the codomain map by $h=(dI+bN_\ell)g$. Indeed $Tg=gN_\ell$, and therefore
$$
\big(x'_2(dI+bN_\ell)+x'_1aN_\ell\big)g
=h(x'_2I+x'_1N_\ell).
$$
The triangular domain map has diagonal entries $(a/d)^j$. Thus its determinant is $(a/d)^{\tau_\ell}$ with $\tau_\ell=\ell(\ell-1)/2$, and the codomain determinant adds a factor $d^\ell$. For a second-root block interchange the two coordinates and $a,d$, giving $(d/a)^{\tau_\ell}$ and an extra $a^\ell$. Substituting $a=\delta/d$ makes the complete reference pair equal to a fixed pair times a pair of integer powers of $d$. All $d\in F^\times$ occur, and the determinant never depends on $b$. Use the single exponent column for $d$ together with the ordered stabilizer columns, after dividing the model target pair by the fixed reference pair. The two-direction root matching passes if either enumeration component passes.

### A conjugate quadratic pair of drop directions

If exactly one drop polynomial splits, reject. When both are irreducible quadratic, form
$$
T=F[z,w]/(P_A(z),P_B(w)),\qquad R=T^{[q]}.
$$
Here $T$ has two quadratic field components and $R$ is split with two factors. Each component of $T$ realizes a matching of a source root $\theta=z$ and target root $\eta=w$ in a common quadratic extension $E$ of $F$, with the other roots their Frobenius conjugates. Each of the two Frobenius-compatible matchings is represented. In a component let $Q_A$ have columns $v(\theta),v(\overline{\theta})$, and $Q_B$ have columns $v(\eta),v(\overline{\eta})$. Conjugation swaps both pairs, so $\delta=c\det Q_A/\det Q_B$ belongs to $F^\times$. The rational maps which carry the ordered pairs have exactly the form
$$
f=Q_B\operatorname{diag}(a,\overline a)Q_A^{-1},\qquad N_{E/F}(a)=\delta.
$$
Indeed diagonal form follows from the ordered correspondence and Frobenius compatibility gives the displayed relation between diagonal entries. Conversely this form is Frobenius-fixed and has the required determinant. Norm surjectivity guarantees existence for every $\delta$.

Use the first-root regular model $x'_2I+x'_1N_\ell$ on $E^\ell$, restricted to $F$ and with basis $1,\theta$ on the copies of $E$ for both models in the component. On extending scalars to $E$, it splits as the block and its conjugate, with the latter at the other root. The singular model and the prescribed determinant calibration remain over $F$. Over the split base algebra $R$ the auxiliary algebra $T$ is free with basis $1,z$, so regular model arithmetic can be performed without choosing quadratic roots in the base field. In particular the ordered determinant algorithm for the calibrated models uses the original field, one copy per split component.

The first-root transport with $b=0,d=\overline a$ is $E$-linear. Its domain determinant over $F$ is $N_{E/F}((a/\overline a)^{\tau_\ell})=1$. Its codomain determinant over $F$ adds $\delta^\ell$. Thus for each component the full reference determinant pair is constant as $a$ varies subject to the norm condition. Divide by that reference pair and test the ordered stabilizer image over the split algebra $R$. No norm preimage needs to be computed.

## Complexity and scope

All matrices and coefficient systems have dimensions bounded by polynomials in the explicit input dimensions. The largest simultaneous root algebra has dimension at most $M^6$. A branch split occurs only when its corresponding field computation would branch and keeps the total number of components polynomial. The rank-drop extraction, truncated-ring nullities, algebra arithmetic, matrix products and Smith operations all have polynomial bit complexity. Exponentiation to $q$, $q/2$, and the power-image test exponents takes polynomial time in $\log q$. Witness construction, deterministic finite-field factoring, and any Riemann hypothesis are unnecessary for this decision theorem.

The proof gives the full decision equivalence for the two-dimensional family and prescribed determinants. The unrestricted reverse reduction with all three dimensions varying remains open here. The paper proof uses the cited algorithmic and classification results and has no Lean certificate. [Chen–Grochow–Qiao–Tang–Zhang, Open Question 1.9](https://arxiv.org/html/2306.03135v2#S1.SS5)
