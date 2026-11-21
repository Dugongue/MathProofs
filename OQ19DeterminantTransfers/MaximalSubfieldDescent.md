# Determinant tests from maximal subfields of pair adjoints

Fix a finite field $F=\mathbb F_q$ and a constant $c>0$. Let $T:V_1\times V_2\times V_3\to F$ be a concise trilinear form given by a dense array of bit length $B\ge2$. Conciseness means that the radical of $T$ in each individual mode is zero. Use the pair adjoint algebra
$$
A=\{(a,b):T(ax,y,z)=T(x,by,z)\ \text{for all }x,y,z\},
$$
with product $(a,b)(a',b')=(aa',b'b)$. Write its semisimple quotient as $\prod_j M_{d_j}(E_j)$ and choose a Wedderburn–Malcev complement $S$ in $A$. Let $e_j=[E_j:F]$. On the two modules for a simple factor of $S$, let $r_{1j},r_{2j}$ be the multiplicities of its natural simple module and its dual, respectively. Order the factors lexicographically by the tuples $(e_j,d_j,r_{1j},r_{2j})$. Require those tuples to be pairwise distinct. In the pair comparison, mismatched descriptor lists or corresponding grade dimensions give a fixed negative instance.

For an ordered factor $j$, let $W_j\subseteq V_3^*$ be the span of the contractions $T(x,y,-)$ with $x,y$ in the corresponding blocks of modes one and two. Write $W_{\le j}=\sum_{i\le j}W_i$, with $W_{<j}$ defined accordingly. The hypothesis on each nonzero grade $G_j=W_{\le j}/W_{<j}$ is one of the following.

- Its $F$-dimension is at most $c\log_2 B$.
- The linear map from the tensor product over $E_j$ of the two multiplicity spaces onto $G_j$, defined below, has $E_j$-stable kernel. The resulting $E_j$-dimension of $G_j$ is at most $c\log_2 B$.

Require, for $i\in\{1,2\}$, that $r_{ij}\le c\log_2 B$ whenever $q-1$ does not divide $d_j$. No bound on $r_{ij}$ is needed if $q-1\mid d_j$.

**Theorem.** This is a deterministically recognizable class over each fixed $F$. Given two based tensors in the class and three prescribed values of their transporter determinants in $F^\times$, a deterministic polynomial-time construction produces one ordinary three-tensor isomorphism instance over $F$ with the same verdict. The conclusion permits arbitrary radical, arbitrary simple matrix degrees and center extension degrees, and arbitrary total dimension in mode three. Over $\mathbb F_3$ the residual rank bound is absent on every even-degree matrix factor.

## Algebra and module frames

Solve the displayed equations by linear algebra. The two projections of $A$ are injective by conciseness. Direct substitution verifies closure under its stated multiplication. An isomorphism $g=(g_1,g_2,g_3)$ of the original tensors induces an isomorphism of adjoint algebras by conjugation in the two projections. Conversely, each unit $(a,b)$ of a target adjoint algebra gives an actual target automorphism $(a,b^{-1},1)$ by the balancing equation.

Compute the radical $J$ and an explicit quotient into full matrix algebras. For this use the fixed-characteristic version of the finite-field algebra algorithm in Theorem 19 of the cited source. Its time is polynomial in the matrix dimension, $\log q$, and $\operatorname{char}F$. Compute a unital section $A/J\to A$ by successively lifting an algebra section from $A/J^m$ to $A/J^{2m}$. Start with $m=1$. Choose a unital linear lift $s$ of the previous section. Its multiplication error lies in $J^m/J^{2m}$, an ideal with zero square. Adding a linear correction $u$ into this ideal changes the error by $s(a)u(b)+u(a)s(b)-u(ab)$. The correction equations and $u(1)=0$ are linear. They have a solution by the Wedderburn–Malcev theorem. Specifically an algebra section in the larger quotient exists because the quotient is separable over $F$. Its image in the smaller quotient is conjugate to the old image by a unit congruent to one modulo the radical. Lift this unit and conjugate the larger section. Both sections induce the identity on $A/J$, so equality of images in the smaller quotient gives equality of sections. Doubling $m$ until $J^m=0$ gives the claimed complement in polynomial time. [Ivanyos–Qiao, *Algorithms based on \(*\)-algebras*, Theorem 19](https://opus.lib.uts.edu.au/bitstream/10453/130877/1/main_arxiv_v2.pdf#page=18)

Every original transporter can be made to carry the chosen source complement to the chosen target complement by a target adjoint operation from $1+J'$. The two components of an element of $J'$ act nilpotently on the indicated raw modes. Thus this operation has determinant one in each mode and is the identity in mode three. In particular the block descriptors and the ordered spaces $W_j$ do not depend on the complement choice, when blocks are indexed by their simple quotient factors. Passing between complements induces a graded identification through actual tensor automorphisms.

For one factor fix a common model $M_d(E)$ for both tensors. Use matrix units to write the two blocks as
$$
V_{1j}=P\otimes_E R_1,\qquad
V_{2j}=P^\vee\otimes_E R_2,\qquad
P=E^d,\quad P^\vee=\operatorname{Hom}_E(P,E).
\tag{1}
$$
The first projection acts on $P$ by the indicated matrix and the opposite projection on $P^\vee$ by precomposition with it. The multiplicity spaces are the images of the first diagonal matrix unit. For instance the first-column units send each vector in that image to its corresponding coordinates in mode one. The transpose operation in the second mode uses the corresponding first-row units. A basis of each image over $E$ is obtained by successively increasing its $E$-span, using $F$-linear algebra. The images of a basis in the different coordinates are linearly independent by applying the returning matrix units. This gives the actual frames in (1).

Different factor labels in the first two modes have zero cross-contractions, by applying the balancing equation to a central idempotent. On the same block, the equation for diagonal matrix units kills off-diagonal contractions between $P$ and $P^\vee$. The equations for the remaining units identify the contractions on all diagonal coordinates. Scalar matrix equations then balance the two $E$-multiplicity spaces. Consequently there is an explicit $F$-linear map
$$
\psi_j:R_1\otimes_E R_2\longrightarrow V_3^*
\quad\text{with}\quad
T(p\otimes x,f\otimes y,-)=\psi_j\big(f(p)x\otimes y\big).
\tag{2}
$$
It is computed by evaluating on the first coordinate and its dual. Its image is $W_j$. In particular $\dim_F W_j\le e_jr_{1j}r_{2j}$. Quotienting by $W_{<j}$ gives the map onto $G_j$ used in the theorem. Test whether its kernel is $E_j$-stable by multiplying a basis by a field basis. This test and the dimension bounds use only linear algebra. An original isomorphism carries the ordered flag to the corresponding flag, even if its adjoint action first needs the complement correction, since that correction fixes mode three.

## Normalize a transporter on a maximal subfield

Keep the original tensor and the indicated blocks as records. The simple algebra, its center and their multiplication and inclusions are additional named roles. In $M_d(E)=\operatorname{End}_E(P)$ attach the field $L/E$ of degree $d$ by its regular multiplication action on $P=L$. Use an $E$-basis to identify $P$ with this same extension model on the two sides. The chosen embedding varies with the model frames and the proof below works for those arbitrary choices. Retain the evaluation $P^\vee\times P\to E$, the $E$-module maps on the two multiplicity roles, and the bilinear maps in (1) with value in the actual raw blocks. The representation of the matrix role on $P$ and its two representations on the raw blocks are also bilinear records. All this data is finite vector spaces and multiplication tables over $F$. Use a common field model for each matched degree, with its appropriate subfield and inclusions. [Shoup, deterministic irreducible-polynomial construction for fixed characteristic](https://www.shoup.net/papers/detirred.pdf) · [Lenstra, explicit finite-field isomorphisms](https://pub.math.leidenuniv.nl/~lenstrahw/PUBLICATIONS/1991b/art.pdf)

Here is why the extra field attachment preserves the possible determinant triples. After aligning complements, the action of an actual transporter on one $M_d(E)$ is $\operatorname{Ad}(M)\sigma$, where $\sigma$ is its automorphism of $E$ and acts entrywise, and $M\in\operatorname{GL}_d(E)$. To see that the remaining $E$-linear automorphism is inner, use the images of the matrix units to build a new basis of the natural module from one nonzero vector in the first diagonal image. In these coordinates an implementing semilinear map on $P$ is $M\sigma$.

Extend $\sigma$ to an $F$-automorphism $\tau$ of $L$. Such an extension exists because both automorphism groups are generated by the $q$-Frobenius. In the chosen coordinates write $\tau=M_\tau\sigma$ and let $m_\lambda$ denote multiplication by $\lambda$ on $L$. Choose $\lambda\in L^\times$ with
$$
N_{L/E}(\lambda)=\det_E(M)/\det_E(M_\tau).
$$
The finite-field norm is onto by cyclicity of the multiplicative groups. Then
$$
Q=m_\lambda M_\tau M^{-1}\in\operatorname{SL}_d(E).
$$
Compose the actual transporter with the target adjoint operation $(Q,Q^{-\mathsf T},1)$ on this factor, in the frames (1). The ambient determinants of the operation are one, since they are norms of $\det_E Q$ and its inverse to the respective multiplicities. Its new simple-module map is $m_\lambda\tau$, which transports the prescribed regular subfields. For differently chosen embeddings the same calculation uses the coordinates determined by each of their regular modules. The norm choice ensures determinant neutrality in those coordinates, hence in the target raw coordinates. The corrections on separate factors commute. These choices show that an existing witness can be normalized. The algorithm constructs the records without finding a transporter or solving a norm equation for an unknown transporter.

Once the simple-module map $u=m_\lambda\tau$ is selected, the raw maps in the two blocks are $u\otimes h_1$ and $u^\vee\otimes h_2$, with $h_i$ semilinear for $\sigma=\tau|_E$ and $u^\vee(f)=\sigma\circ f\circ u^{-1}$. This follows by removing the indicated simple-module actions, after which the maps commute with all matrix units and are determined by the map on the first diagonal image. Conversely the attached evaluation, algebra actions and bilinear maps (1) force exactly these identities on their raw projections. In particular no independent choice of Frobenius is permitted on a linked center or multiplicity space. For (2) the simple-module parts cancel: take a pair $p,f$ with $f(p)=1$, whose transformed evaluation remains one. Thus $h_1\otimes h_2$ induces the dual inverse of $g_3$ on the image and quotient of (2). An $E$-stable grade therefore has a semilinear action for this same $\sigma$. Mark its field-module action to record that link.

## Read determinants using scalar lines

A transporter of the new records has $u=\lambda\tau$ on the regular field module, since its value at one and its action on the field determine its values everywhere. Its $F$-determinant is
$$
D=N_{L/F}(\lambda)\det_F\tau.
$$
For an extension field $K/F$ and a scalar semilinear action $x\mapsto a\eta(x)$, its norm factor can be read in general by the following linear and bilinear records. Make copies linked by the fixed $F$-linear Frobenius powers, one for each $q$-conjugate. They carry scalars $a^{q^s}$ with the same $\eta$. Chain the field multiplication maps to multiply these scalars, and take the $F\cdot1$ line in the last module. Surjectivity of multiplication forces the output action in each step. Thus the line map has multiplier $N_{K/F}(a)$. In a normal basis the $q$-Frobenius is a cycle of length $[K:F]$. Its determinant is one in even characteristic or odd degree. In odd characteristic and even degree, its determinant sign is read on the trace-zero line of the unique quadratic subfield, where the $q$-Frobenius acts by $-1$. The subfield and line are kernels of linear maps in the given field model.

For the second leg, $\operatorname{Tr}_{E/F} f(p)$ is a perfect $F$-pairing and the semilinear dual map preserves it with $u$ since $\operatorname{Tr}_{E/F}\circ\sigma=\operatorname{Tr}_{E/F}$. Thus $\det_F u^\vee=D^{-1}$ in the common model frames. Write $h_i=H_i\sigma$ in fixed $E$-bases. The two block determinants over $F$ are exactly
$$
D^{r_1}N_{E/F}(\det_E H_1)^d,\qquad
D^{-r_2}N_{E/F}(\det_E H_2)^d .
\tag{3}
$$
Indeed the $E$-linear determinant on a tensor product is the product of the factor determinants raised to the other dimensions. The coordinatewise Frobenius on a block of $E$-dimension $dr_i$ contributes $(\det_F\sigma)^{dr_i}$, already included in the indicated power of $D$ or $D^{-1}$. Here $\det_F\sigma=\pm1$ and its inverse equals itself. This accounts for the Frobenius orientation without introducing an extra sign on the second leg.

If $q-1\mid d$, the residual norm power in (3) is one. Otherwise the multiplicity bound permits recording the $E$-exterior powers of $R_i$ and their wedge maps, with total dimension $e_j2^{r_i}$ over $F$. The top line carries the scalar semilinear action $(\det_E H_i)\sigma$ in the given top basis. The norm records above read its norm factor. No separate Frobenius sign from $h_i$ is included in (3). Negative scalar exponents are recorded by dual lines, and products and positive integer powers by one-dimensional bilinear maps.

Tie the third dual role to the original third mode by its evaluation pairing, so its map is the inverse transpose of the actual third-mode map. On that role use the inclusions and quotient maps of the flag. Each grade whose $F$-dimension bound passes uses its ordinary exterior top line. For the other grades record the induced $E$-module action from (2), the smaller exterior algebra over $E$, and the norm and Frobenius sign lines. These force the determinant over $F$ of the actual grade transporter. Their product gives the determinant of the third dual-mode transporter in chosen adapted frames. Conciseness makes the last flag space all of $V_3^*$.

Collect the block determinants (3) in factor order so their product reads the first two determinants in their assembled frames. On the third mode take the reciprocal of the dual determinant. Frame calibration consists of multiplying the readout by the ratio of target to source frame determinants from the written bases, using the inverse ratio for the third dual readout. It can instead be applied to the prescribed multiplier before marking it. Fix a trivial scalar role by its own multiplication and use marked vectors to prescribe the three calibrated line multipliers on the same transporter. All computations depend on the two arrays and the stated prescribed values.

## One ordinary comparison

The above construction uses polynomially many vector spaces and linear and bilinear map records over $F$. Field dimensions and matrix algebra dimensions are bounded by polynomial functions of the input because the respective representations are explicit. The only exterior constructions on multiplicities or grades use ranks at most $c\log_2 B$. Scalar powers can be chained in polynomial length. The normalization proof gives an extension of some actual witness for every attainable determinant triple. Conversely, every isomorphism of the extended records projects to a transporter with exactly the specified triple.

To compile a polynomial list of records, put the original named roles in an ordered direct sum and create a second direct sum with separate copies for every map-slot occurrence. Label these summands by a coordinate algebra $F^s$ with one primitive idempotent per name, and attach its module with distinct dimensions $1,\ldots,s$ on the corresponding primitive idempotents. This forces the idempotents to be fixed. The coordinate algebra action preserves each indicated summand. A linear incidence map from the occurrence sum to the role sum is the identity on each copy into its role and forces the two maps there to agree. Store the original records on their occurrence blocks as tensors with the appropriate primal and dual slots. Pad records of lower order with the fixed scalar role. This gives a constant number of arrays with order at most three, one for each slot variance, and polynomial dense size. Their simultaneous comparison reduces to one ordinary three-tensor isomorphism instance by the tensor-system reduction. The multiplication and module records are included as additional constant-size signature types in this packing. There is no search or multiple-query step. [Chen–Grochow–Qiao–Tang–Zhang, tensor systems and Theorem 4.1](https://arxiv.org/html/2306.03135v2#S4)

The same conclusion applies if a nonconcise input is first quotiented by its mode radicals and the concise tensors meet the stated criteria for the retained determinant tests. On a mode with nonzero radical, a quotient transporter extends with any prescribed nonzero determinant by an appropriate radical isomorphism. On a full mode the original determinant is still imposed. A dimension mismatch in corresponding radicals or quotient formats yields a fixed negative instance. If both tensors vanish, all multipliers on positive-dimensional modes are attainable, and the determinant on a zero-dimensional mode is one.

## A family with nonzero radical and unbounded multiplicities

Take $F=\mathbb F_3$, any finite extension $E/F$, and $R=E[\epsilon]/(\epsilon^h)$ for any $h\ge2$. Use $V_3=(E^2)^m$ and the $2m-1$ maps $\phi_j:V_3\to E^2$ given by the coordinate projections $z_j$ and the sums $z_1+z_j$ for $j\ge2$. Write $\phi_j(z)=(a_j,b_j)$. These maps are pairwise independently surjective to two copies of $E^2$. Use one pair of $R^{d_j}$ blocks for each $\phi_j$, with distinct positive even $d_j$, and define
$$
T(x,y,z)=
\sum_j \operatorname{Tr}_{E/F}\left([\epsilon^{h-1}]
  (a_j+b_j\epsilon)\sum_{\ell=1}^{d_j}x_{j,\ell}y_{j,\ell}\right).
\tag{4}
$$
The trace of the top coefficient of the dot product is a perfect pairing over $F$ since the monomial basis of $R$ pairs complementary exponents. The two possible coefficients $1,\epsilon$ are independent and the $\phi_j$ include all projections. Thus (4) is concise in all modes.

Its pair adjoint is precisely $\prod_j M_{d_j}(R)$. For an off-diagonal block from one label to another, fixing the two raw inputs on those labels gives an equality of functionals in the two independently varying $\phi$ values. Set one value to zero and use the other value $(1,0)$ and the perfect pairing to show that the off-diagonal map vanishes. On a diagonal block, the form with coefficient one forces the two adjoint maps to be trace-dual. Varying the coefficient over $E$ and then using $\epsilon$ forces the first map to commute with scalar $E$ and with multiplication by $\epsilon$. This is exactly $R$-linearity, and every $R$-linear map has the required mate. The quotient is the product of $M_{d_j}(E)$, with multiplicities $h$. Each $\phi_j$ contributes a span supported by no more than two $E$ coordinates in its image space $W_j$. More precisely it is the image of the $E$-dual of $E^2$ under the dual of $\phi_j$, under the trace identification of $F$-duals with $E$-duals. Equation (2) is $E$-linear in those same coordinates, so the flag grades have $E$-stable kernels and rank at most two. This meets the logarithmic bounds for sufficiently large written inputs with no bound on $h,e_j,d_j$.

This family has genuine special-linear constraints. A raw slice of (4) is nonsingular exactly when every $a_j\ne0$. Such slices exist by taking each projected first coordinate equal to one. Every nonsingular slice has the same determinant in a fixed pair of mode bases. The determinant multiplier from each block is $N_{E/F}(a_j)^{h d_j}=1$. Tensor automorphisms permute nonsingular slices, so comparing their determinants proves $\det g_1\det g_2=1$ for every automorphism. Apply any determinant-$-1$ change of first-mode coordinates to (4). This gives an ordinarily isomorphic tensor in the class, with $\det g_1\det g_2=-1$ for every transporter from the original tensor. The pair is special-linearly inequivalent.

## Relation to previous work and scope

The determinant on a regular field module uses the same norm and trace-zero Frobenius lines as the prior centroid-block construction. The new step is the determinant-neutral normalization of arbitrary matrix factors into maximal subfields via actual pair-adjoint units. Complement conjugacy permits nonsemisimple adjoints. The third support flag and the divisibility condition remove large external algebras from the determinant test on the stated modes. This supplies a sufficient class for [Open Question 1.9](https://arxiv.org/html/2306.03135v2#S1.SS5). In the unrestricted ternary square-zero normal form the label determinant can still act on a grade of unbounded rank when there is no relevant adjoint block decomposition. The argument is a written proof and does not establish the unrestricted containment.
