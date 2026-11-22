# Linear Polynomial Calculus degree for thin associative multiplication

**Theorem.** Let $k$ be any field. Let $T,S$ be same-format three-tensors, nonisomorphic over $\overline k$, and suppose the first tensor becomes the multiplication tensor of a finite-dimensional unital associative algebra $A$, up to an ordinary tensor isomorphism and zero padding. Suppose over $\overline k$ that $A/J\simeq\overline k^m$, with $J$ its Jacobson radical, and that for a complete set of orthogonal lifts $e_1,\ldots,e_m$ of the primitive quotient idempotents one has
$$
\dim_{\overline k}e_iAe_j\le 1\qquad(1\le i,j\le m).
$$
There is an ordinary Polynomial Calculus refutation of the literal cubic action and two-sided inverse equations in degree $O(1+b)$ if both tensors have geometric border rank at most $b$. The same bound applies with ordinary rank in place of border rank. The target can be arbitrary. No field equations are used. Worst-case linear degree is attained in every fixed characteristic, including characteristic zero. Examples include incidence algebras of arbitrary finite posets and the radical-square-zero algebras of directed simple graphs without loops. [Galesi–Grochow–Pitassi–She, Questions 7.1 and 7.4](https://arxiv.org/abs/2305.19320)

## 1. Elementary proof operations

We work over $\overline k$ and then descend. A finite proof uses coefficients in a finite extension of $k$, and one can replace each line by its coefficient coordinates over a $k$-basis of that extension containing $1$. Linearity and multiplication by a variable act coordinatewise, and the coordinate of the final $1$ equals $1$. The resulting proof has the same degree. Thus geometric normal forms and fixed choices over $\overline k$ are valid. Constant changes of input and target basis correspond to linear changes in the witness variables and preserve degree by expanding a multiplication by a linear form.

First compress supports. Each flattening rank is at most $b$ since the $(b+1)$-minors vanish on the rank-$b$ locus and its closure. In adapted bases, multiply the action equation by the two inverse matrices from the other two modes. The outside-support rows vanish, and taking a right inverse of the constant supported flattening gives linear equations that the forward map sends source support into target support. The reverse action and the same calculation give the reverse support inclusions. The supported parts consequently satisfy both rectangular inverse identities in constant degree, and their tensor action equations come directly from the supported entries. If dimensions differ, taking a determinant of the larger rectangular product yields a contradiction in degree $O(b+1)$. This determinant step uses Cauchy–Binet and the column-telescoping formula for a difference of determinants. For a zero source against a nonzero target the action already contains a nonzero constant after basis adaptation. From now on assume the trimmed source and target have the same support dimensions. Unital multiplication on an algebra of dimension $d>0$ has support dimension $d$ in all three modes, because multiplication by the unit is the identity. Thus both tensors have format $d^3$ and $d\le b$.

We use two precise PC rules throughout. If a fixed linear system is satisfied by a vector of polynomials, projection to its kernel changes each coordinate by a constant linear combination of the residuals. This lets us express the vector in a fixed kernel basis at the same degree. If a system has previously derived polynomial lines of degree at most $D$, a proof in such lines may use them as axioms while preserving the greater of that degree and its own degree. In particular, repeatedly concluding the vanishing of a fixed projection of a bounded-degree polynomial vector keeps the proof degree bounded.

Substituting polynomials of degree at most $c$ for proof variables multiplies proof degree by at most $c$ up to the degree required to derive the substituted axioms. Indeed a multiplication by a polynomial expands into monomial multiplications and linear combinations, each with degree bounded by $c$ times the original multiplication-step degree.

## 2. Recover a unital algebra comparison on the literal system

Write the source as $A$ with product $xy$, and write the target initially as a bilinear map $S$. Let $P,Q,R$ be the forward transporters with named inverses. The action is
$$
S(Px,Qy)=R(xy)
$$
in the bilinear convention. The literal tensor equations in the covariant convention imply this equality with constant degree by multiplying by the appropriate two maps and using their inverse equations. The reverse equality has constant-degree derivations as well.

If the target has no invertible left slice, its left-slice determinant vanishes identically. In the action put $x=1_A$, giving $L_{P1_A}Q=R$ where $L_a$ denotes the target left slice. The determinant of $L_{P1_A}$ is then identically zero, yet $R$ has a named inverse. Comparing determinants gives a degree-$O(d)$ refutation. The right-slice case uses $y=1_A$ in the same way.

Otherwise choose constant vectors $x_0,y_0$ with both slices $S(x_0,-),S(-,y_0)$ invertible. Transport the two target input spaces by these slices to the output space. On that space define
$$
z*w=S\bigl(S(-,y_0)^{-1}z,\ S(x_0,-)^{-1}w\bigr).
$$
It has unit $e=S(x_0,y_0)$. The original comparison is now with this unital bilinear product, which may a priori fail associativity. Write $P',Q',R'$ for inverses in these coordinates, and put $u=P'e,\ v=Q'e$. The reversed action gives for every $z$ in the target
$$
R'z=u(Q'z)=(P'z)v.
$$
Consequently left multiplication by $u$ and right multiplication by $v$ on $A$ have the two-sided inverse operators $Q'R$ and $P'R$. Taking their values on $1_A$ gives polynomial vectors $\bar u,\bar v$ with $u\bar u=\bar v v=1_A$. The other orders follow from associativity of $A$ and the displayed inverse operators, for example $u(\bar u u)=u$ implies $\bar u u=1_A$. Now
$$
\psi(z)=\bar u(R'z)\bar v,\qquad \phi(a)=R(uav)
$$
give inverse linear maps and satisfy $\psi(e)=1_A,\ \psi(z*w)=\psi(z)\psi(w)$. For the last identity use $P'z=(R'z)\bar v$, $Q'w=\bar u(R'w)$ in $R'(z*w)=(P'z)(Q'w)$. All these are explicit bounded-degree polynomial operations in the raw variables with constant-degree derivations. Substituting any three constant target basis vectors into the associator and applying $\psi$ gives zero by associativity in $A$; applying $\phi$ then gives the associator itself. This refutes a nonassociative target by a nonzero associator coordinate. Otherwise the same identities give a certified algebra isomorphism between $A$ and the constant unital associative target algebra $B$.

## 3. Recover the radical filtration and the quotient permutation

Write $I_A,I_B$ for the commutator ideals of these algebras, meaning the spans of all $a[x,y]b$. They transport in both directions under $\phi,\psi$ with constant-degree certificates, by expanding each product in a constant basis and applying the homomorphism equations. In the thin source, every diagonal corner is spanned by $e_i$, and each off-diagonal corner is a commutator since $[e_i,x]=x$ for $x\in e_iAe_j$, $i\ne j$. The quotient $A/J$ is commutative. These facts give $I_A=J$.

For each $h$, the powers $I_A^h,I_B^h$ transport with constant degree independently of $h$. To see this, choose fixed bases for each ideal power and express each basis vector in the next power as a sum of products of a fixed vector in the current power and a fixed vector in the ideal. Apply the algebra-map equations to these bilinear products, and use the preceding projection lines for the two factors. This derives the next projection lines. Every multiplication at this step combines just two vectors of bounded-degree witness polynomials. Starting at $h=0$ uses the whole algebra. If $I_B^d\ne0$ while $I_A^d=0$, the reverse projection lines say $\psi(x)=0$ for some nonzero constant $x$ in the target power. Its inverse forces $x=0$. Here $J^d=0$ follows from the descending radical filtration in dimension $d$.

The maps induce inverse unital algebra maps on $A/I_A$ and $B/I_B$. Projection to a fixed linear complement in each algebra gives their coordinate matrices and the constant-degree certificates. The source quotient is $k^m$ in the current geometric coordinates. Transport its diagonal separability element $\sum_i e_i\otimes e_i$ to the target quotient. Its image has product $1$ and satisfies
$(a\otimes 1)\Delta=\Delta(1\otimes a)$ for every constant basis vector $a$ there, by expressing $a$ through the inverse map. These are fixed linear equations for a separability element. If inconsistent they directly refute the raw system. If consistent, the commutative target quotient is a product of copies of the algebraically closed field, since the separability element averages projections to split every submodule. Nilpotence of $I_B$ now shows $I_B=\operatorname{rad}B$. Unequal quotient dimensions yield a determinant rank refutation in degree $O(d)$.

Write $f_{ji}$ for the coefficients of the images of the primitive source quotient idempotents in the primitive target quotient basis. Each has degree bounded by a constant in the raw witness. The forward map gives Boolean idempotence, row orthogonality and row sums one. The inverse map gives the corresponding identities to the other side. To identify its coefficient $g_{ij}$ with $f_{ji}$, pull back the identity $e'_j\phi(e_i)=f_{ji} e'_j$ and take coordinate $i$, obtaining $g_{ij}=f_{ji}g_{ij}$. Pushing forward the reverse identity gives $f_{ji}=g_{ij}f_{ji}$. Thus the Boolean matrix $f$ also has column orthogonality and column sums one. Choose actual orthogonal idempotents $e'_j$ in $B$ lifting this quotient basis, which exist for nilpotent ideals in finite-dimensional associative algebras.

## 4. Refute one permutation branch

Fix a permutation $\sigma$ and assume $f_{\sigma(i),i}=1$ for each $i$. Orthogonality forces the other coefficients in these columns to vanish, so $\phi(e_i)-e'_{\sigma(i)}$ belongs to $I_B$ modulo bounded-degree certificates. We first show how to refute any mismatch between the dimensions of corresponding Peirce corners. On each radical grade $I^h/I^{h+1}$, the forward and reverse maps exist and are inverses by the projection lines of Section 3. Under the branch equations, they transport left and right multiplication by $e_i,e_j$ to the corresponding target multiplications: after projecting to the grade the error $\phi(e_i)-e'_{\sigma(i)}$ is killed because it belongs to $I_B$. Their composite is the projection to the grade of the corner $e_iAe_j$. Restrict forward and reverse matrices to its image and to the matched image for $B$. They give two rectangular inverse identities with entries of bounded degree. If the respective dimensions differ, their larger determinant identity refutes the branch in degree $O(d)$. A mismatch of total corner dimensions entails a mismatch on some grade because the filtration of each corner is obtained by these commuting projections. Therefore, for the remaining branches all target corners are thin and their dimensions match those of the source.

Set $p_i=\phi(e_i)$, $q_i=e'_{\sigma(i)}$, and define
$$
U=\sum_i p_iq_i,\qquad V=\sum_i q_i p_i .
$$
The equations $p_i p_j=\delta_{ij}p_i$ and $\sum_i p_i=1$ follow by transporting the corresponding identities. Hence $VU=\sum_i q_i p_i q_i=1$: the difference $q_i(p_i-q_i)q_i$ is zero because $q_i I_B q_i=0$ in each one-dimensional diagonal corner. The element $h=1-UV$ is then idempotent and its reduction modulo $I_B$ is zero. Derive $h=0$ at constant degree as follows. If the current projection lines express $h$ in $I_B^{2^j}$, replace both factors in $h^2$ by their projections to that space. The square has zero projection outside $I_B^{2^{j+1}}$. Using $h^2=h$ derives the new projection lines. The degree stays bounded independently of $j$ because each step multiplies at most two of the same bounded-degree coordinate polynomials and uses the previous projection lines. Nilpotence eventually gives $h=0$, so $U,V$ are two-sided inverses. Also $p_iU=Uq_i$. The adjusted forward map $a\mapsto V\phi(a)U$ now sends $e_i$ to $q_i$. Its inverse is $b\mapsto\psi(UbV)$. The adjusted maps and their identities have constant degree in the raw witnesses on the branch.

On each nonzero corner choose one basis vector $a_{ij}$ and one matched vector $b_{ij}$, using the idempotents on the diagonal. The adjusted map on the corner is
$$
a_{ij}\longmapsto \lambda_{ij} b_{ij}.
$$
The reverse gives $\mu_{ij}$, with $\lambda_{ij}\mu_{ij}=1$ and $\lambda_{ii}=1$. These scalar entries are bounded-degree polynomials in the raw variables, and all the stated identities have constant-degree derivations. Products on composable corners compare fixed scalars via
$$
c_{ijk}\lambda_{ik}=c'_{ijk}\lambda_{ij}\lambda_{jk}.
$$
If both outside corners are absent the corresponding products contribute no constraints. Mismatched zero and nonzero structure constants yield an immediate contradiction by the inverse equations. Otherwise the comparison is a Laurent-binomial system on at most $d$ invertible scalars, with exponent vectors of $\ell_1$-norm at most three. A solution extends to an actual algebra isomorphism by the displayed corner maps and hence gives a tensor isomorphism. Therefore, on a geometrically negative input the remaining Laurent system in every branch is inconsistent.

## 5. Linear degree for the Laurent system and removal of branches

Let $a_j\in\mathbb Z^s$ with $\|a_j\|_1\le D$, and let the equations be $x^{a_j}=c_j\ne0$ on a torus, with named inverse variables. If the system has no point over an algebraically closed field, there is an integral relation $\sum_j h_j a_j=0$ with $\prod_j c_j^{h_j}\ne1$. Indeed without such a relation the assignments define a homomorphism from the lattice spanned by the $a_j$ into the multiplicative group. The integer Smith form extends this homomorphism to all of $\mathbb Z^s$, since arbitrary integral roots exist in the field.

Make a multiset of signed exponent vectors from the relation, using $|h_j|$ copies with the indicated sign. Steinitz's lemma in the $\ell_1$ norm orders this zero-sum multiset with every partial sum of norm at most $sD$. Represent a Laurent monomial by its positive powers and the corresponding named inverse powers. For each step with signed vector $a$ and assigned constant $c$, multiply the previous line $x^w-C=0$ by the current $x^a$, use the current equation, and cancel each adjacent inverse pair by a monomial multiple of $x_i\bar x_i-1$. This derives $x^{w+a}-Cc=0$ in degree at most $(s+1)D$. A step using $-a_j$ is justified by multiplying the original binomial by $x^{-a_j}$ and cancelling, in degree at most $2D$. The final step gives the nonzero constant $1-\prod_j c_j^{h_j}$. Thus the degree is $O((s+1)D)$, regardless of the number of steps. Substitute the scalar witness polynomials of Section 4, and use their bounded-degree derivations. Each branch has degree $O(d)$. [Grinberg–Sevastyanov, Steinitz's constant](https://doi.org/10.1007/BF01086559)

To discharge a permutation branch, multiply every line by
$E_\sigma=\prod_i f_{\sigma(i),i}$. The extra branch axioms multiplied by $E_\sigma$ are derived from idempotence. The other axioms multiplied by $E_\sigma$ follow by monomial multiplication and addition. Inference remains valid with this fixed multiplier, so the degree increases by only $O(m)$ and the branch derives $E_\sigma=0$ in the raw system. Finally expand the product of the $m$ column sums. A term selecting the same row in distinct columns vanishes by row orthogonality, and the surviving terms correspond to permutations. Thus $\sum_\sigma E_\sigma=1$ in degree $O(m)$. This yields the required refutation at degree $O(d)$. The number of branches does not enter the degree estimate.

## 6. Sharpness, including characteristic zero

For a finite simple undirected graph $G$, use an algebra with diagonal idempotents $e_i$ for each vertex and one arrow $a_{ij}$ for each oriented edge, both orientations included. Its only nonzero products on these basis elements are
$$
e_i^2=e_i,\qquad e_i a_{ij}=a_{ij}=a_{ij}e_j.
$$
It is the unital algebra with square-zero radical described by the vertex actions on the arrow space. It is thin. Its multiplication tensor has ordinary rank at most $|V(G)|+4|E(G)|$ by the displayed support of the table. Algebra equivalence implies graph equivalence, since the quotient permutation and the corners of its radical recover oriented adjacency. Conversely a graph isomorphism induces the corresponding algebra isomorphism. Tensor equivalence is equivalent to algebra equivalence by the unital isotopy argument of Section 2 over a field.

Let $x_{ui}$ be the usual Boolean graph-isomorphism variables mapping source vertex $i$ to target vertex $u$, with row and column sums, local compatibility, and collision equations. Substitute the vertex matrix $X=(x_{ui})$ on the idempotents and the matrix
$$
Y_{(u,v),(i,j)}=x_{ui}x_{vj}
$$
on the oriented edges, using transposes for the inverses. The projected matrix inverse equations have constant-degree proofs. Off-diagonal entries of $Y^{\mathsf T}Y$ or $YY^{\mathsf T}$ vanish by row or column collisions. On the diagonal, use the Boolean equations and extend the sum over oriented edges to all ordered vertex pairs. The extra summands are zero by local compatibility. The full product is one by the two vertex sums. Multiplication is preserved by the substitution at constant degree: for example the coefficient on $a'_{uv}$ in the image of the product $e_s a_{ij}$ is compared with $x_{us}x_{ui}x_{vj}$, and this equals $\boldsymbol1_{s=i}x_{ui}x_{vj}$ by collisions or idempotence. Right multiplication and diagonal products follow by the same equations, and both arrow products are zero. Using the inverse identities converts this homomorphism equation into the literal tensor action with constant overhead. A degree-$D_0$ literal TI refutation would therefore give a graph isomorphism refutation of degree $O(D_0+1)$.

Use the bounded-degree graph instances with linear PC degree lower bounds of Berkholz and Grohe in characteristic zero. Their vertex and edge counts are linear in the lower-bound parameter. Their two graphs have the same edge count, as in the bounded-degree CFI families. The multiplication tensors give linear lower bounds in ordinary rank and border rank on this thin class. For every fixed positive characteristic the previous rectangle instances with padded diagonal tensors already give linear lower bounds. These are padded multiplication tensors of products of copies of $k$ and also belong to the class. [Berkholz–Grohe](https://arxiv.org/abs/1502.05912) · [Tensor isomorphism paper, Section 5](https://arxiv.org/abs/2305.19320) · [Earlier rectangle examples](https://github.com/Dugongue/MathProofs/blob/fa1001c4a32d65711c2864f4bdfa1257a44e333b/TensorSparsePCBounds/Proof.md)

The degree conclusion concerns ordinary Polynomial Calculus proofs on the original tensor equations. The construction uses proof lines of lower degree after each multiplication or projection step. It gives no polynomial bound on the number of lines. The result is a sharp sufficient class for the rank question and includes nonsemisimple and graph-isomorphism-hard examples. Publication priority for the combination is provisional.
