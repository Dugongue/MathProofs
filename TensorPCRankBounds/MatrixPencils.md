# Linear Polynomial Calculus degree for all matrix pencils

**Theorem.** Let $A,B$ be same-format three-tensors over any field, nonisomorphic over its algebraic closure, each with flattening rank at most two in the same mode. If both tensors have geometric border rank at most $b$, their literal cubic action and two-sided inverse equations admit an ordinary Polynomial Calculus refutation of degree $O(b+1)$, without field equations. The same conclusion holds with ordinary rank. The linear order is sharp in each fixed positive characteristic, even for concise pencils with two rank-drop points. The result allows rectangular and singular pencils, and repeated eigenvalues. It sharpens the previous bounded-mode polynomial upper bound for the literal equations. [Question 7.1](https://arxiv.org/abs/2305.19320) · [Earlier bounded-mode proof](https://github.com/Dugongue/MathProofs/blob/fa1001c4a32d65711c2864f4bdfa1257a44e333b/NavierStokesGrochowTransfers/BoundedModeTensorPC.md)

## 1. Compress supports and handle fixed pencils

Work over an algebraic closure and descend the proof. Only finitely many algebraic coefficients occur in a finite proof. Taking coordinates over a basis of their extension containing $1$ simulates the original derivations by linear combinations and variable multiplications, with no degree increase.

The supported mode dimensions are at most $b$ by closedness of the flattening rank conditions. Use constant bases putting each support first. In the action equation multiply by named inverses on the other two factors, then apply a constant right inverse for the supported rows of the source flattening. The outside rows of the target yield the vanishing of the block from supported source coordinates to complementary target coordinates. Reverse the action to obtain the corresponding zero block of the inverse. Consequently the supported blocks satisfy both rectangular inverse equations and the supported action. These derivations cost constant degree. If supports differ, a determinant of the larger rectangular product contradicts Cauchy–Binet in degree $O(b+1)$. If the supported slice dimension is one, ordinary matrix rank likewise suffices. A zero tensor against a nonzero one is immediate from the action and its reverse. Henceforth take two slices and put $n=\max(2,u,v)$ for the supported pencil format $v\times u$.

Up to transposes and names of inverses, the literal action gives
$$
P A(z) Q=B(H z),\qquad z=(x,y),
\tag{1}
$$
coefficient by coefficient, and all three factors have named two-sided inverses. For example if the forward slice transform gives $B(z)=P A(H_f^{\mathsf T}z)Q_f^{\mathsf T}$, replace $z$ by $(H_f')^{\mathsf T}z$ and use the specified inverse equations. All derivations have constant degree. The reverse equation likewise follows from the named inverses, so either pencil can be chosen as source.

For fixed left–right inequivalent pencils $A,C$, the linear equations $U A_i=C_i V$ have no solution with both $U,V$ invertible. On their fixed linear kernel the polynomial $\det U\det V$ vanishes identically, since a nonzero polynomial on an affine space over the algebraic closure is nonzero at some point. Project the witness coordinates onto the fixed kernel by constant linear combinations of the residuals. Comparing determinant products before and after this projection derives $\det U\det V=0$; the inverse equations derive $\det U\det V\det U'\det V'=1$. This is a degree-$O(n)$ refutation. If all four witnesses are explicit polynomials of degree $d_0$ whose identities have certificates of degree $d_1$, it costs $O(nd_0+d_1)$. The determinant comparison here and throughout replaces one column at a time, expands along that column, and uses the entrywise difference. The rank identities for rectangular products are Cauchy–Binet.

## 2. Branch on projective rank-drop points without reducing a multiple root

If normal ranks differ, evaluate the larger pencil at a constant point of maximum rank. The appropriate orientation of (1), Cauchy–Binet, and determinant comparison refute the claimed equivalence in degree $O(n)$, since all minors of the larger size are identically zero on the smaller pencil. Assume the common normal rank is $r>0$.

Let $F_B$ be the homogeneous gcd of the nonzero $r$-minors of $B(z)$. These minors have common degree $r$. The projective zeros of $F_B$ are precisely the rank-drop points. For a source rank-drop point represented by a fixed nonzero vector $p$, all the $r$-minors vanish at $z=Hp$ in degree $O(n)$, by comparing the minors in (1) with those of $P A(p)Q$. We can derive $F_B(Hp)=0$ at the same degree.

Indeed, homogeneous binary forms $q_i$ of the same degree $s>0$ with gcd $1$ have two coprime linear combinations $g,h$. Choose $g\ne0$ and choose $h$ avoiding all finitely many roots of $g$, possible since the field is infinite and the forms have no common projective zero. The map $(a,b)\mapsto ag+bh$ from $k[x,y]_{s-1}^2$ to $k[x,y]_{2s-1}$ is injective by coprimality and surjective by dimension. Thus every monomial of degree $2s-1$ has a homogeneous membership certificate. Apply this to the minors divided by $F_B$. With $Z=Hp$, one has $(\ell H')Z=1$, for a fixed row $\ell$ satisfying $\ell p=1$. Expanding the indicated linear combination of $Z$'s coordinates to power $2s-1$ consumes the homogeneous certificate and derives $F_B(Z)=0$ in degree $O(n)$. The degree-zero quotient case is immediate. If $F_B$ is a unit, this already refutes any source rank-drop point.

Otherwise write $F_B=c\prod_j\lambda_j^{e_j}$ for distinct linear forms up to proportionality and positive $e_j$. Set $E_j(Z)=\prod_{i\ne j}\lambda_i(Z)^{e_i}$. Then $E_j(Z)\lambda_j(Z)^{e_j}=0$, and the $E_j(Z)$ generate $1$ with degree-$O(n)$ certificates. For the latter, multiply each selector by all monomials of complementary degree to make them the same degree. They are still base-point-free, so the binary calculation and unimodularity of $Z$ apply.

Fix at most three distinct source points $p_i$. For every choice of a target $j_i$ per point, the branch assumes $x_i=\lambda_{j_i}(Hp_i)=0$. A degree-$D$ refutation on the branch gives $M=\prod_i E_{j_i}(Hp_i)=0$ in degree $D+O(n)$. In detail, $M x_i^{e_{j_i}}=0$ holds from the selector equations. For each vector of exponents $0\le h_i<e_{j_i}$, in descending total degree, replay the branch proof multiplied throughout by $M\prod_i x_i^{h_i}$. Each extra assumption $x_i$ multiplied by this polynomial has already been derived, either at the next exponent or from $M x_i^{e_{j_i}}=0$. The final line gives $M\prod_i x_i^{h_i}=0$. At exponent zero this gives $M=0$. The degree increase is $O(n)$ because there are at most three points. After every branch is discharged, multiply the three or fewer unit certificates for the separate selector lists. Expanding their product derives $1$ from the vanishing $M$'s. A branch sending distinct source points to the same target is refuted in constant degree: the two images of basis vectors under $H$ would be killed by the same nonzero row, contrary to $HH'=I$.

## 3. Three anchors give linear degree

If either pencil has at least three rank-drop points, use it as source and select three. On any remaining branch there is a unique projective transformation sending the ordered chosen points to the ordered target points. Fix a representative $H_0$. The linear equations of the branch force $H=\alpha H_0$ by fixed projection to their one-dimensional kernel. In bases given by the first two source points and the first two target points the matrix is diagonal, and the third pair fixes the ratio of the diagonal entries. A diagonal entry of $\alpha H_0 H'=I$ gives a polynomial inverse for $\alpha$. Absorb $\alpha$ into a row or column factor of (1), yielding a fixed-pencil comparison of $A$ and $B(H_0{-})$, with polynomial witnesses of constant degree. They are left–right inequivalent by the original geometric hypothesis. Section 1 refutes this in degree $O(n)$. The branch discharge preserves that bound.

## 4. Variable pencil transformations fixing at most two points

In the remaining case choose the pencil with more rank-drop points as source. Select all of them, possibly none. A surviving branch matches the two point sets bijectively. Choose a fixed invertible $H_0$ taking the source points to the target points, take $B_0(z)=B(H_0z)$, and set $K=H_0^{-1}H$. Thus $B(Hz)=B_0(Kz)$ and $K$ fixes all rank-drop points of $B_0$. We construct polynomial row and column factors $L,R$ with
$$
B_0(Kz)=L B_0(z) R
$$
and named polynomial inverses, all with entries and certificates of degree $O(n)$.

Take a fixed Kronecker canonical form of $B_0$. Its singular blocks have constant rank on $\mathbb P^1$. In homogeneous coordinates each nontrivial singular block is multiplication by $z$ from $\operatorname{Sym}^{j-1}(k^2)$ to $\operatorname{Sym}^j(k^2)$, or its transpose, using monomial bases. There can also be singular blocks with a zero side. Each regular block is $\lambda(z)I_a+\mu(z)J_a$, with independent linear forms and the nilpotent Jordan matrix $J_a e_i=e_{i-1}$, $J_a e_1=0$. Its rank-drop point is $\lambda=0$. [De Terán and Dopico, Kronecker canonical forms](https://arxiv.org/abs/2204.10237)

On a singular multiplication block, multiplication by $Kz$ is obtained by row action $\operatorname{Sym}^j(K)$ and column action $\operatorname{Sym}^{j-1}(K')$, where $K'$ is the inverse from $H'$. This is multiplicativity on the symmetric algebra and holds in all characteristics. Products with their inverses follow from the formal multiplicativity of symmetric powers and substitution of $KK'=I$ or $K'K=I$. Replacing a degree-$j$ monomial in matrix entries by its value at $I$ telescopes through one factor at a time, at degree at most $2j$. A transpose block uses transposed factors in reverse order. Zero-side blocks use identities.

For a regular block, the fixed-line branch gives
$\lambda(Kz)=\alpha\lambda(z)$ and $\mu(Kz)=\beta\lambda(z)+\gamma\mu(z)$.
In $(\lambda,\mu)$ coordinates these are the two rows of a triangular matrix, so $\alpha^{-1},\gamma^{-1}$ are represented by the diagonal entries of $K'$. The first diagonal entry of $KK'=I$ and the second diagonal entry of $K'K=I$ give the respective scalar inverse equations. Write $t=\beta/\alpha$, $c=\gamma/\alpha$, $J=J_a$, and $W=cJ(I+tJ)^{-1}$, with the last inverse expanded as a finite series. Then the transformed block is $\alpha(I+tJ)(\lambda I+\mu W)$. The matrix $S$ with column $i$ equal to $W^{a-i}e_a$ satisfies $WS=SJ$, because $W^a=0$. For $\ell>0$, the truncated formal identity
$$
W^\ell=c^\ell J^\ell\sum_{h=0}^{a-\ell-1}(-t)^h\binom{\ell+h-1}{h}J^h
$$
and $W^0=I$ bound every entry of $S$ by Laurent degree $O(a)$. Factoring the diagonal entry $c^{a-i}$ out of each column leaves an upper unitriangular matrix with off-diagonal $(i,j)$-entry a constant times $t^{j-i}$. Its inverse has the same form by the finite geometric series, since exponents add along index chains. Therefore $S^{-1}$ has Laurent degree $O(a)$ as well. The desired row and column maps are $\alpha(I+tJ)S$ and $S^{-1}$, with explicit inverses of the same degree. All these identities lift to ordinary polynomials at degree $O(a)$: count negative powers using the named inverse variables. For each product identity, cancel factors $\alpha\alpha^{-1}$ and $\gamma\gamma^{-1}$ by monomial multiples of their inverse axioms, without increasing monomial degrees.

Take the direct sum of these block formulas and undo the fixed row and column changes. Combining their identities with (1) gives
$$
(L'P)A(z)(QR')=B_0(z)
$$
with polynomial factors and inverses, of degree $O(n)$, justified in degree $O(n)$ on the branch. The two constant pencils are left–right inequivalent. To retain linear degree on the branch, compare only a mismatched multiplicity in their constant Kronecker decompositions.

## 5. Compare one Kronecker multiplicity with linear degree

It is enough to compare a single indecomposable type whose multiplicities in the two constant pencils $A,B_0$ differ. View a pencil as a representation of the two-arrow quiver, with the common domain and common codomain its two vertex spaces. Left–right equivalence is exactly representation isomorphism. The Kronecker canonical form decomposes each representation into indecomposable summands, and left–right inequivalence ensures that the two lists of multiplicities differ. Use fixed Kronecker bases in both pencils and identify copies of the same indecomposable with a fixed representative.

Put $M=A\oplus B_0$ as a quiver representation. For an indecomposable type $\tau$, the finite-dimensional endomorphism algebra of one copy of $\tau$ is local, with residue field the algebraically closed coefficient field. Indeed, Fitting decomposition for a module endomorphism splits the module into the eventually stable kernel and image, both subrepresentations. Thus each nonunit endomorphism of an indecomposable is nilpotent. The semisimple quotient of this algebra must be a division algebra, since any nonzero nonunit idempotent there would lift to a nonunit and therefore have to be nilpotent. A finite-dimensional division algebra over an algebraically closed field is the field. These facts use only the standard Artin–Wedderburn theorem and the lifting of units through the nilpotent radical.

There is an algebra homomorphism
$$
\rho_\tau:\operatorname{End}(M)\longrightarrow
M_{m_A+m_B}(k)
$$
where $m_A,m_B$ are the multiplicities of $\tau$ in the two pencils, and $k$ here denotes the algebraically closed working field. Keep exactly the blocks between copies of $\tau$ and in every retained block take the residue of its endomorphism in $k$. This rule preserves multiplication. In computing a retained entry of a product, all terms that pass through a different indecomposable type have residue zero. If such a term were invertible on $\tau$, its two maps would exhibit $\tau$ as a direct summand of the other indecomposable. For same-type terms the residue is multiplicative. This proves the assertion.

From Section 4 the forward quiver map from $A$ to $B_0$ is the pair with codomain component $L'P$ and domain component $RQ'$. Its inverse has components $P'L$ and $QR'$. They satisfy the quiver equations and inverse products in degree $O(n)$. Project each pair of blocks of each map onto the fixed linear space of homomorphisms between those chosen constant indecomposables. The projection is a constant linear operation on that pair of blocks alone, its difference has degree-$O(n)$ certificates, and the projected maps still satisfy the inverse identities in degree $O(n)$. The resulting forward and reverse maps are polynomial vectors in the fixed space of endomorphisms of $M$, zero off their respective direct-sum cross blocks. Their compositions are the two summand projections.

Let $s$ be the sum of the domain and codomain dimensions of $\tau$. The retained blocks of both quiver maps have degree $O(s)$, since $L,L',R,R'$ are block diagonal in the fixed Kronecker bases of $B_0$, and the degree of each such block is bounded by a constant times that block's size. The forward witnesses multiply those target blocks on the left; the reverse witnesses multiply them on the right. The blockwise linear projection preserves this degree bound on the retained entries. Applying $\rho_\tau$ therefore yields rectangular $m_B\times m_A$ and $m_A\times m_B$ matrices $F,G$ of entry degree $O(s)$, with inverse identities $FG=I_{m_B}, GF=I_{m_A}$ certified in degree $O(n)$. The inverse identities follow by applying the constant linear algebra homomorphism to the original composition residuals. If $m_A\ne m_B$, the larger rectangular product has zero determinant identically, so comparing with its identity refutes the branch in degree
$$
O\bigl(n+s\max(m_A,m_B)\bigr)=O(n).
$$
Here the product of the dimension of a summand and its multiplicity is bounded by the sum of the two dimensions of its respective pencil, at most $2n$. This includes a multiplicity of zero, when the larger inverse identity gives a contradiction directly.

Every branch therefore has degree $O(n)$, and its removal in Section 2 preserves this bound. This proves the uniform linear theorem.

## 6. Sharpness in positive characteristic at equal full supports

Fix a positive characteristic $p$. For arbitrarily large powers $q$ of $p$, put $r=4q$, $s=3q$, and $d=r+s+1$. Use
$$
A(z)=xI_d+y\,\operatorname{diag}(I_r,0_s,1),\qquad
B(z)=xI_d+y\,\operatorname{diag}(I_s,0_r,1).
$$
Both pencils are concise in all three modes and have ordinary rank and geometric border rank exactly $d$, by their diagonal decomposition and supported flattening ranks. The two rank-drop points are $x=0$ and $x+y=0$. The respective multiplicity multisets of their determinant factors are $\{s,r+1\}$ and $\{r,s+1\}$, which differ. Thus the pencils are geometrically nonisomorphic, although their format and flattening ranks are identical.

Use the rectangular matching PC lower-bound instance on an $r\times s$ variable matrix $X$. Its Boolean, collision, and row and column sum axioms give $XX^{\mathsf T}=I_r$ and $X^{\mathsf T}X=I_s$ in degree two. In the order of row and column blocks adapted to the two displayed pencils, set
$$
W=\operatorname{diag}\!\left(
 \begin{pmatrix}X^{\mathsf T}&0\\0&X\end{pmatrix},1
 \right).
$$
It maps the source block sizes $r,s,1$ to the target sizes $s,r,1$. Substitute $W$ on both matrix modes, $W^{\mathsf T}$ for their inverses, and the identity on the slice mode and its inverse. The projected identity-slice equation follows from $WW^{\mathsf T}=I_d$; the projector-slice equation uses its first block $X^{\mathsf T}X=I_s$. All projected axioms have derivations of their original constant degree, and the variables map to single variables or constants. Consequently a degree-$D$ refutation of this pencil pair gives a degree-$\max(D,3)$ refutation of the rectangular matching instance. The earlier matching degree lower bound is $\Omega(q)$ in characteristic $p$, proving sharp linear degree already for concise two-eigenpoint pencils in each fixed positive characteristic. [Earlier rectangular projection and Riis lower bound](https://github.com/Dugongue/MathProofs/blob/fa1001c4a32d65711c2864f4bdfa1257a44e333b/TensorSparsePCBounds/Proof.md)

This is a written proof for all two-slice comparisons, with provisional publication priority. The unrestricted rank question remains open.
