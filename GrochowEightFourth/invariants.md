# Composite cyclic and modular invariant-field degrees

All question numbers are from Blum-Smith, Garcia, Hidalgo and Rodriguez. Write $\beta_{\mathrm{field}}$ for the least degree in which polynomial invariants generate the rational invariant field, $\gamma_{\mathrm{field}}$ for the least degree in which those invariants contain a transcendence basis, and $\beta_{\mathrm{sep}}$ for the least degree in which polynomial invariants distinguish all distinct orbits. Proofs here are informal. [Original article, Journal of Pure and Applied Algebra 228 (2024), 107693](https://doi.org/10.1016/j.jpaa.2024.107693) · [Questions 5.5–5.16 and the underlying lattice results](https://arxiv.org/html/2303.05626v6#S5).

In the nonmodular cyclic and abelian cases we use the original paper's base-change and multiplicity reductions. With distinct nontrivial weights $a_1,\ldots,a_m$ in the character group $\widehat G$, the relevant exponent lattice is
$$
L=\ker\left(\mathbb Z^m\longrightarrow\widehat G,\quad e_i\longmapsto a_i\right).
$$
The nonnegative lattice vectors of coordinate sum at most $d$ generate $L$ exactly when $\beta_{\mathrm{field}}\le d$. These vectors have full real rank exactly when $\gamma_{\mathrm{field}}\le d$. In particular, a nonnegative basis of an index-$n$ lattice in $\mathbb Z^m$ can be certified by the absolute determinant $n$. [Original article, §2](https://arxiv.org/html/2303.05626v6#S2).

## Question 5.5. The composite-order extremizer classification fails

For every even $n=2H\ge8$, the three distinct weights $\{1,-1,H+1\}$ have generation degree
$$
\beta_{\mathrm{field}}=H=\left\lceil n/\lceil 3/2\rceil\right\rceil .
$$
They lie in none of the classes proposed for prime order. This gives a negative answer to Question 5.5 about exact equality in the proposed bound. [Question 5.5](https://arxiv.org/html/2303.05626v6#S5.SS1).

The weight relation is $x-y+z+Hz\equiv0\bmod 2H$. If the degree is below $H$, an odd $z$ would force $x-y+z$ to be congruent to $H$ modulo $2H$, contrary to its absolute value being below $H$. For even $z$ the relation instead implies $x-y+z=0$. All the short relations therefore lie in a plane. The three nonnegative rows
$$
(1,1,0),\qquad (0,2,2),\qquad(H-1,0,1)
$$
have degrees at most $H$, lie in the lattice, and have absolute determinant $2H$. This proves the exact generation degree.

The unique inverse pair in the support is $\{\pm1\}$, a pair of units modulo $n$. A three-element deletion from $\{\pm1,\pm2\}$ has its unique inverse pair either $\{\pm1\}$ or $\{\pm2\}$. Dilating the latter pair by a unit cannot turn its two nonunits into units. Dilating the former to $\{\pm1\}$ forces the multiplier to be $\pm1$, after which the remaining weight is $\pm2$. The weight $H+1$ is different from both $2$ and $-2$ modulo $2H$ for $H\ge4$.

## Question 5.12. Composite order preserves the upper bound and can lower the equality value

Let $n=qb+r$ with $0<r<b<n$, and let the two distinct nontrivial weights satisfy $A_2=bA_1\bmod n$. The exponent vectors $(r,q)$ and $(r+b,q-1)$ are invariant, since $r+bq=n$. Their determinant has absolute value $n$, so they are independent even if the action has a kernel. The two-character identity $\gamma_{\mathrm{field}}=\beta_{\mathrm{field}}$ of Proposition 4.1 applies to the effective quotient and gives $\beta_{\mathrm{field}}\le q+b+r-1$.

For any even $b\ge4$, take $n=2b+2$ and weights $1,b$. The action is faithful and $q=r=2$, so the original sufficient condition $q\ge r(r-1)$ holds and would assert equality at $b+3$. The vectors $(2,2)$ and $(0,b+1)$ instead give an invariant lattice basis of determinant $2(b+1)=n$. For degree less than $b+1$, if $y$ is even, the congruence $x+by\equiv0\bmod n$ implies $x=y$. If $y$ is odd, it implies $x\equiv b+1+y\bmod n$, which has no nonnegative solution with $x+y<b+1$. Thus the smaller-degree rows have rank one. It follows that $\beta_{\mathrm{field}}=b+1$, and Question 5.12 is negative for Proposition 4.2 as stated. [Propositions 4.1–4.2 and Question 5.12](https://arxiv.org/html/2303.05626v6#S4.SS1).

## Question 5.13. Two faithful weights can exceed the prime-order bound

For $n=4\ell\ge8$ take weights $1,n/2-1$. Both are units modulo $n$, and the weights are distinct and noninverse. The invariant congruence is
$$
x-y+\frac n2 y\equiv0\pmod n .
$$
If $y$ is even, it reduces to $x\equiv y\bmod n$. Degrees below $n/2+2$ therefore force $x=y$ in that case. If $y$ is odd, $x$ is also odd and $|x-y|\ge n/2$, giving $x+y\ge n/2+2$. The rows of degree below $n/2+2$ consequently have rank one. The exponent vectors $(2,2)$ and $(n/2+1,1)$ form a lattice basis of absolute determinant $n$. Consequently
$$
\beta_{\mathrm{field}}=n/2+2>(n+3)/2.
$$
This answers Question 5.13 in the negative. [Proposition 4.4](https://arxiv.org/html/2303.05626v6#S4.SS1) · [Question 5.13](https://arxiv.org/html/2303.05626v6#S5.SS2).

## Question 5.6. Density and primitive weights yield a gap for composite cyclic groups

For a nonmodular cyclic representation of order $n$, write $A\subseteq(\mathbb Z/n)\setminus\{0\}$ for its distinct nontrivial weights. For $K$ algebraically closed or $K=\mathbb R$, the following give strict separation between the degrees.

- If $n$ is composite and $|A|>3n/4$, then $\beta_{\mathrm{field}}\le3<4\le\beta_{\mathrm{sep}}$.
- If $n\ge4$, at least one weight is primitive, and at least three distinct nonzero weights occur, then $\beta_{\mathrm{field}}\le n-1<n=\beta_{\mathrm{sep}}$.

An absolute cutoff on the number of weights across all composite cyclic orders is impossible, even for faithful representations. These statements answer the density and uniform-count interpretations of Question 5.6. [Question 5.6](https://arxiv.org/html/2303.05626v6#S5.SS2).

### Dense support gives degree three

This argument works in any finite abelian character group $\Gamma$ of order $n$. Let $H_A$ be the quotient of the free abelian group on the weights by the nonnegative zero-sum relations of degree at most three. Write $f(a)$ for the class of the generator indexed by $a\in A$. For each increment $x\in\Gamma$, put $B_x=A\cap(A-x)$. If $a,b\in B_x$ and $-a-b-x\in A$, the two cubic relations with summands $(a+x,b,-a-b-x)$ and $(a,b+x,-a-b-x)$ give
$$
f(a+x)-f(a)=f(b+x)-f(b).
$$
For arbitrary $a,b\in B_x$, there is a common comparison point
$$
c\in A\cap(A-x)\cap(-a-x-A)\cap(-b-x-A).
$$
All four sets have size $|A|$, and $4|A|>3n$ guarantees a nonempty intersection. Thus the increment function $F(x)=f(a+x)-f(a)$ is well defined, since $B_x$ is also nonempty. Threefold translate intersection yields $a,a+x,a+x+y\in A$ for any $x,y$. Telescoping proves $F(x+y)=F(x)+F(y)$.

The difference $f(a)-F(a)$ is constant on $A$. A quadratic zero-sum word exists by $2|A|>n$. A cubic zero-sum word exists by choosing $a\in A$ and using $2|A|>n$ to solve $b+c=-a$ in $A$. These two words kill two and three times the constant, so the constant vanishes. The natural map $H_A\to\Gamma$ is onto because $A$ is too large to be contained in any proper subgroup. The additive map $F$ inverts it on the generators of $H_A$. The zero-sum relations of degree at most three therefore generate the full exponent lattice.

In the cyclic case with composite $n$, at most three nonzero weights can have order two or three. When the density assumption is nonvacuous it forces at least four weights, hence some weight of order at least four. In an algebraically closed field, restricting to its coordinate line shows that invariants of degree below the weight order are constant on that line. Over $\mathbb R$, use a real rotation plane corresponding to the weight and its inverse. Complexifying that plane gives coordinates of opposite weights, so any invariant of degree below the rotation order is a polynomial in the squared radius. It cannot distinguish all orbits on the plane.

### Primitive weights give a gap from three nonzero weights onward

Normalize a primitive weight to $1$. For any other weight $b\ne-1$, use the representative $2\le b\le n-2$. If $b\le n/2$, write $n=qb+r$ with $q\ge2$ and $0\le r<b$. The vectors $(r,q)$ and $(r+b,q-1)$ make an invariant basis on this pair, of maximal degree $q+b+r-1=n-(q-1)(b-1)<n$.

If $b>n/2$, set $x=n-b$ and $j=\lceil n/x\rceil$. Then $(x,1)$ and $(jx-n,j)$ are nonnegative invariant rows of absolute determinant $n$. Their degrees are at most $\max(x+1,x+n/x)$. The convex function $x+n/x$ has value $n/2+2$ at both endpoints of $[2,n/2]$. In this case $n\ge5$, so both degrees are below $n$. Thus each pair just considered has its lattice generated in degrees below $n$. These pair lattices give $ne_1$ and all relations $e_b-be_1$ for $b\ne\pm1$ and $b\in A$. The relation for $-1$, if present, is the degree-two row $e_{-1}+e_1$. The listed relations generate the full lattice.

The primitive weight gives $\beta_{\mathrm{sep}}\ge n$ by the line or rotation-plane argument above. The upper bound $\beta_{\mathrm{sep}}\le n$ for a finite group of order $n$ follows directly by orbit products. Given two distinct orbits, choose a linear form whose value at one point of the first orbit differs from all values on the second orbit. Over the infinite base fields here such a form exists by avoiding finitely many proper subspaces. The product over the group of the translates of the form minus its chosen value is invariant, vanishes on the first orbit, and is nonzero on the second.

### Arbitrarily many characters can give coincident degrees

Let $p<q$ be distinct odd primes and write $C_{pq}=C_p\times C_q$. Let the first factor act on a summand containing every nontrivial $C_p$-weight. Let the second factor act on a faithful one-dimensional summand over an algebraically closed field, or a faithful real rotation plane over the reals. Each factor acts trivially on the other summand. The invariant ring is the tensor product of the two factor invariant rings, with their usual total grading.

In the algebraically closed case, the below-$q$ polynomials are independent of the second summand. In the real case they depend on it only through its squared radius. Thus $\beta_{\mathrm{field}}\ge q$. The nonmodular Noether bound for each factor gives $\beta_{\mathrm{field}}\le q$, and factorwise orbit products give $\beta_{\mathrm{sep}}\le q$. Restricting to the second summand gives $\beta_{\mathrm{sep}}\ge q$. These actions are faithful and have unbounded numbers of characters with $\beta_{\mathrm{field}}=\beta_{\mathrm{sep}}$.

## Question 5.7. The density criterion extends to finite abelian groups

Let $G$ be finite abelian of order $n\ge27$. Over an algebraically closed nonmodular field or over $\mathbb R$, a support of more than $3n/4$ distinct nontrivial characters satisfies
$$
\beta_{\mathrm{field}}\le3<4\le\beta_{\mathrm{sep}}.
$$
The upper bound was proved above. For the lower bound, write $\Gamma=\widehat G$. If $\Gamma$ has exponent at least four, the two subgroups $\Gamma[2]$ and $\Gamma[3]$ are proper. For proper subgroups $U,V$ of an abelian group of order $n$, their union has size at most
$$
|U|+|V|-\frac{|U||V|}{n}\le\frac{3n}{4}.
$$
The first inequality uses $|U+V|\le n$. The last uses $|U|,|V|\le n/2$. Thus the dense support contains an order-at-least-four character, and the line or plane argument applies.

Otherwise $\Gamma$ is elementary abelian of exponent $p=2$ or $p=3$. Choose independent $a,b\in A$. The intersection $A\cap(-a-b-A)$ has size greater than $n/2>p^2$, so choose $c$ in it outside $\langle a,b\rangle$. Then $d=-a-b-c$ belongs to $A$. The four weights $a,b,c,d$ sum to zero and every three are linearly independent. Over a splitting field, restrict the representation to one coordinate of each weight. Over the reals and $p=3$, use one real rotation plane for each weight, with net complex exponent measured as the exponent on $z_i$ minus the exponent on $\bar z_i$. Over the reals and $p=2$, use four real sign lines.

On these four summands, any invariant monomial of degree at most three involves at most three distinct summands. The independence property forces its exponent, or net complex exponent, on every summand to vanish modulo $p$. Consequently all such monomials are unchanged when a single nonzero coordinate is multiplied by a primitive $p$th root, using rotation of one plane in the real $p=3$ case. Taking every coordinate nonzero gives a new point in a distinct group orbit. The sum-zero relation forces the product of the four group phases to be one, which fails for this selected change. This proves $\beta_{\mathrm{sep}}\ge4$.

A uniform absolute cutoff on the number of weights is again impossible. Use $C_p^2\times C_q$ with $q>p^2$ and take the full nontrivial support of the first factor independently of the faithful line or rotation plane of $C_q$. The identical factorwise argument gives $\beta_{\mathrm{field}}=\beta_{\mathrm{sep}}=q$ and unbounded support sizes. [Question 5.7](https://arxiv.org/html/2303.05626v6#S5.SS2).


## Question 5.9. A faithful modular family with an unbounded ratio

Fix a prime $p$, an algebraically closed field $K$ of characteristic $p$, and an odd prime $q>\max\{p,3\}$. Give $C_{pq}=C_p\times C_q$ the following faithful representation. The $C_p$ factor acts on a two-dimensional block by a nontrivial transvection, and the $C_q$ factor acts on another block containing every nontrivial character of $C_q$. The factors act independently on the two blocks. Then
$$
\beta_{\mathrm{field}}=\max\{p,3\},\qquad \beta_{\mathrm{sep}}=q.
$$
In particular $\beta_{\mathrm{field}}<\tfrac12\beta_{\mathrm{sep}}$ for every $q>2\max\{p,3\}$. The ratio $\beta_{\mathrm{sep}}/\beta_{\mathrm{field}}$ is unbounded at each fixed $p$. This supplies sufficient hypotheses for both gaps asked for in Question 5.9. [Question 5.9](https://arxiv.org/html/2303.05626v6#S5.SS2).

Choose linear coordinates $x,y$ on the transvection block with the generator acting by $x\mapsto x$, $y\mapsto y+x$. The invariant $w=y^p-x^{p-1}y$ has degree $p$. The coordinates $x,w$ generate the invariant field since $y$ is a root of a degree-$p$ equation over $K(x,w)$ and the group has order $p$. They separate orbits as well: equal values at a fixed nonzero $x$ give a difference in $x\mathbb F_p$, while at $x=0$ the map $y\mapsto y^p$ is injective. For the degree lower bound, every invariant polynomial of degree less than $p$ is independent of $y$. Indeed, if its highest $y$-degree is $j>0$, the coefficient of $y^{j-1}$ in its difference under $y\mapsto y+x$ is $jx$ times its leading coefficient. It cannot vanish for $0<j<p$.

The second block has $\beta_{\mathrm{field}}\le3$ by the density proof above, since $q-1>3q/4$. The degree-two vectors are the mutually disjoint inverse-pair relations, of rank less than $q-1$. Thus its field generation degree is exactly three. Its separating degree is $q$, by restriction to a primitive line and the orbit-product bound.

The invariant ring on the combined representation is the polynomial-degree graded tensor product of the two invariant rings. This holds also in the modular setting since each factor acts trivially on the other block: one can impose invariance on each coefficient in a vector-space basis of the other block. The field generation degree is the maximum of the two factor values. To see the lower bound directly, let $L_i$ be the full invariant field and $M_i$ the subfield generated up to degree $d$ on factor $i$. Choose the two variable sets disjoint. In the combined field, the degree-$d$ invariant field is the compositum $M_1M_2$. An element of $L_1$ in $M_1M_2$ belongs to $M_1$: expand the numerator and denominator of a rational expression as finite $M_1$-linear combinations of functions in the second variables that are linearly independent over $K$. They remain linearly independent over the first variable field, so equality in one coefficient expresses the element as a quotient in $M_1$. The same argument applies to $L_2$. The upper bound is given by the union of generating sets. The separating degree is also the maximum, since factorwise degrees suffice and restriction to a block gives a lower bound. This proves the stated formulas.


### A uniform field bound on representations with independent generic orbit vectors

Let $V$ be a representation of a finite group $G$ over any field $K$. Suppose the $|G|$ orbit vectors of the generic point of $V$ are linearly independent over $L=K(V)$. This holds for the regular module and for any representation containing it, since at a regular basis vector the orbit is a basis of the regular summand. Then
$
\beta_{\mathrm{field}}(G,V)\le3.
$
Edidin and Katz already recover the generic orbit from the second and third orbit tensors in every characteristic. The following construction obtains equality of the rational fields in modular characteristic by verifying separability. [Edidin and Katz, Theorem III.1](https://arxiv.org/html/2503.00009#S3) · [Blum-Smith and Derksen, §3.1](https://arxiv.org/html/2506.05650v4#S3.SS1).

Let $x\in V(L)$ be the generic point and let $M$ be the subfield of $L$ generated over $K$ by the entries of the invariant tensors
$
C_2(x)=\sum_{g\in G}(gx)^{\otimes2},
\qquad
C_3(x)=\sum_{g\in G}(gx)^{\otimes3}.
$
Regard $C_2$ as a map $V_M^*\to V_M$ and let $W$ be its image. Over $L$, the independent vectors $gx$ are a basis of $W_L$: restriction of functionals to their span is onto, and contraction with $C_2$ sends a functional to the linear combination having its evaluations as coefficients. Also $C_2\in W^{\otimes2}$ and $C_3\in W^{\otimes3}$ over $M$, because each inclusion holds over $L$ and membership in a linear subspace descends through scalar extension.

The inverse to $C_2:W^*\to W$ gives a nondegenerate bilinear form $B$ over $M$. Contract the three arguments of $C_3$ by $B$ to obtain a trilinear form. Define a multiplication $\mu$ on $W$ by
$
B(\mu(u,v),w)=C_3\bigl(B(u,-),B(v,-),B(w,-)\bigr).
$
In the basis $gx$ over $L$, the form $B$ has identity Gram matrix and $\mu$ is coordinatewise multiplication. In particular the vectors $gx$ are precisely the primitive idempotents, and $W_L$ with this multiplication is the split product of $|G|$ copies of $L$. Commutativity and associativity descend through the field extension, and the unique identity descends by solving the linear identity equations over $M$. Thus this is an $M$-algebra.

One can see separability directly. The field $M$ is infinite, since some entry of the positive-degree tensor $C_2$ is nonzero and hence nonconstant at the generic point. Choose $a\in W$ whose coordinates in the $gx$ basis are pairwise distinct. Such an $a$ exists by avoiding finitely many proper linear hyperplanes: a nonzero polynomial over $L$ cannot vanish on all $M$-points of an affine space when $M$ is infinite. Multiplication by $a$ is a matrix over $M$ whose eigenvalues are these distinct coordinates. Its characteristic polynomial is separable, and its spectral projectors over its splitting field are polynomials in this multiplication matrix. Applying each projector to the unit yields the corresponding primitive idempotent. Hence the coordinates of every $gx$, including $x$, lie in a finite separable extension of $M$ inside $L$. Since $L=M(x)$, the extension $L/M$ is finite separable.

Every $M$-embedding of $L$ into an algebraic closure sends $x$ to a primitive idempotent of this algebra. There are exactly $|G|$ such idempotents, and an embedding is determined by the coordinates of $x$. The $|G|$ group elements give distinct embeddings and fix $M$. Therefore $[L:M]=|G|$, and the fixed-field theorem gives $M=L^G$. This argument establishes actual field generation in all characteristics, including the degree-one group case where the conclusion also follows from linear invariants.

In characteristic $p$, if $G$ is a finite $p$-group, its regular module has $\beta_{\mathrm{sep}}=|G|$ by the classical orbit-sum argument. Indeed, evaluate the orbit sums of monomials at the vector whose coordinates all equal one. A monomial orbit contributes its size, which is zero in the field unless the orbit has size one. A fixed monomial has the same exponent in every coordinate by transitivity, so every fixed monomial of positive degree has degree at least $|G|$. Thus degree below $|G|$ cannot separate this vector from zero. The bound in the other direction is the orbit-product bound. Combining the two arguments gives $\beta_{\mathrm{field}}\le3$ and $\beta_{\mathrm{sep}}=|G|$ even for pure modular regular representations. [Kohls and Kraft, Proposition 8](https://dmi.unibas.ch/fileadmin/user_upload/dmi/Personen/Kraft_Hanspeter/Degree_Bounds.pdf#page=9).

## Question 5.16. The Hilbert series determines the cyclic quotient ring

Let $p$ be an odd prime and $K$ a field of characteristic different from $p$. For a two-dimensional representation of $C_p$ with two distinct nontrivial characters after extension to an algebraic closure, the Hilbert series of $K[V]^{C_p}$ determines the unordered character pair up to a group automorphism. It therefore determines the representation up to that automorphism and the graded invariant ring up to isomorphism. In particular, the exponent data in Proposition 4.5 recover the entire graded ring in this family. [Proposition 4.5](https://arxiv.org/html/2303.05626v6#S4.SS1) · [Question 5.16](https://arxiv.org/html/2303.05626v6#S5.SS2).

### Proof

Base change preserves the Hilbert series. Over the algebraic closure, normalize the two coordinate weights to $(1,b)$ with $b\ne0,1$ in $\mathbb F_p$. Use $[s]_p$ for the least nonnegative residue of $s\in\mathbb F_p$. Writing invariant exponents modulo $p$ shows that the Hilbert numerator with denominator $(1-t^p)^2$ counts pairs
$$
0\le x,y<p,\qquad x+by\equiv0\pmod p
$$
by the total degree $D=x+y$. For each nonzero residue $r=D\bmod p$ there is exactly one pair. With $c=(1-b)^{-1}$ its total degree is
$$
D(r)=[cr]_p+[(1-c)r]_p .
$$
In particular the Hilbert numerator determines this entire function of $r$.

For $a\in\mathbb F_p^\times$ define the real-valued function $h_a(r)=[ar]_p-p/2$ on $\mathbb F_p^\times$. Since $h_{-a}=-h_a$, regard its coefficients as indexed by one representative of each pair $\{a,-a\}$. These representative functions are linearly independent over $\mathbb C$. To prove this, suppose $\sum_a \lambda_a h_a=0$ for a sum over representatives. For an odd multiplicative character $\chi$, taking the sum against $\chi(r)$ gives
$$
0=\left(\sum_{r=1}^{p-1}r\chi(r)\right)
  \left(\sum_a\lambda_a\chi(a)^{-1}\right).
$$
The first factor equals $-p L(0,\chi)$ and is nonzero. Every odd character modulo prime $p$ is primitive, and its functional equation gives this nonvanishing from Dirichlet's nonvanishing of $L(1,\bar\chi)$. Equivalently, one may use the invertibility of the odd Maillet matrix. So the odd Fourier coefficients of the coefficient function extended by $\lambda_{-a}=-\lambda_a$ all vanish. Its even coefficients vanish by oddness, and Fourier inversion forces every $\lambda_a=0$. [Pathak, *On a conjecture of Livingston*, discussion of the least-residue character sums and their nonvanishing](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/243BB238260208BD279E611581D95760/S0008439500022773a.pdf/on-a-conjecture-of-livingston.pdf).

The Hilbert numerator determines $D(r)-p=h_c(r)+h_{1-c}(r)$. By independence it recovers the signed multiplicities of the unordered pair $\{c,1-c\}$ on the pairs of opposite residues. There is no cancellation, since the two entries sum to one. Signs and multiplicities therefore recover the unordered pair itself, including the case of a repeated entry. The choice $c\mapsto1-c$ sends $b=1-c^{-1}$ to $b^{-1}$, exactly the effect of swapping the two original weights and renormalizing. This proves the character-pair claim.

For descent to $K$, semisimple generator matrices which acquire the same multiset of eigenvalues after a group automorphism have the same squarefree invariant factors and are conjugate over $K$ by rational canonical form. The conjugation induces the graded invariant-ring isomorphism. Even if the prime order is unspecified, the Hilbert series recovers it by $\lim_{t\to1}(1-t)^2H(t)=1/p$.
