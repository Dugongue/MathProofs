# Exact orbit algorithms for the final-digit tensor family

Let $R$ be a finite commutative local ring, with nonzero maximal ideal $\mathfrak m$, residue field $k$ of cardinality $Q$, and $0\ne s\in\operatorname{Ann}_R(\mathfrak m)$. Put $J=sR$. Then $J\cong k$ by $\bar r\mapsto sr$, and $J^2=0$. Write $N=1+a_1+a_2+a_3$ and $n=N-1$, with $n\ge2$. The theorem includes $R=\mathbb Z/p^e\mathbb Z$ with $e\ge2$, $s=p^{e-1}$, and arbitrary $p,e$. For a varying general ring, the algorithms take the ring arithmetic, residue maps and the socle coordinate $J\cong k$ as explicit operations. All the stated bounds are polynomial in the array size and these arithmetic costs, including bit-polynomial time for the displayed prime-power rings.

**Theorem.** Encode a field bimap $t:k^{a_1}\times k^{a_2}\to k^{a_3}$ as the multiplication tensor of a unitization with residue-sized product $s t$ between disjoint input and output blocks. This family is recognized and decoded in polynomial time even after arbitrary independent invertible changes of basis in the three ring modes. The decoder and encoder give two-way polynomial-overhead reductions for decision, transporter search, exact transporter counting, and orbit canonization. No restriction on the residue characteristic dividing $N$ and no extra padding coordinate are needed.

Write $\mu_0$ for the multiplication of $R1\oplus R^n$ with $R^n$ square-zero. The entire affine fiber of tensors equal to $\mu_0\bmod J$ has an explicit linear orbit quotient under the three congruence kernels modulo $J$. Each such orbit has $Q^{2N^2-1}$ elements. If $b$ is the recovered labeled field bimap on $k^n$ and $\operatorname{Aut}_{\rm diag}(b)$ is its one-map automorphism group, the whole ring tensor orbit intersects the fiber in exactly
$$
 Q^{2N^2-1}\frac{|\mathrm{GL}_n(k)|}{|\operatorname{Aut}_{\rm diag}(b)|}
 \tag{1}
$$
points. The number of tensors in the fiber recognized as belonging to the family is also computable in polynomial time, without a tensor-isomorphism oracle.

## Encoding and removing the trace restriction

Let $B=R^n$ in the indicated three blocks, and let $b\colon\bar B\times\bar B\to\bar B$ be $t$ extended by zero elsewhere, where $\bar B=B/\mathfrak m B$. Define $A_b=R1\oplus B$, with $1$ a unit and $xy=s b(\bar x,\bar y)$ for $x,y\in B$. Here and below multiplication by $s$ applies to field coordinates via $J\cong k$. This is associative since $B^2\subseteq sB$ and $sB$ annihilates $B$. It reduces modulo $J$ to $\mu_0$. The three flattenings have unit minors obtained using a unit slice, or any $N$ coordinate pairs whose products are the basis when one input equals $1$.

Write $L_b,R_b$ for the left and right radicals of $b$ and $I_b$ for its image span. A bimap is of the encoded form in some basis exactly when
$$
 L_b+R_b=\bar B,\qquad I_b\subseteq L_b\cap R_b,\qquad
 \alpha=\dim(\bar B/L_b)\le a_1,\quad \beta=\dim(\bar B/R_b)\le a_2,
 \quad \gamma=\dim I_b\le a_3 .
 \tag{2}
$$
Indeed choose $U_0,V_0$ complementary to $L_b\cap R_b$ in $R_b,L_b$, respectively, and choose a complement to $I_b$ in $L_b\cap R_b$. The supported bimap on $U_0,V_0,I_b$, extended by zero to the original dimensions, has the required form. The span of $b(x,y)-b(y,x)$ equals $I_b$, since $b(V_0,-)=0$ and $b(-,U_0)=0$. This works in characteristic two as well.

For associative unital algebras $A,A'$, an invertible tensor transporter $h(xy)=f(x)g(y)$ has $u=f(1)$ and $v=g(1)$ units. Indeed left multiplication by $u$ and right multiplication by $v$ are bijective, which gives two-sided inverses by applying injectivity to a one-sided inverse. Each transporter is uniquely of the form
$$
 (f,g,h)=(L_u\phi,\ R_v\phi,\ L_u R_v\phi),
 \tag{3}
$$
where $\phi(x)=u^{-1}h(x)v^{-1}$ is a unital algebra isomorphism. These identities also show that a unital multiplication isotopic to an associative one is associative, by directing the transporter toward the associative algebra. [Albert, associative isotopy](https://doi.org/10.2307/1968960)

Every algebra isomorphism $A_b\to A_{b'}$ for data satisfying (2) carries $B$ to $B'$. In fact reduction modulo $\mathfrak m$ carries the unique maximal ideal of the residue square-zero unitization to the corresponding ideal. Write the map as $(r,x)\mapsto(r+\lambda(x),Cx)$ with $C$ invertible and $\lambda(B)\subseteq\mathfrak m$. Comparing the $B'$-components of the products modulo $J$ yields $\lambda(x)y+\lambda(y)x=0\bmod J B$, after canceling $C$. Taking distinct basis vectors gives $\lambda(B)\subseteq J$ since $n\ge2$. Divide the product equation by $s$ in field coordinates. The transported bimaps differ by
$$
 S_\ell(x,y)=\ell(x)y+\ell(y)x
 \tag{4}
$$
for a linear form $\ell$, where $s\ell$ is the scalar component in the common field coordinates. The commutator image of each bimap is its whole image, so these images agree in the common coordinates. Call the image $I$. Equation (4) has image in $I$. Taking $x\in I$ and $y\notin I$ shows $\ell|_I=0$. The induced $\ell$ on $\bar B/I$ is zero as well. Indeed $\dim(\bar B/I)\ge2$ by (2) if the product is nonzero, and by $n\ge2$ if it is zero. In a vector space of dimension at least two, a nonzero linear form admits $x$ with $\ell(x)\ne0$ and a nonzero $y\in\ker\ell$, contradicting $S_\ell=0$. Thus $\lambda=0$. The residual $C$ intertwines the two bimaps. Conversely every such residual intertwiner lifts entrywise to an invertible $C$ over $R$, and every lift extended by the identity on $1$ is an algebra isomorphism.

## Recognition in arbitrary bases

Let $T:R^N\times R^N\to R^N$ be any tensor. Search the two input standard bases for vectors $u,v$ whose contractions $L_u=T(u,-)$ and $R_v=T(-,v)$ are invertible. In every orbit of $\mu_b$ such a vector exists on each side. Modulo $\mathfrak m$ the invertible contractions in a square-zero unitization are precisely the vectors outside its augmentation hyperplane. An invertible change of basis transports the hyperplane, and a standard basis cannot lie in a proper hyperplane. If the search succeeds, define
$$
 x*y=T(R_v^{-1}x,L_u^{-1}y),\qquad e=T(u,v).
 \tag{5}
$$
This is an isotopic unital multiplication on the output module with unit $e$. In the desired orbits it is isomorphic to $A_b$ by (3).

Find the residue augmentation $\bar\epsilon$ of (5) as follows. In a residue square-zero unitization the characteristic polynomial of $L_x$ is $(X-r)^N$ for $r=\bar\epsilon(x)$. Write $N=p^h d$ with $p=\operatorname{char}k$ and $p\nmid d$. The coefficient of $X^{N-p^h}$ is $-d r^{p^h}$, so it recovers $r$ using inverse Frobenius. Compute these values on a basis, extend linearly, and test that $\bar\epsilon(\bar e)=1$ and that the product on its kernel is zero. This validates the entire residue square-zero presentation since $\bar e$ is a unit. Lift a basis of the kernel to $y_1,\ldots,y_n$ over $R$. These vectors and $e$ form an $R$-basis. [Berkowitz, characteristic-polynomial algorithm](https://doi.org/10.1016/0020-0190%2884%2990018-8)

For each $i$ choose $j\ne i$. Read the coefficient $r_i\in R$ of $y_j$ in $y_i*y_j$, and replace $y_i$ by $y_i-r_i e$, using all coefficients from the original basis. In a genuine orbit $r_i$ is the true augmentation of $y_i\bmod J$. To see this, write $y_i=r_i^{\rm true}e+x_i$ in the true augmentation frame. Then modulo $J$ its product with $y_j$ equals $r_i^{\rm true}y_j+r_j^{\rm true}y_i-r_i^{\rm true}r_j^{\rm true}e$. Thus the shifted basis has true augmentation in $J$. Its products then lie in $J$ times its span, since the true products already lie in $J B$ and $J^2=0$. Test this property for the shifted basis. On success divide its product by $s$ to obtain a field bimap $b_1$ on its residue span.

Compute $I=\operatorname{span}\{b_1(x,y)-b_1(y,x)\}$. Reject if $n-\dim I<2$. Solve the linear equations that $b_1-S_\ell$ has image in $I$. In a genuine orbit the true augmentation of the shifted basis gives a solution, because shifting by $-s\ell(x)e$ subtracts (4) from the field product. The solution is unique by the argument after (4). Perform this shift and test (2) on $b_1-S_\ell$. All tests are sufficient because the resulting basis gives exactly a unitization of a bimap satisfying (2), which supplies a basis change to an encoder output. Any NO from the tests excludes the promised orbit family. These constructions return the changes of basis explicitly, including the isotopy in (5). Arbitrary ring orbit canonical representatives can therefore be decoded deterministically into field representatives. Conversely, encode a canonical field representative of the decoded supported tensor, with zero extension to the specified format if necessary. Witnesses move between these representations by (3) and the recovered changes of basis.

## Exact final-digit quotient and orbit sizes

Put $K=(1+\operatorname{Mat}_N(J))^3$. Write a tensor in the anchor fiber as $\mu_0+sD$. An element $(1+sF,1+sG,1+sH)$ acts on $D$ by adding
$$
 \partial(F,G,H)(x,y)
 = H\bar\mu_0(x,y)-\bar\mu_0(Fx,y)-\bar\mu_0(x,Gy),
 \tag{6}
$$
where $\bar\mu_0$ is the residue anchor. This follows from $J^2=0$. Thus all $K$-orbits are translations of a single linear space.

In (5) take $u=v=1$ in the fixed anchor coordinates. This uses two maps congruent to the identity modulo $J$, and its new unit is congruent to $1\bmod J$. Move that unit to $1$ by a basis change congruent to the identity. In the resulting basis the products of $B$ land in $J(R1\oplus B)$, so write them as $s(d(x,y)1+b_0(x,y))$. For every positive index $i$ fix a different positive index $j(i)$. By a common basis change in all three modes, congruent to the identity, one can subtract $S_\ell$ from $b_0$, keeping the unit and $d$ fixed. Choose $\ell(e_i)$ to zero the coefficient of $e_{j(i)}$ in $b_0(e_i,e_{j(i)})$.

These unit and coefficient conditions specify a unique representative of each $K$-orbit, including tensors outside the encoded family. Indeed, if (6) vanishes on the two unit slices, putting $a=F(1)$ and $c=G(1)$ gives $F=H-R_c$, $G=H-L_a$ in the residue anchor. On $B\times B$ the resulting difference is $-S_\ell$, with $\ell(x)$ the scalar component of $Hx$. The coefficient conditions force $\ell=0$. There are $n^3+n^2-n$ free field coordinates in the normal forms, giving $N^3-(n^3+n^2-n)=2N^2-1$ dimensions in each orbit. If $p\nmid N$ one can instead impose $\operatorname{tr}(b_0(x,-))=0$, because $\operatorname{tr}(S_\ell(x,-))=N\ell(x)$.

If two supported labeled $b,b'$ give the same $K$-orbit, the argument for (6) makes their difference $S_\ell$, and (2) then forces $\ell=0$ by their common commutator image. A tensor in the anchor fiber that is ring-isomorphic to $\mu_b$ is $K$-equivalent to $\mu_{b'}$ for some supported $b'$. To see this, first use (5) with the anchored unit and move that output unit to $1$ as above. In this basis all products on $B$ vanish modulo $J$. Under an algebra isomorphism to $A_b$, the scalar coordinate on $B$ therefore lies in $J$, by the same distinct-index comparison modulo $J$ as before. The scalar part of the products is now zero, and shifting the basis by that scalar coordinate gives supported $b'$ by a change congruent to the identity modulo $J$. Two such $b'$ are in the full orbit precisely when they are in the diagonal $\mathrm{GL}_n(k)$-orbit. This proves (1).

## Exact transporter counts and total size

Put $\delta=n-\alpha-\beta-\gamma$. In the decomposition $U_0,V_0,I_b,Z$ from (2), a field diagonal transporter has a block form with invertible blocks $A,B,C,D$ on these summands. The first three are a transporter of supported tensors. The fourth is arbitrary invertible, the maps from $U_0,V_0$ to $I_b\oplus Z$ are arbitrary, and the map $Z\to I_b$ is arbitrary. All other off-diagonal blocks are zero by preservation of the two radicals and image. Thus if $m_{\rm supp}$ is the supported field transporter count, the ring tensor transporter count is
$$
 m_{\rm supp}\,
 |A_b^\times|^2\,|\mathfrak m|^{n^2}\,
 |\mathrm{GL}_{\delta}(k)|\,Q^{(\gamma+\delta)(\alpha+\beta)+\gamma\delta}.
 \tag{7}
$$
Here $|A_b^\times|=|R^\times|\,|R|^n$, since $B$ is nilpotent. The first two factors after $m_{\rm supp}$ count (3) and the lifts of each residual $C$. Counts are zero when the support dimensions differ. For the full original field transporter count, multiply $m_{\rm supp}$ by the analogous independent extension factor
$$
 \prod_{(d_i,r_i)\in\{(a_1,\alpha),(a_2,\beta),(a_3,\gamma)\}}
 |\mathrm{GL}_{d_i-r_i}(k)|\,Q^{r_i(d_i-r_i)} .
$$
The two input extensions preserve their radicals, and the output extension preserves its image. Each ratio gives an exact multiplication-and-division reduction for counts. The free entries and invertible blocks also give uniform fibers over supported transporters.

For a prescribed support rank triple $(\alpha,\beta,\gamma)$, the number of accepted labeled $b$ on $k^n$ equals
$$
 \begin{bmatrix} n\\ n-\alpha-\beta \end{bmatrix}_Q
 \begin{bmatrix} \alpha+\beta\\ \alpha \end{bmatrix}_Q Q^{\alpha\beta}
 \begin{bmatrix} n-\alpha-\beta\\ \gamma \end{bmatrix}_Q
 C_{\alpha,\beta,\gamma}(Q).
 \tag{8}
$$
Choose $L_b\cap R_b$, then two ordered complementary role subspaces modulo it, then the image inside the intersection. The final factor counts fully supported tensors of that format. It is computed by the finite subspace-lattice Möbius inversion formula
$$
 C_{\alpha,\beta,\gamma}(Q)
 = \sum_{i,j,h}
 \begin{bmatrix}\alpha\\i\end{bmatrix}_Q
 \begin{bmatrix}\beta\\j\end{bmatrix}_Q
 \begin{bmatrix}\gamma\\h\end{bmatrix}_Q
 (-1)^{i+j+h}
 Q^{\binom i2+\binom j2+\binom h2+(\alpha-i)(\beta-j)(\gamma-h)} .
$$
The sums run over the three displayed dimensions. Count tensors vanishing on fixed subspaces of the two inputs and fixed annihilators in the dual of the output, then invert on each subspace lattice. Its Möbius value in dimension $r$ is $(-1)^rQ^{\binom r2}$, as follows from the finite binomial identity $\prod_{i=0}^{r-1}(1-XQ^i)$ at $X=1$. Sum (8) over ranks satisfying (2) and multiply by $Q^{2N^2-1}$ for the size of the entire accepted portion of the anchor fiber. The number of terms and the lengths of the integers are polynomial in $N,\log Q$. [Rota, Möbius inversion](https://webhomes.maths.ed.ac.uk/~v1ranick/papers/rota1.pdf)

## Prior results and verification

Grochow–Qiao encode field tensors as algebra multiplication and recover isomorphism information from characteristic subspaces. The final-digit predecessor adds a common socle-level anchor and uses $N^{-1}\operatorname{tr}L_x$ to recover the augmentation, padding to make $N$ invertible. The commutator-image argument above replaces the padding and supplies an explicit recognizer for the whole tensor orbit family. Gerstenhaber's classical first-order theory concerns associative multiplication and one common basis change. Equation (6) acts on all tensors in the fiber with three independent changes. Its explicit quotient, fiber size, and exact counting reductions are the additions proved here. Grochow–Qiao's search/count-to-decision results supply the broader algorithmic context. The proof is in prose and a bounded search found no matching earlier statement. [Grochow–Qiao, TI-completeness](https://doi.org/10.1137/21M1441110) · [Fixed-ring and final-digit predecessor](https://github.com/Dugongue/MathProofs/blob/main/FixedRingFour/CongruenceClass.md) · [Gerstenhaber](https://doi.org/10.2307/1970484) · [Grochow–Qiao, counting and search](https://doi.org/10.4230/LIPIcs.CCC.2021.16)

Run the companion `Algorithms.py` for exact finite controls. It checks the orbit dimensions 17 and 31 for mode sizes 3 and 4 over both $\mathbb F_2$ and $\mathbb F_3$, with 128 normalization checks. At $N=4,p=2$, where the trace argument cannot divide by $N$, it exhausts 12,096 residue-matrix and augmentation-row combinations across $\mathbb Z/4$ and $\mathbb Z/8$ for one supported scalar tensor. Exactly four residual automorphisms survive in each ring, all with zero augmentation row. It also enumerates the 42 labeled rank-$(1,1,1)$ supported products for that example, making the total accepted part of the anchor fiber $43\cdot 2^{31}$, including the zero product orbit.
