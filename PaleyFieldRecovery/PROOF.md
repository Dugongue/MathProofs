# Recovering finite fields from Paley graphs and their Seidel switches

A deterministic algorithm recognizes ordinary Paley graphs and the entire class of their Seidel switches from raw vertex labels. On acceptance it recovers finite-field operations, a coordinate for every vertex, and the signs for a switch to the Paley model. Its running time on $q$ vertices is $O(q^4)$ arithmetic operations over the prime field, up to polynomial factors in $\log q$ for bit operations and coordinate encoding. The same method handles the signed matrices of Paley tournaments when $q\equiv3\bmod4$. For undirected graphs, this gives a constructive result on the Paley family in Grochow–Urisman Question 1.9 and the ensuing recognition question. The full symmetry-characterized graph questions are broader. [Grochow–Urisman, §1.3](https://arxiv.org/html/2606.26244v2#S1.SS3)

Ponomarenko's constant-dimensional Weisfeiler–Leman theorem already gives polynomial recognition of ordinary Paley graphs by comparison to a template. Here the algorithm starts with the input's adjacency matrix, constructs its field operations, and applies even to an unknown switch of the graph. [Ponomarenko, Theorem 1.2](https://arxiv.org/html/2511.18304v1)

## 1. The signed adjacency and its row code

Let $F=\mathbb F_q$, where $q=p^d$ is odd, and let $\chi:F\to\{0,1,-1\}$ be the quadratic character, with $\chi(0)=0$. Assume temporarily that the vertices really are indexed by $F$ and the input signed matrix is
$$
S'_{xy}=\epsilon_x\epsilon_y\,\chi(x-y),\qquad \epsilon_x\in\{1,-1\}.
$$
For an undirected Paley graph require $q\equiv1\bmod4$, assign sign $+1$ to edges and $-1$ to nonedges off the diagonal, and use zeros on the diagonal. For the usual oriented model use $\chi(x-y)=1$ for the arc $x\to y$ at $q\equiv3\bmod4$. The unknown switch acts by multiplying the same signs into rows and columns.

All the matrices used to recover code coordinates are over $\mathbb F_p$. We analyze them after scalar extension to $F$; row spans, coordinate shortenings and their duals commute with this extension. Write $S$ for the matrix without the switch. Put $m=(q-1)/2$, $h=(p-1)/2$. The entries of $S$ are $(x-y)^m$ in $F$, including the diagonal. The row span $C$ of $S$ over $F$ is the span of evaluations of the polynomials
$$
\left\{x^j : j=\sum_{i=0}^{d-1} j_ip^i,\quad 0\le j_i\le h\right\}.
$$
Indeed, the coefficient $\binom mj$ is nonzero modulo $p$ exactly for those $j$, by expanding $(1+t)^m=\prod_i(1+t^{p^i})^h$. The coefficient functions of the row index are nonzero multiples of distinct powers $x^{m-j}$. These powers are linearly independent as functions on $F$, since their degrees are less than $q$. Consequently the coefficient vectors span all the claimed monomials.

Equivalently, use formal variables $X_0,\ldots,X_{d-1}$ evaluated at the points
$$
\mathbf v(x)=(x,x^p,\ldots,x^{p^{d-1}}).
$$
Then $C$ is the evaluation of the box of polynomials of degree at most $h$ in each $X_i$. The larger box of degrees at most $p-1$ in each $X_i$ evaluates isomorphically onto $F^q$: its monomials evaluate to the distinct powers $x^j$, $0\le j<q$, giving a basis of all functions.

## 2. Recovering inverse coordinates by a shortened code product

For a vertex $a$, shorten the input row code at $a$ by keeping only codewords with value zero at $a$, and retain the zero coordinate. Let $J_a$ be the span of all coordinatewise products of two words in that shortened code. The resulting $J_a$ is unchanged by the unknown switch. Row multiplication by a sign does not affect the span. Column multiplication inserts the vector of signs into each shortened word, and the signs square to $1$ in the products.

Over $F$, use the translated formal variables $Z_i=X_i-a^{p^i}$. In the box of degree at most $h$ per variable the shortened code has the basis of nonconstant monomials in $Z_i$. Its square spans every translated monomial with $0\le \deg_{Z_i}\le2h=p-1$ and total degree at least two. Each such exponent vector is a sum of two nonzero exponent vectors in the smaller box: allocate exponents so that neither slot exceeds $h$ in a coordinate, and put at least one unit of exponent in each slot. Conversely every product lacks constant and linear terms. Therefore under the larger-box interpolation isomorphism, $J_a$ consists precisely of the polynomials with zero value and all first partial derivatives zero at $\mathbf v(a)$. Its codimension is $d+1$.

The vectors that represent the first partial derivative functionals can be read off from the Lagrange basis on the $q$ evaluation points. The polynomial that equals $1$ at $\mathbf v(b)$ and $0$ at every other evaluation point is
$$
L_b(X)=1-\prod_{i=0}^{d-1}(X_i-b^{p^i})^{p-1}.
$$
Its first derivatives at $\mathbf v(a)$ are all zero for $b=a$, because $p$ is odd. For $b\ne a$,
$$
\frac{\partial L_b}{\partial X_i}(\mathbf v(a))
=-(p-1)\frac{(a-b)^{q-1}}{(a-b)^{p^i}}
=(a-b)^{-p^i}.
$$
Thus the subspace of $J_a^\perp$ with coordinate $a$ equal to zero is the span of the $d$ Frobenius powers of the vector whose entries are $(x-a)^{-1}$ off $a$ and zero at $a$. The sign change from $a-x$ to $x-a$ just changes the row basis. To see its prime-field form, express each inverse difference in any basis of $F$ over $\mathbb F_p$. The $d$ rows of prime-field coordinate functions span exactly this Frobenius span over $F$. Indeed the change-of-rows matrix is the Moore matrix of the basis. Its invertibility follows because a nonzero polynomial $\sum_{i=0}^{d-1} c_i t^{p^i}$ of degree at most $p^{d-1}$ cannot vanish on the entire field, and vanishing on the basis would imply such vanishing by $\mathbb F_p$-linearity. The coordinate rows are linearly independent because the inverse differences, with zero at $a$, run through $F$.

This proves a raw reconstruction statement. Compute $J_a^\perp\cap\{w:w_a=0\}$ over $\mathbb F_p$, choose any basis, and read its columns. They give a bijection $R_a$ from the vertices to $\mathbb F_p^d$. On a promised input,
$$
R_a(x)=A_a\bigl((x-a)^{-1}\bigr)\quad(x\ne a),\qquad R_a(a)=0
$$
for an unknown prime-field-linear isomorphism $A_a$. This calculation uses no known vertex coordinates, field multiplication in $F$, or choice of the switch signs.

## 3. Two anchors and field multiplication

Take distinct anchors $a,b$ and solve for $R_a,R_b$ as above. Write $U,W$ for the two prime-field vector spaces, with independent bases. For arbitrary input, reject if either recovered space has the wrong dimension or the columns fail to form a bijection. Define a bijection $\iota:U\to W$ by pairing
$$
R_a(x)-R_a(b)\quad\longmapsto\quad R_b(x)-R_b(a)
$$
and swapping the two output entries associated to $x=a,b$. In particular, this sends $0$ to $0$.

For the analysis translate so that $a=0$, and write $b=t\ne0$ in the unknown field. At $x\notin\{0,t\}$ put $z=x^{-1}-t^{-1}$. Then
$$
(x-t)^{-1}+t^{-1}=-t^{-2}z^{-1}.
$$
For $x=t$ the corrected pair is $0\mapsto0$, and for $x=0$ it gives $A_a(-t^{-1})\mapsto A_b(t^{-1})$, as the same formula requires. Thus for all nonzero $z$, the computed bijection has the form
$$
\iota(A_a(z))=A_b(-t^{-2}z^{-1}).
$$

Choose any nonzero $e\in U$ as a candidate multiplicative unit. Define $s(0)=0,\ s(e)=e$, and for $u\notin\{0,e\}$ put
$$
s(u)=u-\iota^{-1}\bigl(\iota(u)+\iota(e-u)\bigr).
$$
In the promised model write $u=A_a(z)$, $e=A_a(c)$. The identity
$$
z-\bigl(z^{-1}+(c-z)^{-1}\bigr)^{-1}=z^2/c
$$
shows $s(A_a(z))=A_a(z^2/c)$. The extra factor $-t^{-2}$ in the representation of $\iota$ cancels. The exceptional cases $z=0,c$ agree by construction. This is the field case of Hua's inverse identity. Polarization now gives a multiplication
$$
u*v=\bigl(s(u+v)-s(u)-s(v)\bigr)/2.
$$
On the promised model it is field multiplication in the prime-field-linear coordinates $A_a(z)\mapsto z/c$, with identity $e$. [Goldstein–Guralnick–Small–Zelmanov, Lemma 1.2](https://msp.org/pjm/2006/227-2/pjm-v227-n2-p03-p.pdf)

For soundness on arbitrary graphs, construct this multiplication table and verify the field axioms, using the already known additive structure of $U$. If the checks pass, label $x\ne a$ by the multiplicative inverse of $R_a(x)$ in the recovered field, and label $a$ by $0$. This map is a bijection, and on a true input it gives the original coordinates up to affine change and the final field isomorphism: in the analysis the new label is $c(x-a)$.

## 4. Recognition, witnesses, and complexity

For ordinary Paley recognition, compute the quadratic character of all differences in the recovered field. Check whether it agrees with $S'$ everywhere off-diagonal, allowing a common sign. A nonsquare field multiplier changes that common sign, so either outcome gives a verified Paley labeling. For switch recognition, check whether the two matrices differ by conjugation by a diagonal matrix of signs, again allowing the common sign. For each common sign determine the switching signs uniquely up to simultaneous negation by setting the first sign to $1$ and using its row. Check all pairs. These verifications give soundness. The preceding construction gives completeness, including for arbitrarily switched inputs. For the ordinary recognition test, the same reconstructed field still works on an unswitched input: the final label differs from its unknown Paley coordinates only by translation and a nonzero field multiplier.

Computing $p,d$ from the displayed order $q$ takes polynomial time by trial division, and the value of $q\bmod4$ determines the symmetric or skew-symmetric model. On $q$ coordinates a basis of the original row code takes $O(q^3)$ field arithmetic. Each of two shortened spaces yields at most $q^2$ pairwise coordinatewise products of basis vectors. Maintaining an echelon basis as these length-$q$ vectors arrive costs $O(q^4)$ field arithmetic, keeping $O(q^2)$ field elements. The table verification needs at most $O(q^3)$ lookups and vector operations. Arithmetic in $\mathbb F_p$ and conversion between the $d$-coordinate representations and table indices cost polynomial factors in $\log q$. Explicit coordinates in a standard field presentation can be obtained by choosing a root in the recovered field of a fixed irreducible polynomial of degree $d$. Trial enumeration of the at most $q$ candidate monic polynomials and a Frobenius-gcd irreducibility test suffice to find such a polynomial. The recovered labels also yield actual graph isomorphisms between two positive ordinary Paley inputs.

The same procedure recognizes the extended Paley switching class on $q+1$ vertices in polynomial time. In its standard model, add one point with sign $+1$ to each of the other vertices. For each candidate added point, normalize the incident signs to $+1$ by a switch, delete that point and run the ordinary Paley test. One candidate succeeds exactly when the extended switching class is present. The accepted candidate supplies both the coordinates and the switch. For undirected graphs this uses the standard Seidel equivalence, with two-graph triples given by the products of signs along triangles.


## 5. An elementary transporter formula

The reconstruction also determines all vertex permutations carrying one Paley signing to another, even when switches are allowed. It gives the usual automorphism description without additional character-sum estimates. Let $F$ be the same standard field on both sides, and let $\pi$ be a switching isomorphism from the ordinary Paley signing on $F$ to itself. Since the shortened square is switch invariant, $\pi$ permutes the recovered coordinate spaces according to their anchors. Use any anchors $a,b$ on the source and $\pi(a),\pi(b)$ on the target. Transport the two bases by permutation and use the same coordinate vector $e$ for the unit. All arrays used to define $\iota$, the field operations, and the recovered vertex labeling then agree under transport. In particular the same recovered field is identified with $F$ in two ways. Both are field isomorphisms, so their composition is a Frobenius power. The source and target label formulas of Section 3 now give
$$
\pi(x)=u x^{p^j}+v
$$
for some $u\in F^\times$ and $v\in F$. Conversely, such a map with square $u$ preserves every sign. A nonsquare $u$ reverses every sign. Reversing all off-diagonal signs cannot be a switch on three or more vertices, because the product of the three switch ratios on a triangle must be $1$. Thus the ordinary Paley signing and its switching class have exactly the affine semilinear permutations with square multiplier. The ordinary automorphism statement is classical, as discussed by Ponomarenko. [Ponomarenko, Introduction](https://arxiv.org/html/2511.18304v1#S1)

For the extended undirected signing, use points $x\in\mathbb P^1(F)$ with homogeneous representatives $v_x=(x,1)$ and $v_{\infty}=(1,0)$. The sign at a pair is $\chi(\det(v_x,v_y))$. For $G\in\operatorname{GL}_2(F)$, write $Gv_x=\lambda_x v_{Gx}$. The projective action changes the sign at $x,y$ by $\chi(\det G)\chi(\lambda_x)\chi(\lambda_y)$. Thus square-determinant projectivities and field automorphisms preserve the switching class. Determinant-one projectivities are transitive on the points, as seen using translations and the map $x\mapsto-1/x$. Compose an arbitrary switching automorphism with such a projectivity so that it fixes $\infty$. The incident signs at $\infty$ are all $+1$, so the switch multipliers must all be equal. The restriction is an ordinary Paley automorphism, already proved affine semilinear with square multiplier, and hence induced by a square-determinant projectivity and a field automorphism. This proves the transporter formula for the extended class as well. It also shows completeness of the extended recognition test using any one chosen vertex as the deletion point, giving the same $O(q^4)$ arithmetic bound as for ordinary recognition. [Mathon, definition of the Paley conference matrix](https://doi.org/10.4153/CJM-1978-029-1)
