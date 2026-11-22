# Tensor Isomorphism for algebraic groups given by equations

## Effective comparison over a coefficient ring

Let $R$ be a commutative ring and $G=\prod_{i=1}^{a}\mathrm{GL}_{n_i,R}$. Present a closed subgroup scheme $H$ of $G$ in matrix entries $X_i$ and inverse matrix entries $Y_i$. For the polynomial ring in these entries let $I$ be the inverse image of the ideal of $H$. Thus $I$ includes the entries of $X_iY_i-I_{n_i}$ and $Y_iX_i-I_{n_i}$. Assume a finite generating list for $I$ and a monic Gröbner basis for $I$ with respect to a total-degree-compatible monomial order are supplied. Here monic means that the leading coefficient of each basis polynomial is 1.

**Theorem.** Comparison of any explicitly given tensor network under the restriction that its basis changes belong to $H$ reduces to ordinary free three-tensor isomorphism. The construction also applies to tensor networks with marked, explicitly generated relation submodules. One output pair tests the comparison over every commutative $R$-algebra $S$. If $D$ is the maximum of two and the largest degree of the supplied ideal generators, $M=2\sum_i n_i^2$, and
$$
N=\binom{M+D}{D},
$$
then all construction costs are polynomial in the input description and $N$ in the coefficient-operation model. The side length contributed by enforcing membership in $H$ is $O(N)$ before adding the existing network ranks. In particular the reduction is polynomial at each fixed $D$, without a bound on the number of factors or labels. Over $\mathbb Z$, $\mathbb Q$, and the usual explicitly encoded finite quotients of $\mathbb Z$, the construction also takes polynomial bit time in the stated sizes.

The restriction on the equation format gives an effective version of the Chevalley subspace construction. The group scheme may be nonreduced, and the conclusion includes nonflat scalar extensions. The result uses the linear-side compiler for variable labelled networks to keep the coefficient window in its ordinary polynomial basis. A previous MathProofs construction realized affine group schemes and their torsors over fields as tensor transporter schemes using a long tensor word. [Chevalley's stabilizer theorem, SGA 3, Exposé VIB, §11](https://grothendiecksga.com/read/sga3/en/VIB-11.html) · [Earlier tensor-torsor realization](https://github.com/Dugongue/MathProofs/blob/b3bde958f05b17ea912394edb1edd18852b9c85d/TensorIsomorphismAndAlgebraicCrossovers/Rings.md) · [Linear-side compiler](https://github.com/Dugongue/MathProofs/blob/b3bde958f05b17ea912394edb1edd18852b9c85d/HigherOrderUniversality/RingUniversality.md)

### A finite stable window

Write $P=R[X_i,Y_i:1\le i\le a]$ and $E=P_{\le D}$, free on the $N$ monomials of degree at most $D$. Right translation by $g=(g_i)\in G(S)$ acts on this window by
$$
(\rho(g)f)(X_i,Y_i)=f(X_i g_i,g_i^{-1}Y_i).
$$
The rule preserves total degree and descends to right translation on the subscheme $G_S$. With this pullback convention $\rho(g)\rho(h)=\rho(gh)$.

Let $W=I\cap E$. Polynomial division by the monic basis gives a normal-form map $E\to E^{\mathrm{std}}$, where $E^{\mathrm{std}}$ is the span of monomials of degree at most $D$ not divisible by any leading monomial of the basis. This map is the identity on that span. For every nonstandard monomial $m$ of degree at most $D$, put $w_m=m-\mathrm{NF}(m)$. These $w_m$ give an explicit free basis of $W$, with $E=W\oplus E^{\mathrm{std}}$. Indeed every $e\in E$ is congruent to its normal form, and a nonzero normal form cannot lie in $I$. More strongly,
$$
I_S\cap E_S = \operatorname{span}_S\{w_m\}.
$$
To see this without flatness, the full polynomial quotient has the free standard-monomial basis over $R$ by the monic division algorithm. Tensoring the quotient presentation is right exact and identifies its base change with $P_S/I_S$; the standard-monomial basis therefore remains a basis there. Restricting this description to $E_S$ gives the displayed equality.

If $g\in H(S)$, right translation and its inverse restrict to automorphisms of $H_S$. Consequently $\rho(g)$ preserves $I_S\cap E_S$ onto itself. Conversely suppose $\rho(g)$ transports $W_S$ onto itself. Every supplied generator $f$ belongs to $W_S$. Evaluating $\rho(g)f\in I_S$ at $X_i=Y_i=I_{n_i}$, which represents the identity in $H(S)$, gives $f(g_i,g_i^{-1})=0$. These generators cut out $H$, so $g\in H(S)$. Therefore $H(S)$ is exactly the stabilizer of this one marked submodule within the indicated $G(S)$-action, functorially in $S$.

### The network computing the action

Use the original $a$ basis-change sorts. In degree one the row variables of $X_i$ are $n_i$ labelled copies of the standard $n_i$-dimensional module, and the column variables of $Y_i$ are $n_i$ labelled copies of its dual. Mark their inclusions into the degree-one space $P_1$, which ties their action to the given basis changes by the displayed translation formula.

On the monomial basis of $E$ give it the multiplication of the truncated polynomial algebra
$$
P/( \text{monomials of degree greater than }D ).
$$
Its table has entries zero and one. Include the map $P_1\to E$, and the multiplication $E\otimes E\to E$. An invertible map preserving multiplication preserves the unit. Its action on $P_1$ determines its action on the algebra, since all monomials are products of degree-one elements. Conversely the specified linear action on $P_1$ extends to the required action on this quotient, since linear substitution preserves the ideal by degree. Hence these two records replace all the homogeneous inclusion records. Mark $W$ by its basis inclusion in $E$.

Use the same network on the two sides, with the same equation data, and include the moving-tensor and relation records. Every $H(S)$-transporter extends over the new markers. Any transporter of the augmented network induces a $g\in H(S)$ by the window test and transports the original records. The $O(M)$ degree-one inclusion markers, each of rank cost $O(M)$, contribute $O(M^2)$ in total. With $D\ge2$ this is $O(N)$; the remaining new markers contribute $O(N)$ directly. Applying the variable-label compiler proves the claimed side bound. If the original records have higher arity, first apply its product ladder to those records.

The normal-form calculation can be done by a single pass over the $N$ monomials in increasing order. For a nonstandard monomial choose a leading term of a basis polynomial dividing it, replace the monomial by the corresponding multiple of the negative lower terms, and use previously calculated normal forms. Total-degree compatibility keeps all new monomials within the same window. This uses polynomially many operations. In the integer and rational bit models the resulting coefficient vectors are obtained by a unit-triangular system of size $N$ with input-size coefficients. After clearing denominators in the input globally, coefficients of each solution are sums of products of at most $N$ input coefficients with at most $N^{O(N)}$ terms, so their bit lengths are polynomial. The remaining table operations copy coordinates. This establishes the time claim.

### Two examples of the scope

For a supplied closed graph of a representation $H_0\to\mathrm{GL}(V)$, take $H$ to be that graph in the product of the chosen ambient groups. Add a vector record in $V$. This compares the $H_0$-orbits of two given vectors using the same coefficients after any scalar extension, with the bound determined by the graph's equations and normal-form presentation. It also handles any number of linear maps and tensor records with these representation actions.

For an infinitesimal example over $\mathbb F_p$, one can take $H=\alpha_p$ inside $\mathrm{GL}_2$ as upper-unitriangular matrices with upper-right entry $t$ satisfying $t^p=0$. A monic degree-compatible basis writes every other entry, including the inverse matrix, as a constant or $-t$, and includes $t^p$. Thus the augmented comparison allows exactly the $\alpha_p(S)$-action for every $S$, including a nontrivial $t$ over $\mathbb F_p[\epsilon]/(\epsilon^2)$ and only the identity over fields. This certifies that the construction uses the schematic stabilizer rather than just its geometric points.

## Linear-size transporters for finite free torsors

There is a smaller direct construction when a finite group scheme is supplied by its Hopf table. Let $B$ be a finite free commutative Hopf algebra of rank $r$ over $R$, and let $C,D$ be finite free commutative right $B$-comodule algebras, with multiplication and coaction tables. Isomorphisms of the comodule algebras reduce to ordinary three-tensor isomorphism on sides $O(r+\operatorname{rank} C+\operatorname{rank} D)$, simultaneously over all commutative test algebras. For right torsors $X,Y$ under $H=\operatorname{Spec} B$, take their coordinate algebras. The resulting pair tests equivariant isomorphism $X\simeq Y$. In particular, for $X=H$, comparison with $Y$ tests whether $Y(S)$ is nonempty.

The network has the multiplication $C\otimes C\to C$ and the coaction $C\to C\otimes B$, and analogously for $D$. Pin $B$ pointwise by a vector equal to its first basis vector and the endomorphism shifting each basis vector to the next, with the last sent to zero. These two records force the identity on $B$ over every test algebra because the iterated shifts give the whole basis. An invertible map preserving multiplication preserves the unit, and the coaction equality with fixed $B$ expresses equivariance. There are a constant number of records, all of order at most three. The linear-side ring compiler proves the bound. Equivariant maps from the trivial right torsor $H_S$ to $Y_S$ are determined by the image of the identity, and translation by any such point identifies the torsors. This gives the final assertion without a geometric-point or separability hypothesis. [Torsors, Stacks Project](https://stacks.math.columbia.edu/tag/0497)

Both constructions have written proofs. The monic-window result uses an explicitly supplied normal-form presentation. It places no complexity bound on computing a Gröbner basis from an arbitrary list of group equations.
