# The smallest extension for tensor isomorphism is NP-complete

Fix a finite field $F=\mathbb F_q$. This informal proof gives a polynomial-time recognizable family of raw balanced 3-tensors over $F$. All tensors of the same format in the family are isomorphic over $\overline F$ and have scalar matrix-mode pair adjoints over $\overline F$ with the slice labels fixed. On this family:

1. For a specified positive integer $d$ in binary, ordinary tensor isomorphism over $\mathbb F_{q^d}$ is decidable in deterministic polynomial time directly from the base-field tensors and $d$.
2. Given a bound $D$ in binary, deciding whether ordinary tensor isomorphism holds over $\mathbb F_{q^d}$ for some $1\le d\le D$ is NP-complete under deterministic polynomial-time many-one reductions.
3. Given $L$ in binary, counting the divisors $d$ of $L$ for which isomorphism holds over $\mathbb F_{q^d}$ is #P-complete under polynomial-time Turing reductions. The reduction from counting vertex covers is parsimonious and outputs a common splitting degree.
4. At side length $n=m+4$, the largest possible minimum extension degree over pairs in the family is $\exp((1+o(1))\sqrt{2m\log(2m)})$. With one specified split tensor it is exactly Landau's function $g(m)$.

The exponent is the extension degree, and the isomorphisms here are ordinary tensor isomorphisms. The distinction between testing a given degree and selecting a short one survives even when the degree test uses small integers and no extension-field output.

## 1. Attach an étale algebra without a tensor direct sum

Let $A$ be a finite étale $F$-algebra of dimension $m\ge1$, meaning a product of finite field extensions. Put $V=F^2\otimes F^2$ and choose
$$
 e=e_1\otimes f_1+e_2\otimes f_2\in V,\qquad
 \epsilon(e_1\otimes f_1)=1
$$
with $\epsilon$ zero on the other three elementary basis vectors. For a matrix $B\in \operatorname{Mat}_2(F)$ put $\theta(B)=B_{12}$. Define a square slice map $M_A:A\oplus\operatorname{Mat}_2(F)\to\operatorname{Hom}_F(A\oplus V,A\oplus V)$ by
$$
  M_A(a,B)=
   \begin{pmatrix}
    L_a& \theta(B)1_A\epsilon\\
    \theta(B)e\,\operatorname{Tr}_{A/F}& B\otimes I_2
   \end{pmatrix},
 \qquad L_a(x)=ax .
$$
All three modes have dimension $m+4$. We take the entire ordinary isomorphism closure of these tensors as the raw input family.

This tensor is concise. The slice map is injective because its top and bottom diagonal blocks detect $a$ and $B$. The two slices at $(1_A,0)$ and $(0,I_2)$ jointly have zero common kernel and images spanning the output. These facts remain true after every extension.

Over $\overline F$, any slice with $B\ne0$ has rank at least two from the bottom block alone. For $B=0$, the slice is multiplication by $a$ on the split étale algebra. Such a slice has rank one exactly when $a$ is supported on a single primitive idempotent. Thus the whole geometric set of rank-one label lines is a finite intrinsic frame whose $q$-Frobenius orbits have the field-factor degrees of $A$.

The pair-adjoint algebra comprises pairs $(P,Q)$ with $QM_A(a,B)=M_A(a,B)P$ for all labels. This algebra is scalar even after extending to $\overline F$. The two slices at $(1_A,0)$ and $(0,I_2)$ are complementary projections and sum to the identity. Their equations make $P=Q$ block diagonal. The top block commutes with every $L_a$ and is itself $L_c$, since a linear map commuting with left multiplication sends every $a$ to $aP(1_A)$. The bottom block commutes with every $B\otimes I_2$ and is $I_2\otimes J$ for some $2\times2$ matrix $J$, as seen using the matrix units. The mixed equations at $B=E_{12}$ give
$$
 c\,\epsilon=1_A\epsilon(I_2\otimes J),\qquad
 (I_2\otimes J)e\,\operatorname{Tr}_{A/F}
       =e\,\operatorname{Tr}_{A/F}L_c.
$$
Evaluate the first on a vector on which $\epsilon$ is one, giving $c=\lambda 1_A$. The étale trace is a nonzero functional over every extension because over $\overline F$ it sums all the split coordinates. The second equation now gives $(I_2\otimes J)e=\lambda e$. The two elementary first-factor coordinates in $e$ force $J=\lambda I_2$. The centroid is scalar as well, because its last two maps are a pair adjoint and the label slice map is injective. In particular the tensor has no nontrivial direct-sum decomposition even over $\overline F$.

## 2. Exact extension spectrum

If $K/F$ is finite, an isomorphism $M_A\simeq_K M_{A'}$ sends the intrinsic rank-one lines to one another, equivariantly for the Galois action over $K$. Its existence therefore implies equality of the cycle types of the two $K$-Frobenius permutations. These are precisely the lists of field-factor degrees of $A\otimes_F K$ and $A'\otimes_F K$. Conversely a $K$-algebra isomorphism of the latter algebras preserves the unit and trace, and hence gives a tensor isomorphism on the three $A$-blocks with identity on the auxiliary blocks. This proves the extension criterion. In particular all $m+4$ examples become isomorphic over $\overline F$, since any rank-$m$ étale algebra splits there. [Finite étale algebras and permutation representations](https://people.math.harvard.edu/~mmwood/Publications/ArithStats.pdf)

A degree-$s$ orbit of the original Frobenius breaks into $\gcd(s,d)$ orbits of degree $s/\gcd(s,d)$ for the $d$-th power. Once the original cycle lists are computed, this tests extension isomorphism in time polynomial in $m+\log(1+d)$. Alternatively use fixed-point counts of permutation powers. For any permutation with $a_s$ cycles of size $s$, its $t$-th power has $\sum_{s\mid t}s a_s$ fixed points. All these counts determine $a_s$ by increasing values of $s$ and subtracting the contributions of proper divisors. Therefore two permutations have the same cycle type after their $d$-th powers exactly when their fixed-point counts agree at every multiple of $d$.

## 3. Recover the family from raw tensors

The following algorithm also gives a polynomial-time language of allowed raw inputs. Its algebraic calculations use only $F$. Let $p=\operatorname{char}F$, let $U,X,Y$ be the raw modes, and require that their common dimension be $m+4$, with $m\ge1$. Check injectivity of the raw slice map $M:U\to\operatorname{Hom}(X,Y)$.

Form the span of products of $2\times2$ minors of $M(u)$ with monomials of total degree $p-2$. Compute the subspace of linear forms whose $p$-th powers belong to that span. This uses the independent pure power monomials and inverse scalar Frobenius on $F$. Its common kernel $H$ contains every geometric rank-one label. For a true template the span contains the $p$-th power of each of the four quotient matrix-entry coordinates: two repeated copies in $B\otimes I_2$ supply a minor equal up to sign to the square of each entry, and multiplying gives the desired $p$-th powers. In a split basis the rank-one lines span exactly $A$, so $H=A$ for the template. Require $\dim H=m$.

To recover the frame algebra on $H$, view quadrics as paired with symmetric matrices via their upper-triangular entries so that $vv^{\mathsf T}$ pairs with evaluation at $v$. Let $\mathcal D$ be the annihilator of the restricted minor span, and set
$$
 {\cal A}=\{a\in\operatorname{End}_F(H): a\mathcal D\subseteq\mathcal D\}.
$$
Both spaces are computed by linear equations. Test $\dim\mathcal D=\dim {\cal A}=m$, commutativity of ${\cal A}$, and injectivity of its $q$-Frobenius map. On a genuine template the minors on $H$ span the split products of distinct coordinates, so the annihilator spans the diagonal matrices and its left idealizer is the diagonal algebra in that split basis. Conversely the tests give an $m$-dimensional finite étale algebra acting faithfully on an $m$-dimensional space. Over $\overline F$ it has $m$ one-dimensional primitive eigenspaces. The part of $\mathcal D$ at any one of these primitive idempotents is supported in one image line and is symmetric, so has dimension at most one. All $m$ parts together have dimension $m$, so each is the symmetric square line of the corresponding eigenspace. The minor equations on $H$ therefore hold exactly on the individual frame lines. All earlier calculations commute with conjugation of tensor coordinates by Cauchy–Binet, coordinate substitution, and the congruence action on $\mathcal D$.

The rational primitive idempotents of ${\cal A}$ are computed by simultaneous eigenspace refinement on the $q$-fixed subalgebra acting on itself. This subalgebra is $F^r$ for $r$ field factors. Iterate over a basis of the subalgebra and split each space by its possible eigenvalues in $F$. The final spaces are lines spanned by these idempotents, each normalized by the equation $e^2=e$. Their factor dimensions give the original Frobenius cycle lengths immediately.

For exact membership, compute $K_X=\bigcap_{v\in H}\ker M(v)$ and $Y_0=\sum_{v\in H}\operatorname{im}M(v)$. Require $\dim K_X=4$, $\dim Y_0=m$. Hence the $m$ geometric rank-one labels have independent input coordinate functionals and independent output lines. Enumerate identifications of $U/H,K_X,Y/Y_0$ with the standard quotient spaces $\operatorname{Mat}_2(F),V,V$. These spaces are all four-dimensional and $q$ is fixed. Retain only charts for which the induced bottom pencil is $B\otimes I_2$. Choose any raw lift $b$ of $I_2$. The subspaces
$$
 X_0=M(b)^{-1}(Y_0),\qquad
 Y_1=M(b)K_X
$$
complement $K_X$ and $Y_0$ and are independent of the lift. They are the standard complements in a true chart. Identify $Y_1$ with $V$ via its quotient.

Choose $v_0\in H$ whose projection to each rational primitive factor of ${\cal A}$ acting on $H$ is nonzero. Such a vector is produced by adding any one nonzero vector in each factor image. Since the action on each factor has rank one over its field, the vector has all geometric coordinates nonzero. Set $A_0=M(v_0)|_{X_0}:X_0\to Y_0$, which is invertible by independence of the frame. The normalized operators $A_0^{-1}M(H)|_{X_0}$ form a regular étale algebra $\mathcal B$ on $X_0$, since they are all coordinate diagonals over $\overline F$. Let $\iota_X$ denote this action and $\iota_Y(a)=A_0\iota_X(a)A_0^{-1}$ its counterpart on $Y_0$.

For any raw lifted quotient slice, remove its top diagonal component by subtracting an element of $H$. Compute that component over $F$ by normalizing the top block through $A_0^{-1}$, then projecting onto $\mathcal B$ by the matrix-trace pairing. The restricted pairing $(a,b)\mapsto\operatorname{tr}(\iota_X(a)\iota_X(b))$ is nondegenerate because over $\overline F$ it is the dot product of coordinate diagonals. In the same split basis the projection takes a matrix to its diagonal, so the choice of raw lift is irrelevant. Check that every quotient lift now has zero top block. Also check that the mixed blocks are $\theta(B)u_Y\epsilon$ and $\theta(B)e\ell_X$ for a common $u_Y\in Y_0$ and $\ell_X:X_0\to F$, which are read from the lift with $B=E_{12}$.

For the output top-mode chart require that $a\mapsto\iota_Y(a)u_Y$ is invertible. For the input top-mode chart solve for $u_X$ with
$$
 \ell_X(\iota_X(a)u_X)=\operatorname{Tr}_{\mathcal B/F}(a)
       \quad\text{for all }a\in\mathcal B,
$$
and require that $a\mapsto\iota_X(a)u_X$ is invertible. In the split frame these conditions amount to $u_Y$ and $\ell_X$ being nonzero on each corresponding coordinate. The solutions, if they pass, are forced coordinatewise by the nondegenerate diagonal trace form, and the linear solve takes place over $F$. These charts turn the two mixed maps into the displayed template. The maps from $H$ between these charts are exactly the $\mathcal B$-multiplication maps: in split coordinates they are the full diagonal space, and the charts identify the corresponding coordinate lines on both sides because their actions were identified through $A_0$. Obtain the label isomorphism explicitly by evaluating these normalized multiplication maps at the unit. Test the full template by matrix equality on a basis. A true tensor has an accepted quotient chart, and the rest of the construction succeeds in that chart by its standard-coordinate description. Conversely an accepted chart is an exact certificate. All loops, including the bounded-degree minor calculation at fixed $p$, have polynomial size in the raw input length.

## 4. Encode Vertex Cover in the extension degree

Let $G$ be a graph on $N$ vertices. Assign each vertex $i$ a different prime $p_i$. For the edge $ij$, make two cycle multisets of equal size $2p_i p_j$.

* In the first put $p_i p_j$ one-cycles and one $p_i p_j$-cycle.
* In the second put $p_j$ cycles of length $p_i$ and $p_i$ cycles of length $p_j$.

Use their disjoint unions over the edges, with a common extra one-cycle so that the format is always positive. For any integer $t\ge1$ the difference between the numbers of fixed points of the $t$-th powers contributed by one edge is
$$
 p_i p_j\bigl(1-\mathbf 1_{p_i\mid t}\bigr)
           \bigl(1-\mathbf 1_{p_j\mid t}\bigr).
$$
Every summand is nonnegative. The full difference at $t=d$ vanishes precisely when $\{i:p_i\mid d\}$ is a vertex cover. In that case it also vanishes at every multiple of $d$, so the cycle types of the $d$-th powers agree by Section 2. If it fails, even the two numbers of rational rank-one label lines disagree over $\mathbb F_{q^d}$. This realizes the admissible degree set as exactly the one specified by the graph's vertex-cover condition.

To encode an upper bound $k$ on the size of the cover, we need near-equal primes of polynomial size. For sufficiently large $N$, the interval $[N^4,2N^4]$ has more than $N^2$ primes by the prime number theorem. Partition it into $N$ intervals of length $N^3$. Some interval contains $N$ primes. A deterministic ordinary sieve finds them in polynomial time in $N$. For the finitely many smaller sizes use a fixed larger constant times $N^4$. Let $P=\min_i p_i$, $Q=\max_i p_i$. The construction gives $Q/P\le 1+1/N$ and $P>e$. Set $D=Q^k$ and restrict $0\le k\le N$, handling trivial bounds directly. A cover of size at most $k$ yields an admissible $d=\prod_{i\text{ in cover}}p_i\le D$. Conversely an admissible $d\le D$ cannot be divisible by $k+1$ distinct chosen primes, because
$$
 P^{k+1}> (1+1/N)^k P^k\ge Q^k .
$$
The chosen prime divisors of $d$ give a cover of size at most $k$.

Realize each length-$a$ cycle as a copy of $\mathbb F_{q^a}$ and build the two raw tensors from the products. The chosen primes are polynomial in $N$, so the tensor dimensions and the dense outputs are polynomial. At fixed characteristic the irreducible polynomials for the field factors can be constructed deterministically in time polynomial in the degree. The bit length of $D$ is polynomial. For membership in NP on this language, give $d$ in binary and run the raw recognition and degree test. This proves NP-completeness on the recognizable family and NP-hardness for the unrestricted extension-degree problem. [Karp's Vertex Cover reduction](https://people.seas.harvard.edu/~madhusudan/courses/Fall2020/Lectures/L19-after.pdf) · [Shoup on constructing irreducible polynomials](https://www.shoup.net/papers/detirred.pdf)

For the counting version put $L=\prod_i p_i$, a common splitting degree for these two étale algebras. There is exactly one field $\mathbb F_{q^d}$ inside $\mathbb F_{q^L}$ for each divisor $d\mid L$. The squarefree divisors of $L$ correspond bijectively to vertex subsets, and the accepted divisors correspond exactly to vertex covers. This reduction is parsimonious. Membership in #P follows by guessing one fixed-width binary encoding of $d$, checking positivity, $d\mid L$, and the raw degree test. [Provan and Ball's counting result](https://epubs.siam.org/doi/abs/10.1137/0212053)

## 5. Sharp extremal extension obstruction

A degree equal to the least common multiple of all the parts of the two cycle lists is always sufficient. Taken together the lists have total size $2m$, so this bounds the minimal degree by the maximal order $g(2m)$ of a permutation on $2m$ points. Landau's asymptotic says $\log g(t)\sim \sqrt{t\log t}$. If the first tensor is split, the second must split too, so its exact minimal degree is the order of its permutation. Maximizing gives precisely $g(m)$. [Nicolas on Landau's function](https://oda.mfo.de/bitstream/handle/mfo/852/full-text.pdf?isAllowed=y&sequence=1)

For the unrestricted pair within this family, fix $\eta>0$, take $x=(1-\eta)\sqrt{2m\log(2m)}$, and consider all primes up to $x$. Their sum is asymptotic to $x^2/(2\log x)$ by partial summation from the prime number theorem. For fixed $0<\eta<1$ and all sufficiently large $m$, this sum is less than $2m-2x$. Divide the primes into two disjoint lists by placing each in the currently smaller partial sum. The final sums differ by at most $x$. Thus each fits within $m$, and we complete the two partitions of $m$ with ones. A nonsplit prime cycle on one side can equal no cycle on the opposite side, since the prime sizes on the two sides are disjoint and powering prime cycles gives either the original prime cycle or fixed points. Consequently an admissible extension degree must be divisible by every prime up to $x$, and their product is the exact minimum. Its logarithm is asymptotic to $x$ by the prime number theorem. Letting $\eta$ tend to zero proves the matching lower asymptotic.

## Scope and provenance

Finite étale descent and fixed-point counts of permutation powers are classical. The construction uses the earlier nonsplit-frame recovery to put those counts into raw tensors with scalar pair adjoints and then encodes Vertex Cover in the minimum field extension. The closest cycle-type result searches a generated permutation group for an element of a requested cycle type. Here the same bounded exponent acts on two given permutations. Ordinary TI over any specified extension is easy on the displayed family. Exact controls compared the extension criterion on all 32,768 pairs of a five-vertex graph and a divisor of the product of five assigned primes. Separate finite linear algebra checked the pair-adjoint dimension and rational rank-one lines on ten split and nonsplit fixtures over $\mathbb F_2$ and $\mathbb F_3$. Publication priority for the tensor extension-degree results is unverified. [Cycle types in permutation groups with few generators](https://arxiv.org/abs/2503.02864)
