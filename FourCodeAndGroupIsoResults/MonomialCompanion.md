# No universal monomial-covariant companion code

Horlemann, Mazumder, Schaller, and Weger ask for a companion code in the section *The Search for New Codes Respecting the Monomial Equivalence* of their 2026 survey. Their desired companion transforms with the inverse coordinate scalars and pairs nonsingularly with the original code. Over each finite field, there are codes with distinct projective columns for which this is impossible. An equivariant list containing at least one nonsingular companion can require exponential size. [Published question](https://arxiv.org/html/2607.12870v2#S6.SS2)

## Exact equivalence with splitting

Write codewords as rows in $E=k^n$, where $k$ is a finite field. A $k_0$-dimensional code $C$ is acted on by monomial matrices $M=DP$, with $D$ diagonal invertible and $P$ a permutation matrix. The requested covariance is
$$
F(CM)=F(C)M^{-\mathsf T}.
$$
Indeed $M^{-\mathsf T}=D^{-1}P$, and the auxiliary left invertible matrix allowed in the survey's generator formula just changes a row basis of $F(C)$. The covariance applies to self-equivalences of a code as well. If $M$ stabilizes $C$, any full-rank generator $G$ can be returned to the identical displayed generator by choosing a left basis change in $GM$. Thus changing basis conventions cannot remove the corresponding condition on the companion subspace.

For a candidate $k_0$-dimensional companion $C'$, invertibility of the displayed matrix $GF(C)^{\mathsf T}$ is exactly nondegeneracy of the ordinary coordinate pairing on $C\times C'$. Equivalently
$$
E=C\oplus (C')^\perp .
$$
In fact the dimensions add to $n$, and the kernel of the pairing on the first argument is $C\cap(C')^\perp$. Moreover, $(C'M^{-\mathsf T})^\perp=(C')^\perp M$. Hence a covariant assignment of companions on the monomial orbit of $C$ exists precisely when $C$ is a direct summand of $E$ for its monomial stabilizer $H$.

For the forward direction the complement of the assigned companion must be $H$-invariant. Conversely let $W$ be an $H$-invariant complement and assign $(WM)^\perp$ to $CM$. To see that the assignment is well-defined, if $CM=CN$, then $MN^{-1}\in H$, so $WM=WN$. The resulting assignment is covariant and its pairings are nonsingular.

When generators of $H$ are given, the existence certificate and a companion can be found by linear algebra. A projection onto $C$ commuting with $H$ has a matrix $\Pi=UG$ acting on row vectors, with $U\in k^{n\times k_0}$. It is precisely a solution of
$$
G U=I_{k_0},\qquad (UG)h=h(UG)\quad \text{for each supplied generator } h .
$$
The first condition makes it the identity on $C$, and the second makes its kernel invariant. Output the orthogonal complement of this kernel. In particular when the stabilizer order is prime to the characteristic, averaging any projection proves existence, and the generator equations compute it without enumerating that stabilizer.

## Explicit counterexamples

For $q=|k|>2$, take the dimension-two evaluation code
$$
C_1=\{(b+at)_{t\in k}: a,b\in k\}\subset k^k.
$$
Its generator columns are $(1,t)^{\mathsf T}$ for $t\in k$. Each is nonzero and no two give the same projective point. The translation group $A=(k,+)$ permutes coordinates and preserves $C_1$. It acts transitively and regularly on the coordinate positions.

The following elementary calculation detects lack of a complement. For a subgroup $B\le A$ of order greater than two, take the linear map
$$
                 N_B=\sum_{a\in B}P_a
$$
on $k^k$, where $P_a$ acts by coordinate translation. On an affine function, its output is zero. Indeed $|B|=0$ in $k$, and $\sum_{a\in B}a=0$. In odd characteristic the latter is pairing $a,-a$. In characteristic two, each coordinate in an $\mathbb F_2$-basis of $B$ occurs equally often, with even count because $|B|>2$. On the entire ambient space, $N_B$ has the constant-one vector in its image. To obtain it, choose a vector with one coefficient $1$ per translation orbit and all others zero. Each orbit is a coset of $B$, where translations act freely and transitively.

If a projection $\Pi:k^k\to C_1$ commutes with $B$, then $\Pi N_B=N_B\Pi=0$. This makes $\Pi$ kill the constant-one vector, which lies in $C_1$, a contradiction. Take $B=A$. Splitting therefore fails for the monomial stabilizer, already for its translation subgroup. Thus over every $k$ of order greater than two the requested universal nondegenerate companion is impossible.

In characteristic two a different block works over every field, including the binary field, while keeping columns projectively distinct. Use the length-four code $C=\{x\in k^4:\sum_i x_i=0\}$. Index the coordinates by $\mathbb F_2^2$ and let its translation group act. Each nonidentity translation is a product of two disjoint swaps. If $P$ denotes one of these permutations, the image of $I+P$ on the ambient space is the two-dimensional space of vectors constant on each swapped pair. This image lies in $C$, and the image of $I+P$ on $C$ has dimension one, since the two pair sums agree. A projection onto $C$ fixes the full two-dimensional image, so it cannot commute with $I+P$. The generator $[I_3\mid\boldsymbol 1]$ has distinct projective columns.

## Exponentially many companions can be necessary

One might ask for an equivariant set of companion subspaces, with the nonsingularity condition imposed on at least one member. This modification still cannot have polynomial list size on all inputs. Fix $q>2$ and take $C_r=C_1^{\oplus r}$ at length $rq$. Its dimension is $2r$, and its block-diagonal generator has pairwise distinct nonzero projective columns. Let $H=A^r$ act by independent translations in the $r$ blocks.

For any nonsingular companion let $K\le H$ be its stabilizer. Coordinate pairing makes the corresponding complement $K$-invariant, so the corresponding projection $\Pi:E\to C_r$ commutes with $K$. The diagonal block $\Pi_{ii}:k^k\to C_1$ is itself a projection, since $\Pi$ is the identity on $C_r$. Since every element of $K$ acts block diagonally, $\Pi_{ii}$ commutes with every translation in the projection $K_i$ of $K$ to its $i$th coordinate. The norm calculation forbids $|K_i|>2$. In odd characteristic every $|K_i|$ is a power of an odd prime, so $K_i=1$. In characteristic two each $|K_i|\le2$, and $K\subseteq\prod_i K_i$ gives $|K|\le2^r$.

Therefore the orbit of any nonsingular companion under $H$ has size at least $q^r$ in odd characteristic or $(q/2)^r$ in characteristic two. Any covariant list for $C_r$ containing a nonsingular companion must contain that whole orbit. This is exponential in the blocklength even for a fixed field, on codes of fixed rate $2/q$. The lower bound in characteristic two is attained for the action of $H$ alone: choose a nonzero $a\in k$, and project each block to the unique affine function agreeing at the two positions $0,a$. The corresponding coordinate-pair companion is stabilized by translations of $\{0,a\}$ and has $q/2$ translates in that block.

With $r$ copies of the length-four parity-check block and $(\mathbb F_2^2)^r$ acting in the corresponding blocks, the same diagonal-block argument forces the stabilizer of every nonsingular companion to be trivial. Thus in characteristic two, over every finite field and at fixed rate $3/4$, distinct-projective-column codes can require a list of at least $4^r$ companions at length $4r$.

## Scope and attribution

The counterexamples resolve the survey's universal companion question under its stated covariance and invertibility requirements. The general relationship between linear code equivalence and graph isomorphism is a separate question. The proof uses elementary modular representation theory. A targeted search found the survey's open question and no earlier resolution of its exact formulation.
