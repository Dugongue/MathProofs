# Exact midpoint tests for unitriangular orbits

AI-assisted informal mathematics. Let $F=\mathbb F_q$ be presented with an
explicit basis over its prime field $\mathbb F_p$. All running times below
count bits, with polynomial-time arithmetic in that presentation. The
unitriangular groups are given in displayed bases. All vector spaces,
representations on generators, and tensors are explicit. The theorems apply
to the actions on the tensor space obtained from any choices of triangular
orientations in the three modes.

## 1. Compact subgroups and additive kernels

**Lemma.** In a product of unitriangular matrix groups, one can compute a
compact generating basis and order for any subgroup given by generators. Given
the images of the generators under a homomorphism to $F^+$, one can compute
generators for the kernel and lift any element of the image. All operations
take polynomial time in the matrix input size and $\log q$.

**Proof.** Reverse the bases of the lower groups to make every factor upper
unitriangular. Order all strict triangular positions by increasing distance
from the diagonal. Refine each position into its ordered $\mathbb F_p$ digits.
Let $K_j$ consist of matrices with their first $j$ digits zero. If the
next position has distance $d$, elements of $K_j$ have zero entries at
all distances below $d$. Matrix multiplication adds the next digit and
conjugation does not affect it, since multiplying a distance-$d$ term by
any strict triangular term raises the distance. This gives a normal chain
with $K_j/K_{j+1}\simeq (\mathbb F_p,+)$, central in $K/K_{j+1}$.

Store at most one pivot matrix per digit. Its earlier digits are zero and
its pivot digit is one. Sift a matrix by canceling the first nonzero digit
by left multiplication by the appropriate inverse power of the stored
pivot. If the pivot is missing, a suitable power of the remainder normalizes
that digit and supplies a new pivot. Process the input generators and repeat
sifting the $p$-th powers of all pivots and the commutators of all pivot
pairs until every such remainder is trivial. This terminates after at most
one insertion per ambient digit. Restarting the scan after each insertion
still uses polynomial time. Powers are computed by repeated squaring.

To prove correctness, let $S_{>j}$ be the set of ordered power products
of pivots with indices greater than $j$, with exponents from 0 to $p-1$.
Work backward through the indices. Once $S_{>j}$ is a group, the sifted
commutators imply that conjugation by pivot $j$ sends its generators into
$S_{>j}$. The inclusion is equality since the group is finite. The sifted
$p$-th power of pivot $j$ belongs to $S_{>j}$. Therefore adjoining pivot
$j$ gives exactly the ordered products at this step. A nonzero pivot digit
separates two choices of the exponent in that position, so all ordered
products are distinct. Every pivot was made inside the input group and
every input generator sifts to the identity. Thus the products are a unique
normal form for the input group, whose order is $p^t$ for $t$ pivots.

For the additive homomorphism, apply linear algebra over $\mathbb F_p$ to
the pivot images. A solution vector for a desired image gives an ordered
power word lifting it. For the kernel, take a row-echelon basis of the
linear nullspace in the pivot exponent coordinates. Convert its rows to
ordered power words. Each word has a distinct leading ambient pivot, equal
to that of the first nonzero exponent of its row. Their ordered products
with powers 0 through $p-1$ are distinct, by comparing the first different
pivot digit. They thus generate a subgroup with at least $p^{\dim\ker}$
elements. The original unique normal form shows that the entire kernel has
exactly this size. This proves the lemma.

## 2. Canonical forms for a single triangular action

**Theorem.** Let $H$ be a subgroup of a displayed product of unitriangular
groups, and suppose its action on $W$ is lower unitriangular in a displayed
basis. There is a deterministic polynomial-time algorithm to find a
canonical point in the orbit $H x$, a transporter to that point, and
generators and order of the stabilizer of $x$. For tensor products of
natural actions with mixed triangular orientations, reverse the basis in
each upper mode and then use the lexicographic tensor basis to get the
required triangular action. The theorem also applies to quotients by
invariant subspaces.

**Proof.** Choose the lexicographically least point in the orbit, using
prime-field digit order inside each field coordinate. Suppose the first
$r$ coordinates of the current point $x'$ have already been minimized,
and let $H_r$ stabilize that prefix. Lower unitriangularity gives the
homomorphism

$$
H_r\longrightarrow F^+,\qquad h\longmapsto (h x')_{r+1}-x'_{r+1}.
$$

Indeed the change in the next coordinate depends only on the preceding
coordinates, which $H_r$ fixes at this point. Any group element sending
the original point to a point with the selected prefix is a prefix-preserving
element times the transporter already found. Hence the possible next
coordinates form precisely the affine coset of the image of this homomorphism.
Find its least field value by row reduction in the prime-field coordinates.
In an echelon basis, eliminate each pivot digit in order, so it is zero at
the first place where a change is possible. Lift this shift using Section 1,
update the point and transporter, and pass from $H_r$ to the kernel. The
shift map is the same at the updated point since the earlier prefix agrees,
so the kernel is exactly the stabilizer of the newly selected prefix.

After $\dim W$ steps, the point is canonical. Conjugating its stabilizer
back by the recorded transporter gives the original stabilizer. To find a
transporter between two inputs, canonicalize both and compose the two
transporters if the canonical forms agree. For the quotient assertion,
take the images of the original invariant flag in the quotient and omit
repetitions. Each successive quotient has dimension one with trivial action.
These bases can be obtained by Gaussian elimination. The running time
bound follows from Section 1 and the bound on the number of coordinates.

## 3. Shared midpoint when one orbit is affine

**Theorem.** Let $A,B$ be two supplied groups as in Section 2 acting on
the same $W$. They may use different flags. Given $x,y\in W$, one can
deterministically test whether the $B$-orbit of $y$ is its own affine
hull in polynomial time. If it is, write it $y+D$. One can decide
$A x\cap B y\ne\varnothing$, and find both maps to a common point when it
exists, in time polynomial in the input length and $|\{aD:a\in A\}|$.
In particular the algorithm is polynomial when the direction has
polynomially many translates, regardless of the sizes of the point orbits.

**Proof.** Compute the span $D$ of all orbit differences $b y-y$ by
starting with the differences for generators of $B$ and closing the span
under their actions. The result is exactly $D$. It is contained in the
orbit difference span, which is invariant. Conversely the resulting
subspace is invariant under inverse generators as well, by finite
dimension, and the difference for a product is the sum of one difference
and the translate of another. There are at most $\dim W$ span increases.
Section 2 gives the stabilizer order, so the orbit-stabilizer theorem gives
$|B y|$. Since $B y\subseteq y+D$, the orbit is its own affine hull
exactly when $|B y|=q^{\dim_F D}$. The integers in this comparison have
polynomial bit lengths.

Assume that equality holds. Traverse the orbit of $D$ under generators
of $A$, identifying subspaces by their reduced row-echelon matrices.
Record a representative $t$ at each subspace $tD$. This gives left
coset representatives for $A/A_D$, where $A_D$ stabilizes $D$.
For every transition $tD\mapsto s tD=t'D$, store $t'^{-1}st$ as a
generator of $A_D$. They generate the stabilizer: for a word in the
generators and their inverses carrying $D$ back to $D$, follow the
transitions and telescope the chosen representatives. Use a symmetric
generating set and choose the identity representative at $D$.

Invert the recorded representatives to enumerate right cosets
$A_D t^{-1}$. For each branch,

$$
(A_D t^{-1})x\cap(y+D)\ne\varnothing
\quad\Longleftrightarrow\quad
A_D(t^{-1}x+D)\ni y+D\quad\text{in }W/D.
$$

This follows because $A_D$ preserves $D$. Apply Section 2 to these
quotient point pairs. From a successful branch recover $a\in A$ and the
actual point $a x\in y+D$, then use Section 2 for $B$ to recover a map
from $y$ to $a x$. The algorithm searches one branch per direction
translate and never enumerates either point orbit.

For example, take $W=D\oplus F e$ with $\dim D=r\ge 2$. Let $A$
and $B$ both contain all maps $e\mapsto e+z$ for $z\in D$ fixing
$D$ pointwise. Allow $A$ to act by the upper unitriangular group on
$D$ and $B$ by the lower one, independently of the translations.
Both groups are unitriangular in suitable bases, with potentially
different flags. Their point orbits on $e+D$ have size $q^r$, and
the direction orbit has size one. In this example the groups cannot
embed simultaneously into one unitriangular group. Their restrictions
to a two-dimensional coordinate block contain both elementary directions,
which generate an order-two element in odd characteristic and an order-three
element in characteristic two.

## 4. Shared midpoint in a common triangular group

**Theorem.** Let $A,B\le K$, with $K$ and its action as in Section 2.
Put $S=\operatorname{Stab}_K(x)$. If the set $AS$ is a subgroup of $K$,
one can decide $A x\cap B y\ne\varnothing$ and recover both maps in
polynomial time. Whether $AS$ is a subgroup is itself decidable in
polynomial time. This includes the case $S=1$ and the case when either
subgroup normalizes the other.

**Proof.** Section 2 tests whether $x,y$ lie in the same $K$-orbit and
gives $g\in K$ with $g x=y$ if they do. Then

$$
a x=b y\quad\Longleftrightarrow\quad a=b g s\text{ for some }s\in S.
$$

Consequently the question is whether $AS\cap B g$ is nonempty. If $AS$ is
a subgroup, its generators are the union of those of $A,S$. Write
$Bg=g(g^{-1}Bg)$. It remains to intersect two left cosets of subgroups of
$K$.

For two such cosets $g_1 C_1,g_2 C_2$, use the ambient digit filtration
$K_j$ of Section 1. At depth $j$ maintain a pair of representatives
$u_i\in g_i C_i$ agreeing modulo $K_j$, and generators of the subgroup

$$
P_j=\{(c_1,c_2)\in C_1\times C_2: c_1\equiv c_2\pmod{K_j}\}.
$$

Every pair of coset elements agreeing modulo $K_j$ is of the form
$(u_1 c_1,u_2 c_2)$ with $(c_1,c_2)\in P_j$. In the next central
quotient, its discrepancy is the discrepancy of the stored representatives
plus that of $(c_1,c_2)$. The latter is the additive homomorphism
$(c_1,c_2)\mapsto c_1 c_2^{-1}\bmod K_{j+1}$, with target
$K_j/K_{j+1}\simeq\mathbb F_p$. Solve for the needed shift and replace
$P_j$ by its kernel, both using Section 1 in the ambient product group.
Start with $j=0$ and $P_0=C_1\times C_2$. At the last depth a match
is exact, and a failed shift at any step rules out a match. This gives the
intersection element $z=b g\in AS$. To find an actual factorization of
$z$ in $AS$, run the same coset intersection on $A\cap z S$. A point
$a$ in that intersection satisfies $a x=z x=b y$, as required.

To recognize the hypothesis, apply the same intersection algorithm to the
subgroups $A,S$ with both coset representatives equal to the identity.
The final correction subgroup is the diagonal copy of $A\cap S$ and its
order follows from Section 1. Compare $|A||S|/|A\cap S|$, which is the
cardinality of the set $AS$, with $|\langle A,S\rangle|$, computed by
sifting the union of the generators. The two sets agree exactly when
these orders agree, since the first set is contained in the second.

## Scope for the four-layer reduction

The one-sided canonicalizer, the affine orbit test, and both shared-point
algorithms give exact ordinary computations for their stated classes, so
they also give polynomial-time ordinary-TI reductions there by outputting a
fixed YES or NO instance. They preserve one common midpoint and can return
its two maps. For the general four-layer problem each half is a union of
point orbits under its final triangular group, indexed by an unknown inner
factor. The proofs here supply the shared-point test for certain pairs of
those orbits. They do not give a polynomial enumeration or a single ordinary
TI query for all inner factors. The unrestricted fixed-field reduction and
the broader field-uniform reduction remain open in this work.

The subgroup computations use standard sifting, power-commutator and
Schreier ideas. See the [GAP Polycyclic documentation](https://gap-packages.github.io/polycyclic/doc/chap5_mj.html)
for induced generating sequences and [Eick and Ostheimer](https://doi.org/10.1090/S0025-5718-03-01493-5)
for related orbit-stabilizer methods in an integral setting. The arguments
here are self-contained for the finite-field hypotheses stated above.
