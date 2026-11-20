# One ordinary tensor comparison for ordered centroid field blocks

Fix a finite field $F=\mathbb F_q$ and a constant $c>0$. Let $T$ be a concise trilinear form on $U_1\times U_2\times U_3$ given by a dense array of bit length $L\ge 2$. Conciseness means the radical in each individual slot is zero. Compute the largest reduced subalgebra of the centroid of $T$ and write it as a product of finite fields $E_j$. Let $U_{ij}$ be its $j$-th summand in the $i$-th mode. Assume that the four-entry descriptors
$$
([E_j:F],\dim_{E_j}U_{1j},\dim_{E_j}U_{2j},\dim_{E_j}U_{3j})
$$
are pairwise distinct and that every $\dim_{E_j}U_{ij}\le c\log_2 L$.

**Theorem.** Over each fixed $F$, this is a deterministically recognizable class of dense tensors. Special-linear isomorphism for two tensors in the class reduces in deterministic polynomial time to one ordinary three-tensor isomorphism instance over $F$. The construction uses no bound on the degrees of the $E_j$ or on the number of independently chosen Frobenius exponents. It handles local nonreduced centroids via their reduced subalgebras. As a restricted language, pairs with a tensor outside the class can be sent to a fixed no-instance.

## Recovering the fields and ordering the blocks

Compute the centroid $C$ by solving the linear equations
$$
T(C_1x,y,z)=T(x,C_2y,z)=T(x,y,C_3z).
$$
It is a unital commutative subalgebra of the product of three matrix algebras. For example, $C_1D_1$ and $D_1C_1$ have equal contractions with every $y,z$, since one can move $C$ to mode two and $D$ to mode three in either order. Conciseness gives equality in mode one, and the other modes follow by permutation. The same transfer identities give closure under composition. An isomorphism of the original tensors conjugates their centroids by its three mode maps.

In a finite commutative $F$-algebra of dimension $h$, the stable image of the $F$-linear Frobenius $a\mapsto a^q$ is the product of the residue fields. Indeed the nilradical has nilpotence index at most $h$, so $a\mapsto a^{q^k}$ kills it for $q^k\ge h$. The induced map on the product of fields is bijective, hence this image maps isomorphically onto that product. This construction is invariant under $F$-algebra isomorphism. Compute the image by linear algebra. Its $q$-Frobenius fixed algebra is $F^s$, where $s$ is the number of field factors. A basis of this fixed algebra separates the factors. For each basis element $b$ and $t\in F$, the interpolation polynomial for the value $t$ yields an idempotent $1_{b=t}$. Refine the current idempotents by all these masks and discard zero products. After all basis elements, the surviving idempotents are the primitive ones. There are at most $h$ at any stage. This is polynomial for fixed $q$.

The image of the $i$-th matrix of a primitive idempotent is $U_{ij}$. Its action is unital as an $E_j$-module and gives its $E_j$-rank from the $F$-dimension. Greedy basis extension via $F$-linear span finds an $E_j$-basis. For a pair of tensors, the distinct descriptors impose an isomorphism-invariant ordering of the blocks. Mismatched descriptor lists give a fixed no-instance. For each matched pair use one common presentation of its field $E_j$. For example, compute a field isomorphism by the deterministic finite-field isomorphism algorithm and compose with one of the at most $[E_j : \mathbb F_p]$ prime-field Frobenius powers until it agrees with the two specified inclusions of $F$. Such a power exists because restrictions of prime-field Frobenius generate the automorphisms of $F$. All matrix frames and the determinant of each frame can now be computed. [Lenstra, Finding Isomorphisms Between Finite Fields](https://pub.math.leidenuniv.nl/~lenstrahw/PUBLICATIONS/1991b/art.pdf)

## A determinant line from multiplication and trace

Fix one matched block, with common model $E/F$ of degree $e$, basis coordinates $E^r$ in each copy, and $F$-linear block transporter $g=P\tau$, where the action of $\tau\in\operatorname{Gal}(E/F)$ is coordinatewise. Pairing the mode action with the marker $E\times U\to U$ enforces this factorization, with the *same* $\tau$ on every marked mode using that field. Register the field multiplication and unit on a field sort. Every raw transporter induces such a $\tau$ by conjugation, so adding these marks excludes none.

With $\lambda=\det_E P$, call $L_{\mathrm{top}}=\bigwedge_E^r U$ the top exterior line. Link the exterior powers by module actions and wedge maps
$$
U\times \bigwedge_E^a U\ \longrightarrow\ \bigwedge_E^{a+1}U.
$$
Isomorphisms on these sorts extend uniquely, because decomposables span each exterior power and all linked actions use the same $\tau$. In the top coordinates the map is $x\mapsto\lambda\tau(x)$. These are all bilinear diagrams over $F$, with total exterior dimension at most $e2^r$.

For $s=0,\ldots,e-1$, make a copy of the top $E$-coordinate space and link it to the top space by the fixed $F$-linear map $x\mapsto x^{q^s}$ in the chosen coordinates. Its forced map is $x\mapsto\lambda^{q^s}\tau(x)$ since $\tau$ commutes with the $q$-Frobenius. Link those copies by a binary chain of multiplication maps $E\times E\to E$. If the input maps are $a\tau,b\tau$, the forced output is $ab\tau$, as the multiplication is surjective. The final map is $N_{E/F}(\lambda)\tau$. Its restriction along $F\hookrightarrow E$ is a one-dimensional scalar map with value $N_{E/F}(\lambda)$. For $e=1$ use the top space itself. This uses $O(e)$ explicit field multiplications and $F$-linear maps. It never lists the elements of $E$.

For odd characteristic and even $e$, compute the unique quadratic subfield $Q$ as the fixed space for $x\mapsto x^{q^2}$. Attach the trace-zero line $Q^-$ by inclusion. This is the orthogonal complement of $1$ for the nondegenerate trace pairing $(x,y)\mapsto\operatorname{Tr}_{Q/F}(xy)$. The $q$-Frobenius acts on it by $-1$ because $\operatorname{Tr}_{Q/F}(x)=x+x^q$. Thus $\tau=\mathrm{Frob}^k$ acts on the line by $(-1)^k$. In a normal basis of $E/F$, $\mathrm{Frob}$ is a single $e$-cycle, so $\det_F(\tau)=(-1)^{(e-1)k}$. For odd $e$ or characteristic two this determinant is always $1$, and no quadratic line is needed. For the coordinatewise action on $E^r$, take the $r$-th power of this scalar. The quadratic line is needed only when $r$ is odd.

The trace construction in Alpöge's release uses an explicit restricted-scalar trace Gram pairing and its orthogonal action. The finite-field trace-zero operation here uses that same pairing construction with identity field involution and coefficient $1$. Its role is to distinguish the even-degree Frobenius sign from the norm of the linear factor. The finite-field argument uses separability and has no RH or GRH hypothesis. The number-field statement in the release is used as a construction in a different setting and is not invoked as a finite-field Lean theorem. [Alpöge announcement and source release](https://alpo.ge/remark.pdf)

The determinant of the $E$-linear map $P$ after restriction of scalars is $N_{E/F}(\det_E P)$. One proof extends scalars to a splitting field, where its $e$ summands have matrices given by the $e$ embeddings applied to $P$. Consequently the product of the two scalar marks is exactly $\det_F(g)$ in the selected block frames. Linked one-dimensional bilinear multiplication maps enforce this product. The same attachment also works for determinant characters by taking powers on scalar lines.

## Assembly and the raw determinant

Place all factors in the prescribed descriptor order and choose a fixed $F$-basis of each shared field model. Concatenate its ordered multiples of an $E$-basis of each mode block to obtain a raw frame $\beta_{T,i}$ in mode $i$ of input $T$. Taking products of the block determinant lines gives a scalar map with value
$$
K_i=\det(\beta_{B,i}^{-1}g_i\beta_{A,i}).
$$
The inclusion maps of the marked blocks into $U_i$ link each computation to the same original $g_i$. In the terminal $F$-line of the $i$-th mode, give $A$ the marked vector $\det(\beta_{A,i})^{-1}$ and $B$ the marked vector $\det(\beta_{B,i})^{-1}$. Its preservation is exactly
$$
1=\det(g_i)=\det(\beta_{B,i})K_i\det(\beta_{A,i})^{-1}.
$$
This check is applied to all three modes. Every input determinant-one transporter induces the centroid actions, preserves the labels, and extends to all diagrams and marked points. Conversely every diagram isomorphism preserves the original tensor and the displayed equations force each raw determinant to be one. In particular there is no mixing of witnesses for different norm or sign equations.

Every mark is a tensor of order at most three, including dual slots for maps. The [uniform mixed-system packing](TraceGramOrthogonalMarkers.md#4-size-and-ordinary-compilation) converts a variable number of linked, marked tensors to a constant-size mixed system, then to one ordinary three-tensor instance. The ambient vector-space dimensions, the number of maps and the total dense lengths are polynomial, since $e$ is at most the input dimension and $2^r\le L^c$. Use the same format on both sides, determined by their common descriptor list. The fixed-field dense bit bound follows. [Published fixed-system reduction, Theorem 4.1](https://arxiv.org/html/2306.03135v2)

## Repeated descriptors and modes with a radical

The pairwise distinct requirement can be relaxed. Let $b$ be the maximum multiplicity of one descriptor. The theorem still holds when $b=O(\log L/\log\log L)$ for sufficiently large $L$, with a fixed implied constant. The total number of repeated descriptors can grow. To see this, a centroid idempotent can move between slots of $T$, so the tensor is a direct sum of its blocks. Order the descriptors and choose an arbitrary fixed order of the blocks in each descriptor group on each side. The calibration frames are computed in these orders.

For one descriptor group, try all bijections between its source and target blocks and all tuples of prescribed relative block determinants in $D=(F^\times)^3$. There are at most $b!|D|^b$ choices. Each individual block-pair comparison is a single ordinary TI test by the construction above, with a prescribed three-coordinate determinant rather than the value one. A group transporter for a chosen bijection exists precisely if all its individual tests pass. The group determinant tuple is the product of the chosen block determinants multiplied, in mode $i$, by $\operatorname{sgn}(\pi)^{[E:F]r_i}$, where $\pi$ is the chosen matching permutation. This is the determinant of the block permutation matrix. Therefore, for every $d\in D$, a polynomial positive formula of ordinary TI tests decides whether the group realizes $d$. Mismatched descriptor multiplicities give a fixed no-instance.

For a balanced binary tree whose leaves are the descriptor groups, let $P_{I,d}$ state that the groups under node $I$ realize combined determinant tuple $d$. The recursion is
$$
P_{I,d}=\bigvee_{h\in D}\left(P_{I_{\mathrm{left}},h}\wedge P_{I_{\mathrm{right}},h^{-1}d}\right).
$$
Expanding one root formula has polynomial size because its depth is logarithmic in the number of groups and $|D|$ is fixed. The test at the root uses the three determinant ratios required by the original calibration frames. The same determinant calculation applies to modes of unequal sizes.

For completeness, the positive formula reduces to one TI query. The binary AND is the ordinary TI comparison of two ordered, tagged direct summands. Grochow–Qiao's partitioned-TI construction yields a linear bound on the output side length for the two-block AND. For the OR of $X\cong X'$ and $Y\cong Y'$, encode each ordered pair by the AND tensor $E(X,Y)$, and then by a connected unital algebra $C(E(X,Y))$. For any bilinear tensor $T:U\times V\to W$, define $C(T)$ as the triangular algebra with three scalar diagonal entries, strict upper entries $U,V,W$ in positions $12,23,13$, and the product of entries $12$ and $23$ supplied by $T$. After padding to positive side lengths, the chain $1\to2\to3$ in the radical modulo its square fixes the three diagonal labels. Images of the diagonal idempotents can be conjugated back by the unit $\sum_i f_i e_i$, where $f_i$ are the images and $e_i$ are the original labels. The remaining isomorphism is exactly that of $T$. The center is the scalar diagonal because both $U$ and $V$ are nonzero, hence the algebra has no nontrivial central idempotents. Compare the product of the algebras for $(X,Y),(X',Y')$ with that for $(X,Y'),(X',Y)$. Isomorphism must either match or swap the two connected factors. The first option asks $Y\cong Y'$, and the second asks $X\cong X'$. Output the corresponding multiplication tensors. Tensor isotopy of unital associative products implies algebra isomorphism by normalizing the images of the identity, as shown in the [semisimple multiplication proof](SemisimpleMultiplicationIsotopes.md). Both gates have linear side growth. Use balanced conjunctions and disjunctions in each bucket and a balanced tree across buckets. The combined formula has logarithmic depth and polynomially many leaves, giving a single polynomial-size output. [Grochow–Qiao, Theorem 5.1](https://arxiv.org/pdf/2306.16317)

For a nonconcise tensor, first take the quotient by its three individual radicals. Mismatched dimensions of corresponding radicals exclude isomorphism. In a mode whose radical is nonzero, any quotient transporter can be extended by a radical isomorphism with whatever nonzero determinant is required to give raw determinant one. In a mode whose radical is zero, impose the original determinant condition. Thus the same theorem applies if the concise quotient meets the field-rank and multiplicity conditions, checking only the full modes. The identically zero pair is immediate. A basis adapted to each radical gives the frame calibration for arbitrary input coordinates.


## Proof status

This proves both implications on the stated raw centroid families. It leaves open arbitrary tensors whose only available centroid field has large module rank or whose descriptor groups exceed the proved matching bound. The norm and quadratic trace identities have a separate Lean companion. The complete tensor encoding argument is a mathematical proof in prose.
