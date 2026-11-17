# Exact graph reductions for cyclic phase equivalence

**Theorem.** Let $m\geq 2$ be binary encoded. Given two dense rectangular exponent matrices over $\mathbb Z/m$, the following equivalence reduces to one graph-isomorphism instance in deterministic time polynomial in the input length. Allow row and column permutations, additive row and column shifts, and multiplication of all entries by one common unit of $\mathbb Z/m$. The graph construction takes no factorization of $m$. Given a graph isomorphism, one can recover all parts of a witness in polynomial time. For each fixed $m\geq2$ the unrestricted exponent-matrix problem is GI-complete.

For a Butson matrix presented by its phase exponents, the operations are monomial equivalence with an additional common cyclotomic automorphism. The graph reduction also works for strict monomial equivalence. Transposition can be included for square matrices by adding both orientations in the disjoint-union construction below. The hardness claim is for rectangular exponent matrices without a Hadamard promise. The proof is informal.

## 1. Match a whole list of phases using pairs

For $x\in\mathbb Z/m$, use its representative in $[0,m-1]$ and put
$$
 d_x=\gcd(m,x),\qquad m_x=m/d_x,\qquad b_x=x/d_x.
$$
When $m_x>1$, $b_x$ gives a unit modulo $m_x$. The case $x=0$ has $m_x=1$ and carries no unit information. Give an ordered pair $(x,y)$ the exact label
$$
 C_m(x,y)=\bigl(d_x,d_y,\ b_y b_x^{-1}\bmod\gcd(m_x,m_y)\bigr).
$$
The last coordinate is defined to be $0$ when its modulus is $1$. Compute it by extended gcd. Multiplying the pair by a unit preserves the two gcds and both reduced coordinates are multiplied by the same unit modulo the common divisor, so the label is invariant.

Suppose aligned lists $(x_i)$ and $(y_i)$ have equal $d_{x_i},d_{y_i}$ coordinatewise. Then $u x_i=y_i$ modulo $m$ is equivalent to
$$
 u\equiv b_{y_i} b_{x_i}^{-1}\pmod{m_{x_i}}.
$$
Equality of the pair labels for indices $i,j$ is exactly compatibility of these two congruences modulo $\gcd(m_{x_i},m_{x_j})$. Therefore all equations have a common residue class modulo $L=\operatorname{lcm}_i m_{x_i}$ by the general Chinese remainder theorem. Its residue is a unit modulo $L$. To produce a unit modulo $m$, start with $B=m$ and repeatedly divide $B$ by $\gcd(B,L)$ until that gcd is $1$. This leaves the product of the prime-power factors of $m$ whose primes do not divide $L$. Combine the residue modulo $L$ with $u\equiv 1\bmod B$, again using gcd arithmetic. Every prime divisor of $m$ is covered by one of the conditions, so the resulting integer is a unit modulo $m$. All intermediates have polynomial bit size, and the loop has at most $\log_2 m$ strict decreases. Consequently the labelled one- and two-coordinate data characterize the entire unit orbit, with a constructive converse.

Pair data are essential in general. Modulo $5$, the lists $(1,1)$ and $(1,2)$ agree in all one-coordinate gcds, while the first coordinate forces the common multiplier to be $1$ and the second rules it out.

## 2. Compile dense matrices to one graph

For each row and column anchor $a,b$, compute the dephased matrix
$$
 D^{a,b}_{ij}=E_{ij}-E_{ib}-E_{aj}+E_{ab}\pmod m.
$$
The marked row and column are zero. Under aligned row and column permutations sending anchors to anchors, this dephased matrix removes every additive shift. Conversely, if two dephased matrices agree after aligned permutations and multiplication by a unit, their difference before dephasing is an additive row plus column matrix. Explicitly, a matrix $R$ with $D^{a,b}(R)=0$ has $R_{ij}=R_{ib}+(R_{aj}-R_{ab})$.

For one anchor pair construct a coloured graph with a vertex per row and column, distinguishing row, column, and marked anchors by colours. Give each cell a vertex joined to its row and column vertices and coloured by $d_{D_{ij}^{a,b}}$. For every ordered pair of distinct cells insert a relation vertex coloured by their $C_m$ label. Join it to the two cell vertices through separate role-coloured intermediate vertices. Thus isomorphisms must preserve the ordered positions. Use disjoint colour palettes for rows, columns, cells, relations and intermediary roles. The cell incidence edges make the anchored graph connected when both sides are positive. Zero-size formats can be decided directly.

Take the disjoint union over all anchors. A matrix equivalence induces a graph isomorphism by moving each anchor pair by its row and column permutations. Conversely any graph isomorphism sends a connected anchored component to a connected anchored component. In that component it specifies row and column permutations preserving every cell gcd and pair label. Section 1 produces the common unit, and the identity for $R$ above produces the shifts. With $s$ cells, the disjoint-union construction has $O(s^3)$ vertices before replacing colours by ordinary graph gadgets. Labels are tuples of $O(\log m)$-bit integers, so a common palette can be built from the two inputs without expanding the alphabet of all possible phase values. Standard coloured-GI encoding gives one ordinary GI instance of polynomial size.

For strict monomial equivalence replace the cell gcd by the exact dephased entry and omit the pair vertices. A full-support phase matrix that is monomially equivalent using arbitrary complex diagonal phases is also equivalent using phase shifts modulo $m$, when both matrices consist of $m$-th roots of unity. Indeed, after removing permutations, every product of a row multiplier and a column multiplier is an $m$-th root. Normalize one row multiplier to $1$ by multiplying all row multipliers by one constant and dividing the column multipliers by it. All columns are then $m$-th roots, and any column proves the same for all rows.

For square matrices where transposition is allowed, include the anchored components for both $E$ and $E^{\mathsf T}$, using the same role palettes for both orientations. An equivalence with transposition swaps the corresponding families of components. Conversely any matched component gives an equivalence between one orientation of each input.

## 3. GI-hardness for exponent matrices

Start from side-coloured binary bipartite graph isomorphism, which is GI-hard by the vertex-edge incidence graph of a simple graph. Use its binary incidence matrix. Append more all-zero rows than the original number of rows and more all-zero columns than the original number of columns. Choose the counts from the input dimensions, which may be compared first. Any isomorphism of the original bipartite graphs extends to the padded arrays.

Among rows, declare two equivalent if their difference is constant over all columns. This relation survives the allowed phases and permutations. In the padded matrix it agrees with exact row equality because there is at least one all-zero column. The all-zero rows constitute its unique largest class, since there are more dummy rows than original rows. Likewise the zero columns are the unique largest column class. Thus an equivalence must match a zero row and column to a zero row and column. Dephasing there gives the unchanged padded binary matrices, so the only remaining phase operation is multiplication by one unit. If a $1$ occurs, the multiplier must be $1\bmod m$ to preserve binary entries. If no $1$ occurs both matrices are zero. Hence there are genuine row and column permutations matching the padded matrices. Cancel the prescribed numbers of dummy rows and columns. Any choice of the appropriate number of zero rows and columns has the same effect up to relabelling, since they are identical. This yields a bipartite graph isomorphism.

## 4. Sparse supports and phase-labelled frames

In a graph with cyclic gains, attach opposite gains to the two orientations of an edge. Suppose the graph has no induced cycle longer than a fixed $k$. Record all oriented simple cycles of lengths $3,\ldots,k$, with their ordered vertices, and record the two-coordinate label for every pair of their cycle sums, together with the gcd for each cycle. The graph and these relations can be encoded by coloured incidence vertices with positions distinguished. For fixed $k$ there are polynomially many cycles recorded and polynomially many pairs. It is enough to know the recorded cycles because every longer simple cycle decomposes into a sum of shorter oriented cycles using a chord, recursively. Every closed walk is a sum of simple cycles after deleting backtracking. The CRT argument gives one unit for all cycle gains at once. A gain difference vanishing on all closed walks is a difference of vertex potentials, by integration along a spanning forest. This proves correctness of a single GI reduction also for this sparse-support class.

For a family of mutually unbiased bases the support of the frame Gram matrix is complete multipartite, so every induced cycle has length at most four. If the overlap phases are given as exponents in a common finite cyclic alphabet, the same construction tests their switching equivalence, with a common unit allowed if desired. For physical projective-unitary equivalence use exact cycle sums and omit the common-unit operation. The cross-basis overlap magnitudes are fixed, and equality of the Gram matrices after phase switching and permutation is equivalent to one unitary on the vectors by Gram reconstruction. The graph can allow permutation of bases or fix their order by colour. This is a result for supplied exponent data.

## 5. Full-support tensors under monomial actions in every mode

The same anchored argument applies to higher-way arrays. For example, let $T$ be a $d$-tensor over a presented finite field with every entry nonzero. Consider the action of independent index permutations and invertible diagonal matrices in every mode. For an anchor tuple $a$, write $a[i\gets x_i]$ for the tuple with its $i$-th entry replaced by $x_i$, and define
$$
 \widehat T_a(x)=
 \frac{ T(x) T(a)^{d-1} }{\prod_{i=1}^d T(a[i\gets x_i])}.
$$
The mode-diagonal factors cancel. Conversely equality of these arrays after aligned index permutations means that the entrywise ratio $R$ of the original arrays satisfies $R(x)=R(a)^{1-d}\prod_i R(a[i\gets x_i])$. This explicitly expresses the ratio as a product of one diagonal factor per mode. Build a graph for each anchor with coloured mode vertices, a vertex for each tensor entry joined to its $d$ index vertices, and entry colour $\widehat T_a(x)$. The anchor is marked in every mode. The disjoint union of all anchored components gives one GI instance by the same connected-component argument. Its size is polynomial in the dense input, and field operations take polynomial bit time in $\log q$. This works uniformly in the sizes of the modes and allows direct transporter recovery from a graph isomorphism.

For $d$-way exponent arrays with complete support, one can instead use additive dephasing $E(x)+(d-1)E(a)-\sum_i E(a[i\gets x_i])$ modulo $m$. Its kernel consists precisely of sums of functions of the individual coordinates. Colour pairs of entries with $C_m$ as in Section 2 to allow one global unit modulo $m$. Both statements concern monomial actions in **every** mode. The variant in which one mode is monomial and others carry unrestricted $\mathrm{GL}$ has a different action. [D'Alconzo, *Monomial isomorphism for tensors and applications to code equivalence problems*](https://doi.org/10.1007/s10623-024-01375-0)

## Provenance

The archival Rune invariant extracted the phase modulus from rectangle differences. Sigil used the monomial class of a descended transition. The useful idea from the Ward and Trellis work was to keep each comparison attached to its indices. Here the retained pair constraints have a proved local-to-global property under the full unit group of the cyclic ring.

Cycle products and spanning-tree reconstruction are standard for gain graphs and projective frames. The GI equivalence in the unrestricted binary-matrix case has a classical antecedent in Booth and Colbourn. Chien and Waldron already show that indexed triple products suffice for three or more mutually unbiased bases. The contribution here is the all-modulus, factorization-free synchronization of one common cyclotomic automorphism using only pair labels, and its compilation with binary modular phases rather than phase-sized fibres. The recent Butson switching paper gives an explicit counterexample to interpreting isomorphism of a particular unmarked lift graph as phase equivalence. The graph above retains indexed rectangle or cycle information, which is sufficient by construction. Publication priority for this particular reduction remains unverified. [Booth–Colbourn, binary matrices](https://cs.uwaterloo.ca/research/tr/1977/CS-77-04.pdf) · [Cavaleri–Donno, gain-graph switching](https://arxiv.org/abs/2111.12428) · [Chien–Waldron, frame cycle products](https://arxiv.org/abs/1312.5393) · [*From Butson Hadamard switching to graph switching and back*, §3](https://arxiv.org/html/2611.18296v1#S3)
