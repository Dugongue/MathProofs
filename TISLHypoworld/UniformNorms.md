# Uniform norm conditions and one-mode orientation over the field of three elements

Write $F=\mathbb F_3$. All ordinary reductions in this chapter are deterministic polynomial-time many-one reductions to ordinary three-tensor isomorphism over $F$. The base assertion $H$ is $\mathsf{TI}_{\rm SL}(F)\le_m^{\rm P}\mathsf{TI}(F)$. It is equivalent to equality of these two many-one degrees because unused lines in the three source modes let ordinary transporters be extended with determinant one. Every isomorphism of the padded tensors takes their intrinsic supports to each other, so the restrictions extend back to the original dimensions. This proves reflection for the padding even on nonconcise tensors. [Open Question 1.9](https://arxiv.org/html/2306.03135v2#S1.SS5).

## Four equivalent assertions

The following each hold exactly when $H$ holds.

1. **One-mode orientation.** Ordinary TI can decide whether a bimap transporter has determinant one on its output mode. The other two maps may have either determinant. It is sufficient to solve this on the unital associative multiplication tensors constructed in Section 2, whose left and right multiplication by units always has determinant one.
2. **Uniform extension-field norm orientation.** Given an explicitly represented finite extension $E/F$ of arbitrary degree and two bimaps over $E$, ordinary $F$-TI can decide whether there is an $E$-linear transporter whose three determinants have norm one to $F$. This is one uniform reduction with input field degree included in the bit size.
3. **Coupled signs across independent comparisons.** Given a list of bimap pairs over possibly different explicitly represented finite extensions of $F$, ordinary $F$-TI decides whether independent choices of transporters give a vector of determinant norms satisfying an explicitly supplied binary affine system of rank $O(\log L)$, where $L$ is the total input length. Each factor contributes three bits. The equations can involve all factors at once.
4. **Finite-state constraints on sign sequences.** For any fixed finite-state automaton on the eight possible determinant-norm triples, ordinary $F$-TI decides whether independent transports for an input list of bimap pairs can produce an accepted word. One alphabet symbol is chosen by the transporter for each pair. The automaton is fixed and the number of pairs and all extension degrees may grow.

The first assertion weakens the group constraint on a single tensor. The second changes the coefficient field and imposes a norm rather than the determinant in the coefficient field. The last two allow genuinely coupled constraints on a varying number of independent input pairs.

## A weighted multiplication table that fixes the coefficient field

Use the bimap convention $B(fx,gy)=hA(x,y)$ with dimensions $n_U,n_V,n_W$. For every character $\chi$ of $\{\pm1\}^3$, one can test by a single output-oriented $F$-tensor comparison whether $\chi$ of the three norm determinants equals $1$. Its weights are three numbers $w_U,w_V,w_W\in\{0,1\}$. Changing bilinear covariant conventions inverts some coordinates, which leaves signs unchanged.

Universal bimap stabilizers are $(sI_U,tI_V,stI_W)$ for $s,t\in E^\times$. The character on these stabilizers is trivial exactly when
$$
w_Un_U+w_Wn_W\equiv w_Vn_V+w_Wn_W\equiv0\pmod2.
$$
If it is nontrivial, an isomorphic pair admits both values of the character by norm surjectivity. The query then reduces to ordinary $E$-TI, followed by ordinary $F$-TI. For the latter, regard the bimap as $F$-bilinear, and include the linear operator of multiplication by the displayed field generator on each role. Its commutation forces each map to be $E$-linear. This is a fixed tensor system, so it compiles to one ordinary $F$-TI instance. The trivial-character comparison also tests ordinary TI. Unequal formats and zero-dimensional formats can be decided directly. Assume positive equal formats from now on. [Chen, Grochow, Qiao, Tang and Zhang, Theorem 4.1](https://arxiv.org/html/2306.03135v2#S4).

### The weighted triangle and its anchor

Let $R_j=E[t]/(t^j)$. Take three ordered vertices $0,1,2$ with diagonal rings $R_{M_i}$. The corners $01,12,02$ are respectively $U\otimes_E R_{k_U}$, $V\otimes_E R_{k_V}$ and $W\otimes_E R_{k_W}$. Choose $k_i\ge2$ of parity $w_i$, with $k_W\le k_U,k_V$, and $M_i\ge\max k_i$. The diagonal rings act by truncation. The only product of two off-diagonal core corners is the given bimap on the two consecutive edges, extended over $R_{k_W}$ after truncation. This is an associative triangular algebra. The weights use a truncation-length form of the triangular tensor-to-algebra encoding. [Grochow and Qiao, Tensor Isomorphism-Completeness](https://doi.org/10.1137/21M1441110).

Add four intermediate vertices $a_1,\ldots,a_4$ and a sink $b$, sharing source vertex $0$. Include one-dimensional $E$-corners from $0$ to each $a_i$ and from each $a_i$ to $b$, and an $E^2$-corner from $0$ to $b$. Let the product on the two-edge path through $a_i$ be scalar multiplication times the $i$th vector in this list:
$$
(1,0),\quad (0,1),\quad (1,1),\quad (1,\alpha).
$$
For a proper extension $E/F$, take $\alpha$ to be the given polynomial-basis generator. For $E=F$ take $\alpha=-1$. These define distinct lines. All diagonal rings at the new vertices are also truncated polynomial rings over $E$. They act on the new corners through their residues. There are no cross products between the core and anchor corners. Apart from diagonal actions, all nonzero products run along two-edge paths with no further possible nonzero off-diagonal product. The diagonal actions commute with those path multiplications. This verifies associativity. The diagonal units give a unit for the full algebra, denoted $D(A)$.

Choose every diagonal ring length distinct. This can be arranged by adding multiples of four to lengths once all the requirements below have been met. All lengths are bounded by an absolute constant. Use bases induced by the same displayed field basis on both outputs.

### Every isomorphism preserves the field and the character

The radical consists of diagonal nilpotent ideals and off-diagonal corners. The quotient is $E^8$. Align primitive idempotents of any isomorphism by conjugation by a unit congruent to one modulo the radical. For example, for matching systems $e_i,f_i$ congruent modulo the radical, $\sum_i f_i e_i$ is such a unit and intertwines the systems. Inner conjugation by this unit has determinant one since left and right multiplication are unipotent along the radical filtration. After alignment the distinct diagonal ring dimensions force each vertex to match only its namesake.

Inside any truncated diagonal ring, the solutions of $x^{|E|}=x$ are precisely the coefficient field. Indeed the residue is fixed, and in characteristic three raising a sufficiently large $|E|$ power kills nilpotent terms. Thus an $F$-algebra isomorphism induces a field automorphism at each vertex. A nonzero corner forces its two endpoints' field automorphisms to be equal, because their scalar actions coincide and are faithful on that corner. Connectivity gives one common field automorphism $\tau$. The induced semilinear map on the anchor $E^2$ preserves the four displayed lines. The first two make its linear part diagonal, and the third makes it scalar. The fourth then forces $\tau(\alpha)=\alpha$, so $\tau$ is the identity. Thus the map is $E$-linear on every role after alignment.

On the anchor $E^2$, write the induced map as $sI$. Each pair of one-dimensional path maps has product of its coefficients equal to $s$, since it carries the specified nonzero line product to itself with scale $s$. The determinant over $E$ of the anchor off-diagonal part is $s^{4+2}$. Its $F$-determinant is the norm of that expression and is one. At each new diagonal ring choose $M_{a_i}\equiv1\pmod4$ and $M_b\equiv0\pmod4$. A linearized uniformizer map $t\mapsto\lambda_i t+O(t^2)$ contributes the norm of $\lambda_i^{\binom{M_i}{2}}$. These exponents are all even, so the new diagonals contribute determinant one.

In the core, the $t$-linearized coefficients at the three vertices agree. In fact each core corner has length at least two, the left and right actions of $t$ coincide, and applying the isomorphism and reducing modulo $t^2$ forces these coefficients to agree. Denote their common value by $\lambda$. Reducing the corner maps modulo $t$ gives $f,g,h$ with exactly the original bimap transport condition. By the $t$-adic filtrations the determinant over $F$ is the norm of
$$
(\det_E f)^{k_U}(\det_E g)^{k_V}(\det_E h)^{k_W}
\lambda^{\,\sum_{i=0}^2\binom{M_i}{2}+\sum_{i=U,V,W} n_i\binom{k_i}{2}}.
$$
An $E$-linear bimap transporter extends in the other direction by coefficientwise maps on the three core corners and identity on the diagonals and all anchor corners.

### Unit determinants and the output-only condition

For a unit acting by left multiplication on a triangular algebra, the exponent of the norm of its residue at vertex $v$ is the sum of the diagonal length and all outgoing corner dimensions over $E$. The exponent for right multiplication uses incoming dimensions. This follows by taking a semisimple section and using the radical filtration for a unit with residue one, whose determinant is one.

At the core vertices the incoming and outgoing sums agree modulo two because the chosen weights are trivial on universal scalar stabilizers. The anchor contributes $4+2$ outgoing dimensions at vertex $0$, which is even. The new intermediate vertices have one incoming and one outgoing dimension. The sink has $4+2$ incoming dimensions and none outgoing. Thus the chosen new lengths make both unit characters trivial at the new vertices. Choose the parities of the core lengths to do the same at the core vertices. Adding two to one core length flips the parity of its triangular exponent $\binom M2$, while preserving its length parity. Use this to make the total exponent of $\lambda$ even. Then make the lengths distinct by multiples of four as promised, which preserve both parities. It follows that every left and right unit multiplication has determinant one, and the possible algebra-isomorphism determinants are exactly the values of $\chi$ on the original transporter norms.

An isotopy of multiplication tensors of two unital associative algebras is of the form
$$
(f',g',h')=(L_a\phi,R_b\phi,L_aR_b\phi)
$$
where $\phi$ is a unital algebra isomorphism and $a,b$ are units. This follows by evaluating the isotopy at the units and normalizing the resulting invertible left and right multiplications. In this construction $\det h'=\det\phi$. Hence the output-only determinant-one question on the multiplication tensors of $D(A),D(B)$ tests the single character exactly. The same pair can be fed directly to three-mode SL-TI, since a determinant-one algebra isomorphism supplies three determinant-one maps and every SL transporter has determinant-one output. As $\dim_F D(A)=O([E:F](n_U+n_V+n_W+1))$, the dense construction is polynomial in the stated bit input.

## Combining character and sign choices

The norm determinant triples of a transporter set are empty or a coset of a subgroup of $\{\pm1\}^3$. A nonempty coset contains a specified triple exactly when every character can attain that triple's value. Indeed any wrong coset is separated by a linear functional on the quotient by the stabilizer sign subgroup. The trivial character detects an empty transporter set. For a negative character target in the weighted case, conjugate the target multiplication by a fixed $F$-linear map of determinant $-1$. All relative algebra determinants then flip sign and the left and right unit determinants remain one. This construction avoids finding an element of prescribed field norm. For a nontrivial character correctable by the universal scalars, either sign is feasible exactly when ordinary isomorphism holds. For the trivial character the negative comparison is always false.

There is a fixed-conjunction compiler for ordinary TI and a binary OR compiler of constant-factor side growth. The latter compares the unordered pairs of tagged ordered objects $\{(a,c),(b,d)\}$ and $\{(a,d),(b,c)\}$, so straight matching tests the second comparison and crossed matching tests the first. To implement the wrappers with linear side length, use centrally indecomposable triangular multiplication algebras with respectively length-two and length-three diagonals to tag the two entries of an ordered pair, then enclose the pair in a fresh centrally indecomposable triangular multiplication algebra. Unordered pairing is a direct product of these outer algebras. The labeled variants are separated by the dimensions of the intrinsic diagonal corners. Multiplication-tensor isotopy reflects their algebra isomorphisms by the preceding unit normalization. A binary AND uses the tagged ordered product. Balanced compositions of these constant-growth wrappers give polynomial-size ordinary TI pairs. [Grochow and Qiao, linear-length tensor gadgets](https://arxiv.org/abs/2306.16317).

Under $H$, the above character tests reduce to ordinary TI. This proves assertion 2 by a fixed conjunction, and the special case $E=F$ proves its converse. If one-mode orientation reduces to ordinary TI, the same character construction over $F$ and the same conjunction prove $H$. The implication from $H$ to assertion 1 follows by testing all four possible choices of signs in the unspecified modes and taking OR. More generally any prescribed subset of the eight sign triples has a single ordinary comparison under $H$.

For assertion 3, view sign triples as vectors over $\mathbb F_2$. Write the constraints as $A x=b$ with linearly independent remaining rows, after removing redundant equations and rejecting inconsistency by elimination. Its rank is $r=O(\log L)$. The total feasible signs are either empty or a product of cosets. Their image under $A$ is again empty or a coset. Thus it contains $b$ exactly when every one of the $2^r$ dual characters can produce its value at $b$, including the trivial character. Each character of the image pulls back to one character on each constituent triple. In every component test both reachable signs for that character. To combine two pairs of tests $(p_+,p_-)$ and $(q_+,q_-)$ use
$$
((p_+\wedge q_+)\vee(p_-\wedge q_-),\quad
 (p_+\wedge q_-)\vee(p_-\wedge q_+)).
$$
This computes attainable products, including cases with multiple or zero choices. Balance the tree over components, then take the conjunction over dual characters. The circuit has bounded fan-in, logarithmic depth, and polynomial-size leaf comparisons under $H$, so applying the positive wrappers gives one ordinary comparison. Conversely take one $F$-pair and require all three determinants one, a rank-three system. A semilinear extension allowing simultaneous Frobenius on the three modes also reduces under $H$, by branching over at most $[E:F]$ Frobenius maps and accounting for the three explicit $F$-linear frame determinants of each branch.

For assertion 4, form for each pair the Boolean transition matrix of the fixed automaton. An entry is the OR, over the letters realizing the corresponding transition, of the fixed-sign-triple tests for that pair. Boolean matrix multiplication across the input positions exactly tests possible successive transitions. The matrices have fixed size, so balanced multiplication uses a bounded-fan-in positive circuit of logarithmic depth. Test acceptance with its start and final states and compile to one ordinary TI pair under $H$. Conversely a fixed automaton accepting just the one-letter identity word recovers $H$ on one $F$-pair.

All the reductions treat the extension degree and the number of factors as part of the input. These proofs make no assertion about requiring the determinants to equal one inside a proper extension field instead of requiring their norms to equal one.
