# A Segre grid realizes conditional determinant characters

For a fixed finite commutative local ring $R$ and a subgroup $\Gamma\le R^\times$, let $L_e$ and $L_*$ be monomial characters on $\Gamma^m$. Attach an ordinary three-tensor-isomorphism instance over $R$ to each $L_e$. There is a polynomial-time construction of a finite free unital associative algebra $A$ with center $R$ and
$$
\det\operatorname{Aut}_R(A)=
\{L_*(X)\mid X\in\Gamma^m,\
L_e(X)=1\text{ for every no instance }e\}.
\tag{1}
$$
Both multiplication-by-unit determinant images are full, so the index of (1) in $R^\times$ is the exact number of determinant-one orbits in the ordinary multiplication orbit. For a chosen $\delta\in\Gamma$ a basis change supplies an ordinary transporter between multiplication tensors with the same unit vector. A determinant-one correction gives a solution $X$ with $L_*(X)=\delta$ and recovers ordinary witnesses for every test with $L_e(X)\ne1$.

In particular, whenever $p\mid |R^\times|$, a linear span program over an explicitly represented finite field of characteristic $p$ can be tested on ordinary TI answers by one supplied-transporter correction. This gives exact $k$-out-of-$n$ thresholds, including over $\mathbb F_2[\epsilon]/(\epsilon^2)$ with $\delta=1+\epsilon$. Linear span compilation into ordinary TI was already available over fields. Here the Segre geometry realizes the entire character image directly in one unmarked multiplication algebra over the same local ring, with witness extraction. [Earlier Ceva construction](https://github.com/Dugongue/MathProofs/tree/main/PolyhedralTensorDeterminants)

If $\Gamma=\{1\}$, take $A=R$. Its algebra automorphism determinant image is trivial and the only required register assignment is the all-1 tuple. Otherwise $s=|R^\times|>1$. We use tests of equal positive shape, replacing cases already decided by their shapes by fixed yes or no tests.

## The Segre grid

Take two free rank-$N$ modules $U,V$ with bases $u_i,v_j$, indexed from 0 to $N-1$. Here $N$ counts the variables and auxiliary registers including 0. Take a scalar source and sink with $H=U\otimes_R V$ between them and axes $w_{ij}=u_i\otimes v_j$. One scalar middle block has incoming module $U$ and outgoing module $V$, with product $uv=u\otimes v$ in $H$.

At every axis put a marker matrix algebra $M_{d_{ij}}(R)$, with the usual incoming row, outgoing column, and row-column pairing into $Rw_{ij}$. The widths $d_{ij}>s=|R^\times|$ are pairwise distinct. Other middle blocks test ratios of pairs of axes. For a pair $(w_\alpha,w_\beta)$ and test $(T,T')$, use the line $R(a w_\alpha+w_\beta)$ at each $a\in\Gamma$. At that line put $M_s(P(T))$ for $a=1$, and $M_s(P(T'))$ otherwise. The algebra $P(T)$ has three scalar diagonal corners, the two input modules and the output module in its upper corners, and the given bilinear map as its only product of two strictly upper blocks. Its first diagonal coordinate gives an augmentation to $R$. Each middle block acts on its outer arrows through $M_s(R)$, with the standard row-column product into its line. A fixed yes test uses equal tensors. A fixed no test uses the scalar tensors $0$ and $uv$. Every test uses a distinct support pair.

The pairings are balanced over their middle algebras and every product of three strictly upper outer blocks vanishes. This gives associativity. The center is the common scalar $R$. Commutation with the outer idempotents first makes an element diagonal. The center in $P(T)$ is scalar, since its consecutive nonzero free upper corners connect the three entries. Its matrix algebra and every marker also have scalar center. The outer modules force equality of all the scalars.

Refine each matrix tensor block into its three internal diagonal vertices. The radical consists of the strictly upper part plus maximal-ideal entries on the diagonal. After reduction the semisimple quotient is a product of simple matrices. Align the transported block idempotents $f_i$ with their targets $e_i$ using the unit $\sum_i f_i e_i$. Its diagonal projections are exactly 1, since each diagonal idempotent congruent to 0 or 1 equals 0 or 1. The unit differs from 1 only in strictly upper positions, so left and right multiplication are triangular with unit diagonals on free Peirce blocks. The conjugation has determinant 1 over $R$.

The source, special Segre middle and sink are the three width-one vertices and are distinguished by their directed corner relations. Each marker is pinned by width. The width-$s$ vertices divide into connected components of the induced undirected Peirce support, each one whole tensor block. Thus the action on $H$ preserves its axes. It can carry a test line only to another line of the same support pair.

Write the actions on the two Segre arrows as $G,J$. Their product forces the action on $H$ to be $G\otimes J$. This is diagonal with units on the diagonal, so $G,J$ are diagonal too. The coefficient $G_{ii}J_{jj}$ is a unit for every $i,j$, so both factors are units. Then $G_{ki}J_{jj}=0$ for $k\ne i$ implies $G_{ki}=0$, with the same argument for $J$. Write their diagonals as $x_i,y_j$, so the weight on $w_{ij}$ is $h_{ij}=x_i y_j$.

On a pair of axes the lines force $h_\alpha/h_\beta\in\Gamma$, and fix that ratio to 1 when its test is no. The normalized line goes to the label $(h_\alpha/h_\beta)a$. The exceptional block at 1 must stay fixed if its algebra is nonisomorphic to the others. To check that the blocks reflect the tensor test, transport the matrix units in a free right module. Their isomorphic summands $Q$ satisfy $Q^s\cong P(T')^s$, so Krull–Schmidt gives $Q\cong P(T')$. The first endomorphism corner cancels the amplification. An isomorphism $P(T)\cong P(T')$ preserves the ordered inner Peirce spaces after aligning idempotents, so its three maps intertwine the original products. Conversely a successful comparison gives an augmentation-preserving isomorphism of the triangular algebras. Use these identifications to translate the label blocks, scaling each incoming row by $h_\beta$ to preserve its pairing. If the ratio is 1 the blocks can be fixed. Thus every allowed assignment of axes is realized.


## Multiplying normalized side ratios

Put $X_i=x_i/x_0$ and $Y_j=y_j/y_0$, with $X_0=Y_0=1$. For every nonzero index $i$, enforce $X_i=Y_i$ by the fixed no test on $(w_{i0},w_{0i})$. On $(w_{i0},w_{00})$ impose the fixed yes test to put $X_i$ in $\Gamma$, or replace it by an input test when that register is a test output. Every comparison still puts its ratio in $\Gamma$.

A multiplication register $X_k=X_i X_j$ with fresh $k$ and $j\ne0$ is enforced by a fixed no test on $(w_{ij},w_{k0})$. Taking $i=0$ copies a register. Repetition computes every specified monomial character. Use a fresh output register for each input test, and omit tests whose row is identically 1. There are no repeated support pairs. A multiplication uses an axis with second index nonzero and another with second index zero and fresh first index. A copy uses the same rule with first index zero for the former axis. Ties between the two Segre factors have identical index on both arms, so cannot coincide with a fresh-register comparison. Membership and input tests use two axes with second index zero and are placed once per register. The register count is polynomial since exponents are read modulo the fixed group exponent.


Let $k_*$ be the output register. Choose marker dimensions by
$$
d_{ij}+1+\mathbf 1_{i=j}\equiv b_{ij}\pmod s,
$$
where $b_{k_*0}=1$, $b_{00}=-1$, and all other weights are zero. For constant output use all zero weights. Distinct widths exist by assigning disjoint intervals of length $s$ above $s$. The two Segre arrows contribute $\prod_i x_i\prod_i y_i=\prod_i h_{ii}$ to the determinant, since their ranks agree. The $H$ and marker terms give $\prod_{ij}h_{ij}^{d_{ij}+1}$. Each matrix-marker action is inner, of determinant 1. Its paired arrow determinants multiply to $h_{ij}^{d_{ij}}$ by the determinant of the scaled identity pairing.

Every automorphism of $M_s(P(T))$ has determinant 1. Aligning its matrix units makes the residual map entrywise, giving an $s^2$-th power determinant. Left and right multiplications in an inner map give $s$-th power determinants by repetition on columns and rows. In a block permutation the determinants of the chosen isomorphisms telescope to the determinant of an automorphism. Each paired arrow contribution is also an $s$-th power. Block signs are 1 because either $s$ is even and all relevant free ranks are even, or $s$ is odd and $-1=1$ in $R$. Thus the full determinant is $h_{k_*0}/h_{00}=X_{k_*}$. This proves (1). For fixed $R$, the number of markers, their widths, and the multiplication table size are polynomial in the register count and query sizes.

Scaling the sink alone gives every left unit determinant, and scaling the source gives every right unit determinant. The ratio $\det X\det Y/\det Z$ of a multiplication isotopy is the determinant of its algebra isomorphism, by evaluating at 1 and normalizing the two unit multipliers. This gives the orbit-index formula and the promised correction by rescaling one $H$ coordinate by $\delta^{-1}$. The known map fixes the common unit. After normalizing a correction and aligning idempotents, read the Segre ratios. For each nonidentity test ratio the exceptional block maps to a copy of the second tensor. Align its transported matrix units by taking a nonzero residue column of the first idempotent and applying the other units to it. This is a basis. The three upper $(1,1)$ slots recover the ordinary transporter over $R$.


## Linear matroids and thresholds

Take $\Gamma=\langle\rho\rangle$ of prime order $p$. A register is uniquely $\rho^a$ for $a\in\mathbb F_p$. Let $K/\mathbb F_p$ be explicitly represented, and let $v_e,v_*$ be row vectors over $K$. Use prime-field registers for the coordinates of a vector $z$ over $K$. For each $e$, repeat test $e$ for each prime-field coordinate of $v_e z$, making all these coordinates zero if that test is no. The coordinates are monomial characters on the registers, since multiplication by a specified field element is prime-field linear. The output is one nonzero prime-field coordinate functional of $v_*z$.

If $v_*$ is in the span of the no rows, the entire output is zero and the determinant image is $\{1\}$. Otherwise there is a $z$ annihilating the no rows with $v_*z=1$. Its scalar multiples over $K$ give every value of the chosen coordinate, so the image is $\Gamma$. A nonzero output yields a separating linear functional. Every row it does not annihilate comes with a TI witness recovered from the correction.

For a test that accepts when the yes rows span a target, represent the dual matroid by a kernel basis. If $t$ is the target element, $Y$ is the yes set and $N$ denotes the no set, the dual rank formula gives
$$
r^*(N\cup\{t\})-r^*(N)=1+r(Y)-r(Y\cup\{t\}).
$$
Thus $t$ is spanned by $Y$ exactly when it is outside the span of $N$ in the dual. A span program with several rows per label is handled by repeating the same TI test for every occurrence. [Karchmer and Wigderson on span programs](https://www.math.ias.edu/~avi/PUBLICATIONS/MYPAPERS/KW93/proc.pdf)

For $k$ out of $n$, choose an extension $K$ of size at least $n+1$. Use $n+1$ distinct values $\alpha$ and the rows $(1,\alpha,\ldots,\alpha^{n-k})$, including the target row. Any $n-k+1$ rows span the space. Any set of at most $n-k$ input rows is independent together with the target. The acceptance threshold is exactly $k$. For fixed $p$ such an extension has logarithmic degree and can be built by testing monic polynomials of the required degree for irreducibility. The orbit count is $|R^\times|$ below the threshold and $|R^\times|/p$ at and above it.

## A size separation from terminal connectivity

Consider terminal-weight Ceva graphs in which each edge is labelled by a single input yes bit or a constant, with arbitrary repetitions permitted. The terminal criterion is disconnection in the graph of no edges. Reachability in that graph has a cubic-size monotone Boolean circuit in its edge-presence bits, by the standard transitive-closure recurrence allowing one more intermediate vertex at each step. Swapping AND and OR and complementing input constants gives a circuit of the same size for disconnection as a monotone function of the yes bits.

Babai, Gál and Wigderson give a linear-size binary monotone span program for the odd-factor function on bipartite graphs and a superpolynomial lower bound on its monotone circuit size. The program uses columns $e_u+e_v$ for edges and the all-ones target. It tests whether the available graph contains a spanning subgraph with all degrees odd. Applying the Segre construction to this program gives a polynomial-size determinant compiler for that function over a ring carrying a unit of order 2. Therefore a terminal-weight graph of polynomial size with those same input labels cannot realize this function on arbitrary yes/no answers. The lower bound concerns this terminal connectivity model of the compiler. [Babai–Gál–Wigderson, Theorems 2.1 and 2.3](https://doi.org/10.1007/s004930050058)

The earlier ordinary-TI span-program construction uses marked shift spaces and a tensor-system compiler over fields. The graph-of-sides proof already gave determinant-one majority and formula composition. The contribution here is a direct Segre implementation over local rings realizing the full determinant character image and reflecting each witness to its normalized register and the corresponding successful input tests. Priority for this realization is open. [Earlier ordinary-TI span-program compiler](https://github.com/Dugongue/MathProofs/blob/main/TISLNegativeAtlas/LinearSwitchCompiler.md)

The written proof gives the full algebra construction and all reductions. The Lean companion checks the Segre ratio and multiplication gate over any commutative group. The finite controls directly enumerate 9,216 matrix pairs over binary dual numbers, check 3,780 group assignments and 1,572 Vandermonde thresholds. [Lean components](D.lean) · [Finite controls](DCheck.py)
