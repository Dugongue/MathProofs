# Eliminating generic auxiliary linear inputs and symmetrizing marked-vertex circuits

Informal proof over a field of characteristic zero. The circuit size bounds count both gates and wires. The weighted injection identity is classical. The conclusions here concern its use and the interpolation test in arithmetic circuits with physical symmetry.

## Model

Let (G=S_n) act by (g(x_{uv})=x_{g(u)g(v)}). A circuit for (P(X,z)) is square-symmetric if each (gin G) lifts to a circuit automorphism that acts this way on the input variables (X), fixes each auxiliary variable label (z_i), fixes constant labels and the output, and respects the unordered addition and multiplication gates. Reusing one auxiliary input at arbitrarily many gates is allowed.

Suppose a homogeneous invariant (f(X)) of degree (d) satisfies (f(X)=P(X,L_1(X),ldots,L_j(X))), with homogeneous linear forms (L_i). Throughout, take the total-degree-(d) part of (P) in (X,z) before reasoning about this identity. Homogeneous linear substitution commutes with this operation. In particular the formal auxiliary degree is at most (d), even when the originally supplied circuit has a much larger formal degree.

## 1. Simultaneous deletion of generic dense auxiliary inputs

Separate the auxiliary tuple into a structured tuple (A), fixed by all permutations of a free set of (w) vertices, and a (k)-tuple (L=(L_1,ldots,L_k)) of unrestricted homogeneous linear forms. Assume (kmle w) for some (mge1) with (m!ge d+1).

**Theorem.** There is a nonempty Zariski-open set of tuples (L) for which setting all (k) auxiliary inputs corresponding to (L) to zero preserves (f), after taking the homogeneous part. This set has an explicit, deterministic membership test consisting of one exact determinant of order (M=inom{d+k}{k}). Its input coefficients are obtained by specializing (X) at a single integer matrix fixed by the choice of free blocks, independently of (L).

*Construction and proof.* Choose disjoint ordered blocks (B_1,ldots,B_k) of (m) free vertices. At each block choose the first (d+1) permutations in lexicographic order, numbered (0) through (d). For each (gammainmathbb N^k) with (|gamma|le d), let (g_gamma) apply permutation (gamma_i) to block (B_i) and fix the rest. Set (X^*) to a diagonal matrix whose entries on each ordered block are ((m+1)^0,ldots,(m+1)^{m-1}), and whose other entries are zero. Form the (M	imes M) matrix
[
V(L)_{gamma,alpha}=prod_{i=1}^kigl((g_gamma L_i)(X^*)igr)^{alpha_i},
qquad |gamma|,|alpha|le d .
]
The open set is ({L:det V(L)
e0}).

To see that it is nonempty, choose (L_i^0) supported on the diagonal of (B_i) with coefficients (1,2,ldots,m). The resulting (d+1) scalar values (a_{i,0},ldots,a_{i,d}) on each block are distinct by uniqueness of base-((m+1)) digits. The evaluation matrix can be written in the Newton basis
[
N_alpha(z)=prod_iprod_{b<alpha_i}(z_i-a_{i,b}),qquad |alpha|le d.
]
These polynomials form a basis because the leading monomial of (N_alpha) is (z^alpha) and all other monomials have smaller total degree. The entry at ((gamma,alpha)) vanishes unless (gammagealpha) componentwise, and the diagonal entry is nonzero. Order rows and columns by increasing total degree with the same tie order. The matrix is lower triangular with a nonzero diagonal.

For any tuple passing the test, the analogous matrix over (F(X)) is invertible because its determinant is the polynomial in (X) whose value at (X^*) passed the test. Substitute (A(X)) into the homogeneous circuit and leave the (k) slots free, obtaining (Q(X,z)). Each (g_gamma) fixes (A), and invariance of (P) with the formal slots held fixed gives
[
Q(X,g_gamma L)=g_gamma,Q(X,L)=f(X).
]
The evaluation matrix therefore annihilates the coefficient vector of (Q(X,z)-f(X)). It is invertible, so (Q(X,z)=f(X)) and (Q(X,0)=f(X)). This proves simultaneous deletion.

For rational input coefficients this is a deterministic test polynomial in the input bit length, (M), (n), (m), (d), and (k). Powers at (X^*) and the entries of (V) have polynomial bit length in those parameters. Clear denominators and use exact integer determinant computation. One directly relevant implementation is Hex's fraction-free determinant. A determinant test at (X^*) is a sufficient certificate using ordinary rational arithmetic, so polynomial identity testing is unnecessary here. [Hex, exact fraction-free determinant](https://github.com/leanprover/hex)

For (d=n), one can choose (m=O(log n/loglog n)). If (w=Omega(n)), the theorem permits (k=Theta(nloglog n/log n)), and (M=2^{o(n)}). A generic individual dense coefficient array has trivial stabilizer, since every equality with its transform by a nonidentity permutation is a proper linear constraint. Thus for two or more generic probes, the subgroup fixing the other generic probes can already be trivial. The all-at-once certificate still applies.

## 2. Exact averaging without listing all placements

For a collection of further linear forms, suppose the forms are either fixed by the pointwise stabilizer of a common core of (t) vertices or each fixed by the stabilizer of a single vertex. Let (r) be the number of distinct single-vertex anchors outside the core. Let (s) denote the size of the square-symmetric input circuit. Its degree-(d) Reynolds average, after substituting all these forms for their auxiliary inputs, has a square-symmetric circuit of size
[
n^t,3^r operatorname{poly}!left(s,n,d,inom{d+3r}{3r}
ight).
]
An already invariant polynomial is its own average. The exponent implicit in the polynomial is absolute.

### Reducing the number of slots

Write (D=sum_v x_{vv}) and (O=sum_{u
e v}x_{uv}). The orbits of a point stabilizer on ordered pairs show that every linear form fixed by the stabilizer of (a) is a linear combination of the invariant (D,O) and three local polynomials at (a):
[
x_{aa},qquad sum_{v
e a}x_{av},qquad sum_{v
e a}x_{va}.
]
Indeed the other two types of entries are the remaining diagonals and the off-diagonals having neither endpoint (a), and their sums are obtained by subtracting the displayed local polynomials from (D,O). Substitute these linear combinations into the appropriate slots of the supplied circuit, keeping only three formal indeterminates per anchor outside the core. Any single-anchor form whose anchor lies in the core is handled with the core forms. This permits an arbitrary number of uses and an arbitrary number of linear probes at the same anchor.

### The weighted injection sum

For a fixed injection (eta) of the core into ([n]), there is a well-defined placement of each core-fixed form: take any permutation extending (eta) and relabel that form. Two extensions differ by a core-fixing permutation. On relabeling the host by (g), these forms move to the ones at (geta).

For this (eta), install all these forms. Extract the coefficients for the remaining (3r) slots from the degree-(d) part. For a particular coefficient monomial, let (w_i(v)) be the product of the corresponding powers of the three local polynomials for the image (v) of anchor (i). Put (U=[n]setminusoperatorname{im}eta). The multiplier of that coefficient in the orbit sum is
[
E([r])=sum_{phi:[r]hookrightarrow U}prod_{i=1}^r w_i(phi(i)).
]
For every nonempty subset (Bsubseteq[r]), set
[
c_B=(-1)^{|B|-1}(|B|-1)!sum_{vin U}prod_{iin B}w_i(v).
]
Use (E(arnothing)=1) and, in increasing subset size, set
[
E(S)=sum_{substack{Bsubseteq S\ min Sin B}}c_B E(Ssetminus B).
]
Here the order on anchor labels is fixed and independent of their images in ([n]).

Expanding the recurrence sums (prod_{Binpi}c_B) over all partitions (pi) of (S). For any map (S	o U), its coefficient in this expansion is the product, over its nonempty fibers (C), of the signed weighted partition sums of (C). The weight ((|B|-1)!) counts cyclic orders on (B), and the sign is the sign of such a cycle. Hence the sum for (C) is (sum_{sigmain S_C}operatorname{sgn}sigma). It is one on a singleton and zero otherwise by pairing the permutations using a transposition. This leaves precisely the injections. The rectangular weighted injection sum generalizes the injection presentation of the permanent used in the new ETH-followup formalization. [ETH follow-up, row-cut source](https://github.com/xennygrimmato/eth-hamiltonicity/blob/41935962f954a4204446f4eddc438b3af6831722/lean/EthFollowup/Barriers/RowCut.lean)

### Circuit size and physical symmetry

There are at most (n^t) core placements, and each uses the (inom{d+3r}{3r}) possible monomials in the local slots of total degree at most (d). To extract their coefficients, scale the actual (X) variables by a formal variable (u), use degree one for the local slots, and work in the truncated ring in (u,z) modulo monomials of total degree above (d). There are at most ((d+1)inom{d+3r}{3r}) coefficient positions. Install each core form using the scaled variables. Addition is coefficientwise and binary products use convolution. For an unordered product of (b) incoming values, take the (b)-th elementary symmetric function of those values through Newton identities and the invariant power sums of orders (1,ldots,b). This costs polynomially many coefficient operations and preserves the gate action. Characteristic zero permits each division by an integer. The coefficient of a local monomial (z^alpha) is read at (u^{d-|alpha|}).

For each monomial, joint products over vertex (v) for all subsets cost (O(nr2^r)) gates and wires up to polynomial factors in (r,d). The subset recurrence uses at most (O(3^r)) summands. All vertex sums have unordered ports. As (g) acts on the input variables, send the copy (eta) to (geta), each vertex gate at (v) to the corresponding gate at (g(v)), and keep coefficient and subset indices fixed. This extends the original physical symmetry to the constructed circuit. Sum the outputs over core injections and divide by ((n)_{t+r}=n(n-1)cdots(n-t-r+1)). Every joint injection of the core and anchors extends to the same number of host permutations, so this is the Reynolds average. This proves the size and symmetry claims.

## 3. Consequences and scope

- For (d=n), (r=o(n)), and (tlog n=o(n)), a subexponential-size input circuit as in Section 2 yields a square-symmetric (2^{o(n)})-size average. For (r=lfloor n/sqrt{log n}
floor) distinct diagonal probes, the tuple has (2^{Theta(nsqrt{log n})}) placements, while the compiler still has subexponential size in (n).
- Section 1 can eliminate generic dense probes before applying Section 2. This gives full square symmetrization for this combined family. The lower bound of Dawar and Wilsenach excludes subexponential-size permanent circuits in the resulting model. For the permanent alone, once the generic probes have been deleted, an easier lower bound applies whenever a linear fraction of the vertices remains unmarked. Specialize the marked block to an identity matrix and the cross terms to zero. The residual circuit computes the smaller permanent and is square-symmetric on the surviving vertices. Thus the marked-vertex averaging theorem proves the stronger task of constructing a full symmetric average, including for polynomials other than the permanent. [Dawar–Wilsenach, Theorem 7.1](https://theoryofcomputing.org/articles/v021a014/)
- These are sufficient conditions on the given auxiliary-input representation. They leave open whether a hypothetical small ordinary permanent circuit admits such a representation. The proof uses no assumption about a refutation of ETH. The cited Lean source supplies an exact identity and the Hex library supplies a determinant implementation. The complete circuit construction here is informal.
