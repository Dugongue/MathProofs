# Rank-two partial matrix completion is existentially complete

**Theorem.** Let \(F\) be a fixed field. The existential theory of \(F\), in the ring language with constants \(0,1\), reduces in polynomial time to deciding whether a partial matrix with all specified entries in \(\{0,1\}\) has a completion of rank at most two over \(F\). Each unspecified entry is an independent placeholder. Conversely the completion problem is expressible in the existential theory of \(F\) with a polynomial-size formula. The reductions pin a \(2\times2\) identity block, so accepting completions have rank exactly two. The arithmetic reduction works uniformly over fields with at least eight elements. A separate graph reduction gives NP-completeness over every fixed finite field.

Shitov's rank-three result already answers the general and constant-rank questions under (A16) in the *Existential Theory of the Reals Compendium*. The argument here sharpens that result to rank two with binary specified entries. For every fixed \(r>2\), pin an independent diagonal block \(I_{r-2}\) and specify zeros on both cross-block rectangles, thereby raising the completion rank by exactly \(r-2\). In the usual one-sided multiplicative approximation problem, the rank gap \(2\) versus at least \(3\) gives \(\exists\mathbb R\)-hardness over \(\mathbb R\) for every approximation factor below \(3/2\). [Compendium, A16](https://arxiv.org/abs/2407.18006) · [Shitov, Theorem 3.3 and Corollary 6.10](https://www.rxiv.org/pdf/2107.0049v2.pdf)

This is an informal proof with finite gadget checks. A targeted search did not locate the exact rank-two binary theorem. The search included Peeters's rank-three finite-field result, Ganian et al.'s parameterized matrix completion and subspace clustering papers, and recent low-rank completion hardness. Ganian et al.'s rank-two clustering lower bound permits multiple subspaces and concerns a different problem. [Peeters](https://pure.uvt.nl/ws/files/191434/orthogon.pdf) · [Ganian et al., 2018](https://proceedings.mlr.press/v80/ganian18a.html) · [Ganian et al., 2020](https://doi.org/10.1609/aaai.v34i04.5804) · [New Hardness Results for Low-Rank Matrix Completion](https://arxiv.org/abs/2506.18440)

## 1. Arithmetic with nonzero scalar values

Assume \(|F|\ge8\) for this construction. First turn an existential field formula into polynomial equations and then into gates for addition, multiplication and constants \(0,1\). For example a bit \(b\) indicating the truth of an atom \(f=0\) can satisfy \(b(b-1)=0\), \(bf=0\), and \((1-b)(fu-1)=0\) with an auxiliary \(u\). Boolean gates have polynomial encodings. Arithmetic circuit gates name all intermediate products and sums, and integer constants can be built with binary arithmetic and negation. Thus the standard reduction has polynomial size. The input language uses prime-ring coefficients given by integer arithmetic, including binary-encoded integers. It does not assume a separate encoding of arbitrary elements of an extension field.

Represent every original scalar \(x\) by \(x^+-x^-\), with both new scalars nonzero. Every field element admits this representation, since one can choose \(x^-\) to avoid zero and \(-x\). Then an addition gate \(x+y=z\) becomes

\[
x^++y^++z^-=x^-+y^-+z^+,
\]

and a multiplication gate \(xy=z\) becomes

\[
x^+y^+ + x^-y^- + z^- = x^+y^- + x^-y^+ + z^+.
\]

All summands are nonzero, including each separately named product. To impose an equality of the two sums with addition gates whose three values are all nonzero, start both sums at the same fresh scalar \(s\ne0\), and add the summands one at a time. Choose \(s\) avoiding the negatives of the at most six nonempty partial sums, as well as zero. There are at most seven forbidden values, so this is always possible. Use one shared label for the two final sums. Conversely the gates give equality of the two unshifted sums by cancellation. An original constant zero is expressed by sharing its two labels. An original constant one is expressed by \(x^-+1=x^+\). Equalities of original variables can also be expressed by an addition gate with a variable fixed to zero before this conversion.

We have reduced to existence of an assignment of nonzero scalars satisfying addition, multiplication and pins to one. The new variables and gates are linear in number in the original elementary arithmetic system.

## 2. Rank-two matrix constraints

Start with a fully specified \(I_2\) on two anchor rows and two anchor columns. Every rank-two completion factors as row vectors and column vectors in \(F^2\), with matrix entries their ordinary pairings. By changing the basis of the factorization, both anchor rows and anchor columns become the standard basis. Therefore any coordinate of a new row or column can be pinned to zero or one by specifying a single entry against the opposite anchor. Other named pairings below are likewise individual matrix entries. Use fresh row and column labels for each named auxiliary vector, except where a reusable vector is explicitly specified.

We will use fixed rows and columns with vectors \((1,1)\), \((1,-1)\), and the signed coordinate axes. Pin \((1,1)\) directly in each orientation. Create \((1,-1)\) by pinning its first coordinate to one and its pairing with the opposite \((1,1)\) to zero. Create \((-1,1)\) by pinning its second coordinate to one and its pairing with the opposite \((1,1)\) to zero. A row \((-1,0)\) is forced by pinning its second coordinate to zero and its pairing with the column \((-1,1)\) to one. Likewise force the row \((0,-1)\) by pinning its first coordinate to zero and its pairing with the column \((1,-1)\) to one. Signed columns are constructed by the same procedure if needed. All these specified entries are zero or one, including in characteristic two.

### Reusable coordinates for a nonzero scalar

For each scalar label \(x\), introduce a row \(R_x=(x,1)\) by pinning its second coordinate. If the scalar is required to be one, also pin its first coordinate. Create the following auxiliary rows and columns.

| Vector | Specified entries in addition to the displayed pinned zeros |
| --- | --- |
| Column \(U_x=(u,0)\) | \(R_x\cdot U_x=1\) |
| Row \(D_x=(d_1,d_2)\) | \(D_x\cdot(1,-1)=0\), \(D_x\cdot U_x=1\) |
| Column \(V_x=(0,v)\) | \(D_x\cdot V_x=1\) |
| Column \(K_x=(-1,k)\) | Pin its first coordinate by its unit pairing with fixed row \((-1,0)\). Set \(R_x\cdot K_x=0\). |
| Row \(Q_x=(0,w)\) | \(Q_x\cdot K_x=1\) |
| Column \(L_x=(l_1,l_2)\) | \((1,-1)\cdot L_x=0\), \(Q_x\cdot L_x=1\) |
| Row \(P_x=(s,0)\) | \(P_x\cdot L_x=1\) |

The first equation forces \(x\ne0\) and \(u=x^{-1}\). The next two force \(D_x=(x,x)\) and \(v=x^{-1}\). The last four rows of the table force \(k=x\), \(w=x^{-1}\), \(L_x=(x,x)\), and \(s=x^{-1}\). Conversely, these choices work for every nonzero \(x\). In particular a new row can have either coordinate forced to \(x\) by setting its pairing with \(U_x\) or \(V_x\) to one. A new column can likewise have either coordinate forced to \(x\) using \(P_x\) or \(Q_x\). The coordinate pins impose no restriction on the other coordinate.

### Multiplication and addition

To impose \(xy=z\), make a fresh row whose coordinates are forced to \((x,z)\) and a fresh column whose coordinates are forced to \((y,-1)\). Use the scalar-coordinate gadgets above and force the last coordinate by unit pairing with the fixed row \((0,-1)\). Set the fresh row–column entry to zero. Its value is \(xy-z\).

To impose \(x+y=z\), introduce nonzero scalars \(u,v\), enforce \(uz=x\) and \(vz=y\) by the multiplication gadgets, and force a fresh row to have coordinates \((u,v)\). Set its pairing with the fixed column \((1,1)\) to one. Since \(z\ne0\), these equations are equivalent to the desired addition, and every valid addition extends by \(u=x/z\), \(v=y/z\).

Every pin fixes an entry to zero or one. All auxiliary labels are fresh as stipulated, so no entry receives two incompatible requirements. Unspecified entries are ordinary independent stars. A solution of the scalar gate system constructs all row and column vectors and hence an actual matrix completion. Any rank-two completion gives the displayed factorization and hence a valid scalar gate solution by the forced-coordinate arguments. The number of named rows and columns is linear in the number of scalar labels and gates, and writing the dense partial matrix therefore takes polynomial time. Zero-padding with additional pinned rows or columns makes the matrix square if required.

## 3. Every fixed finite field

Let \(F=\mathbb F_q\). Reduce fixed \((q+1)\)-colorability to completion. Use one row \(r_v\) and column \(c_v\) per graph vertex. Set \(r_v\cdot c_v=0\), and force both to be nonzero by prescribing one unit pairing each with a private opposite vector. Choose one orientation \((u,v)\) of each undirected edge. Add a new row \(r_{uv}\) with \(r_{uv}\cdot c_u=0\) and \(r_{uv}\cdot c_v=1\). Also pin an independent \(I_2\) block, leaving entries between this block and the rest unspecified.

In any rank-two completion, each vertex line is \(F r_v=\ker c_v\) in the two-dimensional factor space. The edge conditions imply that the two endpoint lines differ. This gives a proper coloring by the \(q+1\) one-dimensional subspaces of \(F^2\). Conversely, given a proper coloring, choose a nonzero representative on each color line and a nonzero annihilator for each vertex. Private opposite witnesses for unit pairings exist by nonvanishing. For edge \((u,v)\), the functional \(c_v\) restricts nontrivially to the line \(F r_u\), so rescale its representative to obtain the required edge row. Add the standard basis anchor vectors and fill all stars using the resulting pairings. This produces a rank-two completion. Fixed \((q+1)\)-colorability is NP-complete for every \(q\ge2\), and fixed-field rank-two completion is in NP by its factorization certificates. The existential theory of a fixed finite field is also in NP, since assignments have polynomial size and the field operations have constant-size tables. This supplies the claimed polynomial reduction for all fixed finite fields, including those with fewer than eight elements.

## 4. Exact scope and consequences

Membership in the existential theory follows by quantifying two coordinates per row and column and equating their pairings to the specified values. The proof applies over the rationals as well as the reals. If Hilbert's tenth problem over \(\mathbb Q\) is undecidable, then these binary rank-two completion instances are undecidable over \(\mathbb Q\). The same hypothesis rules out a total computable bound on the numerator and denominator sizes needed for yes-instance completions, since bounded rational enumeration would decide the problem. The completion question asks whether a rank orbit meets a coordinate affine section. A point-to-point matrix orbit test merely compares two ranks.

The threshold is sharp for binary specified entries. A rank-at-most-one completion exists exactly when no prescribed zero occurs at the intersection of a row containing a prescribed one and a column containing a prescribed one. The necessity follows from the nonvanishing of the corresponding row and column factors of every rank-one factorization. For sufficiency, choose each row or column factor to be one if it contains a prescribed one and zero otherwise. This criterion is checkable in polynomial time.
