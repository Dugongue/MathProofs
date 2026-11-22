# Exact counting at the first rank drop

Let $k=\mathbb F_q$ be a fixed finite field and fix $h\ge2$, with $m=h+1$. Use the marked first-row, centered coefficient substitutions in the square-zero pencils. A point of the pure first rank-drop locus $P$ is an $m$-dimensional direction span contained in the marked first half $X_0$ for which the centered row gains a relation. Equivalently the row rank is less than $m\dim V-\binom m2$. These substitutions use unrestricted matrix coefficients. The same tests can be made on the normalized symmetric pencils, with the fixed transpose contribution removed from the rank threshold. [First rank-drop construction](https://github.com/Dugongue/MathProofs/blob/main/SharpSubstitutionFour/Geometry.md)

**Theorem.**

- Counting $P(k)$ is $\#\mathrm P$-complete under parsimonious reductions. Hardness holds when $P$ is finite étale, every point is $k$-rational, every point lies in one declared standard Grassmannian chart, and the rank deficit is exactly one. In the symmetric matrix presentation, each extra linear equation uses at most four upper-triangular entries with coefficients in $\{0,1,-1\}$.
- For each fixed positive integer $d$, counting degree-$d$ closed points of $P$ is also parsimoniously $\#\mathrm P$-complete. More generally, given circuits $C_i$ and explicit finite field extensions $K_i/k$ of degrees $d_i$, one can construct a single pencil in polynomial time whose pure locus is exactly
  $$
  P=\coprod_i \big(\operatorname{Spec}K_i\big)^{\sqcup N_i},
  \qquad N_i=\#\mathrm{SAT}(C_i).
  \tag{1}
  $$
  In particular distinct $d_i$ provide independent coordinates of the closed-point degree spectrum, even though the format has a single first detecting size.
- Counting the full first-row direction spans, or the corresponding ordered coefficient frames, is $\#\mathrm P$-complete under one-call exact-division reductions. In these hard examples the full locus is smooth projective of fixed dimension $m(m-1)/2$ whenever nonempty. Finally, for an arbitrary symmetric matrix presentation specified by $r$ independent linear equations, the pure count can be computed deterministically in $q^r\operatorname{poly}(\text{input bit length})$, in every characteristic.

## 1. From quadratic equations to marked rank tests

Let $T\subset\mathbb P^{b-1}_k$, $b\ge2$, be cut out by explicit homogeneous quadrics $Q_\nu(z_0,\ldots,z_{b-1})$. Use the square matrix input with $a=b$, and take the space $M$ of symmetric matrices whose upper-triangular entries satisfy the identical linear equations, replacing $z_i z_j$ by entry $ij$ for $i\le j$. Compute a basis of $M$ as the tensor slice list. A zero slice keeps the format positive if $M=0$. This conversion uses linear elimination and has polynomial cost even when a dense tensor or pencil is requested.

The projective rank-one scheme of symmetric matrices is the diagonal in the Segre scheme, identified with the degree-two Veronese image. This statement holds with the scheme structure in all characteristics. Indeed, on a unit pivot chart the rank-one minors factor the matrix as one column times one row. Symmetry forces the two factor lines to agree, by solving their ratios using a unit coordinate. Projective scaling absorbs the resulting unit, without taking a square root. The remaining linear equations are exactly $Q_\nu$ on that diagonal. Hence the projective rank-one scheme of $M$ is $T$.

The first rank-drop theorem now applies in its square symmetric case, for which the combined source and target dimension is at least four. It identifies $P$ with $T$ and the full first-row scheme $\mathcal D$ with
$$
 \mathcal D=T\times_k\operatorname{OGr}(m,2m).
 \tag{2}
$$
The pure section sends a rank-one line to the $m$ copies of its left factor, one in each block of the marked $X_0$. At a geometric detecting plane the rank deficit is exactly one. Indeed, two different rank-one symmetric lines have different left and right factor lines, so the two repeated support spaces have zero intersection. The kernel-line incidence therefore identifies the determinantal scheme on the whole first locus. This includes any nilpotents in the given quadratic presentation. There are no detecting planes at smaller coefficient sizes. [Scheme-level rank-drop and symmetric section](https://github.com/Dugongue/MathProofs/blob/main/SharpSubstitutionFour/Geometry.md)

## 2. A parsimonious quadratic encoding with one affine chart

Given a Boolean circuit, take projective coordinates $z,x_w$, with one $x_w$ per wire. Impose $x_w^2=zx_w$ for every wire. Input wires are free among these Boolean choices. The homogeneous gate rules for AND, OR and NOT are respectively
$$
 zx_c=x_a x_b,\qquad
 zx_c=zx_a+zx_b-x_a x_b,\qquad
 zx_c=z^2-zx_a.
 \tag{3}
$$
Use $zx_c=0$ or $zx_c=z^2$ for a constant gate, and require $zx_{\rm out}=z^2$. A forced-zero wire can be added if needed to ensure $b\ge2$. These constraints involve at most four degree-two monomials. Gates with repeated inputs may first be simplified or supplied with separate copy wires, using $zx_{\rm copy}=zx_{\rm original}$, to keep the stated coefficient restriction.

Every geometric point has $z\ne0$. Indeed $z=0$ forces the square of every remaining coordinate to vanish, which is impossible for a projective point over a field. Consequently $D_+(z)$ is the whole projective scheme. On that affine chart the coordinate algebra defined by the Boolean rules is a product of copies of $k$, one for each Boolean wire assignment, by the comaximal factors $x_w$ and $x_w-1$. In a product of fields each added gate equation deletes exactly the factors on which it fails. Evaluation of an acyclic circuit determines all gate wires from the inputs, so the factors that survive correspond bijectively to satisfying input assignments. This proves the scheme identity $T=\coprod_{\text{satisfying assignments}}\operatorname{Spec}k$, including its reduced structure, over any field. It also ensures that all pure planes in the construction use the same pivot chart, the repeated pivot coordinates corresponding to $z$.

The map in Section 1 therefore preserves the count exactly. The converse witness of a counted pure point is its unique reduced-row-echelon matrix in the declared basis of $X_0$. A verifier checks the pivots and computes the rank of the product map for this plane by finite-field elimination. Every point has a single encoding, and the witness size is polynomial in the explicit input. This gives membership in $\#\mathrm P$, even for pure loci with other structures. The hardness source is Boolean circuit counting, since a fixed-length polynomial-time verifier for any $\#\mathrm P$ function compiles into a circuit with those witness bits as inputs and uniquely determined gate wires. The same construction proves NP-completeness of nonemptiness. [Valiant, counting complexity](https://doi.org/10.1137/0208032)

## 3. Independent closed degrees and zeta functions

To realize the list (1), choose bases $1,\eta_{i,1},\ldots,\eta_{i,d_i-1}$ of the supplied fields $K_i$ and their structure constants $c_{ab}^{(i),j}$. Use one projective coordinate $z$, selector coordinates $e_i$, separate circuit wires $x_{i,w}$, and separate extension coordinates $y_{i,j}$ for $1\le j<d_i$. Put $y_{i,0}=e_i$. The quadratic selector equations are
$$
 e_i^2=ze_i,\qquad e_i e_j=0\ (i\ne j),\qquad \sum_i ze_i=z^2 .
$$
For every variable $v$ in the $i$-th block of wires and extension coordinates impose $zv=e_i v$. Impose $x_{i,w}^2=e_i x_{i,w}$, and use (3) and the output equation for circuit $C_i$ with $e_i$ in place of $z$. Finally take all products of the extension basis coordinates, by imposing
$$
 y_{i,a}y_{i,b}=e_i\sum_{j=0}^{d_i-1}c_{ab}^{(i),j} y_{i,j},
 \qquad 1\le a,b<d_i .
$$
At $z=0$, all selectors vanish at geometric points by their square equations. The wire squares and the diagonal extension product equations then force every wire and extension coordinate to vanish. Thus again the whole projective scheme is on $z=1$.

There the selectors are orthogonal idempotents summing to one. On the factor with $e_i=1$, all other variables vanish by the equations $zv=e_jv$. The circuit algebra is the split product of $N_i$ copies of $k$. The extension-coordinate algebra is $K_i$. Indeed its multiplication table reduces all monomials to the span of the displayed basis, and the map to $K_i$ takes this spanning set to a basis. These two algebras occur in independent variables, so the factor is $K_i^{N_i}$. This proves (1) scheme-theoretically. The number of variables and equations is polynomial in the circuits and the supplied field models. An irreducible-polynomial model also suffices, since its multiplication table is computed by polynomial remainders.

Counting closed points of any fixed degree $d$ belongs to $\#\mathrm P$ using the fixed extension $k_d=\mathbb F_{q^d}$. Guess an RREF plane over $k_d$, test the rank drop, and accept exactly the lexicographically least RREF plane among its conjugates by entrywise $q$-Frobenius. Require its orbit length to be exactly $d$. Frobenius preserves the pivot positions and echelon conditions. Such orbits biject with degree-$d$ closed points, giving one witness per point. The same verifier takes polynomial time if a field model for $k_d$ is supplied and $d$ is measured by its explicit representation. A single circuit with $K_i=k_d$ in (1) gives parsimonious hardness for every fixed $d$, including $d=1$.

Write
$$
 P_m(Q)=2\prod_{j=1}^{m-1}(1+Q^j)=\sum_{j=0}^{m(m-1)/2} b_j Q^j .
$$
This polynomial counts the split maximal isotropic planes over a field of order $Q$. To derive it, count nonzero isotropic vectors $(x,y)$ with $x\cdot y=0$, giving $(Q^m-1)(Q^{m-1}+1)$. Each is contained in as many maximal isotropic planes as there are such planes in split dimension $2m-2$. In fact the quotient $v^\perp/kv$ is split. An invertible coordinate change in one half and its inverse transpose in the other can send the first nonzero half of $v$ to the first axis. The other half then has first coordinate zero and can be removed by an alternating shear. Each maximal plane contains $Q^m-1$ nonzero vectors. The recurrence, with value two at $m=1$, gives $P_m$ in every characteristic.

For every $n\ge1$, (1) and (2) give the exact formulas
$$
 \#P(k_n)=\sum_{d_i\mid n} d_i N_i,\qquad
 \#\mathcal D(k_n)=P_m(q^n)\sum_{d_i\mid n} d_i N_i .
 \tag{4}
$$
There are $d_i$ embeddings $K_i\to k_n$ if $d_i\mid n$ and none otherwise. Thus the formal zeta functions, with variable $u$, are
$$
 Z(P,u)=\prod_i(1-u^{d_i})^{-N_i},\qquad
 Z(\mathcal D,u)=\prod_{i,j}(1-q^{d_i j}u^{d_i})^{-b_jN_i}.
 \tag{5}
$$
These follow by inserting (4) into $\exp(\sum_{n\ge1}\#X(k_n)u^n/n)$. They are compact factorizations and impose no expanded polynomial representation on a counting algorithm.

The same scheme identity gives a count over finite local $k$-algebras $R$ of residue field $k_n$ and maximal ideal $\mathfrak n$. For the schemes (1), reduction $P(R)\to P(k_n)$ is a bijection by unique lifting along finite étale morphisms. Each maximal isotropic plane over $k_n$ has an isotropic complement. Lift their split frame using the unique coefficient-field embedding $k_n\hookrightarrow R$ above the residue map, obtained by simple-root lifting for $X^{q^n}-X$. All lifts of the plane are graphs of alternating $m\times m$ matrices with entries in $\mathfrak n$, as the defining quadratic equation gives zero diagonal and paired off-diagonal entries. Thus $\#\mathcal D(R)=|\mathfrak n|^{m(m-1)/2}\#\mathcal D(k_n)$. This is a statement about $k$-algebra test rings for the same scheme.

The full-locus rational count in the Boolean case is $P_m(q)\#\mathrm{SAT}(C)$. The number of ordered independent first-row frames over $k$ is the same count times $|\mathrm{GL}_m(k)|$, since each plane has exactly that many ordered bases. The corresponding pure frame count has only the basis factor. Both factors are known integers and give one-call exact-division hardness. Membership in $\#\mathrm P$ is by RREF witnesses for planes or the ordered basis itself for frames, with the rank comparison made relative to the full-width baseline. Smoothness and the fixed dimension of the full locus follow from (1) and the alternating graph charts of the split orthogonal Grassmannian.

## 4. An exact algorithm with few equations

Let $Q_1,\ldots,Q_r$ be the independent quadratic equations of an arbitrary symmetric matrix presentation in $b$ variables as in Section 1. Put $Z(F)=|\{x\in k^b:F(x)=0\}|$. The exact affine solution count is
$$
 N_{\rm aff}=\frac{q^b+
       \displaystyle\sum_{[\lambda]\in\mathbb P^{r-1}(k)}
       \left(q\, Z\!\left(\sum_\nu\lambda_\nu Q_\nu\right)-q^b\right)}
       {q^r} .
 \tag{6}
$$
For $r=0$ take the sum empty. To prove the formula, use additive-character orthogonality for the vector $(Q_i(x))_i$, and group nonzero multipliers into projective classes. For a fixed nonzero $\lambda$, summing the character over nonzero scalars gives $q-1$ where the combined quadratic is zero and $-1$ elsewhere. The pure projective count is $(N_{\rm aff}-1)/(q-1)$.

Each $Z(F)$ in (6) is computable in polynomial bit time. In odd characteristic, diagonalize the form by symmetric elimination, find its rank $\rho$ and the determinant $D$ of the nondegenerate part, modulo squares. At rank zero the count is $q^b$. At odd rank it is $q^{b-1}$, and at even positive rank $\rho=2s$ it is
$$
 q^{b-1}+\chi((-1)^s D)(q-1)q^{b-s-1},
$$
where $\chi$ is the quadratic character. For example, the formula follows by splitting hyperbolic planes and using the binary discriminant test. Any nondegenerate form of dimension at least three has an isotropic vector: after diagonalization, the two translated square-value sets in a ternary equation with last coordinate one each have size $(q+1)/2$. Adding a hyperbolic plane to a form of dimension $n$ and zero count $z$ changes its zero count to $qz+(q-1)q^n$. The final anisotropic block is zero-, one- or two-dimensional, and the radical contributes a power of $q$.

In characteristic two, find the radical of the polar alternating form. If $F$ is nonzero there, its restriction is the square of a nonzero linear form, so for each vector in a complement there are exactly $q^{\dim\operatorname{rad}-1}$ ways to make the sum zero. This gives $q^{b-1}$. Otherwise split the nondegenerate quotient into symplectic planes. On a plane the form is $\alpha x^2+xy+\beta y^2$, with zero count $2q-1$ if the absolute trace of $\alpha\beta$ is zero and $1$ otherwise. For $\alpha\ne0$ this follows from the Artin–Schreier equation $t^2+t+\alpha\beta=0$, and the case $\alpha=0$ is hyperbolic directly. The number of representations of each nonzero value is constant because every nonzero scalar is a square. Thus two blocks with zero counts $z_1,z_2$ and nonzero-value counts $c_1,c_2$ combine with zero count $z_1z_2+(q-1)c_1c_2$. Applying this successively and multiplying by the radical factor computes $Z(F)$ using integers of polynomial bit length.

There are at most $q^r$ terms. Multiplying by $P_m(q)$, or by the frame factor as needed, counts the full and ordered loci as well. The same algorithm works over a supplied extension field, replacing $q$ by its order. The quadratic point-counting identities are classical tools. Here they give an explicit codimension parameter for the rank-drop presentation that also supports the hardness reductions above. [Luo–Cheng, counting solutions of quadratic systems](https://www.aimspress.com/article/doi/10.3934/math.2025619)

## Relation to earlier work

Quiver Grassmannian universality and the starting first-drop theorem supply scheme realization. The reductions here are polynomial-size and parsimonious from Boolean witnesses, require no high-degree Veronese, and specify closed degrees independently in one fixed-size rank-drop family. Existing work on finite-field counting studies general point-counting and zeta algorithms. The hardness result fixes the marked first substitution size, and every geometric rank defect in the reduction is one. The proof is in prose and the search did not establish publication priority. [Reineke, quiver Grassmannian universality](https://arxiv.org/abs/1204.5730) · [Lorscheid–Weist, Corollary 3.7](https://arxiv.org/abs/1706.00860) · [Cheng–Hill–Wan, finite-field counting complexity](https://arxiv.org/abs/1111.1224) · [Grochow–Qiao IV](https://arxiv.org/abs/2306.16317)

## Finite controls

Exact enumeration checked nine small projective Boolean systems over $\mathbb F_2,\mathbb F_3,\mathbb F_5$. AND, OR and XOR with forced output one gave one, three and two normalized rank-one points, respectively. The mixed selector system for one degree-one point and two degree-two points gave one point over $\mathbb F_2$ and five over $\mathbb F_4$. Thirty direct quadratic systems over the three prime fields matched (6). An independent span enumeration found the 30 maximal isotropic planes of the split form in dimension six over $\mathbb F_2$.
