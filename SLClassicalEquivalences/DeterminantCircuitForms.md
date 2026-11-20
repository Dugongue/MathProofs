# Special-linear tensor isomorphism and linear equivalence of determinant polynomials

## Computational equivalence for a class of homogeneous forms

The usual polynomial linear-equivalence problem asks whether there is an invertible linear substitution taking one formal polynomial to another. The variables are allowed to mix without a supplied block structure on the substitution. The problem can be posed for homogeneous polynomials supplied by arithmetic circuits. [Kayal, polynomial equivalence](https://epubs.siam.org/doi/10.1137/1.9781611973082.108)

**Theorem.** Over any field $F$, special-linear three-tensor isomorphism reduces by a deterministic objectwise many-one reduction to ordinary linear equivalence of a single homogeneous polynomial given by a division-free arithmetic circuit. The explicit family below has polynomial circuit size and variable count, and its total degree is linear in the sum of the three mode dimensions. The inverse reduction works on the promise that the input circuits compute members of this family in their designated coordinates. It can reconstruct the underlying tensors even if the circuits do not display the defining expression. Thus over explicitly represented finite fields the two problems are polynomial-time many-one equivalent, with the promise understood for the restricted polynomial problem.

In particular, the reverse reduction $\mathsf{TI}_{\rm SL}\leq_m^{\rm P}\mathsf{TI}$ is equivalent to placing this family of ordinary circuit-form equivalence in $\mathsf{TI}$. A reduction for polynomial-degree homogeneous circuit-form equivalence in general would suffice. The theorem below strengthens this sufficient hypothesis to projective equivalence of determinant polynomials of explicit homogeneous linear pencils.

### Determinant forms that enforce the special-linear action

Put $V_i=F^{n_i}$ for $i=1,2,3$, with $n_i\ge1$. For each $i$ make $n_i+1$ vector-variable copies $X_{i,j}$ of $V_i$, for $1\le j\le n_i+1$. Write $X$ for their direct sum and $x_{i,j}\in X_{i,j}$ for a vector variable. For each copy define the determinant form
$$
D_{i,j}(x)=\det(x_{i,1},\ldots,\widehat{x}_{i,j},\ldots,x_{i,n_i+1}),
$$
with the remaining columns in their indicated order. For a tensor $A$, let $L_A(x)$ be the trilinear form of its entries evaluated on $x_{1,1},x_{2,1},x_{3,1}$. A change of variables by three independent determinant-one matrices is the special-linear orbit relation on tensors, since transposes and inverses preserve determinant one.

For a polynomial $P$ on $X$, define its translation radical as the set of fixed vectors $v$ such that $P(x+uv)=P(x)$ as a formal polynomial in $x,u$. For the ordinary determinant on $n$ by $n$ matrices the translation radical is zero. In fact, a nonzero proposed direction can be taken by constant invertible row and column operations to $\operatorname{diag}(I_k,0)$ with $k\ge1$. Choosing $\operatorname{diag}(0,I_{n-k})$ as the translated matrix changes its determinant from zero to one at translation parameter $1$. Undoing the changes of basis scales both determinants by the same nonzero constant. This argument also includes $k=n$ and $n=1$.

It follows that the translation radical of $D_{i,j}$ is the sum of $X_{i,j}$ and all copies from all other groups. Every invertible linear map $R$ that preserves all the $D_{i,j}$ individually preserves their radicals. For each $i,j$, intersect the radical of $D_{i,j}$ with all radicals $D_{i',\ell}$ for $i'\ne i$. The intersection is exactly $X_{i,j}$. Indeed, each other group has at least two copies, and intersecting all its radicals kills its component. Consequently $R$ preserves every individual copy and has invertible blocks $P_{i,j}$.

Fix a group of dimension $n\ge 2$. For any two distinct columns $k,\ell$, choose an omitted column $j$ different from them. In the test of $D_{i,j}$ take the $k$th and $\ell$th column vectors both equal to $v$. The determinant on the original columns is zero. The other transformed columns vary independently because their matrices are invertible. Therefore $P_{i,k}v$ and $P_{i,\ell}v$ must be dependent for every $v$. The invertible map $P_{i,\ell}^{-1}P_{i,k}$ fixes every vector line. Applying it to basis vectors and to their pairwise sums proves it is scalar over every field. Write all blocks in this group as $P_{i,k}=\lambda_k P$ for a common invertible matrix $P$. Preservation of the determinant omitting column $j$ says
$$
\det(P)\prod_{k\ne j}\lambda_k=1.
$$
Comparing the equations for two omissions gives equality of their corresponding scalars. Thus all column copies have one common matrix $P_i$ and $\det P_i=1$. For $n=1$, the two omitted-column determinants are the two coordinate linear forms, and preserving them makes both blocks the identity. Conversely any common $P_i\in\mathrm{SL}_{n_i}(F)$ on the copies of each group preserves all anchors. The simultaneous linear stabilizer of the ordered determinant forms is therefore exactly the diagonal copy of the three desired special-linear groups. This uses formal polynomial identities, including over small finite fields.

### Folding the ordered determinants and data into one form

List the anchors and the data form as $F_1^A,\ldots,F_J^A$, where only the data entry $L_A$ depends on the tensor. Give that entry degree $3$ even for the zero tensor, and sort the list by the assigned homogeneous degrees $e_j$ in nondecreasing order. Resolve ties by a fixed ordering of the copy indices and of the data entry. Put
$$
D= \max_j e_j+J+3,\qquad
b_j=j+1,\qquad c_j=D-e_j-b_j,\qquad
\alpha=D+1,\quad \beta=D+2 .
$$
Both tag exponents $b_j,c_j$ are at least $2$. The $b_j$ increase strictly and the $c_j$ decrease strictly, so the pairs are incomparable in coordinatewise order. Introduce two additional variables $s,t$. Output the single homogeneous form
$$
H_A(s,t,x)= s^\alpha t^\beta
\left(s^D+t^D+s^{D-1}t+\sum_{j=1}^J s^{b_j}t^{c_j}F_j^A(x)\right).
$$
Its degree is $\alpha+\beta+D=3D+3$. Since $J=1+\sum_i(n_i+1)$, this is linear in $\sum_i n_i$. There are $2+\sum_i n_i(n_i+1)$ variables. Every anchor determinant can be constructed by a polynomial-size division-free circuit over $F$, the data uses the explicit trilinear coefficients, and the powers can be formed by repeated squaring. All constants introduced by the construction belong to the prime subfield. This gives polynomial arithmetic construction cost and polynomial bit cost for explicit finite-field input. [Berkowitz, division-free determinant](https://cs.uwaterloo.ca/~r5olivei/courses/2021-winter-cs487/berkowitz-paper.pdf)

To prove soundness, suppose $H_B(S(s,t,x))=H_A(s,t,x)$ for an arbitrary invertible linear map $S$. The parenthesized polynomial has degree $D$ and is divisible by neither $s$ nor $t$, as seen by setting either variable to zero. Its irreducible factors have multiplicity at most $D$. In the full form $s,t$ are the unique factors of multiplicities $\alpha,\beta$, respectively. Unique factorization and invertibility of substitution force
$$
s'=\lambda s,\qquad t'=\mu t,\qquad x'=R x+u s+v t
$$
with $\lambda,\mu\in F^\times$ and $R$ invertible.

Cancel the common monomial $s^\alpha t^\beta$ in the substituted equality. The coefficients of $s^D$ and $s^{D-1}t$ in the resulting polynomials yield
$$
\lambda^{\alpha+D}\mu^\beta=1,\qquad
\lambda^{\alpha+D-1}\mu^{\beta+1}=1.
$$
A tagged term cannot contribute to either coefficient because its $t$ exponent is initially at least $2$ and substitution in $x$ cannot decrease it. Dividing gives $\mu=\lambda$ and then $\lambda^{\alpha+\beta+D}=1$. Replacing $S$ by $\lambda^{-1}S$ preserves the full polynomial equality by homogeneity. We may assume $s'=s$ and $t'=t$.

Now extract the coefficient of $s^{b_j}t^{c_j}$ in the parenthesized identity. Any other tagged term is excluded by incomparability of the pairs. Its own tagged term contributes precisely $F_j^B(Rx)$, since any use of a shear term $us$ or $vt$ increases an exponent. The scalar-only terms have at least one exponent less than $2$ and do not contribute. Hence $F_j^B(Rx)=F_j^A(x)$ for every $j$. The determinant argument gives independent $P_i\in\mathrm{SL}_{n_i}(F)$ acting identically on the copies within each group, and the data equation yields $A\cong_{\rm SL}B$. Conversely, such a special-linear transporter preserves the anchors, carries the data form, and extends by the identity on $s,t$ to a linear equivalence of $H_A,H_B$.

### Recovering tensors from circuit input

Consider circuits promised to compute these forms, with the tuple $(n_1,n_2,n_3)$ and the coordinate order specified. Let $j_*$ be the data index. For each coordinate triple $(i_1,i_2,i_3)$ set $x_{h,1}$ to basis vector $i_h$ in mode $h$ and set all remaining vector copies to zero. Evaluate the division-free circuit in the finite free $F$-algebra
$$
F[s,t]/(s^{\alpha+b_{j_*}+1},\ t^{\beta+c_{j_*}+1}).
$$
The coefficient of $s^{\alpha+b_{j_*}}t^{\beta+c_{j_*}}$ is the required trilinear entry. Other tagged terms and the scalar terms have distinct pairs of exponents. The quotient evaluation preserves the coefficient even when the circuit has larger intermediate degree and subsequent cancellations. Naive polynomial arithmetic in this quotient uses polynomially many field operations. Repeating over all triples recovers both tensors in polynomial time over explicitly represented finite fields. Over general fields this is a polynomial arithmetic-operation bound, with no uniform bit-length assertion for arbitrary coefficient encodings and circuits.

The result makes the missing computational implication precise. If ordinary linear equivalence of these specified circuit forms is in $\mathsf{TI}$, then so is $\mathsf{TI}_{\rm SL}$. The converse follows from reconstruction. General homogeneous circuit-polynomial equivalence already includes polynomial identity testing through pairs $(P,0)$, and the argument gives no reverse reduction from that general problem. This reduction bypasses the explicit exponentially large coefficient tensor of a volume form by keeping a circuit representation.

## A single homogeneous linear matrix pencil and its projective hypersurface

The circuit-form problem can be restricted further to ordinary linear equivalence of determinant polynomials of explicitly supplied homogeneous linear matrix pencils. The same reduction works for projective linear equivalence, where the determinant polynomial may be multiplied by any nonzero scalar. An instance in this classical formulation asks whether a coordinate change of the variables identifies the two determinant polynomials up to scalar. It imposes no matrix-row or matrix-column transporter on the linear representations.

An algebraic branching program is a directed acyclic graph with a designated source and sink, whose polynomial is the sum of the products of affine linear edge labels along source-to-sink paths. The Mahajan–Vinay determinant algorithm provides a polynomial-size, uniformly constructible branching program for each anchor determinant. Their dynamic program for signed partial clow sequences is a path sum, with a transition weighted by a signed matrix entry. Products are realized by serially concatenating programs. Sums are realized with disjoint paths between a new source and sink, joined by edges of weight $1$. Thus the tags, the trilinear monomials, the scalar-only terms and all anchors give a polynomial-size branching program for $H_A$. Include a branch for every explicit tensor coordinate, even when its coefficient is zero. Use the same branching-program topology for inputs of the same shape. [Mahajan and Vinay, Determinant: Combinatorics, Algorithms, and Complexity](https://scholar.lib.vt.edu/ejournals/CJTCS/cjtcs/articles/1997/5/cj97-05.pdf)

Let $M$ be its strictly upper triangular adjacency matrix in topological order, with one row and column per vertex. Let $u,v$ be the source and sink indices, and $e_u,e_v$ their coordinate vectors. The inverse $(I-M)^{-1}$ in the polynomial ring is the finite sum of powers of $M$, and its $uv$ entry is $H_A$. The matrix
$$
K_A=
\begin{pmatrix}
I-M & e_v\\
-e_u^{\mathsf T}&0
\end{pmatrix}
$$
has determinant $H_A$ by the block determinant identity, using $\det(I-M)=1$. Let $k$ be its matrix size and $d=3D+3=\deg H_A$. Since the entries of $K_A$ are affine linear and $H_A\ne0$, one has $k\ge d$.

Construct a homogeneous linear pencil by replacing each constant term in each entry of $K_A$ by that term times the existing variable $s$, and leaving the linear terms unchanged. This is the entrywise map $a_0+a_s s+a_t t+a_x(x)\mapsto(a_0+a_s)s+a_t t+a_x(x)$, involving no field division and adding no variable. In the localization at $s$ it equals the matrix $sK_A(1,t/s,x/s)$. Its determinant is therefore
$$
s^k H_A(1,t/s,x/s)=s^{k-d}H_A(s,t,x)
$$
by homogeneity, and equality holds also as polynomials. Adjoin the two extra diagonal entries $s,s$. The resulting explicit pencil has determinant $s^{k-d+2}H_A$. The exponent is shape-dependent only and is at least $2$. The new $s$ multiplicity $\alpha'=\alpha+k-d+2$ is strictly larger than $\beta$ and both are larger than $D$, so they still identify $s$ and $t$ individually. The dimensions and construction cost are polynomial in the tensor format and coefficient list.

For projective equivalence, allow an equality between the two output determinant polynomials after substitution with right-hand side a nonzero scalar $\rho$ times the source polynomial. Factor multiplicities again force $s'=\lambda s$, $t'=\mu t$, and $x'=Rx+us+vt$. In the two scalar coefficient comparisons, the right-hand sides are now both $\rho$ and the exponent $\alpha$ is replaced by $\alpha'$. Dividing these comparisons yields $\lambda=\mu$, and either then gives $\rho=\lambda^{\alpha'+\beta+D}$. Normalize the substitution by $\lambda^{-1}$. This removes the scalar $\rho$ with no root extraction, so the earlier tag proof applies verbatim. Conversely any special-linear transporter gives equality of the output determinant polynomials.

For a nonzero homogeneous form, equality up to scalar under linear substitution is equivalent to projective-linear equivalence of the embedded hypersurface subschemes. The principal homogeneous ideal of the form is saturated with respect to the irrelevant ideal. To see this, for each irreducible factor choose a coordinate not divisible by that factor, and test the multiplicity of the factor after multiplication by a power of that coordinate. Thus the subscheme retains the whole defining polynomial up to scalar. The argument uses this retention of multiplicities.

The reverse reduction on the displayed pencil family uses the same truncated coefficient extraction. The adjusted $s$ multiplicity is read from the total determinant degree, which is the matrix size, then subtracting $\beta+D$. Evaluate determinants without divisions in the truncated polynomial algebra. For a projective input promised to represent a nonzero scalar multiple of the described determinant polynomial, recover the multiplier as the coefficient of $s^{\alpha'+D}t^\beta$ after setting $x=0$, then divide the extracted data entries by it. This proves polynomial-time many-one equivalence of special-linear tensor isomorphism with either version of the displayed pencil family, with the stated presentation promises.

A sufficient classical hypothesis is that projective equivalence of arbitrary determinant polynomials of explicitly given homogeneous linear pencils belongs to ordinary $\mathsf{TI}$. This hypothesis addresses a broader class. Even restricting the broad problem to nonzero determinant polynomials still contains commutative symbolic determinant identity testing. Given a symbolic determinant $g(x)$, use the same two-variable construction with one data term $F_1=g$ of assigned degree equal to the matrix size, and compare with $F_1=0$. Give both branching programs the same topology by using a zero coefficient on the data branch of the second program. Both outputs are nonzero because of the scalar-only terms. The factor and tag proof, which does not require any particular list of anchors, shows these outputs are projectively equivalent exactly when $g=0$. This exhibits the relation to a classical unresolved algorithmic problem, without requiring an implication in the reverse direction from its general instances. [Ivanyos, Mittal and Qiao, Symbolic Determinant Identity Testing and Non-Commutative Ranks of Matrix Lie Algebras](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITCS.2022.87)

## Two distinctions from orbit-closure and invariant tests

### Full-support separation even inside the null cone

Use the matrix-map convention $B(fx)g=hA(x)$ for the transporter. Let $A(x)$ be diagonal with blocks $L_i(x)I_{m_i}$, forms the $r$ coordinate forms followed by their sum, and distinct positive multiplicities with total $N$. For $B=aA$, taking determinants and using distinct factor multiplicities gives $f=\lambda I_r$ in every transporter. Consequently special-linear equivalence holds over a given field exactly when some scalar $\lambda$ satisfies $\lambda^r=1$ and $(a\lambda)^N=1$. The converse transporter is $(\lambda I_r,I_N,a\lambda I_N)$. These tensors have injective label flattening and full row and column support since the pencil is generically invertible.

In characteristic different from two, take $r=3$ and weights $(5,1,2,3)$, which give $N=11$. The tensor $A$ is ordinarily isomorphic to $-A$ but is not special-linearly isomorphic even over the algebraic closure, because the two scalar equations imply $(-1)^{33}=1$. In characteristic two over a field with more than two elements, take $r=2$ and weights $(5,1,2)$, giving $N=8$. Any $a\ne0,1$ gives the same separation, since the equations force $\lambda=1$ and $a=1$ in characteristic two.

Both source and target belong to the special-linear null cone over the algebraic closure. For a direct proof use weight $(r-1,-1,\ldots,-1)$ on the label coordinates, with covariant action on entries, and let $v_i$ be the minimum weight among the coordinate terms in $L_i$. Thus $v_1=r-1$ and $v_i=-1$ otherwise. Put $S=\sum_i m_i v_i=rm_1-N$, which is positive in both examples. Multiply the label weights by $N$, put weight $S-Nv_i$ on each row coordinate in block $i$, and put weight zero on every column. Label weights sum to zero and row weights sum to $NS-N\sum_i m_i v_i=0$. The diagonal one-parameter subgroup with these weights belongs to the three special-linear groups. Each nonzero tensor entry has total weight at least $S>0$, so the subgroup sends the tensor to zero at parameter zero. The same holds for $aA$.

Thus all algebraic special-linear polynomial invariants take equal values on the pair, even though ordinary isomorphism holds and geometric special-linear orbit equality fails. This directly excludes an unrestricted test that combines ordinary TI only with invariant evaluations on the input tensors. The argument concerns algebraic group invariants, since invariant functions for the finite set of rational group points are a different invariant problem. For the published distinction between orbit equality and orbit-closure intersection, see [Lysikov and Walter, Questions I.11 and I.13](https://arxiv.org/html/2411.04639v2).

### An exact field-descent obstruction through power equations

Let $r\ge2$, and choose distinct positive multiplicities $m_1,\ldots,m_{r+1}$ with $r\mid N=\sum_i m_i$. Such multiplicities can be constructed by taking $m_i=i$ for $i\le r$ and adding an integer between $0$ and $r-1$ to the last multiplicity $r+1$. Use the same coordinate forms and their sum for $A$. Given $b\in F^\times$, set
$$
f_0=\operatorname{diag}(b^{-1},1,\ldots,1),\qquad
h_0=\operatorname{diag}(b^{-N/r},1,\ldots,1),\qquad
B(y)=h_0A(f_0^{-1}y).
$$
There is a rational ordinary transporter $(f_0,I,h_0)$. Over every extension $E/F$ we have the exact criterion
$$
A\cong_{{\rm SL}(E)} B\quad\Longleftrightarrow\quad b\in(E^\times)^r.
$$
Indeed, compose an ordinary transporter with the inverse of the displayed one to get an automorphism of $A$. Its label is $\lambda I_r$ by the same determinant-factor argument. For any such automorphism $(\lambda I_r,g,h)$, taking determinants gives $\det h=\lambda^N\det g$. Repairing the first determinant of $(f_0,I,h_0)$ to one requires $\lambda^r=b$. Given that equality, the automorphism $(\lambda I_r,I,\lambda I_N)$ repairs the third determinant as well, since $b^{-N/r}\lambda^N=1$. This proves both directions. For odd finite fields a nonsquare with $r=2$ already gives ordinary rational equality and special-linear geometric equality without special-linear rational equality. All algebraic special-linear invariants agree because the pair lies in one geometric special-linear orbit.

The reductions to circuit-form and determinant-polynomial equivalence are exact computational equivalences for their constructed families. General circuit-form or determinant-polynomial equivalence would need its own reduction to ordinary TI. Orbit-closure intersection also has a distinct specification. The classical complexity relationship outside the stated families remains open here. This is a paper proof with no Lean certificate. [Chen–Grochow–Qiao–Tang–Zhang, Open Question 1.9](https://arxiv.org/html/2306.03135v2#S1.SS5)
