# Modular cancellation for the rank markers of Futorny, Grochow and Sergeichuk

Fix a positive integer $h$ and put $b=3^h$. Consider **the actual one-axis augmentation** of FGS Lemma 2.2, over a field of characteristic three. It admits a constant-degree ordinary Polynomial Calculus (PC) decoder under the residue criterion below. Degrees depend on $h$, independently of the ambient dimensions. The test uses only indecomposable summands with a one-dimensional first row. It can distinguish marker multiplicities that are both zero in the base field. [FGS, Lemma 2.2](https://arxiv.org/html/1810.09219#S2) · [The original PC question](https://arxiv.org/html/2305.19320#S7.SS5)

## Statement

View a slice pencil as a quiver representation with one vertex for each row or column block and arrows from columns to rows for each slice. The slice space is $U=U_1\oplus\cdots\oplus U_s$, with nonempty blocks. $N_k$ is the representation supported at the first row and first column vertex with dimensions $1$ and $\dim U_k$. Its row of linear forms is the coordinate tuple of $z_k$ for $z\in U$. Writing $r=1+\min(n,m)$ for the FGS dimension parameter, the augmented source and target are
$$
 M=A\oplus\bigoplus_k N_k^{2^{k-1}r},\qquad
 M'=A'\oplus\bigoplus_k N_k^{2^{k-1}r}.
$$
The two remaining axis partitions are still respected at this stage. An ambient witness consists of vertexwise maps and inverses $P,P',Q,Q'$ on rows and columns, and $Z,Z'$ on slices, with $P M(z)=M'(Zz)Q$.

Over an algebraic closure, call an indecomposable type eligible if it has dimension one at the first row vertex and vanishes away from the first row and column vertices. For an eligible type $a$ in an augmented diagram let $t_a$ be its multiplicity and $p_a$ its dimension at the first column vertex. The row-only simple is included with $p_a=0$.

**Residue criterion.** For every source marker type $a=N_k$ and every eligible target type $d$, congruence of both pairs
$$
                (t_a,p_a)\equiv(t_d,p_d)\pmod b
$$
is allowed only if $d=N_k$ and $t_d=t_a$ as integers. More generally, fix a bound $B$ as well as $h$. One may disregard a candidate pair whenever one of its two coordinates has unequal values with minimum at most $B$. Thus all singleton arities are distinguishable from every larger arity without any congruence test. Make the same test with source and target exchanged. Multiplicities in this test include copies already present in the data.

**Theorem.** On inputs satisfying this criterion the augmented PC equations yield a polynomial substitution for the original partitioned-pencil transporter and its two-sided inverse, with bounded-degree derivations of every substituted equation. The augmentation has its usual bounded-degree forward substitution. Consequently if the criterion holds at each of the three single-axis steps, the partitioned pair and the ordinary FGS output pair are low-degree PC equivalent. Polynomial size holds for each fixed $h$ and fixed signature. This is a sufficient condition on the input diagrams.

## Visible matrix factors

Let $E=\operatorname{End}(M)$. For each diagram vertex $v$, let $V_v$ be its natural $E$-module and define $B_v(x,y)=\operatorname{tr}_{V_v}(xy)$. Set $I=\bigcap_v\ker B_v$, where each kernel is the left kernel of its bilinear form. Vertexwise conjugation gives an algebra map $\Psi:E\to E'$ with entries of degree two. Its inverse uses the inverse witnesses. Arrow relabeling by $Z$ leaves the space of endomorphisms unchanged, as one checks by using $Z'$ to range over the original arrows. Substituting the inverse identities in the trace shows that each $B_v$ is preserved. Expanding a target vector by $\Psi^{-1}$ therefore transports $I$ and the quotient algebra by bounded-degree PC operations.

The semisimple quotient of $E$ is $\prod_a\mathrm{Mat}_{t_a}$ over the algebraic closure. In $V_v$, the simple column module belonging to type $a$ occurs exactly $d_{av}=\dim a_v$ times. Indeed the primitive idempotent for one actual copy of $a$ acts with that rank on $V_v$, rank one on each corresponding simple factor, and rank zero on all other simples. Rank additivity for an idempotent through a composition series proves the multiplicity assertion on these fixed input modules. On the matrix factors $B_v$ is accordingly the sum of $d_{av}\operatorname{tr}(x_a y_a)$, since strictly upper triangular contributions have zero trace. The trace pairing on a full matrix algebra is nondegenerate in every characteristic. The quotient $E/I$ is thus the product of the factors with at least one $d_{av}$ nonzero modulo three. Each eligible type survives with $d_{a,\mathrm{row}}=1$ regardless of its multiplicity. These facts about constant algebras specify linear maps and identities on their given coordinates.

On the center of this quotient the induced isomorphism gives a Boolean permutation matrix $q_{da}$ over the PC variables. Indeed coordinate idempotents give idempotence, row collisions and row sums. Apply the same equations to the inverse. Multiplying an inverse equation by one entry and using row collisions in the two directions identifies the inverse with the transpose, giving column sums and collisions. Everything below on the component $q=q_{da}$ means multiplication of each equation by $q$, with $q^2=q$ at every use. This does not divide by a variable or assume the coordinate ring is reduced.

## How a single marker copy detects thin target types

Fix one projector $D_i$ onto an individual source copy of an eligible $a$. Its image on the first row is the witnessed conjugate of a fixed rank-one projector. All its $2$ by $2$ minors vanish by direct expansion of the outer product, and its trace is one. It vanishes on the vertices other than the first row and first column. Write $C_i$ for the component in the target $d$-factor of the semisimple visible quotient. Under $q$, the images of $D_i$ have no component at any other visible factor, since $D_i$ is supported on the $a$-factor modulo $I$. Thus
$$
                    q\,d_{d,\mathrm{row}}\operatorname{tr}(C_i)=q .
$$
A target type with $d_{d,\mathrm{row}}=0$ is excluded immediately. If this dimension is at least two, put the target first-row module in a fixed composition-series basis with all occurrences of each simple represented in its standard coordinates. Two occurrences of the $d$-simple give two diagonal blocks both equal to $C_i$, separated by a zero block below the diagonal. Take a minor with one row and one column from each occurrence. Its determinant is an arbitrary product of two entries of $C_i$. All such products vanish by the rank-one identity. Since $C_i^2=C_i$, all entries vanish and the trace equation gives $q=0$. If $d$ occurs at any vertex outside the first row and column, the transported projector is zero there and a diagonal block at that vertex is $C_i=0$, again giving $q=0$. This proves that eligible types can match only eligible types. Applying it to the inverse supplies the converse.

For a surviving pair we have $q\operatorname{tr} C_i=q$, $C_i C_j=0$ when $i\ne j$, and $q\sum_i C_i=q I_{t_d}$. The last identity is the image of the whole $a$-type projector on $d$. Each $C_i$ has all $2$ by $2$ minors zero by restriction to its one composition factor in the first-row module. These identities hold for arbitrarily many copies using a bounded number of polynomial factors per term.

## Reading base-three digits without taking a large determinant

For a matrix $S$, let $e_j(S)$ be the coefficient of $x^j$ in $\det(I+xS)$, the sum of its principal $j$-minors. Take $S=\sum_{i\le u} C_i$ and $C=C_{u+1}$. On $q$,
$$
                     e_j(S+C)=e_j(S)+e_{j-1}(S).
$$
Here is a bounded-degree justification. In a determinant expansion, terms using two or more columns of $C$ group by Laplace expansion into minors of $C$ of size at least two, each zero by its two-minor equations. The linear-in-$C$ contribution is $x\operatorname{tr}(\operatorname{adj}(I+xS)C)$. Modulo $x^{j+1}$ the inverse of $I+xS$ is its truncated geometric series. Since $SC=0$ and $q\operatorname{tr} C=q$, the contribution becomes $x\det(I+xS)$ on $q$. Each coefficient through $j$ uses at most $O(j)$ polynomial matrix factors. Expanding and multiplying the two-minor equations therefore gives ordinary PC derivations in degree $O(j)$ in the matrix entries, independent of $u$. One may also use formal coefficient identities for the adjugate at zero, avoiding the full determinant as a PC line.

Iterate the recurrence using the *linear expression* for each partial sum $S$. Each intermediate $e_j(S)$ has degree $j$ in the entries of the original $C_i$, so the degree does not accumulate with $u$. At the end,
$$
                q\left(\binom{t_d}{j}-\binom{t_a}{j}\right)=0 .
$$
For $j=3^e$, the coefficient of $x^{3^e}$ in $(1+x)^t=\prod_f(1+x^{3^f})^{t_f}$ is the $e$-th base-three digit $t_e$. Using $0\le e<h$ rejects every mismatch of multiplicities modulo $3^h$ by bounded-degree PC.

## Reading the arrow subspaces and cancelling

An eligible type $a$ has a row pencil represented by a surjective constant linear map $R_a:U\to k^{p_a}$. A common kernel in the column space splits off a column simple, so the asserted surjectivity holds even if the data was given without a normal form. Endomorphisms of $a$ are scalars, since the row maps span its column dual. On the actual $d$-isotypic sum the compression of $\Psi(D_i)$ equals $C_i$ tensored with the identity of one $d$ copy, using the decomposition into indecomposables. Its diagonal compression agrees with the matrix component just used because $\operatorname{End}(d)=k$.

For $z\in\ker R_a$, the source arrow applied to the column component of $D_i$ is zero. Transport and compress at the $d$ copies. This gives $C_i\otimes R_d Zz=0$. Taking trace in the copy indices and multiplying by $q$ gives $qR_d Zz=0$. The inverse equations give $qR_a Z'z'=0$ for $z'\in\ker R_d$. Thus on $q$ the map induced by $Z$ on the two quotient spaces $U/\ker R_a,U/\ker R_d$ has a witnessed inverse induced by $Z'$. Choose fixed linear sections of $R_a,R_d$ to write both maps as rectangular matrices. Their two products are the respective identities on $q$. Cauchy–Binet on their $j$-minors, followed by taking trace in either order, yields
$$
                 q\left(\binom{p_a}{j}-\binom{p_d}{j}\right)=0 .
$$
This includes cases where one side has dimension below $j$, since the corresponding alternating power is zero. Taking $j=3^e$ as above proves the arity part of the criterion.

For the bounded-minimum refinement, if $p_a<p_d$ take a single principal minor of order $p_a+1$ in the larger identity product. Cauchy–Binet makes it zero through the smaller space, whereas the identity minor is one on $q$. Similarly, if $t_a<t_d$, the matrix $qI_{t_d}$ is a sum on $q$ of $t_a$ matrices $C_i$ with all two-minors zero. Expand a principal minor of order $t_a+1$ by multilinearity in columns. Each summand takes at least two columns from the same $C_i$, so a Laplace expansion in those two columns gives zero. The inverse treats the opposite inequalities. For minimum at most $B$ these tests have degree bounded in terms of $B$.

Consequently the center equations identify each $N_k$ with itself whenever the input meets the criterion and no center column gives a contradiction. In particular $Z$ carries $\ker R_{N_k}$ into itself for every $k$, by the compressed arrow equations and the column sum. These kernels are the sums of all the other slice blocks. This makes $Z$ block diagonal and likewise for $Z'$. If any marker multiplicity differs, its center column has no surviving row and supplies a bounded-degree refutation.

For equal multiplicities, remove all marker types from both diagrams, obtaining the residual maps $a,b$ by projection of the transporter and its inverse. Their defects $1-ab$ and $1-ba$ square to zero. To see this, each double passage through deleted summands contains a map from a marker through the residual diagram to a marker. Once $Z$ is block diagonal its twist on each marker has the explicit inverse-transpose column change and identity row change. Substituting this and its inverse puts the middle passage in the two constant Hom spaces. Their compositions vanish. Different markers have zero Hom between them, and a nonzero scalar composition for an equal pair would split that marker off the residual diagram. These are bilinear identities on constant linear spaces. The repaired inverse $b(2-ab)$ is therefore a two-sided inverse, by direct multiplication. Reinsert the equal numbers of original data marker copies with their explicit twists. This proves reverse simulation. Extending a block-diagonal input transporter by the same twists proves the forward simulation. [Original cancellation argument, §§3–4](https://github.com/Dugongue/MathProofs/blob/main/FourRoutePolynomialCalculus/FGS-CANCELLATION.md)

The named marker summands and a splitting-off of all their copies are defined over the input field. The rank of the scalar composition pairing between the two constant Hom spaces for each marker gives their number and dual bases split them off. The residual pairing stays zero under field extension. Thus the final substitution uses input-field coefficients. Fixed-degree PC derivability descends from the algebraic closure, since linear spans, variable multiplication, and intersections with the degree-filtered polynomial spaces commute with scalar extension. Saturating in fixed degree has polynomially many monomials, hence polynomial-size derivations suffice.

## Two graph routes on the published FGS layouts

In fact the bounded-minimum argument alone works at every step of the following two FGS realizations, over **every characteristic**. Over an arbitrary field, retain the factors with some $d_{av}\cdot1_K\ne0$ in the natural trace forms after passing to an algebraic closure. Every eligible factor still survives because its row dimension is exactly one. The two-minor argument, rank-zero test at the other vertices, and minor contradiction through the smaller of two bounded dimensions use only coefficients $0,1,-1$. They need neither a division by a dimension nor an equality of base-three digits. The square-zero correction and linear descent also work in every characteristic. The graph-to-diagram comparisons can then be used in their stated characteristic. The orders of the FGS steps are specified here because the printed construction permits permuting the three tensor directions.

We use an observation about successive augmentations. Suppose a step using row $X$, column $Y$, and slice $Z$ attached the marker summands for the blocks $Z_k$. In the orientation with row $Z$, column $X$, and slice $Y$, each of their private $Y$ coordinates gives an arrow from one particular private $X$ coordinate $a$ to the coordinate vector $e_j$ of $Z_k$, with zero elsewhere. For fixed $a$ such arrows occur for all $j$ in $Z_k$. If $L,Q$ are a diagram endomorphism on row and column, those arrows give
$$
                  (L e_j)e_a^{\mathsf T}=e_j(e_a^{\mathsf T}Q).
$$
Reading the $a$ column shows that $L e_j=Q_{aa}e_j$ for all these $j$. Thus even when the row is now unpartitioned, its endomorphisms scale each old slice block by a single scalar. If these scalars are all equal and the row has dimension at least two, the entire data diagram has no eligible type. Otherwise the fixed projector on an eligible summand would have rank one on that row and also be a scalar matrix.

### Incidence code and the dotted link for diagonal conjugation

The incidence evaluation has tensor directions $X,Y,Z$ of dimensions $N,N,m$, with $N=3m+n$. A single dotted link imposes contragredience on $X,Y$ and leaves $Z$ independent. Use FGS Theorem 4.1, Case 1, on this single link. There is one extra singleton anchor on each axis. Write the original $Z$-block as $Z_d$ and its anchor coordinate as $z_0$. For the incidence matrix with three copies of the edge identity and the vertex incidence columns $c_i$, the linked partitioned tensor becomes
$$
           \sum_{i=1}^N x_i y_i(c_i^{\mathsf T}z+z_0)
                        +x_0y_0z_0 .
$$
The scalar anchor and the $X,Y$ identity in the $z_0$ slice are precisely the two fixed blocks of this construction. Remove partitions in cyclic order, with row/column/slice triples $(X,Y,Z)$, $(Z,X,Y)$, $(Y,Z,X)$. [FGS, Theorem 4.1, Case 1](https://arxiv.org/html/1810.09219#S4)

At the first step the eligible data types are the thin one-column pencils of weights $(c_i,1)$. The separate scalar summand lives at the second row and column vertices. Distinct weights give nonisomorphic summands, since the final weight entry is one. Every nonzero $c_i$ has multiplicity at most five, by the three private copies and the at most two degree-one endpoints of a simple edge. A vertex of degree at least two has a unique incidence column. When $c_i=0$, the resulting type is already the singleton marker $N_2$. Assume the two inputs have equal numbers of isolates. Then its extra multiplicity agrees on the two inputs. For $m\ge2$, the two marker arities $m,1$ are distinguished by the bounded-minimum test. The singleton marker has more than five copies and cannot match an eligible data type of multiplicity at most five. The first marker has arity $m$ and cannot match a data type of arity one. This verifies cancellation of the first step with $B=5$.

At the second step the preceding private arrows force the row endomorphism on $Z$ to be $\lambda I$ on $Z_d$ and $\mu$ on $kz_0$, by the observation above. A slice at an old $y_i$ has precisely one nonzero column, the vector $(c_i,1)$ at $x_i$. Its intertwining equation makes $(c_i,1)$ an eigenvector. There is a nonzero $c_i$ since $m\ge2$, so $\lambda=\mu$. The row has dimension $m+1$, hence no eligible data types. The $Y$ partitions are the enlarged first block and the untouched singleton $y_0$. The two new marker arities are again distinguished with $B=1$.

At the third step the second-step private arrows force the row endomorphism on $Y$ to scale the enlarged old $Y$ block by $\lambda$ and the old singleton by $\mu$. The old $x_0$ slice takes precisely the $z_0$ coordinate to the $y_0$ vector. In addition, a first-step private $X$ coordinate belonging to the singleton $z_0$ marker gives a slice taking precisely that same $z_0$ coordinate to a private vector in the enlarged old $Y$ block. The second augmentation used fresh $X$ coordinates for its own markers, so both arrow descriptions still hold. The two equations for the same row $e_{z_0}^{\mathsf T}Q$ of the column endomorphism give $\lambda=\mu$. Again there are no eligible data types. The $X$ partitions are one enlarged block and the untouched singleton $x_0$. The two arities distinguish their markers with $B=1$. This proves all three cancellations, with no residue assumption on the sizes.

For the remaining linked identities, let $R,S,U$ be the maps on the large blocks and $a,b,c$ their singleton scalars in FGS's trilinear convention. The anchor gives $abc=1$, and the dotted identity gives $c R^{\mathsf T}S=I$. Normalize the transformations to $R/a,S/b,U/c$ using their singleton inverse witnesses. The data equation is unchanged since $abc=1$, and $(R/a)^{\mathsf T}(S/b)=I$ follows from the two displayed scalar identities. Conversely the linked input maps extend by singleton identities. This supplies the actual conjugation equation in the diagonal Lie route.

For $m=0$ or $m=1$, any two simple graphs with equal $n,m$ admit an explicit fixed isomorphism. For larger $m$, the conclusion includes every equal-isolate-count pair. A common preprocessing comparing isolate counts or the pendant construction in the incidence proof supplies the respective extended formulations. [Incidence recovery and preprocessing](Incidence.md)

### The multiplication tensor and Corollary 3.3

Let $T$ be an arbitrary $d\times d\times d$ array with linked action $(S,S,S^{-\mathsf T})$. The actual FGS Corollary 3.3 layout is
$$
                K=T(x,y,z)+x_0\langle y,z\rangle
                                  +y_0\langle x,z\rangle
$$
with $X,Y$ partitioned into their $d$ original coordinates and one singleton each. $Z$ is unpartitioned. Remove $Y$ first using row $Z$, column $X$, then remove $X$ using row $Y$, column $Z$. For $d\ge2$ the following checks verify the bounded-minimum test with $B=1$ in both stages. [FGS, Corollary 3.3](https://arxiv.org/html/1810.09219#S3)

At the first step the column endomorphism on the separate vertex $x_0$ is a scalar. In the slice at $y_i$ the column $x_0$ is exactly $e_{z_i}$. Its intertwining equation forces the row endomorphism to multiply every $e_{z_i}$ by that same scalar. Hence the data has no eligible type, independently of the entries of $T$. The new marker arities are $d$ and one.

At the second step the preceding private arrows force the row endomorphism on $Y$ to scale its $d$ original coordinates by $\lambda$ and $y_0$ by $\mu$. Let $J$ project the column space onto the old $Z$ coordinates, along the added private coordinates. The $x_0$ slice has only the old identity from those coordinates to the original $Y$ block. Its equation gives $JQ=\lambda J$. In the old $x_i$ slice, the row at $y_0$ is the functional reading old $z_i$. Reading this output row in its equation gives $e_i^{\mathsf T}JQ=\mu e_i^{\mathsf T}J$. Thus $\lambda=\mu$. There are no eligible data types and the new $X$ partitions consist of one enlarged block and the singleton $x_0$. Both cancellations follow. For $d=1$ all marker and data dimensions in both steps are bounded absolutely, so one can use the general criterion with $B$ larger than all of them. Integer equality of arities and multiplicities then tags the markers by the disjoint FGS multiplicity intervals, irrespective of the scalar data.

For clarity, let $R,S,U$ be the three large maps on $K$ and $r,s$ the singleton scalars on $X,Y$. Its two identity blocks give $sR^{\mathsf T}U=rS^{\mathsf T}U=I$. Thus $S=(s/r)R$ and $U=s^{-1}R^{-\mathsf T}$. In the data tensor equation the triple $(R,S,U)$ can now be replaced by $(R/r,R/r,(R/r)^{-\mathsf T})$, since the three scalar factors multiply to $1/r$ in both expressions. The inverse variables for the singletons give all the reciprocals in bounded degree. In the forward direction take $r=s=1$. This proves a two-way low-degree comparison for the printed algebra tensor construction with these partition removals, including Grigoriev's graph algebras. [Graph algebra calculation](Algebra.md)

## Unbounded examples for the printed gadget

Take two one-dimensional slice blocks and a square data pencil $(I,J)$ of size $n=18d+2$, where all Jordan blocks of $J$ have size at least two, over the algebraic closure. Each indecomposable data summand has row dimension at least two, by the Jordan decomposition of the pencil with invertible first slice. The only eligible types in its augmentation are the two markers. Their multiplicities $n+1$ and $2(n+1)$ are both zero modulo three, and are $3$ and $6$ modulo nine. The criterion with $h=2$ gives a constant-degree two-way PC simulation on every pair of these inputs, uniformly in $d$ and in the choice of the two Jordan forms. Here the higher digit distinguishes markers of identical arity.
