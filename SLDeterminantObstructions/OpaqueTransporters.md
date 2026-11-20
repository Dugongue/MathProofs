# A query lower bound for extracting determinant information from ordinary tensor transporters

## Oracle and theorem

Let $q=7^{2j+1}$ with $j\ge1$ and $K=\mathbf F_q$. The input consists of opaque handles for two $2\times12\times12$ tensors over $K$ and one public ordinary transporter between them. Use the pencil convention that a transporter $(P,G,H)$ satisfies
$$
 B(Pw)G=HA(w)\qquad(w\in K^2),
$$
with $P\in\operatorname{GL}_2(K)$ and $G,H\in\operatorname{GL}_{12}(K)$. A special-linear transporter has determinant one in all three modes. This convention gives the same determinant-one condition as the covariant three-tensor convention.

The oracle supports the following calls.

- Unpinned ordinary isomorphism, exact unpinned transporter count, and an ordinary witness. A witness may be any correct transporter, so an algorithm requesting one must work for all choices of witness.
- A list of full-vector label pins $Px_i=y_i$ for specified $x_i,y_i\in K^2$. The oracle can give the existence, exact count, or a witness of the compatible ordinary transporters. When the list contains a nonzero input vector, it can also impose any specified additional predicate on the two matrix-mode maps.
- Membership of a fully specified triple $(P,G,H)$ in the ordinary transporter set.
- Optionally, the rank of a single contraction of either tensor in any one mode.

A query can use the two handles in either order, compare a handle with itself, or apply specified invertible maps to the handles first. The answer concerns only those tensors and their specified transforms.

**Theorem.** There is an explicit promise family of pairs of regular pencils for which every deterministic exact algorithm requires at least $\lceil q/2\rceil$ queries without contraction ranks. Every randomized algorithm with error at most $\epsilon<1/2$ on each promised input requires at least $(1-2\epsilon)q/4$ worst-case queries in the same model. With single-contraction rank queries the bounds are $\lceil q/6\rceil$ and $(1-2\epsilon)q/12$, respectively. The ordinary transporter count and a public ordinary witness are the same throughout the family. The sizes of the tensor modes are fixed, so each bound is exponential in $\log q$.

## Pencils with different determinant images and equal orbit counts

Use projective coordinate $z=x/y$ on the label line. For a list of six distinct finite roots $r_1,\ldots,r_6$, define the pencil
$$
  A(x,y)=\bigoplus_{i=1}^6 (x-r_i y)I_{m_i},
  \qquad
  (m_1,m_2,m_3,m_4,m_5,m_6)=(1,1,2,2,3,3).
$$
Its generic rank is $12$, and the drop at $r_i$ has size $m_i$. A projective label automorphism must preserve each of the three pairs of roots of its own drop size.

For the positive type start with the three pairs $\{1,-1\},\{2,-2\},\{3,-3\}$ in the prime field. The projective involution $z\mapsto-z$ swaps both roots in each pair. For the negative type use $\{1,-1\},\{2,3\},\{4,5\}$. The involution $z\mapsto-1/z$ swaps both roots in each of those pairs over $\mathbf F_7$. In each case the color-preserving projective group contains only the identity and the displayed involution. To see this, the cross-ratio convention
$$
 [a,b;c,d]=\frac{(a-c)(b-d)}{(a-d)(b-c)}
$$
gives $4$ for the first two positive pairs in the displayed order and $3$ for the first two negative pairs. These values both differ from their inverses in $\mathbf F_7$. Interchanging exactly one pair would invert the cross-ratio and is impossible. Fixing both pairs pointwise forces the identity because a projective map fixing three distinct points is the identity. Swapping both pairs is realized by the displayed involution and determines it uniquely by images of three points.

Let $A_+^0,A_-^0$ be the two pencils so defined and choose representatives
$$
 S_+^0=\begin{pmatrix}1&0\\0&-1\end{pmatrix},
 \qquad S_-^0=\begin{pmatrix}0&-1\\1&0\end{pmatrix}.
$$
For $S_+^0$, the simultaneous swap $R$ of the two blocks in each pair gives
$$
 A_+^0(S_+^0 w)R=R A_+^0(w).
$$
Here $\det R=(-1)^{1+2+3}=1$. The negative involution also lifts, since its label change carries each linear form to a nonzero scalar times the form for the corresponding equally sized block. The block permutation and these block scalars give the required invertible row and column maps. For the positive representative the determinant triple is $(-1,1,1)$. The negative representative has label determinant $1$.

Fix a public $\alpha\in K\setminus\mathbf F_7$, and let $Q$ represent $z\mapsto 1/(z-\alpha)$. It sends $\alpha$ to infinity. The point $\alpha$ lies in none of the six roots and is fixed by neither involution. For the negative involution this also follows from $q\equiv3\bmod4$, which makes $-1$ a nonsquare in $K$. Write $S_\pm=Q S_\pm^0 Q^{-1}$. Both $S_\pm$ have nonzero lower-left entry because neither fixes infinity.

Choose a block-scalar invertible $D_\pm$ so that $D_\pm A_\pm^0(Q^{-1} e_1)=I_{12}$, and write
$$
 U_a=\begin{pmatrix}1&a\\0&1\end{pmatrix},\qquad
 A_{\pm,a}(w)=D_\pm A_\pm^0(Q^{-1}U_a^{-1}w)
 \quad(a\in K).
$$
Their $x$-coefficient is $I_{12}$ since $U_a^{-1}e_1=e_1$. They have six finite, distinct roots, translated by $a$ from the six roots of $A_{\pm,0}$. The two projective label classes of their stabilizers are $I_2$ and $S_{\pm,a}=U_aS_\pm U_a^{-1}$. Scalar labels lift, and each $S_{\pm,a}$ lifts by applying the coordinate and monomial basis changes to the original lift. Their determinant triples are unchanged under conjugation in the three factor groups.

For either type and every $a$, the subgroup lying over the identity projective label is the same subgroup
$$
 D=\{(\lambda I_2,X,\lambda X):
       \lambda\in K^\times,\
       X\in \operatorname{GL}_1(K)^2\times
             \operatorname{GL}_2(K)^2\times\operatorname{GL}_3(K)^2
       \text{ in the indicated block order}\}.
$$
Indeed the first slice forces $H=\lambda G$, and the second says that $G$ commutes with its diagonal coefficient matrix. The six eigenvalues are distinct across the six indicated blocks, which identifies that centralizer. The entire stabilizer is the disjoint union of $D$ and one coset of $D$ over $S_{\pm,a}$.

Set $W=\operatorname{diag}(1,-1)$ and $B_{\pm,a}(w)=A_{\pm,a}(W^{-1}w)$. The public ordinary transporter is $(W,I_{12},I_{12})$, and the full ordinary transporter set has size $2|D|$. The class above the projective identity of the source becomes the common transporter coset $(W,I_{12},I_{12})D$. A positive input has a special-linear transporter because its extra source lift has determinant triple $(-1,1,1)$, which cancels the public witness determinants. A negative input has none. Both source projective classes in the negative case have square label determinants, including all scalar representatives, whereas $\det W=-1$ is a nonsquare.

## What each query can reveal

For either sign, write $S_\pm=\begin{pmatrix}r&s\\t&u\end{pmatrix}$, where $t\ne0$. Then
$$
 S_{\pm,a}
  =\begin{pmatrix}
       r+at & s+a(u-r)-a^2t\\
       t & u-at
    \end{pmatrix}.
$$
The extra transporter labels have the form $W\lambda S_{\pm,a}$ for $\lambda\in K^\times$. They have pairwise distinct projective classes as $a$ varies within a sign. This follows because the lower-left entry of $S_{\pm,a}$ is fixed and nonzero, so equality up to scalar forces equality, and the upper-left entry recovers $a$. Accordingly a fully specified transporter query can encounter the extra coset for at most one value of $a$ per sign.

Consider a full-vector pin $Px=y$ with $x\ne0$. The pin can be satisfied by an extra label only if $y\ne0$, and then $S_{\pm,a}x$ must be collinear with $w=W^{-1}y$. The determinant of these two vectors is a polynomial of degree at most two in $a$. It is nonzero as a polynomial. If both second coordinates $x_2,w_2$ are nonzero, its quadratic coefficient is $-t x_2 w_2$. If exactly one is nonzero, its linear coefficient is either $t x_2 w_1$ or $t x_1 w_2$, both nonzero in the respective cases. If both second coordinates vanish, its constant term is $-t x_1w_1\ne0$. Thus a query with any nonzero full-vector pin can encounter the extra coset for at most two shifts per sign. This remains true with more pins or additional predicates on $G,H$.

Unpinned existence and count agree on all instances. The unpinned witness may always be the fixed public witness. Pins with no nonzero $x_i$ are either inconsistent or vacuous and also agree on all instances. In any query looking at membership, existence or counts under nonvacuous pins, the answer from the common coset agrees with both actual answers whenever no extra transporter contributes. A valid witness in that common coset can also be selected identically for both signs. These statements remain true for the reversed and self-comparison calls and the invertible transforms allowed by the oracle. One can pull the specified transporters or pins back to the original pair by multiplying the known maps and its public witness on the two sides. In the label mode full-vector pins stay full-vector pins.

A rank call contracting at a nonzero label vector reports $12$ unless its projective direction is one of the six translated finite roots. For any fixed direction this has at most six possible shifts within each sign. At the zero label vector the rank is always zero. A rank call contracting in a matrix mode is independent of both sign and shift. In the original block coordinates the two rows or columns remaining after contraction have rank zero if the contracted vector is zero, rank one if it is supported on just one block, and rank two if it has a nonzero coordinate on at least two blocks. The last fact follows from distinctness of the six scalar eigenvalues. Applying known invertible maps amounts to pulling back the contracting vector and leaves the ranks of the resulting matrices invariant.

## Common-transcript argument

Simulate the unpinned answers by the common affirmative answer, the public witness or transporter count $2|D|$, as appropriate. For the pinned and membership calls simulate only the common coset. Where an ordinary witness is requested select a fixed witness from that coset when one exists. Simulate rank calls by generic rank rather than a root drop and by the block-support ranks in the other modes. This simulation is only a reference transcript and need not define an actual promised input. For each sign independently, every query on this transcript can differ from a real answer for at most $b$ hidden shifts, with $b=2$ without ranks and $b=6$ with ranks.

For a deterministic algorithm, on the simulated path of length $T$ there are at most $bT$ shifts of each sign where any answer differs. If $bT<q$, some positive and some negative input follow the full common path, contradicting correctness of its single output. For randomized algorithms condition on the internal coins and choose the hidden shift uniformly. The probability of any deviation from the reference transcript in either sign is at most $bT/q$. Thus the difference of the positive and negative acceptance probabilities averaged over shifts is at most $2bT/q$. Correctness on every input requires this difference to be at least $1-2\epsilon$. These inequalities prove all stated bounds. A fixed selection rule that gives priority to common-coset witnesses makes the witness replies legal throughout this argument.

## Scope

The hypotheses concern access to opaque tensors through specified ordinary transporter queries. They leave the general reduction in Open Question 1.9, which has raw tensor inputs and can construct fresh TI instances, outside the oracle theorem. The same promise family becomes easy with raw coefficients. For example, the common block order lets one recover the two translated root lists by reading the diagonal coefficients, and compare them to the known lists. Arbitrary pinning restricted solely to the matrix modes, uniform sampling from the full transporter coset, and fresh auxiliary tensor constructions are outside the model as stated. [Chen, Grochow, Qiao, Tang and Zhang, *On the complexity of isomorphism problems for tensors, groups, and polynomials III*, Open Question 1.9](https://arxiv.org/html/2306.03135v2#S1.SS5).

The proof is informal. Its algebraic computations and transcript bounds are independent of any Riemann hypothesis.


## Full-vector pins in all three modes

The same $\Theta(q)$ query bound holds in a larger decision-and-count model. Permit exact vector pins in the domain and codomain modes as well, simultaneously with any label pins, and permit existence and exact counting of ordinary transporters satisfying all of them. Continue to allow witnesses for unpinned queries or queries with a nonzero label input pin. For matrix-mode pins with no nonzero label input the replies are existence and count.

More precisely, with all three modes available, the deterministic lower bound is $\lceil(q-1)/2\rceil$ without ranks and $\lceil q/6\rceil$ with ranks. The randomized bounds for error at most $\epsilon<1/2$ are $(1-2\epsilon)(q-1)/4$ and $(1-2\epsilon)q/12$, respectively. The promise family still consists of $2\times12\times12$ regular pencils with the same public ordinary witness and unpinned count.

To prove this version, let $\pi$ be the fixed permutation exchanging the blocks in each pair, and let $R$ again be its simultaneous block permutation. For each $S_{\pm,a}$, write $\kappa_\pm$ for the scalar such that $S_{\pm,a}^2=\kappa_\pm I_2$; here $\kappa_+=1$ and $\kappa_-=-1$. The extra source lift can be written
$$
 (S_{\pm,a},R,\operatorname{diag}(\rho_1 I_{m_1},\ldots,\rho_6 I_{m_6})R).
$$
In fact, writing $l_i(w)$ for the scalar linear form in block $i$, one has
$$
 l_i(S_{\pm,a}w)=\rho_i l_{\pi(i)}(w),\qquad
 \rho_i\rho_{\pi(i)}=\kappa_\pm .
$$
The product identity follows by applying the first equation twice. Independently scale the output coefficient block $i$ by a nonzero scalar $\eta_i$. This changes $\rho_i$ to $(\eta_i/\eta_{\pi(i)})\rho_i$ and leaves all root directions unchanged. Thus the family can use every possible choice of one $\rho_i\in K^\times$ per pair, with the other determined by the displayed product. Use the uniform distribution on the three independent choices in the proof. Such output changes preserve the stabilizer determinant images by conjugation. They also preserve the common subgroup $D$, since their block scalars commute with all block-diagonal $X$ in $D$. Redefine $B$ from this adjusted $A$ by the same fixed $W$, so the common transporter coset also persists.

For a matrix-mode pin query, the elements of the extra transporter coset have the form
$$
 \big(W\lambda S_{\pm,a},\ RX,\
        \lambda\operatorname{diag}(\rho_1 I_{m_1},\ldots,\rho_6 I_{m_6}) RX\big),
 \qquad \lambda\in K^\times,\quad X=\bigoplus_i X_i.
$$
For each block, the domain pins prescribe $X_i$ on a subspace $A_i$, and the codomain pins prescribe $s_{\pi(i)}X_i$ on a subspace $B_i$, where $s_{\pi(i)}=\lambda\rho_{\pi(i)}$. This is simply the blockwise reading of each prescribed equation on a full vector. Let $\gamma_i,\beta_i$ be the prescribed maps on $A_i,B_i$, respectively. Inconsistent or noninjective prescriptions in either individual group give no extensions. Otherwise an invertible $X_i$ exists if and only if $\gamma_i$ and $s_{\pi(i)}^{-1}\beta_i$ agree on the intersection and define an injection on the sum.

If $A_i\cap B_i$ is nonzero, evaluation at a nonzero vector in the intersection gives at most one admissible scalar $s_{\pi(i)}$. If it is zero, injectivity on the sum is equivalent to disjoint images of the two subspaces, independent of $s_{\pi(i)}$. The feasible scalars in each block thus form an empty set, all of $K^\times$, or a singleton. For any feasible scalar the number of extensions to invertible $X_i$ depends only on $\dim(A_i+B_i)$ and the block dimension. Any two injections on that fixed subspace are related by an invertible map of the target, giving a bijection of extensions. Hence this number is independent of the hidden parameters and the chosen feasible scalar.

Consider a query with matrix-mode pins and no nonzero label input pin. A vacuous label condition contributes no constraint, and an inconsistent one has zero compatible transporters. If any block scalar is infeasible, the extra contribution is zero. If every block allows all scalars, the extra count is a fixed block-extension product multiplied by $q-1$. If exactly one block imposes a specific scalar, it determines exactly one $\lambda$ for every choice of the hidden signs and ratios, so the extra count is the same fixed block-extension product. In the other cases choose any two blocks requiring $s_i=c_i$ and $s_j=c_j$. These constraints force
$$
 \rho_i/\rho_j=c_i/c_j.
$$
For blocks in distinct pairs, the two ratios are independent uniform elements of $K^\times$ and the relation has probability $1/(q-1)$. For blocks in one pair it becomes a quadratic equation for the one independent $\rho_i$, with probability at most $2/(q-1)$ for either sign. Thus the answer predicted by retaining the common coset and the stated constant extra contributions differs from the true answer with probability at most $2/(q-1)$ for each sign. This applies to counts and therefore to existence.

Label-bearing pins and fully specified membership calls have the same exceptional probabilities $2/q$ and $1/q$ as before under a uniform hidden $a$. These bounds hold independently of the hidden block ratios. Contraction ranks are also unchanged by the extra output scalings. For each fixed query on the reference transcript, the exceptional probability under either sign is at most $2/(q-1)$ without ranks and $6/q$ with ranks. The same common-transcript argument, using a union bound over the hidden shift and block ratios, gives the claimed bounds. Reversed and transformed calls reduce to full-vector pins in the displayed convention. In particular a pin of an inverse map $g^{-1}x=y$ becomes the pin $gy=x$.

The restriction on matrix-only pinned witnesses has a direct witness distinction for this family. Pin the entire domain map to $R$. This fits the extra coset and excludes the common coset. Any ordinary witness for these pins has square label determinant on positive inputs and nonsquare label determinant on negative inputs. Thus one such call would decide this family. Witnesses for unpinned calls can always be the public witness, and witnesses for nonzero label-bearing pins obey the exceptional-probability bound.

There is a matching $O(q)$ query upper bound in either model. For each $a\in K$, use pins on a full label basis to test whether $W S_{+,a}$ is an available label. All these labels lie outside the common projective class. Their determinants are squares, whereas the negative family has only nonsquare label determinants. Some test succeeds precisely on a positive input.


## Comparisons against freshly constructed explicit tensors

One may additionally permit arbitrary ordinary TI tests involving newly constructed explicit tensors, as well as comparison of any such explicit tensor with a hidden handle or its specified invertible transform. Fresh inputs are specified by raw coefficients chosen by the algorithm. The oracle may answer existence, exact count, or return any witness for these comparisons. The algorithm may use the returned data to choose subsequent explicit tensors. This model still restricts operations on an opaque handle to the specified invertible transformations and oracle queries.

Vary a fourth hidden parameter $b\in K$. In the positive type replace the size-two pair $\{2,-2\}$ by $\{b,-b\}$. In the negative type replace $\{2,3\}$ by $\{b,-1/b\}$. Keep the size-one and size-three pairs fixed. Exclude values yielding a repeated root, zero $b$, or a root equal to the public $\alpha$. At most seven values are excluded per sign. In the positive case these are contained in $\{0,\pm1,\pm3,\pm\alpha\}$. In the negative case they are contained in $\{0,\pm1,4,5,\alpha,-1/\alpha\}$. In either case the second pair is distinct because the characteristic is odd and $-1$ has no square root. After moving $\alpha$ to infinity, the six roots are still finite.

For the ordered first two colored pairs the respective cross-ratios are
$$
 \chi_+(b)=\left(\frac{1-b}{1+b}\right)^2,\qquad
 \chi_-(b)=-\left(\frac{1-b}{1+b}\right)^2.
$$
These values differ from their inverses on the allowed set. In fact, $\chi_+(b)$ is a square, and can equal $1$ only at the excluded value $b=0$. It cannot equal $-1$, which is a nonsquare. Hence neither $\chi_+$ nor $\chi_-$ equals $1$ or $-1$. All the preceding stabilizer and query calculations apply with these new pairs and any allowed $b$. In particular the same involutions act, the block permutation is fixed, and the auxiliary scalars can again range independently subject to their pair-product conditions.

Any explicit tensor isomorphic to a hidden handle must have a full pencil of the same dimensions whose six rank-drop directions lie in three pairs, with the same three drop ranks. In particular its first two colored pairs must have the same cross-ratio up to reciprocal, independent of the chosen order within each pair. The known invertible transforms and the hidden additive shift do not change this unordered cross-ratio. For a fixed value $\xi$, each equation $\chi_\pm(b)=\xi$ is a nonzero polynomial equation of degree at most two after clearing the denominator. There are at most four allowed $b$ per sign for which its cross-ratio agrees up to reciprocal. Thus for any fixed explicit tensor an ordinary-isomorphism comparison with a hidden handle is affirmative with probability at most $4/(q-7)$ for either sign when $b$ is uniform on its allowed values.

The reference transcript can answer comparisons of a hidden handle against an independently specified explicit tensor with a negative decision, zero count, or no witness. The fresh-to-fresh comparisons are independent of the input and can be simulated by any fixed correct rule. For queries on the hidden pair alone use the earlier simulation. Its probability of a differing answer is at most $4/(q-7)$ per query without ranks and $6/q$ per query with ranks, since $q\ge343$. The same adaptive coupling then gives the deterministic lower bounds
$$
 \left\lceil\frac{q-7}{4}\right\rceil
 \quad\text{and}\quad
 \left\lceil\frac q6\right\rceil
$$
without and with ranks, respectively. The randomized bounds are $(1-2\epsilon)(q-7)/8$ and $(1-2\epsilon)q/12$. The $O(q)$ fixed-label upper bound is unchanged, since the matrices $S_{\pm,a}$ are independent of $b$.

## Finite-field controls

Over $\mathbf F_{343}=\mathbf F_7[\alpha]/(\alpha^3-2)$, both of the original six-point configurations were evaluated under every one of the $343$ shifts. The calculations covered all $344$ possible projective input directions and all $343$ shifted involutions for each sign, for $117{,}992$ pin images per sign. The largest pin collision count was two and every finite rank-drop direction arose from exactly six shifts. Separately, exhaustive enumeration of the $48$ invertible $2\times2$ matrices over $\mathbf F_3$ confirmed the constant-extension-count assertion for all $1{,}069{,}443$ pin systems with one full-vector constraint in one mode and one or two in the other.
