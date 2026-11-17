# Linear and quadratic models for monomial matrices

The final list of open questions in Horlemann, Mazumder, Schaller, and Weger’s *A Survey on Code Equivalence* asks for linear equations enforcing the monomial constraint in its algebraic model of code equivalence. A single affine-linear system cannot express this constraint in general, even with auxiliary variables. Without an invertibility promise the exact number of systems required by a disjunction is $n!(q-1)^n$ for $q>2$ and $n!/2^{\lfloor n/2\rfloor}$ for $q=2$. Exponentially many are still needed with invertibility and the code-compatibility constraints supplied. There is a quadratic model with $O(n^2)$ equations and a unique auxiliary witness for each monomial matrix. [Published question](https://arxiv.org/html/2607.12870v2#S6.SS6) [Algebraic model](https://arxiv.org/html/2607.12870v2#S5.SS1)

## Model and exact disjunctive complexity

Let $k=\mathbb F_q$, $n\ge 1$, and $\mathcal M$ be the set of $n\times n$ matrices with one nonzero entry per row and column. A linear branch is a system of affine-linear equations over $k$ in the matrix entries and any number of auxiliary field variables. It accepts a matrix when the equations have a solution for its auxiliary variables. The accepted set is empty or an affine flat in $k^{n\times n}$, since a coordinate projection of an affine flat is affine. Conversely every affine flat is defined by affine-linear equations. The disjunctive counts below concern an exact union in $k^{n\times n}$.

Suppose first that $q>2$. An affine flat consisting of monomial matrices cannot contain two distinct matrices $A,B$. If their support permutations differ, choose a row in which their supports differ and take $t\in k\setminus\{0,1\}$. The row of $(1-t)A+tB$ has two nonzero entries. If their support is the same and one position has distinct values $a,b$, set $t=a/(a-b)$ to make that entry vanish. The entire row is then zero. Thus each branch contains at most one matrix, and singleton branches realize the bound $n!(q-1)^n$.

Over $\mathbb F_2$ the monomial matrices are precisely permutation matrices. Multiply an affine flat of permutation matrices on the right by the inverse of one of its members to obtain an affine flat containing the identity $I$. For any two members $P,Q$, the matrix $I+P+Q$ is in the flat. Write $P(i)$ and $Q(i)$ for the columns selected by their $i$th rows. If $P(i)\ne i$ and $Q(i)\ne i$, the $i$th row of $I+P+Q$ can have weight one only if $P(i)=Q(i)$. Their common image is also moved by both permutations, because neither can move a point to a distinct point that it fixes. Iteration shows that the cycle of $i$ is identical in both permutations.

Consequently all distinct nontrivial cycles that occur among the members have disjoint supports. If these cycles are $c_1,\ldots,c_m$ with permutation matrices $P_1,\ldots,P_m$, the flat is contained in
$$
I+\operatorname{span}_{\mathbb F_2}\{I+P_1,\ldots,I+P_m\}.
$$
In this larger flat, a subset of the cycles is applied by setting the corresponding coefficients to one. Every resulting matrix is a permutation matrix, since the cycle supports are disjoint. This also classifies the original flats as linear subspaces of cycle choices after normalization by a base member. The dimension is at most $m\le\lfloor n/2\rfloor$. Independent transpositions on $\lfloor n/2\rfloor$ disjoint pairs attain the bound. The subgroup they generate has affine cosets covering all permutation matrices, because multiplication by a fixed permutation matrix is linear on the ambient matrix space. The lower bound by counting and this covering give the exact minimum $n!/2^{\lfloor n/2\rfloor}$.

In particular a single linear branch works without an external promise exactly when $q=2$ and $n\le 2$.

## Allowing invertibility or the original code equations

The original algebraic model first imposes $GMH'^{\mathsf T}=0$, where $G$ generates the source code and $H'$ is a parity-check matrix of the target. It is also natural to supply the external restriction $M\in\mathrm{GL}_n(k)$. This changes the question to whether the accepted invertible matrices can be described by an affine flat intersected with $\mathrm{GL}_n(k)$. The disjunctive counts above are for an unconstrained ambient space. For example a single diagonal affine flat now covers all invertible diagonal matrices.

For $q>2$, all of $k^{n\times n}$ is the affine hull of $\mathcal M$. For each position $(i,j)$, take a permutation with that position in its support and take two monomial matrices with that support differing only at $(i,j)$. Their difference is a nonzero multiple of the corresponding matrix unit. Hence any affine flat containing $\mathcal M$ contains all invertible matrices, including $I+E_{12}$ when $n\ge 2$. In dimension one every invertible matrix is monomial.

For $q=2$, the affine hull of the permutation matrices is the space of matrices with all row and column sums equal to one. Indeed the differences
$$
E_{ij}-E_{in}-E_{nj}+E_{nn}\qquad (i,j<n)
$$
are differences of permutations, obtained by switching a matching between the corresponding pair of rows and columns. They span all matrices with zero row and column sums since the upper-left $(n-1)\times(n-1)$ block determines such a matrix. For $n\ge 4$ the affine hull contains the nonmonomial invertible matrix $I+uv^{\mathsf T}$, where $u=e_1-e_2$ and $v=e_3-e_4$. The addition has zero row and column sums and squares to zero. For $n=1,2$, the binary row and column equations describe exactly the permutations even without invertibility. For $n=3$, the all-ones line and the coordinate-sum-zero plane are complementary in $\mathbb F_2^3$. Invertible matrices satisfying the row and column equations fix that line pointwise and act by an arbitrary invertible map on the plane. There are $(4-1)(4-2)=6$ such maps, all already accounted for by the permutation matrices.

The obstruction persists if the proposed linear branch can depend on the code instance. For any field and $n\ge 4$, take both codes to be $\{x\in k^n\mid\sum_i x_i=0\}$. This is a proper, full-support code whose generator $[I_{n-1}\mid-\boldsymbol 1]$ has distinct projective columns. All permutations satisfy $GMH'^{\mathsf T}=0$. The affine hull of their matrices contains $I+uv^{\mathsf T}$ as above. To see this directly, $uv^{\mathsf T}=A-B$ for permutations $A,B$ which differ by switching the selected columns $3,4$ in rows $1,2$. This gives the affine combination $I+A-B$. It is invertible and preserves the code because its row sums are one. It has extra nonzero entries in its first row, so it is nonmonomial. Every affine system containing all valid monomial witnesses therefore accepts a spurious invertible witness for this pair.

## Exponentially many linear branches even with the promises

For the same single-parity-check code, any exact disjunction relative to both invertibility and the original code equations has at least $\lceil(3/2)^{\lfloor n/4\rfloor}\rceil$ affine branches. The proof uses three permutation matrices of size four with two properties. Every combination $X+Y-Z$, allowing repetitions, is invertible. At least one such combination using all three matrices is nonmonomial.

- In characteristic two use $I,A,B$ from the previous section. Combinations with a repeated term cancel to a permutation, and the distinct combination is $I+uv^{\mathsf T}$.
- In characteristic three use $I,T,T^2$ for a $3$-cycle $T$ on the first three coordinates, fixing the fourth. A distinct combination on the three active coordinates has circulant determinant $a^3+b^3+c^3-3abc=4$, where the coefficients $a,b,c$ are $1,1,-1$ in some order. It has three nonzero entries in each active row. A combination $2X-Y$ with $X\ne Y$ has determinant $7$, by factoring $X$ and using $\det(2I-T)=\det(2I-T^2)=2^3-1$ on the active coordinates. The fourth coordinate is fixed throughout. All other repeated combinations are permutations.
- In characteristic different from two and three use $I,P,Q$ for disjoint swaps $P=(1\,2)$ and $Q=(3\,4)$. On each pair each combination has form $aI+(1-a)S$ with $S$ the swap and $a\in\{-1,0,1,2\}$. Its determinant $2a-1$ belongs to $\{-3,-1,1,3\}$ and is nonzero. The distinct combination $I+P-Q$ is nonmonomial on the second pair, where it is $2I-S$.

Let $r=\lfloor n/4\rfloor$. Use independent choices from the characteristic-appropriate triple in each of $r$ blocks and identity on the remaining coordinates. This gives $3^r$ genuine monomial witnesses. If one affine branch includes witnesses exhibiting all three choices in a given block, take three such witnesses and order them so that $X+Y-Z$ is nonmonomial in that block. The affine branch includes the combination, which is invertible on every block. Its row sums equal one, so it preserves the code. Its nonmonomial block makes it a spurious witness. Thus each branch realizes at most two choices per block and covers at most $2^r$ of the $3^r$ witnesses. Counting proves the stated bound.

When $q>n+2$, the exact count for the invertibility promise is $n!$, both for unrestricted monomial matrices and for the single-parity-check example. A branch containing $A,B$ on different supports contains their entire affine line. The determinant is a polynomial in the line parameter of degree at most $n$ and is nonzero at the two endpoints. Since there are more than $n$ other parameters, some other point is invertible. At each nonendpoint one row contains two nonzeros. For the parity-check example the whole line satisfies the original linear equations as well. Every support occurs among the permissible matrices, and each branch covers at most one support. One branch per support suffices by setting the entries outside it to zero.

## Quadratic equations with unique auxiliary witnesses

For arbitrary $n,q$, introduce support variables $b_{ij}$ shared by all row and column constraints. Make one rooted binary tree with $n$ leaves for each row and each column, using the corresponding $b_{ij}$ as leaf variables. In each tree set the root equal to $1$. For each internal vertex $w$ with two children $\ell,r$, impose
$$
s_w=s_\ell+s_r, \qquad s_\ell s_r=0 .
$$
Whenever a parent is zero both children are zero. Whenever it is one, one child is one and the other is zero. Induction from the root proves that each tree has exactly one leaf equal to one and all other leaves zero. The internal values are determined by those leaves. Thus $(b_{ij})$ is a permutation support matrix in any characteristic.

Writing $m_{ij}$ for the entries of $M$, introduce $z_{ij}$ and impose
$$
m_{ij}(1-b_{ij})=0,\qquad z_{ij}(1-b_{ij})=0,\qquad
\sum_{j=1}^n m_{ij} z_{ij}=1\quad\text{for each row }i .
$$
Only the selected entry in each row can contribute to the sum. It must be nonzero and its auxiliary variable is its inverse. Conversely any monomial matrix has a unique support and these equations then determine all tree and inverse variables. There are $O(n^2)$ variables and equations, each equation has degree at most two, and listing the equations takes polynomial time in $n$ and $\log q$. The original code-compatibility equations can be appended without changing this proof.

The order $n^2$ is optimal for constant degree in the unique-witness model. For $q=p^f$, let an exact model with unique auxiliary witnesses have $N\ge n^2$ total variables and $s$ equations of degrees $d_i\le D$, with $D\ge 1$. Its number of joint zeros is $|\mathcal M|=n!(q-1)^n$, of $p$-adic valuation $v_p(n!)$. Ax–Katz divisibility implies
$$
N-\sum_i d_i\le D\left\lfloor v_p(n!)/f\right\rfloor.
$$
Indeed if the left side were larger, the number of zeros would be divisible by a power of $q$ exceeding its valuation. Using $\sum_i d_i\le Ds$ and Legendre’s bound $v_p(n!)\le n/(p-1)$ gives
$$
s\ \ge\ \left\lceil N/D\right\rceil-\left\lfloor v_p(n!)/f\right\rfloor
\ \ge\ \left\lceil n^2/D\right\rceil-n .
$$
[Katz, *On a Theorem of Ax*](https://www.math.mcgill.ca/goren/SeminarOnCohomology/Katz.pdf)

## Scope and prior work

The affine impossibility answers the literal linear-equation question for the matrix entries in the survey’s algebraic model, where every monomial witness is to be represented. The quadratic construction gives a complete bounded-degree alternative. The equation-count lower bound applies to unique witnesses. The branch counts specify the external promises they use. These are results about algebraic representations of witnesses. The computational complexity of deciding code equivalence is a separate question.

The survey credits Mohamed Ahmed Saeed’s thesis for the algebraic solver. A targeted literature and catalog check located that prior algebraic approach and did not locate the exact disjunctive counts or disjoint-cycle classification above. Publication priority remains unverified. [Saeed, *Algebraic Approach for Code Equivalence*](https://theses.fr/2017NORMR034)
