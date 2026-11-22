# Exact degree of ordinary Polynomial Calculus for symmetric matrix congruence

Let $F$ have characteristic different from two, let $A,B$ be symmetric $n$-by-$n$ matrices, and use the original equations of Galesi, Grochow, Pitassi and She,
$$
 XAX^T=B,\qquad XY=YX=I .
$$
The variables are exactly the entries of $X,Y$, with no finite-field or Boolean axioms. Let $r\le s$ be the two ranks, in increasing order. For $0<u<v$ put $d(u,v)=2$ in characteristic zero and
$$
 d(u,v)=\min(u+2,\ 2p^{v_p(v-u)})
$$
in characteristic $p>0$. Set $d(0,v)=0$ for $v>0$.

**Theorem.** Equal ranks give a solution over the algebraic closure, so no ordinary PC refutation exists over $F$. At unequal ranks, a zero source $A$ gives degree zero. For every other unequal-rank pair the exact refutation degree is
$$
 \max\!\left(3,\ \min\{d(r,s),d(n-s,n-r)\}\right).
$$
This includes $B=0$, $A\ne0$, where the degree is exactly three. The displayed source and target have different roles in this small exceptional case. This result applies directly to the symmetric-matrix portion of the printed matrix-congruence question. The proof does not use Dirichlet GRH. [Published equations](https://arxiv.org/html/2305.19320#S7.SS3)

## Signed partial matchings

We first compute a version of the rectangular inverse degree with a single matrix of variables $P$ of size $v$ by $u$. The input is
$$
 PP^T=I_v,\qquad P^TP=I_u .
$$
Its exact degree is $d(u,v)$. If $u=0$, the larger identity has a nonzero constant entry as an axiom. Otherwise the upper bound follows by substituting $Q=P^T$ into the ordinary rectangular inverse proof. Trace gives the lower bound of two in characteristic zero, in the sense that the first usable nonzero input has degree two, and the difference of traces supplies a proof of that degree.

For the positive-characteristic lower bound adapt the [weighted matching proof](ConjugacyDegree.md). For each edge $e$, send its entry to $t_e x_e$. Use the group algebra of the elementary abelian sign group, with one commuting generator $t_e$ per edge and relation $t_e^2=1$, tensored with the Boolean collision quotient in the $x_e$. Products of distinct $t_e$ are a basis of the group algebra. The relations on $x_e$ give the same partial matching basis as before. The off-diagonal equations vanish, and the diagonal equations map to row and column totalities because every $t_e^2=1$.

The odd-exponent edge set $S$ of a surviving monomial is itself a matching. At target-degree bound $D$, its fixed sign component has basis $t_S x_S x_U$ for matchings $U$ on the complementary board of size at most $\lfloor(D-|S|)/2\rfloor$. Necessity follows by counting powers of variables, and the converse follows by using one copy on $S$ and two copies on $U$. Define the annihilating space in this component by all matching designs at the indicated residual degree. For $D\le u+1$ and $D<2p^{v_p(v-u)}$, the endpoint design lemma in the companion applies in each component. Degree falls are justified by the restriction and extension of those designs. Multiplication by $t_ex_e$ vanishes at collisions. Adding a new sign removes its two endpoints from the residual board and keeps the previous degree budget; pull a design back by forcing that edge present. Canceling an existing sign restores both endpoints and increases the new degree budget by one; pull a design back by adjoining the edge to every matching in its argument. Both operations preserve row and column design recurrences. Thus legal PC steps preserve the annihilating space. Normalization at the empty matching excludes the constant one. This proves the lower bound for the signed rectangle.

## Extraction and specialization in the original equations

Passing to an algebraic closure preserves the minimum PC degree by the scalar-extension argument in the companion. Congruence changes of the two constant bases induce invertible linear substitutions on $X,Y$ preserving PC degree. Over the algebraic closure all symmetric forms diagonalize to ones followed by zeros in the stated characteristic. Write $a=\operatorname{rank} A$, $b=\operatorname{rank} B$. In their respective rank decompositions use blocks $X_{11}$ of size $b$ by $a$ and $Y_{11}$ of size $a$ by $b$, and the corresponding lower-right blocks.

Put $G=XAX^T-B$. The identity
$$
 XA-BY^T=GY^T-XA(YX-I)^T
$$
derives the linear equations on the left in degree three. Their lower-left and upper-right blocks give $X_{21}=0$ and $Y_{21}=0$. Thus the upper-left and lower-right blocks of the two inverse products yield ordinary rectangular inverse systems for the pairs $(a,b)$ and $(n-a,n-b)$. Terms involving the zero blocks are removed by multiplying the available linear equations by variables. Replaying the easier rectangular proof gives the displayed upper bound, including zero-size rectangular sides.

For the reverse inequality specialize $X$ and $Y$ to block diagonals. In their upper-left positions use $P$ and $P^T$ of shapes $b$ by $a$ and $a$ by $b$. In their lower-right positions use independent ordinary rectangular matrices $U,V$ of the required complementary shapes. All other entries are zero. The specialized inverse equations are the signed rectangle and the ordinary complementary rectangle. The congruence equation repeats $PP^T-I_b$ and zeros. Swapping the larger and smaller sizes or transposing $P$ makes no change to the signed rectangle degree. This specialization sends variables to variables or zero. Its disjoint union has degree the minimum of the two constituent degrees, by the disjoint-system lemma in the companion. It proves the claimed lower bound above degree three.

Finally, suppose $A\ne0$. The degree-two line space is just the linear span of usable input equations unless it already contains a nonzero constant, because there are no linear parts. Its quadratic terms have incompatible bidegrees $(2,0)$ from the Gram matrix and $(1,1)$ from the inverse products. If the homogeneous part of an inverse combination vanishes, its constant also vanishes by evaluation at $X=Y=I$. A linear functional killing $XAX^T$ identically annihilates every symmetric matrix. Indeed choose a vector $u$ with $u^TAu\ne0$, which exists for a nonzero symmetric form in odd or zero characteristic by polarization. Taking $X=vu^T$ shows the functional kills every $vv^T$, and those span the symmetric matrices by the coordinate vectors and their pairwise sums. Thus it also kills $B$. There can be no degree-two refutation. If $A=0$ and $B\ne0$, a nonzero entry of $-B$ is a usable degree-zero axiom. This completes all cases.

The exact degree statement is a written proof. The endpoint matching-design construction used in its lower bound is from the cited preprint as sharpened in the companion. The finite-field system with coordinate field equations and the literal system in characteristic two have different classification questions. [Riis, Section 14](https://arxiv.org/html/2611.07280v1#S14)
