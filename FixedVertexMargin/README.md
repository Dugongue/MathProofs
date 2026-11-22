# Exact affine instability for layered quivers with a fixed number of vertices

For every fixed number $k$ of vertices, a deterministic algorithm computes the exact squared affine Hilbert–Mumford margin of a nonzero, explicitly given layered quiver representation in polynomial bit time. It also constructs an optimal weighted flag over the input field whenever the margin is positive. The theorem holds over $\mathbb Q$ and over finite fields given in standard explicit arithmetic representations. The margin measures degeneration to the origin over the algebraic closure under $\prod_v\mathrm{SL}(V_v)$, using the Euclidean norm on all vertex weights. The polynomial exponent may depend on $k$.

**Three-vertex refinement.** With three vertices of total dimension $D$, polynomial preprocessing followed by $O(\log(D+1))$ principal-filtration calls suffices. All queries can have integer prices of magnitude polynomial in $D$. One additional scalar quadratic calculation returns the exact squared margin, including on a wall between price regions. The number of calls counts full Harder–Narasimhan filtrations. Each such filtration may itself use polynomially many matrix-space computations.

## The optimization problem

Let $d_v=\dim V_v>0$. A unit grading assigns heights $h_v$ satisfying $h_t-h_s=1$ for each nonzero arrow $A_a:V_s\to V_t$. Zero arrows can be deleted. Heights can be chosen integral with range at most $k-1$ on each component by traversing the underlying undirected graph and translating the minimum height to zero. We use this choice for the bit bound. The output for a vertex incident only to zero maps is the zero weight there. Dimensions are measured in the ordinary explicit-space input model. At least one nonzero map is required since the defining minimum ranges over nonzero entries.

In a splitting basis write $w_{v,i}$ for integral one-parameter-subgroup weights with zero sum at every vertex. Let $\mu(A,w)$ be the least target weight minus source weight on a nonzero arrow entry. The margin is the supremum of $\mu(A,w)/\|w\|$ for positive $\mu$, with value zero if no such weights exist. A positive answer supplies bases for the flag steps and rational weights normalized to least exponent one. Clearing their denominators gives an integral algebraic one-parameter subgroup over the input field. In particular the output is a value with a witness for the rate of approach to zero. This is an invariant of the vertex-base-change orbit and of invertible changes of basis among parallel arrows. It does not by itself classify such orbits.

## From flags to a function of vertex prices

Write
$$
 \bar h=\frac{\sum_v d_vh_v}{D},\qquad c_v=\bar h-h_v,\qquad
 r_v=d_vc_v,\qquad C=\sum_vd_v c_v^2 .
$$
Both $r\ne0$ and $C>0$ follow from the presence of a nonzero arrow. The shifted weights $q=w+c$ turn every constraint $w_{t,j}-w_{s,i}\ge1$ into $q_{t,j}\ge q_{s,i}$. Hence each superlevel of $q$ must be a subrepresentation. Call these flags admissible and let $m(q)_v$ denote the sum of their weights at vertex $v$. The trace conditions are exactly $m(q)=r$. On that fiber $\|w\|^2=\|q\|^2-C$.

For a real price $\lambda$, take the Harder–Narasimhan flag for slope $\lambda\cdot e/|e|$, where $e$ is a dimension vector and $|e|=\sum e_v$. Denote by $\beta_\lambda$ the flag weighted by its successive slopes, and define $H(\lambda)=\|\beta_\lambda\|^2$. It satisfies
$$
  \lambda\cdot m(q)\le\sqrt{H(\lambda)}\,\|q\|,\qquad
  \lambda\cdot m(\beta_\lambda)=H(\lambda).
$$
Indeed the induced pieces of a subrepresentation inside successive semistable factors have degree bounded by their dimensions times the respective slopes. Thus its degree is at most the sum of the largest slopes up to its total dimension, counting multiplicities. Write the pairing of a weighted flag as its lowest weight times the full degree, plus a nonnegative sum of successive weight gaps times superlevel degrees. This gives the first inequality by Cauchy–Schwarz, and the principal flag attains equality. Consequently
$$
 H(\lambda)=\max_{q\ {\rm admissible}}
       \big(2\lambda\cdot m(q)-\|q\|^2\big).
$$
In particular $H$ is convex. [Earlier principal-flag and height-shift proof](https://github.com/Dugongue/MathProofs/blob/main/ParametricConvexFour/Flags.md)

For a flag with graded dimension vectors $e_1,\ldots,e_s$ put $M=\sum_j e_je_j^{\mathsf T}/|e_j|$. Inside any region where the ordering of all possible slopes is fixed, the largest maximum-slope subrepresentation and every successive quotient step remain the same. Induction uses the same bounded dimension-vector list in each quotient. On this region $H(\lambda)=\lambda^{\mathsf T}M\lambda$ and $m(\beta_\lambda)=M\lambda$. On a wall the semistability inequalities of each factor persist by continuity. Consecutive factors whose slopes become equal form a semistable extension of that slope, so the wall filtration is obtained by merging equal grades. All adjacent quadratics therefore have the same value and gradient there. Since there are finitely many regions, $H$ is differentiable everywhere with gradient $2m(\beta_\lambda)$.

## Exact solution and output

Minimize $H$ on $\lambda\cdot r=1$ and call its minimum $\eta$. This minimum is attained. On each closed price region the function is a positive semidefinite quadratic on a closed polyhedron. A linear image of a polyhedron is a closed polyhedron, so the least squared norm of the image by $M^{1/2}$ is attained whenever the region meets the constraint. There are finitely many regions. At any minimizer, differentiability implies $m(\beta_\lambda)=t r$ for a scalar $t$. Pairing with $\lambda$ gives $t=\eta$.

If $\eta=0$, the price and the support inequality exclude any $q$ with $m(q)=r$, and the margin is zero. If $\eta>0$, $q=\beta_\lambda/\eta$ has the required vertex sums and squared norm $1/\eta$. The support inequality bounds the squared norm of every feasible $q$ below by $1/\eta$, proving optimality. Hence
$$
  \boxed{\quad\mathrm{margin}^2=\frac{\eta}{1-C\eta},\qquad
     w_{v,i}=\frac{(\beta_\lambda)_{v,i}}{\eta}-c_v.\quad}
$$
The denominator is positive because a zero $w$ cannot satisfy the normalized inequality on a nonzero entry. The least exponent is one at the optimum, since a larger exponent permits scaling $w$ down. Two distinct minimizing flags would have distinct arrays in a common adapted basis vertexwise. Their midpoint is feasible with smaller squared norm, proving uniqueness at this normalization. A stored chamber flag yields rational bases and weights as described below.

There are at most $(D+1)^k$ possible nonzero dimension vectors, including every quotient vector. Their pairwise slope comparisons have integer normals $|e'|e-|e|e'$ of size at most $2D^2$. The arrangement in fixed dimension has polynomially many regions. Full-dimensional regions have interior integer representatives of magnitude $D^{O(k)}$ by maximizing a strict slack in the unit box and clearing a vertex determinant. This bounds the *numeric* weights sent to the principal-filtration algorithm. On each feasible closed region minimize its rational quadratic exactly, by enumerating independent active normals and solving the resulting linear stationarity and feasibility equations. Fixed dimension bounds the enumeration. Rational sums and determinants here have polynomial bit length. At the optimal price, reuse the stored chain and merge tied blocks, which avoids another high-weight filtration call. Over rational inputs the fixed-price algorithm is due to Iwamasa, Oki and Soma. Over finite fields one can use the replicated path matrices and constructive noncommutative rank, with all threshold queries on the original matrices. The blow-up rank and shrinking-subspace certificates survive scalar extension. Details of the two field models, tie handling, and complexity appear in the companion proofs. [Duality and field algorithm](Duality.md) · [Chamber and rational-complexity proof](FlagsAlgorithm.md) · [Iwamasa–Oki–Soma, Theorem 4.5](https://arxiv.org/html/2407.06493v2#S4) · [Ivanyos–Qiao–Subrahmanyam, Theorem 1.5 and Corollary 1.7](https://arxiv.org/pdf/1512.03531)

## Why three vertices require only logarithmically many price queries

Adding $z\mathbf1$ to a price shifts each principal slope by $z$. Since the slopes counted with multiplicities sum to $\lambda\cdot d$,
$$
 H(\lambda+z\mathbf1)=H(\lambda)+2z(\lambda\cdot d)+Dz^2 .
$$
Also $\mathbf1\cdot r=0$. Every minimizing price is therefore centered by $\lambda\cdot d=0$. For three vertices the normalized and centered prices form a line
$$
 \lambda(t)=c/C+t(d\times r),\qquad t\in\mathbb R .
$$
The cross product is nonzero because $d$ has positive entries, $r\ne0$, and $\sum r_v=0$. Along this line each candidate slope is affine. Sort all isolated intersections of pairs of these affine functions and discard duplicate points. There are $O((D+1)^6)$ possible intersections. Pairs agreeing identically on the line can be kept tied throughout. The ordering is constant between adjacent points and on each exterior ray, even if the whole price line belongs to an ambient wall.

At a queried price the blocks give the derivative of $H(\lambda(t))$ directly as $2\sum_j (\lambda(t)\cdot e_j)((d\times r)\cdot e_j)/|e_j|$, valid also at a tie. This derivative is nondecreasing. Binary-searching the intersection list therefore takes logarithmically many queries. The list can also be dispensed with entirely, as follows.

Write the base and direction of the price line as $x/s$ and $y/u$ with integer vectors and positive integer denominators. Put
$$
 B=\max\{1,\ 2D^2u\|x\|_\infty,\ 2D^2s\|y\|_\infty\}.
$$
Every isolated wall is a reduced rational $p/q$ with $|p|,q\le B$. Indeed the equation for $e,e'$ uses the normal $n=|e'|e-|e|e'$, with $\|n\|_1\le2D^2$, and has root $-u(x\cdot n)/(s(y\cdot n))$. With the bounded integral grading, $B$ is polynomial in $D$ because only a fixed number of rational operations form these vectors.

Query the derivative at the outer endpoints $\pm(B+1)$. Zero gives an answer. If the signs put the minimum outside, its exterior quadratic determines the stationary point exactly. Otherwise keep two endpoints with strictly negative and positive derivatives. Bisect until an exact zero is found or the bracket has width less than $1/(2B^2)$. Two distinct rationals of denominators at most $B$ differ by at least $1/B^2$. If there is a possible wall in the bracket, it is consequently the rational of denominator at most $B$ nearest the midpoint, computable by continued fractions. Query that candidate if it belongs to the open bracket and keep the side containing the minimum, or return it if its derivative vanishes. A spurious candidate simply subdivides a single price region. The remaining open interval is free of walls. One interior query supplies its quadratic; take its exact stationary point, using the sample itself for a constant piece. The limiting chain remains valid on the endpoints.

Starting with width $2B+2$ takes $O(\log(B+1))=O(\log(D+1))$ halvings. Their dyadic denominators have polynomial magnitude, as do those of the reconstructed candidate and the final sample. Thus the principal-filtration calls use polynomial-magnitude primitive integer prices. The final exact stationary price can have larger denominators and is evaluated on a stored flag. The implementation follows this implicit search; the coordinate tests also exercise the explicit intersection-list algorithm.

### Counting matrix-space optimizations

Each full price query admits an implementation using at most $2D-1$ largest-maximizer calls on the original quiver. Start with the known endpoint steps $0,V$ of the principal chain for the queried integer price $\lambda$. For any two known nested steps $F<G$, take the chord slope $\alpha=\lambda\cdot\dim(G/F)/|G/F|$. Find the largest subrepresentation maximizing $(\lambda-\alpha\mathbf1)\cdot\dim U$ on the original input. The principal polygon shows this is precisely the last step containing all grades of slope at least $\alpha$. If $F,G$ are consecutive, it equals $G$. Otherwise the chord slope is a strict weighted average between the first and last intervening slopes, and the returned step lies strictly inside $(F,G)$. Recurse on both subintervals. A chain with $s$ grades produces a binary tree with $s$ leaves and $s-1$ internal calls. All original-objective weights have polynomial magnitude after clearing the single denominator $|G/F|$. Thus the three-vertex algorithm uses $O(D\log(D+1))$ largest-maximizer calls on the unchanged arrow matrices. This count does not assert the same bound on bit operations. [Principal polygon and largest maximizers](https://arxiv.org/html/2407.06493v2#S4)

## Reproduction and prior work

Three-vertex price search is implemented with exact fractions and a supplied principal-filtration routine. The two test programs supply exhaustive routines for their respective small input classes. The polynomial general-purpose matrix-space backend is specified by reduction in the proof. [Price solver](three_vertex.py) · [Coordinate tests](control.py) · [Finite-field tests](finite_control.py)

* The coordinate test covers all 255 nonempty subsets of the eight independent matrix-unit arrows in dimension $(2,2,2)$. It compares three calculations, including direct minimization over active arrow equalities. It recovers 177 zero margins and 78 positive ones, whose squared values are $1/10,1/4,1/2,3/4,1$. Every returned positive flag passes the trace, norm and least-exponent checks.
* The finite-field test covers all 255 nonzero ordered pairs of binary $2\times2$ arrow matrices on the chain and 256 further inputs with parallel arrows on both legs. It checks the price solver against all 216 triples of bases per input, for 110,376 comparisons of fixed-basis optima against the varying-basis computation in aggregate. All 511 maxima agreed and all 111 positive flags passed the witness checks.
* Lean verifies the weighted variance identity governing the loss when merging slope blocks. The general algorithm, its complexity, and the oracle bound are written proofs. [Lean lemma](Pooling.lean)

Hirai and Sakabe already obtain the exact rectangular matrix-tuple formula and optimal flags under their hypotheses. Bürgisser, Franks, Garg, Oliveira, Walter and Wigderson explicitly prove polynomial-time fixed-vertex null-cone membership in characteristic zero. The contribution investigated here is exact multivertex optimization with recovery of optimal flags, and the logarithmic principal-filtration count at three vertices. Publication priority for these combined statements remains unconfirmed. [Prior-art audit](Literature.md) · [Hirai–Sakabe, Theorem 4.24](https://arxiv.org/html/2404.09746#S4.SS2) · [Bürgisser et al., Corollary 6.22(2)](https://arxiv.org/pdf/1910.12375#page=70)
