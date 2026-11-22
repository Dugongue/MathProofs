# Exact dual prices for the affine instability margin

For a layered quiver with a fixed number of vertices, the exact squared affine instability margin under the product of the vertex special linear groups can be computed in deterministic polynomial time over the rationals and explicitly represented finite fields. The algorithm returns a rational optimal price. In the unstable case a single principal filtration at that price determines all optimal normalized weighted flags and an integral splitting cocharacter. In the zero-margin case the price certifies the geometric obstruction. The parameter is the number of vertices, and the algorithm has a polynomial exponent depending on that parameter.

## Normalization and a finite price problem

Use a nonzero quiver representation $A$ with vertex spaces $V_v$ of dimensions $d_v>0$, total dimension $D$, and rational heights $h_v$ increasing by one on every arrow. As in the principal-flag theorem, set
$$
 c_v=D^{-1}\sum_u d_uh_u-h_v,\qquad
 r_v=d_vc_v,\qquad C=\sum_v d_vc_v^2.
$$
The presence of a nonzero arrow implies $r\ne0$. If a vertex space is zero, remove it and its incident arrows before computing these quantities. For the zero representation, the orbit contains zero already and there is no least nonzero-entry exponent to normalize. That case can be handled separately.

A real weighted tuple of flags is admissible when all its superlevel subspaces form subrepresentations. Write $m(q)_v$ for the sum of its weights at vertex $v$, and $\|q\|$ for the Euclidean norm counted with multiplicities. In adapted bases admissibility is the inequality $q_{s,i}\le q_{t,j}$ at each nonzero arrow entry from $(s,i)$ to $(t,j)$. The change of weights $q_{v,i}=w_{v,i}+c_v$ sends traceless cocharacter weights with least arrow exponent at least one to admissible weights with $m(q)=r$. The squared norm becomes $\|w\|^2=\|q\|^2-C$.

Let $\beta_\lambda$ be the admissible weighted flag given by the principal filtration for price $\lambda\in\mathbb R^s$, where $s$ is the number of vertices. Each graded dimension vector $e$ gives the slope $\lambda\cdot e/|e|$, with $|e|=\sum_v e_v$. The set of admissible moment vectors of flags of norm at most one is compact and convex. Compactness follows from the finitely many possible binary arrow supports in adapted bases. Convexity follows by simultaneously adapting bases to any two flag tuples, then interpolating their weights while preserving the common arrow inequalities. Its support function is $H(\lambda)=\|\beta_\lambda\|$. The principal polygon supplies the upper bound $\lambda\cdot m(q)\le H(\lambda)\|q\|$, with equality on $\beta_\lambda$, since $\lambda\cdot m(\beta_\lambda)=\|\beta_\lambda\|^2$. These are precisely the earlier principal-flag identities. [Parametric subrepresentation flags and affine instability](https://github.com/Dugongue/MathProofs/blob/main/ParametricConvexFour/Flags.md)

Define
$$
           \eta=\min_{\lambda\cdot r=1}H(\lambda)^2.
           \tag{1}
$$
The minimum exists and has a rational attainer, as proved below. If $\eta=0$, then no admissible $q$ can satisfy $m(q)=r$, because pairing with an attaining price gives $1\le0\|q\|$. This price is a certificate with $\lambda\cdot d=0$ and $\lambda\cdot\dim U\le0$ for every subrepresentation $U$. Indeed all principal slopes vanish exactly when those conditions hold, since the full representation then has slope zero and is the largest maximum-slope subrepresentation.

If $\eta>0$, the gauge of $r$ in the compact convex set of unit moments is $\Gamma=1/\sqrt\eta$. To see this, the separating-hyperplane test for membership in a dilation is $\lambda\cdot r\le tH(\lambda)$ for every $\lambda$. Pairings $\lambda\cdot r\le0$ impose no constraint. Rescale every remaining price to the hyperplane in (1). The minimum norm of an admissible $q$ with $m(q)=r$ is thus $\Gamma$ and is attained.

For any attaining price $\lambda_*$, the normalized least-norm flag and squared affine margin are
$$
             q_*=\frac{\beta_{\lambda_*}}{\eta},\qquad
             \mu_{\rm aff}^2=\frac{\eta}{1-C\eta}.
             \tag{2}
$$
To prove the flag formula, both $q_*/\Gamma$ for a least-norm flag and $\beta_{\lambda_*}/H(\lambda_*)$ attain the positive support value $H(\lambda_*)$ on the unit ball. A positive support value has exactly one maximizing weighted flag of norm at most one. If two were distinct, they would both have norm one, and interpolation in common adapted bases would produce a flag of smaller norm with the same positive value. Rescaling it would contradict maximality. Thus the two normalized flags coincide, giving (2). The denominator is positive because $q_*-c$ cannot be zero in the presence of a nonzero arrow. Its least arrow exponent must equal one, because a larger exponent would allow a scaling that lowers the norm and still has exponents at least one. Subtract $c_v$ at vertex $v$ from the weights of $q_*$. Split the resulting rational flags and clear denominators to obtain a cocharacter. The same weighted flag is obtained from every minimizing price even when the prices themselves differ.

## Price chambers and attainment

List all normalized nonzero dimension vectors
$$
                  \mathcal P=\{e/|e|:\ 0\le e_v\le d_v,\ e\ne0\}.
$$
There are at most $(D+1)^s$ vectors. Use the central hyperplanes $\lambda\cdot(p-p')=0$ for distinct $p,p'\in\mathcal P$. Inside any full-dimensional open chamber, the ordering of all possible slopes is fixed, including slopes in any quotient, since the dimension-vector bounds still apply. The largest maximum-slope subrepresentation is therefore constant on the chamber. Applying the same argument to the quotient proves that the entire principal chain is constant. Identically equal normalized dimension vectors do not need a hyperplane. For this chain, with graded dimension vectors $e_j$,
$$
    H(\lambda)^2=\lambda^{\mathsf T}Q_{\mathcal C}\lambda,\qquad
    Q_{\mathcal C}=\sum_j\frac{e_j e_j^{\mathsf T}}{|e_j|}.
    \tag{3}
$$
The matrix is rational and positive semidefinite. The identity extends to the closed chamber $\overline{\mathcal C}$ by continuity of the compact support function. The closed full-dimensional chambers cover all of price space.

For every chamber whose closure meets $\lambda\cdot r=1$, minimize (3) on that closed polyhedron. To prove attainment, apply the linear map $Q_{\mathcal C}^{1/2}$ to the polyhedron. Its image is itself a polyhedron, by linear projection or elimination, so it is closed. The least squared Euclidean norm in the image is attained.

An exact rational implementation uses only linear algebra and linear feasibility. For a chamber with signed inequalities $a_i\cdot\lambda\ge0$, enumerate independent subsets of active equalities, adjoining $\lambda\cdot r=1$. It suffices to enumerate at most $s-1$ inequality normals together with $r$. If a minimum lies on a face, the normals of its active equations and $r$ have a basis of this form, and the gradient is orthogonal to the affine hull of that face. For the resulting independent system $R\lambda=b$, solve
$$
              Q_{\mathcal C}\lambda=R^{\mathsf T}y,\qquad
              R\lambda=b
$$
and test a solution for all weak chamber inequalities using linear feasibility. Every feasible such stationary point minimizes the quadratic on the equality affine space. The enumeration includes one equality space containing each chamber optimum with the required stationarity. Thus retaining the least value of these finitely many rational candidates gives the exact chamber optimum even for a singular quadratic. Taking the minimum over chambers proves (1). [Kozlov, Tarasov and Khachiyan, exact rational convex quadratic programming](https://www.mathnet.ru/eng/zvmmf5189)

For boundary recovery, take any stored chamber chain for a chamber whose closure contains $\lambda_*$. At $\lambda_*$ its graded slopes are weakly decreasing and its graded pieces remain semistable. For every subrepresentation of any fixed graded piece, the required slope inequality is linear in $\lambda$ and holds throughout the open chamber, hence also at the boundary. Consecutive grades of equal slope merge into a semistable piece, by additivity of degree and rank for a subobject's intersection and image in an extension. Thus the stored chain, with boundary slopes and equal grades merged, gives the principal chain for $\lambda_*$. This also covers $\eta=0$, when all grades merge with slope zero. No new principal computation at the optimal rational price is needed.

An alternative primal computation uses the stored chamber chains only. For each chain choose one real variable $x_j$ per graded piece, impose $x_1\ge\cdots\ge x_\ell$ and $\sum_j x_je_j=r$, and minimize $\sum_j |e_j|x_j^2$. Any feasible solution is an admissible flag with the required moments. When a positive margin exists a chamber containing an optimal price in its closure contains the globally optimal weighted flag in this form. This follows from the boundary argument and (2). Thus minimizing over the finite chain list also gives the exact answer, while the dual algorithm yields an explicit price certificate.

## A polynomial principal computation over the input field

A chamber sample can be taken integral with entries of size $D^{O(s)}$ for fixed $s$. Write each comparison with integer normal $|e'|e-|e|e'$, with coordinates of magnitude at most $2D^2$. A sign pattern with nonempty open chamber has a point satisfying every signed inequality with right side one, by homogeneous rescaling. Minimize $t$ subject to these signed inequalities and $-t\le\lambda_v\le t$. The optimal section is bounded and contains a vertex of this feasible polyhedron, and Cramer's rule bounds the denominators and numerators by $D^{O(s)}$. Clear a common denominator. The no-hyperplane case needs just the sample zero. One can enumerate chambers incrementally using these linear feasibility tests, retaining the two feasible signs of each new hyperplane. In dimension $s$, $M$ hyperplanes have at most $\sum_{j=0}^s\binom{M}{j}$ chambers by the usual recurrence from intersecting with the new hyperplane. Thus the arrangement computation and the number of HN calls are polynomial for fixed $s$. [Edelsbrunner, O'Rourke and Seidel, hyperplane arrangements](https://epubs.siam.org/doi/10.1137/0215024)

Here is a field-explicit implementation of the path-matrix reduction of Huszar and Cheng. For an integer vertex weight $\theta$, maximize $\theta\cdot\dim U$ over subrepresentations. Form a rectangular matrix space from positive replicas $S=\bigoplus_{\theta_i>0}V_i^{\oplus\theta_i}$ to negative replicas $T=\bigoplus_{\theta_j<0}V_j^{\oplus(-\theta_j)}$. For every directed path from a positive vertex $i$ to a negative vertex $j$, include its composite as a single block map for every choice of source and target replicas. All other blocks of that matrix are zero. [Huszar, quiver discrepancy and noncommutative rank](https://arxiv.org/abs/2111.00039) · [Cheng, Appendix A](https://arxiv.org/abs/2111.06428)

Call the space $\mathcal B$ and write $\mathcal B(W)$ for the span of the images of a subspace $W\subseteq S$ by matrices from $\mathcal B$. Then
$$
      \max_{U\ {\rm subrepresentation}}\theta\cdot\dim U
       =\max_{W\subseteq S}\bigl(\dim W-\dim\mathcal B(W)\bigr).
       \tag{4}
$$
From $U$, use the full positive replicas of its subspaces. Their image span lies in its negative replicas, so the right side dominates. Conversely, project $W$ to every positive replica and generate the smallest subrepresentation containing these projected subspaces at their vertices. Concretely, sum their images along every path, allowing paths of length zero at the positive vertices. The negative replicas of that generated subrepresentation span exactly $\mathcal B(W)$, because each path map is isolated in one block per replica pair. Its positive replicas contain $W$. This proves the converse and recovers an optimizing subrepresentation from an optimizing $W$.

Pad the rectangular space with zeros to make it square. The added source dimension adds exactly that amount to the maximum shrunk defect. Indeed the image depends only on projection to the unpadded source, while the added kernel contributes at most its full dimension. Thus a projected maximum shrunk subspace attains the right side of (4). The constructive noncommutative-rank theorem gives a maximum shrunk subspace and a matching blow-up rank certificate over $\mathbb Q$ and finite fields. Both certificates persist under any field extension, since a shrinking subspace of larger defect would impose a stronger rank bound on every blow-up. This proves that the optimum in (4) is the same over the input field and its algebraic closure. If there are no positive or no negative replicas, the optimum is attained by the zero or full subrepresentation as appropriate. [Ivanyos, Qiao and Subrahmanyam, Theorem 1.5 and Corollary 1.7(2)](https://arxiv.org/abs/1512.03531)

To obtain the largest maximizer, run (4) with weight $(D+1)\theta+\mathbf 1$. Because the weight and total dimension are integral, this first maximizes the original objective and then the total dimension. The largest maximizer is unique by modularity under sums and intersections. Hence the produced subrepresentation is the geometric largest maximizer over the input field.

At an integer chamber sample $\lambda$, enumerate all possible slope values $\lambda\cdot e/|e|$. For each threshold $\alpha$ in this list, clear the denominator of $\lambda-\alpha\mathbf 1$ and compute its largest maximizer on the original representation. The principal polygon argument identifies this maximizer with the step containing the grades of slope at least $\alpha$. Every actual grade slope appears in the candidate list, so the distinct returned steps, together with zero, give the entire principal chain. No input quotient representation is needed. The field computations and the determinant-one flags therefore take place over the input field, even though the claimed margin is geometric.

For fixed $s$, a graded quiver is acyclic and every path has length at most $s-1$, so enumeration of paths is polynomial in the arrow count. The chamber sample weight magnitude, the replicated dimensions, and the slope enumeration counts are polynomial in $D$, with exponents depending on $s$. All rational optimization has polynomial bit complexity in $D$ and the bit size of the grading. Over $\mathbb Q$ and explicit finite fields the field-side computations also have polynomial bit complexity in the matrix encodings. This gives the claimed deterministic algorithm. Cheng had obtained a polynomial-in-path-count algorithm for principal filtrations over infinite fields, and Iwamasa, Oki and Soma improve the dependence for rational data. The price arrangement and attained-price rule compute the affine least-entry-exponent optimum with independent trace constraints, using those principal computations as the inner step. [Cheng, deterministic Harder–Narasimhan filtrations](https://arxiv.org/abs/2111.06428) · [Iwamasa, Oki and Soma, quiver semistability](https://arxiv.org/abs/2407.06493)

## Positive, boundary, and zero cases

In the earlier three-layer example, the height price alone does not attain the gauge. Normalize the attaining price $(2,-1,-1)$ to $(1/3,-1/6,-1/6)$, which satisfies $\lambda_*\cdot r=1$ for $r=(2,0,-2)$. The principal slopes are $1/6$ and $-1/6$, both repeated three times, giving $\eta=1/6$. The price lies on a chamber wall, and merging equal slopes recovers the correct flag there. Formula (2) gives squared margin $1/2$ and reproduces the traceless weights after the height shift. A single invertible $2\times2$ arrow gives the contrasting zero case. The price $(1/2,-1/2)$ has $\lambda\cdot(1,-1)=1$ and all principal slopes zero because every subrepresentation has source dimension at most target dimension. Thus it supplies the exact zero-margin certificate.

For two vertices over the complex numbers, Hirai and Sakabe's Theorem 4.24 already gives the corresponding normalized optimum and optimal flag, in moment-map and recession-function conventions. In their notation let $C_A=\sum_j m_j n_j/(m_j+n_j)$ for the principal block dimensions, with total dimensions $m,n$. In the principal-price notation, $C=mn/(m+n)$ and $B=C-C_A$, as follows by expanding the square of $m_j/(m_j+n_j)-m/(m+n)$ on each block. Thus the earlier two-vertex formula $B/(C(C-B))$ is exactly $1/C_A-1/m-1/n$. The chamber algorithm addresses the simultaneous trace constraints at any fixed number of vertices. [Hirai and Sakabe, Theorem 4.24 and equation (4.33)](https://pubsonline.informs.org/doi/10.1287/moor.2025.0939)

An exact finite control compared the chamber calculation with direct active-set minimization on all 255 nonempty coordinate arrow supports in the three-layer format $(2,2,2)$. Both calculations gave 78 positive and 177 zero squared margins, with every value agreeing. An independent control checked the path-matrix defect equality over the field with two elements for all 256 ordered pairs of $2\times2$ matrices on a three-vertex path and all 27 vertex weights in $\{-1,0,1\}^3$. All 6,912 instances agreed, including 6,237 with at least one arrow matrix having multiple nonzero entries in the supplied bases.

This is a prose proof. Publication priority and Lean verification are unestablished.
