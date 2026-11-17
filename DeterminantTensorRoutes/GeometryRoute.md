# Determinant tests for tensors of associative algebra actions

Let $F=\mathbb F_q$ be a fixed finite field. Write a raw three-tensor as a bilinear map $b:U\times X\to Y$, with the transporter condition $h\,b(u,x)=b'(g(u),f(x))$. A prescribed triple means prescribed determinants of $g,f,h$ in the original bases. For the covariant tensor convention, invert the requested determinants in the two dualized slots. That inversion leaves determinant one unchanged.

An **action tensor** is one equivalent to $(a,v)\mapsto av$ for a unital associative subalgebra $A\subseteq\operatorname{End}_F(V)$, acting on $V$ by its given faithful representation. The algebra may be noncommutative.

**Theorem.** There is a deterministic polynomial-time raw recognition algorithm for action tensors. On two action tensors, the following tests apply.

1. If the normalized algebra is semisimple, any prescribed determinant triple is decidable in deterministic polynomial time.
2. In general, two explicitly computable subgroups
   $$
      K=\{(\det_F L_a|_A,\det_F(a|_V)):a\in A^\times\},
      \qquad H=\{\det_F r:r\in\operatorname{End}_A(V)^\times\}
   $$
   give a sufficient condition for a one-instance ordinary TI reduction for every prescribed triple. It suffices that $H=F^\times$ and $F^\times\times\{1\}\subseteq K$. There is no bound on the dimension, number of simple quotient factors, or nilpotency index of the radical. The example in Section 5 has scalar center and unbounded dimension and nilpotency index.

## 1. Recognize and normalize the action from raw slices

Dimensions must satisfy $\dim X=\dim Y$, and the slice map $u\mapsto S(u)=b(u,-)$ must be injective. Handle the all-zero format directly and assume henceforth that the three modes are nonzero. Form the slice space $\mathcal S\subseteq\operatorname{Hom}_F(X,Y)$ and compute its left idealizer
$$
   A=\{a\in\operatorname{End}_F(Y):a\mathcal S\subseteq\mathcal S\}
$$
by linear equations. It is a unital associative algebra. Regard $\mathcal S$ as a left $A$-module and find a cyclic generator, if one exists. The following procedure works for any explicit module $M$ over a finite matrix algebra $D$. Compute $J=\operatorname{rad}D$ and the represented quotient
$$
  D/J\simeq\prod_i\operatorname{Mat}_{d_i}(E_i).
$$
The application to $\mathcal S$ uses the explicit action of $A$ on $Y$ to compute this quotient. The algorithm for a given matrix algebra uses deterministic polynomial time at fixed characteristic. [Ivanyos–Qiao, Theorem 18](https://arxiv.org/html/1708.03495#Thmtheorem18)

Compute $M/JM$. In a simple-factor component of this quotient, let $w_1,\ldots,w_t$ be an $E_i$-basis of the image under the first diagonal matrix unit. The component is a sum of $t$ copies of the natural $E_i^{d_i}$-module. The $E_i$-basis is computed by greedily adjoining vectors whose $E_i$-spans increase the $F$-rank, using the explicit field action. If $t>d_i$, the component cannot be cyclic since its $E_i$-dimension exceeds the dimension of the simple matrix algebra. If $t\le d_i$, the vector $\sum_{a=1}^{t}e_{a1}w_a$ generates this component, since $e_{ja}$ sends it to $e_{j1}w_a$. Add the generators across the simple factors and lift the resulting vector to $M$. It generates $M$: the quotient by the submodule it generates equals its multiple by $J$, and a sufficiently high power of $J$ is zero. All steps are polynomial-size matrix and field operations.

Accept the tensor precisely when the procedure finds a generator $s\in\mathcal S$ that is invertible as a map $X\to Y$. In that case $\mathcal S=A s$, and changing coordinates by $x\mapsto sx$ and $u\mapsto S(u)s^{-1}$ gives the faithful action of $A$ on $Y$. Conversely, if the tensor is an action tensor then in raw coordinates $\mathcal S=A_0 s_0$ for a conjugate matrix algebra $A_0$ and an invertible slice $s_0$. Its left idealizer equals $A_0$: for $a$ in that idealizer, $as_0\in A_0s_0$, so $a\in A_0$. Any cyclic generator $s$ found has invertible $s_0=cs$ for some $c\in A_0$, so $s$ is invertible. This proves exact recognition without needing to search the whole slice space for an invertible element.

Fix explicitly ordered bases of the normalized algebra and module and use the *same* module basis in both module slots of each normalized tensor. Retain the changes of basis from these coordinates to the raw three spaces. For each determinant target divide by the target frame determinant and multiply by the source frame determinant to obtain its normalized value.

## 2. Identify the complete transporter in normalized coordinates

Suppose $(g,f,h)$ sends an action tensor $(A,V)$ to $(A',V')$. The tensor equation is
$$
  g(a)f=ha\qquad(a\in A).
$$
Taking $a=1$ gives $u=g(1)=hf^{-1}\in A'$. Invertibility as a matrix implies $u\in A'^\times$: Cayley–Hamilton expresses the inverse as a polynomial in $u$ and the identity. It follows that the linear isomorphism
$$
  \alpha:A\longrightarrow A',\qquad \alpha(a)=u^{-1}g(a)=f a f^{-1}
$$
is a unital algebra isomorphism and $f$ is an invertible $\alpha$-semilinear module map, meaning $f(av)=\alpha(a)f(v)$. Conversely any such pair $(\alpha,f)$ and any unit $u\in A'^\times$ give a transporter by $g=L_u\alpha,\ h=uf$. In particular the determinant triple is exactly
$$
    \bigl(\det_F(L_u|_{A'})\,\det_F\alpha,\quad
          \det_F f,\quad
          \det_F(u|_{V'})\,\det_F f\bigr).
$$
For fixed $\alpha$ and one available $f_0$, the possible $f$ are precisely $rf_0$ for $r\in\operatorname{End}_{A'}(V')^\times$.

## 3. Compute the correction groups

For any finite left $D$-module $N$, put $J=\operatorname{rad}D$, and let $m_i(N)$ be the total multiplicity of the $i$th natural simple module in the grades $J^jN/J^{j+1}N$. A central idempotent of $D/J$ isolates its summand in each grade. Its $F$-dimension divided by $d_i[E_i:F]$ gives the multiplicity there. Compute the action of any lift of the idempotent on that grade, where it is independent of the lift. For $a\in D^\times$ with residue $\bar a_i$ in the $i$th matrix component, the determinant on $N$ is
$$
    \det_F(a|_N)
      =\prod_i \mathrm N_{E_i/F}(\det_{E_i}\bar a_i)^{m_i(N)}.
$$
Indeed each grade is a sum of the natural modules, on which restriction of scalars takes the determinant to its field norm, and the determinant on a filtered space is the product over its grades. The units in $D$ surject onto the units in $D/J$. A lift of a quotient unit has a left and right inverse modulo $J$, which can be corrected by finite geometric series in $J$. The field norm is onto $F^\times$ because the multiplicative groups of finite fields are cyclic. Determinants of matrices in $\operatorname{GL}_{d_i}(E_i)$ independently take all nonzero field values.

Take a fixed generator $\zeta$ of $F^\times$. Therefore $K$ is generated by
$$
    (\zeta^{m_i(A)},\zeta^{m_i(V)})
$$
as $i$ ranges over the simple factors of $A/J$, using the regular left module for $A$. For $H$, compute the centralizer $D=\operatorname{End}_A(V)$ as a matrix algebra by linear equations and apply the same argument. Then $H$ is generated by $\zeta^{m_i(V)}$ for the natural action of this new algebra $D$ on $V$. These groups lie in fixed-size powers of $F^\times$, so membership and the test of the two subgroup conditions are deterministic polynomial-time operations. Conjugation by an actual module isomorphism transports the unit actions, so the condition is invariant under ordinary tensor equivalence.

Let the normalized target determinants be $(x,y,z)$. If $H=F^\times$ and $F^\times\times\{1\}\subseteq K$, then the exact answer is
$$
    [\text{ordinary TI holds}]\quad\text{and}\quad
    [z/y\in\operatorname{pr}_2(K)] .
$$
One implication follows from the transporter formula. For the converse, use any $(\alpha,f_0)$ provided existentially by ordinary equivalence, and postcompose $f_0$ by a centralizer unit to obtain $\det_F f=y$. Choose an element of $K$ whose second coordinate is $z/y$. The axis in $K$ lets its first coordinate be made $x/\det_F\alpha$ while keeping the second coordinate fixed. The resulting element of $K$ is realized by a unit $u$ by definition. The formula then gives the requested transporter. There is no transporter search in the reduction. A failed scalar membership test is mapped to a fixed no-instance, and a passing test is mapped to the original ordinary TI pair.

The same calculation gives one-character tests. For weights $(a,b,c)$, the free changes generated by the unit $u$ and the centralizer of $A'$ realize the product of the subgroup $\{s^a t^c:(s,t)\in K\}$ and $H^{\,b+c}$. If that product is all of $F^\times$, ordinary TI suffices for the exact prescribed character value, even if the full triple criterion fails.

## 4. Semisimple action tensors

For a semisimple algebra, use explicit algebra coordinates
$$
   A=\prod_i\operatorname{Mat}_{d_i}(E_i),\qquad
   V=\bigoplus_i(E_i^{d_i})^{r_i}.
$$
Recover $r_i$ and the module coordinates from the matrix units as in Section 1. Faithfulness gives $r_i\ge 1$. Align equal-degree finite fields with a deterministic finite-field isomorphism algorithm and expand both inputs in the same chosen $F$-basis of the standard model for that degree. Sort equal types $(d_i,[E_i:F],r_i)$ contiguously. The types, with their multiplicities, are a complete ordinary-equivalence invariant: any module algebra isomorphism permutes simple components, preserves each matrix size and field degree, and transports each multiplicity. Conversely, equality of types makes the normalized tensors equal by the standard frames. [Lenstra, Finding isomorphisms between finite fields](https://pub.math.leidenuniv.nl/~lenstrahw/PUBLICATIONS/1991b/art.pdf)

If the types agree, it remains to compute the determinant image of the automorphism group of the normalized action tensor. Apply the following list in each factor of type $(d,e,r)$, and to a transposition within any repeated type. The triple coordinates are still ordered as $(g,f,h)$.

| Generator | Determinant triple |
|---|---|
| Unit $u$ on that simple factor, with $t=\mathrm N_{E/F}\det_E u$ | $(t^d,1,t^r)$ |
| Inner conjugation by $P$, with $f=h=P$ on all $r$ copies and $t=\mathrm N_{E/F}\det_E P$ | $(1,t^r,t^r)$ |
| An invertible change $Q$ of the $r$ copies, with $t=\mathrm N_{E/F}\det_E Q$ | $(1,t^d,t^d)$ |
| Coordinatewise $q$-Frobenius, with $\epsilon=(-1)^{e-1}$ | $(\epsilon^{d^2},\epsilon^{dr},\epsilon^{dr})$ |
| Transposition of two equal-type blocks | $((-1)^{ed^2},(-1)^{edr},(-1)^{edr})$ |

For the first row, left multiplication acts on $d$ matrix columns and on $r$ copies of the natural module. Inner conjugation has determinant one on the matrix algebra, since the determinants of its left and right multiplications cancel. The centralizer action on $V$ is the multiplicity-space matrix action repeated $d$ times. A normal basis of $E/F$ shows that the $q$-Frobenius determinant on $E$ is $(-1)^{e-1}$. Equivalently after separable scalar extension Frobenius permutes the $e$ embeddings cyclically. Each block transposition has sign $(-1)^k$ on two copies of a $k$-dimensional $F$-block.

These operations generate the automorphisms. By Section 2, first remove the free unit $u$. The remaining $\alpha$ permutes equal types. Its action on the center field $E$ is a Frobenius power. Removing the permutation and Frobenius components leaves an $E$-linear matrix algebra automorphism. Such a map is conjugation by an invertible $E$-matrix: its images of the standard matrix units give a basis change by choosing a nonzero vector in the image of its first diagonal unit and applying the first-column units. On $V$ a canonical implementation of these conjugations acts independently on each copy of the natural module. Once they are removed, the residual $f$ commutes with all matrix units and the field, and so acts through the stated multiplicity-space changes. This finishes generation and exhausts the determinant image.

In the first three rows $t$ ranges over $F^\times$. Generate the subgroup of $(F^\times)^3$ from these rows, test the normalized target triple after frame calibration, and reject if the ordinary types disagree. This proves the claimed deterministic polynomial-time test. No oracle or transporter is needed.

## 5. An unbounded scalar-center family

Let $A$ be all upper triangular $d\times d$ matrices over $F$, $d\ge2$, and let
$$
   V=(F^d)^{\oplus(q-1)}\oplus(F_{\chi_1})^{\oplus(q-1)},
   \qquad \chi_1(a)=a_{11}.
$$
This action is faithful. Scaling one of the one-dimensional summands independently shows $H=F^\times$. On units $u$, both repeated blocks contribute determinant one, so $\det_F(u|_V)=1$. On the left regular space of $A$, the contribution of $u_{ii}$ is $u_{ii}^{d-i+1}$, as seen from the invariant column spaces. Choose a diagonal $u$ with all entries one except the last, which can be any element of $F^\times$. It contributes $(u_{dd},1)$ to $K$, proving the axis condition. The radical consists of the strictly upper triangular matrices and has nilpotency index $d$. The center is scalar, since commuting with each diagonal idempotent forces a diagonal matrix and commuting with each adjacent matrix unit forces all its entries equal.

The tensor centroid is also scalar. For an action tensor, its three endomorphisms $(c_U,c_X,c_Y)$ must satisfy $c_U(a)v=a c_X(v)=c_Y(av)$. Evaluating at $a=1$ gives $c_X=c_Y=c_U(1)$ in the action on $V$. Thus $c_U(1)$ commutes with the entire algebra, and faithfulness gives $c_U(a)=a c_U(1)$. Every central element conversely gives a centroid triple. Hence this family has no nontrivial centroid splitting or big centroid field to account for the determinant reduction.

The nearby centroid literature recovers multiplication tensors from cyclicity hypotheses for the centroid modules in equal format. The action-tensor recognition here uses the entire left idealizer, allows rectangular tensor formats and applies to noncommutative algebras. The two determinant results concern the induced action on both the faithful module and the regular algebra and do not require constructing a transporter. Publication priority for their combination has not been established. These statements concern raw action tensors. They leave the general determinant constraint on tensor pairs outside this class open. [Bernardi–Jelisiejew–Reig Fité, Hankel and Multiplication Tensor Completions for Cactus Rank](https://arxiv.org/abs/2606.30600) · [Chen–Grochow–Qiao–Tang–Zhang, Open Question 1.9](https://arxiv.org/html/2306.03135v2#S1.SS5)

The underlying algebra-conjugacy viewpoint is part of the tensor-isomorphism literature, and the radical-filtration norm identity was used in our earlier determinant computations. The additional steps here are recognition of the raw action tensor by a cyclic slice, the joint sufficient correction condition, and the explicit exhaustive semisimple determinant calculation. [Grochow–Qiao, matrix algebras and tensor isomorphism](https://doi.org/10.1137/21M1441110)

## 6. A TI-complete raw action-tensor domain satisfying the criterion

Take any unital associative algebra $B$ given by structure constants. Put $A=B\times F$, $J=\operatorname{rad}A$, and $V=A^{q-1}\oplus (A/J)^{q-1}$ with their natural left actions. The construction is polynomial over fixed $F$, and $V$ is faithful by its regular summand. Units have determinant one on $V$ because each natural block is repeated $q-1$ times. A unit supported on the added field factor supplies arbitrary determinant under left multiplication on $A$, so the first axis lies in $K$. One $F$-summand of $A/J$ can be scaled independently, so $H=F^\times$.

Two such action tensors are ordinarily isomorphic exactly when their algebras $A$ are isomorphic. The forward implication is the raw transporter calculation. For the reverse implication, an algebra isomorphism acts on the regular and quotient modules functorially and gives an action transporter. Also $B\times F\cong B'\times F$ implies $B\cong B'$ by cancellation of one field component from the unique factors determined by primitive central idempotents. Choose matching raw bases for the two copies of $V$ within each tensor. In these bases, the equality $y=z=1$ meets the required ratio from $K$; equivalently, the repeated module maps have determinant one and the unit on the added field adjusts the remaining determinant on $A$. Thus the same construction preserves ordinary yes/no answers as special-linear yes/no answers.

Unital associative algebra isomorphism is TI-hard even on a commutative class by Grochow–Qiao I, Corollary 8.5. Together with the criterion above this makes ordinary and special-linear isomorphism on this raw action-tensor domain TI-complete. It is a completeness result for a domain on which the determinant conditions are correctable. [Grochow–Qiao I, Corollary 8.5](https://arxiv.org/html/1907.00309)
