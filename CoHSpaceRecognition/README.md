# Polynomial-time recognition of co-H-spaces in dimension at most $4c-2$

**Theorem.** Fix $c\ge 2$. There is a deterministic polynomial-time algorithm that, given a finite pointed simplicial complex $X$ promised to be $(c-1)$-connected and of dimension at most $4c-2$, decides whether its diagonal $X\to X\times X$ factors up to pointed homotopy through $X\vee X$. In particular, this decides co-H-space recognition for simply connected finite complexes of dimension at most six.

The argument uses the effective Moore–Postnikov tower and stable section groups of Čadek, Krčál and Vokřínek. At the first stage beyond the stable existence range, the second difference of the obstruction factors through a cup product. Co-H-spaces have zero cup products in positive degrees, so the algorithm either rejects by a cup product or solves a linear equation in a finitely generated abelian group.

## The lifting problem

Give $X$ an ordering of vertices and use its finite simplicial-set model. The simplicial product contains the wedge, and the diagonal is a simplicial map. Set $B=X\times X$, $Y=X\vee X$, $g=\Delta_X$ and $f:Y\hookrightarrow B$. Both $Y$ and $B$ are simply connected. An unpointed homotopy factorization can be made pointed. First use a path from the value of the lift at the basepoint to the basepoint of $Y$ and extend it to a homotopy of the lift. The resulting homotopy in $B$ traces a based loop at the basepoint of $X$. Contract that loop in $B$ and use homotopy extension on $(X\times\{0,1\})\cup(\{*\}\times I)\subseteq X\times I$ to make the homotopy pointed.

The homotopy fibre $F$ of $f$ has homotopy type $\Omega X*\Omega X\simeq\Sigma(\Omega X\wedge\Omega X)$. Indeed, applying the fibrewise join construction to the two maps $X\times *\to B$ and $*\times X\to B$ constructs their homotopy pushout over $B$. Their homotopy pullback is contractible, and their respective homotopy fibres are the two copies of $\Omega X$. This is the sectional fat-wedge construction for $*\hookrightarrow X$ with two factors. It follows that $F$ is $d$-connected for $d=2c-2$. [García-Calcines and Vandembroucq, Definition 6 and Theorems 5 and 8](https://arxiv.org/abs/0901.4426)

Use the Moore–Postnikov stages $P_i\to B$ of $f$. Write $A=\pi_{d+1}F$, $C=\pi_{2d+1}F$, and let $k\in H^{2d+2}(g^*P_{2d};C)$ be the class of the next principal stage, pulled back along $g$. These are constant coefficients since $B$ and $X$ are simply connected. Put $P=g^*P_{2d}$ and let $p:P\to X$ be its projection. The stable-stage procedure decides whether $P$ has a section. If it does, fix a zero section $o:X\to P$. With this choice the section classes form an abelian group $G$. Its sum is induced by a fibrewise multiplication $m:P\times_X P\to P$ that restricts to the fold on the wedge of the two axes, up to fibrewise homotopy. Čadek, Krčál and Vokřínek construct a strictified model of this operation after the pullback and identify the resulting group with the effective section group. [Čadek, Krčál and Vokřínek, Theorems 4.13, 4.15, 4.16 and 5.4 and Section 6.7](https://arxiv.org/abs/1307.6444v4)

For $s\in G$ set $\omega(s)=s^*k\in H^{2d+2}(X;C)$. The class $s$ lifts to $g^*P_{2d+1}$ exactly when $\omega(s)=0$. The map from $Y$ to $P_{2d+1}$ induces a $(2d+2)$-connected map on the fibres over $B$. The first further obstruction to lifting a section to $Y$ has degree at least $2d+3$. Since $\dim X\le 2d+2$, a section at stage $2d+1$ gives a homotopy lift into $Y$. [Čadek, Krčál and Vokřínek, Sections 3.1 and 3.6](https://arxiv.org/abs/1307.6444v4)

## The second difference

The fibre $F'$ of $p$ is the $2d$-th Postnikov truncation of $F$. Its first possible nonzero reduced homology is $H_{d+1}(F';\mathbb Z)=A$, by Hurewicz. There is a class $\tau\in H^{d+1}(P;A)$ whose restriction to each fibre corresponds to $\operatorname{id}_A$ and such that $o^*\tau=0$. The only possible differential out of the fundamental class in bidegree $(0,d+1)$ of the cohomological Serre spectral sequence lands in the row of the base. It vanishes because the section makes $p^*$ injective. The fibre class therefore extends to $P$. Subtract the pullback of the extension's restriction to the zero section to obtain $\tau$.

Put $D=P\times_X P$ and let $W=P\vee_X P$ be the union of the axes defined by $o$. Use the simplicial pullback models for these pairs. The axes meet in $o(X)$, and restriction from either axis to $o(X)$ is onto in cohomology since each axis retracts onto $o(X)$. Mayer–Vietoris therefore makes restriction from $H^*(W;C)$ to the two axes injective. The class

$$
\delta=m^*k-\operatorname{pr}_1^*k-\operatorname{pr}_2^*k+(p\circ\operatorname{pr}_1)^*o^*k\in H^{2d+2}(D;C)
$$

restricts to zero on each axis by the unit property. It lifts to a relative class $\widetilde\delta\in H^{2d+2}(D,W;C)$.

The relative Serre spectral sequence for the pair over $X$ has fibre pair $(F'\times F',F'\vee F')$. Its reduced quotient is $F'\wedge F'$. This smash product is $(2d+1)$-connected and has $H_{2d+2}(F'\wedge F';\mathbb Z)=A\otimes A$ by the reduced Künneth theorem. Thus restriction to the fibre pair induces an isomorphism

$$
H^{2d+2}(D,W;C)\;\cong\;\operatorname{Hom}(A\otimes A,C).
$$

In fact all fibre rows below degree $2d+2$ vanish, so the entry in bidegree $(0,2d+2)$ is the only term in that total degree and no differential meets it. Let $w:A\otimes A\to C$ be the image of $\widetilde\delta$.

Regard $\tau$ as the image of a relative class on $(P,o(X))$. The relative cup product $\operatorname{pr}_1^*\tau\smile\operatorname{pr}_2^*\tau$ is defined on $(D,W)$ with coefficients $A\otimes A$. Its fibre restriction corresponds to the identity on $A\otimes A$ by Künneth. Applying $w$ to its coefficients and forgetting relativity gives $\delta$. Pulling back along the pair of sections $(s,t)$ consequently gives

$$
\omega(s+t)-\omega(s)-\omega(t)+\omega(0)
=w_*\bigl(s^*\tau\smile t^*\tau\bigr).
$$

In particular, if the coefficient cup pairing in degree $d+1$ on $X$ is zero, then $s\mapsto\omega(s)-\omega(0)$ is a homomorphism from $G$ to $H^{2d+2}(X;C)$.

## Decision procedure and polynomial cost

1. Compute the tower through stage $2d+1$, including $A$, $C$, and the obstruction cocycle of that stage. Test the pairing

   $$
   H^{d+1}(X;A)\otimes H^{d+1}(X;A)\longrightarrow H^{2d+2}(X;A\otimes A).
   $$

   If any product is nonzero, reject. The external product of two positive-degree classes restricts to zero on $X\vee X$, and its pullback by $\Delta_X$ is their cup product. Hence a co-H factorization forces this pairing to vanish.
2. Run the stable procedure through stage $2d$. If it finds no section, reject. Otherwise compute the zero section $o$ and representatives $s_1,\ldots,s_r$ of generators of the fully effective section group $G$.
3. Evaluate $\omega$ on $o$ and on each $s_i$ by pulling back the obstruction cocycle to $X$. The pairing test makes $\omega$ affine, so accept exactly when $-\omega(o)$ belongs to the subgroup generated by the differences $\omega(s_i)-\omega(o)$ in $H^{2d+2}(X;C)$. This is a Smith normal form calculation.

For fixed $c$, all simplicial sets in the input have fixed dimension bounds and their wedge and product models have polynomial size. Čadek, Krčál and Vokřínek's Section 8 constructs polynomial-time families of extended towers of fixed length, their effective cocycles and pullbacks, and the zero sections and fully effective groups of sections through the stable stages. Its construction of these groups, including representatives, is stagewise and uses the stable condition on each stage through $2d$. The routine for stage $2d+1$ here only constructs the tower data and evaluates its cocycle on selected sections of the earlier stage. [Čadek, Krčál and Vokřínek, Section 8, pp. 50–52 of the arXiv preprint](https://arxiv.org/abs/1307.6444v4)

In these explicit simplicial models the coefficient cup pairing is computed on pairs of cohomology generators by the Alexander–Whitney formula, using presentations of the coefficient groups and Smith normal form. Each obstruction evaluation uses only the finitely many simplices of $X$ in degree $2d+2$, with the polynomial-time representations of the section and cocycle. The remaining subgroup membership computation uses the same integer linear algebra. Thus every step has polynomial cost for fixed $c$. The computed cup pairing suffices for this decision procedure. $\square$

Verification status is a written mathematical proof.
