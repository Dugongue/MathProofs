# Orbit closures of cubic systems with partial radical image

Let $K$ be algebraically closed of characteristic three and let $V,W$ have dimensions $n,m$. Work with formal cubics $F\in\mathcal F(V,W)=W\otimes\operatorname{Sym}^3 V^*$. Write $T_F=\pi F$ for the coefficient of $abc$ in $F(ax+by+cz)$, and $R_F$ for its contraction radical. Put $r=\dim R_F$, $c=n-r$, and
$$
 E_0=\operatorname{span}F(R_F)\subset W,\qquad t=\dim E_0.
$$
Orbit closures have their reduced structure. The actions considered are $\mathrm{GL}(V)$ with fixed output labels and $\mathrm{GL}(V)\times\mathrm{GL}(W)$ with variable output basis.

For $E\subseteq W$, write $\rho_E:W\to W/E$ and $p_E(G)=(T_G,\rho_EG)$. If $S\subseteq R_G$ and $G(S)\subseteq E$, let $p_E(G)_{V/S}$ denote the induced pair on $V/S$. In particular $z_0=p_{E_0}(F)_{V/R_F}$ exists. For a chosen frame of $V/R_F$, let $X$ be the orbit closure of $z_0$ under $\mathrm{GL}_c$ in the fixed-output case, or under $\mathrm{GL}_c\times P_{E_0}$ in the variable-output case, with $P_{E_0}=\operatorname{Stab}_{\mathrm{GL}(W)} E_0$.

**Theorem.**

1. With fixed output labels, the reduced orbit closure of $F$ is exactly
   $$
   p_{E_0}^{-1}\!\left(\overline{\mathrm{GL}(V)\cdot p_{E_0}(F)}\right).
   $$
   It is a product of the pair orbit closure and $\mathbb A^{nt}$ after a linear splitting. Equivalently $G$ lies in the closure precisely when some $r$-plane $S\subseteq R_G$ has $G(S)\subseteq E_0$ and $p_{E_0}(G)_{V/S}\in X$ in a quotient frame.
2. With variable output basis, $G$ lies in the orbit closure precisely when some $r$-plane $S\subseteq R_G$ and $t$-plane $E\subseteq W$ satisfy $G(S)\subseteq E$ and $p_E(G)_{V/S}\in X$ in frames identifying $V/S$ with $K^c$ and $(W,E)$ with $(W,E_0)$.
3. The specified incidences are reduced varieties and map projectively and birationally onto the respective reduced closures. For each fixed target $G$ and each fixed candidate output plane $E$, the scheme of admissible $S$ is empty or exactly the scheme inside $\operatorname{Gr}(r,R_G)$ defined by the formal equations $(\rho_EG)|_S=0$. Put $K_E=\{v\in R_G:G(v)\in E\}$, a linear subspace. The nonempty fiber has reduction $\operatorname{Gr}(r,K_E)$. On its standard Grassmannian charts it is an affine space of dimension $r(\dim K_E-r)$ times $r(\dim R_G-\dim K_E)$ copies of $\operatorname{Spec}K[u]/(u^3)$.

These descriptions allow simultaneous drops of contraction rank, polarization output rank, and radical image rank. The lower-dimensional pair retains the full polarization in $W$ and only the cubic information in $W/E$.

## 1. Two linear facts

For a basis triple with multiplicities $1+1+1,\ 2+1,$ or $3$, polarization reads the associated monomial coefficient times $1,\ 2,$ or $6$, respectively. The kernel of $\pi$ is consequently the pure-cube subspace $D_V\otimes W$, where $D_V$ is the span of the cubes of coordinate linear forms and $\dim D_V=n$. The same computation over any commutative $K$-algebra shows that if a direct summand is contained in the contraction radical, every mixed monomial involving its coordinates vanishes. Thus for a complement $C$ of $R_F$,
$$
 F(x+y)=F_C(x)+q_F(y) \quad (x\in C,\ y\in R_F).
$$
The pure-cube map $q_F$ is represented by a coefficient matrix acting on cubed coordinates. Its set of values over $K$ is the linear image of that matrix because Frobenius is bijective. In particular its rank is $t\le r$. The same reasoning makes $K_E$ linear for every $G,E$, and proves the asserted descent of both components of $p_E(G)$.

The target of $p_E$ is the vector space of compatible pairs $(T,H)$ with $T\in\operatorname{im}\pi$ valued in $W$, $H\in\mathcal F(V,W/E)$, and $\rho_E T=\pi H$. The map onto this space is surjective. Lift $T$ arbitrarily to a cubic $\widetilde G$, then lift the pure-cube difference $H-\rho_E\widetilde G$ to pure cubes in $W$. Its kernel is $D_V\otimes E$. Hence the inverse image of a reduced subvariety of the compatible pairs is its product with $\mathbb A^{nt}$ after a linear splitting.

## 2. The orbit above a pair

Fix $E=E_0$ and consider a pair in the orbit of $p_E(F)$ under input changes only. Its radical is an $r$-plane $S$ and all lifts $G$ satisfy $G(S)\subseteq E$. Of these lifts the ones with radical image equal to $E$ form an open dense subset of each affine fiber of $p_E$. In an adapted basis the $r$ radical coefficients in $E$ are unrestricted, so requiring rank $t$ is a nonempty maximal-rank condition. This condition is regular on the pair orbit, since the kernel of a fixed-rank contraction matrix has local frames.

Every lift with radical image $E$ belongs to the orbit of $F$. To see this, transport the pair first, so it agrees exactly with $p_E(F)$. Use a common complement $C$ and a basis for $E$. On the common radical $S$, both $q_F$ and $q_G$ are coordinatewise cubes of surjective linear maps $\ell_F,\ell_G:S\to K^t$. On $C$, $F_C-G_C$ has polarization zero and values in $E$, so is the coordinatewise cube of a linear map $b:C\to K^t$. Choose an invertible $L:S\to S$ with $\ell_G L=\ell_F$ and a shear $A:C\to S$ with $\ell_G A=b$. Then $G(x+Ax+Ly)=F(x+y)$. Conversely, input changes preserve the radical image $E$ and carry the pair within its orbit. Taking reduced closures in the affine product of Section 1 proves the fixed-output product assertion.

The same argument works with a prescribed pair transporter on $V/S$ and a prescribed output change taking $E_0$ to $E$. First transport the frames and pair, then apply the radical reparametrization and shear. This observation will also identify the dense orbit in the variable-output incidence.

## 3. Incidence over the Grassmannians

Use the base $\operatorname{Gr}(r,V)$ for fixed outputs, or $\operatorname{Gr}(r,V)\times\operatorname{Gr}(t,W)$ for variable outputs. In local Grassmannian charts, choose frames for the quotient $V/S$ and, in the variable-output case, for $W$ adapted to $E$. Impose $S\subseteq R_G$, $(\rho_EG)|_S=0$ as a formal cubic, and membership of the descended pair in $X$. In an adapted input basis the first two constraints are linear in the coefficients of $G$ and define a vector subbundle. In the same coordinates the map from that subbundle to the compatible quotient pairs is a surjective linear map with kernel $D_V\otimes E$. Surjectivity follows by extending any lift on $V/S$ to $V$. Consequently the incidence scheme is locally the product of the base chart, $X$, and $\mathbb A^{nt}$. These conditions patch because $X$ is invariant under changes of the chosen frames. They define a closed reduced incidence in the product of the Grassmannians with $\mathcal F(V,W)$. The image projection is projective. The incidence is irreducible because its base and the fiber $X\times\mathbb A^{nt}$ are irreducible.

The part of the incidence with quotient pair in the orbit of $z_0$ and radical image on $S$ of dimension $t$ is dense. Indeed the pair orbit is dense in $X$, and the $r$ pure-cube coefficients on $S$ can be varied independently in $E$. That part projects exactly onto the indicated orbit of $F$ by the lifting calculation. The image of the entire incidence is therefore its orbit closure. In particular the conditions on $S,E$ are sufficient even on lower-rank strata.

For fixed outputs, the projection is an isomorphism over the nonempty open locus $\dim R_G=r$, where its inverse recovers $S=R_G$. The kernel is regular by the constant-rank minors. For variable outputs, add the condition that the pure-cube coefficient matrix of $G|_{R_G}$ has rank $t$. On the first open locus the criterion forces rank at most $t$, so rank $t$ is open there and occurs at $F$. Its inverse recovers $S=R_G$ and $E$ as the image of that matrix. A change of basis on $R_G$ changes this matrix by the entrywise cube of an invertible matrix. Its image is regular on the rank-$t$ locus without taking cube roots. These inverse formulas on reduced schemes prove birationality.

## 4. Scheme fibers over a fixed output plane

Fix $G,E$, and suppose the fiber is nonempty. Choose a complement of $R_G$ in $V$ and a complement of $K_E$ in $R_G$. The subgroup acting arbitrarily on $K_E$ and fixing both complements preserves $T_G$ and $\rho_EG$. It is transitive on $r$-planes in $K_E$. It follows that if one eligible plane has its quotient pair in $X$, every plane in $K_E$ does.

For scheme structure, choose any $S_0\subset K_E$ of dimension $r$. Write $R_G=S_0\oplus K'\oplus B$, where $K_E=S_0\oplus K'$. In the Grassmannian chart about $S_0$, a variable plane is the graph of $(a,b):S_0\to K'\oplus B$. Since the radical is a fixed kernel, the condition that the plane lie in $R_G$ holds scheme-theoretically. The pure-cube coefficient matrix of $(\rho_EG)|_B$ has independent columns. Thus $(\rho_EG)|_S=0$ in this chart is precisely the equations $b_{ij}^3=0$. On the scheme they define, the unipotent substitution $u$ sending $s$ to $s+a(s)+b(s)$ and fixing the chosen complement of $S_0$ preserves the full pair $(T_G,\rho_EG)$. This holds over the coordinate algebra because $T_G$ vanishes on radical arguments and $(\rho_EG)(a(s)+b(s))=0$ as a formal cubic there. Therefore $u$ identifies the descended pair on $V/S_0$ with the one on $V/S$. In the induced quotient frames the $X$-equations are evaluated on the constant pair at $S_0$ and vanish identically. Changing frames preserves the $X$-condition as a closed subscheme. The charts cover the support, proving the exact scheme-fiber claim.

Equivalently this fiber is the inverse image, under the relative Frobenius on $\operatorname{Gr}(r,R_G)$, of the Grassmannian of $r$-planes in the Frobenius twist of $K_E$. Its multiplicity at its generic point is $3^{r(\dim R_G-\dim K_E)}$. This statement applies after fixing $E$ in the variable-output incidence as well.

## 5. Examples

Let $V=K^3$ with coordinates $x,y,z$, and take the ordered pair $F=(x^2y+z^3,x^2y)$, with $E_0$ the first output line. The pair $G=(x^2y,x^2y+y^3)$ has the same polarization and radical line, and its radical image is zero. It fails the orbit-closure test. The unique candidate $S$ is the radical line. The quotient cubic in the second output would have to degenerate from $x^2y$ to $y(x^2+y^2)$ under binary substitutions. Having a repeated root is Zariski closed for binary forms by the discriminant, and the three linear factors of $y(x^2+y^2)$ are distinct in characteristic three. Thus a polarized degeneration and radical image containment alone can leave a nontrivial cubic condition.

On the other hand $y\mapsto x+\tau y$ degenerates $F$ to $(x^3+z^3,x^3)$ at $\tau=0$. The radical grows to $V$, and the fixed-output reduced fiber is $\operatorname{Gr}(1,\ker x)\cong\mathbb P^1$. The full fiber in $\mathbb P^2$ is the triple line with equation $x^3=0$.

For the variable-output action, also substitute $z\mapsto \tau z$ and multiply the second output by $\tau$. The target is $J=(x^3,0)$. Every $E\in\mathbb P(W)$ is admissible for some $S$. At $E=E_0$ the quotient pair is zero, attained by scaling the input to zero, and all $S$ occur. At $E\ne E_0$ the plane must lie in $\ker x$, and the quotient pair has zero polarization and nonzero pure-cube second coordinate after framing $E$ as $E_0$. That is a limit of $z_0$ by $y\mapsto x+\tau y$ on its two-dimensional domain, with a constant nonzero scaling on the quotient output if needed. Both the domain line of a nonzero pure cube and its coefficient can be matched by such frame changes. Hence the entire reduced incidence fiber over $J$ is the reducible union
$$
  \bigl(\mathbb P(V)\times\{E_0\}\bigr)
      \ \cup\
  \bigl(\mathbb P(\ker x)\times\mathbb P(W)\bigr).
$$

Write $S=[a:b:c']$ and $E=[u:v]$ in the two projective factors. The full scheme fiber is the divisor $va^3=0$. The containment equation is precisely $va^3=0$. Within that candidate scheme every descended pair has zero polarization, hence its other component is a pure cube in the formal coefficient sense. The compatible linear subspace with zero polarization is contained in $X$ scheme-theoretically. Indeed the exhibited degeneration and input basis changes put every nonzero pure cube in $X$, and scaling gives zero. The subspace is reduced, so these pointwise memberships give scheme inclusion. Thus the $X$-equations add no conditions. The two components have multiplicities one and three, respectively.

Running `python Systems.py` checks all 11,232 elements of $\mathrm{GL}(3,\mathbb F_3)$ for the ordered pair example and finds 18 orbit lifts in its 27-point affine slice. It also counts 25 rational flags in the reducible example and compares 243 lifts on the triple-line chart with 27 on its reduction over $\mathbb F_3[\epsilon]/(\epsilon^4)$ at a fixed rational point.

## Relation to prior work

The pure-cube kernel is the degree-three instance of the Frobenius-twist polarization kernel described by Garibaldi and Nakano. The Grassmannian construction uses the same proper homogeneous-bundle mechanism as collapsing maps. Here the fiber model consists of a compatible pair orbit closure and a pure-cube affine space. The exact fixed-output product for partial radical image and the nonreduced incidence fibers use the radical lift and are the specific statements proved above. [Garibaldi–Nakano, Proposition 3.5.1](https://arxiv.org/abs/1501.07515) · [Lőrincz, collapsing in arbitrary characteristic](https://arxiv.org/abs/2008.08270)

Christandl, Gesmundo, and Zuiddam characterize degeneration of full-rank tensor flattenings by Grassmannian degeneration of their image planes. Bürgisser, Landsberg, Manivel, and Weyman use Grassmannians to pass between polynomial orbit closures with different ambient numbers of variables. The input plane here is controlled by contraction, while the output plane records a Frobenius image of its radical. The residual quotient cubic and the scheme fibers both depend on this distinction. [Christandl–Gesmundo–Zuiddam, Theorem 4.3](https://ir.cwi.nl/pub/34472/34472.pdf) · [Bürgisser–Landsberg–Manivel–Weyman, Section 6.3](https://people.tamu.edu/~jml/BLMWpublished.pdf)

Grochow and Qiao study reductions among equivalence problems for forms, tensors, and algebras. Grochow, Mulmuley, and Qiao study degenerations in algebraic complexity. The theorem above describes precisely which data survive a cubic-system degeneration in characteristic three and how the input and output flags can vary. The remaining test is a smaller compatible pair orbit closure, and its membership complexity is outside the theorem. The proof is mathematical prose. The nearby primary sources establish background, and priority for these statements is open. [Grochow–Qiao, linear-length reductions](https://arxiv.org/abs/2306.16317) · [Grochow–Mulmuley–Qiao, *Boundaries of VP and VNP*](https://doi.org/10.4230/LIPIcs.ICALP.2016.34)

