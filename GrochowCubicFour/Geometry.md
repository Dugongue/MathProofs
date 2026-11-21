# Degeneration of forms through truncated local algebras

Let \(K\) be algebraically closed, \(V\) an \(n\)-dimensional \(K\)-vector space with \(n\geq2\), and \(d\geq3\). Write \(P=\operatorname{Sym}^dV\). We consider the group action on forms induced by its action on \(V\), with no restriction on the characteristic.

For \(f\in P\) define the commutative local algebra
\[
 A_f=\operatorname{Sym}(V\oplus Kz)/
       \big((V,z)^{d+1},\,zV,\,z^d-f\big).
\]
A fixed vector space \(E\) and its grading work for every \(f\). The degree-zero piece is \(K\), the degree-\(i\) piece for \(1\leq i<d\) is \(\operatorname{Sym}^i V\oplus Kz^i\), and the degree-\(d\) piece is \(P\). Write \(\mu_f\) for multiplication on this fixed space and let \(\operatorname{GL}(E)\) act by change of basis on all commutative multiplication laws \(M_E=\operatorname{Hom}(\operatorname{Sym}^2 E,E)\). The orbit includes all laws isomorphic to \(A_f\), regardless of the location of their identity elements.

**Theorem 1.** For every \(f,g\in P\),
\[
 g\in\overline{\operatorname{GL}(V)\cdot f}
 \quad\Longleftrightarrow\quad
 \mu_g\in\overline{\operatorname{GL}(E)\cdot\mu_f}.
\]
The closures are Zariski closures in the indicated affine spaces. In particular the equivalence includes \(g=0\) and holds when the characteristic divides \(\dim E\).

**Theorem 2.** Two form orbits have a common nonzero degeneration if and only if their algebra orbit closures meet at a local algebra satisfying the intrinsic rank and nonvanishing conditions below. The common algebra may be filtered with respect to its maximal ideal rather than graded.

**Theorem 3.** There is an affine multiplication-law encoding with an invertible frame and its inverse, given by a polynomial map of polynomial size for fixed \(d\). Two \(\operatorname{SL}(V)\)-form orbit closures intersect if and only if the orbit closures of their encodings intersect in the full ambient representation. The closed invariant family of encodings, including all their translates, has exactly the invariant ring of the original form space.

## Intrinsic recovery

The algebra description follows by killing mixed monomials, monomials of degree above \(d\), and the single relation in degree \(d\). The positive-degree ideal \(\mathfrak m\) is nilpotent with quotient \(K\), so it is the unique maximal ideal. Since the algebra is generated in degree one, \(\mathfrak m^i=\bigoplus_{j\geq i}E_j\) for \(i\geq1\). Hence the algebra is its own associated graded algebra up to the canonical identification using that grading.

Multiplication by \(z\), viewed as a map \(E_1\to E_2\), has rank one and sends \(z\) to \(z^2\neq0\). Multiplication by \(v+bz\) with \(v\in V\setminus\{0\}\), restricted to \(V\), has rank \(n\). It is ordinary multiplication by \(v\) in the polynomial ring \(\operatorname{Sym}(V)\). Thus \(Kz\) is the unique line of rank at most one, and the kernel for a nonzero element of that line is \(V\). An isomorphism between such graded algebras consequently acts by \(S\in\operatorname{GL}(V)\) and \(z\mapsto az\), with \(a\neq0\). For an isomorphism from \(A_f\) to \(A_g\), the top-degree equation is
\[
 (\operatorname{Sym}^d S) f=a^d g.
\]
The change of variables \(a^{-1}S\) sends \(f\) to \(g\) over the same field. An ungraded isomorphism induces the required graded isomorphism via maximal-ideal powers. The argument works over any field, and the same formula holds after choosing any bases and generators for the recovered summands.

The line can also be recovered by linear algebra once the degree-one and degree-two multiplication is available. In basis coordinates \(u=\sum_i a_i x_i+bz\), the rank-two minors span the quadratics \(a_i a_j\) for \(i\leq j\) and \(a_i b\). For \(a_i^2\), use columns \(x_i,x_j\) with \(j\neq i\) and rows \(x_i^2,x_i x_j\). For \(a_i a_j\) with \(i\neq j\), use columns \(x_i,x_j\) and rows \(x_i^2,x_j^2\). For \(a_i b\), use columns \(x_i,z\) and rows \(x_i^2,z^2\). Every minor vanishes at \(u=z\), so these give exactly the codimension-one subspace of quadratics vanishing at that point. In arbitrary coordinates the annihilator of the span of the minors is consequently the evaluation line in the dual of the quadratic space. Its coordinates in a monomial basis are proportional to \(z_i z_j\). Choose \(i\) with nonzero diagonal coordinate and divide the \(ij\) coordinates by the \(ii\) coordinate to recover the projective line. The same computation works in characteristic two.

## Proof of Theorem 1

The map \(f\mapsto\mu_f\) is a closed affine embedding. The structure constants are fixed except for the products \(z^i z^{d-i}\) with \(1\leq i<d\), each of which has coordinate vector \(f\). In particular one reads \(f\) from \(z z^{d-1}\). Let \(\rho(S)\) act on each \(\operatorname{Sym}^i V\) by the corresponding symmetric power of \(S\), and fix \(1,z,\ldots,z^{d-1}\). Then \(\mu_{S\cdot f}=\rho(S)\cdot\mu_f\), which proves the forward implication by continuity.

For the reverse implication we use a discrete valuation ring \(R\), with fraction field \(L\) and residue field \(K\), on which an \(R\)-law \(B\) specializes from \(A_f\otimes_K L\) to \(A_g\). Here is a direct way to arrange the actual generic isomorphism. Take the closure of the graph of \(T\mapsto T\cdot\mu_f\) in \(\mathbb P(K\oplus\operatorname{End}(E))\times M_E\), embedding \(\operatorname{GL}(E)\) in the affine chart of that projective space. Projectivity makes the image closed, so take a closed point in the graph closure above \(\mu_g\). Unless the graph closure has dimension zero, choose an integral curve through that point with generic point in the graph. Such a curve can be obtained in an affine neighborhood by Noether normalization. Under the finite map from Noether normalization to affine space, the graph boundary has proper closed image by the dimension inequality. Take a line through the image of the chosen point whose generic point avoids that image. The inverse image is cut out by one fewer equations than the dimension of the affine neighborhood. A component through the chosen point has dimension at least one by the principal ideal theorem and at most one by finiteness. It therefore dominates the line. Normalize this curve and take the local ring at a point above the chosen closed point. This gives the DVR and the generic change of basis. In dimension zero the orbit is already closed, and \(R=K[t]_{(t)}\) with a constant law suffices.

An identity for \(B\) can be recovered even though no identity was marked in \(M_E\). The linear system for an identity is \(L_e=I_E\), where \(L_a\) denotes multiplication by \(a\). The map \(a\mapsto L_a\) has full column rank over the residue field because the special law has an identity. Choose a full-rank minor that is a unit in \(R\). Solve the selected equations over \(R\). They give the generic identity by uniqueness, and all the other equations hold in \(R\) because they hold in \(L\). Associativity also holds integrally because it holds generically.

The generic augmentation \(\epsilon_L:B\otimes_R L\to L\) extends to \(\epsilon:B\to R\). For every \(a\in B\), \(\epsilon_L(a)\) is an eigenvalue of the transpose of multiplication by \(a\), since the linear functional \(\epsilon_L\) is a nonzero left eigenvector. It is therefore integral over \(R\), and belongs to \(R\) by integral closedness. The extended map is a unital algebra homomorphism and specializes to the unique augmentation of \(A_g\). Its kernel \(\mathfrak n\) is an \(R\)-module summand of \(B\), with both fibers the required maximal ideals.

For every \(i\geq1\), the multiplication image \(\mathfrak n^i\) is the image of \(\mathfrak n^{\otimes i}\to B\). The ranks of this map over \(L\) and \(K\) agree, by the constant graded dimensions of \(A_f\) and \(A_g\). Over a DVR, diagonalize the matrix using Smith normal form. Equality of ranks means that every nonzero diagonal entry is a unit. Thus \(\mathfrak n^i\) is a direct summand and has the stated ideal-power images after both base changes. The nested flags, their quotients, and their multiplication give a free graded algebra \(\operatorname{gr}_{\mathfrak n}B\) with both prescribed associated graded fibers. For instance, freeness of \(\mathfrak n^i/\mathfrak n^{i+1}\) follows because it is a submodule of \(B/\mathfrak n^{i+1}\), and the free quotients make base change exact.

Write \(W_1,W_2,W_d\) for degrees \(1,2,d\) of this graded algebra. The distinguished generic line in \(W_1\otimes_R L\) has a primitive generator \(z_R\in W_1\), obtained by scaling a vector in the line by a power of a uniformizer. All rank-two minors of multiplication \(m_{z_R}:W_1\to W_2\) vanish over \(L\), hence over \(R\). Primitivity ensures \(\bar z_R\neq0\). The special rank calculation now identifies its line, with \(m_{\bar z_R}\) of rank one and \(\bar z_R^2\neq0\). The kernel \(V_R\) of \(m_{z_R}\) is a rank-\(n\) summand, and its formation commutes with both base changes by the same unit-minor argument. Over \(K\), its basis together with \(\bar z_R\) is a basis of \(W_1\otimes K\), so \(W_1=V_R\oplus Rz_R\) by the unit determinant test.

The multiplication map \(\operatorname{Sym}^d V_R\to W_d\) is an isomorphism. It is between free modules of the same rank and its special fiber is the ordinary multiplication isomorphism on \(A_g\). Pull \(z_R^d\) back by this isomorphism to obtain \(h_R\in\operatorname{Sym}^d V_R\). With any basis of \(V_R\), the two fibers of \(h_R\) are equivalent to \(f\) over \(L\) and \(g\) over \(K\). Indeed the recovered line generator can rescale by \(a\) in either fiber, and the corresponding factor \(a^d\) is absorbed by a scalar change of variables. The resulting morphism from \(\operatorname{Spec}R\) to \(P\) sends its generic point into the orbit closure of \(f\), so it sends its closed point into that closure. The closure is \(\operatorname{GL}(V)\)-stable and hence contains \(g\). This proves the converse without using a trace expression for the augmentation.

## Directional degeneration of the ordinary multiplication tensors

Theorem 1 also holds with the **full ordinary three-tensor orbits** of the multiplication tensors in place of the unmarked algebra-law orbits. In particular the three legs may change independently. Here is the reduction from a tensor specialization back to a law specialization.

Use vector spaces $U,V,W$ of the common algebra dimension and express a tensor as a bilinear map $\beta:U\times V\to W$. In fixed coordinates choose input elements $u_0,v_0$ that are the two identity elements at the endpoint $\mu_g$. On the open set where both $D_\beta=\beta(-,v_0)$ and $E_\beta=\beta(u_0,-)$ are invertible, put
\[
 m_\beta(x,y)=\beta(D_\beta^{-1}x,E_\beta^{-1}y).
\]
This is a regular map on that open set, and $m_{\mu_g}=\mu_g$. If $\beta$ is in the ordinary tensor orbit of $\mu_f$, write $\beta(u,v)=H(Pu\cdot Qv)$ using the product of $A_f$ and three invertible maps. Put $a=P(u_0)$ and $b=Q(v_0)$. Invertibility of the two slices implies that multiplication by $a$ and by $b$ is invertible, so both are units. In $H$-coordinates, $m_\beta(x,y)$ is the product of $H^{-1}x$ and $H^{-1}y$ multiplied by $(ab)^{-1}$. Thus $x\mapsto(ab)^{-1}H^{-1}x$ is an algebra isomorphism from $m_\beta$ to $A_f$.

An orbit is dense in its closure, and density persists on the open set containing $\mu_g$. If $\mu_g$ is a limit of ordinary tensor translates, the regular map therefore puts $\mu_g$ in the algebra-law orbit closure of $A_f$. Theorem 1 recovers the original form degeneration. The forward implication uses the simultaneous basis change on the two inputs and output, which is a particular ordinary tensor action. This also transfers the nonzero common-degeneration test of Theorem 2 to a common tensor with one invertible slice in each input direction, by applying the same law normalization before testing the intrinsic rank and nonvanishing conditions.

## Proof of Theorem 2

The intrinsic conditions on the common witness \(B\) are as follows. It is a finite-dimensional local commutative unital algebra with residue field \(K\), and its maximal ideal \(\mathfrak m\) has \(\mathfrak m^{d+1}=0\) and associated graded dimensions equal to those of \(A_f\). In degree one there is a line \(Kz\) for which multiplication \(m_z\colon \operatorname{gr}^1 B\to\operatorname{gr}^2 B\) has rank one and \(z^2\neq0\). For \(V_B=\ker m_z\) the multiplication map \(\operatorname{Sym}^d V_B\to\operatorname{gr}^d B\) has full rank, and \(z^d\neq0\) in degree \(d\).

These conditions imply \(\operatorname{gr} B\cong A_h\) for a nonzero form \(h\). The kernel condition and \(z^2\neq0\) give degree one as \(V_B\oplus Kz\). The associated graded algebra is generated by degree one. Since \(zV_B=0\), in degree \(i<d\) the only spanning monomials lie in \(\operatorname{Sym}^iV_B\) and \(Kz^i\). The dimensions force independence and identify those pieces with their counterparts in \(A_h\). Degree \(d\) is exactly the given symmetric power, and \(h\) is the preimage of \(z^d\). This proves the presentation. It also gives uniqueness of the tested line by the degree-two calculation. The conditions can be checked on the ideal-power flags and multiplication maps, with nonvanishing of minors and of the top power on the locus in which the relevant dimensions are fixed.

For any such \(B\), choose a vector space splitting \(B=\bigoplus_{i=0}^d B_i\) of the ideal-power filtration, with \(B_0=K1\). Apply the change of basis acting by \(t^i\) on \(B_i\). A product component \(B_i\otimes B_j\to B_k\) is then multiplied by \(t^{k-i-j}\). Multiplicativity of the filtration makes the exponent nonnegative for every nonzero component. At \(t=0\) exactly the associated graded law remains. If both orbit closures contain \(B\), stability and closedness imply that both contain \(\operatorname{gr} B\), hence \(\mu_h\). Theorem 1 now gives a common nonzero form degeneration. Conversely, a common nonzero \(h\) gives the witness \(A_h\) by Theorem 1.

This test excludes the collapse that makes unrestricted algebra orbit closure intersection vacuous on this family. Every \(A_f\) degenerates to the unital algebra with \(\mathfrak m^2=0\) by acting as \(t^{-1}\) on its positive part and as the identity on \(1\). The nonzero common form test is equivalently common degeneration in projective form space for two nonzero forms. Indeed \(\operatorname{GL}(V)\)-orbits of nonzero forms are stable under all nonzero scalar multiples over \(K\). Their affine closures are cones, and their projectivizations are their projective orbit closures. Theorem 3 addresses the affine \(\operatorname{SL}(V)\) question, which retains invariants such as the value of a discriminant.

## Proof of Theorem 3

Let \(W\) be a copy of \(E\), with a fixed identification \(I:E\to W\). On the affine space
\[
 M_W\times\operatorname{Hom}(E,W)\times\operatorname{Hom}(W,E)
\]
let \(G=\operatorname{SL}(V)\times\operatorname{GL}(W)\) act by
\[
 (S,T)\cdot(\mu,Q,R)=
 (T\cdot\mu,\ TQ\rho(S)^{-1},\ \rho(S)RT^{-1}).
\]
Encode \(f\) as \((I\cdot\mu_f,I,I^{-1})\). The equations \(QR=I_W\) and \(RQ=I_E\) define a closed invariant subvariety \(Z\). Transport multiplication along \(Q^{-1}\). This gives the regular isomorphism
\[
 Z \longrightarrow M_E\times\operatorname{Iso}(E,W),
 \qquad (\mu,Q,R)\longmapsto(Q^{-1}\cdot\mu,Q).
\]
The inverse transports the multiplication back by \(Q\) and stores \(Q^{-1}\). Both expressions are regular, since the inverse matrices are supplied on \(Z\) or regular on the frame variety. Under this isomorphism the action becomes
\[
 (S,T)\cdot(\nu,Q)=(\rho(S)\cdot\nu,\ TQ\rho(S)^{-1}).
\]
After any choice of \(S\), the factor \(\operatorname{GL}(W)\) ranges over all frames independently. Each encoded orbit thus maps to the orbit of \(\mu_f\) under \(\rho(\operatorname{SL}(V))\) times \(\operatorname{Iso}(E,W)\). Taking closure in this product extends exactly the first factor. One inclusion follows from projection to the first factor, and for the other inclusion one takes the closure in each slice at a fixed frame. Closedness of \(Z\) makes these the full ambient orbit closures. Closedness and equivariance of \(f\mapsto\mu_f\) now give the claimed equivalence.

If \(F=\{\mu_f:f\in P\}\), the inverse image of \(F\times\operatorname{Iso}(E,W)\) in \(Z\) is closed and invariant in the full space. Its invariant regular functions descend to functions of \(\nu\) by evaluation at \(Q=I\), because invariance under the second group makes the value independent of \(Q\). Invariance under the first group is precisely invariance of the resulting function of \(f\) under \(\operatorname{SL}(V)\). Conversely any such function of \(f\) defines an invariant regular function on the closed family by projection in the trivialized coordinates. This identifies the two coordinate rings of invariants with no restriction on characteristic. In these coordinates an explicit source separating invariant yields a regular separating invariant on this closed family. The dimension of \(E\) is \(\binom{n+d}{d}+d-1\). Thus dense multiplication tables and the two frames have polynomial size for fixed \(d\).

## Binary cubics and the literature boundary

Take \(d=3,\ n=2,\ f=x^3+y^3,\ g=x^3\) in characteristic zero. The substitution \(y\mapsto t y\) specializes \(f\) to \(g\), and the only moving table entries are the coefficients of \(z z^2=x^3+t^3y^3\). The form \(f\) cannot occur as a degeneration of \(g\). The binary-cubic discriminant vanishes throughout the orbit closure of \(g\) and is \(-27\) at \(f\). Theorem 1 gives exactly the same strict direction for the algebras. For \(f\) and \(2f\), the unmarked algebras are isomorphic over \(K\) via a scalar change of variables, while their affine \(\operatorname{SL}_2\) orbit closures are disjoint. Their discriminants are \(-27\) and \(-432\), respectively, so Theorem 3 distinguishes them after adding frames. The recovered line and dimensions can be read from the same tables in characteristics \(2\) and \(3\), in which \(\dim E=12\) and the generic augmentation proof still applies.

Agrawal and Saxena compare ordinary isomorphism of cubic forms and finite-dimensional commutative algebras. Grochow and Qiao situate algebra isomorphism and cubic equivalence in tensor isomorphism complexity. Here the passage through valuation, rank and saturation addresses what survives taking an affine orbit closure for one particular algebra family. [Agrawal and Saxena, On the Complexity of Cubic Forms](https://www.cse.iitk.ac.in/%75sers/nitin/papers/cubic-forms.pdf) · [Grochow and Qiao, Isomorphism Problems for Tensors, Groups, and Cubic Forms](https://arxiv.org/abs/1907.00309)

Grochow, Mulmuley and Qiao study border complexity through orbit-closure degenerations and distinguish general degenerations from those realized by one-parameter subgroups. The converse here is for arbitrary orbit degenerations between the displayed endpoint algebras, via a curve and a DVR. This is a direction-preserving encoding of that form-geometric question inside multiplication laws. The paper's broader arithmetic circuit complexity results are separate. [Grochow, Mulmuley and Qiao, Boundaries of VP and VNP](https://doi.org/10.4230/LIPIcs.ICALP.2016.34)

Lysikov and Walter give a general framework for algebraic reductions among tensor orbit closure intersection problems. The inverse-frame construction above is a concrete transport of action on a closed locus. Its ambient representation is explicitly a space of multiplication laws and two linear maps under \(\operatorname{SL}(V)\times\operatorname{GL}(W)\). Recent fixed-parameter degree bounds for the standard product of special linear groups acting on three-way tensors concern a different representation. The proofs here do not transfer those bounds or identify the unframed algebra problem with that standard tensor problem. [Lysikov and Walter, Complexity theory of orbit closure intersection for tensors](https://arxiv.org/abs/2411.04639) · [Doğan et al., Fixed-Parameter Degree Bounds and Complexity of the Orbit Closure Intersection Problem for Tensors](https://doi.org/10.4230/LIPIcs.CCC.2026.32)

The specific scope of the contribution is the exact specialization equivalence for these intrinsic-line algebras, the resulting rank test for a nonzero common degeneration, and the closed representative with inverse frames for affine \(\operatorname{SL}(V)\) orbit closure intersection. The proofs are mathematical proofs in prose. Independent priority and Lean verification are unestablished.

An independent finite control checked all 722 binary cubic tables over the fields of orders 2, 3 and 5, including the ideal-power dimensions, the degree-one marker and the top power.
