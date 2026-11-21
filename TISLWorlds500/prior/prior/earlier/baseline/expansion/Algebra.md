# Algebraic additions to the ternary orientation atlas

Dependencies from the earlier atlas are the [cube-zero carrier](../baseline/earlier/CubeZeroAndExtensions.md), [regular forms and compact group reduction](../baseline/AlgebraWorlds.md), and the [constant-component packing](../baseline/LinearSwitchCompiler.md#packing-the-system).

Write \(H(F)\) for the deterministic polynomial-time many-one reduction \(\mathsf{TI}_{SL}(F)\le_m\mathsf{TI}(F)\) over a fixed finite field \(F\), and \(H=H(\mathbb F_3)\). Unless specified otherwise comparisons take explicit dense structure constants in ordered bases, and a reduction is deterministic polynomial-time many-one. For compact groups the input consists of commutator or commutator-and-power coefficients, without enumerating the group. A determinant condition on tensor multiplication uses bimap coordinates; using covariant tensors inverts the first two factors and preserves determinant one. Statements identified as unconditional hold in either branch. Internal proof dependencies refer to the other entries here, and *Cube-zero commutative rings and finite extension fields* and *Regular forms, extraspecial quotients, and determinant corrections* are the proved compilers from the earlier atlas.

<a id="entry-79"></a>

### 79. Associative tables with three fixed residue vertices

**Unconditional.** Ordinary TI over \(F\) is equivalent to isomorphism of the explicit unital associative tables \(A_T\) with quotient \(F^3\), radical cube zero, and three fixed positive off-diagonal corners. This is a different class from the commutative local class in the preceding atlas.

For \(T:U\times V\to W\), place its spaces in the \(01,12,02\) corners of a triangular algebra and define \(uv=T(u,v)\) as the only nonzero radical product. The diagonal is \(F^3\). All triple radical products vanish. Any algebra isomorphism aligns the lifted quotient idempotents by conjugation by a radical unit. The total directed order of the nonzero corners fixes the three vertex labels. The remaining isomorphisms on the corners are exactly the three independently acting maps transporting \(T\). Conversely these maps extend with identity diagonal. The reverse reduction takes the multiplication tensor and normalizes any isotopy at the unit as in [Entry 82](#entry-82). Zero formats can be decided directly. [Grochow and Qiao, tensor-to-algebra construction](https://doi.org/10.1137/21M1441110)

<a id="entry-80"></a>

### 80. Triangular corners programming arbitrary determinant exponents

**Unconditional.** For fixed \(F\), a specified character \(\prod_i d_i^{w_i}\) of the three bimap determinants is the exact algebra-isomorphism determinant image of bounded-radical-length triangular tables, with side dimension linear in the input format. Requiring determinant one in all three multiplication modes tests that character.

Replace corner \(i\) of [Entry 79](#entry-79) by its scalar extension to \(F[t]/(t^{k_i})\), with \(k_i\equiv w_i\pmod{|F^\times|}\), \(k_i\ge2\), and the output length no greater than either input length. The diagonal vertices are \(F[t]/(t^{M_j})\), with larger lengths. Align idempotents as in [Entry 79](#entry-79). The two actions of \(t\) on each corner agree, so the first-order parameter change is a common \(\lambda\) across the vertices. The determinant in the adapted layers is \(\prod_i(\det g_i)^{k_i}\lambda^{\sum_j\binom{M_j}{2}+\sum_i(\dim V_i)\binom{k_i}{2}}\). Choose \(M_j\) to cancel the exponent modulo \(|F^\times|\). Three triangular numbers represent every residue: modulo odd prime powers apply \(8\binom{M}{2}=(2M-1)^2-1\), use two squares by the pigeonhole principle, add a third to guarantee a nonzero coordinate, and lift that coordinate. Modulo \(2^a\), the first \(2^a\) triangular numbers give distinct residues by factoring their differences. Chinese remaindering and adding \(2|F^\times|\) as needed finish the lengths. Every original transporter lifts with \(\lambda=1\). The normalized multiplication argument in [Entry 82](#entry-82) identifies all-mode determinant one with determinant-one algebra isomorphism. [Prior weighted truncated-corner proof](https://github.com/Dugongue/MathProofs/tree/main/TensorDeterminantProfileMethods) · [Underlying triangular construction](https://doi.org/10.1137/21M1441110)

<a id="entry-81"></a>

### 81. A recognizable nonsemisimple class with ordinary TI degree

**Unconditional.** On raw associative multiplication isotopes with \(J^3=0\) and all simple residue matrix sizes divisible by \(m=|F^\times|\), SL-TI has exactly the ordinary TI degree over fixed \(F\).

For the upper direction apply [Entry 87](#entry-87) with common matrix size divisor at least divisible by \(m\), or the no-visible-corners case of [Entry 88](#entry-88). For hardness take the multiplication table of \(M_m(A_T)\) from [Entry 79](#entry-79). Unit-aligned isotopy implies algebra isomorphism; matching full matrix units and restricting to their first corner recovers \(A_T\cong A_{T'}\). Conversely an ordinary corner transporter extends entrywise, with determinant \((\det\phi)^{m^2}=1\). The radical stays cube zero and the promise is recognized by [Entry 82](#entry-82) and finite-algebra decomposition. This gives a concrete nonsemisimple locus of collapse even if \(H\) fails. [Finite-algebra decomposition, Theorem 18](https://arxiv.org/html/1708.03495)

<a id="entry-82"></a>

### 82. Raw associative isotopes and their three-coordinate calibration

**Unconditional.** A raw dense bimap can be recognized and normalized as a unital associative multiplication isotope in deterministic polynomial time. After normalization, three independent raw determinant conditions reduce to two unit-image tests and one prescribed algebra determinant.

Compute the adjoint pairs \((D,E)\) with \(T(Du,v)=T(u,Ev)\), and compare each projected operator representation with its regular module. On actual multiplication, those projections are the right and left regular operators, so constructive module isomorphisms yield cyclic vectors \(\alpha,\beta\) corresponding to units. The maps \(K_1=T(-,\beta)\), \(K_2=T(\alpha,-)\) normalize the input; verify they are invertible and that \(T(K_1^{-1}x,K_2^{-1}y)\) is unital associative. These checks make the recognition sound on arbitrary input. Every normalized isotopy is \((L_a\phi,R_b\phi,L_aR_b\phi)\): evaluate at each unit to see that \(a,b\) are units and \(\phi=a^{-1}h(-)b^{-1}\) is multiplicative. With \(\lambda_i=\det K_i/\det K_i'\), algebra determinant \(r\) and unit determinants \(u,v\), the raw determinant triple is \((\lambda_1ur,\lambda_2vr,uvr)\). Thus all-mode SL requires \(u=\lambda_2,\ v=\lambda_1,\ r=(\lambda_1\lambda_2)^{-1}\). [Brooksbank and Luks, constructive module isomorphism](https://ix.cs.uoregon.edu/~luks/ModIso.pdf)

<a id="entry-83"></a>

### 83. Left and right unit determinants can differ

**Unconditional.** Let the semisimple quotient be \(\prod_i M_{n_i}(E_i)\), and let \(\ell_i,r_i\) be the multiplicities of its natural simple left and right modules on the full associated radical filtration. The unit determinant images are respectively \((F^\times)^{\gcd(m,\ell_i\text{ for all }i)}\) and \((F^\times)^{\gcd(m,r_i\text{ for all }i)}\). Neither image can substitute for the other in [Entry 82](#entry-82).

On each filtration layer the residue action of a unit \(u_i\) contributes the field norm of its matrix determinant, to the power given by the module multiplicity. Multiply across the filtration, and use surjectivity of residue unit lifts, field norms and matrix determinants. The multiplicities are computed by the \(E_i\)-dimension of the action of a first diagonal matrix unit. For a concrete asymmetry over \(\mathbb F_3\), use a square-zero split two-vertex algebra with two radical blocks, one loop at vertex \(0\) and one arrow from \(1\) to \(0\), each one dimensional. The left multiplicities are \((2,2)\) and the right are \((3,1)\). The left image is trivial and the right image contains both signs. [Finite-algebra decomposition](https://arxiv.org/html/1708.03495)

<a id="entry-84"></a>

### 84. Inner determinant corrections depend on multiplicity differences

**Unconditional.** The determinant subgroup of inner automorphisms in [Entry 83](#entry-83) is exactly \((F^\times)^{\gcd(m,\ell_i-r_i\text{ for all }i)}\). It can distinguish algebras with the same two separate unit determinant images.

Conjugation by the unit \(u\) is \(L_uR_{u^{-1}}\), so the two regular actions use the **same** residue norm, with exponents of opposite sign. Take the product in [Entry 83](#entry-83) and use again surjectivity for each residue norm. For example \(\mathbb F_3[t]/(t^3)\) and \(UT_2(\mathbb F_3)\) both have the full left and right sign images. The former has trivial inner image by commutativity. In the latter the left and right multiplicities are \((2,1)\) and \((1,2)\), and an inner automorphism of determinant \(-1\) exists.

<a id="entry-85"></a>

### 85. Exact correction from a detachable radical annihilator

**Unconditional.** Put \(J=\operatorname{rad}(A)\), \(K_0=\{x\in J:xJ=Jx=0\}\) and \(Q=K_0/(K_0\cap J^2)\). For every nonzero \(ij\) component of \(Q\) as a residue bimodule, there are actual algebra automorphisms supplying \((F^\times)^{n_in_j}\). The product over these components is the exact determinant image of the constructed detached-bimodule automorphisms. A component on two matrix-size-one vertices absorbs all algebra determinant restrictions.

Choose a Wedderburn–Malcev section \(S\) and a complement to \(K_0\cap J^2\) as an \(S\)-bimodule in \(K_0\). Such complements exist by separability over finite fields. Take a further complementary summand of \(J\) containing \(J^2\). Every bimodule automorphism of the chosen detachable space extends identically on all other summands: its mixed products with \(J\) vanish. In a simple \(ij\) bimodule the multiplicity action has determinant equal to a field norm raised to \(n_in_j\), and the norm is surjective. Choose components independently. Together with [Entry 82](#entry-82), full correction gives a single ordinary TI test after the unit calibrations. [Wedderburn–Malcev background](https://doi.org/10.1007/978-1-4419-8616-0)

<a id="entry-86"></a>

### 86. Radical product support gives a Smith-form correction

**Unconditional.** For \(J^3=0\) the determinant image generated by independent scalar actions on individual degree-\(1\) and degree-\(2\) residue corners is computable exactly by Smith normal form. It can be full even when [Entry 84](#entry-84) and [Entry 85](#entry-85) contribute nothing.

Split \(J=V\oplus J^2\) as a residue bimodule. A scalar \(t_{1,ij}\) on \(V_{ij}\) and \(t_{2,il}\) on \((J^2)_{il}\) preserve multiplication exactly when \(t_{1,ij}t_{1,jl}=t_{2,il}\) for every nonzero product of the corresponding blocks. In the exponent group \(\mathbb Z/m\) these are integer linear equations; the determinant exponent is the dimension-weighted sum of the exponents. Smith normal form parameterizes this kernel and gives the exact subgroup image. In \(F[x_1,\ldots,x_s]/(x_1,\ldots,x_s)^3\) the common tangent rescaling has determinant exponent \(s+2\binom{s+1}{2}=s(s+2)\). Choose arbitrarily large \(s\) avoiding \(0,-2\) modulo every odd prime divisor of \(m\), and odd when \(2\mid m\). The image is then full, while the algebra is commutative and its radical annihilator lies in \(J^2\). [Kannan and Bachem, polynomial Smith normal form](https://doi.org/10.1137/0208040)

<a id="entry-87"></a>

### 87. One-corner reduction for arbitrary radical length

**Unconditional.** Let \(d=\gcd_i n_i\) for the simple residue matrix sizes of a normalized associative multiplication tensor. Let \(C=(F^\times)^g\) be any computed subgroup of actual automorphism determinants containing the inner image, such as the product of [Entry 84](#entry-84)–[Entry 86](#entry-86) where applicable. If \(g\mid d^2\), the calibrated SL comparison reduces to one ordinary TI comparison of a corner, irrespective of radical length.

Lift a complete \(d\)-by-\(d\) system of matrix units from the quotient. The algebra is \(M_d(B)\), with \(B=e_{11}Ae_{11}\). All such systems are conjugate: first align quotient systems, then for two lifts \(e_{ij},f_{ij}\) agreeing modulo \(J\) use the unit \(\sum_i f_{i1}e_{1i}\). An aligned isomorphism is entrywise, so in its ordered matrix-entry frames it has determinant \((\det\psi)^{d^2}\) for \(\psi:B\to B'\). In raw frames it has in addition the known frame ratio \(\kappa\). Thus its exact determinant image modulo \(C\) is \(\kappa(\det\psi)^{d^2}C=\kappa C\). Verify the residue types and the unit conditions in [Entry 82](#entry-82), then test this coset and ask ordinary TI for the two corners. Conversely a successful corner witness lifts entrywise and true automorphism determinants in \(C\) correct it. [Finite-algebra decomposition](https://arxiv.org/html/1708.03495)

<a id="entry-88"></a>

### 88. Heterogeneous matrix corners with logarithmic remaining widths

**Unconditional.** There is a single ordinary TI query for associative multiplication isotopes over fixed \(F\) when all bijections of the visible residue descriptors are polynomially enumerable without isomorphism queries, and each visible corner grade has dimension logarithmic in input length over its chosen endpoint center. There is no bound on the invisible widths or the total radical length.

Use the correction \(C=(F^\times)^g\) of [Entry 87](#entry-87) and raise determinants to \(h=m/g\). Align a residue section and matrix units. An \(ij\) first Peirce corner occurs \(n_in_j\) times in the full algebra, so its contribution disappears if \(g\mid n_in_j\). The permutation sign also disappears if \(h\) is even. Otherwise \(g\) is even and an odd-sized permuted block has odd \(n_in_j\), so both endpoints of that block are visible and the sign is known from the matching. In each remaining grade write the transported map as \(P\tau\) over the endpoint center \(E\), using the same \(\tau\) wherever that endpoint occurs. Its \(F\)-determinant is the norm of \(\det_E P\) times the determinant on the field coefficient space repeated once per grade basis vector. Read \(\det_E P\) from the small full exterior algebra, and the finite-field Frobenius sign from the trace-zero line of the quadratic subfield if it is present. Link the grades, all incidences, matrix units and determinant lines in a fixed-arity tensor system. One diagram per matching is polynomial-size, and ordinary TI OR combines them. Omitted wide corners make no contribution to the powered determinant. For example \(F[t]/(t^N)\times M_m(B)\) with arbitrary local \(B\) of scalar residue has only one visible residue vertex, whose corner grades are all one dimensional. [Tensor-system compiler, Theorem 4.1](https://arxiv.org/html/2306.03135v2)


<a id="entry-89"></a>

### 89. Peirce profiles without enumerating all residue matchings

**Unconditional.** The logarithmic visible-grade bound in [Entry 88](#entry-88) suffices for an exact determinant-profile computation by a deterministic polynomial-time Turing reduction to ordinary TI, with no bound on the number of visible matchings.

Use the diagram with determinant lines omitted and pin residue labels successively to find one realizable full visible matching. On the target self-instance, for each position in the stabilizer chain fix all earlier labels and try each possible image at the current position. Extend successful pins greedily to get representatives generating the visible permutation image. For each selected full matching, restore the determinant lines and test the constant number of possible powered values. On the identity matching this computes the character image of the kernel of visible permutations. Together with one value from each generator matching it generates the image on the entire aligned automorphism group. Inner alignment lies in the kernel of the powered determinant. A reference value times this subgroup, lifted modulo \(C\), is the exact relative determinant coset. [Entry 82](#entry-82) then recovers all three raw determinants. This uses decision queries and makes no claim about merging the adaptive computation into one TI instance. [Tensor-system compiler, Theorem 4.1](https://arxiv.org/html/2306.03135v2)

<a id="entry-90"></a>

### 90. Square-zero radical isomorphism as a colored incidence graph

**Unconditional.** Ordinary associative algebra isomorphism for \(J^2=0\) reduces to colored graph isomorphism in fixed characteristic. The graph retains all compatible Frobenius actions on the residue centers, including when their degrees differ.

With a residue section \(S\), the algebra is \(S\oplus J\) and is classified by the \(S\)-bimodule \(J\), up to quotient automorphisms. For centers of degrees \(e_i,e_j\) put \(b_{ij}=\gcd(e_i,e_j)\) and record the simple multiplicities \(a_{ij,t}\), \(t\bmod b_{ij}\), obtained by testing equality of the two actions of a chosen common-subfield generator up to \(q^t\)-Frobenius. Represent factor \(i\) by an oriented cycle of length \(e_i\) colored by \((n_i,e_i)\), and label ordered pairs of positions \((i,a),(j,b)\) by \(a_{ij,a-b}\). Graph maps are compatible cycle permutations and rotations, imposing precisely the twist change \(t\mapsto t+k_i-k_j\). Each admissible map lifts by a constructive bimodule isomorphism. This treats the full square-zero associative class, not only scalar-residue local algebras. [Lenstra, finite-field isomorphism algorithms](https://pub.math.leidenuniv.nl/~lenstrahw/PUBLICATIONS/1991b/art.pdf)

<a id="entry-91"></a>

### 91. Exact signed square-zero profiles from a graph oracle

**Unconditional.** The same graphs yield the complete calibrated transporter determinant profile for every raw square-zero-radical multiplication isotope, with polynomially many colored GI oracle calls.

Use pinning to lift a reference graph isomorphism and stabilizer-chain coset representatives for the target graph. Each has a constructive bimodule lift from [Entry 90](#entry-90). After removing the graph permutation and rotations, quotient inner conjugation reduces the remaining map to one fixing the residue section. Align sections by a unit from \(1+J\), which is unipotent, and the residual freedom is exactly an \(S\)-bimodule automorphism of \(J\). Its determinant group is [Entry 85](#entry-85) with \(Q=J\). Thus the graph-lift determinants, [Entry 84](#entry-84) and [Entry 85](#entry-85) generate the full subgroup. Compute the reference coset and use [Entry 82](#entry-82). If \(J\ne0\) the quotient after the known detachable correction has order at most \(\dim_F A\), so in variable field sizes this step requires no unbounded-size discrete logarithms. The fixed-characteristic algebra and module routines are deterministic. [Brooksbank and Luks](https://ix.cs.uoregon.edu/~luks/ModIso.pdf) · [Ivanyos and Qiao](https://arxiv.org/html/1708.03495)

<a id="entry-92"></a>

### 92. Closed semisimple determinant profile and a polynomial-time SL case

**Unconditional.** For a semisimple target \(\prod_i M_{n_i}(\mathbb F_{q^{e_i}})\), all algebra automorphism determinants are generated by Frobenius signs \((-1)^{(e_i-1)n_i^2}\) and permutations of repeated blocks with sign \((-1)^{n_i^2e_i}\) per transposition. All-mode SL for arbitrary raw isotopes of semisimple algebras is in deterministic polynomial time over fixed \(F\).

Inner conjugations have determinant one by left–right cancellation. On the \(n_i^2\) entries of a matrix factor, the field Frobenius acts on a normal basis by an \(e_i\)-cycle. A permutation interchanging two equal matrix blocks permutes their \(n_i^2e_i\) coordinates in pairs, giving its displayed determinant. These maps generate all automorphisms modulo inner conjugation by the splitting of the simple algebra. Match simple types, compute one reference algebra isomorphism, then get its exact determinant coset. The two unit groups in [Entry 83](#entry-83) have the common exponent gcd of the \(n_i\) and \(m\). [Entry 82](#entry-82) proves the assertion in arbitrary raw bases. [Finite-algebra decomposition](https://arxiv.org/html/1708.03495)

<a id="entry-93"></a>

### 93. Sharp matrix-amplification reflection threshold

**Unconditional.** On all associative multiplication isotopes, the conjunction of SL comparisons after fixed matrix amplifications \(M_{d_1},\ldots,M_{d_s}\) reflects the original SL comparison exactly when \(\gcd(m,d_1,\ldots,d_s)=1\).

In the amplified algebra the unit and inner determinant groups become their \(d\)-th power subgroups, since the natural residue multiplicities are multiplied by \(d\). The entire algebra automorphism determinant group becomes \(D^{d^2}I^d\), where \(D\) is the old full automorphism image and \(I\) the inner image. Indeed align \(d\)-by-\(d\) matrix units as in [Entry 87](#entry-87) and restrict entrywise. An original relative determinant triple is raised to \(d^2\) in the amplified comparison. For every prime \(\ell\mid m\), a \(d_j\) not divisible by \(\ell\) preserves the complete comparison in the \(\ell\)-primary subgroup, proving reflection under the gcd condition. For sharpness use \(\mu_A\) with \(A=M_m(F[t]/t^3)\). All three determinant images of its isotopy stabilizer and those of all its matrix amplifications are trivial. Twist a single raw mode by a determinant of prime order \(\ell\) dividing the failed gcd. The original pair has no SL transporter, while every amplified pair does. This is an unconditional obstruction in the specified construction model.

<a id="entry-94"></a>

### 94. A dimension-divisibility obstruction for arbitrary tensor ancillas

**Unconditional.** On the rigid ordinary orbit in [Entry 93](#entry-93), any schedule of tensor products with fixed ancillas loses the original orientation whenever all ancilla dimensions in a selected mode are divisible by some common prime \(\ell\mid |F^\times|\). The ancillas may be unrelated to matrix multiplication or to one another.

Use the one-mode raw twist of order \(\ell\) from [Entry 93](#entry-93). Tensoring it with the identity on an ancilla mode of dimension \(b\) raises the determinant to the \(b\)-th power. Every transformed pair is therefore already SL-equivalent, despite the original determinant obstruction. No subsequent isomorphism-invariant test on the resulting individual transformed pairs can recover it. Unlike [Entry 93](#entry-93) this one-way failure does not rely on cancellation or on any form for the ancilla tensors.

<a id="entry-95"></a>

### 95. Ordered grades suffice at radical length three

**Unconditional.** For finite associative algebras over finite fields with \(J^3=0\), the ordered associated graded algebra plus the numerical raw-frame calibrations determines the full raw SL profile.

Choose a Wedderburn–Malcev residue section and an \(S\)-bimodule complement to \(J^2\) in \(J\). The two radical actions by \(J^2\) vanish, and all products of tangent vectors are their grade-two products. This gives an algebra isomorphism to the graded table inducing the identity on all layers. Handled in ordered lifted frames, changing complements only contributes unipotent maps. The left and right regular unit images follow from [Entry 83](#entry-83), and the algebra determinant from the lifted graded table. With [Entry 82](#entry-82) this determines the full profile. This claim has no algorithmic assumption on the complexity of computing an isomorphism of the graded table. [Wedderburn–Malcev background](https://doi.org/10.1007/978-1-4419-8616-0)

<a id="entry-96"></a>

### 96. A nine-dimensional collision at the first possible radical length

**Unconditional.** Over every odd field, two commutative local algebras with \(J^4=0\) in dimension nine have the same ordered associated grades, radical flag, and annihilator, but can give opposite signed multiplication comparisons with identical calibration.

Take two branches \((x,u)\) and \((y,w)\) with cross products zero, \(u^2=w^2=y^2w=y^4=0\), and impose \(x^2=0\) in \(B_0\) or \(x^2=y^3\) in \(B_1\). The common basis is \(1,x,u,y,w,y^2,yw,xu,y^3\). The redirected value lies in the socle, so the displayed products are associative and induce identical ordered grades. In the graded tangent space the cube-zero hyperplane is \(\langle x,u,w\rangle\); its product has radical \(\langle w\rangle\) and the quotient is the hyperbolic pair on \(x,u\). The two hyperbolic axes can swap in the graded table, but in \(B_1\) the relation \(x^2=y^3\ne0\) pins the \(x\)-axis. If \(\alpha\) is its scale and \(\beta\) is the scale of \(y\) modulo the hyperplane, \(\alpha^2=\beta^3\). Filtration determinants then give \(\beta^7\) times a square, hence always a square. Scaling \(w\) realizes every square. In \(B_0\) scaling \(y\) alone yields arbitrary determinant modulo squares, and together with scaling \(w\) gives every determinant. Make the same fixed nonsquare basis conjugation at one endpoint in the two comparisons. By [Entry 82](#entry-82) their raw determinant-one answers differ, although their retained data coincide. [Entry 95](#entry-95) establishes the sharp radical-length boundary.

<a id="entry-97"></a>

### 97. Arbitrarily deep filtered agreement does not determine orientation

**Unconditional.** For each finite \(F\) with \(q>2\) and each fixed depth, there are commutative local tables agreeing to that depth, with identical full ordered grades and annihilator, whose algebra automorphism images are respectively trivial and full.

For \(m=q-1\) take \(a=6rm-1,\ c=8rm+1,\ d=10rm\). Use three orthogonal monomial branches \(x,y,z\), truncate \(y^{c+1},z^{d+1}\), and impose respectively \(x^a=y^c\) or \(x^a=z^d\). The common ordered basis is \(1,x,\ldots,x^{a-1},y,\ldots,y^c,z,\ldots,z^d\); the common annihilator is \(F y^c+F z^d\). The defining difference appears in degree at least \(c\), so it is invisible modulo \(J^c\). The tangent matrix is diagonal: independent squares make it monomial and the three distinct graded nilpotence lengths prevent permutations. For scales \(\alpha,\beta,\gamma\), the determinant is \(\alpha\beta\) by the branch length congruences. Because \(d<2a\), higher terms vanish in the powered relations. The first relation forces \(\beta=\alpha^{-1}\); the second forces \(\alpha=1\) and allows arbitrary \(\beta\). These diagonal possibilities lift. The dimension \(24rm\) makes both unit determinant images trivial. A common orientation twist gives opposite SL comparisons, with \(r\) arbitrary.

<a id="entry-98"></a>

### 98. A one-generator local algebra has a triangular-number determinant subgroup

**Unconditional.** In \(A=F[t]/(t^N)\) over \(F=\mathbb F_q\), the entire automorphism determinant group is \((F^\times)^{\gcd(q-1,\binom N2)}\). Arbitrary raw isotopes of these algebras therefore admit deterministic polynomial-time SL comparison over fixed \(F\).

An automorphism is exactly \(t\mapsto a t+O(t^2)\), \(a\ne0\); its graded scales are \(1,a,\ldots,a^{N-1}\). Every \(a\) lifts by this substitution. Unit determinants have image \((F^\times)^N\). The normalized algebra is recognized by finding a tangent generator, whose monomials must span; changing to that basis computes the reference calibrations. The residue is scalar and the monomial test is directly verifiable. [Entry 82](#entry-82) then decides the raw comparison, using both exact images and the explicit ordinary dimension classification.


<a id="entry-99"></a>

### 99. One large quadratic image absorbs the orientation of a mixed product

**Unconditional.** Over \(\mathbb F_3\), consider unital scalar-residue local algebras with \(J^3=0\), \(V=J/J^2\) of even dimension, \(W=J^2\), and possibly nonzero symmetric and skew parts of the product. If for one part the kernel of its map \(\Gamma^2(V)\to W_\varepsilon\) and the quotient \(W/W_\varepsilon\) both have logarithmic dimension, determinant-one algebra comparison, and the calibrated raw signs, reduce to one ordinary TI. Here \(\Gamma^2\) is \(\operatorname{Sym}^2\) or \(\Lambda^2\) and \(W_\varepsilon\) the corresponding image.

In the two short exact sequences involving that kernel and quotient, multiply the determinant equations. The symmetric- and exterior-square determinants are \((\det g)^{\dim V+1}\) and \((\det g)^{\dim V-1}\). After multiplying by \(\det g\) from the tangent layer, either exponent is even, so vanishes as a sign. The required total sign is the calibrated product of the two small induced signs. Attach the two full exterior algebras, linked to the original product via the induced square map and quotient inclusions, and pin their joint volume line. Their dimensions are polynomial by the logarithmic bounds. For a raw three-mode request apply [Entry 82](#entry-82) first. [Tensor-system compiler, Theorem 4.1](https://arxiv.org/html/2306.03135v2)


<a id="entry-100"></a>

### 100. A small commutator kernel gives a single ordinary query

**Unconditional.** For compact special class-two exponent-three groups, if \(K_0=\ker(\Lambda^2 X\to Z)\) has logarithmic dimension in input length, even group isomorphism reduces to one ordinary TI. There is no bound on center dimension.

If \(\dim X=n\) is odd, the automorphism \((-I_X,I_Z)\) already corrects every sign. For even \(n\), the exact sequence from \(K_0\) to \(\Lambda^2X\) to \(Z\) gives \(\det(\Lambda^2g)=\kappa\,\det(g|_{K_0})\det h=(\det g)^{n-1}\), with a computable frame ratio \(\kappa\). Hence the sign on \(X\oplus Z\) is the sign on \(K_0\) times \(\kappa\). Encode the exterior-square map, its kernel inclusion and bracket, and the volume of \(K_0\) through its full exterior algebra. Its dimension is polynomial by the bound. The required determinant is thus a single typed ordinary comparison. This differs from bounding the size of the center. [Baer correspondence](https://www.ams.org/journals/tran/1938-044-03/S0002-9947-1938-1501972-1/) · [Tensor-system compiler](https://arxiv.org/html/2306.03135v2)

<a id="entry-101"></a>

### 101. A low-corank scalar probe and a logarithmic center

**Unconditional.** For the same groups, \(\dim Z=O(\log L)\) and the existence of a scalar bracket form of corank \(O(\log L)\) suffice for a deterministic ordinary many-one reduction.

Enumerate all central covectors in time polynomial in coefficient length \(L\). Fix one suitable source covector and branch over its possible images in the target. In each branch the transporter of the induced alternating form acts symplectically on the quotient by its radical \(R\). After a known frame change, the ambient determinant is \(\det(g|_R)\). Both \(R\) and \(Z\) have logarithmic dimension, so their linked full exterior algebras give the exact volume test. The ordinary TI OR combines the polynomially many branches. The argument works when the center substantially exceeds the square-root-logarithmic enumeration bound for entire central matrices. [Tensor-system compiler](https://arxiv.org/html/2306.03135v2)

<a id="entry-102"></a>

### 102. Several high-corank forms can collectively certify the sign

**Unconditional.** Over \(\mathbb F_3\), with logarithmic center, an even fixed number \(s\) of scalar probes can replace the low-corank hypothesis. Require only that the sum of their radicals \(\Sigma:\bigoplus_i R_i\to X\) have logarithmic kernel and cokernel.

Under each marked probe, \(\det g=\kappa_i\det g_{R_i}\) by its symplectic quotient. Multiply these equations: the sign raised to the even power \(s\) is one. Apply the determinant identity for the exact sequence of \(\Sigma\), and get \(\det g\det h\) as a calibrated product of determinants on \(\ker\Sigma,\operatorname{coker}\Sigma,Z\). Link these small spaces and their volume lines to the same maps in each target-probe branch, then use ordinary OR. This condition allows arbitrarily large individual radicals: for \(Z=\mathbb F_3^2\), take four independent equally large symplectic blocks valued on the four different lines in \(Z\). Every nonzero scalar form misses one block, while those four radicals form a direct sum equal to \(X\). [Tensor-system compiler](https://arxiv.org/html/2306.03135v2)

<a id="entry-103"></a>

### 103. Any logarithmic center permits an ordinary decision-oracle algorithm

**Unconditional.** Without any probe hypothesis, even isomorphism of compact special exponent-three groups with \(\dim Z=O(\log L)\) has a deterministic polynomial-time Turing reduction to ordinary TI.

Compute the center-fixed determinant subgroup by the adjoint algebra, as in the preceding atlas. On a fixed candidate center map \(h\), deterministic simultaneous isometry of the scalar forms finds \(g\) if it exists. When the fixed-center subgroup is trivial, its sign is independent of the choice of \(g\). Use ordinary TI with central vectors pinned to search for one realizable \(h\), trying all \(3^{\dim Z}\) images for each of the ordered basis vectors. The same pinning on the target self-instance yields one center-action generator for each stabilizer-chain coset. Compute the sign of a lift of each by simultaneous isometry. Their signs together with the fixed-center subgroup give the exact parity profile. If the fixed-center subgroup is nontrivial, every ordinary transporter is corrected instead. This is adaptive, in contrast to [Entry 101](#entry-101) and [Entry 102](#entry-102). [Ivanyos and Qiao, Theorems 7 and 18](https://arxiv.org/html/1708.03495) · [Fixed-arity pinning](https://arxiv.org/html/2306.03135v2)

<a id="entry-104"></a>

### 104. The extraspecial one-dimensional center has an exact orientation threshold

**Unconditional.** For a compact exponent-three extraspecial group with \(\dim X=2r\), the group automorphism determinant image on \(X\oplus Z\) is \(\{\alpha^{r+1}:\alpha\in\mathbb F_3^\times\}\). It is full exactly when \(r\) is even. When \(r\) is odd, a normalized sign is forced and computed from the endpoints without an isomorphism oracle.

Here the bimap is a nonsingular alternating scalar form. The output map scales by a similitude multiplier \(\alpha\in\mathbb F_3^\times\) and the input determinant is \(\alpha^r\). Every multiplier occurs by rescaling one vector of each symplectic basis pair. Comparing two input frames adds the computed symplectic-basis determinant ratio; all groups with the same \(2r\) are ordinarily isomorphic. This contrasts the larger group classes with an extraspecial quotient in the preceding atlas, where a nontrivial center kernel remains. [Classical-form isometry algorithms](https://arxiv.org/html/1708.03495)

<a id="entry-105"></a>

### 105. Exact determinants for the free symmetric and alternating cube-zero tables

**Unconditional.** For \(F1\oplus V\oplus\operatorname{Sym}^2V\) or \(F1\oplus V\oplus\Lambda^2V\), with the canonical quadratic product on \(V\) and all third radical products zero, the full algebra automorphism determinant image is \((F^\times)^{n+2}\) or \((F^\times)^n\), respectively, where \(n=\dim V\). Ordinary dimensions and this subgroup give a polynomial-time calibrated SL test on these recognizable tables.

Every tangent automorphism \(g\) induces its canonical action on all quadratic outputs, since the products span. Conversely any \(g\) extends, and shears are unipotent. The quadratic determinants are \((\det g)^{n+1}\) or \((\det g)^{n-1}\) by multiplying the diagonal pair products in a triangular frame over a splitting field. Combined with the tangent determinant these give the displayed powers. Recognize a candidate by computing its tangent and square layers and checking that its product induces the canonical quotient map with zero kernel on the corresponding quadratic space. The vanishing of triple radical products gives the actual table isomorphism. Apply [Entry 82](#entry-82) to obtain the raw signs, including for nonternary \(F\). For alternating products with \(n=0\) separately take the one-dimensional base algebra.

<a id="entry-106"></a>

### 106. Product algebra orientation includes a permutation sign

**Unconditional.** For products with specified central indecomposable factors, a relative algebra-isomorphism determinant is the product of the local factor determinants times the sign of permuting all the ordered factor blocks. A swap of two isomorphic factors of dimension \(d\) contributes \((-1)^d\). In particular, a repeated odd-dimensional factor supplies an actual odd full-algebra automorphism, whatever its local orientation group is.

Algebra isomorphisms necessarily preserve the primitive central idempotents and hence permute exactly the indecomposable factors. Conversely component isomorphisms and the factor permutation assemble directly. A block swap on vector spaces has determinant \((-1)^{d^2}\); general permutations factor into block swaps with the same multinomial parity rule. To realize the swap correction use a factor isomorphism and its inverse so the two local determinants cancel. Thus in the ternary case a product can lose orientation even though every component is orientation-rigid. For products of the one-generator algebras in [Entry 98](#entry-98), matching the lengths and using these explicit generators gives deterministic polynomial-time computation of the full determinant profile in the displayed frames.

<a id="entry-107"></a>

### 107. Square-zero algebras preserve parity of selected relational colors

**Unconditional.** For finite colored relational structures of bounded arity, the relative permutation sign on any specified union of color classes is the exact algebra-isomorphism determinant image of an explicit square-zero-radical associative algebra over \(\mathbb F_3\). In particular, the even and ordinary comparisons for the original colored graph or relational model map exactly to the determinant-one and ordinary comparisons on the produced tables.

Give each entity vertex a simple matrix factor \(M_{n_i}(\mathbb F_3)\). Allocate different sizes to different colors, odd exactly for selected colors. Introduce a distinct vertex for every relation tuple, with different even factor sizes by relation type, separate from all entity colors. For each tuple–entity pair encode the incidence positions by the sum of distinct powers of two, doubled to make this multiplicity even. Put that many copies of the natural \(ij\) bimodule in the ordered corner from the tuple factor to the entity factor. Set \(J^2=0\). Factor permutations preserving types and multiplicities are exactly the original relational isomorphisms with the induced tuple permutations. Every such permutation lifts by copies of the identity in common matrix and multiplicity frames. All radical block dimensions are even. All detached and inner determinant corrections are trivial by [Entry 84](#entry-84) and [Entry 85](#entry-85): radical tensor module exponents \(n_in_j\) are even, and the extra left and right regular multiplicities are even. Radical-unit alignments are unipotent. Thus only the swaps of odd-size semisimple blocks contribute a sign, exactly the required entity parity. The bounded arity and linearly sized color numbers keep the table polynomial. If a tensor comparison is required, use normalized multiplication and [Entry 82](#entry-82).

<a id="entry-108"></a>

### 108. Split symmetric spaces with a named common maximal isotropic subspace

**Equivalent to \(H(F)\)** for odd fixed \(F\). In marked symmetric spaces with a named split nonsingular scalar slice, also require all comparisons to preserve a given half-dimensional subspace \(L\) isotropic for every slice. The ordinary comparison is TI-complete; determinant one on the forms space reduces to ordinary comparison exactly when \(H(F)\) holds.

Use the earlier symmetric trace-edge carrier, with all edge multiplicities even. Its field \(E\) has even degree, so choose \(i\in E\) with \(i^2=-1\). In each pair of \(E\)-coordinates the line \(\{(v,iv):v\in E\}\) is isotropic for the \(E\)-dot product and both trace forms. Their direct sum, together with the complete evaluation dual \(M^*\), gives the required common half-dimensional isotropic \(L\). Canonical lifts in the character construction preserve \(L\), and imposing its preservation leaves the reflection proof unchanged. For the reverse reduction add the inclusion \(L\to X\) as a typed linear constraint; the ordinary and weighted compilers apply. Every ambient isometry of a fixed nonsingular form preserving \(L\) automatically has determinant one in common compatible frames because its map on \(X/L\) is the inverse dual of its map on \(L\). Moreover **every** nonsingular slice of the carrier is split: in the \(M\oplus M^*\) block it contains the half-dimensional isotropic \(M^*\), and the even trace-edge sums are split whenever nonsingular. [Ordinary tensor-system compiler](https://arxiv.org/html/2306.03135v2)


<a id="entry-109"></a>

### 109. All scalar slices can have split nonsingular quotients

**Equivalent to \(H(F)\)** for odd fixed \(F\). Consider marked symmetric matrix spaces with an ordered pair of complementary common maximal-dimensional isotropic spaces \(U,V\), a named linear identification \(U\simeq V\), and a named nonsingular slice. Require transporters to preserve the two spaces and their identification. The determinant-one problem on the forms space has strictly larger degree than ordinary comparison exactly under failure of \(H(F)\). This carrier has even scalar-slice ranks, with split nonsingular quotient for every slice, even when singular.

Double any marked symmetric carrier \(B:X\times X\to Z\) from [Entry 108](#entry-108) to \(U\oplus V=X\oplus X\) and use the block product \(B(u,v')+B(u',v)\). The ordered decomposition and named identification force the same \(g\) on its two factors. Then the mixed block recovers \(B\) and the identical output map \(h\), including its determinant, and every old transporter lifts diagonally. A scalar slice of the doubled form has matrix \(\begin{psmallmatrix}0&M\\M^{\mathsf T}&0\end{psmallmatrix}\); after quotienting its two kernels, its two summands are a perfect dual pair, yielding a split form. In a general input of the stated marked class, keep the two inclusions and identification as typed linear constraints for the reverse ordinary and oriented compilers. The named identification is part of the model.

<a id="entry-110"></a>

### 110. Maximal abelian polarizations in compact three-groups

**Equivalent to \(H\).** For compact special exponent-three groups, restrict to a nonsingular scalar commutator form and mark an abelian subgroup containing the center whose quotient modulo the center has half the dimension of the abelianized group. Ordinary comparison with this mark is TI-complete. Even comparison reduces to ordinary comparison precisely in the equality branch. The nonsingular form may either be marked or supplied only as a witness.

In the alternating compiler from the preceding atlas, let \(L\) be the sum of all evaluation duals and a fixed Lagrangian from each auxiliary symplectic block. The bracket vanishes on \(L\times L\) and \(\dim L=\tfrac12\dim X\). A nonsingular slice bounds every common isotropic subspace by this number. Thus its full preimage in the group is abelian of maximal possible size and contains the center. Canonical character lifts preserve it. Necessity still uses the exact total determinant on \(X\oplus Z\). For the reverse reduction enforce the subgroup by including \(L\hookrightarrow X\) in the typed system, and the scalar form by the corresponding linear map if it is marked. This proves that preserving the whole maximal abelian polarization does not remove the separation in the inequality branch. [Baer correspondence](https://www.ams.org/journals/tran/1938-044-03/S0002-9947-1938-1501972-1/) · [Tensor-system compiler](https://arxiv.org/html/2306.03135v2)

<a id="entry-111"></a>

### 111. Exponent-nine groups with any fixed positive rank of the power map

**Equivalent to \(H\).** For each fixed \(t\ge1\), consider compact class-two groups of exponent nine whose center \(Z\) is elementary abelian and equal to the derived group. Their cube map \(\pi:X=G/Z\to Z\) is required to have rank \(t\). Ordinary isomorphism is TI-complete. Even versus ordinary isomorphism in the coordinate order collapses precisely if \(H\) holds.

The bracket \(\beta\) and \(\pi\) classify these compact groups under simultaneous \(g,h\). Indeed \([G,G]\) has exponent three, so cubing on \(X\) is linear. A presentation has central order-three generators, commutators prescribed by \(\beta\), and generator cubes by \(\pi\). The coordinate multiplication is a central bilinear commutator correction plus the coordinate carry \(\lfloor(a_i+b_i)/3\rfloor\pi(e_i)\). Both satisfy the two-cocycle equation, yielding the claimed groups, and a compatible pair of maps lifts by choosing images of the generators. A group isomorphism permutes the odd-sized central fibers over \(g\), and acts on each fiber by \(h\) followed by a translation. The fiber translations are even. The permutation sign is thus \(\det g\,\det h\), despite the carries.

For the lower direction attach to a compact special exponent-three bracket \(t\) fixed symplectic blocks \(X_i\) with one-dimensional outputs \(Z_i\), odd superincreasing half-dimensions \(r_i\), and a nonzero cube functional into each \(Z_i\). The subspace \(Z_*=\operatorname{im}\pi\) is now intrinsic and \(X_*\) is the common radical of the bracket modulo \(Z_*\). The rank subset sums of the bracket on \(X_*\) identify the individual blocks and their output lines. The determinant on each pair is \(\alpha_i^{r_i+1}=1\) over \(\mathbb F_3\). Consequently all added blocks have even total action and the induced quotient transporter has exactly the original sign. Conversely original transporters lift by identity on the blocks. For the reverse direction put \(\beta,\pi\) into the typed compiler with duplicate input roles linked by the identity, and assign determinant weights \(1,1\) to \(X,Z\). Ordinary and oriented comparisons then map to the corresponding tensor comparisons. This argument changes the exponent and uses the nonzero power map as a structural invariant. [Class-two group and tensor reductions](https://doi.org/10.1137/21M1441110)

<a id="entry-112"></a>

### 112. Small power-map defects make the exponent-nine sign easy to compile

**Unconditional.** In the compact exponent-nine setting of [Entry 111](#entry-111), if \(\dim\ker\pi+\dim\operatorname{coker}\pi=O(\log L)\), even isomorphism reduces to one ordinary TI. The rank need not be bounded. When \(\pi\) is an isomorphism, the determinant sign is fixed by a numerical frame calibration on every ordinary transporter.

Use the two exact sequences for \(\pi\). Then \(\det g\,\det h\) is the calibrated product of the determinant on \(\ker\pi\) and on \(\operatorname{coker}\pi\), since the factor acting on \(\operatorname{im}\pi\) occurs twice. Its square is one over \(\mathbb F_3\). Keep \(\beta,\pi\) and their kernel and quotient links in one typed diagram. A top-volume pin on the small spaces provides the remaining sign, and the exact frame ratio comes from ordered lifts along the sequences. The two exterior algebras have polynomial dimension under the stated bound. This sufficient regime is independent of commutator kernel and center dimension. [Tensor-system compiler](https://arxiv.org/html/2306.03135v2)

<a id="entry-113"></a>

### 113. Detachable center for general elementary-center exponent-nine groups

**Unconditional structural reduction.** For compact class-two groups of exponent at most nine with elementary abelian center, set \(D=[G,G]+\operatorname{im}\pi\le Z\) in additive central coordinates. A positive-dimensional complement of \(D\) in \(Z\) makes even isomorphism coincide with ordinary isomorphism whenever the groups are isomorphic.

The commutators and powers land in the characteristic subgroup \(D\). Choose lifts of a basis of \(X=G/Z\) and a central complement \(C\) to \(D\). The class-two presentation or the carry formula of [Entry 111](#entry-111) gives a direct product of the group on \(X\oplus D\) and \(C\). Ordinary isomorphism is determined by the compatible bracket-and-power pair on the first summand and the dimension of \(C\). Negating any coordinate of a nonzero \(C\) is an automorphism, and it is odd because the other factor and all other coordinate sets have odd size. When \(C=0\), the exact sign criterion is instead that of the remaining simultaneous bracket and power maps. The broader elementary-center class still has the collapse equivalence by inclusion of [Entry 111](#entry-111) and the reverse typed compiler. This identifies exactly when the free central factor itself supplies a sign correction.

<a id="entry-114"></a>

### 114. One-dimensional radical square for commutative local algebras

**Unconditional.** For a commutative scalar-residue local \(F\)-algebra of odd fixed \(F\) with \(J^3=0\), \(\dim J^2=1\), and \(n=\dim J/J^2\), the algebra determinant subgroup in the nonsingular case is
\[
 \langle-1,(F^\times)^{n+2}\rangle\ \text{for odd }n,\qquad
 \langle-1,(F^\times)^{n/2+1}\rangle\ \text{for even }n.
\]
If the scalar tangent form is singular, the subgroup is full. All raw SL comparisons on this class are deterministic polynomial time, with no dimension bound on the tangent space.

The bracket is a symmetric scalar form. In the singular case its common radical is a detachable annihilator, so [Entry 85](#entry-85) applies. Otherwise a transporter on the tangent space is a similitude with multiplier \(\alpha\), and the output line has determinant \(\alpha\). If \(n\) is odd, \(\alpha\) must be a square, because multiplying the form by \(\alpha\) changes its discriminant by \(\alpha^n\). Conversely every square \(\lambda^2\) is attained by a scalar similitude with total determinant \(\lambda^{n+2}\). If \(n\) is even, every multiplier is attained by classification of nonsingular finite-field symmetric forms of equal dimension and discriminant, and the total determinant is \(\pm\alpha^{n/2+1}\). A reflection supplies the minus sign in both cases. For relative comparison try the constant number of output scalars and construct one tangent congruence for each allowable multiplier. Apply [Entry 82](#entry-82) for the raw calibration. For \(\mathbb F_3\) this contrasts with [Entry 104](#entry-104), where a nonsingular alternating scalar form can force the sign. [Finite-field form algorithms](https://arxiv.org/html/1708.03495)

<a id="entry-115"></a>

### 115. Cubes recognize the scalar residue without radical decomposition

**Unconditional.** A normalized unital associative table over \(\mathbb F_3\) can be checked for scalar residue and \(J^3=0\) using basis cubes and elementary linear algebra, without a semisimple-quotient algorithm.

On such a table every \(x=a1+j\) has \(x^3=a1\) since the scalar commutes with \(j\) and \(j^3=0\). Compute the cubes of basis vectors and reject if any is nonscalar. Their scalar entries define a candidate linear map \(\rho\) to \(\mathbb F_3\). Test multiplicativity on all basis products, the unit condition, and whether \((\ker\rho)^3=0\). Success proves that \(\ker\rho\) is a nilpotent ideal with scalar field quotient, so it is exactly the Jacobson radical. Necessity is the cube calculation. Taking [Entry 82](#entry-82) first gives recognition directly on raw bimap input. This supplies a proof of polynomial testability of the promises in [Entry 99](#entry-99), [Entry 114](#entry-114) and [Entry 117](#entry-117) using only table operations.

<a id="entry-116"></a>

### 116. Twisted residue bimodule types give a computable small-square regime

**Unconditional.** For raw multiplication isotopes of local ternary algebras with \(J^3=0\) and residue field of degree \(e\), write \(f_i\) for the dimensions over that field of the individual Frobenius bimodule types in \(J^2\). If \(e\sum_i f_i^2=O(\log L)\), the exact attainable signs in any one specified physical mode are computable in deterministic polynomial time.

Use a residue section and split the radical layers as bimodules. For each of the \(e\) Frobenius choices on the residue field, enumerate the maps on \(J^2\) separately on each type, at cost at most \(3^{e\sum_i f_i^2}\) times a polynomial. Fixing that map reduces the tangent equations to a constrained congruence: solve the paired linear intertwining equations for the left and right field actions and for the product and its transpose, then solve the resulting symmetric-norm condition in the adjoint algebra. The radical of that algebra changes no determinants. Its semisimple exchanged, orthogonal, symplectic and unitary factors give the exact determinant subgroup, as in the earlier adjoint correction proof. An explicit quotient solution lifts by a self-adjoint inverse square root of a nilpotent perturbation of one. The coordinate change and unit effects are from [Entry 82](#entry-82) and [Entry 83](#entry-83). This result concerns different **left and right actions in a local table over \(\mathbb F_3\)**. [Ivanyos and Qiao, adjoint decomposition and lifting](https://arxiv.org/html/1708.03495) · [Lenstra, finite-field isomorphisms](https://pub.math.leidenuniv.nl/~lenstrahw/PUBLICATIONS/1991b/art.pdf)

<a id="entry-117"></a>

### 117. A small skew specialization detects orientation in mixed cubic radical layers

**Unconditional.** For raw ternary scalar-residue cube-zero multiplication tables, no parity restriction on \(\dim J/J^2\) is necessary if \(W=J^2\) has logarithmic dimension and the skew part of the radical product has a scalar specialization of logarithmic corank. The relevant calibrated determinant condition reduces to one ordinary TI.

For every qualifying covector \(\ell\in W^*\), choose an adapted frame with a kernel basis and lifts of a symplectic quotient basis. The tangent determinant is then the determinant on the kernel times its endpoint frame ratio. The qualifying covectors form an intrinsic polynomial-size set. Pack their kernels and exterior algebras as modules over its coordinate algebra, whose idempotents map to the actual covectors. Thus an isomorphism permutes exactly the appropriate kernels. Form a common volume line linked to their top lines with the chosen frame ratios. It forces the tangent sign on the same map that preserves the full, possibly nonsymmetric product. Link also the top volume of \(W\), and pin the product sign. The dimension bound is \(3^{\dim W}\,2^{\max_\ell \dim\ker(\ell\cdot(m-m^{\mathrm{op}}))}\) up to polynomial factors. Unlike [Entry 101](#entry-101) this compiles the intrinsic probe family together and retains both symmetric and skew multiplication channels. [Tensor-system compiler](https://arxiv.org/html/2306.03135v2)

<a id="entry-118"></a>

### 118. A one-dimensional twisted square need not bound residue degree

**Unconditional.** Still in [Entry 116](#entry-116), the one-mode sign profile is computable in deterministic polynomial time without a bound on the residue degree if \(J^2\) is one dimensional over the residue field and the first argument of every nonzero radical product belongs to one Frobenius bimodule type \(\tau\) of odd order. This includes a central residue section with one-dimensional square.

For each residue field isomorphism \(\sigma\), the square map is given by a nonzero scalar. In the single active type, rescaling the tangent map by \(c\) multiplies the square map by \(c\,\tau(c)\). When \(\tau\) has odd order this runs through exactly the subgroup of squares: if \(\tau\) is the \(3^i\)-Frobenius, then \(\gcd(1+3^i,3^e-1)=2\). Thus only two square-class representatives need constrained tangent congruence rather than enumerating all residue scalars. If the tangent dimension over the residue field is even, these rescalings preserve its \(\mathbb F_3\) determinant and preserve the determinant on the one-dimensional square because the scalar is a square. If the tangent dimension is odd, the total residue dimension of the algebra is odd and the unit action in [Entry 83](#entry-83) supplies both signs in any requested single mode. Taking the union of the exact representative profiles over the \(e\) possibilities for \(\sigma\) gives the answer. This removes a field-degree bound by a twisted multiplication constraint internal to the algebra. [Fixed-characteristic form algorithms](https://arxiv.org/html/1708.03495)
