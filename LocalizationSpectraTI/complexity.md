# Exact congruence-image counts for signed tensor transporters

The directional localization construction tests whether an arithmetic transporter exists. The following refinement counts finite reductions of its global witnesses exactly. The normalization depends on one explicit linear map over \(\mathbf F_3\). It applies to shared transporters of linked systems, and also gives an exact coordinate-observed count on one raw free arithmetic tensor pair.

## Statement

Put \(R_0=\mathbb Z\) and \(R_1=\mathbb Z[1/2]\). Start with a common-format pair of explicitly linked systems of linear and bilinear maps over \(K=\mathbf F_3\). A role indexed by \(i\) has dimension \(n_i\ge 1\) and a single map \(G_i\) shared by all its occurrences. Every arrow has one or two input roles and one output role. Specify independently, in each role, either no determinant condition or one prescribed sign. For each prescribed sign also specify whether to keep or release the condition after localization.

There is one polynomial-size ordinary free three-tensor pair \(F\) over \(\mathbb Z\), the same coefficients used over \(R_1\), with explicitly designated coordinate blocks in its three transporter matrices. For \(k\ge1\), let \(N_j(k)\) count the distinct reductions modulo \(3^k\) of the **designated blocks of actual global \(R_j\)-transporters** of \(F\). Let \(a_j\) be the exact number of source transporters satisfying the indicated signs, with every prescribed sign in force for \(j=0\) and only the keep signs in force for \(j=1\). There are explicitly computable integers \(d_j,\rho_j\) such that
\[
 \begin{aligned}
 N_0(k)&=4\cdot 3^{(k-1)d_0+\rho_0}\,a_0,\\
 N_1(k)&=4\cdot 3^{(k-1)(d_1+2)+\rho_1}\,a_1 .
 \end{aligned}
\]
Here \(d_0=\sum_i(n_i^2-1)\), \(d_1=\sum_i n_i^2\), and \(\rho_j\) is a rank over \(K\) specified below. The output tensors do not depend on \(k\). A proposed tuple of observed residues can be tested for global liftability in deterministic time polynomial in the input and residue encoding lengths. This test does not have to write an integral or localized lift of polynomial height.

For the raw three-mode source, pin every role with release to obtain the exact cardinality at any prescribed determinant tuple from \(N_0(k)\), and the total ordinary transporter cardinality from \(N_1(k)\). In particular this realizes exact signed cardinalities and their ratio to the ordinary count. The counted object is the reduction image of a global arithmetic solution set through a specified coordinate observation. Counting every transporter over the finite coefficient ring \(\mathbb Z/3^k\mathbb Z\) is a different problem.

## An ordinary congruence diagram

For every arrow let \(P_q\) be its input role or the tensor product of its two input roles, and \(Z_q\) its output role. The original source and target matrices are \(T_q,U_q:P_q\to Z_q\). The associated residue equation is
\[
 G_{Z_q}T_q=U_q G_{P_q},
\]
where \(G_{P_q}\) is one role map or the tensor product of two role maps. Apply target coordinate reflections at the data place to change every pinned sign into \(+1\), using the same target role change across all occurrences. This is a bijection of the relevant ternary transporters. In the formulas below \(U_q\) denotes the resulting target arrow. All coefficient lifts are canonical integral lifts.

Use named input product spaces and named direct sums, with the tensor-product map and inclusions retained as typed maps. Their transporters are forced by the original role maps. Add the domain \(P_q\oplus Z_q\) of a graph-cover arrow to another copy of that direct sum, using the respective source and target maps
\[
 (p,z)\longmapsto (p,\widetilde T_q p+3z)
 \quad\hbox{and}\quad
 (p,z)\longmapsto (p,\widetilde U_q p+3z).
\]
On the receiving space the transporter has diagonal blocks \(G_{P_q},G_{Z_q}\). Its unique possible transporter on the graph-cover domain is
\[
 (p,z)\longmapsto
 \left(G_{P_q}p,\ G_{Z_q}z+
 \frac{G_{Z_q}\widetilde T_q-\widetilde U_q G_{P_q}}{3}p\right).
 \tag{1}
\]
It exists exactly if the numerator vanishes modulo three, since \(3\) is a nonzero element in both rings and the arrow is injective with a triangular inverse over the fraction field. It is invertible whenever the two diagonal maps are invertible.

For each pinned role add the previously used identity-pin graph with denominator \(5\) for release and \(11\) for keep. A separate copy of the role is pinned pointwise by coordinate maps from a scalar line whose multiplication fixes its basis vector. The pin graph forces \(G_i\equiv I\) at the chosen pin prime. Its transporter is ascertainable by the analogue of (1) and is unique once \(G_i\) is known. Both pin denominators are units modulo every \(3^k\), so these graph-cover maps carry no extra last-digit data in the count. Unpinned roles have no such arrow. [Original congruence carrier and fixed rings](prior/transfer.md)

## Which base-role matrices occur modulo higher powers of three

Over \(R_0\) the only units are signs. A pin forces the integral determinant to be \(+1\), and an unpinned role may have either sign. Once the reduction modulo three is prescribed, its integral determinant sign cannot vary with higher lifts.

Over \(R_1\), write a unit as \(\pm2^m\), \(m\in\mathbb Z\). The units congruent to one modulo five are the powers of \(-4\). The units congruent to one modulo eleven are the powers of \(-32\), since \(2\) has order ten modulo eleven and \(2^5=-1\) there. For every \(s\ge1\) these groups have the following images:
\[
 \langle-4\rangle\bmod 3^s=(\mathbb Z/3^s\mathbb Z)^\times,\qquad
 \langle-32\rangle\bmod 3^s=\{u:u\equiv 1\bmod3\}.
 \tag{2}
\]
Indeed \(-4\) reduces to \(-1\) modulo three, and \(16=(-4)^2\) satisfies \(v_3(16-1)=1\). Also \(v_3(-32-1)=1\). Binomial expansion gives \(v_3((1+a)^3-1)=v_3(a)+1\) when \(v_3(a)\ge1\). Thus each stated principal-unit generator has order \(3^{s-1}\) modulo \(3^s\), the full order of the principal-unit group. Unpinned localized units also map onto the full unit group.

These unit-image conditions are sufficient for liftability of any given \(G_i\bmod3^s\) with the compatible determinant. Choose one permitted global unit realizing the specified residue determinant and divide the first row by it, leaving a determinant-one matrix modulo \(3^s\). Such a matrix is a product of elementary matrices over the local principal ring \(\mathbb Z/3^s\mathbb Z\). To see this, in each column of an invertible matrix some pivot is a unit; elementary row operations reduce to a diagonal, and a determinant-one diagonal is a product of two-coordinate unit inverse pairs, each a product of elementary matrices. Lift each coefficient by CRT, reducing to zero at the pin prime when there is one. Undo the chosen determinant scaling by the corresponding diagonal global unit. This yields a global lift with the required pin condition. The rank-one case is immediate since its special-linear group is trivial. For \(R_0\) the same procedure uses the required sign \(\pm1\). The roles lift independently, and the data congruences require only the given reductions modulo three. Formula (1) gives all remaining maps.

Fix a source transporter \(g=(g_i)_i\) counted by \(a_j\). Its base-role lifts to level \(k\) number exactly \(3^{(k-1)d_j}\). At each single step the kernel consists of left perturbations \(I+3^\ell X_i\), with \(X_i\in M_{n_i}(K)\), since each fixed residue lift differs from any other by a unique such perturbation. Under the integral screen the determinant-one condition on the perturbation is \(\operatorname{tr}X_i=0\) by expansion modulo \(3^{\ell+1}\). The same trace-zero condition holds for prescribed determinant \(-1\). In the localized case (2) makes every last digit of the determinant free. This proves the claimed values of \(d_0,d_1\).

## A single derivative gives the exact extra fiber size

Write \(E_0=\bigoplus_i\mathfrak{sl}_{n_i}(K)\) and \(E_1=\bigoplus_i M_{n_i}(K)\). For an arrow with input-role list \(i_1,\ldots,i_t\), \(t=1\) or \(2\), set
\[
 X_{P_q}=\sum_{\nu=1}^{t}
    I\otimes\cdots\otimes X_{i_\nu}\otimes\cdots\otimes I .
\]
Repeated occurrences contribute separately to the sum. Define the simultaneous tangent map
\[
 \mathscr L_j:E_j\longrightarrow\bigoplus_q \operatorname{Hom}_K(P_q,Z_q),
 \qquad
 (X_i)_i\longmapsto
       (X_{Z_q}U_q-U_q X_{P_q})_q,
 \qquad \rho_j=\operatorname{rank}_K\mathscr L_j .
 \tag{3}
\]
All matrices in (3) are field matrices of the original dimensions and are computable from the written target arrows. In particular there is no transporter search in computing the normalization.

For each fixed base-role lift at level \(k\), choose any permissible extension to level \(k+1\). Replacing this extension by left multiplication \(I+3^k X_i\) changes the divided blocks in (1), modulo \(3^k\), by
\[
 3^{k-1}\big(X_{Z_q}U_q-U_q X_{P_q}\big)g_{P_q}
 \quad\text{for each }q .
 \tag{4}
\]
To check the formula, first differentiate the numerator of (1) modulo \(3^{k+1}\). Its source-side contribution is \(3^kX_{Z_q}g_{Z_q}T_q\), whose residue coefficient equals \(X_{Z_q}U_q g_{P_q}\) by the data equation. The target-side contribution is \(-3^k U_q X_{P_q} g_{P_q}\). All quadratic perturbation terms vanish modulo \(3^{k+1}\), including when \(k=1\). Dividing the resulting difference by three gives (4). In each summand, right multiplication by \(g_{P_q}\) is an invertible linear change. Therefore the combined set of possible divided-block residues for the fixed base lift is one affine space of size \(3^{\rho_j}\), independent of which residual source transporter was chosen.

The graph-cover domain blocks are the only new data at this last digit. The base-role matrices themselves occur among the observed typed components, so two distinct base lifts modulo \(3^k\) cannot coincide as an observed tuple. Every permissible choice in (4) is attained by a global lift, by the unit and CRT argument. Hence the exact number of tuples of **typed** transporter matrices reduced modulo \(3^k\) is
\[
 a_j\cdot 3^{(k-1)d_j+\rho_j}.
 \tag{5}
\]
This is also a uniform-fiber statement over the original ternary transporters, even when the underlying isomorphisms are highly nonrigid.

There is a direct liftability test. Check that the proposed base-role residues are invertible and in the correct determinant classes modulo \(3^k\), and that the original data arrows hold modulo three. Check all incidences and pin-graph components that are already forced modulo \(3^k\). Construct one base extension modulo \(3^{k+1}\); in the trace-constrained case one row scaling by \(1+3^k c\) adjusts the determinant to its prescribed sign, and otherwise any extension is allowed. Use (1) to compute its reference divided-block tuple. The differences from the proposed blocks must be divisible by \(3^{k-1}\) and then their coefficient tuple must belong to the image in (4). Solve this one linear system over \(K\). These steps are deterministic polynomial time in the residue bit length. Only the existence of a full global lift is used after this check. Powers such as \((-4)^m\) realizing high-level localized units can require a full lift of large height.

## Coordinate-observed ordinary free tensors

The same counts can be read on one ordinary free arithmetic tensor pair with a specified block observation. Here are the packing factors, which also explain why the entire uncropped raw transporter is not counted.

Use the previous tagged algebra packing of the typed signature into a free bilinear algebra table over \(\mathbb Z\). Every named space occupies a master slot and its private occurrence copies. Two quotient idempotents distinguish a diagonal labeling operator and a nilpotent linking operator. For clarity, the common ideal of master and occurrence slots is cube-zero and the quotient is \(R_j^2\), so it is the largest nilpotent ideal. The two standard quotient idempotents have unique idempotent lifts: writing a lift as \(e_i+w\) yields \((I-L_i)w=w^2\) in the final output slot sum. Modulo that slot sum, \(I-L_i\) is injective and then the equation forces \(w=0\). The two idempotents are distinguished by one nonnilpotent and one nilpotent left action. Distinct integer labels of the diagonal action remain distinct in both domains, so the global comparison preserves every master and occurrence slot. All linking and bilinear maps are then imposed exactly. Each tuple of typed maps determines one blockwise algebra map, and conversely the tuple is recovered literally from the master blocks. These statements concern global maps before reduction, so equality of some labels after reduction does not introduce any new fibers. Reduction of the algebra isomorphism matrices thus has exactly the count in (5).

Wrap the algebra in the prior fixed-partition tensor with a single scalar line and the entire algebra slot in each mode. On the two mixed blocks use scalar multiplication on the algebra slot, and on the scalar-scalar block use ring multiplication. If \(\alpha,\beta,\gamma\) are the scalar maps and \(P,Q,H\) the big maps, the mixed equations give \(H=\alpha Q=\beta P\) and \(\gamma=\alpha\beta\). The full algebra equation is then exactly the equation for the linear multiplicative isomorphism \((\alpha\beta)^{-1}H\) of the tagged multiplication table. Conversely every algebra map and independent choice \(\alpha,\beta\in R_j^\times\) supplies a transporter. This factorization is still recoverable after reduction since every scalar residue is a unit. Thus the count of fixed-partition transporter reductions is (5) times \(|R_j^\times\bmod3^k|^2\). These factors are \(4\) and \(4\cdot3^{2(k-1)}\), respectively.

Erase the partitions using the identity-slice construction over domains, with the same output coefficients for \(R_0,R_1\). Its reflection obtains the original maps as blocks of the three expanded matrices, and its lift extends each original partitioned map. Repeated application to the constant number of partitions yields a fixed extraction schedule of original blocks. Declare those blocks to be the observed coordinates in the raw output pair. The image of the observation on global transporters is exactly the full partitioned transporter set just analyzed, so taking the designated blocks modulo \(3^k\) gives the two displayed formulas. Equivalently the block observations can be interpreted in bimap coordinates; any transpose or inverse needed for the convention change is computed over the corresponding finite quotient of the invertible blocks. The extra rank-marker degrees of freedom are outside the observation. [Grochow–Qiao–Stange–Sun, Theorem 3.12, block extraction and lifting](https://arxiv.org/html/2611.00735v1#S3.SS3)

## Exact normalized phase change

In the raw three-mode all-release case, after division by the stated normalization, \(N_0(k)\) gives the number \(a_v\) of ordinary transporters at precisely the original prescribed sign \(v\), and \(N_1(k)\) gives the full ordinary count \(b\). On the promise \(a_v>0\), \(b/a_v\) is exactly the order of the determinant image of the ordinary stabilizer, since the nonempty sign fibers are cosets of its determinant kernel. In particular \(b/a_v\) is one of \(1,2,4,8\). If \(a_v=0<b\), the finite observed image is empty on the integral side at every level and nonempty on the localized side at every level. Uniform sampling from either displayed finite reduction image pushes forward to uniform sampling on the corresponding ternary transporter set, by the uniform-fiber proof in (4)–(5).

Using two independent copies of the construction, one with all keep pins and one with all release pins, gives normalized integral count \(a_\alpha a_\beta\) and normalized localized count \(a_\alpha b\) for any prescribed ternary tuples \(\alpha,\beta\). This refines the earlier Boolean localization defect to exact signed witness cardinalities of the same two arithmetic observations. More generally (3) handles shared maps across many arrows rather than multiplying their counts separately. No implication about the unrestricted ordinary finite-field counting problem is drawn from this arithmetic observed-image theorem.


## Bounded checks

Direct enumeration of the base-role lifts through levels 2 and 3 confirms the divided-block counts for the \(1\times1\times1\) nonzero scalar comparison, with all release pins. Before the two wrapper scalars, target coefficient 1 gives integral counts 1 and 1 at observed levels 1 and 2, and localized counts 12 and 324. Target coefficient 2 gives integral counts 0 and 0 and the same localized counts. For the rank-one action \((x_1,x_2),y\mapsto x_1y\), the observed-level-1 typed counts are 27 and 216, including the full derivative image of size \(3^2\). These checks accompany the general written proof.
