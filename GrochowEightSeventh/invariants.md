# Exact modular moment thresholds and real orbit reconstruction

The results below are informal proofs. Generic means on a nonempty Zariski open set of the indicated representation. For an infinite field, the geometric separation assertions concern points over its algebraic closure and imply separation on points over the original field.

## Sharp dihedral moment cutoffs in characteristic two

Edidin and Katz ask in §5.2 whether generic recovery from the first three polynomial invariant tensors extends to arbitrary infinite fields. Here the tensor is the unnormalized group-sum tensor. In characteristic two these tensors have positive-dimensional fibers for every natural dihedral action. For the action on an odd number \(n\ge5\) of points, orders through four suffice and are sharp. For \(n=3\), orders through five are required and suffice. When using all polynomial invariants instead of tensor entries in characteristic two, the sharp generic cutoff for odd \(n\ge3\) is three except at \(n=5\), where it is four. [Edidin and Katz, Theorem 2.6 and §5.2](https://arxiv.org/html/2408.09599v4#S5.SS2)

Let \(D_n\) have order \(2n\), and define
\[
T_d(x)=\sum_{g\in D_n}(gx)^{\otimes d}.
\]
The normalization by \(2n\) is unavailable in characteristic two. For \(d=1,2\), each monomial specifying an entry in the permutation basis is fixed by at least one reflection. For a pair of distinct indices \(i,j\), the reflection sends an index \(l\) to \(i+j-l\) modulo \(n\). The group sum can be paired under that reflection, so \(T_1=T_2=0\). The zeroth group sum is also zero. A constant vector \(\mathbf 1\) is fixed by the group. Expanding \(T_3(x+a\mathbf 1)\) and collecting the terms by their number of ordinary slots gives \(T_3(x)\), since each lower-order tensor vanishes. Each such affine line has infinitely many points over an infinite field, while an orbit is finite. A nonempty Zariski open set containing \(x\) meets that line in a nonempty open subset. This proves the lower bound even for recovery restricted to a generic locus.

### Recovering the quadratic Fourier information at order four

For odd \(n\), work over a field containing a primitive \(n\)-th root of unity. In Fourier coordinates \(x_i\), indexed modulo \(n\), rotation multiplies \(x_i\) by \(\zeta^i\), and reflection interchanges \(x_i,x_{-i}\). Let \(\overline m\) denote the reflected monomial, and put \([m]=m+\overline m\) and \(p_i=x_i x_{-i}\). The entries of \(T_d\) give \([m]\) for each degree-\(d\) monomial of weight zero. Indeed rotation contributes the nonzero factor \(n\) at weight zero and cancels every other monomial. Reflected fixed monomials have zero trace. If \(n\ge3\), the cubic trace \(S=[x_1^2x_{-2}]\) is a nonzero polynomial, so \(T_4\) gives the zero-frequency coordinate from \(x_0S/S\) on the open set where \(S\ne0\).

For odd \(n\ge7\), put \(k=(n-1)/2\). For distinct \(a,b\in\{1,\ldots,k\}\), use the cubic monomials
\[
 A=x_a x_b x_{-a-b},\qquad B=x_{-a}x_b x_{a-b}.
\]
Expanding their trace product by \([A][B]=[AB]+[A\overline B]\) gives
\[
 [A][B]=p_a C_{ab}+p_b D_{ab},\qquad
 C_{ab}=[x_b^2x_{-a-b}x_{a-b}],\quad D_{ab}=[x_a^2x_{-a-b}x_{b-a}].
\]
Both quartic traces are nonzero polynomials. For example, the unreflected monomial in \(D_{ab}\) includes \(x_a^2\), and to be fixed under reflection its other two factors would both have to be \(x_{-a}\). This would force \(b=0\). The same reasoning applies to \(C_{ab}\).

Use rows \((a,b)=(1,2),(1,3),(2,3)\). Their determinant on \(p_1,p_2,p_3\) is \(C_{12}D_{13}C_{23}+D_{12}C_{13}D_{23}\). It is nonzero for every odd \(n\ge7\). The two products involve the following triples of weight lists before reflection.
\[
\begin{array}{c|ccc}
&\text{first factor}&\text{second factor}&\text{third factor}\\
 C_{12}D_{13}C_{23}&(2,2,-3,-1)&(1,1,-4,2)&(3,3,-5,-1)\\
 D_{12}C_{13}D_{23}&(1,1,1,-3)&(3,3,-4,-2)&(2,2,-5,1)
\end{array}
\]
To check a nonzero coefficient, the table below records the triples of exponents of \(x_1,x_2,x_3\) in the eight terms of each product. A digit string \(243\) here means the triple \((2,4,3)\). Signs of individual factors are chosen independently.

| Modulus | First product | Second product |
|---|---|---|
| \(7\) | \(243,324,032,113,331,412,120,201\) | \(433,134,440,141,303,004,310,011\) |
| Odd \(n\ge9\) | \(232,313,022,103,330,411,120,201\) | \(422,123,430,131,302,003,310,011\) |

In each row the first product's unreflected term has a triple occurring exactly once across both products. For \(n\ge9\), none of the signed indices \(\pm4,\pm5\) reduce to \(1,2,3\), which makes the table uniform. This proves nonvanishing even in characteristic two. Solving this system recovers \(p_1,p_2,p_3\) rationally from the moment entries. Then use the row \((1,j)\) and divide by \(D_{1j}\) to recover each remaining \(p_j\). All divisions are by nonzero polynomials, so these steps work on a single generic locus.

For \(n=5\) write \(a=x_1,b=x_2,c=x_3,d=x_4\), \(p=ad,q=bc\), and take traces
\[
 S=a^2c+d^2b,\qquad T=ab^2+dc^2,\qquad
 U=a^3b+d^3c,\qquad V=b^3d+c^3a.
\]
Expansion gives \(ST=qU+pV\) and \(UV=pT^2+qS^2\). The second identity uses the characteristic-two squaring law. The determinant \(VS^2+UT^2\) takes the value one at \((a,b,c,d)=(1,1,0,0)\), so the two equations recover \(p,q\) generically.

### Recovering the orbit from the extracted information

For any odd \(n\), ordinary degree-one and degree-two polynomial invariants give \(x_0,p_i\) directly. The cubic invariants add the traces of weight-zero cubic monomials. Each pair \((m,\overline m)\) is determined up to exchange by its sum and product: the product is a known monomial in the \(p_i\) when \(m\) has no zero-frequency factor. For a generic candidate \(y\) with the same data, let \(t_i=y_i/x_i\) and \(a_i=x_i/x_{-i}\). The products give \(t_{-i}=t_i^{-1}\), and put \(e_{-i}=-e_i\). Each cubic triple with form \(v=e_i+e_j+e_l\) constrains \(t^v\) to either \(1\) or \(a^{-v}\). On the generic nonzero locus the \(a_i\) for \(1\le i\le k\) are independent Laurent variables. Consequently a minimal integer dependence among such forms synchronizes their choices. To see this, for \(\sum_v c_v v=0\) the chosen alternative branches imply \(a^{\sum_v c_v\epsilon_v v}=1\), with \(\epsilon_v\in\{0,1\}\). A proper nonempty subset of the terms has nonzero sum by minimality, and its Laurent equality is excluded generically.

For \(n=2k+1,\ k\ge4\), the forms \(w_j=e_1+e_j-e_{j+1}\), \(1\le j<k\), are independent. The cubic forms \(e_2+e_j-e_{j+2}=-w_1+w_j+w_{j+1}\) for \(2\le j\le k-2\) give minimal dependences and synchronize every \(w_j\). Reflecting once if necessary makes all these branches equal to \(1\), yielding \(t_i=t_1^i\) for \(1\le i\le k\). The two triples \((1,k,k)\) and \((2,k-1,k)\) then constrain \(t_1^n\) to \(1\) or their respective distinct Laurent monomials in the \(a_i\). This forces \(t_1^n=1\) generically, which is exactly the remaining rotation freedom. For \(n=7\), the four forms \(v=2e_1-e_2,\ w=e_1+e_2-e_3,\ a=e_1+2e_3,\ b=2e_2+e_3\) have the minimal dependence \(v-w-a+b=0\), as seen from rank three and its four nonzero coefficients. Synchronizing them also gives the same chain and wrap conclusion. These branch arguments use multiplicative identities and remain valid in characteristic two.

For \(n=5\) the only nonzero-frequency cubic pairs are the ones traced by \(S,T\) above. Put \(u=a^2/b,\ v=ab^2\). With \(p,q\) fixed, \((a,b)\mapsto(u,v)\) is onto over an algebraic closure and has kernel exactly the rotations, since its exponent determinant is five. The traces fix \(u,v\) up to independent inversion with the reflection factors \(p^2/q,\ pq^2\), respectively. Generically the four choices are distinct and give two dihedral orbits. The quartic trace \(U\) specifies the unordered reflection pair for \(uv\). Since the exponent form for \(uv\) is the sum of the two cubic forms, the minimal dependence synchronizes the two branches and proves quartic sufficiency. For ordinary polynomial invariants, at all odd \(n\ge3\) degree two gives only \(x_0,p_1,\ldots,p_k\), so its fibers have positive dimension. Degree three suffices at \(n=3\) by the elementary symmetric polynomials.

For the tensor cutoff at \(n=3\), the only nonzero-frequency monomials of degree at most four with nonzero trace are the two orientations of \(x_1^3\). The remaining weight-zero monomials of degree at most four on those frequencies are powers of \(p_1\), hence have trace zero. Thus through order four the data generate just the field of \(x_0,S=[x_1^3]\). At order five the trace \(p_1S\) recovers \(p_1\). The sum \(S\) and product \(p_1^3\) recover the unordered pair \(x_1^3,x_2^3\), and the known product \(p_1\) makes the remaining third roots exactly the rotations. This proves the stated sharp cutoff.

The geometric statements also give rational invariant field generation in the stated sufficient degrees. Over the Fourier splitting field the oriented monomials satisfy quadratic equations with a generically nonzero linear coefficient, and the remaining rotation ambiguity comes from an \(n\)-th root with \(n\) odd. The extensions are separable, and the generic fiber has exactly the group order, which is also the degree over the full fixed field. The resulting field equality descends along the finite separable Fourier splitting field. For example, base change of invariant polynomial spaces follows by writing the spaces as simultaneous kernels of linear differences, and the rational fixed field is the fraction field of the invariant polynomials by clearing denominators with an orbit product.

## Sharp worst-case obstruction to one-orbit real group and action recovery

Mixon and Vose ask whether one can drop the two-orbit requirement for real concrete recovery in Corollary 3.5 when the orbit span is already large enough. They separately ask whether one generic orbit identifies the unknown permutation action on that orbit. Both answers are negative in general, even for an irreducible four-dimensional action whose very first orbit spans. The two-generic-orbit bound is therefore sharp for these tasks in the worst case. [Mixon and Vose, Theorem 2.12, Example 3.7 and §4](https://arxiv.org/html/2411.17434#S3.SS2)

Use the quaternions \(\mathbb H\) as a real Hilbert space with the usual quaternion norm, and let \(Q=\{\pm1,\pm i,\pm j,\pm k\}\). Write \(L_C\) and \(R_C\) for the subgroups of orthogonal maps given by multiplication on the left and right by elements of a unit quaternion subgroup \(C\). For every \(x\ne0\) the orbit of \(x\) under \(L_Q\) is \(Qx\), and it spans \(\mathbb H\) because right multiplication by \(x\) is invertible. The group \(R_{x^{-1}Qx}\) has exactly the same orbit on the same \(x\). Under the labeling \(q\mapsto qx\), the induced regular actions are respectively the left and right translations of \(Q\). These are different permutation subgroups. For instance, a left translation by \(i\) and the only right translation with the same value at \(1\) give different values at \(j\). The two orthogonal subgroups are correspondingly distinct.

There is an obstruction even if a recovery rule may prescribe separate dense open sets of admissible seeds for every candidate group. For unit quaternions \(a,b\) and \(r>0\), let
\[
 \Gamma_a=L_{aQa^{-1}},\qquad \Delta_b=R_{b^{-1}Qb}.
\]
Both groups have orbit \(r aQb\) on the seed \(r ab\), and their permutation actions again disagree on this orbit. Suppose admissible dense open seed sets \(U_{\Gamma_a},U_{\Delta_b}\subset\mathbb H\) are specified for all the groups in these families. Fix a countable dense set of \(a\)'s on the unit sphere \(S^3\). For every such \(a\) and every open interval \(I\) with positive rational endpoints, the set
\[
 \{b\in S^3 : r ab\in U_{\Gamma_a}\text{ for some } r\in I\}
\]
is open and dense in \(S^3\). This follows by projecting the dense open preimage of \(U_{\Gamma_a}\) under the radial coordinate homeomorphism \((r,b)\mapsto rab\). The Baire theorem gives one \(b\) meeting all these countably many conditions. For this \(b\), the seeds \(r ab\) admissible for their \(\Gamma_a\) are dense in \(\mathbb H\), since for each selected \(a\) their allowed radii are dense. Thus at least one such seed also belongs to \(U_{\Delta_b}\). That orbit cannot be decoded correctly for both groups.

Both groups in the construction are isomorphic to \(Q\), so abstract recovery has a separate answer. Two generic orbits suffice for concrete recovery here because both orbits together identify the permutation action by the real two-orbit theorem and one orbit alone spans the ambient space. Every left or right quaternion action in the example is irreducible, since the span of each nonzero orbit is the full space.

## One real Gram graph recovers involution-generated groups

For every faithful finite real orthogonal group generated by involutions, a single generic Gram graph recovers the group and its permutation action. This establishes Mixon and Vose's Conjecture 2.7 on the entire involution-generated class, even when a competitor is allowed to be any finite real orthogonal group with a free orbit and need not be generated by involutions in advance. [Mixon and Vose, Theorem 2.5 and Conjecture 2.7](https://arxiv.org/html/2411.17434#S2)

Label a generic free orbit by group elements. The edge label from \(g x\) to \(g h x\) is the quadratic form \(x^{\mathsf T}h x\). Two such forms agree identically precisely when the symmetric parts of the respective operators agree. A finite collection of distinct quadratic forms is pairwise distinct upon evaluation on a suitable nonempty Zariski open set.

An involution \(h\) is symmetric and has eigenvalues in \(\{1,-1\}\). No other orthogonal operator \(u\) has symmetric part \(h\). In fact for a vector \(z\) in the \(h\)-eigenspace of sign \(\epsilon\) one would have \(\langle z,uz\rangle=\epsilon\langle z,z\rangle\), forcing \(uz=\epsilon z\) by equality in Cauchy–Schwarz. Thus every involution yields a color for which each vertex has exactly one neighbor. Conversely, any off-diagonal color admitting exactly one neighbor comes from an involution, since \(h\) and \(h^{-1}\) always give the same quadratic value. This converse even holds for an arbitrary free orbit.

For each color having one neighbor, form the permutation taking a vertex to that neighbor. In the displayed labeling this is right translation by the corresponding involution. If the involutions generate \(G\), these permutations generate a regular group, from which one reads the isomorphism class of \(G\). The centralizer of the right regular group on the vertices is the left regular group, recovering the actual orbit action. Any competing free orbit with the same colors yields the same single-neighbor permutations, so its right regular group contains the reconstructed transitive subgroup. The equal orders force equality. This also gives a finite algorithm by closing the labeled permutations under multiplication.

## One-orbit recovery for actions with irreducible constituents of dimension at most two

Let a finite real orthogonal group act faithfully, with all real irreducible constituents of dimension at most two in the given representation. A single generic Gram graph recovers its abstract group and its permutation action, even against arbitrary competing real orthogonal representations on their own generic loci. In particular this proves the abelian case of the real one-orbit conjecture. The graph data and the construction determine the concrete restriction to the span of the orbit. [Mixon and Vose, Conjecture 2.7 and Example 2.8](https://arxiv.org/html/2411.17434#S2)

A Gram graph determines its point configuration up to isometry of the linear span. For the realized orbit \(X\), form the self-adjoint operator \(S=\sum_{y\in X}yy^{\mathsf T}\). It commutes with the action and is positive definite on the span. Its positive eigenspaces are invariant subspaces. The following description shows how \(S\) generically separates the active one- and two-dimensional pieces.

A one-dimensional real isotype consists of copies of one sign character, possibly trivial. The projected orbit spans one line in that isotype, contributing a single positive eigenvalue to \(S\). On a two-dimensional rotation isotype, identify the representation with copies of one complex line on which the group acts by common scalar roots of unity. The orbit projects into a single complex line and its positive covariance eigenvalue there is \(|G|/2\) times the squared norm of the projected vector. The plane projection is a regular polygon, with a unique cyclic rotation group acting transitively.

In a two-dimensional real isotype on which the image contains a reflection, the image is a dihedral group \(D_m\) with \(m\ge3\), since the constituent is irreducible. Its commuting algebra on the constituent is \(\mathbb R\). Write the projected seed in \(q\) copies of this plane as a real \(2\times q\) matrix \(M\). Averaging a rank-one operator \(u v^{\mathsf T}\) over the group gives a scalar times the identity on the plane, by the commuting algebra and preservation of trace. Applying this to each pair of columns of \(M\) shows that \(S\) on the isotype is
\[
 \frac{|G|}{2}(M^{\mathsf T}M)\otimes I_2.
\]
The positive eigenvalues of \(M^{\mathsf T}M\) are generically distinct. For a unit eigenvector \(w\) with positive eigenvalue, the corresponding invariant plane is \(w\otimes \mathbb R^2\), and the seed in it corresponds to \(Mw\), an eigenvector of \(MM^{\mathsf T}\). A projected \(D_m\)-orbit is free and nonregular except in finitely many directions in the plane. These exceptional lines consist of reflection axes and the midway directions giving evenly spaced interleaving of two cyclic polygons. Generically \(MM^{\mathsf T}\) has no positive eigenvector on any of those lines. Indeed the condition that it preserve a specified line spanned by a unit \(u\) is the polynomial equation \(\det(u,MM^{\mathsf T}u)=0\). This polynomial is nonzero, as a matrix with one column in neither the line nor its perpendicular shows. Thus the projection to each active plane is generically a nonregular free dihedral orbit.

Different isotypes of \(S\) have no off-diagonal terms, since \(S\) commutes with the group. Its positive eigenvalues also separate from one isotype to another generically. This follows by independently rescaling the seed components in the different isotypes. For algebraicity, after fixing each generic positive rank, remove the fixed powers of the zero root from the isotype characteristic polynomials, counting each two-dimensional plane eigenvalue once using the displayed matrices. A common positive root lies in the vanishing set of their resultant, and independent scaling makes that polynomial nonzero. The covariance consequently identifies every active line and plane without a representation label.

On a recovered line, its projected points specify the unique local group, either the trivial or sign group. On a plane with a regular polygon, take its full rotation group, the unique possible local group on the generic locus by the preceding local descriptions. On a plane with a nonregular polygon of \(2m\) points, take its full point-set symmetry group. This group is exactly the local \(D_m\). Indeed as a finite subgroup of the plane orthogonal group it contains \(D_m\), and its rotation subgroup has order a multiple of \(m\) dividing \(2m\), since nonidentity rotations fix no nonzero point. Order \(2m\) would make the polygon regular, so its order is \(m\).

Choose any \(x\in X\). In each recovered block, the local group acts freely at the projected vertex. For each vertex \(y\in X\), there is thus a unique product of local orthogonal maps carrying each projection of \(x\) to the corresponding projection of \(y\). These products give precisely the unknown group's restriction to the orbit span. That restriction is faithful because the orbit is free. It can also be read as a permutation group on \(X\).

Finally, any competing generic representation of a finite real orthogonal group matching the Gram graph has no real irreducible constituent of dimension at least three. Such a constituent's isotype would receive nonzero seed projection generically, and hence contribute a nonzero covariance eigenspace containing an irreducible subrepresentation of that dimension. All observed positive eigenspaces have dimension at most two. A competitor therefore satisfies the same local descriptions and leads to the identical product reconstruction.
