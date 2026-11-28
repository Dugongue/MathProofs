# A fixed closed aspherical four-manifold realizes every affine integral solution set

For every affine scheme \(X\) of finite presentation over \(\mathbb Z\), there is a closed connected oriented smooth stably parallelizable four-manifold \(M_X\) containing an embedded marked bouquet \(A\) of three circles. One fixed closed orientable aspherical smooth four-manifold \(Y\), with one fixed based boundary map \(f:A\to Y\), gives a bijection
\[
[M_X,Y]_f\cong X(\mathbb Z).
\]
Here maps and homotopies fix \(f\) pointwise. The fundamental group of \(Y\) is virtually two-step nilpotent. The same presentation provides a fixed group functor and a natural bijection to \(X(R)\) for all rings \(R\) with no additive two-torsion. A variant with a six-dimensional closed aspherical integral target works naturally for every commutative coefficient ring, including rings with additive torsion and nilpotents.

## The fixed four-manifold

For a commutative ring \(R\) with identity, let \(N(R)\) have elements \((p,q,z)\) in \(R^3\) with multiplication
\[
(p,q,z)(p',q',z')=(p+p',q+q',z+z'+pq').
\]
Use the convention \([a,b]=aba^{-1}b^{-1}\). Write \(P=\{(p,0,0)\}\) and \(Q=\{(0,q,0)\}\). Let \(s\) generate a copy of \(\mathbb Z\) acting on \(N(R)\) by
\[
\alpha(p,q,z)=(-q,p,z-pq).
\]
The cross term in the group law gives \(\alpha(nn')=\alpha(n)\alpha(n')\). We have \(\alpha^2(p,q,z)=(-p,-q,z)\) and \(\alpha^4=1\). Put \(G(R)=N(R)\rtimes_\alpha\mathbb Z\) and mark \(s,e=(1,0,0),f_0=(0,1,0)\).

For \(R=\mathbb Z\), \(G(\mathbb Z)\) acts on \(N(\mathbb R)\times\mathbb R\) by
\[
(n,a)\cdot(m,r)=\bigl(n\alpha^a(m),r+a\bigr).
\]
It is a free properly discontinuous action. Its quotient is a smooth bundle over a circle with fiber the compact Heisenberg nilmanifold \(N(\mathbb Z)\backslash N(\mathbb R)\). For compactness of the fiber, first use the integer \(p,q\) coordinates of a left translation to reduce \(p,q\) modulo one, then use its integer \(z\) coordinate to reduce the resulting \(z\) modulo one. The automorphism has determinant one on the tangent spaces of \(N(\mathbb R)\cong\mathbb R^3\), so the quotient is orientable. Contractibility of the covering space makes this quotient \(Y\) a classifying space for \(G(\mathbb Z)\). The subgroup over \(4\mathbb Z\) is \(N(\mathbb Z)\times 4\mathbb Z\) and has index four.

## Arithmetic with three marked loops

When multiplication by \(2\) is injective on \(R\), the simultaneous equations
\[
[e,u]=1,\qquad s^2us^{-2}=u^{-1}
\]
select exactly \(P\). The second equation forces the image of \(u\) in the quotient \(\mathbb Z\) to equal its negative, so \(u=(p,q,z)\). The first then says \(q=0\). On that centralizer, comparison of \(\alpha^2(u)\) with \(u^{-1}=(-p,0,-z)\) says \(2z=0\). Conversely the equations hold on all of \(P\). Replacing \(e\) by \(f_0\) selects \(Q\) by the same argument since \([f_0,(p,q,z)]=(0,0,-p)\).

Associate one \(P\)-variable \(u_a\) and one \(Q\)-variable \(v_a\) to each wire of an arithmetic circuit. The relation \([u_a,f_0]=[e,v_a]\) identifies their scalar coordinates because \([(p,0,0),(0,q,0)]=(0,0,pq)\). Addition and multiplication gates with inputs \(a,b\) and output \(c\) are respectively
\[
u_a u_b=u_c,\qquad [u_a,v_b]=[u_c,f_0].
\]
Constants use \(u_0=1\) and \(u_1=e\). Negation is addition to zero, and every prescribed zero output is pinned to \(1\) in \(P\). Starting from a finite polynomial presentation for \(X\), introduce circuit wires in a topological order. Each internal wire is uniquely determined from the input values, and the output equations hold exactly when those inputs satisfy the defining polynomials of \(X\). All reconstructions commute with homomorphisms of the indicated coefficient rings.

## Closed sources and strict boundary maps

Take the finite presentation complex with one vertex, the three marked loops, two loops per scalar wire, and one two-cell per relator. Write \(\Gamma_X\) for its fundamental group. A homomorphism \(\Gamma_X\to G(R)\) whose values on the three marked generators are \(s,e,f_0\) is exactly a circuit solution.

Build a smooth compact five-dimensional handlebody \(W\) with this presentation. Attach 1-handles for the generators to a ball. Represent the attaching words by disjoint embedded circles in its four-dimensional boundary, by general position for unbased loops, and attach five-dimensional 2-handles. The oriented rank-three normal bundles of these circles are trivial. Starting with a trivialization on the ball, choose 1- and 2-handle framings that extend the tangent trivialization. At index two the possible changes in the normal framing surject onto \(\pi_1 SO(5)\), since \(\pi_1 SO(3)\to\pi_1 SO(5)\) is an isomorphism. Thus \(W\) is parallelizable. Dual handles relative to \(M_X=\partial W\) have index at least three, so \(M_X\to W\) is an isomorphism on fundamental groups. In particular \(M_X\) is connected, and it is stably parallelizable since \(TM_X\oplus\mathbb R=TW|_{M_X}\). In \(M_X\) choose an embedded based bouquet representing the three marked generators. A map from this finite graph can be homotoped to a PL embedding with fixed vertex by general position in dimension four. The inclusion is a cofibration. Use as the boundary map any one fixed choice of based loops representing \(s,e,f_0\) in \(Y\).

For a connected CW pair with connected marked subcomplex and a fixed based boundary map to \(BG\), relative homotopy classes correspond bijectively to based fundamental group homomorphisms with the prescribed restriction. One proof uses the universal covers. For a proposed homomorphism \(\rho\), its agreement with the boundary homomorphism gives a lift of the prescribed boundary map from the preimage of the marked subcomplex, equivariant under \(\rho\). To construct it, lift on the component through the chosen basepoint using agreement on the kernel of the boundary inclusion on fundamental groups, then transport that lift to the other components by equivariance. Extend equivariantly over the lifted cells of the whole source, since the target universal cover is contractible. The same argument for the relative cylinder extends the two prescribed lifted maps and the stationary lifted marking to an equivariant homotopy, proving uniqueness. The argument applies to arbitrary connected CW pairs and preserves the fixed marking pointwise. Applying it to \(M_X\) gives the theorem.

## Exact point functor over every commutative ring

Let \(P_R=R^2\) and \(Q_R=R^2\). Use the same law on \(P_R\times Q_R\times R\) with the dot product \(p\cdot q'\) as the cross term. Put \(U=\begin{pmatrix}0&-1\\1&1\end{pmatrix}\) and \(V=U^{-T}\). Let \(s\) act by \((p,q,z)\mapsto(Up,Vq,z)\), which preserves the dot product, and form the semidirect product with \(\mathbb Z\). Use the basis \(e_1,e_2\) in \(P_R\) and its dual \(f_1,f_2\) in \(Q_R\), also writing these symbols for the corresponding embedded group elements. Only \(s,e_1,f_1\) are marked. The other basis elements are the words \(e_2=se_1s^{-1}\) and \(f_2=(sf_1s^{-1})f_1^{-1}\), since \(Ue_1=e_2\) and \(Vf_1=f_1+f_2\).

To select the copy \(R e_1\) in \(P_R\) impose
\[
u=[s,(sus^{-1})^{-1}],\qquad [u,e_1]=[u,e_2]=[u,f_2]=1.
\]
The first equation places \(u\) in the kernel of the \(\mathbb Z\) quotient because its right side is a commutator. On that kernel the other equations are exactly \(q_1=q_2=p_2=0\), by the dot product commutator. For \(u=(p,0,z)\) the first equation has right side \(((U-I)(-U)p,0,0)\), since the action fixes the center. As \(U^2-U+I=0\), the matrix \((U-I)(-U)\) is the identity. Thus \(u=(p,0,0)\) with \(p\) an arbitrary multiple of \(e_1\). For the copy \(R f_1\), keep the first equation and use \([u,f_1]=[u,f_2]=[u,e_2]=1\). The resulting proof uses \(V^2-V+I=0\).

The matching relation and the circuit gates apply with \(e=e_1,f_0=f_1\). Their commutator pairings are exact since \(e_1\cdot f_1=1\). This gives a natural bijection with \(X(R)\) for every commutative ring and preserves the entire affine point functor.

For \(R=\mathbb Z\) the group is the fundamental group of the corresponding mapping torus. Its nilmanifold fiber has dimension five and is compact by the preceding coordinate reduction, applied to two \(p\), two \(q\) and one \(z\) coordinate. The action preserves orientation since \(U,V\) have determinant one. The mapping torus is a fixed closed orientable aspherical six-manifold. Both matrices have order six, so the preimage of \(6\mathbb Z\) is a two-step nilpotent direct product of index six. The same four-dimensional closed-source construction applies with the three marked loops.

## Relation to earlier work

Diophantine interpretability of coefficient rings in nilpotent groups and universality for representation-scheme germs provide neighboring results. The statements here give an explicit global bijection, prescribed elements from a single fixed group, uniquely determined auxiliary variables, and closed smooth sources and integral targets. [Garreta, Miasnikov and Ovchinnikov](https://arxiv.org/abs/1805.04085), [Kapovich and Millson](https://arxiv.org/abs/1303.2347)
