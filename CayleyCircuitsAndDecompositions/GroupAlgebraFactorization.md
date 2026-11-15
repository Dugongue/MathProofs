# Loewy lengths in tensor products of regular modules

**Counterexample.** For every prime $p$ and every field $k$ of characteristic $p$, there is a directly indecomposable $p$-group $G$ and permutation modules $M,N$ over $kG$ for which the diagonal tensor product is the regular module and
$$
 \ell(M)+\ell(N)-1-\ell(kG)=p-1.
$$
This refutes the conjecture immediately after Corollary 1.8 in Philip Lloyd Osterlund's 1997 thesis. The gap is unbounded for each fixed $p$ if $G$ can be a direct product. The corresponding algebra factorization problem of Carlson and Kovács concerns a stronger premise. Sections 4 and 5 prove the algebra result over every coefficient field of characteristic $p$ when the group has central elementary abelian Frattini subgroup. [Osterlund, *Tensor Decompositions of the Regular Representation of p-Groups Over Fields of Characteristic p*, Chapter 3, p. 74](https://www-users.cse.umn.edu/~webb/PhDStudents/OsterlundThesis.pdf#page=76) · [Carlson–Kovács, §5](https://archives.maths.anu.edu.au/people/Kovacs/K089.pdf)

## 1. Exact formula for regular tensor products of permutation modules

Let $J$ be the augmentation ideal of $kG$, which is its nilpotent Jacobson radical. Let $\ell(X)=\min\{t:J^tX=0\}$ for a nonzero $kG$-module $X$. Write $D_i=\{g\in G:g-1\in J^i\}$ for the Jennings dimension subgroups. For $H\leq G$, set
$$
 d_i=\dim_{\mathbb F_p}(D_i/D_{i+1}),\qquad
 h_i=\dim_{\mathbb F_p}((H\cap D_i)/(H\cap D_{i+1})).
$$
Then
$$
 \ell(k[G/H])-1=(p-1)\sum_{i\geq1} i(d_i-h_i).
$$
To see this, in each $D_i/D_{i+1}$ take a basis of the image of $H\cap D_i$, extend it to a basis of the whole quotient, and use corresponding group lifts. Put the lifts from $H$ at the end of the ordering of the Jennings generators. The monomials in the lifted $g-1$, with exponents from $0$ to $p-1$, form a basis of $kG$ in which $J^s$ is spanned by the weight-at-least-$s$ monomials. The weight of the factor $g-1$ is $i$ for $g\in D_i\setminus D_{i+1}$. This is Jennings's basis theorem with an arbitrary fixed ordering.

Apply these basis elements to the coset $H$ in $k[G/H]$. Every monomial using at least one lift $g\in H$ is zero, since it ends in such a $g-1$. The remaining monomials span and their number is exactly $[G:H]$, since $\sum_i d_i=\log_p|G|$ and $\sum_i h_i=\log_p|H|$. They give a basis of the permutation module, so the largest surviving weight gives its Loewy length. [Jennings theory in Webb, *A Course in Finite Group Representation Theory*, §6](https://doi.org/10.1017/CBO9781316677216.007) · [Alperin, *Loewy Structure of Permutation Modules for p-Groups*](https://doi.org/10.1093/qmath/39.2.129)

If $G=HK$ and $H\cap K=1$, set $M=k[G/H]$ and $N=k[G/K]$. The diagonal action on $G/H\times G/K$ is regular. Indeed the stabilizer of $(H,K)$ is trivial and the product of the two coset-set sizes is $|G|$. Hence $M\otimes_k N\cong kG$ as $kG$-modules. Subtracting the formulas for these modules and the regular module gives
$$
\begin{split}
 \ell(M)+\ell(N)-1-\ell(kG)
 &=(p-1)\sum_{i\geq1}i(d_i-h_i-k_i)\\
 &=(p-1)\sum_{i\geq1}
   \log_p\frac{|D_i|}{|H\cap D_i|\,|K\cap D_i|},
\end{split}
$$
where $k_i=\dim_{\mathbb F_p}((K\cap D_i)/(K\cap D_{i+1}))$. The second equality is summation of the tail sums, since each coefficient of index $j$ occurs in exactly $j$ tails. All summands in the last line are nonnegative. The product $(H\cap D_i)(K\cap D_i)$ is a subset of $D_i$ and has size $|H\cap D_i||K\cap D_i|$. Thus equality in Osterlund's conjecture for these permutation-module factorizations holds exactly when $D_i=(H\cap D_i)(K\cap D_i)$ for every $i$.

## 2. A directly indecomposable family at every prime

Let $V=\mathbb F_p^3$ and $W=\mathbb F_p^3$ with respective ordered bases $e_1,e_2,e_3$ and $a,b,c$. On $V\oplus W$, define
$$
 (v,w)(v',w')=(v+v', w+w'+v_1v'_2a+v_1v'_3b+v_2v'_3c).
$$
Bilinearity of the correction gives associativity, identity $(0,0)$, and inverses. The central subgroup $0\oplus W$ is written multiplicatively below. Write $x=(e_1,0)$, $y=(e_2,0)$, $z=(e_3,0)$. They have order $p$, and their ordered commutators generate $W$, with each pair giving one of $a,b,c$ up to the commutator sign convention. The commutator map is the wedge map $\wedge^2 V\to W$ up to sign. Consequently $G'=Z(G)=W$, since a nonzero $v\in V$ has a nonzero wedge with some $v'$. For odd $p$, $G$ has exponent $p$ by the binomial formula for powers in this bilinear model. For $p=2$ its squares lie in $W$ and it has exponent four. In both cases $\Phi(G)=W$, and the Jennings dimension subgroups are $D_1=G$, $D_2=W$, $D_3=1$. This follows from the dimension subgroup formula as all commutators are central of order dividing $p$, and only $p=2$ can have nontrivial powers of weight two.

The group is directly indecomposable. An abelian direct factor would lie in the center, which here is the derived subgroup and intersects any abelian direct factor trivially. If there were two nonabelian direct factors, their minimal generator counts would each be at least two. The counts add under direct product of finite $p$-groups by the Frattini quotient. Here that quotient has dimension three.

Use $H=\langle x,y\rangle$ and $K=\langle xc,z\rangle$. Their images in $G/W$ are the planes $\langle e_1,e_2\rangle$ and $\langle e_1,e_3\rangle$, and their intersections with $W$ are $\langle a\rangle$ and $\langle b\rangle$, respectively. To verify the latter claims, collect the powers of the two generators of each subgroup, adding only powers of their one commutator. The two planes meet in $\langle e_1\rangle$. Two elements above a common vector $i e_1$ in that line have forms $x^i a^j$ and $x^ic^ib^t$, so they can be equal only if $i,j,t$ are all zero. Thus $H\cap K=1$. Their orders are both $p^3$, so $HK=G$.

The dimension-subgroup gap formula has only one nonzero summand, at $D_2=W$, where the ratio of orders is $p^3/(p\cdot p)=p$. Therefore the gap is $p-1$. Equivalently, the regular module has length $1+9(p-1)$ and each permutation factor has length $1+5(p-1)$. Taking an $m$-fold direct product and the corresponding products of $H$ and $K$ makes the gap $m(p-1)$. The dimension subgroups of the direct product are the coordinatewise products, as follows from the dimension subgroup formula.

## 3. An order-sixteen counterexample

Osterlund also remarks after the conjecture that it holds for groups of order at most $16$. With the quantifiers in the stated conjecture there is a counterexample of order $16$. Let $G=D_8\times C_2$, with $r$ the order-four rotation, $s$ a reflection, and $c$ the generator of the second factor. Write $t=r^2$, and take $H=\langle s,c\rangle$, $K=\langle rs,tc\rangle$. Each subgroup has order four. Their noncentral involutions have different $D_8/Z(D_8)$ images, and their central intersections are $\langle c\rangle$ and $\langle tc\rangle$, respectively. Therefore the intersection is trivial and $G=HK$. Here $D_2=\langle t\rangle$, $D_3=1$, and $H$ and $K$ both intersect $D_2$ trivially. The Loewy lengths are $6$ for $kG$ and $4$ for each permutation factor. This example uses a directly decomposable group. The construction in Section 2 also refutes the conjecture under the additional restriction of direct indecomposability. [Conjecture and order bound](https://www-users.cse.umn.edu/~webb/PhDStudents/OsterlundThesis.pdf#page=76)

## 4. The algebra factorization result over the prime field

**Theorem.** If the Frattini subgroup of a finite $p$-group $G$ is central and elementary abelian, and $\mathbb F_pG\simeq A\otimes_{\mathbb F_p}B$ as unital algebras, then $G$ has a direct decomposition $G=G_A\times G_B$ with $\mathbb F_pG_A\simeq A$ and $\mathbb F_pG_B\simeq B$.

Write $k=\mathbb F_p$, $R=kG$, and $I=I(k\Phi(G))R$ for the relative augmentation ideal. The ideal $I$ is intrinsic. It is generated by commutators of elements of $J$ and by $p$-th powers of elements of $J$. Indeed the commutator ideal is the kernel of $kG\to k[G/G']$. In the latter commutative group algebra the $p$-th powering identity and $(g-1)^p=g^p-1$ show that imposing the remaining relations gives the quotient $k[G/(G'G^p)]$. Since $G'G^p=\Phi(G)$, this proves the intrinsic description.

Use the tensor identification and give $A,B$ the augmentations inherited from $R$. Their augmentation ideals are $J_A,J_B$; they are nilpotent since they lie in $J$. Define $I_A,I_B$ by the same intrinsic commutator and $p$-power recipe. Then
$$
 I=I_A\otimes B+A\otimes I_B.
$$
For commutators this follows by abelianizing $A\otimes B$. For powers it suffices to work in that commutative quotient and use additivity of Frobenius on sums of pure tensors from $J_A\otimes B+A\otimes J_B$. The two augmentation retractions give the direct-sum decomposition
$$
 I/JI\ \cong\ (I_A/J_AI_A)\oplus (I_B/J_BI_B).
$$
Indeed, every pure tensor from $I_A\otimes B$ reduces to $a\otimes 1$ times the augmentation of its second coordinate modulo $JI$, and similarly in the other summand. Here $IJ=JI$ since $I$ is generated by central group elements minus one. The two retractions show that no further ties between the summands are introduced.

The maps $g\mapsto g-1$ identify $G/\Phi(G)$ with $J/J^2$ and $\Phi(G)$ with $I/JI$ as $\mathbb F_p$-spaces. For the second identification, choose representatives of $G/\Phi(G)$, so $I$ is a sum of copies of $I(k\Phi(G))$ indexed by cosets. Modulo $JI$ each coset representative can be removed, and $I(k\Phi(G))^2$ vanishes. Conversely the sum of coefficients in the coset copies, taken modulo $I(k\Phi(G))^2$, kills $JI$. Multiplying by a group element only permutes these copies and multiplies a coefficient by an element of $\Phi(G)$, which acts trivially modulo $I(k\Phi(G))^2$. This proves the second identification since $\Phi(G)$ is elementary abelian. The first identification is the standard augmentation tangent isomorphism and also follows by passage to $k[G/\Phi(G)]$, since $I\subseteq J^2$, and by the truncated polynomial presentation of that elementary abelian group algebra.

In $R/JI$, the image of $I$ annihilates the image of $J$ on both sides, and contains every additive commutator and $p$-th power of elements of $J$. The additive commutator and $p$-th powering of an element of $J$ therefore respect changes of representatives modulo $J^2$. For commutators, $[J^2,J]=0$ in this quotient. For powers, any word of at least three elements of $J$ can be freely reordered, since interchanging two adjacent elements inserts a commutator multiplied on one side or the other by another $J$-element. Hence for $a,b\in J$, $(ab)^p=a^pb^p=0$. Elements of $J^2$ commute with each other and with $J$. It follows by Frobenius for commuting elements that every $r\in J^2$ has $r^p=0$, and that $(a+r)^p=a^p$.

Under the group identifications, these two operations are the commutator and power maps of the central extension. The algebra commutator of $g-1,h-1$ is congruent to the group commutator minus one modulo $JI$, and $(g-1)^p=g^p-1$. Write $U_A\oplus U_B=J/J^2$ for the tensor splitting of the tangent space. Representatives for vectors in $U_A$ and $U_B$ can be chosen in the corresponding embedded augmentation ideals. They commute across factors, and commutators within either side and $p$-th powers on that side land in the corresponding summand of $I/JI$.

Choose group lifts of bases of $U_A,U_B$, and let $G_A,G_B$ be the subgroups they generate. They generate $G$ together by the Burnside basis theorem. They commute across factors by the vanishing of the cross commutators. The intersection of each with $\Phi(G)$ is generated by the $p$-th powers and mutual commutators of its chosen lifts. To verify this, collect a word in the lifts, moving commutators and $p$-th powers into the central subgroup and reducing all exponents to $0,\ldots,p-1$. For a word in $\Phi(G)$ all resulting exponents must be zero because the chosen images are independent. The two subgroup intersections with $\Phi(G)$ therefore lie in the two disjoint summands of $I/JI$. Any element of $G_A\cap G_B$ lies first in $\Phi(G)$, since $U_A\cap U_B=0$, and then is trivial. Hence $G=G_A\times G_B$.

Lastly the augmentation retraction $kG\to A$ restricts to a surjection $kG_A\to A$, because the images of its generators minus one span $J_A/J_A^2$. Lifting through the powers of that nilpotent ideal gives generation of $A$. The same argument gives a surjection $kG_B\to B$. The product of the source dimensions is $|G|=\dim A\dim B$. Thus both surjections are isomorphisms.

The prime-field hypothesis in this argument identifies the two tangent summands with actual subspaces of $G/\Phi(G)$. The unrestricted Carlson–Kovács question remains open in this proof. The all-field result for one commutative factor uses a different detection argument. The cited older results include cases with cyclic center or few generators, and Sakurai's uniqueness theorem gives cancellation once algebra factors exist. The literature search did not find an earlier statement of the above refutation or the prime-field Frattini-class-two decomposition. [Erdmann–Kovács](https://archives.maths.anu.edu.au/people/Kovacs/K086.pdf) · [García-Lucas–del Río–Sakurai](https://doi.org/10.1007/s10468-026-10379-4) · [Sakurai, *Tensor factorization of local algebras*](https://arxiv.org/abs/2609.38323)

## 5. The algebra factorization result over every field of characteristic $p$

**Theorem.** Let $k$ be any field of characteristic $p$. For a finite $p$-group $G$ with central elementary abelian Frattini subgroup, every unital algebra factorization $kG\simeq A\otimes_k B$ comes from a direct product $G=G_A\times G_B$ in the sense that $A\simeq kG_A$ and $B\simeq kG_B$.

First assume that $G$ is directly indecomposable. Continue to use $R=kG$, its radical $J$, and the relative augmentation ideal $I$ from Section 4. The intrinsic recipe, the formula $I=I_A\otimes B+A\otimes I_B$, and the splitting formulas for $J/J^2$ and $I/JI$ hold over $k$. Define the rational spaces
$$
V=G/\Phi(G),\qquad W=\Phi(G),\qquad W'=[G,G]\subseteq W
$$
over $\mathbb F_p$. If $D$ is any of these spaces, write $D_k=k\otimes_{\mathbb F_p}D$. The group maps are the alternating commutator $\beta:V\times V\to W'$ and the $p$-th power $q:V\to W$. Their extensions to $k$ are the commutator and power on $J/J^2$ with values in $I/JI$. The operation $q$ is additive and $p$-semilinear for odd $p$, since mixed words of length $p\ge 3$ reorder and the intermediate binomial coefficients vanish. For $p=2$, $q(cv)=c^2q(v)$ and $q(u+v)-q(u)-q(v)=\beta(u,v)$. These statements also hold over $\mathbb F_p$ by restriction. The tangent partitions furnished by the algebra factors are
$$
 V_k=U_A\oplus U_B,\qquad W_k=W_A\oplus W_B.
$$
They satisfy $\beta(U_A,U_B)=0$, $\beta(U_i,U_i)\subseteq W_i$, and $q(U_i)\subseteq W_i$. A containment of a bilinear map's image gives the same containment for its linear span.

**Commutator over the elementary abelian quotient.** Put $\Lambda=k[V]=R/I$. There is a natural $\Lambda$-module isomorphism
$$
 I/I^2\simeq \Lambda\otimes_k W_k .
$$
Choose a transversal for the cosets of the central subgroup $\Phi(G)$. Different cosets are disjoint parts of the group basis. Each coset contributes a copy of $I(k\Phi(G))/I(k\Phi(G))^2\simeq W_k$, since $I^2=I(k\Phi(G))^2 R$. Multiplication by a lifted coset representative translates the cosets. The correction from the choice of transversal lies in $\Phi(G)$ and acts trivially on $I(k\Phi(G))/I(k\Phi(G))^2$. This proves the asserted module action. Also $[R,I]\subseteq I^2$, since $I$ is generated by central elements and $[R,R]\subseteq I$. Consequently the commutator of lifts of two elements of $\Lambda$ is well defined modulo $I^2$.

In a fixed $\mathbb F_p$-basis of $V$, let $E_j$ be the $k$-linear derivation given on the basis element $t_v$ of $\Lambda$ by $E_j(t_v)=v_jt_v$. It is a derivation because $t_vt_u=t_{v+u}$, and $E_j^p=E_j$. Write $Ef=(E_1f,\ldots,E_{\dim V}f)$. On group basis elements the first-order commutator is $t_{v+u}\otimes\beta(v,u)$, by the group commutator identity. Thus on general elements it is $\beta_\Lambda(Ef,Eg)$, with $\beta_\Lambda$ the scalar extension of $\beta$ to $\Lambda$.

Now $\Lambda=A_0\otimes B_0$, where $A_0=A/I_A$ and $B_0=B/I_B$. There is a direct sum
$$
 I/I^2=\big((I_A/I_A^2)\otimes B_0\big)\ \oplus\ \big(A_0\otimes (I_B/I_B^2)\big).
$$
This follows by dividing $I_A\otimes B+A\otimes I_B$ by $I_A^2\otimes B+A\otimes I_B^2+I_A\otimes I_B$. Both summands are $\Lambda$-submodules, and their images at augmentation are respectively $W_A,W_B$. Choose elements $f_a$ in the augmentation ideal of $A_0$ and $g_b$ in the augmentation ideal of $B_0$ lifting bases of their tangents. They generate their respective algebras by successively lifting through their nilpotent radical powers. Since $I\subseteq J^2$, the combined tangent coordinates of $f_a,g_b$ form a basis of $V_k$. At the augmentation of $\Lambda$, the gradient of $h=\sum_v c_v t_v$ specializes to $\sum_v c_v v$, its tangent coordinate. The combined gradients $Ef_a,Eg_b$ therefore form a basis of the free $\Lambda$-module $\Lambda\otimes_k V_k$ by the determinant unit test in the local ring $\Lambda$. Write $P_A,P_B$ for their respective spans. At augmentation they specialize to $U_A,U_B$.

The spaces $P_A,P_B$ are cross-orthogonal for $\beta_\Lambda$, since the $A$- and $B$-lifts commute. The spans of their internal bracket images belong to the respective independent $\Lambda$-summands of $I/I^2$ above. These two bracket spans together give $\Lambda\otimes_k W'_k$, since $P_A\oplus P_B$ is the whole input module and $W'$ is the span of $\beta$.

**Descent of the noncentral slots.** Let $\mathcal R=\{v\in V: \beta(v,V)=0\}=Z(G)/\Phi(G)$. The radical of $\beta_\Lambda$ is the extension of $\mathcal R$, as its defining linear equations are over $\mathbb F_p$. The projections onto $P_A,P_B$ preserve this radical. Indeed, if $a+b$ is in the radical, where $a\in P_A$ and $b\in P_B$, then $a$ has zero bracket with $P_A$ because $b$ does, and also has zero bracket with $P_B$ by cross-orthogonality. The same holds for $b$. Thus $P_A,P_B$ induce complementary summands over $\Lambda$ in the radical-free quotient $\bar V=V/\mathcal R$. Write $\bar\beta:\bar V\times\bar V\to W'$ for the induced map. Let $e$ be the projection onto the first induced input summand and let $f$ be the projection onto the first internal bracket span in $\Lambda\otimes_k W'_k$. Cross-orthogonality gives
$$
 \bar\beta_\Lambda(e x,y)=\bar\beta_\Lambda(x,e y)=f\bar\beta_\Lambda(x,y).
$$

The centroid of $\bar\beta$ consists of pairs satisfying these linear equations, with componentwise composition. This algebra is commutative. In fact, if $(e,f),(e',f')$ are two such pairs, evaluating $\bar\beta(ex,e'y)$ in both orders shows $ff'=f'f$, because $\bar\beta$ spans its output. Then $\bar\beta(ee'x,y)=\bar\beta(e'ex,y)$ shows $ee'=e'e$ because $\bar\beta$ is radical-free. The equations also show closure under composition. Formation of this algebra commutes with extension from $k$ to $\Lambda$, since the equations are linear over $k$. In any commutative algebra, two idempotents $a,b$ with nilpotent difference agree, because $a(1-b)$ and $b(1-a)$ are nilpotent idempotents and vanish. Apply this to the centroid over $\Lambda$, using the nilpotent augmentation ideal of $\Lambda$. The augmentation of $(e,f)$ admits a constant idempotent lift from $k$. Therefore $(e,f)$ itself is constant. The projected gradient spans are the scalar extensions of the projected tangent spaces $\bar U_A,\bar U_B$ in $\bar V_k$.

For a functional $\lambda\in(\bar V_k)^*$, view it as a functional on $V_k$ vanishing on $\mathcal R_k$, and form $D_\lambda=\sum_j\lambda_j E_j$. The derivation $D_\lambda$ kills all of $A_0$ precisely when it kills the $f_a$, which is precisely when $\lambda$ annihilates $\bar U_A$, by the constant gradient span. Since $D_\lambda^p=D_{\lambda^{(p)}}$ on the group basis, with coordinatewise $p$-th power in a rational basis, the annihilator of $\bar U_A$ is stable under coordinatewise Frobenius. The same holds for $\bar U_B$. A subspace with this property is rational over $\mathbb F_p$. Take its reduced row echelon basis. Coordinatewise Frobenius preserves its pivot table and linear independence, and leaves its rows in the subspace, so uniqueness of the reduced row echelon matrix fixes every entry. This argument includes imperfect $k$. It shows that $\bar U_A,\bar U_B$ come from rational complementary summands in $\bar V$, denoted by the same symbols. Their internal bracket spans $W'_A,W'_B$ are likewise rational.

**Lifting over the central directions.** If $G$ is abelian, direct indecomposability makes $G$ cyclic and $\dim_k J/J^2=1$. Both nontrivial algebra factors would have positive tangent dimension by nilpotence of their augmentation ideals, so there is no such factorization. For nonabelian directly indecomposable $G$, the map $q|_{\mathcal R}$ is injective. If a nonzero $v\in\mathcal R$ has $q(v)=0$, a lift is a central element $z$ of order $p$ outside $\Phi(G)$. A functional on $G/\Phi(G)$ nonzero on $v$ gives a retraction onto $\langle z\rangle$, which splits off this central subgroup. This is impossible. As $q|_{\mathcal R}$ is linear over $\mathbb F_p$, put $Q_0=q(\mathcal R)\subseteq W$, and identify $\mathcal R$ with $Q_0$ by $q$.

The original tangent summands $U_A,U_B$ split $\mathcal R_k$ into their intersections with it by the same orthogonality argument. The $k$-spans of the $q$-images of those intersections give complementary subspaces of $Q_{0,k}$, precisely $Q_{0,k}\cap W_A$ and $Q_{0,k}\cap W_B$. Here $q$ is semilinear on the radical. It takes a basis of $\mathcal R_k$ to a basis of $Q_{0,k}$, since the determinant of the basis in rational coordinates is sent to its $p$-th power. This use of spans includes imperfect $k$.

Each $W_i$ is spanned by $q(U_i)$ and the internal $\beta$-image, for $i=A,B$. These images together span $W_k$ since $G^p[G,G]=\Phi(G)$, the cross bracket vanishes, and $q$ on a sum across the slots is additive. Independence of $W_A,W_B$ gives the separate equalities. Consequently the image of $W_i$ in $W_k/Q_{0,k}$ is rational. It is spanned by $W'_i$ modulo $Q_0$ and the $q$-images of rational lifts of a rational basis of $\bar U_i$. Indeed, lifts in $U_i$ of that same basis over $k$ differ from the rational lifts by radical vectors, so their powers agree modulo $Q_{0,k}$. Powers of linear combinations are governed by semilinearity and, for $p=2$, the internal bracket already included. Denote the two complementary rational output images by $\bar W_A,\bar W_B\subseteq W/Q_0$.

Choose a rational complementary decomposition $Q_0=Q_A^\circ\oplus Q_B^\circ$ in which $Q_i^\circ$ contains $W'_i\cap Q_0$ and has the dimension of $W_i\cap Q_{0,k}$. The required subspaces exist by extending the two independent bases of $W'_A\cap Q_0,W'_B\cap Q_0$ and assigning the remaining basis vectors to attain the dimensions. For each $i$, choose a rational subspace $W_i^\circ\subseteq W$ with intersection $Q_i^\circ$ with $Q_0$, image $\bar W_i$ in $W/Q_0$, and containing $W'_i$. Start with $W'_i+Q_i^\circ$ and adjoin rational lifts of a basis extending its image to $\bar W_i$. The $W_i^\circ$ are therefore complementary.

For each rational basis vector of $\bar U_i$, take a rational lift $x\in V$. Its power $q(x)$ is in $W_i^\circ+Q_0$. By adding a rational radical vector to $x$, one can put its power in $W_i^\circ$, using the isomorphism $q: \mathcal R\to Q_0$ and additivity across a radical vector. Span these corrected vectors together with $q^{-1}(Q_i^\circ)\subseteq\mathcal R$ to obtain $U_i^\circ$. The $U_i^\circ$ are rational and complementary, each of dimension $\dim_k U_i$. These dimensions follow from the maintained dimensions of the quotient and radical slots. The $U_i^\circ$ have zero cross bracket since their projected slots do, and their internal brackets lie in $W'_i\subseteq W_i^\circ$. The power map takes $U_i^\circ$ into $W_i^\circ$ by the correction on the basis and the expansion formula for $q$.

Finally lift bases of $U_A^\circ,U_B^\circ$ to group elements. Collection of words as in Section 4 gives commuting subgroups that together generate $G$ and have trivial intersection, since the powers and commutators in each are contained in the complementary $W_i^\circ$. If $A,B$ are nontrivial then both $U_i$ have positive dimension, hence both resulting subgroups are nontrivial. This contradicts direct indecomposability and proves that $kG$ is tensor-irreducible for every directly indecomposable $G$ in the theorem.

**Recovering the prescribed algebra factors.** For arbitrary $G$ in the theorem, choose a decomposition into directly indecomposable subgroups. Their Frattini subgroups are again central elementary abelian, since the Frattini subgroup of a direct product of finite $p$-groups is the product of the Frattini subgroups. By what was proved, the corresponding group algebras are tensor-irreducible. Refine $A$ and $B$ into tensor-irreducible factors. Sakurai's Theorem A matches this second list of factors with the group-algebra list, since $kG$ is a split local algebra. The products of the group factors matching the refinements of $A$ and $B$ are the required $G_A,G_B$. The unrestricted Carlson–Kovács question for other finite $p$-groups remains open in this proof. [Carlson–Kovács, §5](https://archives.maths.anu.edu.au/people/Kovacs/K089.pdf) · [Sakurai, Theorem A](https://arxiv.org/html/2609.38323v1#S1)
