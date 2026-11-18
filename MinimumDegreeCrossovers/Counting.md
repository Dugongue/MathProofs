# Fixed dihedral quotients and counting small transitive group actions

These are informal proofs. Complexity is measured in the written finite presentation or explicit permutation generators, as indicated.

**Theorem A.** Epimorphism testing from finite presentations onto the dihedral group $D_8$ of order eight is NP-complete. This answers Elder–Shen–Weiß Open Question 4.1. Hardness holds for presentations of finite class-two groups of exponent dividing four, and also for explicit permutation generators of such groups whose supplied actions have orbit sizes at most eight. In the latter model even counting equivalence classes of transitive four-point actions is #P-complete. For every fixed nonabelian finite dihedral group, epimorphism testing from finite presentations is NP-complete. For every fixed nonabelian dihedral $2$-group, counting epimorphisms from finite presentations is #P-complete, with finite $2$-groups as the hard source instances. [Elder–Shen–Weiß, Open Question 4.1 and Theorem A](https://arxiv.org/html/2610.39487v1#S4) · [Their original 2025 challenge problem](https://arxiv.org/html/2501.05283v1)

**Theorem B.** Fix an odd prime $p$. Counting index-$p^2$ subgroups and counting their conjugacy classes are each #P-complete under single-call polynomial-time counting reductions, already on class-two groups of exponent dividing $p^2$ supplied by permutation generators with all orbit sizes at most $p^3$. The second count is the number of transitive $p^2$-point actions up to group-equivariant isomorphism. Hardness remains if only actions with nonabelian image are counted. Counting epimorphisms onto the fixed Heisenberg group of order $p^3$ is also #P-complete on these sources, and its decision version is NP-complete.

## 1. Circuit assignments become rank-one points

For a Boolean circuit, use indices for all input bits and gate outputs and an additional index 0. Over any fixed prime field, define a symmetric matrix space $L$ by homogeneous linear relations
$$
 M_{ii}=M_{i0}\ (i>0),\qquad
 M_{z0}=M_{xy}\ (z=x\wedge y),\qquad
 M_{z0}=M_{00}-M_{x0}\ (z=\neg x),\qquad
 M_{\mathrm{out},0}=M_{00}.
$$
Every nonzero symmetric rank-one matrix has the form $suu^{\mathsf T}$ with $s\ne0$, in characteristic two as well. The first equations force $u_0\ne0$ and $u_i/u_0\in\{0,1\}$ for each $i>0$. The remaining equations enforce the gate evaluations and acceptance. Conversely each satisfying input assignment determines the gate outputs uniquely and gives exactly one projective rank-one line by $u_0=1$. Thus the number $R$ of projective rank-one lines in $L$ is exactly the number of satisfying assignments. Compute $L$ or its annihilator by Gaussian elimination.

## 2. Hardness for the dihedral group of order eight

Over $\mathbb F_2$ take vector spaces $X,Y$ of positive dimensions $a,b$. Set $E=X\otimes Y$, let $K\subseteq E$, choose a complement $I$ to $K$ and put $k=\dim K$. Take $C=(\mathbb Z/4)^k\oplus I$, with $E$ embedded as $2(\mathbb Z/4)^k\oplus I$ and $K=2C$. Construct a group $G(K)$ on $X\times Y\times C$ with product
$$
 (x,y,c)(x',y',c')
  =(x+x',y+y',c+c'+x\otimes y').
$$
The bilinear cocycle gives associativity. The commutator factors as the alternating form
$$
 \beta\bigl((x,y),(x',y')\bigr)=x\otimes y'+x'\otimes y.
$$
Its values span $E$, and its common radical is zero because $X,Y$ both have positive dimension. Thus $[G,G]=E$ and $Z(G)=C$. Squares are $2c+x\otimes y$, so the exponent divides four.

Realize $D_8$ by the same law with $X,Y,C$ all equal to $\mathbb F_2$. In this model the two coordinate lifts are involutions with nontrivial central commutator, and their product has order four. The commutator form on the two-dimensional central quotient is nondegenerate alternating, and the square form on that quotient is $(r,s)\mapsto rs$.

Any epimorphism $G(K)\to D_8$ sends $C$ into the center of the target by surjectivity. Its restriction $\lambda:C\to\mathbb F_2$ kills $2C=K$ and is nonzero on $E$ because the commutator subgroup must map onto that of $D_8$. The pullback of the target's commutator form along the induced surjective map $X\oplus Y\to\mathbb F_2^2$ has rank two. That pullback is $\varphi\beta$ for $\varphi=\lambda|_E$, whose matrix has zero diagonal blocks and opposite off-diagonal blocks $\varphi,\varphi^{\mathsf T}$. Its rank is twice the matrix rank of $\varphi$ in every characteristic. Hence $\varphi$ has rank one and belongs to $K^\perp$.

Conversely, if $\varphi=u\otimes v\in K^\perp$ is nonzero of rank one, extend it to $\lambda:C\to\mathbb F_2$ using $\varphi|_I$ and any $\mathbb F_2$-valued assignments to the long generators. Then
$$
 (x,y,c)\longmapsto (u(x),v(y),\lambda(c))
$$
respects the products and is onto. Setting $K=L^\perp$ from Section 1 gives the SAT reduction.

For the finite-presentation input, use one lift for each basis vector of $X,Y$, the displayed central cyclic generators with their orders, centrality relations, the commutators of the lifts, and the relation that each basis lift squares to one. Each commutator is written using the embedding $E\hookrightarrow C$ computed by elimination. These relations hold in the group above and allow collection to at most $2^{a+b}|C|$ words, exactly the cardinality of that group. Thus they present it, with polynomial written length.

For the permutation-generator input, choose each tensor-coordinate functional of $E$ in turn. If a functional $\varphi$ kills $K$, the preceding epimorphism onto $D_8$ applies. Otherwise set $\lambda:C\to\mathbb Z/4$ with restriction $2\varphi$ on $E$, choosing each long generator's value to have parity equal to the value of $\varphi$ on its double. Use the quotient on $\mathbb F_2^2\times\mathbb Z/4$ with cocycle $2rs'$. Its order is 16 and its center is its last factor. The coordinate subgroup generated by $(1,0,0)$ has order two and is disjoint from the center in either case. A nonidentity normal subgroup of a finite $2$-group meets its center, so the coset action of each quotient on this subgroup is faithful. It has degree four or eight. The joint action of the pulled-back quotients is faithful. Their kernels intersect the order-two part of $C$ trivially, since this part is $E$ and the coordinate functionals span $E^*$. Any nontrivial joint kernel would meet $C$ and would then contain an order-two element of $C$. Compute each coset action on its constant-size group table. This gives a polynomial-size output with the claimed input orbit cap.

For any finite presentation, one verifies an epimorphism to a fixed finite group by checking all defining relators and generation of the target. For explicit permutation generators $g_1,\ldots,g_s$, check proposed images $h_i$ by forming the subgroup of the product generated by $(g_i,h_i)$ in a disjoint-union action. Its first projection is onto $G$. It is injective exactly when the subgroup's order equals $|G|$, so standard permutation group order algorithms check whether the tuple defines a homomorphism. Generation of the target then gives surjectivity. This proves NP membership and #P membership in both input models. [Seress, Permutation Group Algorithms](https://doi.org/10.1017/CBO9780511546549)

## 3. Exact counts for the order-eight target and four-point actions

For $G(K)$ constructed in Section 2, the number of epimorphisms onto $D_8$ is
$$
                    2^{k+a+b+1} R,
$$
where $R$ is the projective rank-one count of $K^\perp$. Each rank-one $\varphi$ has $2^k$ central extensions $\lambda$. For each such $\lambda$, any allowable map to the target's central quotient has kernel equal to the radical of $\varphi\beta$ and must give an isometry of the induced square form with the target form $rs$. There are exactly two such isometries after choosing one reference, since an isometry of $rs$ permutes its two nonzero isotropic vectors and this permutation determines it. Each of the $a+b$ lift images can choose either central coordinate independently. These assignments extend to group homomorphisms by the normal-form presentation. This proves the count, and dividing by the known factor recovers the number of satisfying assignments. The reduction uses one count and exact polynomial-time arithmetic.

For a nonabelian transitive action of $G(K)$ of degree four, the image is $D_8$, as it is a nonabelian $2$-subgroup of $S_4$ and the Sylow $2$-subgroups of $S_4$ have order eight and are dihedral. The normalizer of a chosen image in $S_4$ is itself since it has index three and is not normal. An isomorphism of two actions is simultaneous conjugation of their generator-image tuples. The actions with fixed chosen image therefore give a count equal to the number of epimorphisms to this image divided by four, the size of its inner automorphism group. Thus the number of nonabelian transitive classes is $2^{k+a+b-1}R$. For abelian images, transitivity forces regularity, and the abelianization of $G(K)$ is elementary abelian of dimension $r=a+b+k$. The count of its index-four subgroups is $(2^r-1)(2^r-2)/6$, obtained by choosing two independent linear forms and dividing by $|\mathrm{GL}_2(2)|$. Adding the abelian and nonabelian terms gives the unfiltered transitive count.

For #P membership for transitive classes, guess the generator images in $S_4$, certify the homomorphism and transitivity, and require the tuple to be lexicographically first among all its simultaneous conjugates in $S_4$. There are only constantly many conjugating permutations. Choose a canonical encoding of each permutation so each tuple is guessed once. The verification procedure counts each class exactly once.

## 4. All fixed finite dihedral targets

Theorem A of Elder–Shen–Weiß handles fixed non-nilpotent finite dihedral targets. Their Proposition B lifts hardness through the quotient by the center. For a dihedral group $D_{2^j}$ of order $2^j$, $j\ge4$, its center has order two and quotient $D_{2^{j-1}}$. Thus our proof for $D_8$ gives NP-hardness inductively for every fixed nonabelian nilpotent dihedral target. The finitely presented source verification above gives NP membership. Fixed abelian dihedral targets are in P by abelianization and Smith normal form. This gives the classification for all fixed finite dihedral groups. [Elder–Shen–Weiß, Proposition B, Open Question 4.1 and Lemma 5.3](https://arxiv.org/html/2610.39487v1)

An explicit counting lift moreover retains finite sources for the nilpotent targets. Given $G=\langle S\mid R\rangle$ and $H=D_{2^j}$, $j\ge4$, put
$$
 G^\sharp=\langle S\mid [r,s]=1,\ r^2=1 \ (r\in R,\ s\in S)\rangle .
$$
There is a quotient $G^\sharp\to G$ with central elementary abelian kernel generated by the images of $R$. Consequently if $G$ is a finite $2$-group, so is $G^\sharp$; its nilpotency class increases by at most one and its exponent at most doubles. Any epimorphism $G^\sharp\to H$ sends the kernel into $Z(H)$ and induces an epimorphism $G\to H/Z(H)$. Conversely every epimorphism $G\to H/Z(H)$ can be lifted by choosing each generator image from its two preimages. The relator images are central involutions or identity, so all choices factor through $G^\sharp$. Since $Z(H)\subseteq\Phi(H)$, any subgroup whose image in $H/Z(H)$ is full is $H$ itself. Here the center is generated by a rotation that is a square, so indeed lies in the Frattini subgroup. Thus the number of lifted epimorphisms is exactly $2^{|S|}$ times the old number. Each presentation increases by a polynomial factor, and the number of iterations depends only on the fixed target. Starting from Section 2 proves #P-completeness for every $D_{2^j}$, $j\ge3$, with presentations of finite $2$-groups of class at most $j-1$ and exponent dividing $2^{j-1}$ as the hard sources.

## 5. Small transitive actions at odd primes

Use the original minimum-permutation-degree group at fixed odd $p$. Its center is $C=(\mathbb Z/p^2)^k\oplus I\oplus C_Y\oplus Q$, where $K=pC$, $C_Y$ is a copy of $Y$, $E=K\oplus I$, and $\ell=\dim Q$. The quotient by $C$ is $A=X\oplus Y$, its commutator is the universal alternating cross pairing, and its powers in the central order-$p$ part are $y+pc$, with $y$ read in $C_Y$. The earlier construction gives explicit faithful permutations with supplied orbit size at most $p^3$. These groups encode $K^\perp$ from the circuit by taking $K=L^\perp$.

Let $H\le G$ have index $p^2$ and nonabelian image in its action on cosets. Write $D=H\cap C$. The index $[C:D]$ is $p$. Indeed index one would make the image a quotient of the abelian group $G/C$. Index $p^2$ would make the central image transitive, hence regular abelian, since a central action stabilizer fixes every point. Its centralizer in the symmetric group of the orbit is the same regular abelian group, so the full image would be abelian. Thus $D=\ker(\lambda)$ for a nonzero $\lambda:C\to\mathbb F_p$ determined up to scalar. The image is nonabelian exactly when $\varphi=\lambda|_E\ne0$ because $E$ is the derived subgroup and $E\subseteq C$. Also $\varphi$ kills $K$.

Put $U=HC/C$, a hyperplane of $A$. A subgroup with this $D,U$ is a complement to $C/D$ in the preimage of $U$ under $G/D\to A$. Existence is equivalent to $(\lambda\beta)|_{U\times U}=0$ and the $p$-th power map of $G/D$ vanishing over $U$. If these hold the preimage is elementary abelian and linear algebra splits it. Conversely a complement is elementary abelian and yields both conditions. A nonzero alternating form admitting an isotropic hyperplane has rank two, so $\varphi$ has matrix rank one. Its radical on $A$ is $\ker u\oplus\ker v$ when $\varphi=u\otimes v$. All isotropic hyperplanes contain that radical and arise from the $p+1$ lines in the two-dimensional quotient.

Fix a projective rank-one $\varphi$ and normalize $\lambda$ by choosing a specified representative of $\varphi$. There are $p^{k+\ell}$ choices on the long generators and $Q$. Let $\psi\in Y^*$ be its restriction to $C_Y$ in the chosen identification. The power map on $A$ is $(x,y)\mapsto\psi(y)$. For $\psi=0$ all $p+1$ hyperplanes are viable. For $\psi\ne0$ the only candidate is $\ker\psi$, which is isotropic exactly when $\psi$ is a nonzero multiple of $v$. This gives $2p$ choices of the pair $(\psi,U)$ in total. Each viable $(D,U)$ yields $p^{a+b-1}$ complements, one for each homomorphism $U\to C/D$ measured from any chosen complement. Conjugation affects neither $D$ nor $U$, and translates the homomorphism by $(\lambda\beta)(g,-)|_U$. The possible translations form a one-dimensional subspace, because $U$ maps to a line in a nondegenerate two-dimensional alternating quotient. Therefore each conjugacy class has $p$ subgroups. Writing $R$ for the projective rank-one count, the nonabelian contributions to the conjugacy-class and subgroup counts are respectively
$$
             2p^{a+b+k+\ell-1}R
 \quad\text{and}\quad
             2p^{a+b+k+\ell}R .
$$

The abelian image occurs precisely for $E\subseteq H$. These subgroups are normal and correspond to subgroups of index $p^2$ in $G/E$, an abelian group of type $(\mathbb Z/p^2)^b\oplus(\mathbb Z/p)^u$ where $u=a+k+\ell$. The $Y$-lifts are the long abelian coordinates because their powers are independent in $C_Y$. The $X$-lifts, the old long central coordinates reduced modulo $E$, and $Q$ supply the short coordinates. Counting surjections to the cyclic and elementary abelian groups of order $p^2$ and dividing by their automorphism group orders gives
$$
 \frac{p^{2b+u}-p^{b+u}}{p^2-p}
       +\frac{(p^{b+u}-1)(p^{b+u}-p)}
                    {(p^2-1)(p^2-p)}.
$$
This same term contributes to both counts. Subtract it and divide by the known nonabelian coefficient to recover $R$. The #P membership argument of Section 3 works with $S_{p^2}$ at fixed $p$. For counting individual index-$p^2$ subgroups, distinguish a base point, and choose the lexicographically first generator-image tuple under simultaneous conjugations fixing that point. Isomorphism of rooted transitive actions identifies exactly the subgroup stabilizing the root, so this counts once per subgroup.

For the fixed exponent-$p$ Heisenberg target, a surjection has a central restriction $\lambda:C\to\mathbb F_p$ with $\varphi=\lambda|_E$ nonzero rank one in $K^\perp$ and $\lambda|_{C_Y}=0$. These conditions follow from commutators and powers. Conversely each such $\lambda$ allows an induced quotient map $A\to\mathbb F_p^2$ carrying $\lambda\beta$ to the target form. Its kernel is the radical of that form and the possible maps form a torsor for $\mathrm{SL}_2(\mathbb F_p)$; maps on independent tangent lifts can choose arbitrary central coordinates. The original collection relations then give exactly the corresponding surjections. Thus the count is
$$
       (p-1)R\,p^{a+b+k+\ell}\,|\mathrm{SL}_2(\mathbb F_p)|.
$$
This yields the stated exact counting and decision hardness. The fixed-target epimorphism results here concern finite presentations or succinct permutation-generator inputs. Grochow–Srivastava–Thakkar Open Questions 2 and 3(2) concern Cayley-table inputs, for which the same source would have exponentially many entries. [Grochow–Srivastava–Thakkar, §7](https://arxiv.org/html/2609.07429v1#S7)
