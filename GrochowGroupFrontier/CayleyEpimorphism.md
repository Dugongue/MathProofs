# Polynomial-time epimorphism testing onto Fitting-free groups

Inputs are complete Cayley tables unless specified otherwise. Count distinct surjective homomorphisms as functions. The proofs are informal.

**Main theorem.** For an arbitrary finite source group $G$ and a finite Fitting-free target group $H$, deterministic polynomial time in the Cayley-table lengths suffices to test for an epimorphism, construct one, and count all of them. In fact one can enumerate all normal subgroups $N\unlhd G$ for which $G/N$ is Fitting-free in polynomial time. There are at most $|G/\operatorname{Rad}(G)|$ such subgroups. This gives an affirmative answer to Grochow–Srivastava–Thakkar Open Question 3(1), with no restriction on the source. [Published formulation, §7](https://drops.dagstuhl.de/storage/00lipics/lipics-vol374-icalp2026/html/LIPIcs.ICALP.2026.104/LIPIcs.ICALP.2026.104.html#S7)

## The Fitting-free quotient algorithm

A finite group is Fitting-free when it has no nontrivial abelian normal subgroup. Equivalently, its solvable radical is trivial. A nontrivial solvable normal subgroup would give a nontrivial abelian normal subgroup by taking its last nontrivial derived subgroup. Any epimorphism to a Fitting-free group kills the solvable radical of the source, since its image is solvable and normal. The quotient by the radical is Fitting-free, since an extension of a solvable group by a solvable group is solvable.

We maintain a Fitting-free quotient $Q$ of $G$, with a list of distinct marked minimal nontrivial normal subgroups $T_i$ of $Q$. A mark requires the desired quotient map out of $Q$ to be injective on $T_i$. Begin with $Q=G/\operatorname{Rad}(G)$ and no marks. Keep the quotient map from $G$ to every current $Q$ so that each output kernel is a subgroup of the original source.

Distinct minimal normal subgroups of a group have trivial intersection and commute, because their commutator subgroup is contained in their intersection. A minimal normal subgroup of a finite Fitting-free group is a direct power of a nonabelian simple group. For the latter standard fact, the minimal normal subgroup is characteristically simple. Choose a minimal nontrivial normal subgroup of that subgroup, and take all its images under the automorphism group of the characteristically simple subgroup. They generate the whole subgroup and commute pairwise if distinct. If the chosen subgroup is abelian their product is abelian, which is excluded here. If it is nonabelian, its center is a proper characteristic subgroup and hence trivial by minimality. The commuting product is then direct, and the chosen subgroup is simple since every normal subgroup of a direct factor is normal in the product. Consequently every product $R$ of marked minimal normals here is a direct product of centerless groups with trivial solvable radical. In particular $R$ is centerless and has trivial solvable radical.

Choose an unmarked minimal nontrivial normal subgroup $T$ of $Q$, if one exists. Every normal kernel either contains $T$ or intersects it trivially. Explore two branches.

1. **Keep $T$.** Append $T$ to the marks. This represents precisely the eligible kernels intersecting $T$ trivially.
2. **Kill $T$.** Pass first to $Q/T$, then quotient by its solvable radical. This represents precisely the eligible Fitting-free quotient kernels containing $T$. The marked groups survive both quotients: $T$ centralizes $R$ and $T\cap R\subseteq Z(R)=1$. The image of $R$ in $Q/T$ is therefore isomorphic to $R$. Its intersection with the solvable radical is solvable and normal in that image, hence trivial. Finally each marked group's image remains minimal normal under either quotient. For a normal subgroup inside such an image, pulling back along the isomorphism restricted to the marked group gives a $Q$-normal subgroup of the original minimal normal group.

When no unmarked minimal normal remains, the marked product $R$ is the socle. Any allowed kernel $N$ centralizes it: for every marked $T_i$ we have $[N,T_i]\le N\cap T_i=1$. The centralizer $C_Q(R)$ is normal in $Q$. If nontrivial it would contain a minimal nontrivial $Q$-normal subgroup, hence one inside $R$. This is impossible since $C_Q(R)\cap R=Z(R)=1$. Thus $N=1$ and the accumulated map from $G$ to the current $Q$ is the sole eligible quotient at this leaf, up to target isomorphism. The trivial group obeys the same argument. Induction on the branch tree now shows that the branch choices partition all Fitting-free quotient kernels, with exactly one output per leaf.

At any node charge the ratio $|Q|/|R|$, an integer. The keep branch multiplies $|R|$ by $|T|\ge 2$ with $|Q|$ fixed. The kill branch decreases $|Q|$ by a factor at least $|T|$ while preserving $|R|$. The ratio at each child is therefore at most half the parent ratio. Depth is at most $\lfloor\log_2 |G/\operatorname{Rad}(G)|\rfloor$, so the entire binary tree has at most $2|G/\operatorname{Rad}(G)|-1$ nodes and at most $|G/\operatorname{Rad}(G)|$ leaves. Thus mixing chief factors from several socle layers fits in a polynomial computation.

All node operations use the actual group table. The normal closure of one element is constructed by generating the subgroup from its conjugates. Solvability is tested by repeated derived subgroups. The radical is the product of the solvable normal closures of individual elements. A product of two solvable normal subgroups is again solvable and normal, while the normal closure of any element of the radical is contained in the radical. Running the solvability test on all single-element normal closures therefore recovers the radical. List the distinct nontrivial single-element normal closures and keep the inclusion-minimal ones to get precisely the minimal nontrivial normal subgroups. Each minimal normal subgroup contains an element whose normal closure equals that subgroup. Group generation, subgroup comparisons, image maps and quotients work by table scans of polynomial size. The algorithm consequently enumerates the kernels in deterministic time polynomial in $|G|$.

For each output $N$, test $G/N\cong H$ by the Babai–Codenotti–Qiao Cayley-table isomorphism algorithm for Fitting-free groups. Composing an isomorphism with the quotient map gives a witness. For exact counting, that isomorphism algorithm represents isomorphisms respecting two specified socle diagonals by a coset of a permutation group. Fix one source diagonal and try each of its possible images, at most $|\operatorname{Soc}(H)|^2$ by the diagonal bound in that paper. Each isomorphism belongs to exactly one of these cosets, according to the diagonal image. Their representatives and orders can be recovered in polynomial time using the coset representations and permutation-group algorithms. This gives the number of isomorphisms from each $G/N$ to $H$, or equivalently one computes $|\operatorname{Aut}(H)|$ once and multiplies by the number of kernels with quotient isomorphic to $H$. This counts distinct epimorphisms because an epimorphism uniquely determines its kernel and the resulting isomorphism. Counts use polynomially many bits, since there are at most $|H|^{|G|}$ functions in total. [Babai–Codenotti–Qiao, Theorem 1 and §§3, 5.3](https://people.cs.uchicago.edu/~laci/papers/icalp12.pdf)

Grochow–Srivastava–Thakkar proved the polynomial result when the source has no abelian composition factors or when the target is Fitting-free and the source has sufficiently small abelian width. The quotient enumeration above also covers source groups and intermediate quotients with arbitrary abelian width. [Theorem 6 and Corollary 15 in the proceedings](https://drops.dagstuhl.de/storage/00lipics/lipics-vol374-icalp2026/html/LIPIcs.ICALP.2026.104/LIPIcs.ICALP.2026.104.html#S6) · [Theorem 5 and Corollary 2 in the arXiv version](https://arxiv.org/html/2609.07429v1#S6)

## Other Cayley-table target classes


**Theorem 1.** For arbitrary finite groups $G,H$ with target order $|H|\le k$, decision, witness search and exact counting of epimorphisms take deterministic time $(|G|+|H|)^{O(1+\log k)}$. This answers the constant-size-target clause of Grochow–Srivastava–Thakkar Open Question 3(2) affirmatively. For a solvable target $H$, let $R$ be the sum of the minimum generator numbers of the abelian derived-series factors of $H$. Exact epimorphism enumeration from an arbitrary finite $G$ takes time $(|G|+|H|)^{R+O(1)}$. In particular this solves decision, search and counting in polynomial time for $k$-generated finite nilpotent targets of class at most $c$, for every fixed $k,c$, allowing arbitrary primes and exponent.

**Theorem 2.** For odd $p$, suppose both input groups are nonabelian central quotients of finite-field Heisenberg groups of arbitrary dimension and field degree, with optional elementary abelian direct factors. Epimorphism decision, search and exact counting are deterministic polynomial time. The class is recognizable from the raw Cayley tables. This treats the single-field Heisenberg-quotient portion of Grochow–Srivastava–Thakkar Open Question 3(3).

The published questions concern complete Cayley tables. In particular the constant-target result includes $D_8$, while the earlier hardness theorem uses finite presentations or permutation generators. [Grochow–Srivastava–Thakkar, Section 7](https://arxiv.org/html/2609.07429v1#S7) · [Elder–Shen–Weiß, Open Question 4.1](https://arxiv.org/html/2610.39487v1#S4)

## 1. Bounded target order

Find a generating list for $G$ greedily. Start from the trivial subgroup and adjoin any element outside the current subgroup, computing the generated subgroup from the table each time. Its size at least doubles, so the list has length at most $\log_2 |G|$. Enumerate all image tuples of that list in $H$. Propagate the assignment along generator edges in $G$ from the identity and reject any inconsistency. Check the homomorphism identity on all pairs and the surjectivity condition. Each accepted tuple gives a distinct epimorphism and every epimorphism is inspected. All checks per tuple are polynomial and there are $|H|^{\log_2|G|}\le |G|^{\log_2 k}$ tuples. Retaining one tuple gives search, and incrementing a binary counter gives exact counting.

## 2. A bound on the number of crossed homomorphisms

Let $Q$ be a finite group acting on a finite abelian group $A$ generated by at most $r$ elements. Write $Z^1(Q,A)$ for the group of maps $z:Q\to A$ satisfying $z(xy)=z(x)+x\cdot z(y)$. The subgroup $B^1$ consists of the maps $z(x)=a-x\cdot a$. We prove
$$
                         |Z^1(Q,A)|\le |A|\,|Q|^r.
$$

First assume that $A$ is a $p$-group. Restriction of $H^1=Z^1/B^1$ to a Sylow $p$-subgroup $P$ of $Q$ is injective. Indeed $z$ gives the affine action $x\star a=x\cdot a+z(x)$. If $z$ restricts to a member of $B^1(P,A)$, this action has a $P$-fixed point. Its $Q$-orbit has size dividing $[Q:P]$. Sum all orbit points in $A$ and divide by the orbit size, which acts invertibly on $A$. Since the action is affine, this average is $Q$-fixed. Therefore the original $z$ belongs to $B^1(Q,A)$.

Now a $p$-group $P$ has an index-$p$ normal subgroup $K$ unless trivial. The kernel of the restriction $H^1(P,A)\to H^1(K,A)$ is an image of $H^1(P/K,A^K)$. To see this directly, subtract a coboundary from a restriction-trivial class to make its representative vanish on $K$. The cocycle rule then makes it constant on the cosets of $K$ and gives values fixed by $K$. Thus it descends with coefficients in $A^K$. For a cyclic group $C_p=\langle t\rangle$ and module $B$, a cocycle is specified by its value $x$ at $t$, where $(1+t+\cdots+t^{p-1})x=0$, and coboundaries contribute $(t-1)B$. The quotient is killed by $p$, since $px=\sum_{i=0}^{p-1}(1-t^i)x\in (t-1)B$ on the norm kernel. If $B=A^K$, the norm kernel is a subgroup of a finite abelian $p$-group of rank at most $r$. Its quotient has rank at most $r$ and order at most $p^r$. Induction along index-$p$ subgroups gives $|H^1(P,A)|\le |P|^r$.

For arbitrary finite abelian $A$, its primary factors are invariant under the action. Multiply these bounds over all primes dividing $|A|$. The product of the Sylow group orders used is at most $|Q|$. Finally $|B^1(Q,A)|\le |A|$, proving the assertion.

The elementary rank fact used here follows by taking the $p$-torsion subgroup of an abelian $p$-group. The dimension of that subgroup equals the minimum generator number, so subgroups cannot increase rank. Quotients cannot increase the minimum generator number either. A finite abelian group has minimum generator number equal to the maximum of its primary generator numbers, by combining primary generators of coprime orders.

## 3. Lifting through the derived series

Let $H$ have derived length $d$. Any map to $H$ kills $G^{(d)}$, so first replace $G$ by the table of $G/G^{(d)}$. This substitution gives an exact bijection of epimorphisms. For the last nontrivial abelian layer put $A=H^{(d-1)}$ and $U=G^{(d-1)}$. In particular $U$ is abelian after the substitution. An epimorphism must induce epimorphisms
$$
             f:G/U\longrightarrow H/A,\qquad \alpha:U\longrightarrow A .
$$
Conversely any homomorphism lifting these two epimorphisms is surjective: its image contains $A$, and its image modulo $A$ is the full quotient.

Recurse to enumerate the epimorphisms $f$. Enumerate the homomorphisms $\alpha:U\to A$ using cyclic invariant-factor charts, then test onto. If $A$ is generated by $r$ elements, there are at most $|U|^r$ homomorphisms. For each cyclic factor $C_n$ of $U$ its image lies in $A[n]$, of size at most $n^r$. The admissible coordinates are obtained directly by divisibility in the cyclic factors. Count can be computed from the explicit list as well.

For a pair $f,\alpha$, choose sections for $Q=G/U$ and $H/A$ and compute their multiplication cocycles $c_G,c_H$ from the tables. Conjugation gives actions on $U,A$ of the respective quotients since both kernels are abelian. First test that $\alpha$ intertwines these actions via $f$. A lift then has the form
$$
 (u,x)\longmapsto (\alpha(u)+t(x),f(x))
$$
in section coordinates, where $t:Q\to A$ satisfies
$$
 t(x)+f(x)\cdot t(y)-t(xy)=\alpha(c_G(x,y))-c_H(f(x),f(y)).
$$
These equations are necessary and sufficient by expanding multiplication in the two groups. If solvable, solutions form a coset of $Z^1(Q,A)$, with the action via $f$. Expand in invariant factors of $A$ to obtain an integral linear congruence system. Add one integer slack variable per congruence to account for the modulus, then use Smith normal form to decide existence and produce one solution. The same computation gives generators of the homogeneous solution group by projecting the integral nullspace basis to the variables modulo their cyclic orders. Enumerate this finite subgroup from its generators by a queue and a balanced search tree keyed by coordinate tuples. Its size is at most $|A||Q|^r$ by Section 2. Smith normal form, quotient tables, and cocycle extraction cost polynomial time in the written tables. If the target quotient is trivial, its unique epi is used as the base of the recursion.

The number of choices of $\alpha$ and lifts per quotient epi is at most $|A|(|U||Q|)^r\le |A||G|^r$. Apply this bound at each layer. The orders of the target layers multiply to $|H|$, and their generator numbers sum to $R$. Every epi appears once, because its induced maps and its section adjustment determine it. The entire recursion and the output costs are at most $(|G|+|H|)^{R+O(1)}$.

If $H$ is $k$-generated and nilpotent of class at most $c$, its lower central factors $\gamma_i(H)/\gamma_{i+1}(H)$ are abelian and generated by at most $k^i$ left-normed commutators of length $i$. This follows inductively from commutator identities and additivity modulo the next lower central group. For any subgroup of $H$, intersect with the lower central series. Each resulting factor embeds in the corresponding abelian factor, so each subgroup has a generating set of size at most $\sum_{i=1}^c k^i$. The abelian derived factors of $H$ therefore have generator number bounded by the same quantity, and the derived length is at most $c$ for nontrivial $H$. Thus $R\le c\sum_{i=1}^c k^i$. This gives Theorem 1 for all such targets, with arbitrary source and no bound on the order or exponent of $H$.

## 4. Recognizing central quotients of finite-field Heisenberg groups

Let $F=\mathbb F_p$ with $p$ odd. In a class-two exponent-$p$ group write $V=G/Z(G)$, $W=[G,G]$, and let $b:V\times V\to W$ be the commutator. The source group can be written in additive coordinates on $V\oplus Z(G)$, with law
$$
 (v,z)(v',z')=(v+v',z+z'+b(v,v')/2).
$$
Indeed switching to $x+y=xy[y,x]^{1/2}$ gives its elementary abelian additive Lie ring. Choose a linear section of its center quotient. These coordinates and the bracket tables are computable in polynomial time from the Cayley table. Let $\mathcal A$ be the space of alternating scalar forms $\lambda b$ for $\lambda\in W^*$. Since the commutator values span $W$, this identifies the dual $W^*$ with $\mathcal A$.

For a nonzero finite field $K/F$, the bracket of a Heisenberg group $H_m(K)$ is the standard $K$-valued symplectic form on $K^{2m}$. On quotienting by a proper central additive subspace $L\subset K$, the scalar pencil consists of the forms $\operatorname{Tr}_{K/F}(a b)$ for $a$ in the trace-annihilator of $L$. Each such form with $a\ne0$ is nonsingular, and relative to any nonzero member the ratios act by multiplication by scalars in $K$. The additional elementary abelian direct factors in the theorem do not change the pencil.

Conversely, suppose all nonzero forms in $\mathcal A$ are nonsingular and, for some nonzero $\alpha_0\in\mathcal A$, the unital algebra $K_{\mathcal A}$ generated by the ratio space $\alpha_0^{-1}\mathcal A$ is a field. Every ratio is self-adjoint relative to $\alpha_0$ because both matrices are alternating. Commutativity makes all algebra elements self-adjoint. Thus $V$ is a vector space over $K_{\mathcal A}$ and $\alpha_0$ is balanced over the field. Define the $K_{\mathcal A}$-valued form $B$ by
$$
 \operatorname{Tr}_{K_{\mathcal A}/F}(tB(v,w))=\alpha_0(tv,w)
 \qquad (t\in K_{\mathcal A}).
$$
Nondegeneracy of the trace pairing gives uniqueness. The balance identity makes $B$ bilinear over $K_{\mathcal A}$. It is alternating since $\alpha_0(tv,v)=-\alpha_0(v,tv)=-\alpha_0(tv,v)$ and $p$ is odd. It is nonsingular because vanishing of $B(v,-)$ implies vanishing of $\alpha_0(v,-)$. Therefore $B$ is a symplectic form over $K_{\mathcal A}$. The original pencil consists of its traces with coefficients in the ratio space, so the dual bracket arises from the Heisenberg group over $K_{\mathcal A}$ by quotienting its center by the trace-annihilator of that space. The complement of $W$ in the original $Z(G)$ is an elementary abelian direct factor in the displayed group coordinates.

This supplies a raw recognizer. Test the group class and exponent and compute the center, derived group and elementary abelian quotient charts. Enumerate the $|W|$ forms to test nonsingularity, choose $\alpha_0$, and generate the ratio algebra by linear algebra on matrices. If the algebra is commutative and of dimension at most $\dim_F V$, enumerate its elements to test that every nonzero element is invertible. Rejection is correct if its dimension is larger, because a nonzero module over a field has dimension at least the field degree. Thus this check never enumerates more than $|V|$ elements. Testing class, exponent and all group coordinates can use the explicit input tables. This characterization uses the symplectic Heisenberg structure for the field case of genus one. [Brooksbank–Maglione–Wilson, Section 3](https://arxiv.org/html/1508.03033#S3)

## 5. Matching pencils for Heisenberg quotient epimorphisms

Suppose $G,H$ are nonabelian and pass the recognition tests. Write $V_G,V_H,W_G,W_H$ for their spaces above and $\mathcal A,\mathcal B$ for their pencils. A surjection gives an onto map $h:W_G\to W_H$. It also induces an onto map $g:V_G\to V_H$ because centers map into centers. If $v\in\ker g$, then every scalar form $(h^*\lambda)b_G$ vanishes on $(v,w)$ for all $w$. A nonzero $\lambda\in W_H^*$ has nonzero pullback, and that form is nonsingular, so $v=0$. Thus the tangent map is invertible. Its pullback $g^*\mathcal B$ is contained in $\mathcal A$, and $h$ is uniquely determined by that inclusion and $g$. Conversely an invertible tangent map with this property yields the corresponding onto $h$ and preserves the bracket. It extends to an epimorphism if and only if
$$
       \dim_F Z(G)/W_G\ \ge\ \dim_F Z(H)/W_H.
$$
Indeed its action on the remaining central degrees of freedom may be any lift of a surjection between these elementary abelian spaces. The displayed group law verifies every such extension as well as arbitrary linear center shears of the tangent.

After checking dimensions, fix a nonzero $\beta_0$ in the target pencil. Enumerate all nonzero $\alpha_0$ in the source pencil as candidates for $g^*\beta_0$. There are at most $|W_G|$ candidates. Compute the associated ratio fields $K_{\mathcal A},K_{\mathcal B}$, as well as the ratio spaces. Any desired $g$ transports the target ratio space into the source ratio space by conjugation $D\mapsto g^{-1}Dg$, hence extends uniquely to an $F$-field embedding $\iota:K_{\mathcal B}\to K_{\mathcal A}$. Enumerate all these embeddings by finding a field generator and testing its images in the source field. Field elements can be enumerated since both field orders are bounded by the tangent-space orders. Retain an embedding exactly when it carries the target ratio space into the source ratio space.

Every retained embedding works. Regard the source tangent as a $K_{\mathcal B}$-vector space via $\iota$ and the target in its native $K_{\mathcal B}$ coordinates. Both $\alpha_0,\beta_0$ lift by trace over $K_{\mathcal B}$ to nonsingular alternating forms, and their dimensions agree. They therefore have a $K_{\mathcal B}$-linear isometry. It pulls back $\beta_0$ to $\alpha_0$ and intertwines every ratio under $\iota$, giving the required pencil inclusion. A symplectic basis construction produces that isometry. Conversely any allowed tangent map occurs in its own unique branch $(\alpha_0,\iota)$, since the ratios generate the field. This proves decision and search in polynomial time.

For counting, in each retained branch the tangent isometries form a torsor under $\operatorname{Sp}_{2m}(\mathbb F_q)$, where $q=|K_{\mathcal B}|$, $2m=\dim_{K_{\mathcal B}}V_H$. The order is $q^{m^2}\prod_{j=1}^m(q^{2j}-1)$, by counting ordered symplectic bases. The number of full lifts for each tangent isometry is
$$
 p^{\,\dim_F V_G\dim_F Z(H)+a\dim_F W_H}
       \prod_{j=0}^{b-1}(p^a-p^j),\qquad
 a=\dim_F Z(G)/W_G,\quad b=\dim_F Z(H)/W_H.
$$
The factors count all tangent-to-center shears, all lifts of the central quotient map into $Z(H)$, and the surjective central quotient maps. Sum over branches. These integers have polynomial bit length since all counted maps are functions between explicit tables. For an abelian target of exponent $p$ one can directly count onto linear maps from the abelianization. Thus the algorithm also handles abelian targets of the same exponent without the nonsingular-pencil hypothesis.
