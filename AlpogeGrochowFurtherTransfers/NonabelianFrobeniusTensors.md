# Nonabelian multiplication tensors from correlated Frobenius reductions

Let $A,B$ be finite étale $\mathbb Q$-algebras given by multiplication tables, of common dimension $n$. Fix full-rank orders $\mathcal O_A,\mathcal O_B$ and let $D$ be the product of their absolute order discriminants. An exceptional product $B_0$ will always be a positive multiple of $D$. A prime will be called admissible when it does not divide $B_0$. A positive absolute constant in the bounds below can be made effective.

The three results use the same degree-one prime estimate. It comes from Alpöge's primitive Dirichlet zero-location endpoint for abelian fields. The estimates for other number fields use Dedekind RH for the explicitly indicated fields. The criterion in Part 1 also gives examples with nonabelian field factors that use only the Dirichlet endpoint.

**1. Unmarked comparison and a Dirichlet-only nonabelian class.** Form the three rational étale algebras $A\otimes A$, $B\otimes B$, and $A\otimes B$. Write $r_E$ for the signed multiplicity of an isomorphism type of field $E$ in the first two minus twice the third. Set
$$
 S=\sum_{E\ne\mathbb Q}|r_E|\log |d_E|,\qquad \kappa=\sum_E r_E.
$$
Here $d_E$ is the field discriminant. Assume Dirichlet GRH and Dedekind RH only for the nonabelian fields with $r_E\ne 0$. The permutation characters of $A,B$ are equal if and only if the numbers of linear factors in their reductions agree at every admissible prime through
$$
 C\bigl(4+(S/\kappa)^2+(S/\kappa)\log(2B_0)\bigr)                 \tag{1}
$$
when $\kappa>0$. The case $\kappa=0$ gives character equality outright. An input-data bound which needs no preliminary computation of $\kappa$ or of maximal orders is $C n^2\log^2(2B_0)$. Equal characters imply equality of the full unmarked reduction tensor orbits at all admissible primes. If the square of the character difference factors through the abelianization of its common normal closure, Dirichlet GRH alone gives an admissible witness prime whenever the characters differ, with an explicit Fourier-dependent bound. This applies to the nonabelian $D_8\times C_2$ example below even though the character difference itself does not factor through the abelianization.

**2. Exact dimension-free test for arbitrary normal field factors.** Suppose every constituent field is Galois over $\mathbb Q$. Retain the primitive rational component marks across primes. For each field factor, record its degree and whether it splits completely at each admissible prime through $C\log^2(2B_0)$. Equality of the multisets of marked profiles is equivalent to rational multiplication-tensor isomorphism. The only additional zero hypothesis is Dedekind RH for the nonabelian input fields and their pairwise composita. The pairwise compositum of two fields of degree $m$ has degree at most $m^2$. Neither the composita nor their discriminants are needed to run the scan.

**3. Exact comparison of arbitrary factors via correlated lifts.** Supply a common Galois splitting field $K/\mathbb Q$, a $G$-stable order $\mathcal O_K'$ with $G=\operatorname{Gal}(K/\mathbb Q)$, and the action of $G$ on the order by matrices. Now take $B_0$ to be a multiple of $D$ and of $|\operatorname{disc}\mathcal O_K'|$. Assume Dirichlet GRH and Dedekind RH for each nonabelian field $K^U$ with $U\le G$ cyclic, including $U=\{1\}$. There is a common catalogue with one admissible rational prime through $C\log^2(2B_0)$ per conjugacy class of cyclic subgroups. Each selected prime is used with its primes above it in $K$. Joint fixed-point counts from these residue Frobenii give an exact multiplication-tensor orbit test without retaining rational field-factor marks. It suffices to test the stabilizer types present in the two inputs, with at most $\lfloor\log_2|H|\rfloor$ Frobenius tests in any simultaneous query for a nontrivial stabilizer $H$. The test constructs a rational algebra isomorphism when one exists and counts all such isomorphisms. Construction and testing take polynomial bit time in the sizes of the multiplication tables and the supplied Galois model, including its explicit matrices.

These results describe arithmetic certificates for a subfamily of the three-tensor problem studied by Grochow and Qiao. The anchored method charges for the supplied splitting field. [Grochow–Qiao, *On the Complexity of Isomorphism Problems for Tensors, Groups, and Polynomials I*](https://doi.org/10.1137/21M1441110)

## 1. Tensor transport and the residue statistic

For commutative unital algebras, an ordinary multiplication-tensor transporter is a triple $P,Q,R$ of linear bijections with $R(xy)=P(x)Q(y)$. Put $a=P(1)$ and $b=Q(1)$. The identities $R(x)=P(x)b=aQ(x)$ make multiplication by $a$ and $b$ bijective, so $a,b$ are units. Therefore
$$
 \varphi(x)=(ab)^{-1}R(x)
$$
is a unital algebra isomorphism. Conversely the three maps $a\varphi,b\varphi,ab\varphi$ give a transporter for every two units. In particular any algorithm that produces $\varphi$ produces an ordinary three-mode transporter.

A rational multiplication table gives an order in polynomial bit time. Compute its unit, choose a common denominator $M$ for the structure constants in the input basis $(e_i)$, and take the lattice generated by $1,Me_1,\ldots,Me_n$. It is multiplicatively closed. Hermite normal form gives a basis, and the determinant of the multiplication trace Gram matrix gives the discriminant. The index-square formula compares this order with the product of maximal orders. The product trace Gram form splits orthogonally over field factors. The nondegeneracy of each field trace pairing is the case $\sigma=\mathrm{id},J=(1)$ of the release's **traceGram_det_ne_zero**.

At an admissible prime the order reduces to a finite étale $\mathbb F_p$-algebra $S_p$. Write $\ell_A(p)$ for the number of degree-one field factors. If $v_1,\ldots,v_n$ is an $\mathbb F_p$-basis, then
$$
 \ell_A(p)=n-\operatorname{rank}[v_i(v_j^p-v_j)]_{i,j}.
$$
Indeed the columns span the ideal generated by all $z^p-z$, and this ideal is zero in a degree-one factor and is the whole field in any larger factor. Repeated squaring evaluates Frobenius without factoring a polynomial over $\mathbb F_p$.

Let $K$ contain the images of all embeddings of $A$ and $B$. A prime admissible for the orders is unramified in the compositum of their normal closures. This follows by embedding each unramified local factor, and each of its conjugates, into the maximal unramified extension of $\mathbb Q_p$. For a finite Galois $K/\mathbb Q$ where $p$ is unramified, let $X=\operatorname{Hom}_{\mathbb Q}(A,K)$ and $Y=\operatorname{Hom}_{\mathbb Q}(B,K)$, with the action by postcomposition. If $g$ is any Frobenius above $p$, then $\ell_A(p)=|X^g|$. The cycles of $g$ give all the residue degrees. Since the number fixed by each power determines each cycle count by divisor inversion, equality of the permutation characters gives equality of the unmarked multiplication tensors at all these primes.

## 2. The smoothed degree-one estimate

Fix a nonnegative $C^2$ function $w$ supported on $[1/2,1]$ and positive on its interior, and put $I=\int_0^\infty w(t)\,dt>0$. A polynomial bump with a zero of order three at each endpoint suffices. For any number field $E$ of degree $e$, set
$$
 P_E(x;B_0)=\sum_{p\nmid B_0}\ell_E(p)\log p\,w(p/x).
$$
In applications the primes under consideration are unramified in $E$. Assuming RH for $\zeta_E$, the estimate is
$$
 P_E(x;B_0)
 = Ix+O_w\bigl(\sqrt x(\log |d_E|+e)+e\log(2B_0)\bigr),\qquad x\ge 4.       \tag{2}
$$

Here is the uniform error calculation. Apply the smoothed explicit formula for $-\zeta_E'/\zeta_E$ to ideal norms. The pole at $1$ gives $Ix$. The Mellin transform of $w$ on the critical line is $O_w((1+|t|)^{-2})$ by two integrations by parts. The number of zeros with imaginary part in a unit interval at height $T$ is $O(\log |d_E|+e\log(3+|T|))$. Under RH their aggregate contribution is $O_w(\sqrt x(\log |d_E|+e))$. The zeros from the archimedean factors, including a possible zero at $0$, contribute $O_w(e)$ since $x\ge 4$ and the weight is supported away from zero. For a rational prime $p$ and an exponent $a\ge2$, the sum of $\log N\mathfrak p$ over all powers $\mathfrak p^j$ of norm $p^a$ is at most $e\log p$. The prime powers thus contribute $O(e\sqrt x)$ by $\sum_{a\ge2}\vartheta(x^{1/a})\ll\sqrt x$. Finally each deleted degree-one prime costs at most $e\|w\|_\infty\log p$, giving the displayed exceptional-prime error. All analytic constants are uniform and effective. [Grenié–Molteni, *Explicit smoothed prime ideals theorems under GRH*](https://arxiv.org/abs/1312.4465)

For an abelian field $E/\mathbb Q$, $\zeta_E$ factors as primitive Dirichlet $L$-functions, with the inducing primitive character used for each quotient character. Thus the zero-location input to (2) for these fields is precisely **LFunction_eq_zero_re_of_isPrimitive** in the release's **Main.lean**, with the usual treatment of the trivial character at the pole of $\zeta$. The companion theorem **LFunction_ne_zero_of_half_lt_re** supplies the corresponding right-half nonvanishing statement. For a nonabelian $E$ this proof uses separately stated Dedekind RH for $\zeta_E$.

## 3. Tensor-square amplification without a Galois closure in the estimate

Let $h=\chi_X-\chi_Y$. Cartesian products of the embedding sets correspond to tensor products of their rational algebras. Consequently the pointwise square is
$$
 h^2=\chi_{X\times X}+\chi_{Y\times Y}-2\chi_{X\times Y}
     =\sum_E r_E\chi_E.
$$
A field embedding set is transitive, so its character has mean one. Hence $\kappa=\frac{1}{|G|}\sum_{g\in G}h(g)^2$. This is a nonnegative integer, and is zero exactly in the equal-character case. The identity evaluation gives $\sum_E r_E[E : \mathbb Q]=h(1)^2=0$.

Minkowski's discriminant bound gives $[E : \mathbb Q]\ll\log |d_E|$ for $E\ne\mathbb Q$. For example, the factor $e^e/e!$ in the square root of the bound is at least $2^{\lfloor e/2\rfloor}$, and the complex-place factor $(\pi/4)^{r_2}$ changes the exponential base to another absolute base above one. The finitely many smallest degrees can be bounded directly. The dimension cancellation now controls the total dimension with absolute multiplicities:
$$
 |r_{\mathbb Q}|+\sum_{E\ne\mathbb Q}|r_E|[E : \mathbb Q]\ll S.
$$
Apply (2) to the nonzero signed field terms. For $p$ admissible, the result is
$$
 \sum_{p\nmid B_0}(\ell_A(p)-\ell_B(p))^2\log p\,w(p/x)
 =I\kappa x+O_w\bigl(S\sqrt x+S\log(2B_0)\bigr).                  \tag{3}
$$
When $\kappa>0$, the quantity in (1) is large enough to leave at least $I\kappa x/2$ on the left of (3). Since $|\ell_A-\ell_B|\le n$, there are $\gg_w \kappa x/(n^2\log x)$ prime witnesses in $(x/2,x)$. All three tensor product algebras have degree $n^2$. The Gram matrices for the tensor product orders are Kronecker products, so
$$
 S\le \log |\operatorname{disc}(\mathcal O_A^{\otimes2})|
   +\log |\operatorname{disc}(\mathcal O_B^{\otimes2})|
   +2\log |\operatorname{disc}(\mathcal O_A\otimes\mathcal O_B)|
 =4n\log D.
$$
This uses the index-square formula for every product of fields. These bounds give (1) and the input-data cutoff. A character mismatch witnessed at a good prime is unconditional, and the zero hypotheses bound the search for a witness.

For the Dirichlet-only case take $K$ to be the joint normal closure, so the action on $X\sqcup Y$ is faithful. Put $G_{\rm ab}=G/[G,G]$. Suppose $f=h^2$ is inflated from $G_{\rm ab}$. Write $f=\sum_\xi c_\xi\xi$ over the characters of $G_{\rm ab}$, with $c_1=\kappa$ and $L=\sum_\xi|c_\xi|$. The conductors $q_\xi$ of the primitive Dirichlet characters divide the product $|d_A d_B|$ of field-algebra discriminants. To see this, use the local Artin conductor formula as a nonnegative weighted sum of codimensions of ramification-group invariants. Whenever a ramification subgroup acts nontrivially on a one-dimensional $\xi$, it acts nontrivially on the faithful permutation representation $\mathbb C[X\sqcup Y]$, whose corresponding codimension is at least one. The conductor–discriminant formula for permutation representations turns this termwise inequality into the asserted divisibility.

For each primitive Dirichlet character the same Mellin calculation as in (2), with zero count $O(\log(2q_\xi(3+|T|)))$, gives an error $O_w(\sqrt x\log(2q_\xi)+\log(2B_0))$ and contributes the main term only for $\xi=1$. Put $W=\sum_\xi|c_\xi|\log(2q_\xi)$. Summing gives a witness bound
$$
 C\bigl(4+(W/\kappa)^2+(L/\kappa)\log(2B_0)\bigr).                 \tag{4}
$$
Since $f\ge0$, each $|c_\xi|\le\kappa$. In particular $C|G_{\rm ab}|^2\log^2(2B_0)$ is a coarser bound even without the Fourier weights. This argument uses no nonabelian Dedekind zero input.

For a concrete example let $G=D_8\times C_2$, with $D_8$ the dihedral group of order eight and $C_2=\{1,t\}$. Write $Z=\{1,z\}$ for the center of $D_8$. Take the difference of the two positive finite $G$-sets defined by the positive and negative terms of
$$
 ([D_8/\{1\}]-[D_8/Z])\boxtimes([C_2/\{1\}]-2[C_2/C_2]).
$$
The resulting character is $-8$ at $(1,t)$, $+8$ at $(z,t)$, and zero elsewhere. It is nonabelian, but its square is $64$ on the single coset $Z\times\{t\}$ and zero elsewhere. The two positive sets each have size $24$. The example is realized over $\mathbb Q$ by the splitting field of $x^4-2$ composed with $\mathbb Q(\sqrt5)$: the quartic splitting field has the displayed dihedral group, has quadratic subfields $\mathbb Q(i),\mathbb Q(\sqrt2),\mathbb Q(\sqrt{-2})$, and is disjoint from $\mathbb Q(\sqrt5)$. The two finite $G$-sets give products of fixed fields. They have different Frobenius records at any prime whose abelianized Frobenius lies in that coset. Formula (4) yields the dimension-free logarithmic-square bound for this comparison using only the Dirichlet endpoint.

## 4. Exact field matching with a dimension-free bound

Two normal fields of the same degree $m$ inside the common closure are isomorphic precisely when equal, since every $\mathbb Q$-embedding of a normal field into the algebraic closure has that field as its image. Let $E\ne F$ be distinct such fields. Put $J=EF$, $s=[E\cap F : \mathbb Q]$ and $e=[J : \mathbb Q]=m^2/s$. Their transitive permutation characters have the values $m$ on the normal stabilizers and zero off them. Thus
$$
 (\chi_E-\chi_F)^2=m\chi_E+m\chi_F-2s\chi_J,\qquad
 \kappa=2m-2s\ge m.
$$
Here $s\le m/2$ because $[E:E\cap F]\ge2$. The product $E\otimes F$ is the product of $s$ copies of $J$: the product embedding set has $s$ orbits and each stabilizer is the intersection of the two normal stabilizers. Applying the index-square formula to the tensor product of maximal orders yields
$$
 s\log|d_J|\le m\log|d_E|+m\log|d_F|.
$$
The $S$ in (3) is therefore at most $3m(\log|d_E|+\log|d_F|)$. This controls both the explicit-formula error and the excluded-prime contribution in (3), since the total absolute signed degree is $O(S)$. With $\kappa\ge m$ and both field discriminants dividing $B_0$, the bound (1) is at most $C\log^2(2B_0)$ after enlargement of the absolute constant. At any prime witnessing the discrepancy, exactly one of the fields splits completely.

To apply the pairwise argument to a product, get its primitive rational idempotents by deterministic rational étale algebra decomposition. Each projected order lies in the corresponding field, and the index of the original order in the product of its projected orders is prime to admissible primes by the index-square formula. The local component marks thus reduce faithfully. Compute each split bit by asking if Frobenius is the identity on that component. Compare the multisets of degrees and profiles. Different canonical field types of the same degree have different profiles by the two-field argument, and isomorphic fields give the same reductions at every admissible prime. Only the component degrees and the rational orders are needed for the scan. [Lenstra–Silverberg, *Algorithms for commutative algebras over the rational numbers*](https://arxiv.org/abs/1509.08843)

## 5. Realizing subgroup generators by the same prime estimate

Write $d=|G|$, and let $H\le G$ be a cyclic subgroup of order $m$. The following class function vanishes away from elements whose generated subgroup is conjugate to $H$:
$$
 \Phi_H(g)=\sum_{U\le H}|U|\mu([H:U])\chi_{G/U}(g)
          = |N_G(H)|\,\mathbf 1_{\langle g\rangle\sim H}.           \tag{5}
$$
Indeed $|U|\chi_{G/U}(g)=|\{a\in G:a^{-1}ga\in U\}|$. Fix $a$. The sum of $\mu([H:U])$ over subgroups $U$ containing $a^{-1}ga$ is one if $\langle a^{-1}ga\rangle=H$ and zero otherwise by cyclic subgroup Möbius inversion. The choices of $a$ that conjugate the generated subgroup onto $H$, when they exist, form a coset of $N_G(H)$. This proves (5). The mean of $\Phi_H$ is $\sum_{U\le H}|U|\mu([H:U])=\varphi(m)$, also for $m=1$.

Each summand in (5) is the permutation character of the field $K^U$, times a signed coefficient. The discriminant tower formula gives $|U|\log|d_{K^U}|\le\log|d_K|$ and $|U|[K^U : \mathbb Q]=d$. Apply (2) to the summands. There are $2^{\omega(m)}$ squarefree quotients and $2^{\omega(m)}/\varphi(m)\le2$: each prime contributes $2/(p^{a-1}(p-1))$ to the ratio. The prime $2$ contributes at most $2$, and each other prime contributes at most $1$. After division by $\varphi(m)$ the weighted sum has main term $Ix$ and error bounded by
$$
 O_w\bigl(\sqrt x(\log|d_K|+d)+d\log(2B_0)\bigr).
$$
For $d>1$, Minkowski controls $d$ by $\log|d_K|$, which is at most $\log B_0$. When $d=1$ the group is trivial and (2) itself suffices. Thus every cyclic subgroup class is realized by an admissible prime through $C\log^2(2B_0)$. This gives the needed generator-class bound using only zeta functions of cyclic fixed fields. Any generator of the indicated cyclic subgroup will impose the same fixed-point test.

## 6. Alignment across primes and recovery of the tensor orbit

Let $q$ be a prime of $\mathcal O_K'$ over an admissible prime $p$, and let $k_q$ be its residue field. Every homomorphism $x\in X$ reduces to a map $\overline x_q : \mathcal O_A/p\mathcal O_A\longrightarrow k_q$. One may work in the full ring of integers locally at $p$ since the order index is prime to $p$. The reduction is a bijective labeling of all the finite-algebra homomorphisms. In fact, if $e_j$ is an integral basis of the order of $A$, put $M_{x,j}=x(e_j)$. The separable trace formula gives
$$
 M^{\mathsf T}M=[\operatorname{Tr}_{A/\mathbb Q}(e_ie_j)]_{i,j},
 \qquad \det(M)^2=\operatorname{disc}(\mathcal O_A).
$$
The determinant is invertible modulo $q$ at an admissible prime. The evaluation map after base change to $k_q$ is therefore a bijective algebra map onto $k_q^X$, whose coordinate projections are precisely the homomorphisms. This uses the same trace Gram form as in Section 1 and identifies a labeled set of residue maps canonically from the chosen global labels.

The arithmetic Frobenius $g_q$ is the unique element of $G$ with $g_q(a)\equiv a^p\bmod q$ on the order basis. The equality on the basis extends by $\mathbb F_p$-linearity and implies preservation of $q$. Unramifiedness then gives uniqueness. Under the bijective labeling, the residue map $\overline x_q\mapsto (\overline x_q)^p$ is the permutation $x\mapsto g_qx$. Varying $q$ above $p$ gives its conjugates. Thus a prime in the class from (5) gives a Frobenius permutation for a generator of each cyclic subgroup in the conjugacy class. All these permutations act on the same labels $X$, and the same construction is made separately on $Y$.

Given a subgroup $H=\langle g_1,\ldots,g_r\rangle$, use a lifted prime whose Frobenius generates $\langle g_i\rangle$ for each $i$. The number of labels fixed by all these residue permutations is exactly $\phi_H(X)=|X^H|$. A subgroup can be generated by at most $\lfloor\log_2|H|\rfloor$ elements since every strict step in a greedy generation at least doubles the order. The subgroup $1$ corresponds to the empty query. Reusing a rational prime with different $q$ is allowed. Independent relabelings between primes would destroy this joint fixed-point count.

Write $X=\coprod_L m_L(G/L)$ with one representative for each stabilizer conjugacy type. The term $\phi_H(G/L)$ vanishes unless $H$ is contained in a conjugate of $L$, and the self-term is $|N_G(H):H|>0$. If positive multiplicities for $X$ and $Y$ differ anywhere, choose a maximal differing type under subconjugacy. Its mark differs, because larger differing types are absent. Thus testing the stabilizer types present in the two inputs gives equality of all multiplicities, and hence equality of the rational tensor orbits. This comparison uses the subgroup marks of the Frobenius permutations. It applies even when every separate prime has identical cycle types.

Here are explicit algorithms for the needed labels, computation, and witness. The order and rational matrix model give $G$ as a list of automorphisms. Obtain the labeling set $X$ by decomposing the rational algebra $K\otimes A$ into primitive idempotents $\epsilon_x$. Each corresponding factor is a copy of $K$. For a basis element $a\in A$, solve
$$
 (1\otimes a)\epsilon_x=(x(a)\otimes1)\epsilon_x
$$
for the element $x(a)\in K$. Reduction in $k_q$ is allowed on the images of the order since their denominators in the order of $K$ are prime to $p$. The catalog is found by enumerating the primes through the cutoff, computing the finite étale factors of the order reduction and comparing the congruences above with the supplied automorphism matrices. Over $\mathbb F_p$ the factors of a finite étale algebra can be separated by computing the algebra fixed by Frobenius and successively splitting with the kernels of multiplication by $a-c$ for $c\in\mathbb F_p$ on its factors, for each basis element $a$ of that fixed algebra. Iterating these splits distinguishes the factors since the fixed algebra is the product of one copy of $\mathbb F_p$ per field. This costs polynomial time in $p$ and the dimensions, and the bound on $p$ is polynomial in the input length. Orders, tensor products, discriminants, exact factoring over $\mathbb Q$ of a finite étale algebra, and all linear solves have polynomial bit complexity. The same matrix model permits all subgroup generation and conjugacy comparisons in polynomial time in the explicit list size.

The catalog permutations also recover every point stabilizer by testing, for each $g\in G$, the fixed set for the available generator of its cyclic subgroup. They generate the action since the cyclic generator for each group element generates that element. Match orbits of the same types. In a match of type $H$, choose representatives with exactly the same stabilizer (subgroup conjugacy and a translate supply this) and send each of their translates to the corresponding translate. This yields a $G$-equivariant bijection of the coordinate labels. The latter is a $G$-equivariant algebra isomorphism of the split algebras, which descends to $A\cong B$: the split coordinate algebras have the semilinear action combining the permutation of the labels and the action on $K$, and their invariants are the displayed rational algebras. On $m_H$ orbits of type $H$, the number of bijections is $m_H!|N_G(H):H|^{m_H}$. Multiplying over types counts all algebra isomorphisms. The two-unit formula of Section 1 describes the resulting full family of ordinary tensor transporters.

## 7. A nonabelian collision resolved by two simultaneous tests

Let $G=\operatorname{GL}_3(\mathbb F_2)$ act on the seven one-dimensional subspaces and the seven two-dimensional subspaces. The former correspond to nonzero vectors. The latter correspond to kernels of nonzero linear functionals. For every $g\in G$ the fixed-point counts are equal by
$$
 \operatorname{rank}(g-I)=\operatorname{rank}(g^{\mathsf T}-I).
$$
In particular the individual permutations also have equal cycle types by evaluating powers. Take
$$
 g_1=I+E_{12},\qquad g_2=I+E_{13}.
$$
The vectors fixed by both lie in the span of the first standard vector, so the joint mark on points is one. A linear functional fixed by both vanishes on that vector, so the joint mark on planes is three. The two actions are inequivalent, and a single two-generator joint query distinguishes their fixed-field multiplication tensors in a common Galois model with this group. Classical septic Gassmann pairs provide real number-field instances of these two actions. [Mantilla-Soler, *On a question of Perlis and Stuart regarding arithmetic equivalence*](https://nyjm.albany.edu/j/2019/25-25p.pdf)

There is also an exact bound on what any uniformly shorter collection of simultaneous fixed constraints can recover. For each $r\ge1$ take $G=(C_2)^{r+1}$ and form the virtual difference
$$
 Z=\sum_{H\le G}|H|\mu(H,G)[G/H],
$$
where $\mu$ is the Möbius function of the subgroup lattice. For any subgroup $L$ its mark is
$$
 \phi_L(Z)=|G|\sum_{L\le H\le G}\mu(H,G)=|G|\,\mathbf1_{L=G}.
$$
Its positive and negative parts therefore have the same size and equal $r$-generator marks, but differ on the full group. Multiquadratic Galois fields realize the example over $\mathbb Q$. In particular, even when all the zero inputs are Dirichlet, an arbitrary test family limited to joint counts of at most $r$ Frobenius permutations cannot distinguish these two classes. The full stabilizer-size cutoff in Part 3 supplies the constructive test.

## 8. Source dependencies and status

The zero inputs come from the release archive with SHA-256 **9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc**. The member **lean/src/Main.lean** has SHA-256 **017645ca448f2fd1f6fd5c4c2cb2c6e96e472725be13f6e180ca6e1574360939**. The predicate for primitive Dirichlet zeros in the open critical strip is defined in **lean/src/Statements.lean**, SHA-256 **79ef7ca776e42abe1f46caee13ea09bd19f1e2d0b1620d8d5d200258f33b47bf**. The perfect trace form is the specified identity and size-one specialization of **traceGram_det_ne_zero** in **lean/src/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/TraceGramDetNeZero.lean**, SHA-256 **5da8355bcf4a434b8db6a3035e2a70249c52c71ce6acc831be1cd80504e3a112**. The transfer arguments above are written proofs. The analytic deductions retain Dirichlet GRH and the stated Dedekind RH assumptions. [Alpöge's release](https://alpo.ge/remark.pdf)

Classical arithmetic equivalence already describes the unmarked collision. The results here give a signed tensor-square prime estimate without requiring zero hypotheses for a full Galois closure, an exact comparison for normal nonabelian factors with a dimension-free bound, and an exact bounded-prime reconstruction from correlated lifts for arbitrary factors in a supplied Galois model.

## Finite controls

Exhaustive tests checked all 13,272 instances of (5) on the 168 group elements and 79 cyclic subgroups of $\operatorname{GL}_3(\mathbb F_2)$. All 168 separate point and plane characters agree, while the two specified transvections have joint marks one and three. The $D_8\times C_2$ calculation was checked on all 16 group elements. Subgroup-lattice computations on elementary abelian groups of ranks two through five checked all 462 truncated-mark identities.
