# Prescribing tensor isomorphism over every intermediate field

The degree of an extension can hide which subgroups of a Galois group remain after base change. Finite Galois sets let us prescribe the full isomorphism pattern, including the actual subfields and simultaneous equivalence among more than two tensors.

## Theorem

Let $L/K$ be finite Galois with group $G$. Let $I$ be a finite nonempty index set, and for every subgroup $H\le G$ prescribe an equivalence relation $\sim_H$ on $I$. Assume the relations are invariant under conjugation of $H$, every pair is equivalent at $1$, and $i\sim_H j$ implies $i\sim_J j$ for $J\le H$.

There is an explicit family of equally sized ordinary three-tensors $T_i$ over $K$, all isomorphic over $L$ to the split diagonal tensor, such that $T_i,T_j$ are isomorphic over $L^H$ exactly when $i\sim_H j$. There is another family of at most twice the side length realizing the same pattern under **special-linear** tensor isomorphism and ordinary tensor isomorphism simultaneously. In characteristic different from $2,3$ the two constructions also give the corresponding ordinary and special-linear patterns for homogeneous cubic forms.

In particular, for a pair of tensors one can realize any conjugation-invariant downset of subgroups containing $1$. For any algebraic extension $M/K$ in a fixed algebraic closure, the test is the prescribed relation at $\operatorname{Gal}(L/(L\cap M))$. For a completion of a number field the test uses its decomposition group. Thus these are exact field criteria, and no restriction to Galois intermediate fields is necessary.

## A group-set construction

For a finite $G$-set $X$, let $m_J(X)=|X^J|$. Marks extend additively to formal integral combinations of transitive sets $G/H$. On restriction of $G/H$ to $J$, the orbit of $gH$ is $J/(J\cap gHg^{-1})$. These orbits are indexed by the double cosets $JgH$, which is the set-level Mackey decomposition. The mark counts the orbits with stabilizer equal to $J$. The marks for all subgroups of $G$ determine the orbit multiplicities. Order the transitive sets and the mark rows by nonincreasing subgroup order, up to conjugacy. The resulting matrix is triangular, since a $J$-fixed coset of $H$ requires $J$ to be conjugate into $H$. Its diagonal is $|N_G(H):H|>0$. Applied to an $H$-set, the same argument shows that restriction to $H$ agrees for two sets exactly when their marks agree for every $J\le H$.

For any $H\ne1$, write $\mu(-,-)$ for the Möbius function of the subgroup poset. Define a virtual $G$-set
\[
B_H=\sum_{D\le H}|D|\mu(D,H)[G/D].
\]
Its mark at $J$ is
\[
\sum_{\substack{g\in G\\g^{-1}Jg\le H}}
\ \sum_{g^{-1}Jg\le D\le H}\mu(D,H).
\]
The inner sum is one exactly when $g^{-1}Jg=H$, and zero otherwise. Thus $B_H$ has mark $|N_G(H)|$ at the conjugacy class of $H$ and zero elsewhere. This is the numerator in the Gluck–Yoshida inversion formula, with its short proof included here. Divide its coefficients by their gcd if desired. Write the resulting virtual set as $U_H-V_H$ by its positive and negative orbit multiplicities. Its trivial mark is zero, so $|U_H|=|V_H|$. [Gluck and Yoshida inversion, as stated by Bouc](https://lamfa.u-picardie.fr/bouc/burnamscorr.pdf)

Choose one $H$ from each nontrivial conjugacy class. If $\sim_H$ has $k_H$ classes, assign distinct codes $0,\ldots,k_H-1$ to them. Let $c_H(i)$ be the code of $i$. Form
\[
X_i=\{*\}\ \sqcup\ \bigsqcup_H
  \big(c_H(i)\,U_H\ \sqcup\ (k_H-1-c_H(i))\,V_H\big).
\]
Here multiplicity means disjoint copies, and $*$ is fixed. All sets have side length $1+\sum_H(k_H-1)|U_H|$. At a subgroup $J\ne1$, the mark difference between $X_i$ and $X_j$ is a nonzero constant times $c_J(i)-c_J(j)$, where a conjugate representative gives the same value. If the prescribed relation holds at $H$, it holds at every $J\le H$, so the restricted sets have equal marks and are isomorphic. If the restrictions are isomorphic, equality of their mark at $H$ gives the prescribed relation. For a single pair, it suffices to use $B_H$ for minimal excluded subgroups, since an excluded group contains a minimal excluded subgroup.

## From Galois sets to tensor and cubic transporters

For a $G$-set $X$, use the finite étale algebra
\[
A_X=(L^X)^G\cong\prod_{G/H\text{ an orbit of }X} L^H ,
\]
where the action on $L^X$ permutes coordinates and acts on coefficients. Over $L^H$ the primitive idempotents after splitting are the $H$-set $X|_H$. A permutation equivariant under $H$ induces an algebra isomorphism by permuting the coordinates before descent. Conversely the scalar extension of an algebra isomorphism permutes these primitive idempotents equivariantly. The same argument over any base change uses the image of its absolute Galois group in $G$. For $M$ algebraic this image equals $\operatorname{Gal}(L/(L\cap M))$, by applying finite Galois theory to $LM/M$.

Take $T_i$ to be the coordinate tensor of the bilinear multiplication $A_{X_i}\times A_{X_i}\to A_{X_i}$, with the output recorded in the third mode. A tensor transporter $(P,Q,R)$ between two unital commutative algebras has $R(xy)=P(x)Q(y)$. Setting one input equal to one gives $R(x)=P(1)Q(x)=Q(1)P(x)$. Since these maps are surjective, $u=P(1)$ and $v=Q(1)$ are units. Dividing by $u,v,uv$ gives the same unital multiplicative linear isomorphism on all three legs. Conversely any algebra isomorphism is such a transporter. This argument works after every base change.

For determinant-one transport, give $A\oplus A^*$ the multiplication of $A\times A$ by transporting its second copy across $x\mapsto\operatorname{Tr}(x\,{-})$, the nondegenerate étale trace pairing. Fix a basis of $A$ and its dual in the second copy. An algebra isomorphism $P:A\to A'$ acts in these coordinates by $\operatorname{diag}(P,P^{-\mathsf T})$, of determinant one. It preserves the transported multiplication because algebra isomorphisms preserve trace. Conversely ordinary tensor equivalence of the doubled tensors implies equality of the doubled Galois sets. Cancellation of orbit multiplicities shows that the original Galois sets are isomorphic. This gives both directions for special-linear equivalence, also after every base change.

For $\operatorname{char} K\notin\{2,3\}$ use $f_A(x)=\operatorname{Tr}(x^3)$. After splitting it is $\sum x_i^3$. Its Hessian determinant in split coordinates is $6^{\dim A}\prod_i x_i$. A linear equivalence of cubics preserves the hyperplane arrangement of this determinant, because Hessians transform by congruence. It therefore induces a permutation of the split coordinate hyperplanes, which are the same Galois set as the primitive idempotents. An equivariant permutation descends to an isomorphism of the étale algebras and thus preserves the cubic. The trace-dual doubling gives the same determinant-one conclusion for cubics.

## Sharp dimensions when every proper subgroup suffices

Suppose $G=(C_p)^r$ with $r\ge1$. Among side-balanced three-tensors split diagonal over $L$, the smallest ordinary side length of a pair equivalent over every intermediate field strictly containing $K$ and inequivalent over $K$ is exactly
\[
 p\prod_{i=1}^{r-1}(1+p^i).
\tag{1}
\]
To see that the range covers all such tensors, choose an isotopy to split multiplication over $L$ for a tensor split by $L$. Its descent acts semilinearly by autotopies of split multiplication. The preceding normalization shows that each such autotopy has a common permutation of the coordinate lines and two arbitrary invertible diagonal factors on the input legs. On one representative line of each Galois orbit, Hilbert's Theorem 90 gives a nonzero vector fixed under its stabilizer in each input leg. Transport these two vectors around the orbit. Use the products of these vectors in the output leg. Then the descent in all three bases merely permutes coordinates and acts on scalars. The original tensor is the multiplication tensor of the corresponding $A_X$.

Write $E$ for the group viewed as an $\mathbb F_p$-vector space. A difference of sets giving the indicated comparison has zero marks at all proper subgroups and nonzero mark at $E$. By triangularity it is a nonzero rational multiple of
\[
 e_E=\sum_{D\le E}\frac{\mu(D,E)}{[E:D]}\,[E/D].
\]
For codimension $k$, the subgroup Möbius value is $(-1)^k p^{k(k-1)/2}$. For completeness, the Gaussian binomial identity
\[
 \sum_{a=0}^{k}{k\brack a}_p p^{a(a-1)/2}t^a
     =\prod_{i=0}^{k-1}(1+p^it)
\]
follows by counting $a$-subspaces according to whether they lie in a chosen hyperplane. For a fixed $(a-1)$-intersection with that hyperplane, there are $p^{k-a}$ choices of an $a$-subspace outside it. This gives the binomial recurrence and the displayed product by induction. Substituting $t=-1$ gives the required subgroup-lattice Möbius recurrence. The $D=E$ coefficient of $e_E$ is one, and the coefficient for every codimension-one $D$ is $-1/p$. All denominators divide $p$ since $k(k-1)/2-k\ge-1$ for $k\ge0$. Hence the primitive integral difference is $p e_E$ up to sign.

After cancelling common orbits, the positive and negative parts of $p e_E$ have equal size since the trivial mark is zero. The sum of their sizes is
\[
\sum_{k=0}^r {r\brack k}_p\,p^{1+k(k-1)/2}
  =p\prod_{i=0}^{r-1}(1+p^i).
\]
Taking half gives (1). Every larger multiple has at least this side length, and the two actual parts achieve it. This minimality argument applies to tensors split by the specified $L$ and does not impose a bound on the dimensions of their constituent field factors beyond the common side length.

## Rational examples with local equivalence and controlled first extension

Multiquadratic examples can be made totally real with every decomposition group of order at most two. Choose distinct primes $\ell_1,\ldots,\ell_r$ recursively, each new prime congruent to one modulo $8$ times the product of the earlier primes. Dirichlet's theorem gives the next prime. Quadratic reciprocity implies that each prime is a quadratic residue at every other chosen prime. The square classes are independent by their valuations. For
\[
L=\mathbb Q(\sqrt{\ell_1},\ldots,\sqrt{\ell_r})
\]
the only nontrivial local quadratic factor at a chosen prime is its own factor. At $2$ all chosen primes are local squares, and at the real place they are positive. At any remaining prime the extension is unramified, hence its decomposition group is cyclic. This proves the claim for all places.

Every pattern from the theorem in which all pairs are equivalent at subgroup dimension at most one now gives rational tensors and cubics equivalent at every completion. For example, take $r\ge2$ and allow precisely subgroups of dimension at most one. All completions agree, but the smallest degree of a global number-field extension allowing equivalence is $2^{r-1}$. Indeed $\operatorname{Gal}(LM/M)$ must have order at most two, so $[M : \mathbb Q]\ge [L\cap M : \mathbb Q]\ge 2^{r-1}$. A fixed field of any subgroup of order two attains equality. For this example the mark construction needs only the two-dimensional subgroups. For each such $H$ the primitive element over $H$ from (1), induced to $G$, has positive and negative sizes $6\cdot 2^{r-2}$. Summing over all planes gives ordinary side at most $6\cdot 2^{r-2}{r\brack2}_2$, with a factor of two for the determinant-one construction. The nontrivial two-object pattern can use those signed orbit multiplicities directly without adjoining a common singleton.

## Relation to previous work

The Galois-category starting point was the workspace's archived formalization of universal-cover classification, where finite covers are recovered from a fiber with its action. The algebraic version uses split primitive idempotents as the fiber. Mackey restriction and the subgroup mark calculation supply the extension law. Grochow–Qiao's orbit reductions and Chen–Grochow–Qiao–Tang–Zhang's comparison of classical actions give the tensor complexity context. The earlier workspace result programmed extension *degrees* in the cyclic finite-field case. The new assertion prescribes simultaneous equivalence relations on the full conjugacy poset, with exact field-by-field transport and a sharp side bound in an elementary abelian case. Sutherland's Proposition 2.19 records the classical decomposition-group test for transitive Galois sets; the theorem here uses finite disjoint unions and independently prescribed subgroup marks. Publication priority remains unverified. [Grochow–Qiao I](https://arxiv.org/abs/1907.00309) · [Chen–Grochow–Qiao–Tang–Zhang III](https://arxiv.org/abs/2306.03135) · [Gluck–Yoshida inversion](https://lamfa.u-picardie.fr/bouc/burnamscorr.pdf) · [Sutherland](https://arxiv.org/abs/2104.01956)

The main theorem and minimality argument are written proofs. GaloisMarks.py checks all marks in a nonabelian example and seven elementary abelian examples, and verifies a three-object pattern on the Klein four group. These controls complement the universal arguments.
