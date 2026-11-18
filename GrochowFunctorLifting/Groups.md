# Complement filtrations for two-prime Abelian Sylow towers

This is an informal advance on Grochow–Srivastava–Thakkar Open Question 3(4). The exact question asks for polynomial-time group epimorphism testing on Abelian Sylow towers or tame towers, with Cayley-table input. The results here concern two-prime Abelian Sylow towers and leave both unrestricted clauses open. [Open Question 3(4)](https://arxiv.org/html/2609.07429v1#S7)

## 1. The count for a fixed action isomorphism

Let $K,L$ be finite abelian $\ell$-groups with epimorphic marks $\rho:K\to C$ and $\sigma:L\to D$. Fix an isomorphism $\alpha:C\to D$. We count the epimorphisms $\beta:K\to L$ satisfying $\sigma\beta=\alpha\rho$.

Define torsion-image flags
$$
 \Theta_t=\rho(K[\ell^t]),\qquad
 \Gamma_t=\sigma(L[\ell^t]),\qquad
 \Lambda_t=\ell\Gamma_{t+1}.
$$
Here $X[\ell^0]=0$, and a flag is continued constantly above the exponent of the group. The homomorphism lift constraints have a solution exactly when $\alpha\Theta_t\subseteq\Gamma_t$ for all $t$. Necessity follows by applying any lift to $\ell^t$-torsion. For sufficiency, decompose $K$ into cyclic factors. Lift each generator of order $\ell^t$ to an element of $L[\ell^t]$ with the required mark. The choices are independent and define a homomorphism.

Let $Z=\ker\sigma$ and $\pi:L\to L/\ell L$. All solutions for a source generator of order $\ell^t$ form an affine coset of $Z[\ell^t]$. Its permitted head columns form an affine coset of $U_t=\pi(Z[\ell^t])$. Each admissible head column has exactly $|Z[\ell^t]\cap\ell L|$ lifts, and $U_t$ is an increasing sequence. The lift is surjective precisely when its head columns span $L/\ell L$.

Put $S_t=\pi(L[\ell^t])$. A head vector in $S_t$, reduced modulo $U_t$, is determined by the mark of any representative in $L[\ell^t]$ modulo $\Lambda_t$, and this is an isomorphism
$$
 S_t/U_t \;\simeq\; \Gamma_t/\Lambda_t.
$$
Indeed $\ell L\cap L[\ell^t]=\ell L[\ell^{t+1}]$, whose image under $\sigma$ is $\Lambda_t$. Thus the assignment to a mark modulo $\Lambda_t$ is well-defined and onto, and subtracting a representative in $\ell L\cap L[\ell^t]$ identifies its kernel with $U_t$. The quotient is elementary abelian.

Process source generators in increasing order of exponents. Before the block at exponent $t$, the span of the previously chosen head columns projected modulo $U_t$ has dimension
$$
 d_t^-=\dim_{\mathbb F_\ell}(\alpha\Theta_{t-1}+\Lambda_t)/\Lambda_t.
$$
After the entire block its projected span has dimension
$$
 d_t^+=\dim_{\mathbb F_\ell}(\alpha\Theta_t+\Lambda_t)/\Lambda_t.
$$
To see this, the images of the chosen generators of exponent at most $t'$, with $t'=t-1$ or $t$, span the projection of the whole $\ell^{t'}$-torsion. The latter differs from their generated subgroup only by elements of $\ell K$, using the cyclic decomposition of $K$. Any homomorphic lift takes these extra elements into $\ell L\cap L[\ell^t]$, whose mark lies in $\Lambda_t$. This proves both identities. The variation subspaces for all columns already processed lie in $U_t$, so none of their choices changes the projected span.

Within a block, first take $d_t^+-d_t^-$ generators whose projected marks extend the previous span to its full new span. Only a reordering of an ordinary cyclic generating basis is needed, since some subset of its columns is a basis modulo the previous span. Those columns force an increase of rank and give $\ell^{\dim U_t}$ options each. For any remaining column, if the actual rank before choosing it is $r$, exactly $\ell^{r-d_t^+}$ choices preserve the rank. The rest raise it by one. This follows because the column and the previous span meet in a coset of their intersection with $U_t$, of dimension $r-d_t^+$. Therefore the standard dynamic program on ranks counts all head choices of full rank. After multiplying the uniform lift factors, it counts the epimorphisms. Positive suffix counts and affine linear systems give a witness. This is the prescribed-map count of the finite module algorithm, with its dependence on the isomorphism $\alpha$ expressed only through the two transported flags.

Consequently the exact answer for a fixed $\alpha$ is a function of the pair of flags $(\alpha\Theta,\Gamma)$, and of the abstract orders of the specified source and target cyclic summands and target head variations. If both flags are moved by the same automorphism of $D$, the answer is unchanged. These statements concern the count for fixed $K,L,\rho,\sigma$. The abstract orders, variation sizes and lift fibers are independent of $\alpha$. Computing them and the flag intersection ranks uses ordinary table group operations or compact additive arithmetic. The count has at most $\log_\ell|K|\log_2|L|+1$ bits.


## 2. An orbit algorithm with no splitting hypothesis

**Theorem.** Let $G=A\rtimes K$ and $H=B\rtimes L$ be two-prime Abelian Sylow towers, where $A,B$ are abelian $p$-groups and $K,L$ are abelian $\ell$-groups, $p\ne\ell$. From raw Cayley tables one can decide, construct and count epimorphisms in time polynomial in the table size and in the maximal smaller flag orbit defined below. In particular the time is polynomial if either flag is invariant under the relevant action automorphism group. No splitting condition on either action kernel is needed.

Enumerate each distinct $K$-module quotient type $B'$ of $A$ of the abstract group type of $B$. There are at most $|A|$ quotient types before that test. For a simple residue type with $\mathbb F_p$-dimension $d$, collect the exponents of its homocyclic lifts as a partition of $e$, contributing $p^{de}$ to $|A|$. The possibilities for the quotient exponents are size-at-most-$e$ partitions, at most $2^e$ including the empty one. The choices over all source types give at most $|A|$ tuples. The coprime module routines enumerate and construct precisely the quotient types, using projectivity to lift equal-type residue maps to the homocyclic blocks. These are the same algorithms as in the earlier source/target cover result. [Weighted quotient recursion](https://github.com/Dugongue/MathProofs/blob/main/PortfolioIsomorphismCrossovers/GroupAlgorithms.md)

Take the faithful action quotients $C=K/\ker(K\to\operatorname{Aut}(B'))$ and $D=L/\ker(L\to\operatorname{Aut}(B))$, with the natural quotient marks $\rho,\sigma$. Construct the two groups $X=B'\rtimes C$ and $Y=B\rtimes D$, treating the quotient actions as given. Their orders are bounded by those of $G,H$. Compute their isomorphism coset. If it is empty, skip $B'$. The isomorphisms identify the normal Sylow groups and induce the compatible action isomorphisms $\alpha:C\to D$. Every such isomorphism can be normalized by target conjugation to send the selected complement into the selected complement. The induced $\alpha$ on the faithful quotient is unchanged. [Babai–Qiao, polynomial-time isomorphism for Abelian Sylow towers](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.STACS.2012.453) · [Skresanov, constructive coset algorithm](https://arxiv.org/html/2605.26748v2)

Choose one isomorphism $X\to Y$, with induced $\alpha_0:C\to D$. Compute generators for $U$, the image of $\operatorname{Aut}(Y)$ on $D=Y/B$, by projecting the automorphism generators on the canonical quotient. The set of induced action isomorphisms is $U\alpha_0$. Consider the two $U$-orbits on sequences of subgroups of $D$
$$
 \mathcal O_s=U\cdot(\alpha_0\Theta),\qquad
 \mathcal O_t=U\cdot\Gamma .
$$
Each sequence has at most $O(\log|K|+\log|L|)$ relevant entries. A subgroup can be stored by its list of elements in table time. Enumerate the smaller orbit and one transporting automorphism per state by breadth-first search using the generators. Running both searches alternately allows runtime polynomial in the smaller orbit without advance knowledge of its size. In the source-orbit version, choose $\alpha=u\alpha_0$ at state $u\alpha_0\Theta$. In the target-orbit version, choose $\alpha=u^{-1}\alpha_0$ at state $u\Gamma$. Section 1 implies that the compatible complement count $b(\alpha)$ is determined by the state and does not depend on the choice of representative. For the target version, move both flags by $u$ and use its simultaneous-invariance statement.

Let $\mathcal O$ be the chosen orbit. The epimorphism contribution of this $B'$ is
$$
 \frac{a_{\rm epi}\,|\operatorname{Iso}(X,Y)|}
      {a_{\rm aut}\,|\mathcal O|}
 \sum_{\omega\in\mathcal O} b(\alpha_\omega),
$$
where $a_{\rm epi}=\#\operatorname{Epi}_K(A,B')$ and $a_{\rm aut}=|\operatorname{Aut}_K(B')|$. These two local factors are the unmarked coprime-module counts. To prove the formula, a normalized isomorphism of $X,Y$ gives an equivariant isomorphism $B'\to B$ and a compatible $\alpha$. Compose it with an equivariant quotient map $A\to B'$, and choose any complement epimorphism $K\to L$ lifting $\alpha$. The resulting maps $G\to H$ are all normalized epimorphisms with quotient type $B'$. Each has exactly $a_{\rm aut}$ identifications of the abstract source quotient with $B'$. Each flag-orbit state has the same number of isomorphisms, by the quotient action and the orbit-stabilizer formula. Normalizing and restoring complements gives cancelling factors: both $B\rtimes L$ and $B\rtimes D$ have exactly $|B|/|B^D|$ conjugates of the chosen complement, since $B^L=B^D$. This proves the displayed count. The construction also lifts a positive witness through the chosen representative action isomorphism, via Section 1. Quotient types are disjoint, so sum their contributions.

If $\Gamma_t$ is characteristic in $D$ for every $t$, the target orbit has size one regardless of quotient type. More generally one can test invariance under $U$ directly on its computed generators. Likewise either invariant source flag or any polynomial smaller orbit suffices. This includes arbitrary split action kernels as a special case, since a split target mark has $\Gamma_t=D[\ell^t]$.

There are nonsplit examples with arbitrarily mixed complement exponents. Let $D=\bigoplus_j C_{\ell^{a_j}}$, choose $h\ge1$, and use
$$
 L=\left(\bigoplus_j C_{\ell^{a_j+h}}\right)\oplus W
 \longrightarrow D
$$
by the indicated cyclic quotient maps and zero on any auxiliary abelian $\ell$-group $W$. Then $\Gamma_t=D[\ell^{\max(0,t-h)}]$ is characteristic for every $t$. The mark does not split for nontrivial $D$, since an element of order $\ell^{a_j}$ mapping to its generator would violate the displayed torsion-image formula. The exponents $a_j$ and the factors of $W$ may be arbitrary. Pull any faithful coprime $D$-action back to $L$. Both source and target may have arbitrarily many complement factors outside every single exponent, so the earlier fixed exceptional-count promise need not hold.


## 3. A separate exact algorithm on the code subfamily

The established binary code correspondence uses $A=\mathbb F_3^r$ and $L_E=(\mathbb Z/4)^r/(2E)$ for a binary code $E\le\mathbb F_2^r$. The action quotient is $\mathbb F_2^r$ with its coordinate sign action on $A$. Its torsion-image flag in degree one is exactly $E$. Thus selection of a compatible action isomorphism from Section 2 includes finding a coordinate permutation taking the source code into the target code. Even for one nontrivial flag step, this can involve a superpolynomial orbit in the group table size. The correspondence and its exact count factor were already proved. [MathProofs, SylowTowerActionRanks, §5](https://github.com/Dugongue/MathProofs/blob/main/SylowTowerActionRanks/PROOF.md)

There is a different deterministic counting algorithm taking time $2^{O(r+ab)}$ on binary codes $E,F\le\mathbb F_2^r$, where $a=\dim E$ and $b=\operatorname{codim}F$. Write $x_i\in\mathbb F_2^a$ for column $i$ of a generator matrix of $E$, and $y_j\in\mathbb F_2^b$ for column $j$ of a parity-check matrix of $F$. A permutation is compatible exactly when
$$
 \sum_{i=1}^r x_i y_{\pi(i)}^{\mathsf T}=0.
$$
For a subset $S\subseteq[r]$ and a matrix $M\in\mathbb F_2^{a\times b}$, store the number of bijections from the first $|S|$ source coordinates to $S$ whose accumulated sum is $M$. Start at the empty set and zero matrix. To add a column $j\notin S$, add $x_{|S|+1}y_j^{\mathsf T}$ to the sum and increase the subset by $j$. The recurrence counts each bijection once and gives the desired answer in the full-subset, zero-matrix state. There are $2^r2^{ab}$ states and at most $r$ choices per state. Each count is at most $r!$, and predecessor states give a witness. This is a direct instance of exact group-weighted matching. [Kahn–Meshulam, On the Number of Group-Weighted Matchings](https://doi.org/10.1023/A%3A1008671206536) · [Santini–Baldi–Chiaraluce, Permuted Kernel and Subcode Equivalence](https://iris.univpm.it/handle/11566/325875)

Hence this algorithm takes polynomial time in the Cayley-table size throughout the code subfamily with $ab=O(r)$. It allows both dimensions to grow and does not require small flag orbits. For example take $a=b=\lfloor\sqrt r\rfloor$ for sufficiently large $r$. Choose a generator for $E$ and a generator for $F^\perp$ with $r$ distinct nonzero columns that include their basis vectors. A coordinate permutation stabilizing either code determines a unique invertible row transformation, and conversely such a transformation determines at most one coordinate permutation because the columns are distinct. Each flag orbit therefore has at least $r!/2^{\max(a,b)^2}=2^{\Omega(r\log r)}$ elements, even though the exact signature algorithm takes time $2^{O(r)}$. Both the exact signature count and the orbit algorithm are unconditional. The signature count may use $ab=\Theta(r^2)$ bits in general, so it does not imply a universal polynomial bound.

## 4. Route conclusions

The filtration route replaces enumerating complement quotient representatives and individual homomorphisms by a weighted orbit of torsion-image flags. It gives a polynomial theorem for an invariant side even when both complement extensions are nonsplit and have unbounded exponent diversity. The signature route bypasses this orbit in another family, but its state size depends on the product of a code dimension and a codimension. Unrestricted binary permutation subcode containment still needs time $2^{O(r)}$ to complete this approach on the binary code family. The compact model's known NP-completeness gives no Cayley-table lower bound. The full two-prime case and the unrestricted Abelian Sylow and tame-tower questions remain unresolved.


## 5. A polynomial algorithm for matched flag sizes

The orbit enumeration in Section 2 can be bypassed even when both orbits are large. Work on one quotient-type branch and first reject if $|\Theta_t|>|\Gamma_t|$ for any $t$. If $|\Theta_t|=|\Gamma_t|$ for every $t$, the condition for a homomorphic lift becomes the equality
$$
 \alpha\Theta_t=\Gamma_t\qquad\text{for all }t.
$$
The compatible action isomorphisms respecting these equalities can be found and counted in deterministic polynomial table time.

First find one plain flag isomorphism $\alpha_0:C\to D$, or prove none exists, using finite-ring module isomorphism. Represent each flag as the diagram of its successive subgroup inclusions ending at the whole group. Both are modules over the same line path algebra with coefficients $\mathbb Z/\ell^e\mathbb Z$, where $\ell^e$ bounds the two exponents. This finite ring has one additive generator per path over those coefficients and products specified by path composition. Its dimensions, modulus bit lengths and structure constants are polynomial in the input. The subgroup generators and inclusion matrices come from ordinary abelian group calculations. Ring-module isomorphisms are exactly componentwise diagram isomorphisms, so their terminal component is the required flag isomorphism. [Ciocănea–Teodorescu, Theorem 1.1](https://arxiv.org/abs/1512.08365)

Let $P$ be the flag-preserving subgroup of $\operatorname{Aut}(D)$. It is the unit group of the finite ring of additive endomorphisms $u$ of $D$ satisfying $u(\Gamma_t)\subseteq \Gamma_t$ for every $t$. Indeed, if $u$ is invertible on the additive group then its injections on these finite subgroups have image equal to the subgroup, so its inverse also preserves them. Compute the ring generators by simultaneous additive congruences in cyclic coordinates. The ring is an additive $\ell$-group, and its coordinate bit size is polynomial in $\log|D|$ and the flag data. Skresanov's Proposition 4.2 therefore computes unit generators in polynomial table time. Convert these to permutations on $D$ by direct evaluation. [Skresanov, Proposition 4.2](https://arxiv.org/html/2605.26748v2#S4)

All plain flag isomorphisms are $u\alpha_0$ for $u\in P$. Transport the source action on $B'$ to an action of $D$ using $\alpha_0$, and place it on the additive group $B$ by any additive isomorphism $B'\simeq B$. The given target action is already an action of $D$ on $B$. Skresanov's Proposition 3.9 computes the coset of $u\in P$ that make the two representations equivalent. Its hypotheses hold here: $P$ is given by permutation generators on the explicit group $D$, $B$ is an abelian $p$-group, and $D$ is an $\ell$-group with $\ell\ne p$. Both table orders and the explicit action lists are polynomial in the original table sizes. The proposition returns a coset, giving a representative and generators or an empty answer. [Skresanov, Proposition 3.9](https://arxiv.org/html/2605.26748v2#S3.SS2)

Every accepted $\alpha=u\alpha_0$ has the same transported source flag and therefore the same complement count $b_{\rm lift}$ from Section 1. If the coset is nonempty, evaluate this count once. Let $a_{\rm epi}$ be the number of $K$-module epimorphisms $A\to B'$. Given one intertwiner for a fixed $\alpha$, composition bijects these with the lower-layer epimorphisms to $B$ for any complement lift of $\alpha$. Hence the contribution of this quotient type is
$$
 |\text{compatible action-isomorphism coset}|\,
 b_{\rm lift}\,a_{\rm epi}\,\frac{|B|}{|B^D|}.
$$
Compute the coset size by permutation group order, and use its representative for witness construction. The last factor restores the conjugate image complements. All accepted complement epimorphisms determine their own $\alpha$, so distinct coset elements never double count a group epimorphism.

More generally, put
$$
 \Delta=\sum_t\log_\ell\frac{|\Gamma_t|}{|\Theta_t|}
$$
on any branch not immediately rejected by the size test, ending the sum at the larger complement exponent. Enumerate sequences $\Gamma'_t\le\Gamma_t$ of the same sizes as $\Theta_t$, retaining only chains, and run the same coset method for equality to $\Gamma'$. Continue to evaluate the complement count using the original target flag $\Gamma$, since that is the actual extension. Distinct $\Gamma'$ give disjoint transporter sets. A subgroup of index $\ell^{d_t}$ in $\Gamma_t$ is annihilated by a dual subgroup of order $\ell^{d_t}$, generated by at most $d_t$ elements. Enumerate tuples of that many elements in the additive character group of $\Gamma_t$, then take the annihilators and remove duplicates. This costs at most $|\Gamma_t|^{d_t}$ choices up to a polynomial factor, including $d_t=0$. The whole algorithm takes $N^{O(1+\Delta)}$ time on this branch, for $N=|G|+|H|$. A constant bound on $\Delta$ on all branches thus suffices for deterministic polynomial decision, construction and exact counting, with no orbit size bound. One can run this procedure alongside the orbit bound, taking the faster one per branch.


### Equal-order complements

If $|K|=|L|$, the two-prime problem is in deterministic polynomial time without any conditions on either action kernel or on the cyclic exponent lists. A complement epimorphism $\beta:K\to L$ is necessarily an isomorphism, so any action isomorphism $\alpha$ it induces must satisfy $\alpha\Theta_t=\Gamma_t$. This follows because $\beta$ maps each torsion subgroup $K[\ell^t]$ bijectively to $L[\ell^t]$. Reject any branch with unequal flag sizes and apply the matched-flag algorithm to every other branch.

There is also a shorter direct proof. For each previously enumerated $K$-module quotient type $B'$ of $A$ of the abstract type of $B$, form $B'\rtimes K$ and test its isomorphism to $H$. Any epimorphism to $H$ induces an isomorphism of the complements after passing to quotients by their normal $p$-groups. Thus its kernel lies in $A$, is $K$-invariant, and has one of these quotient types. Conversely, any equivariant quotient $A\to B'$ extends to $G\to B'\rtimes K$, which can be composed with a returned group isomorphism. The exact contribution is
$$
 \frac{\#\operatorname{Epi}_K(A,B')\,
 |\operatorname{Iso}(B'\rtimes K,H)|}{|\operatorname{Aut}_K(B')|}.
$$
Indeed each resulting epimorphism determines its $K$-module kernel quotient, and the choices of an identification of that quotient with $B'$ form a torsor under $\operatorname{Aut}_K(B')$. Isomorphisms here need not preserve the selected complement, so no additional complement counting factor is needed. Both algorithms take the original Cayley tables as input. [Babai–Qiao](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.STACS.2012.453) · [Skresanov](https://arxiv.org/html/2605.26748v2)
