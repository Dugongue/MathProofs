# Exact coprime-extension descent for central simple multiplication tensors

Let $L/K$ be a fixed finite Galois extension of number fields, with $G=\operatorname{Gal}(L/K)$, and fix $n\ge1$. A degree-$n$ central simple $L$-algebra has dimension $n^2$ over $L$. Its ordered multiplication tensor over $K$ has side $[L:K]n^2$.

Write $\kappa(G)$ for the least positive integer such that every finite family of left cosets of subgroups of $G$ with empty intersection contains at most $\kappa(G)$ members with empty intersection. We also permit an empty set as a constraint, which leaves this definition unchanged. The Helly dimension is $r+1$ when $G$ is finite abelian with minimal generator number $r$. [Domokos–Szabó, Helly dimension of algebraic groups, Corollary 2.3](https://arxiv.org/abs/0911.0404).

## The exact degree-list criterion

Fix a nonempty finite list of positive integers $d_1,\ldots,d_t$. Consider the following property. Whenever multiplication tensors of two degree-$n$ central simple $L$-algebras are isomorphic over finite extensions $E_j/K$ of degrees $d_j$ that are each linearly disjoint from $L$, their multiplication tensors are isomorphic over $K$. The $E_j$ are allowed to depend on the algebras.

**Theorem 1.** This property holds if and only if there is no set $P$ of at most $\kappa(G)$ distinct prime divisors of $n$ such that every $d_j$ is divisible by at least one member of $P$. The criterion is unchanged if all probes must be subfields of one cyclic extension of $K$ linearly disjoint from $L$.

In particular, if $n>1$ and the $d_j$ are pairwise coprime, $\min\{\kappa(G),\omega(n)\}+1$ probes suffice, where $\omega(n)$ counts the distinct prime factors of $n$. That number is the smallest uniform bound, even when all probes are cyclic extensions. A nontrivial cyclic center and a degree divisible by two distinct primes give the sharp threshold of three. For $n=1$ the tensors are already isomorphic.

The upper direction only needs finite separable extensions of fields, with the same Galois-center and disjointness conditions. The converse uses number fields. This is a restricted descent result for Grochow–Qiao's field-comparison question, Open Question 10.6 in the long preprint. It gives an exact criterion for one tensor family and does not give a reduction between unrestricted TI classes. [Grochow–Qiao, On the Complexity of Isomorphism Problems for Tensors, Groups, and Polynomials I](https://arxiv.org/pdf/1907.00309).

## 1. Natural witnesses on centers

For unital associative algebras $A,B$, let a multiplication-tensor witness be a triple of invertible linear maps satisfying
$$
R(xy)=P(x)Q(y).
$$
Put $a=P(1)$ and $b=Q(1)$. Evaluating with one argument equal to $1$ gives $R(x)=aQ(x)=P(x)b$. Left multiplication by $a$ and right multiplication by $b$ are invertible linear operators, so $a,b$ are units. Indeed, surjectivity supplies a one-sided inverse, and injectivity then supplies the other equality. The map
$$
\phi(x)=a^{-1}P(x)=Q(x)b^{-1}=a^{-1}R(x)b^{-1}
$$
is a unital algebra isomorphism. Conversely any such $\phi$ and units $a,b$ give the witness
$$
(P,Q,R)=(L_a\phi,\ R_b\phi,\ L_aR_b\phi).
$$
These identities commute with arbitrary scalar extension, as does the projection of $\phi$ to the induced isomorphism of centers. In particular the complete tensor witness set has natural coordinates $(a,b,\phi)$. Two algebra witnesses inducing the same center map differ by an inner automorphism of $B$, by Skolem–Noether. The set of attained center maps is thus the quotient of the tensor witness set by arbitrary changes to the two unit coordinates and postcomposition of the normalized isomorphism by an inner automorphism. [Stacks Project, Skolem–Noether](https://stacks.math.columbia.edu/tag/074P).

Write $\alpha=[A]$ and $\beta=[B]$ in $\operatorname{Br}(L)$. Let $\alpha_\ell,\beta_\ell$ be their $\ell$-primary parts. Each class has period dividing $n$. A center map $g\in G$ lifts to an algebra isomorphism over $K$ precisely when $g\alpha=\beta$. Here $g$ acts by the change of scalar structure for which local invariants are transported from $w$ to $gw$. The equality criterion holds because the two central simple algebras have equal degree and a Brauer class determines the underlying division algebra. [Gille–Szamuely, Central Simple Algebras and Galois Cohomology, Chapters 2 and 4](https://www.math.ens.psl.eu/~benoist/refs/Gille-Szamuely.pdf).

For each $\ell\mid n$, put
$$
C_\ell=\{g\in G:g\alpha_\ell=\beta_\ell\}.
$$
This is empty or a left coset of the stabilizer of $\alpha_\ell$. The set of attainable center maps over $K$ is exactly $\bigcap_{\ell\mid n}C_\ell$. For $E/K$ linearly disjoint from $L$, the center becomes $LE$ and $\operatorname{Gal}(LE/E)=G$ by restriction. These identifications commute with scalar extension between disjoint probes. If a witness over $E$ induces $g$, then the restriction of $g\alpha-\beta$ to $\operatorname{Br}(LE)$ vanishes. Corestriction makes its multiple by $[E:K]$ vanish over $L$. Hence $g\in C_\ell$ whenever $\ell\nmid[E:K]$. [Kleinert, On the restriction and corestriction of algebras over number fields](https://webdoc.sub.gwdg.de/ebook/serien/e/hbm/hbm2007270.pdf).

If the family of $C_\ell$ has empty intersection, some subfamily indexed by a set $P$ of at most $\kappa(G)$ primes has empty intersection. Every witness degree must be divisible by at least one of those primes. This proves the sufficient part of Theorem 1, including the pairwise-coprime bound. A failed descent for this class is localized to at most $\kappa(G)$ primary constraints.

## 2. Realizing all coset constraints by genuine tensor witnesses

**Theorem 2.** Fix distinct rational primes $\ell_1,\ldots,\ell_m$ dividing $n$. Let $D_1,\ldots,D_m$ be any left cosets of subgroups of $G$, with the empty set also allowed. There are degree-$n$ central simple $L$-algebras $A,B$ and cyclic fields $E_i/K$ of degree $\ell_i$, whose compositum is linearly disjoint from $L$, such that over
$$
E_S=\prod_{i\in S} E_i,\qquad S\subseteq\{1,\ldots,m\},
$$
where the product denotes compositum, the attainable center maps of the multiplication-tensor witnesses are exactly
$$
\bigcap_{i\notin S} D_i .
$$
An empty intersection of constraints means all of $G$. The identification is compatible with all inclusions of probe composita. Moreover, for every positive integer $d$, some degree-$d$ extension $E/K$ linearly disjoint from $L$ gives a witness exactly when $\bigcap_{\ell_i\nmid d}D_i\ne\varnothing$.

**Construction.** Choose the $E_i$ by taking over $\mathbb Q$ a cyclic degree-$\ell_i$ subfield of a prime conductor cyclotomic extension and adjoining it to $K$. For step $i$, choose its rational conductor prime $q_i\equiv1\bmod \ell_i$ outside the ramification set of $L E_1\cdots E_{i-1}$ over $\mathbb Q$; Dirichlet gives such primes. The cyclotomic subfield ramifies at $q_i$ and its prime degree means it has no proper nontrivial subfield. Its intersection with $L E_1\cdots E_{i-1}$ is therefore $\mathbb Q$. Since the cyclotomic subfield is Galois, the compositum grows by $\ell_i$. The resulting compositum with $L$ has Galois group $G\times \prod_i C_{\ell_i}$ over $K$.

Choose two distinct finite places $v_i^+,v_i^-$ of $K$ with trivial Frobenius in $L$ and every $E_j$ for $j\ne i$, and generator Frobenius in $E_i$. The specified elements are central in the product Galois group, and Chebotarev gives these places. Choose all places distinct. At each of the two places for $i$, label primes of $L$ above it by the regular $G$-set $G$, after choosing the prime labeled $1$.

If $D_i=g_iH_i$, prescribe the local invariants of an $\ell_i$-primary Brauer class $\alpha_i$ to be $+1/\ell_i$ at the primes labeled by $H_i$ above $v_i^+$, and $-1/\ell_i$ at the same labels above $v_i^-$, zero elsewhere. Prescribe $\beta_i$ using $g_iH_i$ in place of $H_i$. If $D_i$ is empty, use $H_i=\{1\}$ for $\alpha_i$ and set $\beta_i=0$. Each list sums to zero. The Albert–Brauer–Hasse–Noether theorem gives the classes, and its injectivity gives
$$
\{g:g\alpha_i=\beta_i\}=D_i
$$
because $g$ acts on the local labels by left translation. Over a number field the index equals the period. Thus the classes $\alpha=\sum_i\alpha_i$ and $\beta=\sum_i\beta_i$ have index dividing $\prod_i\ell_i$, which divides $n$. Choose degree-$n$ algebras in the two classes by taking full matrix algebras over their division representatives. [Chernousov–Rapinchuk–Rapinchuk, The genus of a division algebra and the unramified Brauer group, §3.1](https://link.springer.com/article/10.1007/s13373-013-0037-z).

For $i\in S$, the local extension degree at every $\ell_i$-support place is divisible by $\ell_i$, so base change to $LE_S$ kills both $\alpha_i$ and $\beta_i$ by the local invariant restriction formula. For $i\notin S$, restriction to $LE_S$ is injective on the $\ell_i$-primary part because $[LE_S:L]=\prod_{j\in S}\ell_j$ is coprime to $\ell_i$. This proves exactness on the composita, and the witnesses' naturality was proved in §1.

Now take a degree $d$. For a degree-$d$ disjoint extension with a witness, §1 gives an element of $\bigcap_{\ell_i\nmid d}D_i$. Conversely assume that intersection nonempty. Let $S=\{i: \ell_i\mid d\}$. There is a witness over $E_S$, of degree $e=\prod_{i\in S}\ell_i$ dividing $d$. Choose a finite prime of $E_S$ splitting completely in $LE_S/E_S$. A monic polynomial of degree $d/e$ Eisenstein at that prime stays Eisenstein over $LE_S$ at any prime above it. Adjoining one root gives an extension $E/E_S$ of degree $d/e$ with $[LE:LE_S]=d/e$. Thus $E/K$ has degree $d$ and is disjoint from $L$. The witness over $E_S$ extends to $E$.

**Necessity in Theorem 1.** Suppose $P=\{\ell_1,\ldots,\ell_m\}$ meets the prime divisors of every $d_j$, with $1\le m\le\kappa(G)$. For $m=1$ use $D_1=\varnothing$. For $m\ge2$, start with a minimally inconsistent family of $\kappa(G)$ cosets, which exists by the definition of $\kappa(G)$, and partition it into $m$ nonempty blocks. Intersect the members of each block to obtain $D_i$. Each $D_i$ is nonempty and a left coset since its block is proper. The intersection of all $D_i$ is empty, while omitting any one gives a nonempty intersection. Theorem 2 produces base-inequivalent tensors with a witness over a disjoint extension of every listed degree $d_j$, since each degree removes at least one constraint. For the sharp pairwise-coprime counterexample use $m=\min\{\kappa(G),\omega(n)\}$ and the probe fields $E_i$ themselves. In this case the probes are Galois of prime degree.

**One common cyclic extension.** In the converse for a fixed list $d_j$, the cyclic probe fields can all be taken inside one cyclic extension disjoint from $L$. For every rational prime $\ell$ dividing $\prod_jd_j$, set $a_\ell=\max_jv_\ell(d_j)$. In the cyclotomic construction choose prime conductor $q_\ell\equiv1\bmod\ell^{a_\ell}$ and a degree-$\ell^{a_\ell}$ subfield over $\mathbb Q$, then adjoin it to $K$. The distinct conductors can be unramified in all previous fields and in $L$. Every nontrivial subfield of the chosen cyclotomic subfield ramifies at $q_\ell$, so each step is linearly disjoint from the previous compositum with $L$. The product of the resulting cyclic groups is cyclic because their orders are coprime. For a constraint prime $\ell_i$, use the degree-$\ell_i$ subfield of the chosen cyclic $\ell_i^{a_{\ell_i}}$-extension as $E_i$ in the Brauer construction. The unique degree-$d_j$ subfield of the full cyclic compositum contains each $E_i$ with $\ell_i\mid d_j$. It therefore carries the required witness, and is disjoint from $L$.

## 3. Constructing a base witness when the probe center maps already agree

The previous theorem gives existence even when different probes use different center maps. There is an elementary recovery method if supplied witnesses on a subfamily of probe degrees with greatest common divisor $1$ all induce the same $g$. It uses linear algebra over $L$ and avoids computing Brauer invariants.

Change the specified $L$-structure of $A$ by $g$ so that the supplied normalized isomorphisms $\phi_j$ are $LE_j$-linear. Give $B_{LE_j}$ a left $B$-action by multiplication and a right $A$-action through $\phi_j$, and restrict scalars to $L$. These are modules $M_j$ of dimension $d_j n^2$ over the central simple algebra $C=B\otimes_L A^{\mathrm{op}}$. Every finite-dimensional $C$-module is a direct sum of copies of one simple module. Given two such modules of dimensions $a n^2,b n^2$ with $a\ge b>0$, there is an injective $C$-map $M_b^{\oplus\lfloor a/b\rfloor}\to M_a$. Take its cokernel to realize the Euclidean remainder $a\bmod b$ at module level. Repeat with the supplied $M_j$ until a module $M$ of dimension $n^2$ is reached.

As a left $B$-module $M$ is isomorphic to $B$, by the same simple-module uniqueness and dimension argument. Choose a cyclic vector $m$ giving an isomorphism $B\to M$, $b\mapsto bm$. The right action defines $\phi:A\to B$ by
$$
ma=\phi(a)m .
$$
The commuting actions and associativity show $\phi(a_1a_2)=\phi(a_1)\phi(a_2)$. The map is unital and injective by simplicity, then bijective by dimension. Undo the initial center twist. The resulting algebra isomorphism gives an explicit tensor witness by using both unit parameters equal to $1$.

The required injections are found inside linear intertwiner spaces. Over an infinite field, sample coefficients in a basis of the intertwiner space from a finite set of cardinality at least twice the domain dimension plus one. Some full-rank minor is a nonzero polynomial of degree at most that dimension, giving success probability at least $1/2$ by the polynomial zero bound. Rank verifies success. The same method finds the cyclic vector by a determinant test. Module bases, actions, Hom spaces, and cokernels are obtained by linear algebra on dimensions bounded by the supplied restricted-scalar modules. This is a Las Vegas algorithm with polynomial expected field-operation count, given explicit extension arithmetic, center identifications and probe witnesses. No bit-height bound or arithmetic algorithm for aligning differing center maps is assumed.

## 4. The determinant-one action with no increase in tensor size

There is an intrinsic volume normalization over $L$ for each central simple algebra $A$ of degree $n$. Over a finite Galois splitting field, transport the volume form assigning value $1$ to the ordered matrix-unit basis of $M_n$. Two splitting isomorphisms differ by conjugation by an invertible matrix $C$, by Skolem–Noether. This conjugation has determinant $(\det C)^n(\det C^{-1})^n=1$, using its left and right multiplication operators. Thus all splitting isomorphisms transport the same volume form. Its Galois conjugate is obtained from another splitting isomorphism by the same rule, so it is fixed and descends to a volume form $\nu_A$ over $L$. This construction is compatible with scalar extension and with change of field structure along a center isomorphism.

For both $A$ and $B$, choose $L$-bases of volume $1$ and expand them by the same ordered $K$-basis of $L$ to obtain the $K$-bases for the multiplication tensors. Over a disjoint extension $E/K$ these bases extend and have the same normalization. An algebra isomorphism $\phi$ inducing $g\in G$ on the center is $g$-semilinear on the center vector spaces and preserves the normalized volumes semilinearly. In the chosen coordinates its linear part after separating the entrywise action of $g$ has determinant $1$ over the center. Restriction of scalars takes this determinant to its field norm, still $1$. The remaining map applies $g$ to $n^2$ copies of the center. A normal basis for $L/K$ identifies the $K$-linear action of $g$ with its regular permutation, and extends to a normal basis for $LE/E$. Consequently, over $K$ or any disjoint probe,
$$
\det(\phi)=\bigl(\operatorname{sgn}_{\mathrm{reg}}(g)\bigr)^{n^2}.
$$
The sign is the sign of the permutation $x\mapsto gx$ of $G$.

For the tensor witnesses in §1, multiplicativity of the determinant gives
$$
\det(\phi)=\frac{\det(P)\det(Q)}{\det(R)} .
$$
A special-linear triple therefore requires $\det(\phi)=1$. Conversely if $\det(\phi)=1$, choosing $a=b=1$ gives a special-linear triple. Thus the exact attained center maps for the determinant-one action are the ordinary attained center maps intersected with
$$
G_n=\{g\in G: \operatorname{sgn}_{\mathrm{reg}}(g)^{n^2}=1\}.
$$

**Corollary.** Theorem 1 holds for determinant-one tensor isomorphism with the same side $[L:K]n^2$, replacing $\kappa(G)$ by $\kappa(G_n)$ and using the volume-normalized bases. Indeed, intersections of the primary constraints with $G_n$ are empty or left cosets in $G_n$. To obtain sharpness, realize any left cosets of subgroups of $G_n$ as the same left cosets in $G$ in Theorem 2. This also gives exact determinant-one witness profiles on the cyclic composita. When $n$ is even the restricted and ordinary degree-list criteria coincide.

**An explicit difference for odd degree.** Let $K=\mathbb Q$, $L=\mathbb Q(\sqrt5)$, and $n=15$, giving tensor side $450$. Write $\tau$ for the nontrivial center automorphism. Take $E_3=\mathbb Q(\zeta_7)^+$ and $E_5=\mathbb Q(\zeta_{11})^+$, the maximal real subfields, of degrees $3$ and $5$. The rational primes $89,109$ split in $L$ and $E_5$ and are inert in $E_3$. The rational primes $29,41$ split in $L$ and $E_3$ and are inert in $E_5$. These statements follow from the residues modulo $5,7,11$, since the trivial Frobenius class in each real cyclotomic subfield is $\{\pm1\}$.

Use the first pair of primes for a $3$-primary constraint $D_3=\{1\}$ and the second for a $5$-primary constraint $D_5=\{\tau\}$. In detail, put the invariant $+1/3$ at a chosen prime of $L$ above $89$ and $-1/3$ at one above $109$ in both classes. Put $+1/5$ above $29$ and $-1/5$ above $41$ at chosen primes for $\alpha$, and at the other primes over the same rational primes for $\beta$. All other local invariants are zero. These are degree-$15$ division classes by period–index equality. Both tensor actions give no witness over $\mathbb Q$. Over $E_3$ the ordinary action gives witnesses inducing $\tau$, so the determinant-one action gives none. Over $E_5$ there is a witness inducing $1$ for both actions. This uses the same tensors and the same inherited volume normalization over the two probes.

## Prior work and status

Grochow–Qiao's example distinguishes scalar extension for tensors from the unconditional descent of labeled matrix tuples. Ordinary autotopy normalization for associative algebras, Brauer primary decomposition and the Helly dimension of cosets are established ingredients. The workspace already classifies split diagonal multiplication tensors by Galois sets and programs field profiles by subgroup marks. The present construction fixes a single center field throughout and programs the attainable *maps on that center*, even for probe extensions that leave the center's Galois structure unchanged. It gives a sharp criterion for all degree lists at a fixed tensor side. These are pencil-and-paper proofs. Independent publication-priority review and Lean verification remain open.
