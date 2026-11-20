# Counting epimorphisms of central extensions of products of simple groups

Let $G,H$ be finite groups given by Cayley tables. Suppose $A=\operatorname{Rad}(G)$ and $B=\operatorname{Rad}(H)$ are central, and both quotients are direct products of nonabelian simple groups. There is a deterministic algorithm that decides, constructs and exactly counts epimorphisms $G\twoheadrightarrow H$ in time
$$
|A|^{d(B)}\operatorname{poly}(|G|+|H|),
$$
where $d(B)$ is the minimum number of generators of the finite abelian group $B$. In particular the bound is polynomial for bounded target radical generator number. The source radical may have arbitrary rank, the target radical may have unbounded order and exponent, and simple factors may repeat with unbounded multiplicity. The proof gives a product formula for the number of epimorphisms with each prescribed surjection $A\to B$. When the radicals are elementary abelian for the same prime, bounding the dimension of either radical’s intersection with the derived subgroup also suffices, even with unbounded radical ranks.

This is a case of Grochow–Srivastava–Thakkar’s Open Question 3(5) and an exact-counting case of Open Question 2. Its extension decomposition uses Grochow–Qiao’s central-radical cohomology method. The recent epimorphism paper supplies the finite table model and target class. The Hexagon paper on model subgroupoids uses the related method of separating factors of a lift problem by orbit type and counting each type with its own multiplicity. Here the relevant orbits are automorphism orbits of restricted cocycle classes, with omitted source factors forced to have zero class. [Grochow–Srivastava–Thakkar, §7](https://arxiv.org/html/2609.07429v1#S7) · [Grochow–Qiao, §7](https://arxiv.org/abs/1309.1776) · [Zhenyu Sun, §§6–8](https://hexagonmath.org/2611.00276v1)

## Quotient and extension data

The two radicals are the respective centers, since the quotient groups are centerless. Compute them by comparing table entries. Under any epimorphism the image of the center is central. Also $H/\varphi(A)$ is a quotient of $G/A$ and hence a direct product of nonabelian simple groups, possibly empty. Its center is trivial, which forces $B\subseteq\varphi(A)$. Thus $\varphi(A)=B$.

For completeness, the normal subgroups of a product of centerless nonabelian simple groups are precisely the products of subsets of factors. If a normal subgroup has a nontrivial projection on a factor, commuting a projecting element with that factor gives a nontrivial element of their intersection, and the intersection is normal in the simple factor. This proves the assertion and shows that a surjection of such products selects one distinct source factor of the same simple type for each target factor and an isomorphism for each selection. The minimal nontrivial normal subgroups are exactly the factors. Compute them from the normal closures of individual nonidentity elements, keeping the inclusion-minimal closures. A quotient with no factors causes no exception to the construction.

Put $Q=G/A$ and $P=H/B$. Choose sections through the identity to construct normalized additive central cocycles $c$ on $Q$ with values in $A$ and $d$ on $P$ with values in $B$. Fix a surjection $u:A\to B$ and a quotient surjection $v:Q\to P$. A lift has form $(a,q)\mapsto(u(a)+h(q),v(q))$ in the section coordinates. The lift exists precisely when the two $B$-valued cocycles $u c$ and $v^* d$ differ by a coboundary. Any two solutions differ by a homomorphism $Q\to B$. Since $Q$ is perfect, there is exactly one lift whenever the coboundary equation is solvable, and this lift is surjective because both endpoint maps are onto. The equation can be solved by Smith form in cyclic coordinates of $B$ with one unknown $h(q)$ per quotient element.

A central extension of a product of perfect groups is determined by its restrictions to the factors when the central kernel and the quotient are fixed. To see injectivity, note that lifts of distinct factors commute. Their commutator lies in the central kernel and hence factors through a bi-homomorphism from the pair of factors to that kernel. Perfectness makes it trivial. Multiplying the lifts of factor sections therefore produces a section whose cocycle is the sum of the pullbacks of the restricted cocycles. This also shows directly that zero restricted classes on every factor imply zero global class. Consequently a dropped source factor must have $[u c_i]=0$, and a selected one must have class matching the pullback of its assigned target factor by the chosen simple-group isomorphism.

## Product formula and algorithm

Within each simple isomorphism type $T$, identify all copies with one representative $S_T$. Isomorphisms and the full automorphism list of an individual nonabelian finite simple group are computable in polynomial table time by finding a generating pair and enumerating its possible images. The finite simple two-generation theorem guarantees a pair. One checks each proposed map on the table. For cocycles with values in $B$, test class equality by solving the coboundary congruences and test equality of automorphism orbits by the same check after pulling back by each automorphism. [Guralnick–Kantor, Probabilistic generation of finite simple groups](https://pages.uoregon.edu/kantor/PAPERS/gkfinal.pdf) This groups the source classes $[u c_i]$ and target classes $[d_j]$ into orbit types $O$. Let $s_O,t_O$ be their respective counts and let $w_O$ be the order of the stabilizer of a class in $O$ under $\operatorname{Aut}(S_T)$, computed by the same comparisons. For any source and target classes in that orbit, exactly $w_O$ isomorphisms pull back the target class to the source class.

For a nonzero orbit all source factors must be used and every target factor must be matched, so the contribution is zero unless $s_O=t_O$, when it is $s_O!\,w_O^{t_O}$. For the zero orbit the contribution is zero when $t_O>s_O$, and otherwise it is
$$
(s_O)_{t_O}\,|\operatorname{Aut}(S_T)|^{t_O}
$$
with $(s)_t=s(s-1)\cdots(s-t+1)$ and $(s)_0=1$. Indeed all pairs within an orbit are equally eligible and the assignments are injective. The product over the simple types and all their orbits counts quotient surjections that lift. Each yields one epimorphism, so the product is also the desired count for $u$. A positive product gives a witness by making the indicated assignments, choosing the tested isomorphisms and solving the global correction equations.

Finally enumerate the homomorphisms $A\to B$ using cyclic decompositions, retaining the surjective ones. Such decompositions for explicit finite abelian groups can either be computed by standard table algorithms or obtained by presenting the group with one generator per element and a relation for each table entry, then using integer Smith form with transformations. For each cyclic target factor $C_m$, the number of maps $A\to C_m$ is $\prod_k\gcd(m,n_k)\le |A|$, where the $n_k$ are the cyclic orders of the source decomposition. Enumerate them by generator images of permissible order, independently in each target factor. A minimal cyclic decomposition of $B$ uses $d(B)$ invariant factors. The sum over the enumerated surjections gives the full count and the claimed bound. All intermediate integers have polynomial bit length, for example the final count is at most $|H|^{|G|}$. The number of simple factors in either group is logarithmic in its order, and the automorphism lists above concern individual factors. No factorial enumeration of equivalent factor assignments enters the algorithm.


## Unbounded radical rank with a bounded intersection with the derived subgroup

Suppose $A$ and $B$ are elementary abelian for the same prime $p$. Set $W_A=A\cap [G,G]$ and $W_B=B\cap[H,H]$. There is an alternative deterministic decision, construction and exact counting algorithm in time
$
\min\bigl(|W_A|^{\dim W_B}, |W_B|^{\dim W_A}\bigr)
\operatorname{poly}(|G|+|H|).
$
Thus bounded dimension of either intersection suffices even if both radical ranks grow. This case includes groups with arbitrarily many split central direct factors.

First, any epimorphism maps $W_A$ onto $W_B$. It maps $[G,G]$ onto $[H,H]$, and $[G,G]/W_A$ is $Q$ since $Q$ is perfect. So $[H,H]/\varphi(W_A)$ is a quotient of $Q$ and is centerless. The central subgroup $W_B$ maps trivially there, giving the other inclusion. Compute $W_A,W_B$ using table commutators and subgroup closure. Each central extension can be represented by a cocycle with values in the corresponding intersection. Indeed the projection $[G,G]\to Q$ is onto, so choose its section values inside $[G,G]$. Their defects lie in $W_A$, and the same argument applies to $H$.

Enumerate the surjective linear maps $w:W_A\to W_B$. The number of candidates is at most $p^{(\dim W_A)(\dim W_B)}$, giving the displayed two equivalent forms. For each $w$, compare the restricted cocycle classes over the coefficient group $B$, using $w c_i$ for the source. The earlier orbit formula counts quotient surjections that lift for any extension of $w$ to a surjection $A\to B$, because the chosen cocycles take values in $W_A$ and $W_B$. Using coefficient group $B$ directly also keeps the correction system in the exact original model.

It remains to count the extensions of $w$. Write $s=\dim(A/W_A)$, $r=\dim W_B$ and $b=\dim(B/W_B)$. Choose vector-space complements. The image of $W_A$ is already $W_B$. The linear map on the source complement must induce a surjection onto $B/W_B$, and each such map has $p^{rs}$ lifts into $B$. The number of extensions is therefore zero when $s<b$, and otherwise
$
p^{rs}\prod_{i=0}^{b-1}(p^s-p^i).
$
The product counts full row rank $b\times s$ matrices by choosing independent rows. The empty product covers $b=0$. Multiply the earlier orbit count by this number for each $w$ and sum. For a witness choose any such full-rank map and lift it, then use the earlier correction calculation. This proves the bound and the exact count, including when either intersection is zero.

The Lean lemma checks the uniqueness of the correction on perfect quotients. The factor analysis, count and polynomial bound are proved above in prose. The general case where both relevant intersection dimensions and target radical rank are unbounded remains open in this account.
