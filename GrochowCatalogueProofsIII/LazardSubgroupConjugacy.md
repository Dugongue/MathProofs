# GP-0471 · Subgroup conjugacy through the Lazard lower central series

**Theorem.** Let $G$ be a finite $p$-group of nilpotency class $c<p$, given by a consistent compact power–conjugate presentation, with $p$ given. Given subgroups $H,K$ by ambient generator words, decide in deterministic polynomial bit time whether they are conjugate. In the positive case the algorithm computes a conjugator in Lazard Lie-ring coordinates and can output a straight-line word for it in the original generators. The algorithm handles variable $c,p$ and arbitrary exponent. It uses integer normal forms and successive linear congruence systems.

## Computing the Lazard coordinates from the presentation

Let $L$ be the corresponding finite Lie ring with additive $p$-group. Write $\operatorname{BCH}(X,Y)$ for its group law, with $\exp,\log$ denoting the correspondence between group and Lie coordinates. In a given Lie ring with bracket structure constants, BCH can be evaluated in bit-polynomial time without expanding it in a free Lie basis. In the formal identity
$$
 Z(s)=\log(\exp(X)\exp(sY)),\qquad
 Z'(s)=F(\operatorname{ad} Z(s))Y,\qquad
 F(u)=\frac{u}{1-e^{-u}},
$$
the derivative formula follows by multiplying $d\exp Z(s)/ds$ by $\exp(-Z(s))$ on the left. Its series before inversion is $(1-e^{-u})/u$. Truncate the latter below degree $c$ and invert it by the usual recursion for a series with constant term one. Modulo nilpotence, $Z(s)$ has degree at most $c$ in $s$, with $Z(0)=X$. Compute its next coefficient as the coefficient of $s^j$ on the right of the derivative equation divided by $j+1$. The right side only uses coefficients already computed. All divisions used have denominators built from integers at most $c$, which are invertible on the additive $p$-group. This computation is valid over the $p$-local integers by truncating the universal identities, and uses a polynomial number of truncated-polynomial and bracket operations. Evaluate at $s=1$. The same method works with any known bound $c'$ satisfying $c\le c'<p$; $\min(p-1,\log_p|G|)$ is such a bound.

Build the Lie-ring presentation from the end of the given polycyclic series to the beginning. At one step let $N\triangleleft G_0$ be the next tail subgroup, with cyclic quotient $G_0/N=\langle tN\rangle$ of relative order $m$. By induction write the coordinates of $\log N=L_N$ and of its original generators. Evaluate the supplied conjugation relation words in $L_N$ using BCH and integer scalar multiplication for powers. The images of the original generators of $N$ determine the additive map $T$ induced by conjugation by $t$, because their logarithms generate $L_N$ additively by the construction. If the presentation supplies conjugation by $t^{-1}$, use the same procedure and negate $\log T$ below. Evaluate the power-relator word $t^m$ in $L_N$ to get $w=\log(t^m)$. Lazard correspondence identifies normal subgroups with ideals and carries conjugation by $\exp x$ to $\exp(\operatorname{ad}x)$. Thus for $x=\log t$,
$$
 L_{G_0}\simeq (L_N\oplus\mathbb Z x)/\langle m x-w\rangle
 \quad\text{as an additive group},\qquad
 [x,v]=\sum_{j=1}^{c-1}\frac{(-1)^{j+1}}{j}(T-I)^jv\quad(v\in L_N).
$$
The additive description follows because the quotient by $L_N$ is cyclic of order $m$ and $m x=w$. The bracket follows by applying the inverse exponential series to the conjugation identity. These data, including the old bracket and $[x,x]=0$, determine the Lie ring. They agree with the actual Lazard Lie ring, so consistency of the original presentation guarantees compatibility of the bracket with the additive relation. Compute invariant-factor coordinates with integer Smith normal form. Keep coordinate maps for the original generators, whose logs continue to generate the new additive group.

There are as many stages as original generators, and $\log|G|$ is the sum of the bit sizes of the relative orders up to a linear term. Matrices, elements and structure constants at each stage have polynomial bit size in these coordinates. Evaluating compressed powers does not expand words. The logarithms of the subgroup generators are evaluated in the computed ring; their Lie subrings are obtained by iterated additive span and bracket operations, terminating after at most $\log_p|G|$ strict additive subgroup increases. By the correspondence, these Lie subrings are $U=\log H$ and $V=\log K$.

## Conjugating the Lie subrings

Form the lower central ideals $L_1=L$, $L_{i+1}=[L,L_i]$. Suppose the current conjugate $U$ of the source agrees with the target $V$ modulo $L_i$. This holds initially at $i=1$. The set of Lie coordinates of group elements preserving this common projection is the additively specified subring
$$
 N_i=\{x\in L:[x,U]\subseteq U+L_i\}.
$$
To verify the equality, apply the truncated exponential and logarithm series to the nilpotent map $\operatorname{ad}x$. A subgroup of a finite abelian $p$-group is closed under the denominators appearing in these series. Consequently a subgroup is invariant under the unipotent exponential if and only if it is invariant under its logarithm. Since $[x,L_i]\subseteq L_i$, test this on the generators of $U$ to obtain linear congruences for $N_i$.

Work in $M=(U+L_i)/L_{i+1}$, and put $C=L_i/L_{i+1}$ and $P=M/C$. Conjugation is the identity on $C$. If the intersections of the images of $U,V$ with $C$ differ, conjugation at this step is impossible. If the intersections agree, denote the common subgroup by $B$. In $M/B$ both subrings are additive complements of $C/B$, since they project onto $P$ with kernel $B$ before taking the quotient. Use $U$ to split $M/B=(C/B)\oplus P$. The subrings now correspond to graphs of additive maps $h:P\to C/B$; for $U$ the map is zero. For $x\in N_i$, the map $\operatorname{ad}x$ on this split group has block form
$$
 \begin{pmatrix}0&d_x\\0&A_x\end{pmatrix},
$$
where $d_x:P\to C/B$, $A_x:P\to P$ are additive and depend additively on $x$. The zero blocks use $[L,L_i]\subseteq L_{i+1}$.

Set $R=\mathbb Z/p^e$ with $p^e$ the exponent of $L$, and set $E=\operatorname{Hom}(P,C/B)\oplus R$. On this additive group put
$$
 T_x(h,t)=(t\,d_x-hA_x,\,0).
$$
The action of $\exp x$ on graphs is $(h,1)\mapsto\exp(T_x)(h,1)$. Indeed $\exp(\operatorname{ad}x)$ takes the graph of $h$ to the graph of
$$
 h e^{-A_x}+d_x\sum_{j\ge0}\frac{(-1)^jA_x^j}{(j+1)!}.
$$
This follows by taking the two blocks of the exponential on $M/B$, then using the inverse of its $P$-block to express the result again as a graph over $P$. Expanding $\exp(T_x)$ gives the same expression; all sums truncate before any invalid denominator.

Define $E_0=E$, $E_{j+1}=\sum_{x\in N_i}T_x E_j$; the sum over an additive generating set of $N_i$ suffices. This filtration descends and $E_c=0$. A mixed product of $j$ operators $T_x$ has terms given by $h$ composed with a product of $j$ of the $A_x$, and terms given by $d_x$ composed with a product of $j-1$ of the $A_x$. These are blocks of mixed length-$j$ products of the ambient $\operatorname{ad}x$ operators, which vanish at $j=c$ by the lower central series. All these subgroups and homomorphism spaces are computed in finite abelian coordinates by integer normal forms.

For a current graph point $a=(h,1)$ and the target $b$, suppose $a=b\bmod E_j$. We want a conjugation preserving this congruence and matching modulo $E_{j+1}$. The necessary and sufficient condition on $x\in N_i$ is the linear congruence
$$
 T_x a\equiv b-a\pmod{E_{j+1}}.
$$
In fact fixing $a$ modulo $E_j$ is equivalent to $T_xa\in E_j$ by the inverse logarithm series. Once this holds, all higher exponential terms land in $E_{j+1}$, so the displayed test is exactly the remaining requirement. The test itself implies $T_xa\in E_j$. Solve it by abelian-group linear algebra and update the graph by the exponential of any solution. Choosing an arbitrary solution cannot lose a full transporter: the graph points before and after the update are in the same orbit under $\exp N_i$. At the end $E_c=0$ gives equality at this central layer. Apply the recorded conjugations to the full subring $U$ and continue with $i+1$. The same orbit argument in $G$ applies to these choices at every outer step.

Each of the at most $c$ outer steps uses at most $c$ congruence lifts. Every abelian group used, including a homomorphism group between subquotients of $L$, has polynomial-size cyclic coordinates and presentation. In particular the whole search is bit-polynomial. The product of the successful conjugations is accumulated using BCH. To convert the final Lie element to an original straight-line word, recursively use the additive cyclic quotient at each polycyclic step to find the exponent of $t$; multiply on the left by its negative power in Lie coordinates to descend into $L_N$. The trivial group needs no steps. The same data give the number of conjugators. The full normalizer has Lie coordinates $\{x:[x,U]\subseteq U\}$, by the same exponential–logarithm invariance test. Smith normal form computes its order and additive generators, which also generate it under the group law by the subgroup–Lie-subring correspondence. A nonempty transporter is a coset of the normalizer.

[Catalogue context](https://arxiv.org/abs/2306.16317) · [Effective Lazard correspondence](https://doi.org/10.1016/j.jalgebra.2011.11.031) · [Grochow–Qiao, constructive Lazard comparison](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CCC.2021.16)

The graph lifting extends the portfolio's finite-field unipotent orbit method from vector spaces to abelian $p$-groups and intrinsic inner actions. [GP-0288 and GP-0289](https://github.com/Dugongue/MathProofs/blob/d7366c4348bc03f0e93cb8674db191de32ba58bf/GrochowCatalogueProofsII/UnipotentOrbitAlgorithms.md)
