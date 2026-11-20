# Sharp upper bound for prime-cyclic rational invariant fields

This is an informal proof of Conjecture 5.1 of Ben Blum-Smith, Thays Garcia, Rawin Hidalgo, and Consuelo Rodriguez. It uses the Cauchy–Davenport theorem, Vosper’s theorem, Kneser’s theorem, and Kemperman’s structure theorem in abelian groups. [Original conjecture](https://doi.org/10.1016/j.jpaa.2024.107693) · [Kemperman’s theorem and elementary pairs, as stated by Lev](https://arxiv.org/abs/math/0508179)

**Theorem.** Let $p$ be a prime, $k$ a field of characteristic different from $p$, and $V$ a finite-dimensional representation of $C_p$ over $k$. If $m\ge 1$ distinct nontrivial characters occur after extension to an algebraic closure, the invariant field $k(V)^{C_p}$ is generated over $k$ by polynomial invariants of total degree at most
$$
 D=\left\lceil\frac{p}{\lceil m/2\rceil}\right\rceil.
$$
The cited conjecture’s sharpness examples already attain this upper bound. When $m=0$, the action is trivial and degree 1 suffices. [Original conjecture, §5.1 and Proposition 5.2](https://doi.org/10.1016/j.jpaa.2024.107693)

## Integral relation problem

The degree parameter is unchanged by base extension. After adjoining the $p$-th roots of unity and removing trivial and repeated characters, the field-generation statement is equivalent to the following lattice statement. In the diagonal representation, polynomial invariant monomials correspond to nonnegative integral zero-sum exponent vectors, and division of monomials corresponds to subtraction of exponent vectors. The field-generation criterion uses integral lattice generation. [Base extension, original Lemma 2.1](https://arxiv.org/abs/2303.05626) · [Lattice equivalence and reduction, Lemmas 2.10 and 2.12](https://arxiv.org/html/2604.18876v1#S2)

Let $A\subseteq\mathbb F_p^\times$ be the set of nontrivial weights, let $m=|A|$, and put $B=A\cup\{0\}$. Write
$$
 L=\ker\!\left(\mathbb Z^A\longrightarrow\mathbb F_p,\quad e_a\longmapsto a\right),\qquad
 R=\big\langle u\in L\cap\mathbb Z_{\ge 0}^{A}:\ \textstyle\sum_a u_a\le D\big\rangle_{\mathbb Z}.
$$
We will prove $R=L$. When $m=1$, the generator $p e_a$ suffices. When $m=2$, dilate the weights to $1,b$ for $2\le b\le p-1$. The vectors $(p,0)$ and $(p-b,1)$ have lengths at most $D=p$ and determinant $p$. Their span has index $p=[\mathbb Z^A:L]$, giving $R=L$.

Suppose $m\ge 3$. Then $p$ is odd, $D\ge 3$, and $k_0=\lceil m/2\rceil$ satisfies $2\le k_0<p$. Use the abelian group $H=\mathbb Z^A/R$ with its natural surjection $\pi:H\to\mathbb F_p$. Write $f(a)=e_a+R$ for $a\in A$ and $f(0)=0$. Every sequence of at most $D$ elements of $B$ with sum zero in $\mathbb F_p$ has $f$-sum zero in $H$. Repeated letters and zero padding are allowed. It suffices to extend $f$ to an additive map on $\mathbb F_p$, since the composite of $\pi$ followed by that map then fixes the generators $f(a)$ of $H$.

## Progression supports

Suppose $B$ is an arithmetic progression in $\mathbb F_p$. Dilating by a nonzero residue and possibly reversing the progression, we may represent it by the integer interval $[-a,b]$, where $a,b\ge 0$, $a+b=m$, and $b\ge a$. Here $0$ is a term of the progression and is chosen as the origin of its integer indices. Regard $f$ as defined on this interval by reduction modulo $p$.

Put $J=[-a,b-1]\cap\mathbb Z$ and $\Delta_i=f(i+1)-f(i)$ for $i\in J$. For $i,j\in J$, if
$$
 tp-(D-2)b\le i+j+1\le tp+(D-2)a
$$
for an integer $t$, then $\Delta_i=\Delta_j$. Indeed, $tp-(i+j+1)$ is a sum of $D-2$ integers in $[-a,b]$, since the integer sumset of $D-2$ copies of an interval is the corresponding full interval. Append that same sequence to $(i+1,j)$ and $(i,j+1)$ and use the two zero-sum relations.

For each $t$, all $\Delta_i$ for
$$
 i\in J_t=J\cap[tp-(D-1)b,\ tp+(D-1)a-1]
$$
are equal. Indeed, any adjacent $i,i+1$ in $J_t$ have a common comparison index $j$ in
$$
 J\cap[tp-(D-2)b-i-1,\ tp+(D-2)a-i-2].
$$
The two adjacent membership bounds give respectively that the left endpoint of this new interval is at most $b-1$ and the right endpoint is at least $-a$. The interval has endpoint difference $(D-2)m-1\ge 0$.

We have $Dk_0\ge p+1$, as $p$ is prime and $k_0\ge 2$ is less than $p$. Consequently $Db\ge p+1$, and
$$
 (D-1)m-p\ \ge\ (D-1)(2k_0-1)-Dk_0+1=(D-2)(k_0-1)\ge 1.
$$
If $a=0$, $J_1$ covers $J$. If $a>0$, $J_0$ contains the left endpoint of $J$, $J_1$ contains the right endpoint, and the displayed inequalities give $J_0\cap J_1\ne\varnothing$. Thus all increments equal a common $\Delta$, and $f(i)=i\Delta$ since $f(0)=0$. The integer $p$ is the sum of $D$ integers from $[0,b]$ because $Db\ge p+1$. This is a zero-sum relation modulo $p$, hence $p\Delta=0$, giving the required additive extension.

## Sumset growth outside the progression case

Suppose $B$ is a non-progression. Write $jB$ for the sumset of $j$ copies of $B$. If $m$ is even, Cauchy–Davenport gives $|jB|\ge \min(p,jm+1)$. If $m$ is odd, then
$$
 |jB|\ \ge\ \min(p,j(m+1)).
$$
For this second bound, induct on $j$, starting at $j=1$. If $(j-1)B$ is full the result follows at once. Otherwise Cauchy–Davenport gives $|jB|\ge\min(p,j(m+1)-1)$. If $j(m+1)\ge p$, then $j(m+1)\ge p+1$ by parity, and this implies fullness. In the remaining regime, equality $|jB|=j(m+1)-1$ would force equality in Cauchy–Davenport with sumset size at most $p-2$ and both summand sets of size at least two. Vosper’s theorem would then make $B$ an arithmetic progression. This proves the bound.

First assume $D\ne 4$. Define $r=\lceil D/3\rceil$, $s=D-2r$, and $C=rB$. These choices satisfy $1\le s\le r$ and $D-r\ge D/2$. The growth bounds give
$$
 (D-r)B=\mathbb F_p,\qquad 3|C|>2p,\qquad 2|C|+|sB|>2p+1.
$$
Indeed, $|jB|\ge\min(p,2jk_0)$ in both parity cases, and $2Dk_0\ge 2p+2$. This proves the first two assertions. For the last, if $|C|=p$ then $|sB|\ge 2$. If $|C|<p$, then $2rk_0<p$ and $2sk_0\le 2rk_0$, so the lower bound is $2(2r+s)k_0=2Dk_0$.

Define $g:C\to H$ by taking the $f$-sum of an $r$-letter representation. Any two $r$-letter representations of a value have the same $f$-sum, since both can be completed to zero using the same $D-r$ letters. In particular $g(0)=0$ and $g|_B=f$.

For $x\in\mathbb F_p$ write $U_x=\{u\in C:u+x\in C\}$. On $U_x$ join distinct $u,v$ when $u+v+x\in -sB$. The two pairs $(u+x,v)$ and $(u,v+x)$ each consist of elements of $C$, and appending the same $s$-letter filler for their opposite sum produces two zero-sum words of length $2r+s=D$. Thus
$$
 g(u+x)-g(u)=g(v+x)-g(v)
$$
along each edge. The graph is connected. Otherwise some nonempty partition $Y,Z$ of $U_x$ would have $Y+Z+x$ disjoint from $-sB$. Cauchy–Davenport gives
$$
 |Y+Z|\ge |U_x|-1\ge 2|C|-p-1>p-|sB|.
$$
The disjointness contradicts this bound.

It follows that $F(x)=g(u+x)-g(u)$ is well-defined for every $x$, as each $U_x$ is nonempty. The inequality $3|C|>2p$ gives an element $z$ with $z,z+x,z+x+y\in C$ for every $x,y\in\mathbb F_p$, by the union bound on the three complements. Telescoping these three values of $g$ proves $F(x+y)=F(x)+F(y)$. For $x\in B$ choose $u=0$ to get $F(x)=f(x)$. This concludes the non-progression case for $D\ne 4$.

## Degree four

It remains to treat $D=4$ and $B$ a non-progression. Since $4k_0\ge p+1$, we have $|B|=m+1\ge (p+1)/2$. Cauchy–Davenport gives $2B=\mathbb F_p$.

Let $S=f(B)\subset H$. The restriction of $\pi$ to $2S$ is a bijection onto $\mathbb F_p$. To prove injectivity, take two pairs of letters of $B$ of the same weight. Append a common opposite pair, which exists by $2B=\mathbb F_p$. The resulting zero-sum words of length four have zero $f$-sum, so the original pairs have equal $f$-sum.

If the stabilizer $P=\{h\in H:2S+h=2S\}$ is nontrivial, it projects injectively by the bijection on $2S$. Its image is therefore the whole prime order group. As $0\in 2S$, the inclusion $P\subseteq 2S$ is equality by cardinality. Then $P$ contains $S$, which generates $H$, and $\pi$ is an isomorphism.

Suppose instead that $2S$ is aperiodic, meaning $P=\{0\}$. Kneser’s theorem gives
$$
 p=|2S|\ge 2|S|-1=2|B|-1\ge p.
$$
Thus $(S,S)$ is an aperiodic critical pair, to which Kemperman’s structure theorem applies in the abelian group $H$. In the quasi-periodic alternative for a non-elementary pair, $S$ contains a full coset of a nonzero subgroup $Q$. Indeed, the periodic parts in the partitions are unions of full $Q$-cosets, and if both were empty the residual pair would be the whole pair and would be elementary. Translating such a full coset by an element of $S$ places it in $2S$. Injectivity of $\pi$ on $2S$ forces $\pi|_Q$ to be injective, and primality forces $|Q|=p$. The coset is then all of $2S$, contradicting aperiodicity. [Kemperman’s theorem, Lev Theorem C and §3](https://arxiv.org/abs/math/0508179)

The remaining elementary alternatives are as follows.

- Type I has a singleton summand, whereas $|S|\ge 4$.
- Type II makes $S$ an arithmetic progression. Its common difference projects to a nonzero element because $\pi$ is injective on $S\subseteq 2S$. Hence $B=\pi(S)$ would be a progression.
- Type III makes $2S$ a full coset of a finite nontrivial subgroup and therefore periodic.
- Type IV makes $2S$ a coset of a finite subgroup $Q$ with one point removed. Then $|Q|=p+1$, so the homomorphism $\pi|_Q$ is trivial. The coset cannot project onto $\mathbb F_p$.

The aperiodic case is impossible. The periodic case gave $\pi$ an isomorphism, so $R=L$ also in degree four. This finishes the proof.
