# Bounded-register programs and shallow circuits for Cayley group membership

**Theorem.** Let $G=\langle X\rangle$ be a finite group, put $L=\max(2,\log_2|G|)$, and let $\mathcal T(G)$ be its nonabelian composition factors. Write
$$
D(G)=\max(\{1\}\cup\{\operatorname{diam}(T):T\in\mathcal T(G)\}),
\qquad
\theta(G)=\max\left(\{1\}\cup\left\{
\frac{\log\operatorname{diam}(T)}{\log\mu(T)}:T\in\mathcal T(G)
\right\}\right),
$$
where diameter is the maximum symmetric Cayley diameter over generating sets, and $\mu(T)$ is the least faithful permutation degree. Every element of $G$ has a straight-line program over $X\cup X^{-1}\cup\{1\}$ of width at most eight and length
$$
O\bigl(L^{26+5\theta(G)}D(G)\bigr).
$$
The bound is independent of the exponents of the abelian sections. For nonempty $X$, programs with only generator loads and multiplication over $X$ have width at most ten and length $O(L^{27+5\theta(G)}D(G))$.

**Consequences.** Cayley-table subgroup membership has logspace-uniform polynomial-size unbounded-fan-in circuits of depth $o(\log n)$ on arbitrary groups of order $n$. The depth is $O(\log\log n)$ whenever the generated subgroup has nonabelian composition factors of uniformly bounded rank. This is a promise on the generated subgroup, so the ambient table can describe a larger group. Babai's diameter conjecture for nonabelian finite simple groups would give the $O(\log\log n)$ depth bound on all finite groups. This gives an unconditional family and a conditional general answer to the second part of Stober–Thumm–Weiß Question 39. [Question 39](https://arxiv.org/html/2601.04747v2#S12).

## 1. A normal subgroup whose generators and quotient have short words

Use the proof of Eberhard–Maini–Sabatini–Tracey Lemma 6.1. The part before the solvable-radical diameter estimate supplies the following data for every nonsolvable $G=\langle X\rangle$.

1. Pass to $G/R(G)$, where $R(G)$ is the solvable radical. Proposition 5.4 gives a nonidentity element of the socle represented by a word of length at most $O(L^{18+5\theta(G)})$ over the quotient generators. Lift its word to $g\in G$.
2. Set $N=\langle g^G\rangle$, the normal closure of $g$. Lemma 3.1 gives generators $Z$ for $N$ represented by $X$-words of length $M=O(L^{18+5\theta(G)})$. Its extra length is at most twice the maximum length of a subgroup chain in $N$, hence at most $2\log_2|G|$.
3. The image of $N$ in $G/R(G)$ is nontrivial and normal in its socle. Thus the image is a product of nonabelian simple composition factors of $G$. The radical $R(N)$ equals $N\cap R(G)$: the intersection is solvable normal in $N$, and $R(N)$ is characteristic in $N$, hence solvable normal in $G$. The direct-product diameter bound of Theorem 5.5 gives
$$
D'=\max(1,\operatorname{diam}(N/R(N)))=O(L^4D(G)).
$$
Indeed the number of factors is at most $\log_2|G|$, and their ranks are $O(\log_2|G|)$ under the conventions of that paper. Since $N$ is nonsolvable, $G/N$ has strictly fewer nonabelian composition factors than $G$.

These steps specify existence of short words. The circuit below will not need to find $N,Z$, or their quotient factors. [Proposition 5.4, Theorem 5.5, and Lemma 6.1](https://arxiv.org/html/2604.15303#S5).

## 2. Solvable kernels use bounded registers

Write $Q=N/R(N)$ and $\pi:N\to Q$. Choose, for each $a\in Q$, a word $u_a$ over $Z\cup Z^{-1}$ of length at most $D'$ with image $a$, taking $u_1=1$. The elements
$$
u_a z u_{a\pi(z)}^{-1}\qquad(a\in Q,\ z\in Z\cup Z^{-1})
$$
generate $R(N)$. To verify this, read a word in $Z\cup Z^{-1}$ representing a kernel element. If the successive quotient prefixes are $a_0=1,a_1,\ldots,a_j=1$, the corresponding products $u_{a_{i-1}}z_i u_{a_i}^{-1}$ telescope to the word's value. Every displayed generator has signed $X$-length at most $(2D'+1)M$.

For $h\in N$, let $a=\pi(h)$ and $v=u_a^{-1}h\in R(N)$. By Stober–Thumm–Weiß Theorem 21, $v$ has a width-four program of length $O(L^3)$ over the Schreier generators, with an identity load available for the trivial cases. Replace each such load by its short signed $X$-word evaluated with two scratch registers. This produces $v$ in width six and length $O(L^3 M D')$. Preserve $v$ while evaluating $u_a$ with two scratch registers, and multiply $u_av=h$. Thus every element of $N$ has a width-six program of length
$$
O(L^3MD')=O(L^{25+5\theta(G)}D(G)).
$$
The identity and inverses of fixed letters can be treated as alphabet constants at this stage. [Stober–Thumm–Weiß, Theorem 21](https://arxiv.org/html/2601.04747v2#S8.SS2).

## 3. The cost of successive quotients adds

Take a width-eight program for the image of $t\in G$ in $G/N$, and lift every alphabet load to a preimage in $X\cup X^{-1}\cup\{1\}$. The same instructions give some $r\in G$ with $rN=tN$. Retain $r$ in one register and run the width-six program for $r^{-1}t\in N$ in disjoint registers. Multiply the results.

In this induction both $t$ and the program for its quotient image are fixed, so $r^{-1}t$ is a fixed element for which the preceding existence theorem applies. The quotient program runs to completion before space is reserved for its result. Width therefore obeys a maximum, while length obeys a sum. There are at most $\log_2|G|$ nonsolvable stages and the final solvable quotient uses Theorem 21. Parameters $\theta,D,L$ of each quotient are bounded by those for $G$, by Jordan–Hölder and monotonicity of order. The announced bound follows. For unsigned programs with $X\ne\varnothing$, use $x^{\operatorname{ord}(x)-1}$ for $x^{-1}$ when $\operatorname{ord}(x)>1$, $x$ itself otherwise, and $x^{\operatorname{ord}(x)}$ for the identity. Repeated squaring adds at most two scratch registers and multiplies length by $O(L)$.

## 4. From program length to circuit depth

Let the ambient table have $n$ elements and let the supplied generator mask be $X$. Test the trivial empty-generator case by equality to the identity. A configuration is an eight-tuple of elements or empty register markers. There are $O((n+1)^8)$ configurations. In constant depth form the adjacency relation for any single allowed alphabet load or register product, or for a self-loop. Multiplication is a table lookup. The identity and the inverse of each label are first-order definable from the table, so the signed generator mask is also available in constant depth.

If length $B$ suffices, Boolean-matrix squaring of this adjacency relation $\lceil\log_2 B\rceil$ times tests whether any configuration containing a specified target is reachable from the all-empty state. A squaring is an OR over intermediate configurations of ANDs of two relation entries. It has constant depth, and $\operatorname{poly}(n)$ gates including all pairs. Self-loops permit padding. The same construction can output all membership bits at once. Every accepted target is in $\langle X\rangle$ regardless of the promise, and the program bound gives completeness under the stated hypotheses. The wiring is logspace uniform by enumerating register tuples, intermediate tuples, and layer indices with counters. This is the explicit configuration form of the general bounded-width-to-depth simulation. [Fleischer, section 3.2](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CCC.2018.25).

For fixed rank, the simple-group diameter results summarized in equations (1.1)–(1.2) and their surrounding text give $D(\langle X\rangle)\leq(\log n)^{O(1)}$ and $\theta(\langle X\rangle)=O(1)$; the same follows for all ranks if Babai's conjecture holds, using $\theta_1\le 2\theta_2$ of the diameter paper. So $\log B=O(\log\log n)$.

For arbitrary rank put $b=\max(2,\lceil\log_2\log_2(n+4)\rceil)$. For an alternating factor $A_m$, $m\leq 2+\log_2|A_m|$ and Eberhard–Maini–Sabatini–Tracey equation (1.1) gives $\log\operatorname{diam}(A_m)=O(b^4\log b)$; it also bounds $\theta_1(A_m)=O(b^3\log b)$, using $\mu(A_m)=m$. For a simple classical factor $T$ in dimension $d$ over $\mathbf F_q$, outside finitely many small cases we have
$$
\log |T|\ge c d^2\log q,\qquad \mu(T)\ge c' q^{d/2}
$$
for absolute positive constants, by the classical group order formulas and the minimal permutation degree bound used in Corollary 1.6 of the diameter paper. The Halasi–Maróti–Pyber–Qiao bound, as stated in equation (1.2) there, gives
$$
\log\operatorname{diam}(T)
 \le C(d\log q)(\log(d+1))^2
 \le C'\log |T|/\sqrt d .
$$
The same estimate and the lower bound for $\mu(T)$ give $\theta_1(T)=O((\log(d+1))^2)=O(b^2)$. Bounded-rank exceptional and sporadic cases contribute $O(b)$ to the log diameter and $O(1)$ to $\theta$.

For any rank cutoff $r$, classical factors of rank at most $r$ have log diameter at most $K(r)b$, by the bounded-rank theorem, whereas the ones of rank exceeding $r$ have log diameter at most $C'\log n/\sqrt r$ since $d$ is at least the rank up to an absolute constant, which can be absorbed into $C'$. Fixing $r$ and then sending it to infinity shows that $\log D=o(\log n)$ uniformly in the abstract groups of order at most $n$. The factor $L^{26+5\theta}$ contributes $O(b^4\log b)=o(\log n)$ to $\log B$.

The rate can be chosen logspace-computable. The bounded-rank theorem of Pyber–Szabó supplies a computable nondecreasing integer majorant $K(r)$, including the finitely many exceptions. For effectiveness, see the description of the tower-type constants in Bajpai–Dona–Helfgott, section 1.2. Let $\ell=\lfloor\log_2 n\rfloor$. For successive integer $r\le\lfloor\sqrt\ell\rfloor$, compute $K(r)$ subject to limits of $n$ steps and $\ell$ space, and accept the cutoff while the simulation succeeds and the bound is at most $\lfloor\sqrt\ell\rfloor$. Use the last accepted cutoff $r(n)$. If no cutoff succeeds, use $\lceil\log_2(n+1)\rceil$ layers, since ordinary signed words of length at most $n-1$ reach the entire generated subgroup and use two registers. This procedure is logspace and $r(n)\to\infty$ because every fixed finite prefix eventually fits all limits. When a cutoff succeeds, taking a fixed large constant times
$$
 b^5+(\lfloor\sqrt\ell\rfloor+1)b+
 \left\lceil\frac{\ell}{\max(1,\lfloor\sqrt{r(n)}\rfloor)}\right\rceil ,
$$
therefore gives the claimed logspace-uniform polynomial-size family with depth $o(\log n)$. Computing the layer bound uses only integer counters and square-root rounding. [Diameter inputs and references, equations (1.1)–(1.2) and Corollary 1.6](https://arxiv.org/html/2604.15303#S1). [Effectiveness of the bounded-rank bounds](https://arxiv.org/html/2308.09197#S1.SS2).

## 5. Semigroups and scope

Stober–Thumm–Weiß Theorem 31 transfers the group-program length bound to every efficiently compressible pseudovariety of finite semigroups, adding at most three registers and an additive $O(\log n)$ length term. The group bound $n^{o(1)}$ therefore gives logspace-uniform polynomial-size depth $o(\log n)$ membership circuits for each of these pseudovarieties as well. Use the same register graph with only input-generator loads and multiplication. A polynomially encoded state records an explicit multiplication-table element or an empty register marker. The known group length majorant supplies a uniform bound on the number of squarings after a constant-factor increase in program length. A nonempty generated semigroup uses nonempty programs, so acceptance starts from all registers empty and requires an actual target in a register. Thus the bounded-rank consequence also applies to every such pseudovariety with a uniform bound on the ranks of its nonabelian group composition factors. The conditional consequence of Babai's conjecture applies to every efficiently compressible pseudovariety. The Cayley-table algorithm does not require a factorization, the solvable radical, a normal series, or a promised rank bound as extra input data. To obtain the sharper depth, its circuit family uses a fixed bound on the ranks of the generated subgroups it is required to cover.

The ingredients are the short normal generators and product-diameter bound of Eberhard–Maini–Sabatini–Tracey, the bounded-width programs for solvable groups of Stober–Thumm–Weiß, and the configuration simulation from Fleischer. The new step here is the bounded-register use of solvable kernels and additive composition of the nonsolvable layers, which eliminates the exponent factor without a new Cayley diameter theorem. For example, the ordinary Cayley diameter of a large cyclic group with its canonical generator is linear in its order, while its bounded-register programs are logarithmic. The unrestricted $O(\log\log n)$ bound remains conditional here. This is an informal argument based on the cited results, and publication priority for the combination is unestablished.
