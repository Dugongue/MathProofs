# No binary coarse-graining for the sixteen unresolved elementary rules

For each of the sixteen elementary cellular automata left unresolved by Israeli and Goldenfeld and by Song and Grochow, there is no nonconstant binary block projection to an elementary rule at any supercell size $N>1$. This completes the existence census **within the elementary-rule family**. The broader question of proper coarse-grainings to larger target alphabets has a different quantifier. [Israeli–Goldenfeld, §IV](https://guava.physics.ucsd.edu/~nigel/REPRINTS/2006/Israeli%20Coarse-graining%20of%20cellular%20automata%20PRE%202006%20%28PDF%29.pdf) · [Song–Grochow, §§II, IV.A and V](https://arxiv.org/pdf/2012.12153#page=8)

## Statement and model

Let $F$ be the cellular automaton associated with an elementary local rule $f : \{0,1\}^3\to\{0,1\}$. With spatial coordinate $i$, $(Fx)_i=f(x_{i-1},x_i,x_{i+1})$. Write $\mathcal A_N(u,v,w)$ for the middle length-$N$ word after $N$ updates on a concatenation of three length-$N$ words $u,v,w$. This local operation requires no boundary convention outside these $3N$ input cells. A binary exact coarse-graining consists of a nonconstant function $P : \{0,1\}^N\to\{0,1\}$ and an elementary local rule $b$ satisfying
$$
P\bigl(\mathcal A_N(u,v,w)\bigr)=b(P(u),P(v),P(w))
\qquad\text{for every } u,v,w.
$$
We prove there is no such pair when $N\ge2$ and
$$
f(a,b,c)=a+\alpha b+\beta c+bc+\gamma
$$
for arbitrary $\alpha,\beta,\gamma\in\mathbb F_2$. Addition in every Boolean formula below is modulo two. Reflection gives the same result for the right-permutive mirror rules.

## 1. The target is left-permutive

Use moving coordinates $G(x)_i=f(x_i,x_{i+1},x_{i+2})$. The local operation $\mathcal A_N$ consists of $(G^Nx)_i$ for $0\le i<N$ on $x=u v w$. This follows by shifting space by one per update, since the original CA commutes with shifts.

Each coordinate $(G^tx)_i$ depends only on $x_i,\ldots,x_{i+2t}$, and is $x_i$ plus a function of the other variables. Inductively the latter variables affect the two right inputs of the next local rule, while its left input retains the leftmost variable with coefficient one. Therefore with $v,w$ fixed the map $u\mapsto\mathcal A_N(u,v,w)$ is a bijection: solve for $u$ from right to left.

For any fixed $v,w$, the left side runs through both labels as $u$ varies, since $P$ is nonconstant. As $P(v),P(w)$ can take any pair of labels, the target has the form
$$
b(a,d,e)=a+k(d,e)
$$
for some binary function $k$.

## 2. A right-edge derivative of the source

Index the supercells by $0,\ldots,N-1$, and let $\ell$ be the largest index on which $P$ depends essentially. For a Boolean function, the Boolean derivative in a variable is the sum modulo two of its values when that variable is set to $0$ and $1$. It is itself independent of the differentiated variable. Let $\delta>0$ be the probability that $D_\ell P=1$ for independent uniform bits on the other coordinates. Consider the derivative in fine input coordinate $j=\ell+2N$.

Application of the local rule from depth $t$ to $t+1$ gives the product formula
$$
D_j (G^N x)_\ell=\prod_{t=0}^{N-1}
\bigl((G^t x)_{\ell+2(N-t)-1}+\beta\bigr).
$$
Indeed only the right input of each gate on the extreme right path can see $x_j$. The middle input is at coordinate $r_t=\ell+2(N-t)-1$ at depth $t$, and the derivative of the local rule in its right input is the middle input plus $\beta$.

The $N$ middle inputs in the product are jointly uniform independent bits under uniform fine input. To see this, fix all initial coordinates other than the distinct $x_{r_t}$. Each middle input $(G^t x)_{r_t}$ is $x_{r_t}$ plus a function only of later coordinates. Sorting the $r_t$ in decreasing order gives a bijection from the $N$ free bits to the $N$ middle inputs. Thus the edge-derivative product equals $1$ with probability exactly $2^{-N}$.

No middle output coordinate left of $\ell$ sees $x_j$, and coordinates to the right of $\ell$ are irrelevant to $P$. It follows that the Boolean derivative of the left side of the coarse-graining identity is the above product times $D_\ell P$ evaluated at the other effective output coordinates. Conditional on all fine inputs of index at least $\ell$, the output coordinates $0,\ldots,\ell-1$ are uniformly distributed by the same right-to-left bijection. The conditional probability that their $D_\ell P$ value is one is $\delta$. The edge-derivative product is fixed under this conditioning because all its initial inputs lie to the right of $\ell$. Therefore
$$
\Pr\!\left[D_j P\bigl(\mathcal A_N(u,v,w)\bigr)=1\right]=\delta\,2^{-N}.
$$

## 3. Every binary target has a different derivative frequency

On the right side only $P(w)$ can depend on $x_j$. Its derivative is $D_\ell P(w)$. Consequently the derivative probability for the right side is
$$
\delta\,\Pr_{v}\bigl[k(P(v),0)+k(P(v),1)=1\bigr].
$$
The product law follows because the independent words $v,w$ determine the two factors.

The derivative probability from the source is positive. In particular $k$ takes the value $1$ somewhere. Fix $v,w$ at a pair of labels where $k=1$. For this pair the bijective left-section map $u\mapsto\mathcal A_N(u,v,w)$ swaps the two $P$-fibers, so these fibers have equal size. Thus under uniform $v$, $P(v)$ is a fair bit. The last displayed probability after the factor $\delta$ can only be $0$, $1/2$, or $1$. The identity would require it to equal $2^{-N}$, which for $N>1$ is strictly between $0$ and $1/2$. This contradiction proves the theorem.

## 4. The sixteen rules

The left-permutive nonaffine local rules in the theorem have Wolfram codes
$$
30,\ 45,\ 75,\ 120,\ 135,\ 180,\ 210,\ 225.
$$
Their distinct reflections have codes
$$
86,\ 89,\ 101,\ 106,\ 149,\ 154,\ 166,\ 169.
$$
These lists follow by evaluating the eight coefficient triples and assigning to $(a,b,c)$ the bit with index $4a+2b+c$. They are exactly the reflection and state-conjugation orbits of $30,45,106,154$. Those are the four representatives in the Israeli–Goldenfeld statement. When $N=1$ a nonconstant $P$ is necessarily a bijection, so any resulting factor is just a relabeling of states. [Israeli–Goldenfeld, §IV](https://doi.org/10.1103/PhysRevE.73.026203)

The proof is uniform in $N$. A cutoff from finite experiments is unnecessary. Magiera and Dzwinel previously isolated the same four representatives through block size seven. Song and Grochow's search also goes through block size seven for elementary targets. Israeli and Goldenfeld describe a separate search strategy for targets with more than two labels, which the binary derivative-frequency argument by itself does not classify. [Magiera–Dzwinel, *Irreducible elementary cellular automata found*](https://doi.org/10.1016/j.jocs.2015.08.008) · [Song–Grochow, §IV](https://arxiv.org/pdf/2012.12153#page=6)



## 5. No proper quotient of any alphabet for the rule 154 orbit

For the four rules in the reflection and state-conjugation orbit of rule 154, one can allow every finite target alphabet. In this case a block map commuting with the dynamics is either constant or injective. This is stronger than the binary conclusion for this particular orbit.

Reflection reduces the proof to rule 210, with the moved local rule
$$
(Gx)_i=x_i+(1+x_{i+1})x_{i+2}.
$$
Let $P$ be a nonconstant block map onto a finite set $S$. Its image is the only part of the target alphabet needed. For each fixed middle and right word $v,w$, the left-section permutation $L_{v,w}:u\mapsto\mathcal A_N(u,v,w)$ descends to a permutation on $S$. Indeed it respects the fibers by the coarse-graining identity and its induced map is surjective. In particular, each such permutation and its inverse preserve the partition into fibers.

### Transitivity of the left sections

The following argument applies to every source in the theorem. Let $\Gamma$ be the permutation group generated by the left sections. For each $i$ between $0$ and $N$, the subgroup fixing coordinates $0,\ldots,i-1$ at every word acts transitively on the words with any given values at those coordinates. Here the case $i=N$ is trivial.

For the induction step choose $v,w$ and a value of the left word for which the edge derivative at output coordinate $i$ with respect to input coordinate $i+2N$ is one. Such a choice exists by the product computation in §2. The changed input bit is the $i$-th bit of $w$, so this gives two left sections $L,L'$. The permutation $L'L^{-1}$ fixes every output coordinate before $i$. Its change at coordinate $i$ depends only on the current suffix after $i$: the edge derivative depends only on initial coordinates after $i$, and the triangular inverse of $L$ recovers those left-word coordinates from the output suffix after $i$. At some such suffix the change is one. The induction hypothesis within fixed prefixes of length $i+1$ allows preparation of this suffix, flipping coordinate $i$ by $L'L^{-1}$ when desired, and then adjustment of the later coordinates. This proves the required transitivity for $i$.

In particular $\Gamma$ is transitive, and any two fibers of $P$ have the same size, since $\Gamma$ acts on the fibers by permutations.

### What a quotient label reveals

First the rightmost essential index of $P$ is $N-1$. Otherwise let that index be $\ell<N-1$, and consider again the change in the fine input bit $x_{\ell+2N}$ in the right word. The last pivot to the left in the edge product in §2 is $x_{\ell+1}$, in the ignored suffix of the left word. Choose the other initial variables to make all the other factors in the edge product one. Their values are independent of $x_{\ell+1}$. Varying this one pivot then toggles the edge activity at output coordinate $\ell$. It has no effect on the quotient label of the input left word. For the inactive value, every relevant output bit remains unchanged when the right-word bit is flipped. As the left prefix varies, $P(u)$ ranges over $S$, so the two corresponding target left sections must be equal. For the active value, the output coordinate $\ell$ is flipped and the preceding output coordinates are unchanged. By triangularity, their shared values can be made any given prefix by choosing the initial coordinates before $\ell$. Essentiality of $\ell$ now gives a prefix where the two output labels differ, contradicting equality of the target left sections.

With $\ell=N-1$, the edge activity for the last output coordinate depends only on $v,w$. In an active context the two source left sections obtained by flipping the last bit of $w$ differ by a global toggle $J$ of the last output bit, since all other output coordinates are unchanged. Therefore $J$ itself descends to a permutation $\tau$ of $S$, by composing one left section with the inverse of the other. Essentiality of the last bit makes $\tau$ nonidentity. It follows that the edge activity in each context $v,w$ is determined by $P(v),P(w)$: compare the two induced left sections with last labels $P(w)$ and $\tau(P(w))$. They are equal when the edge is inactive, and they differ by $\tau$ when it is active.

For rule 210 the extreme-edge factor at output position $i$ after $T$ steps is active exactly when the initial positions
$$
i+1,\ i+3,\ \ldots,\ i+2T-1
$$
are all zero. To prove this, order these positions from right to left as $r_t=i+2(T-t)-1$ for $0\le t<T$. At depth $t$, the middle input in the edge product is $(G^tx)_{r_t}$, which must be zero. At $t=0$ this is the first initial bit on the list. If the earlier initial pivots are zero, each position $r_s$ with $s<t$ stays zero up to time $s$, by induction on $s$: its right neighbor at distance two is the preceding pivot, which stays zero through the times used in those updates. Thus at position $r_t$ the update adds zero at every previous step, and the constraint there is exactly $x_{r_t}=0$. This proves the characterization. Apply it with $i=N-1$, $T=N$ and the right word zero. The pivots in the middle word are its even coordinates, starting at coordinate zero. Since the corresponding activity is determined by the quotient labels, $P(v)$ determines the predicate
$$
Z(v)=\mathbf 1\{\text{every even coordinate of }v\text{ is zero}\}.
$$

### A singleton fiber

Suppose $P(x)=P(0^N)$ for some nonzero word $x$. Its even coordinates are all zero. Let $k$ be its rightmost coordinate equal to one, so $k$ is odd. Put $i=k-1$, choose $T=N2^r$ with $2^r>N$, and put a single pulse at fine position $j=i+2T$. Compare two infinite initial configurations. One is zero apart from that pulse. The other has the same pulse and also the word $x$ in positions $0,\ldots,N-1$. Their blockwise quotient labels coincide. Applying the coarse-graining identity $T/N$ times yields equal labels at time $T$, and the shift to moved coordinates is by $T$, a multiple of the block length. Therefore their first length-$N$ outputs of $G^T$ have equal $P$-labels.

For the first input the odd stream remains zero, and the even stream evolves by $e_a\mapsto e_a+e_{a+1}$. Its output at even position $i'$ is therefore the coefficient of the pulse in the binomial expansion of this shift rule. Within the first length-$N$ output it equals one at $i'=i$, where this coefficient is $\binom{T}{T}$, and zero at all other even positions. At positions before $i$ the pulse is outside the dependency range. At even positions after $i$ the relevant coefficient is $\binom{T}{T-(i'-i)/2}$, which is zero modulo two. The latter follows from $(1+z)^T=(1+z^{2^r})^N$ over $\mathbb F_2$ and $0<(i'-i)/2<2^r$.

For the second input, at even positions after $i$ the initial word's nonzero coordinates are outside the dependency range. Those outputs agree with the first input. At even positions before $i$ the pulse is outside the dependency range, and the even stream of the pulse-free word stays zero, since an all-zero even stream is preserved by the rule regardless of the odd stream. At $i$ the pulse-free output is also zero. The pulse does not change it because one of the required edge pivots is $x_k=1$. Thus every even output of the second input is zero. The two outputs have opposite $Z$-values despite equal $P$-labels, a contradiction.

Consequently the fiber of $0^N$ is a singleton. Transitivity forces all fibers to be singletons. This excludes every proper nonconstant coarse-graining of rule 210 and, by state conjugation and reflection, of all four rules in the orbit of rule 154. The all-alphabet problem for the other three orbits is not resolved here.
