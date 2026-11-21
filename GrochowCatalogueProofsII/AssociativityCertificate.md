# GP-0459 · Bit certificates for associativity of Latin tables

**Theorem.** In the binary-label bit-query model with a promise that the table is Latin, the worst-case certificate complexity of deciding associativity is $\Theta(n^2\log n)$ on the sequence $n=2^k$, $k\ge3$. The positive certificate for the displayed XOR table needs at least $n^2 k/4$ bits. For all orders a full-table certificate gives the matching general worst-case upper bound. Every negative instance at order $n$ has a certificate using at most $2\lceil\log_2 n\rceil+2$ bits.

Let the labeled domain be $V=F_2^k$ with its ordinary $k$-bit labels. The table of vector addition is associative. For each coordinate basis direction $t$, partition the row labels into pairs $\{a,a+t\}$ and independently partition the column labels into pairs $\{b,b+t\}$. Every product of a row pair and a column pair is a Latin intercalate. Its entries repeat the two symbols $a+b,a+b+t$ in opposite order. In one chosen intercalate, interchange the two symbols at all four cells. Every row and column still contains each symbol once. The only changed bit at each of the four cells is the coordinate of $t$.

The changed table fails associativity. Write $A$ and $B$ for the flipped row and column pairs, respectively. Choose $x\in A$, $y\in B$, and $z$ outside $B\cup(y+B)$, which is possible since that union has size at most four. For the modified operation $\star$, the pair $(x,y)$ is flipped. Since $z\notin B$, neither $(x\star y,z)$ nor $(y,z)$ is flipped. Since $y+z\notin B$, the pair $(x,y\star z)$ is unflipped as well. Thus
$$
(x\star y)\star z=x+y+t+z,\qquad
x\star(y\star z)=x+y+z .
$$
For fixed $t$, the $(n/2)^2$ intercalates used in this argument are disjoint in cell coordinates. Across directions $t$, their changed bit positions are disjoint even when their cells overlap. A certificate accepting the XOR table must therefore query at least one bit from each of the $k n^2/4$ pairwise disjoint supports. Each produces its own Latin nonassociative table if missed. This proves the certificate lower bound.

The same controls give the randomized query lower bound $q\ge(1-2\epsilon)kn^2/4$ for worst-case query budget $q$ and error at most $\epsilon<1/2$. Couple a run on the XOR table and on a uniformly chosen perturbed table using identical coins. Unless the XOR run reads a bit in the altered support their transcripts agree. Every coin sequence queries at most $q$ of the disjoint supports. The probability of differing acceptance is therefore at most $q/(kn^2/4)$, while correctness requires a difference of at least $1-2\epsilon$ between the two acceptance probabilities.

For a negative certificate, give a triple violating associativity. Display the two complete output labels at $(x,y)$ and $(y,z)$, then one bit in which the resulting two outer products differ. The first two labels identify the positions of those outer products. This makes the required check with the claimed bit count even when some cells coincide.

The construction uses the multiplication-table bit model of Grochow–Kardeş–Levet. It concerns associativity of a single table under a Latin promise, with intercalate perturbations as explicit negative witnesses. The earlier MathProofs Cayley circuit argument instead supplies lower bounds for comparing two valid group tables. [Cayley circuit model](https://arxiv.org/html/2608.26257v2) · [Earlier MathProofs partial-table argument](https://github.com/Dugongue/MathProofs/blob/ef3248c44a28fcc2e97f90392942083b33dce716/SimpleQuasigroupsAndCircuitBounds/GroupIsomorphismCNF.md)
