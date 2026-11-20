# Sharp simultaneous matrix multiplication from nonmixed-gap packings

A single translated tile packing controls a two-coordinate family of simultaneous matrix multiplications. The exact finite capacity in this family is computable by a transfer matrix. At the upper density bound, the nonmixed-gap packing proof of Davis and Astra gives a smaller description of **every** optimal family, including moduli not divisible by its character modulus.

## The shear construction

Let \(X,Y,Z\) be finite abelian groups, written additively. For each index \(i\), take labels \(x_i\in X,y_i\in Y\) and tiles \(S_i\subset X,T_i\subset Y\). Assume \(S_i\ne\varnothing\) and \(0\in T_i\). In \(X\times Y\times Z\) take
\[
A_i=(x_i+S_i)\times\{y_i\}\times\{0\},\quad
B_i=\{0\}\times(y_i+T_i)\times\{0\},\quad
C_i=\{0\}\times\{0\}\times Z.
\]
These triples have the simultaneous triple-product property (STPP) if and only if the \(x_i+S_i\) are pairwise disjoint and the \(y_i+T_i\) are pairwise disjoint. Thus they realize all matrix multiplication tensors \(\langle |S_i|,|T_i|,|Z|\rangle\) simultaneously in the same group algebra.

Indeed, a mixed equation \((a_i-b_i)+(b_j-c_j)+(c_k-a_k)=0\) reads
\[
x_i+u=x_k+w,\qquad y_j+t=y_k+s,\qquad p=q,
\]
with \(u\in S_i,w\in S_k,s\in T_i,t\in T_j,p,q\in Z\). The first packing forces \(i=k\). The second then forces \(j=k\). Cancellation gives \(u=w,s=t,p=q\), proving even the within-triple uniqueness. If the first packing fails, choose an overlapping pair \(i,k\), set \(j=k\), and use \(s=t=0\) and \(p=q\). If the second fails, choose an overlapping pair \(j,k\), set \(i=k\), and use the same \(S_k\) element in the first equality and \(p=q\). Each failure yields an actual mixed collision. The companion Lean file proves this equivalence over arbitrary additive commutative groups.

## The cyclic nonmixed-gap family

Take \(X=Y=\mathbb Z/N\), let \(a>b>0\) be coprime, and let \(k,m\ge1\). Put
\[
S=\{0,a,\ldots,ka,ka+b,\ldots,ka+mb\},\quad
D=ka+mb,\quad s=k+m+1 .
\]
Use common tiles \(S_i=T_i=S\) in the shear construction. Assume \(N>D\), so the tile has \(s\) distinct residues. The set of positive differences is
\[
F=\{ia+jb:0\le i\le k,\ 0\le j\le m,\ i+j>0\}.
\]
All such combinations occur by taking appropriate endpoints across the turn, including endpoints on either arm. A center set \(A\subseteq\mathbb Z/N\) packs precisely when its periodic lift to \(\mathbb Z\) avoids \(F\).

Write \(a-b=sd+r\), with \(0<r<s\), and define the critical window \(Q\), its occupancy \(H\), the other window \(Q'\), and \(\delta\) by
\[
(Q,H,Q')=
\begin{cases}
(D+b,\ b+kd,\ D+a)&1\le r\le m,\\
(D+a,\ a-m(d+1),\ D+b)&m<r<s,
\end{cases}\qquad \delta=H/Q.
\]
This covers both nontiling branches. The finite-state formula below applies also when \(r=0\), but the classification using \((Q,H)\) concerns \(r\ne0\).

Let \(\alpha(N)\) be the maximum possible number of matrices \(\langle s,s,|Z|\rangle\) in this shear construction. By the shear equivalence, it is exactly the maximum size of an \(F\)-avoiding center set on the circle. In particular, \(\alpha(N)\le\lfloor N\delta\rfloor\), with equality to \(N\delta\) whenever \(Q\mid N\). For an explicit packing modulo \(Q\), exchange \((a,k)\) and \((b,m)\) if \(r>m\), then recompute the quotient and remainder. In this orientation \(1\le r\le m\), and
\[
Q=sH+kr,\qquad aH-b(H+r)=dQ .
\]
Choose \(U,V\in\mathbb Z\) with \(Ua+Vb=1\), let \(P=U(H+r)+VH\), and choose all centers \(x\) for which \(Px\bmod Q\in[0,H)\). Each forbidden difference maps into \([H,Q-H]\), while image differences of chosen centers have distance from zero less than \(H\). If \(g=\gcd(P,Q)\), then \(g\mid H\) by \(bP\equiv H\bmod Q\), so the inverse image has exactly \(H\) points even when the character is not injective. The upper bound follows from the local inequalities explained below.

### All families meeting the density bound

Put \(G=\gcd(N,Q)\), \(L=N/G\), and \(K=HG/Q\). When \(K\) is integral, let \(\mathcal U\) consist of the \(K\)-element subsets of \(\{0,\ldots,G-1\}\) containing zero and avoiding \(F\) internally. When \(K\) is nonintegral, no family has \(N\delta\) copies.

When \(K\) is integral, **every** packing of size \(N\delta\) is obtained by choosing an anchor \(x\in\mathbb Z/N\), together with an indexed cyclic word \(W_0,\ldots,W_{L-1}\) in \(\mathcal U\), and taking the blocks \(x+jG+W_j\). The exact compatibility condition is
\[
tG+v-u\notin F
\quad
(1\le t\le\lceil D/G\rceil,\ u\in W_j,\ v\in W_{j+t}),
\]
with word indices interpreted cyclically. Conversely every such word gives a packing of size \(N\delta\). The two axes can use any two of these packings and any bijection between their centers. This classifies the rate-achieving families, and gives a finite criterion for their existence even when \(Q\nmid N\).

Construct a finite directed graph with memory \(\lceil D/G\rceil\) over \(\mathcal U\) by shifting in one block at a time and imposing exactly the displayed constraints. More explicitly a state records that many consecutive blocks with all pair tests internal to the state satisfied. An edge is permitted when the states overlap on their common blocks and the combined sequence, with one extra block, passes all tests. Let \(M\) be its zero-one adjacency matrix. Existence of an \(L\)-block word is exactly \(\operatorname{tr}(M^L)>0\). A closed walk with a distinguished start determines a unique indexed cyclic word, including when the word period is shorter than the memory, because each entry of the memory is the corresponding cyclic predecessor. Conversely every word defines that walk.

To count actual center sets, order each \(W_j\) increasingly and set
\[
J(W)=\{(e,p):\text{ the element in position }e\text{ of every }W_j\text{ equals }p\},
\]
with positions starting at zero. The number of center sets meeting the density bound is
\[
R(N)=G\sum_W \frac1{|J(W)|},
\]
where the sum is over the indexed valid words. This also gives an ordinary trace formula if desired. Let \(\mathcal E\) be the set of possible position-and-residue pairs excluding \((0,0)\). For \(A\subseteq\mathcal E\), restrict the allowed blocks to those satisfying every pair in \(A\) and use the resulting matrix \(M_A\). Then
\[
R(N)=G\sum_{A\subseteq\mathcal E}\frac{(-1)^{|A|}}{|A|+1}\operatorname{tr}(M_A^L).
\]
For fixed parameters and \(G\), the state dimensions do not grow with \(N\). If \(N>2D\), the number of unordered shear families with \(t=N\delta\) copies is \(R(N)^2t!\). This counts actual subset triples, since \(y_i\) is given by the constant second coordinate of \(A_i\), and \(x_i\) is uniquely determined by \(x_i+S\). Indeed the latter has a unique largest cyclic gap, of length \(N-D>D\), so the only translation preserving it is zero.

### Why a rate-achieving word has an anchor

The local ingredient from Davis–Astra is the following count. For a center at zero let \(J_1,C_1\) count centers in \([0,D+b)\) and \([0,D+a)\). There is an integer \(z\) such that
\[
J_1\le b+kz,\qquad C_1\le a-mz.
\]
For completeness, lift each center \(t\in[0,D+a)\) to \((u,v)\in\mathbb Z^2\) with \(au-bv=t\). Choose its unique representative of weight \(mu+kv\in[0,D)\); the shift \((b,a)\) adds \(D\) to the weight. Append endpoint \((b,a)\), also of height zero. For any oriented displacement \((u',v')\) of nonnegative weight between distinct lifts, either both coordinates are positive, or it has type \(X\) with \(v'\le0,\ u'\ge k+1,\ v'\ge1-m\), or it has type \(Y\) with \(u'\le0,\ v'\ge m+1,\ u'\ge-k\). For type \(X\), \(u'\le k\) would force \(-v'\le m\) by the weight inequality and give a forbidden difference. Once \(u'\ge k+1\), a value \(v'\le-m\) would give a height increase at least \(D+a\). For type \(Y\), \(v'\le m\) likewise gives a forbidden difference, and once \(v'\ge m+1\), \(u'\le-k-1\) would make the height drop by more than \(D+a\). The only displacement between copies of the same center is \((b,a)\), covered by the positive case. Every allowed displacement has strictly positive weight.

Sort by weight. There are \(C_1\) steps from \((0,0)\) to \((b,a)\). With \(z\) the number of \(Y\) steps minus the number of \(X\) steps, the lower bounds on the second coordinates give \(a\ge C_1+mz\). The first-coordinate bounds give \(b\ge C_1-kz\) apart from a loss of one at each exceptional \(Y\) step with \(u'=-k\). Such a step drops in height by at least \(D+b\), so its starting center lies in \([D+b,D+a)\). There are at most \(C_1-J_1\) exceptions. This gives \(b\ge J_1-kz\).

When \(r\le m\), \(z\le d\) gives at most \(H\) centers in the critical window. If \(z\ge d+1\), the other window has at most \(b+(k+1)d\) centers, since \(C_1\le a-m(d+1)\) and \(r\le m\). This count is strictly less than \(\delta Q'\), because \(H(D+a)-(b+(k+1)d)(D+b)=br>0\). When \(r>m\), \(z\ge d+1\) gives at most \(H\) in the critical window. If \(z\le d\), the other window has at most \(a-(m+1)(d+1)\) centers, since \(J_1\le b+kd\) and \(r\ge m+1\). This is strictly less than \(\delta Q'\), because \(H(D+b)-(a-(m+1)(d+1))(D+a)=a(s-r)>0\).

On a periodic lift, use the following deterministic walk from any site. At an empty site step one. At a center, step \(Q\) if its forward \(Q\)-window contains at most \(H\) centers, and otherwise step \(Q'\). Each traversed half-open interval has density at most \(\delta\). The empty steps and the \(Q'\) steps are strict. The walk mod \(N\) eventually follows a directed cycle, along which the total traversed length is a positive multiple of \(N\). It follows that every periodic packing has density at most \(\delta\). In an equality packing, every interval on the recurrent cycle must be tight. Therefore every cycle step is \(Q\), starts at a center, and sees exactly \(H\) centers. Its orbit is an entire coset \(x+G\mathbb Z\) modulo \(N\).

Partition the circle into \(G\)-blocks starting at \(x+jG\). Write \(c_j\) for the count in such a block. Every block begins at a center, and a window of \(Q/G\) successive blocks has total \(H\). Subtracting successive window sums gives \(c_{j+Q/G}=c_j\). Since \(\gcd(Q/G,L)=1\), all block counts are \(K\). This proves necessity of the anchored description. Conversely the compatibility conditions exclude every pair at a forbidden distance. A pair separated by \(t\) blocks has positive difference at least \((t-1)G+1\), so a larger \(t\) needs no test. Counting the blocks then gives density \(\delta\).

For the count, fix one anchored representation at \(x\). Any other candidate anchor is \(x+jG+p\) with \(0\le p<G\). Every shifted block begins at a center precisely when \(p\) occurs in every \(W_j\). Its shifted block count is
\[
K-|\{u\in W_j:u<p\}|+|\{u\in W_{j+1}:u<p\}|.
\]
All shifted counts equal \(K\) if and only if the position of \(p\) in the ordered block is fixed. Thus the exact anchor multiplicity of this packing is \(L|J(W)|\). Count each pointed packing with reciprocal of this multiplicity. There are \(N\) choices of initial point, giving the factor \(N/L=G\). To turn the weighted sum into traces, use
\[
\frac1{|J|}=\int_0^1(1+(z-1))^{|J|-1}\,dz=
\sum_{A\subseteq J\setminus\{(0,0)\}}\frac{(-1)^{|A|}}{|A|+1}.
\]
A trace of \(M_A^L\) counts exactly the words with the prescribed common pairs \(A\).

### Exact finite capacity even off the density bound

Let the states be binary words of length \(D\) whose selected sites avoid \(F\) internally. For each state shift in \(b\in\{0,1\}\) and delete the oldest bit. If \(b=1\), require every bit at positive distance \(f\in F\) behind the new bit to be zero. Put weight \(z^b\) on the resulting edge, and let \(B(z)\) be the polynomial adjacency matrix. Then
\[
\operatorname{tr}(B(z)^N)=\sum_{\substack{A\subseteq\mathbb Z/N\\ A\text{ packs }S}}z^{|A|}.
\]
Indeed the appended bits on a rooted closed walk give the indicator in the fixed cyclic coordinates. The shift rule determines every state uniquely from the preceding \(D\) bits. Conversely the indicator yields precisely this walk. Thus the degree of the trace is \(\alpha(N)\), and its leading coefficient is the exact number of maximizing center sets. Equivalently one can take max-plus powers with weights \(b\) and read the maximum diagonal entry. This computes actual finite capacity whether or not \(N\delta\) is attained. For \(N>2D\), if the leading coefficient is \(c\), the number of unordered maximum shear families is \(c^2\alpha(N)!\).

There is also an eventual affine periodicity result. Truncating a \(Q\)-periodic optimal pattern to \(Q\lfloor(N-D)/Q\rfloor\) consecutive sites leaves a seam longer than all forbidden distances. It follows that
\[
0\le HN-Q\alpha(N)\le H(D+Q-1).
\]
Normalize each finite-state edge weight to \(Qb-H\). Every closed walk has nonpositive normalized weight, since its periodic infinite pattern has density at most \(\delta\). The character pattern gives at least one zero-weight simple directed cycle by cycle decomposition. Let \(P_0\) be the least common multiple of the lengths of all simple zero-weight cycles. If the graph has \(M_0\) states, a closed walk of length \(N>M_0H(D+Q-1)\) attaining \(\alpha(N)\) must have a zero-weight simple cycle in a decomposition. Otherwise there are at least \(N/M_0\) strictly negative integer-weight simple cycles, exceeding the deficit bound. At a vertex of this zero-weight cycle visited by the original walk, insert it enough times to add length \(P_0\), leaving normalized weight unchanged. Hence the nonnegative integer deficit is eventually nonincreasing along each residue class modulo \(P_0\). Each class stabilizes, proving
\[
\alpha(N+P_0)=\alpha(N)+P_0H/Q
\quad\text{for all sufficiently large }N.
\]
The increment is an integer because each zero cycle has integer weight in the original edge counts.

### Examples

For \(a=4,b=1,k=1,m=2\) the critical pair is \((Q,H)=(10,2)\). At \(N=15\) the integral density bound is three, but anchors would be spaced by \(G=5\), a forbidden distance. The actual maximum is two, attained by centers \(0,3\). For \(a=3,b=1,k=2,m=1\) the pair is again \((10,2)\), and the modulus \(N=15\) does attain three, using \(0,5,10\). Thus the narrowed equality criterion is sensitive to the tile and not just the density fraction.

For \(a=5,b=3,k=m=2\), all density-bound achievers on \(\mathbb Z/(19L)\) are \(19\)-periodic, and there are exactly **38** for every integer \(L\ge1\). Here \(D=16,Q=19,H=3\), and the allowed anchored blocks have three entries. The adjacent anchors zero and 19 force each inner entry into \(\{1,2,4,15,17,18\}\). Test the distance between the two inner entries to obtain the following table. Successors are precisely the blocks for which all \(19+v-u\) pass the forbidden-distance test.

| Block number | Block | Successor block numbers |
| --- | --- | --- |
| 0 | \((0,1,2)\) | 0, 1, 2, 3, 4, 5, 6, 7 |
| 1 | \((0,1,15)\) | 6, 7 |
| 2 | \((0,1,18)\) | 2, 7 |
| 3 | \((0,2,4)\) | 3, 4, 5, 6, 7 |
| 4 | \((0,2,17)\) | 4, 6, 7 |
| 5 | \((0,4,18)\) | 7 |
| 6 | \((0,15,17)\) | 6, 7 |
| 7 | \((0,17,18)\) | 7 |

The block number is nondecreasing along every edge, and precisely six blocks have self-loops. Thus every closed walk repeats a single block. Each such word has three common position-and-residue pairs, giving \(19\cdot6/3=38\) unpointed center sets. Equivalently they are the \(19\) translates of each of \(\{0,1,2\}\) and \(\{0,2,4\}\), repeated cyclically. The tile has trivial translation period for \(L\ge2\) by the unique gap test. For \(L=1\) it has trivial period since the modulus is prime and the tile is proper and nonempty. There are therefore exactly \(38^2(3L)!\) unordered maximum shear families of \(3L\) copies of \(\langle 5,5,|Z|\rangle\).

### Scope and provenance

The simultaneous-realization interpretation is the usual [Cohn–Kleinberg–Szegedy–Umans STPP framework](https://arxiv.org/abs/math/0511460), also used in [Blasiak et al.](https://arxiv.org/abs/1605.06702). The two-window lemma and character construction are credited to [Davis and GPT-6.2 Astra](https://github.com/1337isnot1337/solved-conjectures/blob/892c04046aadc8731dd510bb9c9b3ca1a086bae1/results/nonmixed-gap-packing/PROOF.md), building on [Natalchenko and Sagdeev](https://doi.org/10.1002/jgt.23269). Finite-state methods for distance graphs precede this work, in particular [Carraher, Galvin, Hartke, Radcliffe and Stolee](https://arxiv.org/abs/1401.7183). The conclusions here combine exact STPP realization in the displayed template with the anchor classification and exact rate-achiever counts. The bounds concern that template and give no improvement to the unrestricted matrix multiplication exponent.

The Lean audit covers the shear STPP equivalence. The cyclic classification and finite-capacity formulas have written proofs, and the companion Python program cross-checks finite instances using independent enumeration.
