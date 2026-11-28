# A two-square formula for the divisor congruence on the full class two modulo four

Write

\[
S(N)=\sum_{1\le k<\sqrt N}\tau(N-k^2),
\]

where \(\tau\) counts positive divisors. For every \(N\equiv2\pmod4\),

\[
\boxed{\quad S(N)\equiv \sum_{\substack{k,a>0\\k^2+a^2=N}} a\pmod4.\quad}
\tag{1}
\]

The right side uses ordered pairs. This extends the zero congruence on \(N\equiv6\pmod8\) to an exact answer on all of \(N\equiv2\pmod4\). It also gives an arithmetic distribution of the two possible residues on twice a prime that splits in \(\mathbb Q(i)\). This combines the lab's involution with the portfolio's use of splitting probes and residue densities. [Ken Wu Lab on square-plus-product divisors](https://kenwu-lab.wooqianghao.workers.dev/papers/square-plus-product-divisors/) · [Jirattikansakul, Kittipassorn, Kongsiri, Moonwichit, and Sriamorn](https://arxiv.org/abs/2604.25394) · [Portfolio arithmetic splitting probes](https://github.com/Dugongue/MathProofs/blob/main/ExactMatrixProofDegrees/JointGalois.md).

## Boundary correction to the involution

Count positive triples \((k,a,b)\) with \(k^2+ab=N\). For even \(k\) the product has 2-adic valuation one. Swap \(a,b\) to get twice the count with \(b\) even. On that half, the involution \((a,b)\mapsto(b/2,2a)\) reduces parity to the fixed points \(b=2a\). Thus the even-\(k\) contribution is \(2F\bmod4\) where \(F\) counts positive \((u,v)\) with \(2u^2+4v^2=N\).

For odd \(k\), set \(m=N-k^2\equiv1\pmod4\). The factors are odd and have the same residue modulo four. Diagonal factor pairs contribute one for each positive solution \(k^2+a^2=N\). Write \(E\) for their count. After the swap, each strict pair \(a<b\) corresponds to \((x,y,z)=(a,a,(b-a)/4)\) in the positive solutions to \(x^2+4yz=m\). We calculate the parity of these strict pairs with the fixed-point argument, retaining the boundary cases.

The exceptional set for Zagier's involution is \(x+z=y\). The other possible boundary \(x=2y\) is excluded by odd \(m\). Remove the exceptional set temporarily. In the remaining region the involution is

\[
(x,y,z)\mapsto
\begin{cases}
(x+2z,z,y-x-z)&x+z<y,\\
(2y-x,y,x+z-y)&x+z>y,\ x<2y,\\
(x-2y,x-y+z,y)&x>2y.
\end{cases}
\]

All displayed coordinates are positive. The first and third cases exchange regions, while the second case maps to itself, since the sum of the first and third new coordinates is \(y+z>y\). Substitution gives the original triple after applying the map twice and preserves \(x^2+4yz\). Its fixed points are exactly \(x=y\), none of which are removed. Put \(B\) for the total count of exceptional triples, summed over odd \(k\). The count of strict pairs is therefore congruent modulo two to the size of the whole solution set minus \(B\).

On that whole solution set, swapping \(y,z\) reduces parity to \(y=z\). Next swap \(k,x\), both odd, in \(k^2+x^2+4y^2=N\). The fixed points number \(F\). Thus the strict pairs number \(F-B\bmod2\), and the full total is \(E-2B\bmod4\).

On the exceptional set, \(m=(x+2z)^2\). For each ordered positive pair \((k,a)\) with \(a^2=m\), there are exactly \((a-1)/2\) positive choices of \(z\), with \(x=a-2z\) and \(y=x+z\) determined. Hence \(E-2B=\sum(2-a)\equiv\sum a\pmod4\), because \(a\) is odd. This proves (1).

## Arithmetic consequences

Pairing a representation with its coordinate swap shows \(S(N)\) is odd precisely when \(N=2u^2\) for an odd positive integer \(u\). If \(N\) is not a sum of two squares, (1) is zero. In particular this gives the known entire class \(N\equiv6\pmod8\).

For an odd prime \(p\equiv1\pmod4\), take the unique positive representation \(p=a^2+b^2\) with \(a\) odd and \(b\) even. The positive ordered pairs for \(2p\) are the two orders of \((a+b,|a-b|)\), by multiplication by \(1+i\) in the Gaussian integers and uniqueness of Gaussian factorization. Consequently

\[
S(2p)\equiv 2\max(a,b)\pmod4.
\]

The values zero and two occur with equal relative natural density among these split primes. To see this, for a Gaussian ideal prime to \((1+i)\), choose its generator \(\gamma\equiv1\pmod{2}\), unique up to sign. The functions \((\gamma/|\gamma|)^{2j}\) are well-defined multiplicative Hecke characters of conductor dividing \((2)\) and nonzero angular frequency for \(j\ne0\). The prime ideal theorem for these characters and Weyl's criterion give equidistribution of the angles of these generators modulo \(\pi\). Inert prime ideals have square norm and form a negligible subset. Each split rational prime gives two conjugate angles, and the condition \(|\operatorname{Re}\gamma|>|\operatorname{Im}\gamma|\) applies to both or neither. It holds on half the circle modulo \(\pi\), and is exactly the event that the larger coordinate is odd. This proves the density assertion by the Gaussian prime ideal argument with finite conductor. [Rudnick and Waxman for the Hecke angular prime theorem](https://arxiv.org/abs/1705.07498).
