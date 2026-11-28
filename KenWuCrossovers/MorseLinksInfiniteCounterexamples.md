# Every exponent congruent to two modulo four refutes the Morse-link valuation formula

Let \(L_n(k)\) be the sum of products of up-step weights \((2h+1)^{2k}\) over Dyck paths of semilength \(n\), with \(h\) the height before an up-step. Put \(D_n(k)=L_n(k)-C_n\), where \(C_n\) is the ordinary Catalan number. Write \(s_2(n)\) for the number of ones in the binary expansion of \(n\) and \(v_2(0)=+\infty\).

**Theorem.** For every \(k\in 2+4\mathbb Z_2\), there are no \(\alpha\in\mathbb Z_2\) and integer \(c\ge0\) such that

\[
v_2(D_n(k))=s_2(n)+v_2(n-\alpha)+c\qquad(n\ge2).
\]

The same indices \(n=2,3,19\) refute all these exponents. For 2-adic \(k\), define the odd square raised to \(k\) by its convergent binomial series in \(1+8\mathbb Z_2\). For positive integer \(k\), the statement gives an infinite family of counterexamples to Gao and Gu's formula. This upgrades the previously reported single exponent \(k=2\) and finite survey. The argument uses the precision comparison from the arithmetic-threshold work in MathProofs: a uniform low-precision residue test suffices even when the individual valuations become arbitrarily large. [Gao and Gu, Conjecture 4.12](https://arxiv.org/abs/1908.03914) · [Ken Wu Lab's counterexample and survey](https://kenwu-lab.wooqianghao.workers.dev/papers/morse-link-2adic-conjecture/) · [Portfolio arithmetic precision](https://github.com/Dugongue/MathProofs/blob/main/OrdinaryTensorTransferFallout/Arithmetic.md).

## Two simultaneous congruences

For any Dyck path \(P\) write \(A(P)=\prod_{\mathrm{up}\ h}(2h+1)^2\). It belongs to \(1+8\mathbb Z\), so

\[
D_n(k)\equiv \sum_{j=1}^3\binom{k}{j}\sum_P (A(P)-1)^j\pmod {2^{11}}.
\]

Terms of binomial index at least four vanish since \(8^4\) is divisible by \(2^{11}\). For \(j\le3\), the inner sum is \(\sum_{i=0}^{j}(-1)^{j-i}\binom ji L_n(i)\). The following table gives a finite certificate.

| \(n\) | modulus | \(L_n(0)\) | \(L_n(1)\) | \(L_n(2)\) | \(L_n(3)\) | three inner sums |
| --- | --- | --- | --- | --- | --- | --- |
| 3 | 1024 | 5 | 325 | 5 | 69 | 320, 384, 0 |
| 19 | 2048 | 982 | 1366 | 982 | 1878 | 384, 1280, 0 |

Here is complete independent pseudocode for the table. At time \(t\), the entry \(a_h\) sums weights of all allowable prefixes ending at \(h\). Discard heights exceeding \(n\), which no completed path of semilength \(n\) can visit. Initialize \(a_0=1\) and all other entries zero. Iterate \(2n\) times with \(a'_{h+1}\gets a'_{h+1}+a_h(2h+1)^{2i}\) when \(h<n\) and \(a'_{h-1}\gets a'_{h-1}+a_h\) when \(h>0\), starting each \(a'\) at zero and reducing in the indicated modulus. Return \(a_0\). The induction on prefix length proves the recurrence, including the final value.

Thus \(D_3(k)\equiv64k(3k+2)\pmod {1024}\) and \(D_{19}(k)\equiv128k(5k-2)\pmod {2048}\). Set \(k=2+4t\). Direct multiplication in \(\mathbb Z/16\) gives

\[
D_3(k)\equiv 512t\pmod {1024},\qquad
D_{19}(k)\equiv1024t\pmod {2048}.
\]

## Incompatibility of the shift

The two paths of semilength two give \(D_2(k)=9^k-1\). Since \(k\equiv2\pmod4\), the binomial expansion modulo \(32\) gives \(D_2(k)\equiv16\pmod{32}\), hence \(v_2(D_2(k))=4\). The proposed formula at \(n=2\) therefore forces \(c\le3\).

If \(t\) is even, the valuations at 3 and 19 are at least 10 and 11, respectively. With \(s_2(3)=2\), \(s_2(19)=3\), and \(c\le3\), both \(3-\alpha\) and \(19-\alpha\) would be divisible by 32. Their difference is 16.

If \(t\) is odd, the two valuations are exactly 9 and 10. The proposed shift valuations are both \(7-c\). For \(c\le2\) they are both at least five, giving the same contradiction. For \(c=3\), they would both be exactly four. Two 2-adic integers of valuation four have difference divisible by 32, since their quotients by 16 are odd. Again their difference is 16. This exhausts the parameters.

The result uses \(n=3\). It leaves the version starting at \(n=4\) open, as well as the validity of the formula on the other exponent classes.
