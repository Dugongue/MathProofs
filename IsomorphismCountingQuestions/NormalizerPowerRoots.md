# Power-root counts for conjugation-invariant target sets

In *A set theoretic version of equations on groups*, Mihai-Silviu Lazorec asks after Lemma 2.1 whether the number of elements \(x\in G\) with \(x^n\in L\) is divisible by \(\gcd(n,|N_G(L)|)\) when \(L\) is a nonnormal subgroup. The answer is yes, as a consequence of the classical Frobenius root-count theorem. [Published article](https://doi.org/10.1007/s13366-026-00844-y) · [Question after Lemma 2.1](https://arxiv.org/html/2603.27026#S2)

**Theorem.** Let \(G\) be a finite group and \(K\le G\). If \(L\subseteq G\) is preserved by conjugation by \(K\), then for every positive integer \(n\),
\[
  \gcd(n,|K|)\mid |\{x\in G:x^n\in L\}|.
\]

For \(y\in G\) write \(R_n(y)=|\{x:x^n=y\}|\). Frobenius's theorem gives \(\gcd(n,|C_G(y)|)\mid R_n(y)\). For an orbit of \(K\) in \(L\) with representative \(y\), set \(J=C_K(y)\). Conjugation bijects the root fibers, so this orbit contributes \([K:J]R_n(y)\). Since \(J\le C_G(y)\), the contribution is divisible by \([K:J]\gcd(n,|J|)\). At any prime \(p\), writing \(a=v_p(n),b=v_p(|J|),c=v_p(|K|)\), its valuation is at least \(c-b+\min(a,b)\ge\min(a,c)\). Sum over the orbits and take \(K=N_G(L)\) for the published case. The universal single-exponent divisor is sharp for \(K=G\) cyclic and \(L=\{1\}\). [Frobenius's theorem as quoted in Theorem 1.1](https://arxiv.org/html/2603.27026#S1)

**Simultaneous powers.** Let \(L\subseteq G^r\) be stable under simultaneous \(K\)-conjugation and let \(n_1,\ldots,n_r\) be positive. Then the number of tuples with \((x_1^{n_1},\ldots,x_r^{n_r})\in L\) is divisible by \(\gcd(\prod_i n_i,|K|)\). The orbit of a tuple \((y_i)\) contributes \([K:J]\prod_iR_{n_i}(y_i)\), where \(J\le C_G(y_i)\) for every \(i\). At each prime,
\[
  \sum_i\min(v_p(n_i),v_p(|J|))\ \ge\
  \min\left(\sum_i v_p(n_i),v_p(|J|)\right).
\]
The same index calculation gives the required valuation.

The proofs are informal. The normalizer result uses the classical Frobenius theorem and does not depend on a bound on the group order.
