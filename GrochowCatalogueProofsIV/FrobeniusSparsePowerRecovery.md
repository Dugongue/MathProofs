# Frobenius removes inseparability from sparse-power reconstruction

## GP-0702

Over explicit finite fields of fixed characteristic, reconstruction of sums of powers with an exponent divisible by the characteristic is polynomial-time oracle equivalent to reconstruction with a coprime residual exponent. The forward reduction is also uniform when the characteristic varies. This holds for proper output with the original top fan-in and sparsity bounds, and with exact field-extension query access. In particular, when the exponent is a pure characteristic power the problem has a uniform polynomial-time proper reconstruction.

Let $F=\mathbb F_q$ have characteristic $p$. Write the given exponent as $e=p^a b$ with $p\nmid b$. In $F[x]$,
$$
\sum_{\ell=1}^r P_\ell(x)^e
=\left(\sum_{\ell=1}^r P_\ell(x)^b\right)^{p^a}.
$$
The same identity holds on every finite extension $E$ of $F$. One query to the original oracle therefore simulates the residual oracle by applying the inverse of the $a$-fold Frobenius on $E$. This inverse can be evaluated by repeated squaring, reducing its exponent modulo the order $[E\colon \mathbb F_p]$ of the generating Frobenius automorphism first. Every proper reconstruction $\sum_\ell Q_\ell^b$ then gives a proper reconstruction $\sum_\ell Q_\ell^e$ with the same bases.

In the other direction, a coprime-exponent input $g=\sum_\ell P_\ell^b$ gives oracle access to $g^p$ by applying Frobenius to each value. If an inseparable solver finds $g^p=\sum_\ell Q_\ell^{pb}$, Frobenius injectivity on $F[x]$ gives $g=\sum_\ell Q_\ell^b$. For any fixed characteristic this is polynomial overhead in the usual numerical degree bound. With a variable characteristic the reverse direction must account for the factor $p$ in the degree, unless the reconstruction algorithm already uses a binary or residual degree bound. The forward reduction never needs to increase the degree.

If $b=1$, the residual polynomial is at most $rs$-sparse and its degree is no larger than the sparsity-base degree promise. Use a deterministic sparse polynomial reconstruction over finite fields with sufficiently large explicitly represented evaluation extensions. Partition its monomials into at most $r$ lists of size at most $s$ and use the resulting polynomials as the bases $Q_\ell$, giving a proper representation with exponent $p^a$. This recovers a valid representation of the output, as required by the reconstruction problem. The original summands need not be uniquely determined.

This resolves the inseparability step uniformly. For residual exponents above one the availability of a polynomial-time proper algorithm remains governed by the coprime-exponent problem at the same characteristic. [Catalogue source](https://arxiv.org/abs/2602.20832) · [Sparse interpolation, Theorem 4.6](https://arxiv.org/html/2611.07106#S4)
