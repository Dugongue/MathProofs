# Deep Riemann Hypothesis for Dirichlet $L$-functions: a progress report

**Status (28 November 2026): the conjecture is OPEN.** It is strictly stronger than GRH. This page records a reduction map, a derivation of the $\sqrt2$ constant, one soft limitation remark, an almost-all-characters sketch, and numerical evidence. Most of the content is classical and is credited below. The parts we add are labelled **[new]**. Nothing here has been formalised. These are informal notes, pending human validation.

## 1. The conjecture

Let $\chi$ be a non-principal Dirichlet character, let $\Re s = \tfrac12$, and let $m$ be the order of vanishing of $L(s,\chi)$. The Deep Riemann Hypothesis (DRH) for $\mathrm{GL}_1$ asserts

$$
\lim_{x\to\infty}\Big((\log x)^m\prod_{p\le x}\big(1-\chi(p)p^{-s}\big)^{-1}\Big)
=\frac{L^{(m)}(s,\chi)}{e^{m\gamma}\,m!}\times
\begin{cases}\sqrt2 & s=\tfrac12 \text{ and } \chi^2=\mathbb 1,\\ 1 & \text{otherwise.}\end{cases}
$$

This is Kaneko, Conjecture 1.2 (arXiv:1902.04203), and also Kimura–Koyama–Kurokawa, Conjecture 2 (arXiv:1210.1216). It rests on Conrad, *Partial Euler products on the critical line*, Canad. J. Math. 57 (2005).

## 2. The equivalence chain (classical)

With $\vartheta(x,\chi)=\sum_{p\le x}\chi(p)\log p$ and $\psi(x,\chi)=\sum_{n\le x}\Lambda(n)\chi(n)$:

- **Conrad Thm 6.2/6.3, and independently Kuo–Murty (2005).** The partial Euler products converge at one point of $\Re s=\tfrac12$ $\iff$ they converge at every point of that line $\iff$ $\vartheta(x,\chi)=o(\sqrt x\log x)$ $\iff$ $\psi(x,\chi)=o(\sqrt x\log x)$. The last two are interchangeable because $\psi-\vartheta=O(\sqrt x)$.
- **GRH for $L(\cdot,\chi)$** $\iff$ $\psi(x,\chi)=O(\sqrt x\log^2 x)$. This gives convergence of the partial products only on $\Re s>\tfrac12$ (Conrad Thm 3.3).

**The exact gap from GRH to DRH** is an improvement from $O(\sqrt x\log^2x)$ to $o(\sqrt x\log x)$: one full power of $\log x$, plus $O\to o$. That gain must come from cancellation in the zero sum $\sum_\rho x^{\rho}/\rho$, which depends on the vertical distribution of the zeros (pair correlation, linear independence), not merely on their location. Montgomery's heuristic predicts that the true size is $O(\sqrt x(\log\log\log x)^2)$. So DRH is expected to hold, but it is out of reach of GRH alone.

## 3. Where the $\sqrt2$ comes from (classical; Conrad §4 and Cor. 5.6)

Expand $\log(1-\chi(p)p^{-s})^{-1}=\sum_{k\ge1}\chi(p)^k/(k\,p^{ks})$ at $s=\tfrac12$.

- The $k=1$ sum $\sum_{p\le x}\chi(p)/\sqrt p$ is the part DRH is sensitive to.
- The $k=2$ sum is $\tfrac12\sum_{p\le x}\chi(p)^2/p$. Passing from a cutoff on prime powers $p^k\le x$ to a cutoff on primes $p\le x$ leaves the window $\sqrt x<p\le x$, which contributes
  $$\tfrac12\sum_{\sqrt x<p\le x}\frac{\chi(p)^2}{p}.$$
  - **If $\chi^2=\mathbb 1$:** we have $\chi(p)^2=1$ for $p\nmid q$, and Mertens' theorem gives $\tfrac12(\log\log x-\log\log\sqrt x)+o(1)=\tfrac12\log2$. The partial product therefore carries an extra factor $e^{\frac12\log 2}=\sqrt2$.
  - **If $\chi^2\ne\mathbb 1$:** the character $\chi^2$ is non-principal, so the window sum tends to $0$, and there is no extra factor.
- **Second-moment reading.** The second-moment $L$-function is $L(s,\chi^2)$. It has a pole at $s=1$ exactly when $\chi^2=\mathbb 1$; this is Conrad's $R_0=-1$, which places $\sqrt2$ in the numerator. Goldfeld's elliptic-curve analogue has $R_0=+1$ and so produces $1/\sqrt2$.
- **Trigger.** The $\sqrt2$ is triggered by $\chi^2=\mathbb 1$, not by the root number. A quadratic $\chi$ with root number $-1$ still gets the $\sqrt2$, on the leading Taylor coefficient.
- **Function fields.** Over function fields the full asymptotic, $\sqrt2$ included, is a theorem (KKK Thm 1, via Deligne's RH for curves and a generalised Mertens theorem).

## 4. Averaged information cannot give the pointwise statement [new, soft]

Put $g_\chi(u)=\psi(e^u,\chi)e^{-u/2}$.

- **What GRH gives.** Under GRH, Cramér's argument shows that $g_\chi$ is bounded in mean square, with
  $$\frac1U\int_2^U|g_\chi(u)|^2\,du\to V_\chi=\sum_\gamma\frac1{\tfrac14+\gamma^2}<\infty.$$
  By Chebyshev's inequality, $\psi(x,\chi)=o(\sqrt x\log x)$ for all $x$ outside a set of logarithmic density $0$. This consequence is known: it is implicit in Cramér and Gallagher, and appears explicitly in arXiv:2512.23302. Gallagher gives even $O(\sqrt x(\log\log x)^2)$ outside a set of finite logarithmic measure.
- **Remark A1 [new, soft].** A uniform bound on any finite moment, $\frac1U\int_2^U|g_\chi|^{2k}\,du=O_k(1)$, only controls the measure of the set where $|g_\chi(u)|>\varepsilon u$: that measure is $O(U^{1-2k}\varepsilon^{-2k})$. It cannot exclude a sparse set of spikes. Concretely, for every $k$ there are functions with all moments bounded that exceed $\varepsilon u$ on a sequence $u_n\to\infty$: take spikes of height $u$ on sets of measure $e^{-u}$.
- **Consequence.** Any route to DRH for every $x$ needs a pointwise input on the zero sum $\sum_\gamma e^{i\gamma u}/(\tfrac12+i\gamma)$. Moment or mean-value hypotheses alone are not enough. Conrad's second-moment hypothesis is automatic for Dirichlet $L$-functions, since the relevant $L$-function is $L(s,\chi^2)$, so that hypothesis is not the missing ingredient either. This is a structural remark, not a deep theorem.

## 5. Almost all characters [new packaging of classical inputs; sketch]

Fix $q$. Combine two inputs:

- **Over characters:** the multiplicative large sieve (unconditional), together with the Montgomery–Hooley variance $\frac1{\varphi(q)}\sum_{\chi\ne\chi_0}|\psi(x,\chi)|^2\asymp x\log q$.
- **Over $x$:** Cramér's second moment.

Swapping the order of averaging gives the following.

> **Sketch B1.** For all but $o(\varphi(q))$ characters $\chi\bmod q$, the bound $\psi(x,\chi)=o(\sqrt x\log x)$ holds for a density-one set of $x$.

The exceptional set of characters is controlled by the large sieve, without GRH for each individual character. The uniformity in $x$ (the Barban–Davenport–Halberstam range) has not been fully bookkept. We did not find this combination stated as a theorem in the literature, but it may be folklore. Confidence: medium.

## 6. Numerical evidence for $\chi_4$ [new, supporting]

Sieve computation up to $2\cdot10^8$ for the character mod 4. The target is $\sqrt2\,L(\tfrac12,\chi_4)=0.94414\ldots$. Without the $\sqrt2$ it would be $L(\tfrac12,\chi_4)=0.66769\ldots$.

| $x$ | $\vartheta(x,\chi_4)/(\sqrt x\log x)$ | $\prod_{p\le x}(1-\chi_4(p)/\sqrt p)^{-1}$ |
|---|---|---|
| $10^3$ | $-0.129$ | $0.919$ |
| $10^4$ | $-0.075$ | $0.969$ |
| $10^5$ | $-0.060$ | $0.969$ |
| $10^6$ | $-0.133$ | $0.887$ |
| $10^7$ | $-0.058$ | $0.946$ |
| $10^8$ | $-0.037$ | $0.961$ |
| $2\cdot10^8$ | $-0.084$ | $0.914$ |

- The partial products oscillate around $\sqrt2\,L(\tfrac12,\chi_4)$, and nowhere near $L(\tfrac12,\chi_4)$. This agrees with Conrad's Table 1.
- The normalised $\vartheta$ shows no growth; its mean square over primes up to $2\cdot10^8$ is about $0.004$.
- This is evidence only. Convergence is slow, and oscillation is expected.

## 7. Relation to the Lean proof of GRH

The Lean development announced in November 2026 for RH and Dirichlet GRH (see [RiemannHypothesisConsequences](../RiemannHypothesisConsequences/README.md)) proves that the zeros lie on the critical line. It does so by a positivity argument, not by an explicit formula, and it contains no asymptotic for $\psi(x,\chi)$. So it settles the zero-location hypothesis that the conditional statements above assume. It contributes nothing to the extra pointwise cancellation that DRH requires. All GRH-conditional statements here inherit the status of that development: AI-assisted, machine-checked, and pending human review.

## 8. Open directions

1. A pointwise bound $\psi(x,\chi)=O(\sqrt x(\log\log x)^2)$ for all large $x$, under GRH plus a hypothesis on zero ordinates, would imply DRH. The linear-independence and random-model heuristics predict it, but a rigorous law of the iterated logarithm for these sums is open.
2. Complete the uniformity bookkeeping in Sketch B1.
3. Formalisation: the statement $\vartheta(x,\chi)=o(\sqrt x\log x)$, and the cited equivalences, would be a natural Mathlib-only target once the informal side is settled.

## References

- K. Conrad, *Partial Euler products on the critical line*, Canad. J. Math. 57 (2005) 267–297.
- S. Kaneko, *Euler product asymptotics for Dirichlet $L$-functions*, arXiv:1902.04203.
- T. Kimura, S. Koyama, N. Kurokawa, *Euler products beyond the boundary*, arXiv:1210.1216.
- W. Kuo, M. R. Murty, *On a conjecture of Birch and Swinnerton-Dyer*, Canad. J. Math. 57 (2005).
- H. Cramér (1922), and P. X. Gallagher (1980), on mean values of $\psi(x)$ under RH.
- H. L. Montgomery, heuristics for the size of $\psi(x)-x$.
- arXiv:2512.23302, the density-one form under GRH.
