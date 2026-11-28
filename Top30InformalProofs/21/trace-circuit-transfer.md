# A conditional circuit lower-bound transfer for the cubic trace

The displayed implication uses a finite-size nonscalar lower bound for matrix multiplication as a hypothesis. Its stated numerical instantiation needs an independently verified input.

## Proof

- **MM lower bound.** OpenAI, "The matrix multiplication exponent is nine-fourths" (Nov 24, 2026), Cor. 1.2 (intro.tex l.56–62): every formal arithmetic circuit over F for the n×n product has ≥ ⌈n^{9/4}/2⌉ multiplication or division gates, for every n ≥ 2.
- **Baur–Strassen** (nonscalar form, BCS Thm 7.20): L*(f, ∂f/∂z_{ki} for all k,i) ≤ 3 L*(f). This holds formally over every field.
- **Transfer.** ∂T_n/∂z_{ki} = (XY)_{ik}. So a circuit for T_n with s nonscalar gates yields a circuit for XY with ≤ 3s nonscalar gates. Hence 3s ≥ ⌈n^{9/4}/2⌉. ∎

**Same transfer, already in the repo.** L_ns(det_{3n}) ≥ n^{9/4}/6, via the cofactors of [[I,A,0],[0,I,B],[0,0,I]]. This was recorded and killed as "classical transfer" in [research manuscript] B5. It does not mention the constant-degree open problem. Only the T_n statement and the explicit link to Raz's open problem are new here.

## Inputs
- OpenAI: the finite-n nonscalar bound, which is paper-only and NOT in the Lean. The Lean `square_exponent` is a division-free exponent, and it also gives Ω(N^{9/8−ε}) for division-free circuits.
- Classical: Baur–Strassen.
