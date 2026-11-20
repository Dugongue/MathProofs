# Four advances on tensor isomorphism, proof complexity and matrix multiplication

Four proof searches drew on different results from the pinned [Cinna Davis and GPT-6.2 Astra collection](https://github.com/1337isnot1337/solved-conjectures/tree/892c04046aadc8731dd510bb9c9b3ca1a086bae1). They address problems in Grochow's work on tensor and group isomorphism, the Ideal Proof System and the group-theoretic approach to matrix multiplication.

| Result | What the proof establishes |
| --- | --- |
| [Log-free finite-ring isomorphism](LOG-FREE-TENSOR-ISOMORPHISM.txt) | A constant-factor bound on noncommutative rank in terms of base-field rank removes the logarithmic loss in finding zero rectangles. The deterministic \(2^{O_R(n^{3/2})}\) algorithm over fixed odd finite commutative rings resolves decision, witnesses, stabilizer generators and determinant-resolved counts. |
| [Integral tensor isomorphism and principal ideals](INTEGRAL-PENCILS.md) | A deterministic many-one reduction in every number-field degree \(n\ge3\), to full unmarked \(2\times n\times n\) integral tensor isomorphism. It works for determinant-one isomorphism in odd degree. A separate criterion lists all slice changes of arbitrary irreducible pencils before testing their lattices. |
| [Separable IPS refutations](SEPARABLE-IPS.md) | Exact reciprocal ROABP width for grid equations with separable summands, a sharp factor-three interleaved width bound for the reduced IPS certificate, and a fixed-parameter algorithm to find an optimal reciprocal order. |
| [Simultaneous triple-product capacity](SHEAR-STPP.md) | Exact finite capacity and maximizing counts for cyclic nonmixed-gap packings in the displayed shear template, plus all rate-achieving configurations and eventual affine periodicity. |

## Verification

The four notes give complete written arguments at their stated scopes and credit the relevant prior theorems. The Lean sources and receipts cover the named supporting declarations. They use Lean 4.33.0 and [Mathlib db584cd6](https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d). The Python scripts replay exact finite controls with assertions enabled. Priority and external refereeing remain unestablished.
