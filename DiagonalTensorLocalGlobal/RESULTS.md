# Four local–global theorems for geometrically diagonal tensors

All results concern the ordinary \(\mathrm{GL}_n^3\) or the special-linear \(\mathrm{SL}_n^3\) action on three-tensors over a number field. A tensor is geometrically diagonal when it is ordinarily equivalent over an algebraic closure to \(\sum_{i=1}^n e_i\otimes e_i\otimes e_i\). The signed local genus of a tensor is the set of global \(\mathrm{SL}_n^3\)-classes that agree with it over every completion.

| Result | Theorem | Proof |
|---|---|---|
| Exponential extension degree | For every \(k\ge 1\), side \(6k\) has an everywhere locally special-linearly isomorphic pair with minimum global isomorphism degree \(2^k\) and exactly \(3^k\) inclusion-minimal isomorphism fields. | [Proof](repair-fields.md) |
| Sharp maximum for abelian Galois fields | In degree \(n=\prod_p p^{k_p}\), the maximum number of signed classes locally equivalent within one ordinary orbit coming from an abelian Galois field is \(2^{\epsilon(n)}\prod_p p^{k_p(k_p-1)}\). The proof gives an equality criterion and attainment over every number field. | [Proof](abelian-maximum.md) |
| Sharp first signed failure | The special-linear local–global principle holds through side three and fails at side four over every number field. Every side-four signed genus is classified, with possible sizes 1, 2, 4, and 8. | [Proof](sharp-threshold.md) |
| Exact signed counts over the first ordinary failures | The two ordinary degree-six failure types give signed local genera of exactly five and two classes, respectively, after trace-discriminant normalization. | [Proof](side-six-genera.md) |

The [determinant calculation](determinants.md) supplies the common comparison within an ordinary orbit. The four main statements have written proofs. [Lean source](DiagonalLocalGlobal.lean) and the [audit](Verification.json) cover the determinant coordinates, fixed-point noncancellation, and reciprocity parity identity.
