# Further answers from the Grochow open-problem catalog

Six written answers from 20 November 2026, using the [catalog's stable identifiers](../GrochowOpenProblems/README.md).

| ID | Result |
| --- | --- |
| GP032 | First-order logic with counting modulo three identifies Fitting-free groups with $O(\log\log N)$ variables. An explicit abelian family needs $\Omega(\log N)$ variables. [Proof](MODULAR-COUNTING.md) |
| GP038 | Isomorphism on valid abelian Cayley tables requires $N^{\Omega(\log N)}$ DNF terms. [Proof](ABELIAN-DNF.md) |
| GP088 | The original multiplication-output tangency formula fails already for a four-dimensional square-zero algebra. The follow-up paper proves the multiplication-input formula. [Proof and factor comparison](TANGENCY-FLATTENING.md) |
| GP143 | Over every field, determinant partition rank is $n-1$ for even $n\ge4$ and $n$ for odd $n\ge3$ and $n=2$. [Proof](DETERMINANT-PARTITION-RANK.md) |
| GP145 | The Lie exponent of $\mathrm{SL}(n,\mathbb R)$ is at most $3(n-1)/(n-2)$ for $n\ge3$ and is infinite at $n=2$. [Proof](LIE-EXPONENT.md) |
| GP162 | Explicit 2-CNFs with the same number of variables and the same homogeneous syzygy regularity can differ by a linear factor in minimum IPS size. [Proof](IPS-REGULARITY.md) |

[Prior results for GP089, GP197 and GP200](LITERATURE-STATUS.md) record three status corrections. The [third-minor argument](MINOR-FLATTENING.md) extends the characteristic-zero conormal formula to every field of odd characteristic.

The main results are written proofs. [Lean source](ImplicationCertificate.lean) and its [axiom audit](ImplicationCertificateAudit.json) cover the implication-chain certificate identity used in GP162. The package includes exact finite replays for the abelian DNF construction, determinant partition-rank proof ingredients, and the two tensor flattenings.
