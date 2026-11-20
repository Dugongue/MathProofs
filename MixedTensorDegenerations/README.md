# Mixed tensor degeneration and related transfers

Written proofs with independent internal review. Publication priority is unestablished. The results have no Lean formalization.

| Result | Scope |
|---|---|
| [Directional degeneration and local singularities](DEGENERATION.md) | Every fixed basis-explicit mixed tensor signature reduces to directional degeneration of a single ordinary three-tensor. The reduced closures have smoothly equivalent germs at encoded points. This works over an algebraically closed field of any characteristic and includes fixed-rank relation subspaces. |
| [Exact transporter counts](COUNTING.md) | Computes the fiber factors in the dimension-controlled balanced rank-marker reduction over finite fields and in the free-tensor reduction for presented modules over finite chain rings. Each uses one exact ordinary tensor counting call. |
| [Mixed supports and spectral canonization](SUPPORT.md) | Gives the minimum ambient dimension for simultaneous primal and dual supports. Gives a canonization algorithm over a fixed finite field when the marked squarefree cyclic covariants satisfy the stated zero-or-unit cell promise. |
| [Polynomial Calculus transfer](PC-TRANSFER.md) | Proves fixed-signature higher-order transfer to ordinary three-tensors in every field. Extends the reverse simulation for the exact FGS route to the stated good-prime conditions. The unrestricted small-characteristic case of the exact route remains open here. |

[Review and verification scope](REVIEW.md)

Run the three Python files with Python 3 to reproduce finite controls for the identities in the proofs. The controls are examples and finite enumerations. They supplement the written arguments, including the geometric proof of the general result.
