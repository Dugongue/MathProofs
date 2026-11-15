# Matrix-code benchmark data

Each text input lists the prime p, matrix dimensions m and n, and code dimension k. The next k rows are a basis for the source code, with each matrix flattened in row-major order. The last k rows give the target basis in the same format. An equivalence means that invertible matrices L and R over the prime field satisfy L C R = D as subspaces. The input gives neither a matching between generator rows nor a witness.

## Published and derived cases

| Dataset | Prime | Matrix size | Code dimension | How labels were determined |
| --- | ---: | --- | ---: | --- |
| Oxford MEDS example | 13 | 4 × 6 | 5 | Verified published L and R and exact equality of the transformed span |
| Rebased Oxford example | 13 | 4 × 6 | 5 | Verified the same map after independent changes of code basis |
| Oxford tensor amplifications | 13 | 8 × 12, 12 × 18, 16 × 24 | 5 | Verified the constructed isomorphism after dense invertible masks and rebasing |
| Morrison Table 1 | 2 | 2 × 2, 2 × 3 | 2, 3 | Exact GL search on all unordered pairs of published representatives |
| Morrison Table 2 | 3 | 2 × 4 | 4 | Exact GL search on all unordered pairs of published representatives |
| Official MEDS v1.1 KAT, first pair | 8,191, 4,093, 2,039 | 10 × 10, 14 × 14, 22 × 22, 30 × 30 | Positive by the published key-generation algorithm |

- The Oxford poster provides both generators and the left and right invertible matrices. Its entries printed as 13 are zero modulo 13. The rebased example and all amplifications share the same source pair. An amplification maps each code matrix X to X ⊗ I_r before independent dense masks and basis changes, so the matrix dimensions grow while the code dimension and projective coefficient search space stay fixed. [Oxford MEDS poster](https://www.maths.ox.ac.uk/system/files/inline-files/meds.pdf)
- Morrison gives representative generators and rank distributions under equivalences preserving self-duality. For our GL equivalence, the adapter rechecks self-duality, basis rank and the published rank distributions, then enumerates one representative of each scalar class of GL₂. For each left map it builds the linear equations for the right map and checks the whole solution space for an invertible matrix, stopping once a verified witness is found. The tables supply one 2 × 2 binary pair, ten 2 × 3 binary pairs, and 78 ternary pairs. Under unrestricted GL, two ternary pairs are equivalent and 87 pairs are inequivalent. Of the inequivalent pairs, 13 share their full rank distribution. The manifest gives exact labels and both positive witnesses. [Katherine Morrison, An Enumeration of the Equivalence Classes of Self-Dual Matrix Codes, Tables 1–2](https://arxiv.org/abs/1505.07363)
- MEDS known-answer inputs come from record zero of the 2023-07-26 public archive. The adapter uses the public key and decodes its source and first transformed generator stacks. Distinct parameter IDs can emit identical first pairs, as three pairs of IDs do in this record. The decoded bases were checked for the published dimensions. Their equivalence labels follow from the exact construction, while the Oxford and Morrison positive labels additionally have explicitly checked witnesses. [MEDS v1.1 specification, Algorithm 10](https://www.meds-pqc.org/spec/MEDS-2023-07-26.pdf) · [MEDS public KAT archive](https://www.meds-pqc.org/KAT/MEDS-KAT-2023-07-26.tgz)

## Reproduction

From the benchmark directory with Python 3.11 or newer:

```console
python dataset_meds.py dataset/oxford-meds-13-4-6-5.txt
python dataset_meds_derived.py dataset
python dataset_morrison.py dataset/morrison
python dataset_meds_kat.py MEDS-KAT-2023-07-26.tgz dataset
```

The KAT decoder pins the archive SHA-256 to `4045fbde6d2c6a4ccce1df5c46230e227ad5961047a4d172cf502622b3250760`. It reads the archive directly and emits public generator entries. Use the archive and reference implementation from the original publishers. The dataset adapters are independent implementations. Solver timing excludes data generation and equivalence labelling.
