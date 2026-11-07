# Published examples and reproducible fixtures

The fixture set contains two exact published positive functions, one exact published negative design construction, one relabeling of a published example, three clearly labeled family instances, and the project's own rank-only counterexample. Matrices are generated from formulas with integer arithmetic; none is transcribed from a screenshot or supplied to the recognizer with a hidden coordinate frame.

## Primary source

Jong Yoon Hyun, Jieun Kwon, Jiaxin Wang and Yansheng Wu, [Designs, linear codes, plateaued functions, and their interconnections, arXiv:2605.24355v1](https://arxiv.org/html/2605.24355v1).

- **Section IV-A, Example 1:** the six-variable quadratic bent function `x1*y1+x2*y2+x3*y3`.
- **Section VI-A, Example 2:** the five-variable function `x1*x3+x2*x4+x1*x2*x5`. The paper attributes the earlier function to Hodžić, Pasalic, Wei and Zhang, *Designing Plateaued Boolean Functions in Spectral Domain and Their Classification*, IEEE Transactions on Information Theory 65(9), 5865–5879 (2019), Example 4.1; [preprint](https://arxiv.org/abs/1811.04171).
- **Section VIII, Example 4 and Theorem 10:** the finite-field construction using `g(x,y)=Tr(x*y^14)` and `h(x,y)=Tr(alpha*x*y^14)` over GF(16), with `alpha^4+alpha+1=0`. This is a published negative control for addition-design recognition.

## Independently computed fixture properties

All properties below were checked directly from the regenerated incidence arrays by `examples/validate.py`, independently of the recognizer implementation.

| File | Provenance | Matrix shape | Design parameters | Binary rank | Bordered rank | Expected |
|---|---|---:|---|---:|---:|---|
| `published-example-1.json` | Exact Example 1 function | 64 × 64 | 2-(64,28,12) | 8 | 8 | Recognized |
| `published-example-2.json` | Exact Example 2 function | 16 × 32 | 2-(16,6,4) | 7 | 7 | Recognized |
| `published-example-2-permuted.json` | Independently shuffled rows and columns of Example 2 | 16 × 32 | 2-(16,6,4) | 7 | 7 | Recognized |
| `quadratic-family-m4.json` | Four-variable quadratic family instance | 16 × 16 | 2-(16,6,2) | 6 | 6 | Recognized |
| `cubic-mm-family-m6.json` | Cubic Maiorana–McFarland family instance | 64 × 64 | 2-(64,28,12) | 8 | 8 | Recognized |
| `plateaued-stabilization-m7.json` | Example 2 plus a disjoint quadratic pair | 64 × 128 | 2-(64,28,24) | 9 | 9 | Recognized |
| `proof-counterexample-64x128.json` | Project proof's own sum-free construction | 64 × 128 | 2-(64,28,24) | 9 | 10 | Rejected |
| `published-example-4-negative.json` | Exact Example 4 construction | 256 × 256 | 2-(256,120,56) | 30 | 30 | Rejected |

The ordinary-rank collision in the two 64 × 128 examples is particularly useful: identical design parameters and binary rank do not determine the answer, while the bordered rank distinguishes these cases. The negative project fixture is attributed to `SumFreeCounterexample` in `PlateauedAdditionDesigns_BorderedRankCharacterization.lean`; it is not presented as a published paper example.

## Coordinate and construction conventions

Integer bit `i` represents variable `x_(i+1)`. The Walsh transform is `W_f(a)=sum_x (-1)^(f(x)+parity(a & x))`. The addition-design point set is the nonzero Walsh support, its block labels are all domain vectors, and incidence is `f(b) XOR (W_f(a)<0) XOR parity(a & b)`. These labels and source functions are fixture metadata, not inputs needed by the recognizer.

Example 4 uses polynomial-basis GF(16) arithmetic modulo `t^4+t+1`; integer `2` encodes `alpha`. Its matrix is `M[x,b]=g(b) XOR h(x XOR b) XOR g(x) XOR h(x)`. The checker independently reproduces its rank 30.

## Regeneration and larger cases

```console
python examples/generate.py
python examples/validate.py
```

`generate.py --include-large` additionally materializes dimension-8 quadratic and cubic family instances and the dimension-9 stabilized plateaued instance. These are generated tests from cited families, not additional individually published examples. The Python functions `make_fixture`, `addition_design` and `permuted` also support in-memory benchmark generation. The manifest records SHA-256 hashes of the exact fixture bytes.

The validator checks rectangular binary input, block distinctness, every block weight, every point-pair multiplicity, and both ranks. These checks validate the fixture data and do not replace testing the recognizer or independently checking its reconstruction certificates.

## Baseline scope

SageMath already provides [`BooleanFunction.walsh_hadamard_transform`, `is_plateaued` and linear-structure methods](https://doc.sagemath.org/html/en/reference/cryptography/sage/crypto/boolean_function.html). Those methods verify a supplied function; they do not by themselves reconstruct one from an unlabeled design. Its [`IncidenceStructure.is_t_design`](https://doc.sagemath.org/html/en/reference/graphs/sage/combinat/designs/incidence_structures.html) supplies a design-validation baseline. Binary matrix rank is computed through a matrix over GF(2), not `IncidenceStructure.rank()`, which means maximum block size. Benchmark reports must retain these different tasks when comparing timings.
