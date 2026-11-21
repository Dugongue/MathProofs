# A one-instance directional-gap compiler on shrinking and balanced ternary tensor formats

For two dense ordered tensors of the same positive format over the field of three elements, the program outputs one ordinary tensor-isomorphism instance. Its YES predicate is that the transporter sign tuple (−,+,+) occurs and (+,+,+) does not. The default algorithm covers shrinking formats, every 3 by 3 by 3 core, and the unbounded balanced families described in [the balanced-core proofs](BALANCED.md). It signals an unresolved core outside its proved polynomial domain. The optional exhaustive algorithm terminates on every input, with exponential worst-case time. The unrestricted polynomial-time construction remains open.

## Usage

Run Python 3 on [compiler.py](compiler.py), supplying one JSON object on standard input. Input entries use 0, 1, 2 in row-major order with the last index varying fastest. A common shape and two flat entry arrays specify the instance. For example, the scalars 1 and 2 admit the sign tuple (−,+,+), while three positive determinants fix the scalar. The following input yields the ordinary scalar comparison 1 versus 1.

```json
{"shape":[1,1,1],"source":[1],"target":[2]}
```

Each successful invocation prints one ordinary comparison in this same format. Ordinary scalar 1 versus 0 is the NO instance. For a terminal format exceeding the default budget the program exits with code 2 and prints the format on standard error. Passing `--exhaustive` enables enumeration there. Run `python check.py` to run the regression checks.

## Correctness

Record determinants as bits with 0 for +1. Transposing a map, taking its inverse, or passing to the dual preserves its bit. This permits any mode to serve as the output of a bilinear map. Write its flattening as a matrix with k rows and mn columns.

1. Distinct flattening ranks imply an empty transporter profile. A zero pair admits every sign. For rank r strictly between 0 and k, replace each matrix by its r nonzero reduced echelon rows. Each new flattening differs by an invertible output change of coordinates from the old flattening with its zero rows removed. Transporters on the images extend to the whole spaces, with an arbitrary determinant on the unused complement. This makes the original output bit free and removes all dependence on the orientation used during support compression.
2. For full row rank, set h = mn − k. When h < k, use the standard nullspace basis with the free-coordinate identity block. Reshape its h vectors into an m by n by h tensor. An input action P ⊗ Q preserves the kernel pair exactly when it induces an invertible map of the two quotients. Its restriction to the kernels provides the third map of the dual problem. Conversely every transporter of the kernel tensors gives such an input action after dualization. This gives the two implications even when the original tensors fail to be ordinarily isomorphic.
3. If p and q are the input bits and t the kernel determinant bit, the original output bit is np + mq + t + s modulo 2. Here s is the sum of the two orientation corrections. To compute one correction, list the standard pivot vectors first and the free-coordinate kernel vectors second. The sign of this ordered basis is the parity of the pivot/free shuffle. The images of its pivot vectors give a quotient basis with determinant the pivot minor. Multiplicativity of determinant on the kernel and quotient gives the formula, including precisely the shuffle bit and the pivot-minor bit at each endpoint. For h = 0 there is a unique empty kernel map of bit 0 and the input bits are independent.
4. At a terminal concise format, apply intrinsic direct-sum and local-algebra recognition, row-space orbit intersection or the fixed-slice intertwiner solver. Their exact hypotheses, determinant formulas and polynomial bounds appear in [the balanced-core proofs](BALANCED.md). The exhaustive fallback enumerates pairs of input maps and derives the unique output map by elimination.

Each support or kernel step strictly decreases the sum of dimensions and never increases the dense input volume. At most the original sum of dimensions many polynomial-time elimination stages occur. In reverse order the program transports a set of at most eight sign triples at every stage. Equal tensors, an unused first-mode dimension, and a first mode of odd dimension together with an even other mode have immediate negative directional answers. In the last two cases a first-mode reflection on the unused complement or simultaneous central negations, respectively, preserve the source with sign (−,+,+), so the two sign tests agree.

One unbounded example is the shift pencil of format (2,n,n+1) and its entire ordinary orbit. With bases indexed from zero, its output at (i,j) is the vector indexed by i+j. The kernel basis consists of the differences of the two preimages of each interior basis vector. Regrouping by the old n-mode gives the same shift pencil of length n−1 up to invertible coordinate changes and signs. This proves the claimed orbit family by induction. More generally every pair whose reductions reach a bounded terminal enumeration is covered.

For an example with all three dimensions growing, take an m by n by mn tensor with invertible flattening in the last mode. Its kernel is zero and the algorithm terminates after one determinant computation and sign lift. Full-row-rank last flattenings of format (m,n,mn−1) have a kernel line. The resulting (m,n,1) pair is a matrix comparison: after support compression a nonzero matrix of rank r is supported on (r,r,1) and choosing an r-mode as output gives zero kernel. These families include YES instances of the directional predicate, for example an invertible flattening with even m and odd n compared to its first-mode reflection.

## Checks and scope

The independent small-format checker enumerates each mode action on entries directly, with the determinant bits tracked separately. Other controls compare kernel descent with a two-mode exhaustive search on full-row-rank flattenings and test the shift pencils through n = 9. These checks supplement the determinant argument. The terminal solvers and independent tests on balanced cases are documented [here](BALANCED.md).

The relationship between the unrestricted promise compiler and signed nonisomorphism is the [directional sign-gap theorem](https://github.com/Dugongue/MathProofs/tree/main/TISLDirectionalGap). The distinction between ordinary and special-linear tensor isomorphism appears in [Chen, Grochow, Qiao, Tang and Zhang, Open Question 1.9](https://arxiv.org/html/2306.03135v2#S1.SS5).
