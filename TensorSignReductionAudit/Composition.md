# Composition audit of the existing one-sign gadgets

Status: internal informal audit. No unrestricted reduction or new positive theorem is claimed in this file.

Let x,y in F_2 record two independent rigid transporter signs: bit zero means the desired determinant one. The conjunction accepts precisely (0,0).

Direct sums and tensor products with fixed parity exponents give a target determinant character of the form a*x+b*y+c. A single determinant-one test therefore accepts a fiber of an affine linear function. If (a,b) is nonzero, the fiber has two points; if (a,b) is zero, it is empty or the entire plane. None is the singleton {(0,0)}. Specifically x+y=0 falsely accepts (1,1).

This is an exact audit of a restricted composition model. It is not a lower bound on arbitrary pair-dependent reductions. In particular, an algorithm can construct target data that are not equivariant functions of the input orbit, and its behavior is not covered just by writing a determinant character on source witness blocks.

The neutral-conjunction construction adds ordinary TI comparisons while leaving the one live determinant unchanged. It is useful once a signed conjunct has already been compiled to ordinary TI, but supplies no such compilation on its own. The helper-swap construction supplies a correction when an ordinary comparison succeeds. On inputs where that ordinary comparison has the same answer for both relative orientations, the swap cannot distinguish the two orientations. Its two local maps can be chosen inverse, so their determinants cancel; the physical block permutation contributes the remaining dimension-dependent sign.

These observations were checked against the raw all-input requirement, rather than used to assume that raw inputs have a known transporter or sign-rigid stabilizer. They explain why the constructions used in this pass do not assemble into the requested reduction. They do not classify all possible constructions, and no impossibility of the requested reduction is claimed.

The exact two-bit control enumerates all eight affine Boolean functions and confirms that none of their zero fibers equals the required singleton. The same script independently verifies the affine-slice identity from PairDependent.md for all 2,304 pairs of invertible two-by-two matrices over F_3.
