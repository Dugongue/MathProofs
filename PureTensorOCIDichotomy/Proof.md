# A dichotomy for pure-power tensor orbit closure intersection

Informal proof. November 14, 2026.

For a fixed signature, let a single general linear group act on a tuple of tensors, each slot being either a pure primal power of the defining space or a pure dual power. Let `a` and `b` be the greatest positive orders on the primal and dual sides, respectively, using zero when that side is empty. If `min(a,b) >= 2` and `max(a,b) >= 3`, orbit closure intersection is TOCI-complete under the efficient algebraic reductions of Lysikov–Walter. In the remaining cases, it is decidable in deterministic polynomial time over the usual exact encodings of rational or fixed number field coefficients, with the orbit closures always taken over C. The algorithms also use polynomially many exact field operations.

This classifies the pure-power portion of the broader dichotomy in [Lysikov–Walter, Question I.12](https://arxiv.org/html/2411.04639v2#S1.SS4). In particular, the mixed-sign cubic pair `V^⊗3 ⊕ (V*)^⊗3` is TOCI-complete. The general question includes individual slots having both primal and dual factors, as well as products of groups. The theorem here concerns pure slots for a single group.

## Fixing a closed marker

Let a complex algebraic group `G` act on an affine variety `Z`, let `m : Z -> M` be an equivariant regular map, and assume the orbit of `m(z)` is closed. Fix a point `m0` in that orbit and let `H` be its stabilizer. For any `z,z'` in the fiber over `m0`, their `G`-orbit closures intersect if and only if their `H`-orbit closures intersect in the fiber.

For the forward direction, take a common point of the closures and translate it by one element of `G` so its marker is `m0`. This is possible because all markers along the closure lie in the closed marker orbit. For either input, choose a sequence of translates converging to the common point. Over C the Euclidean and Zariski closures of algebraic orbits agree. The orbit map from `G` to the marker orbit has local complex-analytic sections because it is the quotient map onto a smooth complex homogeneous space. Choose a section taking `m0` to the identity. If `g_j z` is the sequence and `s_j` is the section evaluated at its marker, then `s_j -> 1` and `s_j^-1 g_j` belongs to `H`. Thus `s_j^-1 g_j z` still converges to the common point. Apply this to both inputs. The reverse follows from `H <= G`. The same argument works on any closed invariant fiber obtained in a preceding application. See [Lysikov–Walter, Definition II.4 and the preceding discussion](https://arxiv.org/html/2411.04639v2#S2.SS2) for the closure convention.

## A TOCI-complete source with one vanishing trace

Use a fixed standard nondegenerate complex symmetric form on each based space below. Theorem V.21 of Lysikov–Walter supplies a TOCI-complete source consisting of two labelled cubic tensors on a space `E` under `O(E)`. We reduce that source to a single cubic tensor under an orthogonal group, with the tensor required to have zero contraction in positions 1 and 3. The trace condition will be used in the degree-two dual case.

First set `Y = E ⊕ E` with the direct sum form. Write `P` for the projection onto the first copy, write `J(x,y)=(-y,x)`, and set `A=2I-P+J`. Identifying `Y^⊗2` with `End(Y)` via the form, place `A` in a quadratic slot and the two input cubics in the respective disjoint pure-copy blocks in a cubic slot. The symmetric and skew parts of `A` recover `P` and `J`. The orbit of `(P,J)` under orthogonal conjugacy is closed: it is defined by

```
P^T=P, P^2=P, trace(P)=dim E,
J^T=-J, J^2=-I, PJ=J(I-P).
```

Indeed a self-adjoint projection gives two orthogonal nondegenerate spaces, and `J` exchanges them isometrically. An orthonormal basis of the image of `P` followed by its `J`-images recovers the standard pair. The common stabilizer is diagonal `O(E)`. The closed marker argument therefore proves the reduction. Its remaining data map is an injective linear equivariant map, so its image is closed and reflects closure intersection.

Now take `U = Y ⊕ C e`, an orthogonal sum with `e` of norm one, and `N=dim U`. Let `q` denote the inverse metric, and `c_12,c_13` the contractions for the form. Define `F(u)=q_12 ⊗ u_3` and `G(v)=q_13 ⊗ v_2` by the indicated slot placements. On the sum of the images their two contractions give the matrix

```
          F    G
c_12      N    1
c_13      1    N
```

Since `N>1`, the sum is direct and has an orthogonal-group-equivariant linear complement `K = ker c_12 ∩ ker c_13`. Let `pi` be the projection onto `K` along the two images. In `ker c_13`, place the marker `F(e)-G(e)/N`. It is recovered from `c_12` by multiplying by `(N-1/N)^(-1)`. Its orbit is the closed unit quadric under the resulting copy of the vector representation and its stabilizer is `O(Y)`.

Place the cubic data in `Y^⊗3`, place the quadratic data from the preceding stage in `Y ⊗ e ⊗ Y`, and apply `pi` to their sum. The projection is injective on this data subspace. Indeed, if `F(u)+G(v)` lies there, the forbidden components in `e ⊗ e ⊗ Y` and `e ⊗ Y ⊗ e` imply `u,v ∈ C e`. The forbidden component `Y ⊗ Y ⊗ e` then forces `u=0`, and the forbidden component `C e^⊗3` forces `v=0`. The map is equivariant for `O(Y)`. The same closed marker argument now reduces the two-slot source to `ker c_13` under `O(U)`. All these maps are affine with rational coefficients. This spells out the trace-free variant of the orthogonal compression used in earlier MathProofs work. [Lysikov–Walter, Theorem V.21](https://arxiv.org/html/2411.04639v2#S5.SS2).

## Completeness of two opposite pure powers

Let `a >= 3` and `b >= 2`. Using the preceding source, let `f ∈ U^⊗3` have `c_13(f)=0`. Enlarge once more to `W=U ⊕ L`, where `L=C l`. Let `epsilon` be the covector annihilating `U` with `epsilon(l)=1`. Let `q ∈ U^⊗2` and `q* ∈ (U*)^⊗2` be the standard inverse metric and metric, respectively. The notation `[q]_(2,3)` means put `q` in slots 2 and 3, filling every other primal slot with `l`. The analogous notation on the dual side fills other slots with `epsilon`. For `b=2`, use `q*` in its two available slots. Define

```
T(f) = 2 l^⊗a + [q]_(2,3) + f ⊗ l^⊗(a-3).
S    = epsilon^⊗b + [q*]_(2,3),                         b >= 3,
S    = epsilon^⊗2 + q*,                                  b = 2.
```

### Recovering the splitting by an equivariant contraction

Put `gcd = gcd(a,b)`, `ell = b/gcd`, and `r = a/gcd`. Take `ell` copies of `T` and `r` copies of `S`, so the counts of primal and dual legs agree. The following partial contractions give a polynomial equivariant map to `W ⊗ W* = End(W)`.

If `b >= 3`, reserve position 2 of the first primal and first dual copies as the output legs. Contract their position 3 legs with each other. In every primal copy, connect position 1 to a different line-only leg of a dual copy. There are enough available such legs since `r(b-2) >= ell`, and none was reserved or used by the position 3 contraction. Complete the matching of the remaining legs arbitrarily. The position 1 contractions kill all terms involving `f`. In the distinguished pair of copies, the remaining line legs are fixed independently of whether the pure-line or metric term is chosen. The designated position 3 contraction makes their output exactly `2 l ⊗ epsilon + I_U`: the two cross-terms vanish because `U` and `L*` pair to zero. The residual contraction is a scalar `C>0`, depending only on the dimensions and matching. Its terms are nonnegative integers in the standard basis and include the strictly positive all-line term. Thus the output is `C(I_W + P_L)`, where `P_L=l ⊗ epsilon`.

If `b=2`, first use a separate copy of `S` to contract positions 1 and 3 internally in each primal copy. The trace condition kills `f`, and the line-versus-`U` mismatch kills the `q` term. The result from each such copy is `2 l^⊗(a-2)`. At least one copy of `S` remains since `r>ell`. Reserve one leg of such a copy and one remaining primal leg for the outputs, and match all other remaining legs. Every available primal leg is a line leg. Hence the output is `2^ell l ⊗ epsilon`.

In either case the above operation recovers an equivariant spectral marker whose orbit is closed: after fixed rescaling and possibly an identity shift, it is the orbit of the rank-one projection `P_L`, cut out by `P^2=P` and `trace(P)=1`. Its stabilizer is `K0=GL(U) × GL(L)`. Use the closed marker argument to pass from `GL(W)` to `K0` on the fiber of this marker.

### Recovering the orthogonal action in the fiber

In that fiber, take the four marked blocks: the pure-line coefficients `t,s` in `T,S` and the two metric blocks `B,D` in their displayed positions. This is a `K0`-equivariant linear projection. An element `(h,lambda)` of `K0`, acting by `lambda` on the line, changes the four tags to

```
t=2 lambda^a,       s=lambda^(-b),
B=lambda^(a-2) h h^T,
D=lambda^(-(b-2)) h^(-T) h^(-1).
```

Their joint orbit is closed. In these coordinates it is defined exactly by

```
(t/2)^ell s^r=1,     B=B^T,     D=D^T,     BD=(ts/2) I_U.
```

For the converse, let `X=t/2` and `Y=s`. The first equation makes both nonzero. Choose integers `u,v` with `ru-ell v=1`, and let `eta=X^u Y^v`. Then `eta^r=X` and `eta^(-ell)=Y`. Taking any `gcd`-th root `lambda` of `eta` gives `lambda^a=X` and `lambda^(-b)=Y`. The equation for `BD` makes `B` nonsingular. Over C every nonsingular symmetric form is congruent to the identity, so one can choose `h` with `h h^T=lambda^(-(a-2)) B`. The equation for `BD` then forces the displayed formula for `D`. This proves the orbit description.

The stabilizer of the four tags has `lambda^a=lambda^b=1` and `h=z o` with `o ∈ O(U)` and `z^2=lambda^(-(a-2))`. The induced multiplier on the displayed payload is `lambda^(a-3) z^3`. Its square is `lambda^(-a)=1`. The possible minus sign can be absorbed by `-I_U`, which acts by minus one on cubics. Conversely every `o ∈ O(U)` arises with `lambda=1` and `z=1`. Hence the action of the joint stabilizer on the payload is exactly its orthogonal action. The affine payload family is closed in the fiber. Applying the closed marker argument again proves reflection and preservation of orbit closure intersection.

Every reduction step has polynomial output size, since `a,b` are fixed and all underlying dimensions increase by a constant factor or additive constant. All inserted coefficients are rational and efficiently computable, and correctness holds for all complex input points. This is an efficient algebraic reduction in the sense of Definition III.3. If instead `a=2` and `b>=3`, replace the defining space by its dual and exchange the two slots. In coordinates this uses the group automorphism `h -> h^(-T)`. Thus the hardness condition is symmetric in `a,b`. Membership is by the definition of TOCI. [Lysikov–Walter, Definitions III.3 and IV.21](https://arxiv.org/html/2411.04639v2).

## Polynomial cases and extension to fixed tuples

The first fundamental theorem for general linear groups gives spanning invariants by full contractions, as stated in Theorem IV.23 and equation (IV.24) of Lysikov–Walter. Each vertex of a contraction diagram is an occurrence of a tensor slot, with one edge per tensor leg. Edges always pair a primal leg and a dual leg. A disconnected diagram evaluates to a product of its connected components. Scalar slots are fixed and can be compared directly.

If `a<=1` or `b<=1`, every nontrivial connected diagram is a star. Its leaves are occurrences of one-leg tensors, and its center is one tensor from the opposite side. For each center slot and each assignment of available leaf labels to its fixed number of legs, evaluate the corresponding scalar contraction. The number of such assignments depends only on the signature. Equality of all these values is equivalent to equality of all invariant polynomials and thus to orbit closure intersection. If one side is empty, there are no nonconstant contractions involving the nonscalar slots.

If `a,b<=2`, every connected nonscalar diagram is a path or cycle, including parallel-edge cycles of length two. Construct block matrices on `D=V ⊕ V* ⊕ C` from each input tensor. Use both `A,A^T : V* -> V` for a primal quadratic, both `B,B^T : V -> V*` for a dual quadratic, the two blocks `C -> V` and `V* -> C` for a primal vector, and the two blocks `C -> V*` and `V -> C` for a covector. Each block is put in its own matrix with all other blocks zero. These matrix letters transform by simultaneous conjugation by `diag(h,h^(-T),1)` under `h ∈ GL(V)`.

Traverse a connected cycle as a trace word in the quadratic letters, choosing a transpose when the traversal reverses that vertex's listed tensor legs. Traverse a path from the one-dimensional block back to that block, using the linear letters for its endpoints. The result is again a trace word. Conversely every compatible trace word is a contraction, with a visit to `C` between paths multiplying their scalar evaluations. An incompatible word has trace zero by its block structure. Thus equality of all traces is exactly closure equivalence.

For two inputs, run linear span closure under left multiplication by the corresponding pairs of matrix letters, starting at `(I,I)`. The ambient vector space has dimension `2(dim D)^2`. Any basis accepted by this algorithm can be chosen from words of length at most that dimension. The trace difference vanishes on this basis precisely when all trace words agree. This uses polynomially many arithmetic operations and Gaussian elimination. In rational encodings the entries of these bounded-length words have polynomial bit length: one can clear all input denominators with a single polynomial-bit common denominator, and a product of `k` resulting integer matrices has entry lengths bounded by `k` times the maximum cleared entry length plus `O(k log(dim D))`. The same argument in a fixed rational basis handles fixed number fields. Exact linear algebra then has polynomial bit cost.

Finally, when the fixed signature has `a,b>=2` with one at least three, fill all other slots with zero and use the pair reduction. The insertion of zero slots is equivariant with closed linear image, so it reflects as well as preserves closure intersection. This covers every fixed pure-power signature. [Lysikov–Walter, Theorems II.7 and IV.23](https://arxiv.org/html/2411.04639v2).

## Attribution and verification status

The TOCI model, the complete two-cubic orthogonal source, and the contraction-invariant characterization are due to Lysikov and Walter. The first-stage orthogonal compression adapts the earlier MathProofs orthogonal marker construction. The present pure-power dichotomy uses contractions to extract a closed marker while all payload terms vanish in that extraction. It then extracts a closed metric-and-line tag orbit with exactly the needed orthogonal action on the payload. Exact sparse integer contraction controls in dimension two passed for eleven arity pairs: (3,2), (4,2), (5,2), (6,2), (3,3), (3,4), (4,3), (4,5), (5,3), (6,3), and (7,3). Each included nonzero signed trace-free payload. These controls check the evaluated markers; the uniform claims rest on the proof. This is an informal mathematical proof and makes no publication-priority claim.
