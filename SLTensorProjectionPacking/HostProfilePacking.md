# One two-sign query for direct sums with one locally testable character

Work over \(F=\mathbb F_3\). Write determinant signs as elements of
\(\Gamma=\mathbb F_2^3\). Fix a nonzero linear character
\(\chi\colon\Gamma\to\mathbb F_2\), and a vector \(\ell\) with \(\chi(\ell)=1\).
Let \(P\colon\Gamma\to\mathbb F_2^2\) be a surjection with kernel
\(\langle\ell\rangle\).

**Theorem.** Let the inputs be concise three-tensors, with their primitive
centroid blocks recovered from the raw arrays. Suppose that on the local
block family, a prescribed value of \(\chi\) on a block transporter
reduces to one ordinary TI instance in deterministic polynomial time.
Suppose also that for each source block's stabilizer sign group \(H_i\),
either \(\chi(H_i)=0\) or \(\ell\in H_i\). Then the full three-sign
comparison reduces to one explicit two-sign TI instance in deterministic
polynomial time. The reduction makes no decision queries while building
the output. It allows arbitrary numbers of blocks, arbitrary repetitions,
heterogeneous types of the same format, and arbitrary block dimension
parities. In the sign-rigid case \(\chi(H_i)=0\) for all blocks, any
fixed choice of \(\ell\) complementary to \(\ker\chi\) works.

The local compiler needs to accept the raw pair and either requested bit,
and may depend on both blocks. A compiler for bit zero suffices if the
promise also covers the relevant coordinate reflections. The stabilizer
hypothesis is sufficient for correctness on the stated domain. It is not
used as an oracle during construction.

## The profile from an ordinary matching

Recover primitive centroid blocks on both sides and re-express the tensors
in ordered bases consisting of their block bases. Equal formats and equal
concise block counts are required. Reorder the blocks first by dimension
parity vector \(p\in\Gamma\) and then arbitrarily within each bucket,
and let \(c\in\Gamma\) be the determinant calibration from these
concatenated frames to the original frames on the two endpoints. If the
parity bucket counts differ, return a fixed negative instance.

In any genuine ordinary block matching, each matched edge has local
sign \(a_{ij}\), measured in the chosen local bases. The raw sign is
\(c+z+v\), where \(z=\sum a_{ij}\) and \(v=\sum_p p\,t_p\) with \(t_p\)
the inversion parity of the matching in bucket \(p\). The latter formula
follows by exchanging adjacent intervals of dimensions \(d,e\) in an
ordered basis, which contributes \((-1)^{de}\) in that mode.

Assume an ordinary isomorphism exists. In each ordinary type \(\tau\),
choose only for the proof a representative tensor and an isomorphism
from it to each source block and each target block. Let the respective
bits be \(b_i\) and \(d_j\), and let \(H_\tau\) be the representative's
stabilizer sign image. The sign profile of edge \(i,j\) in this type is
\(b_i+d_j+H_\tau\). Therefore every fixed ordinary matching gives the
same possible internal sums
\[
Z=\sum_i b_i+\sum_j d_j+H,\qquad H=\sum_\tau H_\tau.
\]
For each nonempty type, the subgroup contribution can be supplied by
varying one local edge. The choices for the other types are independent.
Thus the true internal sums \(Z\) do not depend on the permutation
choices. The isomorphisms and the ordinary type partition in this
argument need not be computed by the reduction.

The hypothesis implies \(\chi(H)=0\) or \(\ell\in H\). In the first
case \(\chi\) is constant on \(Z\). In the second case every value of
\(P(z)\), \(z\in Z\), can be combined on the same internal sign profile
with either value of \(\chi(z)\) by adding \(\ell\). This is the
condition that permits combining an ordinary bit computation with the
two physically tested signs.

## Read the actual internal signs without block-permutation signs

Make a mixed tensor system containing the original tensor in the ordered
block frames. Add the coordinate algebra \(F^I\) of the set \(I\) of
primitive blocks and its three module actions, which project onto those
blocks in each mode. The algebra multiplication and unit force
permutations of its coordinate idempotents. Compatibility with the three
actions and the original tensor realizes precisely the ordinary block
matchings and their local witnesses.

In each mode attach a second module obtained from the direct sum of its
blocks by adding one scalar vector to each odd-dimensional block. Mark
the inclusion of the unpadded role and the map from the coordinate
algebra sending the idempotent of a padded block to its extra vector
and all other idempotents to zero. A compatible map on a scalar
padding vector is forced to send it to the corresponding chosen vector.
All padded blocks are even-dimensional. Thus the determinant bit of the
whole padded role is its internal bit \(z_m\), with zero contribution
from every block permutation. This leaves a simultaneous actual
transporter on the input tensor, and does not require matching the
blocks during preprocessing.

## Two exact binary computations with ordinary gates

We use variables with allowable values \(\{0\}\) or \(\{0,1\}\), where
the value one is allowed if an attached ordinary TI instance is
positive. First obtain a variable \(x_{ij,a}\) for every source-target
block pair and \(a\in\mathbb F_2\). Its gate is the ordinary local
comparison for \(\chi=a\). Require odd degree at every source and
target block
\[
 \sum_{j,a}x_{ij,a}=1,\qquad \sum_{i,a}x_{ij,a}=1.
\]
Let \(u=\sum_{ij,a}a\,x_{ij,a}\). Conditional on an ordinary matching,
the possible values of \(u\) are exactly \(\chi(Z)\). Indeed the
enabled edges remain within ordinary types. For one type their edge
values lie in \(\chi(b_i)+\chi(d_j)+\chi(H_\tau)\). The odd degrees
leave exactly one contribution from each vertex label, and the sum of
the subgroup terms stays in \(\chi(H_\tau)\). Conversely a genuine
ordinary matching and local choices realize all of \(\chi(Z)\) and
give such variables. The variables need not themselves describe a
perfect matching.

Independently compute the possible \(v\)'s. In a parity bucket, for
every source pair \(i<i'\), give a variable \(y_{ii'jj'}\) to each
ordered pair of distinct target indices from that bucket. Gate it by
the conjunction of ordinary comparisons \(i\simeq j\) and
\(i'\simeq j'\). Require the sum of the variables for this source pair
to be one in \(\mathbb F_2\). Let
\[
 t_p=\sum_{i<i'}\sum_{j>j'} y_{ii'jj'},\qquad v=\sum_p p\,t_p .
\]
If each ordinary type in this bucket has multiplicity one, each
row has exactly one enabled target pair, so this gives the inversion
parity of the unique matching. If some type repeats, swapping its
matched targets gives both parities. Thus any computed bit is
realizable in this case as well. Empty and singleton buckets give
zero. Every actual matching supplies one assignment of these
variables, so both inclusions hold and the computation gives exactly
the true permutation profile. The choices may be treated as
independent of \(Z\), by the preceding matching argument.

Add to these ordinary equations the single constraint
\[
 u+\chi(v)+\chi(c)=0.
\]
All sums here are binary and use explicit coefficients or additional
binary variables. The two live signs to be tested are
\(P(z+v+c)\). They must use the **same** permutation variables that
supplied \(\chi(v)\).

## Keep the permutation variables live in the physical signs

Here is an explicit way to implement the preceding equations and
retain the variables. Represent a binary variable \(x\) by the
two-dimensional coordinate algebra \(F^2\). Its factor idempotents
can be exchanged precisely when its gate \(A\simeq B\) is positive.
To impose this, link the two idempotents via module projections to
two copies of the three tensor roles supporting \(A\) and \(B\),
and place \(A\oplus B\) on these roles at both endpoints. With the
idempotents fixed, identities extend. With them exchanged, extensions
are precisely ordinary transporters between the two tensors in the
two directions, so an isomorphism and its inverse suffice. A free bit
needs no gate. A fixed-false bit can be pinned by a marked first
idempotent. Unequal gate formats can be treated as fixed false.

Split binary rows into equations of arity at most three using free
partial sums. For one row on a list of bits, give it a coordinate
algebra whose idempotents are the satisfying tuples, using zero
right-hand side at the source and the required right-hand side at the
target. Link an idempotent to the indicated bit idempotent in each
participating role by a linear map. The variable permutations force
translation of the tuple, so the row maps exist exactly when the
variable values satisfy the displayed binary row. All local extension
choices are independent after fixing variable values.

A map on the natural vector space of the two coordinate idempotents
has determinant bit exactly \(x\). To read a sum of selected
variables, put fresh direct sums of their coordinate roles in the
system, linked by the fixed-index inclusions. Their determinant bit
is the sum. In particular, this reads \(P(v)\) on the very same swaps
whose assignments satisfy the ordinary equations. Combine these
sums with the indicated padded aggregate roles for \(P(z)\), again
using linked direct sums. Include \(P(c)\) by choosing a
calibrated reference basis in each of the two designated physical
readout roles, or by using a two-idempotent role forced to swap.
Only these two designated role determinants are physically tested.
The retained-two-sign compiler for explicit mixed systems produces
one two-sign three-tensor instance.

All these diagrams use maps of bounded tensor order. They use a
polynomial number of roles and maps with polynomial total
dimension. If a fixed list of role types is desired, index the gate
and row roles by pinned coordinate idempotents and aggregate their
module spaces. The inclusions for the determinant sums are then the
blockwise inclusions indexed by the appropriate fixed idempotents.
In either presentation, compiling introduces no ordinary or signed
decision queries.

## Exactness

An actual determinant-one transporter gives \(c+z+v=0\).
Keep its block maps on the internal system, take its real matching
for the inversion options, and take its own local character values
for the odd-incidence options. This realizes both marked signs and
the binary equations.

Conversely any accepted output yields an ordinary block matching
in the padded internal system, so ordinary types are balanced.
That system determines some \(z\in Z\); the live permutation
variables determine a realizable \(v\). The ordinary character
variables determine \(u\in\chi(Z)\). If \(\chi(H)=0\), then
\(\chi(z)=u\). If \(\ell\in H\), replace \(z\) by \(z\) or
\(z+\ell\) to make \(\chi(z)=u\) while keeping \(P(z)\) unchanged.
The resulting internal sum is realizable on any ordinary matching,
including one with the selected permutation vector \(v\). The
binary equation and the two physical signs now give both
\(\chi(c+z+v)=0\) and \(P(c+z+v)=0\). Since \(\chi\) is
nonzero on \(\ker P\), \(c+z+v=0\). Choose their actual local
maps on that matching and assemble them. This establishes the
full original verdict.

## A heterogeneous family with large blocks

The split-Pfaffian circuit criterion from the earlier packet gives
local ordinary tests for the first matrix sign and makes that
character rigid. It supplies same-format, mutually nonisomorphic
primitive blocks with unbounded dimensions. To make the examples
explicit, fix a large even \(s\). Choose two disjoint even circuits
of linear forms with lengths \(2j\) and \(s-2j\), where
\(2\le j\le\lfloor s/4\rfloor\). Each circuit of length \(k\) is a
basis of \(k-1\) variables and their sum, and the two spans are
independent. Let \(A\) be the diagonal \(s\)-by-\(s\) matrix of the
distinct forms. Use the alternating pencil
\[
\begin{pmatrix}0&A\\-A^\mathsf T&B\end{pmatrix},
\]
with independent labels for every entry above the diagonal of the
alternating \(B\)-block. Its Pfaffian is, up to sign, the product of
the \(s\) forms. The even nullity-one matroid components calibrate
that product by the earlier proof. Its right symmetrizer is
scalar, by the same calculation using independent \(B\)-labels and
the distinct factor lines. It is concise. In a centroid triple
the product of a slice by the second-mode transpose action is a
linear combination of the alternating slices, so that transpose
lies in the scalar right symmetrizer. Conciseness then makes all
three centroid actions scalar. Each tensor is consequently a
primitive centroid block.

All formats are
\((2s,2s,s-2+\binom{s}{2})\), and different unordered circuit
length pairs distinguish ordinary types by Pfaffian covariance
and the matroid decomposition. Arbitrary direct sums and multiplicities
of these blocks satisfy the theorem without any width bound on the
blocks. For example, taking \(s\) copies of each type has joint
input length polynomial in \(s\), while the protected block
dimension is linear in \(s\) and the one format bucket contains a
quadratic number of blocks. The ordinary comparison of a block
and its determinant-negative rebase demonstrates that the local
character is nontrivial on pairs. This example does not assert
hardness of the assembled family.

## Research scope

The [AgentAlphaXiv exact-verifier study](https://huggingface.co/datasets/alphaXiv/AgentAlphaXiv/resolve/a63f46066ac16fcb470f41933415e175825b6bcc/papers/01a1b00f-3a81-791c-98fd-c5daefe85ff8.pdf)
motivated keeping selected permutation bits live across the ordinary
equations and the physical determinant tests. The reduction and
the affine-profile argument are proved here independently of that
study. It reuses
[centroid recovery and ordinary-gated inversion options](https://github.com/Dugongue/MathProofs/blob/main/TensorSignPacking/VectorAssembly.md),
[the retained-two-sign compiler](https://github.com/Dugongue/MathProofs/blob/main/TensorSignChain/RetainedSigns.md),
and the earlier split-Pfaffian circuit criterion. The unrestricted
SL-TI to two-sign TI reduction remains open here, since arbitrary
primitive blocks are not known to satisfy the local compiler and
sign-profile hypotheses. All arguments are informal.
