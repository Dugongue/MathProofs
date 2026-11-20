# A third-sign lock from invariant subspace sums

Work over \(F=\mathbb F_3\). Let \(T,S\) be explicit three-tensors in fixed ordered coordinate frames, of joint length \(L\ge2\).

**Theorem.** Suppose the third mode of each is presented as \(W=\bigoplus_{i\in I}W_i\) with nonzero summands. Suppose the summand labels have a family \(\mathcal C\) of nonempty subsets containing the full set and every singleton, and every nonsingleton member is a disjoint union of two members. Require that every ordinary transporter permute the summands and carry the source family to the target family. Then SL-TI on these pairs reduces deterministically to one two-sign TI instance, in time polynomial in the size of the data and \(\sum_i2^{\dim W_i}\). A polynomial rule extracting such a decomposition and family gives the corresponding raw reduction.

## Preserve one shared transporter

For \(A\in\mathcal C\), put \(W_A=\bigoplus_{i\in A}W_i\) and \(D_A=\bigwedge^{\dim W_A}W_A\). Store only the top line \(D_A\), in a frame obtained by concatenating chosen bases of the \(W_i\) in a fixed order. Store the full exterior algebra \(H_i=\bigwedge W_i\) only for each singleton. On a disjoint pair \(A,B\) with \(A\cup B\in\mathcal C\), record the wedge map
\[
 D_A\otimes D_B\longrightarrow D_{A\cup B}.
\]
It sends the two basis vectors to a signed basis vector. The sign is computed by sorting basis blocks, with an exchange of dimensions \(d_i,d_j\) contributing \((-1)^{d_i d_j}\).

For a fixed-signature encoding, use the coordinate algebras \(E=F^I\), \(P=F^{\mathcal C}\), and the incidence pairing \(E\otimes P\to F\) given by subset membership in primitive idempotent bases. Fix the scalar role. Give \(W,H=\bigoplus_iH_i\) their displayed \(E\)-actions and give \(D=\bigoplus_A D_A\) its \(P\)-action. Include the blockwise multiplication on \(H\), the generator inclusion \(W\to H\), and the map \(D\to H\) including the singleton top lines and vanishing on the others. Add the aggregate map \(D\otimes D\to D\) equal to the recorded wedges on the indicated pairs and zero elsewhere. Keep the original tensor. Mark the vector in \(D_I\) corresponding to the raw ordered basis. In the chosen top frame its coefficient is the inverse determinant of the assembled leaf basis matrix in raw coordinates.

Every system transporter permutes the primitive idempotents of \(E,P\). The incidence pairing forces the \(P\)-permutation to be \(A\mapsto\pi(A)\), where \(\pi\) is the \(E\)-permutation. The \(E\)-action on \(W\) identifies restrictions \(g_i:W_i\to W'_{\pi(i)}\) of the actual original transporter. Exterior multiplication and the generator inclusion force the action on \(H_i\) to be \(\bigwedge g_i\). The inclusions then force all singleton line actions. Induct on \(|A|\), using a disjoint decomposition from the family. Its wedge map is surjective, and naturality forces the action on \(D_A\) to be the top exterior power of the actual map on \(W_A\). The same action satisfies every other decomposition. Thus the root mark tests exactly \(\det g_W=1\). Conversely every original transporter with that sign extends by its permutations and exterior powers, which preserve all equations and the root mark.

The roles and maps have order at most three, with dimensions polynomial in \(|I|,|\mathcal C|,\sum_i2^{\dim W_i}\) and the source dimensions. The [retained-two-sign compiler](https://github.com/Dugongue/MathProofs/blob/main/TensorSignChain/RetainedSigns.md) reads the first two original role signs on this same simultaneous system transporter. Its one output pair gives the desired reduction.

## Two ways to keep the subset list small

A rooted decomposition tree provides such a family by taking all unions of children at each node, together with the leaf singletons. A node with \(b\) unordered children contributes at most \(2^b\) sets. Each union splits into smaller child unions, and each single child is already represented by its subtree. Thus logarithmic unordered fan-out suffices at arbitrary depth.

If the \(k\) children of a node have a cyclic order preserved up to reversal, instead take the unions of children over the nonempty cyclic intervals. There are at most \(k^2+1\) sets. A proper interval can split into one endpoint and a shorter interval, and the full set into one child and its complement. The transporter can now rotate or reflect an arbitrarily large sibling set. The wedge rule includes the determinant effect of those permutations. This case requires the cyclic family to be supplied or recovered compatibly.

## A raw centroid family

For a concise tensor compute its centroid \(C\) by solving \(c_1\cdot T=c_2\cdot T=c_3\cdot T\) in the endomorphism variables. It is a commutative unital algebra under componentwise composition. For two solutions \(a,b\), the mode-one action of \(ab\) can be rewritten as
\[
 a_1 b_1 T=a_1 b_3T=b_3a_1T=b_3a_2T=a_2b_3T=a_2b_2T .
\]
Cyclically obtain closure. Moving \(b\) from mode one to mode two also gives \(b_2a_2T\), so conciseness gives commutativity. If any mode of a centroid triple is zero, conciseness makes the triple zero. The primitive idempotents of \(C\) give a direct sum in each mode, and the equal actions of each idempotent on \(T\) force \(T\) to be the direct sum of the induced tensor blocks. A transporter conjugates the centroid and permutes these idempotents. The dimension triple of each block is preserved.

The idempotents can be obtained by linear algebra over \(F\). Solve \(x^3=x\) in the commutative algebra \(C\), where cubing is linear. The resulting algebra maps injectively into the product of finite fields \(C/J\), where \(J\) is the nilpotent radical. This is because a Frobenius-fixed nilpotent is zero. Its image is the product of the Frobenius-fixed parts, each equal to \(F\): lift a fixed element arbitrarily to \(x\), then take \(y=x^{3^r}\) for \(3^r\) at least the nilpotence exponent, so \(y^3-y=(x^3-x)^{3^r}=0\). All idempotents are fixed by cubing. Simultaneously decompose multiplication by a basis of this fixed algebra using its possible eigenvalues \(0,1,-1\). The joint eigenspaces are precisely its one-dimensional factors. Rescale a generator \(v\) of each factor by the inverse of the nonzero scalar \(\lambda\) with \(v^2=\lambda v\). This gives its primitive idempotent. The entire calculation uses polynomial-time linear algebra.

Bucket the blocks by their dimension triples, and sort the distinct bucket types. Suppose every bucket has at most \(c\log_2 L\) blocks, and each protected-mode block has dimension at most \(c\log_2 L\), for a fixed constant \(c\). There is no bound on the block dimensions in the other two modes or on the number of buckets. For \(\mathcal C\), take every nonempty subset of each bucket and every cumulative union of whole buckets in the sorted order. Remove duplicate subsets. An ordinary transporter preserves this family. Each subset within a bucket can split, and each cumulative union of more than one bucket splits into the preceding union and the next complete bucket. Both the subset list and total exterior dimension are polynomial in \(L\). A mismatch of block profiles rejects ordinary equivalence before the construction.

For example, form the direct sum of two-slice pencils \((I_{m_i},J_{m_i})\) for \(i=1,\ldots,k\), where \(m_i=2i+4\) and \(J_m\) is the nilpotent Jordan block. Each pencil is concise and has scalar centroid. Indeed the identity slice identifies the two matrix-side actions. On the identity the common action has form \(\alpha I+\beta J\), and on the second slice its product with \(J\) still lies in the two-dimensional span. As \(J^2\) is outside that span, \(\beta=0\), and the label map is then also scalar. The displayed blocks supply centroid projectors and commutativity makes every centroid element preserve their images. Consequently these are precisely the primitive blocks. Each protected block has dimension two, and all dimension triples are distinct. The three full dimensions and all positive castling defects grow faster than \(\log L\), although the raw subset condition applies.

## Source and scope

A study in AgentAlphaXiv requires every local verifier to act on the actual current state of its candidate. Here the auxiliary wedge equations share their line actions, and the inductive recovery forces all of them to come from one input transporter. The archived study provides the organizing idea. The proof uses exterior algebra and the existing retained-sign compiler. [Pinned AgentAlphaXiv study](https://huggingface.co/datasets/alphaXiv/AgentAlphaXiv/resolve/a63f46066ac16fcb470f41933415e175825b6bcc/papers/01a1b00f-3a81-791c-98fd-c5daefe85ff8.pdf)

This is an informal sufficient construction. An arbitrary concise single-block tensor can still have a large protected mode and no known small compatible subset family. The unrestricted reverse reduction remains open.
