# A maximal proper effective enlargement has a decidable orbit

**Theorem.** Let F be a finitely generated free group, R a normal subgroup, and H the fiber product consisting of pairs (u,v) with uv⁻¹ in R. Use the fixed integral representation of F and the action on multiplication tensors described in the companion proofs. Suppose K contains H and is a maximal proper subgroup of F × F. If K is computably enumerable as a set of pairs of free-group words, then membership in the K-orbit of the standard multiplication tensor is decidable on the family T_s with s supplied as an F-word. In particular this applies to every finitely generated maximal proper enlargement.

The same statement applies if the input is only the integer coefficient array of T_s, promised to belong to this family. Evaluate at (I,I) to recover its integer matrix s. Enumerate F-words and compare their integral matrices to s to recover a word. Faithfulness ensures correctness, and the promise ensures termination. This decidability conclusion concerns fixed groups. It claims no uniform algorithm to recognize maximality or to find such an overgroup.

### The exact subgroup dictionary

Every K containing H contains the diagonal subgroup of F × F. Put N={u : (u,1) belongs to K}. Conjugation by diagonal elements makes N normal in F, and R is contained in N. For every pair (u,v),

    (u,v)(v⁻¹,v⁻¹) = (uv⁻¹,1),

so K consists exactly of pairs with uv⁻¹ in N. Conversely every normal N containing R gives such an overgroup. These assignments preserve inclusion. Since K is maximal proper, N is maximal proper normal and S=F/N is a nontrivial simple group.

The orbit of the standard multiplication tensor under K consists precisely of the T_s with s in N. For an allowed pair (u,v), the resulting parameter is vu⁻¹, which belongs to N exactly when uv⁻¹ does, by inverse and conjugation invariance. Conversely s in N gives the allowed pair (1,s), carrying the standard table to T_s. Thus orbit membership is the word problem in S.

### Two searches that always decide the word problem

The assumption that K is computably enumerable enumerates N by selecting pairs of the form (u,1). Present S by the fixed finite free generating set of F and this enumerable list of relators. Equality of words in a recursively presented group is computably enumerable by listing finite products of conjugates of the relators and their inverses, while also using free reduction.

Given a word w, run the following two searches in parallel.

* Enumerate consequences of the relators N until a proof of w=1 appears.
* Add w as a further relator. Enumerate proofs that each of the finitely many generating letters equals 1 in this enlarged presentation. Halt this search only when proofs for all the letters have appeared.

If w=1 in S, the first search terminates. The second cannot terminate, because S is nontrivial and adding an already true relator cannot trivialize it. If w differs from 1 in S, simplicity says its normal closure is S. Every generator therefore has a finite proof of being trivial after adjoining w, so the second search terminates. The first cannot terminate. These searches decide the required alternative.

This is the classical simple-group word-problem argument attributed to Kuznetsov. The tensor conclusion follows by applying it through the explicit overgroup dictionary. Every finitely generated K is computably enumerable, so it satisfies the hypothesis.

### Sufficient algorithmic conclusion

If a choice of allowed changes is known to form a maximal proper effective enlargement in this ambient pair action, the two searches above furnish a terminating transporter decision algorithm on the entire promised family. This shows precisely what happens at this endpoint of relaxation. Halting-completeness can persist in proper intermediate overgroups, as the protected-factor construction establishes. It cannot persist in a maximal proper effective overgroup of this particular form.

This is an informal deduction, with no novelty claim for the classical simple-group theorem. The group-word encoding and effectiveness assumptions are part of the stated input contract. [Kuznetsov theorem statement and attribution](https://lean-lang.org/eval/problems/boone_higman_simple/) · [Boone–Higman context and simple-group word problems](https://pmc.ncbi.nlm.nih.gov/articles/PMC9305904/) · [Earlier multiplication-tensor construction](https://github.com/Dugongue/MathProofs/blob/main/TensorTransportAndHalting/Profinite.md)
