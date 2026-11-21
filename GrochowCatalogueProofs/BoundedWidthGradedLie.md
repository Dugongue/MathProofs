# GP-0084 · Fixed-parameter graded Lie isomorphism at bounded homogeneous width

**Result.** Grade-preserving isomorphism of explicitly presented graded Lie algebras over each fixed finite field is fixed-parameter tractable in the largest homogeneous dimension. The number of nonzero grades is unrestricted. Uniformly over finite fields the time is q^{O(k²)} poly(N, log q), where k is the largest homogeneous dimension, q is the field size and N is the input length. The algorithm returns an isomorphism. The proof is written.

Compare the two sequences of labelled nonzero grades and corresponding dimensions. Reject a discrepancy. For a grade i of common dimension k_i, choose bases on its two layers. The unknown layer map becomes a variable in G_i=GL(k_i,F_q). Write β_{ij} and β'_{ij} for the bracket tensors from grades i,j to i+j. For each pair of nonzero input grades, require

    g_{i+j} β_{ij}(x,y) = β'_{ij}(g_i x,g_j y).

If the output grade is absent these brackets are identically zero. If some of the three indices coincide, use the same variable for that index. The constraint is a relation on at most three variables. It can be tabulated by checking the displayed equation on basis pairs for each tuple of invertible matrices. The time per relation is q^{O(k²)} poly(N, log q).

Each nonempty local relation is a left coset of a subgroup of the product of the relevant groups. Indeed, it is a transporter for the action of that product group on the tensor of the bracket, with repeated roles using the same group variable. Fixing one transporter g_0 writes all the others as g_0 h for h in the source stabilizer. Consequently the relation is preserved by the coordinatewise operation (a,b,c)↦a b^{-1} c. This operation satisfies both Mal'tsev identities. Embed each G_i into GL(k,F_q) by adjoining an identity block and enforce it with a unary constraint. This gives a common domain and an explicit Mal'tsev operation preserving every constraint.

Use the Bulatov–Dalmau algorithm on the listed relations and furnished operation. Its running time is polynomial in the explicit constraint instance and operation table. There are polynomially many bracket pairs, and the tables, including the operation on the common domain, have size q^{O(k²)} poly(N, log q). The conjunction of constraints is exactly preservation of the bracket by the direct sum of the layer maps. To construct maps after a positive decision, fix the variables one by one by trying their possible values with a unary singleton constraint and keeping a value that preserves satisfiability. Singleton constraints preserve the same operation. This gives the same claimed asymptotic time once constant powers are absorbed.

The proof uses the decomposition into explicitly indexed layers. A problem allowing arbitrary transformations between different grades would require further constraints. The field dependence here supports FPT in k for each fixed field and FPT in the combined parameters k and log q.

[Bulatov–Dalmau, A Simple Algorithm for Mal'tsev Constraints](https://doi.org/10.1137/050628957) · [Derivation and densor methods in tensor isomorphism](https://arxiv.org/abs/2005.04046)
