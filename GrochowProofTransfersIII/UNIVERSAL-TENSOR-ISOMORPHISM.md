# Universality of tensor isomorphism for basis-explicit linear structures

**Theorem.** Fix an arbitrary finite linear signature, with relations that are subspaces of tensor powers of the underlying vector space and its dual, and operations that are linear maps from such tensor powers to the underlying space. Over every field \(K\), isomorphism of finite-dimensional basis-explicit models of this signature reduces in deterministic polynomial time to ordinary 3-tensor isomorphism. Here an isomorphism acts by the same change of basis at every primal occurrence and its inverse transpose at each dual occurrence. Relations are transported as subspaces, and operations are transported as maps with their output included.

The reduction first produces a linear model with all relation arities at most three and all operation arities at most two. At this stage every input isomorphism has a unique extension, every output isomorphism restricts to an input isomorphism, and both operations preserve composition. If the largest number of tensor factors in a record is \(d\), counting an operation's output as one factor, the intermediate vector space has dimension \(O_\sigma(n^{\lceil \max(3,d)/3\rceil})\) for input dimension \(n\ge1\). The ordinary unmarked tensor reduction then uses the published arity-three compiler.

This answers Grochow and Qiao's [Open Question 7.4](https://epubs.siam.org/eprint/VA7M2DT6DFQMVDVWIBBN/full), numbered [10.4 in the preprint](https://arxiv.org/html/1907.00309#S10.SS1), in the basis-explicit model defined there. Since padding by one-dimensional factors reduces 3-tensor isomorphism to \(k\)-tensor isomorphism for each \(k\ge3\), the stated universality also holds with \(k\)-way arrays as the target.

## Balanced records

Write \(V^+=V\) and \(V^-=V^*\). For each relation use its tensor word in the two signs. Regard each linear operation \(F:U\to V\) as the tensor in \(U^*\otimes V\) given by the canonical identification with \(\operatorname{Hom}(U,V)\). In this word the input signs are reversed, and the output has sign plus. The tensor word for \(U^*\) uses the tensor product of the dual factors in the original order, with the standard finite-dimensional pairing.

Divide each record's word into three consecutive pieces, as equally as possible. A piece may be empty and then has tensor product \(K\). Fix all parentheses and coordinate orders in the construction depending only on the signature. Every piece and the signwise dual of every piece can be built by a rooted binary tree of products of the single-factor sorts \(V\) and \(V^*\), together with the scalar sort \(K\). Share or reuse a named sort for a word whenever necessary. Every node has at most \(\lceil\max(3,d)/3\rceil\) letters.

## Forcing the auxiliary changes of basis

Take the direct sum \(W\) of the base sorts, the scalar sort and all the product sorts. Mark each summand by a separate unary subspace relation, forcing any isomorphism of the new model to be block diagonal. Include the following named bilinear operations, extended by zero off their specified input sorts.

- Multiplication \(K\times K\to K\) on the scalar sort.
- Evaluation \(V^*\times V\to K\).
- At each product node, the canonical map \((u,v)\mapsto u\otimes v\) from its two child sorts to that node.

An invertible scalar-sort map has the form \(x\mapsto\lambda x\). Preserving multiplication gives \(\lambda=\lambda^2\) and hence \(\lambda=1\). Let \(g\) be the restriction to \(V\). Preservation of evaluation determines the dual restriction uniquely as \((g^{-1})^*\), since evaluating it on \(g v\) has to equal evaluation on \(v\). Preservation at a product node prescribes \(g_1(u)\otimes g_2(v)\) on every pure tensor \(u\otimes v\). Pure tensors span, so the only possible restriction is \(g_1\otimes g_2\). Induction up the chosen trees makes every auxiliary restriction unique. Conversely these forced maps are invertible and preserve all three classes of named operations.

## Encoding every input record

For an input relation, regroup its ambient tensor word as \(P\otimes Q\otimes R\) using the selected pieces. Include the image of the relation as a named subspace of \(W^{\otimes 3}\) through the three summand inclusions. Under a block-diagonal map this relation is preserved precisely when its original subspace is transported by the original tensor-word action.

For an operation, regroup its tensor \(F\in U^*\otimes V\) as \(T\in P\otimes Q\otimes R\). Include the new bilinear operation
\[
(\alpha,\beta)\longmapsto(\alpha\otimes\beta\otimes 1_R)(T)
\]
on the \(P^\vee,Q^\vee\) sorts, with output in \(R\). Give these dual sorts their signwise tensor bases. The auxiliary maps on them are the inverse transposes of the ones on \(P,Q\), by the product induction and the natural pairing of dual bases. If \(g_P,g_Q,g_R\) are the restrictions to the product sorts, then preserving this bilinear map is exactly the equation \(T'=(g_P\otimes g_Q\otimes g_R)T\). This follows by evaluating each side on the covectors \(g_P^{-*}\alpha,g_Q^{-*}\beta\) and using that basis covectors recover every coefficient. Undoing the regrouping, this is precisely preservation of \(F\) as a linear map from its input tensor word to \(V\). Tags and the construction depend only on the fixed signature, so each named record is checked against its own counterpart.

## Assembly, cost and scope

Restricting a target isomorphism to \(V\) and extending by the forced auxiliary maps are inverse operations. Extension respects composition because so do inverse transposes on isomorphisms and tensor products. This identifies isomorphism sets and automorphism groups at the intermediate stage.

All product coordinates, structure constants, relation bases and bilinear maps are explicit. Forming the intermediate tables involves only copying and permuting input entries, plus zero and one for structural maps. The number of nodes and marks is bounded in terms of the fixed signature. Product ranks are the powers of \(n\) bounded above, so the dimensions and the dense table lengths are polynomial. The original dimension can be compared before construction. If there are no nonzero records, the answer depends only on that dimension and can be mapped to a fixed yes or no instance. With any nonzero record and \(n>0\), a dense record of positive length either has at least \(n\) entries or is a scalar independent of the action. In the latter case compare the scalar records separately. This also treats signatures where the dimension is recorded as a header without listing a basis. Zero-dimensional base spaces are covered by the same explicit small construction.

Apply the published Futorny–Grochow–Sergeichuk result on mixed systems of at most three-way tensors, in the basis-explicit formulation of [Grochow–Qiao, Theorem 7.3](https://epubs.siam.org/eprint/VA7M2DT6DFQMVDVWIBBN/full). For a version using only unary subspace marks, give each ternary relation its full product sort with two more canonical product maps and mark the relation there as a unary subspace. This still has polynomial cost, with product dimension at most n to the power d. The same forcing argument proves unique extension across the added nodes. In that version each unary relation can also be expressed as a linear inclusion from a dedicated auxiliary space based on its supplied basis, with its change of basis uniquely fixed by the inclusion. Thus the data needed by the published compiler can be viewed directly as a mixed system of linear and bilinear maps. It gives one ordinary tensor isomorphism instance over the same field. For \(k>3\), append \(k-3\) one-dimensional factors with basis vector one. Their invertible changes of basis only contribute a nonzero total scalar, which is absorbable into a change of basis on the first mode. This verifies the padding in both directions.

The exact extension statement concerns **isomorphisms of the intermediate model**. We use the published compiler for the final ordinary decision reduction. The argument for dual factors uses an inverse and makes no functoriality claim for singular source morphisms.

## Source and verification

The use of rooted auxiliary product trees transfers the local-to-global step from [Davis and Astra's high-girth Frankl proof](https://github.com/1337isnot1337/solved-conjectures/blob/892c04046aadc8731dd510bb9c9b3ca1a086bae1/results/frankl-generator-families/HIGH-GIRTH.md). There the conditioned boundary makes child contributions combine by a fixed local rule and the root is recovered by induction. Here the marking of every internal node forces the product of its two child maps, with dual evaluation fixing the boundary. The low-arity compiler itself is prior work. The contribution is the exact arity reduction and its application to the stated universality question.

The full theorem has a written proof. The Lean companion verifies the two local recovery identities. The Python replay checks mixed high-arity examples over prime fields directly in coordinates.
