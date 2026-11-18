# Homomorphism obstructions for graph and algebra reductions to tensor isomorphism

Grochow and Qiao ask which reductions in their paper can be made functorial on the entire source and target categories. Section 2.3 defines the tensor category using arbitrary tuples of linear maps that send the source tensor to the target tensor. Under that convention, the full graph-homomorphism direction to ordinary fixed-order tensor isomorphism is impossible at polynomial output dimension. The same holds from all finite-dimensional commutative unital associative algebras with unital homomorphisms. Both results allow the choice of any object kernel reduction and make no efficiency assumption on the arrow map. [Grochow–Qiao, §2.3, Open Question 7.5 and Appendix B](https://par.nsf.gov/servlets/purl/10494304)

## Mutual restrictions and the obstruction

A tensor's minimal support in mode $i$ is the image obtained by contracting the other modes. Under a morphism into another tensor, the target support is contained in the image of the source support under the $i$-th linear map. If there are arrows in both directions, their support dimensions are equal in each mode. A map in either direction then restricts to invertible maps on the supports and gives an isomorphism of the concise tensors. With a fixed concise isomorphism type, two ordinary tensors are isomorphic exactly when their full ambient dimension tuples agree, since a support isomorphism then extends along the unused directions.

Take all simple bipartite graphs on $n$ vertices that have an edge. Each admits a homomorphism to $K_2$ by a bipartition and a homomorphism from $K_2$ by selecting an edge. Hence every functor to ordinary tensors sends all such graphs to tensors with mutually isomorphic concise parts. If the target order is a fixed integer and every output dimension is polynomial in $n$, there are only polynomially many ambient dimension tuples. By contrast, with a fixed balanced bipartition there are $2^{\lfloor n^2/4\rfloor}-1$ choices of a nonempty labeled edge set. Dividing by $n!$ still gives $2^{\Omega(n^2)}$ isomorphism classes. An isomorphism-reflecting functor is therefore impossible.

The same argument applies to symmetric or alternating shared-factor tensor targets when their repeated mode supports are equal by symmetry. Mutual restrictions there again give an isomorphism on the support and extend along unused directions using the shared map. The claim uses full graph homomorphisms and the paper's all-covariant restriction convention on tensors.

## A positive graph-to-algebra functor

A graph-to-algebra route nevertheless is functorial on those same graph homomorphisms. For a graph $G$, let $V_G$ have one standard vector $e_v$ per vertex. A graph homomorphism $g$ acts by $e_v\mapsto e_{g(v)}$. In $V_G\otimes V_G$ put
$$
D_G=\operatorname{span}\{e_v\otimes e_v\},\qquad
E_G=\operatorname{span}\{e_u\otimes e_v : \{u,v\}\text{ is an edge}\}.
$$
Both subspaces are preserved under the tensor products of these graph maps.

Use a cube-zero commutative algebra with five named degree-one summands $Ke,U,V,U',V'$, where the last four are copies of $V_G$. Give $U\times V$ the quotient product into $(U\otimes V)/D_G$, and $U'\times V'$ the quotient product into $(U'\otimes V')/E_G$. Add products of $e$ with $U,U'$ into the same common copy of $V_G$ and likewise with $V,V'$ into a second common copy. All products are symmetric and land in degree two, which annihilates the algebra. The abovementioned graph maps and induced quotient maps preserve all these products.

Make the named summands recoverable intrinsically by the private leaf construction of the companion functor proof. Namely write $H$ for the sum of the five degree-one semantic spaces and $D=\dim H$. Attach to summand $H_i$ a leaf $L_i=K^i\oplus H$ with the separate product $H_i\times L_i\to H_i\otimes L_i$ by tensoring. The pure leaf space is detected in the degree-one quotient by multiplication rank at most $D$, and $D$ is determined by its total dimension. Modulo the leaves, the maximal proper annihilators of leaf vectors are the complements of the nonzero named summands. For a nonempty graph all five semantic summands are nonzero. The subspace of leaves annihilating the complement of the i-th semantic summand is exactly its own private leaf, of dimension D+i, which identifies the label. Intersecting the other complements recovers the summand itself. For the empty graph D=1 and the total degree-one dimension already distinguishes it from every nonempty input. The same morphism formulas still apply. Quotienting the product space by the leaf products recovers the core. This construction is functorial because each graph map acts on leaves by the identity on $K^i$ and by the given semantic map on $H$.

An isomorphism of the core has equal maps on $U,U'$ and on $V,V'$, because multiplication by the marked line $Ke$ identifies each duplicated pair with its common copy. The maps on $U,V$ carry $D_G$ to $D_{G'}$. The nonzero rank-one elements of a diagonal space are exactly the individual diagonal lines, so the two factor maps are monomial with the same underlying permutation of the vertex labels. Preservation of $E_G$ by these same maps is then exactly the preservation of all edges under that permutation. Thus the functor reflects graph isomorphism. The construction has polynomial size and works over every field.

Unitalizing gives a functor into ordinary commutative unital associative algebras. The original nilpotent algebra is the radical, so unitalization still reflects isomorphism.

## Consequence for the algebra-to-tensor direction

The preceding graph-to-unital-algebra functor, composed with any polynomial-dimension functorial reduction from ordinary unital algebra isomorphism to ordinary fixed-order tensor isomorphism, would give the prohibited graph functor. This rules out a natural extension of that reverse direction to all unital homomorphisms, even on unitizations of commutative cube-zero algebras. Equivalently, all of the resulting unital algebras have arrows both ways through $K$ by augmentation and inclusion. Their polynomially bounded dimensions still encode exponentially many graph isomorphism types. Thus the all-morphism issue persists even when all target algebras are local and their semisimple quotient is scalar.
