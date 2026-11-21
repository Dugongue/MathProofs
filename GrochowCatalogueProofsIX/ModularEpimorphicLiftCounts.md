# Exact counts of epimorphic lifts across modular layers

## GP-0363

Let $G,Q$ be Cayley-table groups with a supplied epimorphism $\alpha:G\to Q$, and put $A=\ker\alpha$. Consider a split target $H=B\rtimes Q$, where $B$ is a displayed direct sum of finite $\mathbb F_p Q$-modules with simple tops. There is a polynomial-time exact count of epimorphisms $G\to H$ inducing $\alpha$ under the conditions below. They allow unbounded top multiplicity and nonsemisimple modules, including repeated nonsplit two-layer modules for a $p$-group quotient.

Write the summands as $U_j$, with simple tops $S_j=U_j/\operatorname{rad}U_j$. Work with supplied identifications of isomorphic tops. Require that every endomorphism of $S_j$ lift to an endomorphism of $U_j$. For summands sharing one top, the image subspaces $W_j$ defined below must be nested, in some order. In particular this holds when all summands with one top are copies of the same module. These conditions can be tested by linear algebra from the presented module actions and top maps. For a $p$-group $Q$ and a simple-top module the top is the one-dimensional trivial module and the endomorphism lifting condition is automatic. Its radical is the span of $(q-1)u$ over $q\in Q$.

A homomorphism above $\alpha$ has the form $g\mapsto(z(g),\alpha(g))$, where the crossed homomorphism equation is
$$
z(gh)=z(g)+\alpha(g)z(h).
$$
Solve these equations on the Cayley table for each summand separately. Denote its solution vector space by $Z_j$. The restriction to $A$ is additive, vanishes on $A'A^p$, and is equivariant for conjugation by $G$. Thus restricting and then projecting onto the top gives a linear map
$$
Z_j\longrightarrow \operatorname{Hom}_{\mathbb F_p[G/A]}(A/(A'A^p),S_j).
$$
Let $W_j$ be its image and $p^{k_j}$ the size of its kernel. If the simple top is identified with $S$, let $D=\operatorname{End}_{\mathbb F_p Q}(S)$, a finite field. The endomorphism lifting hypothesis makes $W_j$ a $D$-subspace, since postcomposition on $U_j$ preserves the crossed homomorphism equation and respects the top projection.

The map is onto $B\rtimes Q$ if and only if $z(A)=B$, since $\alpha$ is onto and the image over the identity quotient element is exactly this subgroup. The image of $A$ is a $Q$-submodule of $B$. It equals $B$ precisely when its projection onto $B/\operatorname{rad}B$ is onto, by the finite-module Nakayama lemma over $\mathbb F_p Q$. For one simple type $S$ repeated $m$ times, the component maps to $S$ must then be linearly independent over $D$. Indeed a proper submodule of $S^m$ is killed by some nonzero map to $S$, given by a $D$-linear combination of the coordinate projections, and conversely. Surjectivity for distinct simple types imposes no coupled constraints, because their direct sum is semisimple and different simple types share no nonzero quotient.

Order the $m$ spaces for one type so $W_1\subseteq\cdots\subseteq W_m$. With $j-1$ independent rows already chosen, their span lies in $W_j$, and exactly $|W_j|-|D|^{j-1}$ choices continue the independent sequence. If a step has no choices, the answer is zero. Otherwise the final count is the product, over simple types, of these factors, times $p^{\sum_j k_j}$ over all summands. After choosing the top maps, the lift choices in the $Z_j$ are independent and each has exactly its kernel size. Sizes and inclusions are obtained over the prime field by linear algebra. All arithmetic is polynomial in the table and displayed module sizes, including the bit length of the answer.

For example, take $Q=C_p$ acting on $U=\mathbb F_p^2$ by one nontrivial unipotent Jordan block. Any multiplicity $m$ in $U^m$ gives a nonsplit action with two elementary layers, and the exact formula applies to every supplied source epimorphism. More generally simple-top modules can have arbitrary radical lengths in this theorem. [Group epimorphism context](https://arxiv.org/html/2609.07429v1#S7) · [Earlier abelian quotient rank tests](https://github.com/Dugongue/MathProofs/blob/3454ca222e13e2f12bf232b920771763bf8a7d1a/GrochowCatalogueProofsVI/MarkedQuotientSeparation.md)
