# Covariant tensor functors and categories with zero morphisms

Informal theorem addressing reverse directions in Grochow–Qiao Open Question 7.5. Fix a finite field k and a tensor order d. No polynomial-size, isomorphism-reflecting functor exists from any of the following ordinary categories into the category of covariant d-tensors, whose morphisms are tuples of linear maps carrying one tensor to the other.

- Finite-dimensional associative algebras with all algebra homomorphisms.
- Finite-dimensional commutative nonunital algebras with all homomorphisms.
- Finite-dimensional Lie algebras with all homomorphisms.
- Augmented local unital algebras with residue field k and all unital k-algebra homomorphisms.

The first category can be taken to consist only of radical-cube-zero nonunital algebras, and the unital category can be taken to consist only of their unitizations. The Lie example has class two. This is a statement about covariant tensor morphisms. An isomorphism reduction alone need not be a functor on those morphisms. It places no restriction on reductions defined only on isomorphisms, or on tensor categories with different variances.

The original question asks which reductions can extend to all homomorphisms and which associated categories support asymptotic spectra. The theorem settles these reverse directions under the stated standard morphism convention. It does not classify every reduction in the paper. Publication priority of this categorical counting argument has not been established. [Grochow–Qiao, Question 7.5](https://epubs.siam.org/eprint/VA7M2DT6DFQMVDVWIBBN/full)

## 1. Mutual tensor restriction determines the concise core

For a tensor T in V_1 tensor ... tensor V_d, let U_i(T) be the smallest subspace in mode i supporting T. Equivalently it is the image of the corresponding flattening into V_i. Every covariant tensor morphism f:T to S satisfies
$$
U_i(S)\subseteq f_i(U_i(T)).
$$
Consequently every mode-support dimension is nonincreasing along a morphism.

If there are morphisms in both directions, all those dimensions are equal. Then each restriction f_i to U_i(T) is an isomorphism onto U_i(S). Thus the concise cores are tensor-isomorphic. If T and S also have the same ambient dimension tuple, extend these core isomorphisms to invertible linear maps between the ambient spaces by choosing complements. This proves that T and S themselves are isomorphic.

In particular, within any collection of pairwise mutually reachable objects of the covariant tensor category, the ambient dimension tuple determines the isomorphism class. At order d with every mode dimension at most M there are at most (M+1)^d isomorphism classes in that collection. Zero mode dimensions and zero tensors obey the same conclusion.

## 2. Every algebra in the source family reaches every other

For ordinary nonunital algebras or Lie algebras, the zero map is a homomorphism between any ordered pair. A functor must therefore send every pair of source objects to mutually reachable tensors.

For augmented local unital algebras A=k plus J_A, the augmentation A to k followed by the unit map k to B is a unital homomorphism A to B for every other such B. This also gives mutual reachability without using zero unital homomorphisms.

We now show that these families have far too many isomorphism types for polynomial ambient dimension.

## 3. Counting source isomorphism types

Let U and W have dimensions a and b, with a+b=n. Every bilinear map
$$
\beta:U\times U\longrightarrow W
$$
defines a radical-cube-zero algebra on U plus W by multiplying elements of U using beta and making every product involving W zero. Associativity follows because every product of three elements vanishes. Distinct beta give distinct multiplication tables in the fixed basis.

There are $q^{a^2b}$ such tables. An isomorphism orbit among all tables has at most the order of GL_n(k), hence fewer than $q^{n^2}$ elements. With a near 2n/3 and b near n/3, the family has at least $q^{c n^3}$ isomorphism classes for one positive constant c and all sufficiently large n.

The commutative case restricts beta to symmetric bilinear maps. There are $q^{a(a+1)b/2}$ choices, giving the same exponential-in-n-cubed lower bound after dividing by $q^{n^2}$. This argument works in characteristic two too. The Lie case instead uses alternating maps, with $q^{a(a-1)b/2}$ choices. Their image is central, so the Jacobi identity holds. They again provide the same lower bound.

For unital local algebras use k plus these nilpotent algebras. The nilpotent ideal is exactly the Jacobson radical, since the quotient is k. A unital algebra isomorphism restricts to an isomorphism of those radicals, so the unitizations retain the lower bound. Their augmentation is unique.

These are explicit structure-constant inputs of length O(n cubed) over fixed k. If a functor has polynomial-size output, every target mode dimension is bounded by a polynomial in n. Section 1 then allows only polynomially many target isomorphism classes, contradicting the source lower bound whenever the functor reflects isomorphisms. This proves the theorem. No hypothesis about P versus NP or a tensor-isomorphism algorithm is used.

The same argument implies an exponential lower bound on the largest output mode for any isomorphism-reflecting functor on this n-dimensional source family, when output is measured only by the fixed-order ambient dimension tuple.

## 4. The asymptotic-spectrum convention matters

The semiring of algebra isomorphism classes uses direct product as addition and tensor product over k as multiplication, with k as its multiplicative unit. If its preorder comes from all unital homomorphisms, k and k times k are mutually reachable through the diagonal and a projection.

A normalized real-valued semiring homomorphism sends k to 1 and k times k to 2. Monotonicity for mutually reachable objects would force those values equal. Therefore the corresponding normalized asymptotic spectrum is empty. The same obstruction holds for nonunital algebra categories using all homomorphisms, since zero maps provide mutual reachability. For Lie algebras no choice of multiplicative structure is needed for the negative conclusion. An all-homomorphism-monotone invariant additive under direct sums and normalized to one on the one-dimensional abelian Lie algebra is already impossible, since that object and its double have zero maps in both directions. Thus no compatible normalized spectrum can use that all-homomorphism preorder and additive convention. This does not assume a naive tensor-product Lie semiring.

This conclusion is about those precise operations and preorder. A tensor restriction preorder, a degeneration preorder, or a choice of embeddings defines a different question. The positive symmetric-tensor spectrum results in the companion [functor note](Functors.md) use their explicitly stated preorder and operations.

## 5. Relation to the positive constructions

The companion functors take covariant tensors into algebra or form categories while reflecting isomorphisms. The reverse algebra-to-covariant-tensor direction above cannot have the same polynomial-size all-morphisms property. Consequently polynomial equivalence of the isomorphism decision problems does not promote to an equivalence of these categories with all homomorphisms.

This is a complete negative answer for the listed reverse directions and a precise nonexistence result for the listed spectral conventions. It leaves the remaining directions of Question 7.5 to be assessed with their own morphism contracts.
