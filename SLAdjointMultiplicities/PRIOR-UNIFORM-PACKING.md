# Uniform polynomial compilation of mixed tensor systems

Date: 2026-09-13. Earlier MathProofs construction; internal algebraic audit passed. No external novelty claim, no Lean verification, and no claim of unrestricted TI_SL <= TI.

## Theorem

Over every field K, a system of an arbitrary input number c of explicitly represented tensors of order at most three, with arbitrary repeated primal and dual occurrences of its vector spaces, can be transformed in polynomial time into a mixed tensor system with at most fourteen components on four vector spaces. All components have order at most three. Source and target transporters project and extend exactly; the only additional automorphism freedom is an explicit product of general linear groups on marker spaces.

Applying the cached published constant-component mixed-system compiler (Chen--Grochow--Qiao--Tang--Zhang, arXiv:2306.03135v2, Theorem 4.1, rephrasing FGS Theorem 1.1) then gives a uniform polynomial-time many-one reduction to ordinary 3-tensor isomorphism. The bound is polynomial jointly in the number of components and the explicit input dimensions; it has no exponential dependence on the component count.

This use of the published compiler asserts decision equivalence. Although the packing itself has exact all-witness projection and extension, a claim about extracting witnesses from the final ordinary-TI output would require the corresponding property of that final compiler and is not silently assumed here.

## 1. Input and padding conventions

Let V_1,...,V_m be the original vector spaces, with chosen bases. Each component T_c is supported on an ordered list of at most three primal or dual occurrences of these spaces. The same original space may occur repeatedly, including with opposite variances. An isomorphism uses one transformation g_i on V_i and the corresponding inverse-transpose on every occurrence of V_i*.

Introduce a one-dimensional trivial space V_0=K and a chosen nonzero vector u_0. Pad every component to order three by tensoring with u_0 in new primal slots. Enforcing that u_0 is fixed makes this padding exactly equivalent to the original component. Order-zero scalars can first be compared directly; mismatching scalar components give a fixed NO instance, and matching ones may be omitted.

For each padded component c and each slot a in {1,2,3}, create a separate occurrence space W_(c,a), a primal copy of the underlying V_i, even when that slot will later be used dually. Every occurrence is distinct, including repeated occurrences of the same original V_i.

Set

    V = direct sum_(i=0)^m V_i,
    W = direct sum_(c,a) W_(c,a).

## 2. Freeze every original and occurrence label using two tensors

Let L=m+1+3c, one label for every V_i and every W_(c,a). Define

    D=K^L,
    N=direct sum_(ell=1)^L K^ell.

Include the multiplication tensor of D and the D-module action on N for which the primitive idempotent e_ell projects onto the dimension-ell summand.

An algebra automorphism of D permutes the primitive idempotents. A compatible isomorphism of its module N must send the corresponding simple-module summands onto each other. Their dimensions 1,...,L are pairwise different, so every idempotent is fixed. Hence the action on D is exactly the identity. The remaining freedom on N is the product of GL_ell(K), acting independently on its summands.

This reasoning is valid in every characteristic. Distinct dimensions are integer dimensions, not field elements; no field-size lower bound is used.

## 3. Force all occurrence transformations to equal their original transformations

Include a D-action tensor on V, assigning each V_i its own original-space idempotent label. Include a D-action tensor on W, assigning every W_(c,a) its separate occurrence label. Since the action on D is already fixed, these tensors force every individual summand of V and W to be invariant.

Define the linear map

    f:W -> V

to be the fixed identity identification from each W_(c,a) to its underlying V_i, followed by inclusion of V_i in V; on a direct sum of vectors, add these images. Include f as an order-two mixed tensor in W* tensor V. Also include the order-one vector u_0 in the V_0 summand of V.

Preservation of f is the equation g_V f=f g_W. Restrict it to any one occurrence space W_(c,a). Both sides land in its underlying V_i, so it forces precisely

    g_(W_(c,a)) = g_i

under the chosen copy identification. It introduces no equation between different original spaces. Preservation of u_0 forces g_0=1.

Conversely, every list of original transformations g_i extends uniquely to V and W by these rules and preserves all the structures described so far. The action on N remains arbitrary within its explicitly known blocks.

There are now six components: D multiplication, its action on N, its action on V, its action on W, the linking map f, and the marked trivial vector u_0.

## 4. Pack all data tensors into eight variance types

For each sign pattern epsilon=(epsilon_1,epsilon_2,epsilon_3) in {+,-}^3, form one tensor

    S_epsilon in W^(epsilon_1) tensor W^(epsilon_2) tensor W^(epsilon_3),

where W^+=W and W^-=W*. For every padded original component with that variance pattern, embed its three slots into the three private summands

    W_(c,1)^(epsilon_1),
    W_(c,2)^(epsilon_2),
    W_(c,3)^(epsilon_3),

and add these embedded tensors. Use zero if a pattern has no component.

Every occurrence summand is individually invariant under g_W, so every ordered triple of occurrence summands is invariant under the corresponding tensor-product action. Distinct input components occupy distinct such blocks. Consequently equality of S_epsilon under the action is equivalent, block by block, to every original tensor equation of that variance pattern. No component can mix with another, and no cancellation between different components is possible.

This adds eight order-three tensors, for a total of fourteen components supported by only the four spaces D,N,V,W.

## 5. Exact transporter correspondence

Given a source-system isomorphism (g_i), extend it by g_0=1, by its repeated actions on the occurrence copies, by the identity on D, and by any blockwise invertible action on N. All fourteen packed tensor equations hold.

Conversely, a packed-system isomorphism fixes D pointwise by the distinct-multiplicity argument, preserves every summand of V and W, identifies every occurrence action with its original action by f, and fixes V_0 by u_0. Each data tensor then imposes exactly the original equations on the recovered g_i.

Thus projection onto the original spaces is surjective on transporter sets. On automorphism groups the kernel is exactly

    product_(ell=1)^L GL_ell(K),

coming from N. It has no action on the original variables. In fact the packed-system automorphism group is the direct product of the original automorphism group with this marker group.

This is an ordinary-GL statement. The marker group has determinant freedom; the packing is not asserted to preserve special-linear constraints on its new ambient spaces.

## 6. Polynomial output bounds

Let n=sum_(i=1)^m dim V_i. Then

    dim D=m+1+3c,
    dim N=(m+1+3c)(m+2+3c)/2,
    dim V=n+1,
    dim W=sum_(c,a) dim V_(i(c,a)) <= 3c(n+1).

Writing any of the fourteen dense tensors therefore takes polynomial time and space in n+m+c. Every original tensor entry is copied into one known block of one data tensor. The structural arrays consist only of zero and one entries in the prescribed bases.

The published Theorem 4.1 bounds its final dimensions by a polynomial in the sum of supporting dimensions and an exponential depending only on the component count. Here that count is fourteen, an absolute constant. Its final output and running time are consequently polynomial in the original input dimensions and component count.

## 8. Explicitly dense higher-order systems

There is a further direct corollary for explicitly dense input tensors of arbitrary order. For each component, introduce successive prefix tensor-product spaces, canonical bilinear tensor-product maps, and the final tensor as a vector. Preserving the canonical maps forces each prefix action to equal the tensor product of the original primal or dual actions. Dual occurrences may be linked by a canonical evaluation pairing to an occurrence-copy variable.

Each prefix dimension is at most the product of that component's factor dimensions, which is its explicit dense entry count; the sum over prefixes is at most its order times that count. The number of canonical maps is also linear in the total input order. Apply the uniform low-order packing to these polynomially many components. This gives a polynomial ordinary-TI reduction for explicitly dense higher-order systems as well.

This corollary does not apply to an implicitly specified volume tensor or high derivative supplied only by a circuit. Materializing their prefixes can be exponential in the compact circuit input; that representation distinction is retained.
