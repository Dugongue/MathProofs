# Recovering the full determinant coset from a small tensor mode

Let $q$ be fixed, let $T,S$ be arbitrary explicitly given 3-tensors over $\mathbb F_q$, and let $r$ be the minimum of their three concise mode ranks, after rejecting unequal ranks. Let $L$ be the input length. There is a deterministic ordinary TI oracle algorithm that returns an empty transporter or one explicit transporter together with generators for the image of the entire stabilizer under the three determinants. It uses
$$
 q^r \operatorname{poly}(r,\log q)
$$
oracle calls on polynomial-size instances, and runs in $q^{O(r)}\operatorname{poly}(L)$ time apart from the oracle evaluation. In particular it decides all prescribed determinant triples, including special-linear isomorphism, in polynomial time using an ordinary TI oracle whenever $r=O(\log L)$. This is a polynomial-time Turing reduction on that rank regime. It requires no supplied isomorphism, frame, invertible slice or symmetry description.

The following proof uses the indexed compatibility principle from Ward and Trellis. Stabilizer information is kept on a shared ordered basis of only one mode. The other two components of every selected transporter are recovered jointly from their ordered matrix equations.

## Concise support and exact vector queries

For each mode compute the image of the corresponding tensor contraction map into that mode by Gaussian elimination. The tensor lies in the tensor product of these three support subspaces. Every transporter restricts to an isomorphism of the support subspaces, because contraction images transform covariantly. Conversely any transporter of the supported tensor extends to the original spaces. In a mode with positive codimension, the determinant of the extension can be chosen freely by rescaling one vector in a complementary basis. Choices in different deficient modes are independent and preserve the transported tensor. Thus we may do the main calculation on concise supports. Full-support modes retain their original coordinate bases and determinants. Deficient modes acquire every nonzero determinant on lifting. To produce an actual full transporter, extend the supported maps on any chosen complements. Zero and dimension mismatches are handled directly. A zero-dimensional mode has determinant group $\{1\}$.

Permute the three mode roles in the proof so the first concise mode has dimension $r$. A query consists of both tensors plus ordered lists $u_1,\ldots,u_t$ and $v_1,\ldots,v_t$ in their first modes. The required answer means there is one tensor transporter taking each $u_i$ to $v_i$, with the other two maps unrestricted. Encode this with a constant number of order-at-most-three structural tensors. Use an auxiliary $t$-dimensional space $P$ with the shift $Je_i=e_{i+1}$ for $i<t$ and $Je_t=0$. Tie a fixed one-dimensional sort to the vector $e_1\in P$ by a linear map. Fix its scalar by the ordinary multiplication map of the one-dimensional field sort. Every automorphism of these structural tensors acts identically on $P$, since it commutes with $J$ and fixes $e_1$, whose iterates give a basis. On the source attach the linear map $P\to V_1$ with values $u_i$; on the target attach the map with values $v_i$. The isomorphism condition for this map is exactly the required list of pins. Any actual transporter having those images extends across the extra sorts by the identities. For $t=0$ the original tensor query suffices. Compile these fixed-size tensor systems to ordinary 3TI. [Chen–Grochow–Qiao–Tang–Zhang, Theorem 4.1](https://arxiv.org/html/2306.03135v2#S4)

Suppose a query answers yes. Complete the first-mode matrix by choosing the images of an ordered source basis, one vector at a time. Keep any already pinned images and test the $q^r$ possible new images by the exact-list queries. At least one works at each step. The final first-mode matrix $F$ is known and has a lift to a true transporter. When applying this procedure below, every prescribed input list is already a prefix of the chosen source basis.

## Constructing a lift of the first-mode matrix

Use the tensor convention $B_i=X(\sum_j F_{ij}A_j)Y^{\mathsf T}$, where the $A_j$ and $B_i$ are the source and target slice matrices, and $X,Y$ are the second and third transporter factors. Put $C_i=\sum_jF_{ij}A_j$ and $Z=Y^{-\mathsf T}$. The remaining equations are exactly
$$
 XC_i=B_iZ\quad(1\leq i\leq r),\qquad X,Z\text{ invertible}.
$$
These are constructive isomorphism equations for the two ordered representations of the parallel-arrow quiver. They are ordinary finite-dimensional module isomorphism equations. For example, act on the direct sum of the two vertex spaces by the two vertex projections and the given parallel-arrow maps with all other blocks zero. An isomorphism must preserve the vertex summands and intertwine those ordered maps. The constructive module isomorphism algorithm returns $X,Z$ in polynomial time, with no assumptions on individual slice ranks. Then $Y=Z^{-\mathsf T}$. [Brooksbank–Luks, constructive module isomorphism](https://ix.cs.uoregon.edu/~luks/ModIso.pdf)

This yields an actual transporter for $T,S$ using at most $rq^r+1$ TI queries, or correctly reports that no transporter exists. The same method constructs constrained automorphisms of $T$ whenever a list query on $T,T$ answers yes.

## Generate the first-mode image from indexed point orbits

Let $G=\operatorname{Aut}(T)$, $H=\pi_1(G)\leq\operatorname{GL}_r(q)$, and let $H_i$ be the pointwise stabilizer in $H$ of $e_1,\ldots,e_i$. For all $0\leq i<r$, compute the full orbit $H_i e_{i+1}$ using $q^r$ ordinary TI queries. One query pins $e_j\mapsto e_j$ for $j\leq i$ and $e_{i+1}\mapsto v$ for a proposed next image $v$. No group generators are needed for this step.

Maintain an explicit subgroup $M\leq H$, initially trivial, together with the actual lifts in $G$ of its generators. From the current generators, build their permutation action on all vectors of the first mode and compute the pointwise stabilizers $M_i$ and their listed orbits by permutation-group algorithms. This uses polynomial time in $q^r$. If $M_i e_{i+1}$ misses some $v\in H_i e_{i+1}$, construct one actual lift in $G$ using those $i+1$ exact pins and the greedy completion. Its first-mode matrix lies outside $M$. Adjoin it and repeat. Each addition at least doubles the order, so there are at most $\log_2|H|\leq r^2\log_2q$ successful additions.

If there is no missing point in any row, then $M=H$. Indeed, the common orbit sizes are the respective successive indices in the chains. The last pointwise stabilizers are trivial, so multiplying the indices gives $|M|=|H|$. Thus we have actual lifts $g_1,\ldots,g_s\in G$ of generators of the **entire** image $H$, without enumerating $\operatorname{GL}_r(q)$ or completing every point query. The total number of TI queries including the preceding steps is at most $1+(2+r^2\log_2 q)rq^r$. Construction and postprocessing of each individual query take $\operatorname{poly}(L)$ time at the fixed field. Accepting a destination retains only its vector and a yes bit. Each chosen completed first-mode matrix then incurs one polynomial-time module solve. The explicit orbit computations on the $q^r$-element domain take polynomial time in $q^r$ per round, separately from the oracle calls.

## Compute the determinant image of the kernel algebra

The kernel of $\pi_1:G\to H$ consists of the tensor automorphisms whose first map is the identity. In the same slice convention the other two components of such an automorphism are $X$ and $Z^{-\mathsf T}$, where $(X,Z)$ is a unit of the algebra
$$
 R=\{(X,Z):XA_i=A_i Z \text{ for every }i\}.
$$
The algebra is computed by linear equations, with componentwise multiplication. A pair is a unit exactly when both its entries are invertible. One direction follows by projecting an inverse in $R$ to each matrix algebra. For the other, multiply the displayed equations by the two inverses to obtain that the pair of inverses also lies in $R$.

Compute the radical $J$ and a decomposition
$$
 R/J \simeq \prod_a \operatorname{Mat}_{s_a}(E_a)
$$
over finite extension fields $E_a/\mathbb F_q$. The natural second and third coordinate spaces are left $R$-modules via the two projections. For each factor $a$, let $\mu_{2,a}$ and $\mu_{3,a}$ be the multiplicities of its natural simple module in all radical layers of those two modules. They are computable by finding the isotypic projections on the layers and dividing their base-field dimensions by $s_a\dim_{\mathbb F_q}E_a$. To justify this, each layer is semisimple over $R/J$ because it is annihilated by $J$. The determinant of a unit on a filtered module is the product of its determinants on the graded layers. On one copy of the natural simple module for factor $a$ this determinant is $N_{E_a/\mathbb F_q}(\det_{E_a}\overline u_a)$. Consequently the kernel's determinant image is exactly the subgroup generated by the triples
$$
 \bigl(1,\zeta^{\mu_{2,a}},\zeta^{-\mu_{3,a}}\bigr)
$$
as $a$ ranges over the factors, where $\zeta$ generates $\mathbb F_q^\times$. Indeed units lift across the nilpotent radical, matrix determinants and finite-field norms are surjective, and the factors in the quotient can be chosen independently. The inverse in the third tensor mode accounts for the minus sign. All fixed-field algebra operations and filtration computations take polynomial time. [Ivanyos–Qiao, constructive finite-field algebra decomposition](https://arxiv.org/abs/1708.03495)

The determinants of the selected $g_j$ together with the kernel triples generate the whole stabilizer determinant image. For any $g\in G$, its image in $H$ is a word in the first-mode images of the $g_j$. Dividing $g$ by the corresponding word in the actual lifts gives an element of the kernel. This proves exactness without a generating list for the kernel matrices themselves.

## The resulting determinant coset

If $g_0$ is a computed transporter from $T$ to $S$, their full transporter is $g_0G$. The determinant profile is the single coset
$$
 \det(g_0)\,\det(G) \subseteq (\mathbb F_q^\times)^3.
$$
Use subgroup membership in this fixed finite group to decide any prescribed triple. For the original determinant subgroup, discard the concise determinant values on the deficient modes. Retain all coordinates on full-support modes, and adjoin a generator of the independent factor $\mathbb F_q^\times$ in each deficient coordinate. This is exact by the independent complementary extensions. The explicit transporter is extended to the original spaces as above.

Grochow–Qiao IV already used one-mode individualization and projective stabilizer chains, with enumeration exponential in the tensor mode. The present computation uses exact ordered pins, keeps the full determinant values of the few constructed lifts, and computes the remaining determinant image through the ordered-slice unit algebra. It supplies a smallest-concise-mode bound for the **entire determinant coset**. The inputs are raw in that rank range. The proof leaves unrestricted ranks open and does not combine its adaptive queries into one ordinary TI instance. [Grochow–Qiao IV, §§7.3–7.4](https://arxiv.org/html/2306.16317v2#S7.SS3) · [Special-linear containment question](https://arxiv.org/html/2306.03135v2#S1.SS5)
