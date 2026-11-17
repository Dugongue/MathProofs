# A sufficient reduction through the ordinary orbit of a conjunction gadget

Let $E(x,y)$ denote one-sign tensor isomorphism over $\mathbb F_3$, using determinant one in the first mode. Let $O(x,y)$ denote ordinary tensor isomorphism. Write $E^{[2]}$ for the equivalence relation on ordered pairs defined by testing $E$ in both coordinates. All tensor formats are fixed on each pair being compared. The statements concern ordinary polynomial-time many-one reductions on decision languages.

**Theorem.** A polynomial-time kernel reduction $E^{[2]}\to E$ gives $E\le_m^p O$ by a positive conjunction of two ordinary TI tests. Consequently it gives unrestricted $\mathrm{SL\text{-}TI}\le_m^p\mathrm{TI}$ over $\mathbb F_3$. The conclusion also holds for an encoder with a shared auxiliary structure computed from the unordered set of input tensors. Conversely, if $E\le_m^p O$, then such an unordered-set-context encoder exists.

The adjective kernel has the usual meaning that the reduction on a comparison sends the two compared objects through the same object map, before comparing their outputs. It is more restrictive than a general many-one reduction. [Fortnow–Grochow, Complexity Classes of Equivalence Problems Revisited](https://arxiv.org/abs/0907.4775) · [Finkelstein–Hescott, Polynomial-time kernel reductions](https://arxiv.org/abs/1604.08558)

## 1. Recover the original answer through two ordinary comparisons

Each ordinary orbit of 3-tensors is a union of at most two one-sign orbits. To see this, let $G$ be the product of the three general linear groups in a fixed format, and $H$ the kernel of the determinant sign in the first mode. The index $[G:H]$ is at most two. The $G$-orbit of $T$ is the union of the images of the at most two left cosets of $H$, each of which is a single $H$-orbit. The same conclusion holds when one mode has dimension zero or the ordinary stabilizer realizes both signs.

Suppose a polynomial-time map $f$ sends ordered tensor pairs to tensors and satisfies
$$
 E(f(u_1,u_2),f(v_1,v_2))\quad\Longleftrightarrow\quad
 E(u_1,v_1)\ \wedge\ E(u_2,v_2).
$$
Even a version with different side maps $f_L,f_R$ suffices when both are given separately. Reflexivity forces $E(f_L(\mathbf u),f_R(\mathbf u))$ for every tuple $\mathbf u$, so replacing $f_R$ by $f_L$ preserves correctness.

On input $x,y$ form three tuples
$$
       p_0=(x,x),\qquad p_1=(x,y),\qquad p_2=(y,y).
$$
Compute $f(p_i)$ for $i=0,1,2$. If $E(x,y)$ holds, the three tuples are $E^{[2]}$-equivalent, so their images are all ordinarily isomorphic. If $E(x,y)$ fails, the three tuples are pairwise $E^{[2]}$-inequivalent. Their images are pairwise $E$-inequivalent, so an ordinary orbit cannot contain all three. Thus
$$
 E(x,y)\quad\Longleftrightarrow\quad
 O(f(p_0),f(p_1))\ \wedge\ O(f(p_0),f(p_2)).
$$
The two ordinary comparisons can be packed into one ordinary TI instance by assigning independent types to the two tensor triples and applying the fixed-signature tensor-system compiler. This gives the claimed deterministic polynomial-time many-one reduction. [Chen–Grochow–Qiao–Tang–Zhang, Theorem 4.1](https://arxiv.org/html/2306.03135v2#S4)

Use the calibrated annihilator transfer in the preceding collapse packet to make each of the three character types a one-sign query. An ordinary transporter sign set is empty or an affine coset in $\mathbb F_2^3$. Such a set contains zero exactly when it meets every linear hyperplane through zero. Hence seven character queries suffice to test all three signs. Composing the reduction above on every query and packing their ordinary conjunction gives unrestricted $\mathrm{SL\text{-}TI}\le_m^p\mathrm{TI}$. The ordinary lower reduction is already proved in the interval packet.

## 2. A common context may depend on the entire input

Suppose a polynomial-time procedure computes a common structure $c$ from the four raw tensors entering a comparison, using only their unordered set of distinct members. Suppose it sends the two ordered tuples through one map $f_c$ and correctly reduces their conjunction to a single one-sign instance. The same theorem applies even though this is a jointly dependent procedure.

Indeed each of the three comparisons between distinct $p_i$'s uses the same unordered union $\{x,y\}$. The shared context is therefore identical for all three comparisons. Correctness implies that the three tensors $f_c(p_i)$ are pairwise $E$-equivalent when $E(x,y)$ holds and pairwise $E$-inequivalent when it fails. Apply the same ordinary-orbit argument. It is enough for a more general shared context to agree on these three cross-comparisons, with one map used on both outputs. This covers some algebra and module constructions built from a shared raw family without a distinguished comparison pairing.

This condition can be tested on a proposed construction. A construction satisfying it would produce ordinary TI instances for the original determinant constraint by the explicit two-test method above.

## 3. Converse for the common unordered context

Suppose there is a polynomial-time many-one reduction from $E$ to ordinary TI. It may jointly use its two input tensors. We construct the encoder in Section 2.

First observe that ordinary TI comparisons can be packed by any fixed conjunction or disjunction. For conjunction, use the usual independent-sort tensor-system compiler or a direct sum of tagged absolutely indecomposable data. Here is a precise disjunction construction. Given two ordinary comparisons $(a,b)$, $(c,d)$, take the ordinary isomorphism type $P(x,y)$ of an encoded ordered pair. The four objects $P(a,c),P(a,d),P(b,c),P(b,d)$ can all be made concise, absolutely indecomposable and of one common format as follows.

* Compact each of the two comparisons to intrinsic support bases. If its shape or support sizes disagree, substitute a fixed ordinarily inequivalent concise pair of equal format. If both members are zero, substitute a fixed positive concise pair. An explicit equal-format negative pair consists of the two label pencils $\operatorname{diag}(x,y)$ and $xI_2+yJ_2$, where $J_2$ is nonzero nilpotent. Their determinants have respectively two distinct projective roots and one double projective root, so ordinary tensor transport is impossible.
* Apply the scalar-centroid embedding from the preceding packet to each tensor, using one common tag size within the first slot and another within the second slot. The sizes can be chosen to make the two ordered formats different. This embedding carries precisely the ordinary comparison of the original concise inputs, and makes every slot tensor absolutely indecomposable. For $P(x,y)$, direct sum these two slot tensors and apply the same scalar-centroid embedding again, using one tag size for all four combinations. The inner direct sum carries the ordered comparison because its two primitive blocks have distinct formats. Its shape is the same for each of the four combinations. Thus the final $P$'s are absolutely indecomposable and of equal format.

Now compare the ordinary tensors
$$
       P(a,c)\oplus P(b,d)\quad\text{and}\quad P(a,d)\oplus P(b,c).
$$
The primitive centroid blocks permit exactly the two possible matching patterns. The order-preserving match exists exactly when $c$ and $d$ are ordinarily equivalent, since each first coordinate then matches itself. The order-reversing match exists exactly when $a$ and $b$ are ordinarily equivalent. This realizes ordinary disjunction, including repeated isomorphism types. Iterating this construction a fixed number of times gives a polynomial-time map. Ordered conjunction is simpler: use a direct sum whose slot tensors have mutually distinct large formats, or apply the fixed-signature compiler. These arguments use the earlier determinant-neutral marker embedding only for its ordinary reflection and its scalar centroid. The following ordinary version also suffices.

For an explicit ordinary version, write a concise slot tensor as $M(w):V\to U$. Add a two-dimensional label $c=(x,y)$ and large fixed matrix spaces $B,A$. Add the block-diagonal tag $G(c)=\operatorname{diag}(xI_{r_1},yI_{r_2},(x+y)I_{r_3}):B\to A$, with all $r_i>\dim U$. On the enlarged input and output use
$$
 \widehat M(w,c):V\oplus(U\otimes(F^2)^*)\oplus B\to U\oplus A,\qquad
 \begin{pmatrix}M(w)&\operatorname{ev}_c&0\\0&0&G(c)\end{pmatrix}.
$$
Here the middle slot evaluates the dual marker factor against $c$. The old labels are exactly those of rank at most $\dim U$, since for $c\ne0$ at least two large tag blocks are invertible. Their image span gives $U$, their joint kernel the extra input slots, and restricting the whole pencil to that kernel modulo $U$ distinguishes the evaluation slot. Hence ordinary transport reflects to $M$ and every old map extends by the identity on the marker labels and tag spaces and by its $U$-action on the evaluation slot.

To see absolute indecomposability, a centroid element preserves those intrinsic flags over the algebraic closure. Indeed $I+tC$ in one mode and its inverse in another give an actual tensor automorphism for a generic scalar $t$ whenever the separate actions of $C$ in those modes agree. The evaluation factor forces its diagonal action on $U$ and on the marker label quotient to be a common scalar, by the equality of their actions on a full tensor product, and then forces the same on the evaluation input slot. Conciseness gives that scalar on all the other blocks. After subtracting it, the label shear affects only the original $V\to U$ block while the output shear affects only the $B\to U$ block, so equality kills both. The remaining input shears are killed by the zero common kernels of the tag and evaluation maps. The centroid is scalar, as required. The tag lengths may grow arbitrarily, preserving polynomial size when chosen polynomially, and provide the ordered format tags used above.

On an input comparison of two ordered pairs, construct its unordered set $S$ of distinct raw tensors, with $|S|\le4$. For every nontrivial cut $C\mid S\setminus C$, use the assumed $E$-to-TI reduction on each pair $(u,v)$ crossing the cut. Pack the resulting ordinary instances by the fixed disjunction construction. Call the output comparison $(L_C,R_C)$. Its ordinary answer is whether any oriented equivalence edge crosses the cut. This computes two raw tensor outputs only, without asking any TI questions.

For each $u\in S$, define a list by picking $L_C$ when $u\in C$, and $R_C$ otherwise, in a fixed order of cuts. Two lists compare ordinarily in every slot exactly when every cut separating their two items has an oriented equivalence edge crossing it. This condition is exactly $E(u,v)$. An equivalent pair crosses every cut that separates it. An inequivalent pair is separated by the cut consisting of the entire $E$-class of its first item within $S$, which has no crossing edge. The construction uses this class only in the proof.

A tuple $(u_1,u_2)$ now gives an ordered concatenation of its two lists. Pack all slots by ordinary conjunction with independently sorted labels. Finally append an unused first-mode coordinate. This last step leaves the ordinary orbit comparison unchanged and allows any first determinant to be corrected on the complement. Thus one-sign comparison of the two encoded tuples tests the ordinary conjunction, and hence tests $E$ in both coordinates. Only the set $S$ determines the common collection of cut tests. If $S$ has one element, the comparisons are reflexive and a common fixed output suffices. This proves the converse.

## 4. Bounded-index version

Let $E_0$ be any input equivalence relation and $F_0$ a target equivalence relation refining $O_0$, with at most $k$ $F_0$-classes per $O_0$-class. Suppose an objectwise polynomial-time reduction takes the coordinatewise relation $E_0^{[r]}$ to $F_0$, and $2^r>k$. On input objects $x,y$, take $k+1$ distinct binary words of length $r$, expand their symbols as $x,y$, and apply the object map. If $x$ and $y$ are inequivalent, the outputs occupy $k+1$ different $F_0$-classes. If they are equivalent, the outputs lie together in a single $F_0$-class. Thus $k$ ordinary $O_0$-comparisons with one reference suffice. A polynomial compilation of that constant conjunction gives a direct many-one reduction from $E_0$ to $O_0$.

For determinant subgroups over a fixed finite field the number $k$ can be bounded by the index of the allowed determinant subgroup in the full determinant group. This version needs no assumption that isomorphisms act separately on the old modes or preserve any displayed determinant reading. It uses only the finite splitting bound and the correctness of the original tuple encoder.

## 5. An unconditional compiler for one ordinary and one oriented conjunct

There is a deterministic polynomial-time many-one reduction
$$
            O\ \wedge\ E\ \le_m^p\ E,
$$
where the two input comparisons are independent. It follows that two one-sign comparisons pack into a single one-sign query whenever one of them has a polynomial-time certificate of sign flexibility. This includes an odd first-mode dimension, an unused first-mode direction, or a supplied stabilizer element with negative first determinant. An ordinary transporter can change its first sign by composing with the certified stabilizer at that endpoint.

For the ordinary comparison, restrict both tensors to their intrinsic supports, which preserves ordinary isomorphism. Mismatched dimensions and zero supports can be handled as immediate answers. The resulting tensors are concise. To make the sum of their three side lengths odd, if needed append the same larger evaluation tensor of shape $(ab,a,b)$ with $a,b$ odd. It is concise and has scalar centroid, and its format distinguishes it from every original summand. The ordinary verdict stays the same. Now write this tensor as a bilinear map $m:U\times V\to W$ and form $B=F\,1\oplus U\oplus V\oplus W$, with $uv=m(u,v)$ the sole nonzero radical product. It is a local associative algebra with scalar residue. The ordinary tensor verdict equals the algebra isomorphism verdict, because $J^2=W$ and the two annihilators in $J/J^2$ recover $U,V$. Every original witness extends to an algebra isomorphism, and filtration shears have no effect on either verdict. The dimension $b=\dim B$ is even.

Take the tensor of the action of $B$ on its free left module $B\oplus B$. Ordinary equivalences of the action determine algebra isomorphisms up to left multiplication by a unit on the label. On the matrix modes the determinant is always one: a lifted algebra map appears twice, a $B$-linear module unit contributes the $b$-th power of the determinant on its top, and the left-unit adjustment likewise contributes an even power of its scalar residue. These are the fixed-label regular action computations in the preceding conjunction construction. Orient this block so that its algebra label is an untested axis.

For the one-sign comparison apply the exact regular action-algebra construction in the preceding collapse packet. It encodes the comparison as an absolutely indecomposable tensor whose untested determinants are always one, and whose possibly nontrivial sign on the label gives precisely the original one-sign answer. Place its label in the tested axis. The two new tensor formats can be chosen distinct by selecting oversized evaluation pads. Both tensors are absolutely indecomposable because their centroids are the centers of local algebras with scalar residue. Therefore every transporter of the direct sum respects the two blocks. For the tested determinant the ordinary block contributes one, and the exact oriented verdict comes entirely from the second block. Conversely every pair of local witnesses of the required kinds combines. Immediate true comparisons can be omitted, and immediate false comparisons can use a fixed negative one-sign instance.

The compiler covers arbitrary ordinary inputs and any certifiably flexible first orientation comparison. The finite-index theorem gives a sufficient route for treating both independently oriented conjuncts through one encoder.
