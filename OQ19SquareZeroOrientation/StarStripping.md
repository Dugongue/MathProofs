# Orientation by stripping full exterior stars and unused support

Let $F=\mathbb F_3$. The data are a based space $V$ and a based subspace $J\subseteq\bigwedge^2 V$. A transporter to $(V',J')$ is an invertible linear map $g:V\to V'$ with $\bigwedge^2 g(J)=J'$. Write $f$ for its induced map on $J$. The test is
$$
(\det g)^a(\det f)^b=s,\qquad a,b\in\{0,1\},\quad s\in\{1,-1\}.
\tag{1}
$$
The anchored square-zero problem takes $V=U^*$, $a=0$ and $b=1$. Here $U$ is the quotient of the pencil's ambient space by the common radical of its singular hyperplane. The symplectic lift extends every descended transporter on $U$. In the original odd-dimensional square-zero normalization the raw product sign is the same as $s$ after the known frame and Pfaffian calibration. The present procedure uses the descended space $J$ as its input. [Square-zero normal form and the published question](https://arxiv.org/html/2306.03135v2#S1.SS5)

**Theorem.** Compute the following two canonical subspaces using linear equations:
$$
S(J)=\operatorname{span}\{\iota_\lambda\omega:\omega\in J,\ \lambda\in V^*\},
\qquad
K(J)=\{x\in V:x\wedge V\subseteq J\}.
\tag{2}
$$
While $S(J)\ne V$, restrict the ambient space to $S(J)$. Otherwise, if $K(J)\ne0$, quotient the ambient space by $K(J)$ and replace $J$ by its image. In the first case record the free exponent $a$ on the removed space and keep $(a,b)$. In the second case, for $n=\dim V$ and $k=\dim K(J)$, record the free exponent $a+b(n-1)$ and use $(a+bk,b)$ on the quotient. Exponents are in $\mathbb F_2$.

If any recorded free exponent is odd, there is a deterministic polynomial-time reduction to one ordinary three-tensor isomorphism instance over $F$, with no bound on the final core. If every free exponent is even, the attainable signs on the original pair equal those of its terminal pairs and terminal character, multiplied by one computable frame factor. In particular, there is a single polynomial-size ordinary comparison when, in the terminal pair or its annihilator dual, all spaces of nonzero tested exponent have dimension $O(\log B)$, where $B$ is the dense input bit length. Earlier specialized determinant tests can also be applied directly to the terminal character when their hypotheses hold.

The stripping is intrinsic, can be repeated through arbitrarily many large layers, and can be used on inputs with scalar pair adjoints. Its acceptance test and construction do not search for an ordinary transporter.

## 1. Canonical support strip

For $\lambda\in V^*$ use $\iota_\lambda(x\wedge y)=\lambda(x)y-\lambda(y)x$. The space $S=S(J)$ is the smallest space with $J\subseteq\bigwedge^2 S$. To prove this, choose a basis beginning with a basis of $S$. Any wedge coefficient with an index outside $S$ would give, by contraction in its other index, a vector with a nonzero coordinate outside $S$. Conversely the contraction of any element of $\bigwedge^2S$ has image in $S$. It follows that every transporter identifies the two supported cores.

For two inputs with equal support and quotient dimensions, every isomorphism on the supported core extends. Choose complements to $S$ on both sides and an arbitrary isomorphism between them. This does not affect the map on $J$. Every possible determinant of the removed quotient occurs independently for each core transporter as long as its dimension is positive. In adapted ambient bases the original determinant is that of the map on $S$ times that of the removed quotient. Thus the exponent on this free determinant in (1) is $a$. If the quotient has positive dimension and the exponent is odd, either sign occurs above any supported-core transporter. Otherwise the original sign is the supported-core sign up to the known frame factor.

## 2. Full-star strip

The condition defining $K=K(J)$ is a linear kernel. It gives the containment $K\wedge V\subseteq J$. Set $Q=V/K$, and use a bar for the image of $J$ in $\bigwedge^2 Q$. The map $\bigwedge^2 V\to\bigwedge^2Q$ is surjective with kernel $K\wedge V$. Therefore $J$ is exactly the inverse image of $\bar J$. Every transporter preserves $K$ and induces a transporter of $(Q,\bar J)$. Conversely every transporter $g_Q$ of the latter pair lifts to a transporter of the original pair with any specified isomorphism $g_K:K\to K'$. Choose vector-space splittings and take the block diagonal map. All shears preserving the quotients preserve the full inverse image, although they are unnecessary for the lift.

The subspace $K\wedge V$ has the natural filtration with successive pieces $\bigwedge^2K$ and $K\otimes Q$. Its determinant multiplier in the corresponding frames is
$$
(\det g_K)^{k-1}\,(\det g_K)^{n-k}\,(\det g_Q)^k
  =(\det g_K)^{n-1}(\det g_Q)^k .
\tag{3}
$$
The exterior-square factor follows directly by extending scalars and triangularizing, or by the determinant character on elementary matrices. The tensor-product factor follows by the same computation on the two factors. For $k=1$ the exterior-square factor is one, as is the case when $Q=0$ for the tensor-product factor. Use exact sequences to multiply (3) by the determinant on $\bar J$. The original character in adapted coordinates is then
$$
(\det g_K)^{a+b(n-1)}
  (\det g_Q)^{a+bk}
  \bigl(\det(\bigwedge^2g_Q|_{\bar J})\bigr)^b.
\tag{4}
$$
This proves both the reduction rule and the free correction claim.

At either type of strip, each frame factor is computed by concatenating bases of the subspace and lifts of the quotient, and taking determinants of the resulting change-of-basis matrices on each input. More explicitly, a map of an original role has raw determinant equal to its adapted determinant times $\det B'/\det B$ for source and target frame matrices $B,B'$. Use the applicable exponent on each role when multiplying these factors. In the full-star label frame, first concatenate the wedge basis of $\bigwedge^2K$, the wedge lifts of the basis of $K\otimes Q$, and lifts of the chosen basis of $\bar J$. The known factor from this frame accounts for all choices of orientation of the based subspaces. An odd-exponent free determinant can select either sign regardless of these known factors.

## 3. One exact comparison

The flags in (2) are transported by every original transporter. A mismatch in kind or dimensions at any stage therefore gives a fixed negative pair. Otherwise stripping terminates after at most $\dim V$ steps. The whole sequence is computed by linear algebra on spaces of dimension at most $\binom{\dim V}{2}$. The lifting statements show that every terminal transporter extends across all earlier strips. Moreover the indicated free determinants at distinct steps are independent. Lift in reverse order and choose the indicated map on the deleted subspace or quotient at each step.

If any free exponent was odd, the terminal ordinary isomorphism verdict is the answer, even if the tracked terminal exponents are still nonzero. If no exponent was odd, multiply the computed frame factors and impose the remaining character on the same terminal transporter. A zero-dimensional role has determinant one. If both exponents vanish, compare the known factor with $s$ and, in an affirmative case, ask only about the ordinary core.

The optional terminal annihilator transform uses $C=J^\perp\subseteq\bigwedge^2 V^*$ and $g^{-{\mathsf T}}$ on $V^*$. In the exact sequence
$$
0\longrightarrow C\longrightarrow\bigwedge^2V^*
  \longrightarrow J^*\longrightarrow0
$$
the last map is the dual inverse of $f$. The determinant on the middle space is $(\det g)^{-(n-1)}$. Thus the new exponents in characteristic three with $q=3$ are $(a+b(n-1),b)$, and a basis of $C$ followed by quotient lifts computes the frame factor. This is an exact duality on the transporter set. The algorithm can test both final dimension profiles and use the first passing profile in a fixed order. Its use here is compatible with even and odd final ambient dimension.

To encode the ordinary core, keep roles $V,J,\bigwedge^2V$, the alternating surjection $V\times V\to\bigwedge^2V$, and the inclusion $J\hookrightarrow\bigwedge^2V$. These maps force the genuine induced actions, and every core transporter extends. To enforce a terminal character attach the exterior algebra only to each role whose determinant is actually needed. A rank-$r$ exterior algebra has dimension $2^r$ and its multiplication and degree-one inclusion force the induced map on the top line. Use scalar multiplication maps on the resulting lines and a marked vector on their product to impose (1) with the calibrated value. There are only a fixed number of exterior roles. One may keep just the top line as a named inclusion into the exterior algebra. All maps are linear or bilinear, hence they are records of order at most three using dual slots for inputs.

The number of records in this final compilation is bounded independently of the stripping depth, since earlier flags are used only for the frame arithmetic and the exact witness lift. The mixed tensor-system compiler therefore produces one ordinary three-tensor instance in polynomial time and over the same field. A fixed no-instance uses unequal tensors of the same shape, one zero and one nonzero. A fixed yes-instance compares a tensor with itself. The procedure works without enumerating choices of deleted bases or looking for a transporter. [Chen–Grochow–Qiao–Tang–Zhang, Theorem 4.1](https://arxiv.org/html/2306.03135v2#S4)

## 4. Scalar adjoints, quadratic labels and genuine orientation

Here is a family where the procedure needs arbitrarily many steps and where one cannot simply apply the small-label or small-complement tests to the original space or to the supported first dual. Begin with the two-dimensional alternating form space given by the four diagonal blocks
$$
a\Omega_2,\quad b\Omega_4,\quad (a+b)\Omega_6,\quad(a-b)\Omega_8
$$
on a 20-dimensional ambient space, with each $\Omega_j$ nonsingular alternating. On the four projective label lines their ranks are $18,16,14,12$ in some order. The lines are therefore fixed individually by every automorphism of that form space. Any map on its two-dimensional label space fixing each line is scalar, so its determinant is one over $\mathbb F_3$. Write $J_0$ for the corresponding subspace of the exterior square of its dual. It has full support in dimension 20. Adjoin one unused ambient dimension so it initially sits in an odd-dimensional ambient space. This unused direction does not alter label orientation.

For a chosen depth $h\ge2$, use nested spaces
$$
V_i=K_i\oplus B_i\oplus V_{i+1},\qquad
J_i=K_i\wedge V_i+J_{i+1}\quad(1\le i\le h),
$$
with $(V_{h+1},J_{h+1})$ the terminal augmented pair above. Take $\dim K_i=\dim B_i=2^{h-i+1}$. In every outer layer the star subspace is exactly $K_i$. In fact, after quotienting by $K_i$, the subspace $J_{i+1}$ is supported in a proper subspace because of $B_i$. A subspace of $\bigwedge^2 S$ with $S$ proper admits no nonzero full star in an ambient space of dimension at least two. To see this, for $x\ne0$ in $S$ wedge with a vector outside $S$, and for $x$ outside $S$ wedge with any independent vector in $S$ when $S\ne0$. For $S=0$, wedge with any independent vector. In each case the wedge is outside $\bigwedge^2 S$. On the other hand, each $J_i$ has full support in $V_i$ because it contains $K_i\wedge V_i$. Thus the actual procedure removes $K_i$ by a full-star strip, then removes the unused $B_i$ by support stripping, and proceeds inward. The last support strip also removes the extra terminal unused direction.

Every $V_i$ has odd dimension. For the label sign $(a,b)=(0,1)$, every star and every unused-support strip is neutral, since $n-1$ and $\dim K_i$ are even. The terminal two-dimensional determinant suffices. It follows that all automorphisms of $J_1$ have label determinant one. Changing just one basis vector of $J_1$ by a sign on the target produces an ordinarily isomorphic pair whose attainable label sign is $-1$ in the supplied bases. In particular this is a genuine oriented test. Hyperbolic addition of the nonsingular anchor puts it in the square-zero pencil locus.

The pair adjoint on the original ambient form space is scalar. In general, when $J$ contains $K\wedge V$ with $\dim K\ge2$ and $\dim V\ge3$, let $(P,Q)$ be adjoints on the form inputs $V^*$. For each independent $u\in K$, $v\in V$, the equation on $u\wedge v$ gives
$$
P^*u\otimes v-P^*v\otimes u=u\otimes Q^*v-v\otimes Q^*u.
$$
Quotienting either tensor factor by $\operatorname{span}(u,v)$ shows that $P^*$ and $Q^*$ preserve this plane. Intersect the planes containing a fixed nonzero $u\in K$ to get its line. For $v\notin K$, intersect the two planes spanned by $v$ and two independent vectors in $K$ to get $Fv$. Thus the two maps preserve every line and are scalar. A nonzero alternating form forces the two scalars to agree.

The first annihilator $J_1^\perp$ has support on $B_1^*\oplus V_2^*$, and on that support it contains the full star through $B_1^*$. Indeed annihilating $K_1\wedge V_1$ imposes precisely that the forms lie on this quotient, and $J_2$ has zero wedge coordinates involving $B_1$. The same scalar-adjoint proof applies there. Both the original label dimension and codimension are quadratic in $\dim V_1$. The label dimension is at least $\dim K_1(\dim V_1-\dim K_1)$ and the codimension is at least $\binom{\dim B_1}{2}$. On the supported first dual, the codimension is $\dim J_2$, also quadratic since $\dim K_2$ and $\dim V_2$ are each a constant fraction of $\dim V_1$ as $h$ grows. Its label dimension is at least $\binom{\dim B_1}{2}$. Thus the earlier one-grade adjoint test cannot read either of these two pairs in logarithmic width. The recursive strips reduce both to the small terminal label.

There is also a family with no bound on the terminal label in the case of a free sign. Take $V=K\oplus B\oplus Y$ with $n$ odd, $\dim K$ odd and at least three, and $B\ne0$. Put $J=K\wedge V+D$ for any $D\subseteq\bigwedge^2Y$. Stripping the star transfers exponent one onto the quotient ambient space. The next support strip deletes at least $B$, so a reflection there flips the original label sign. Underlying ordinary equivalence and oriented equivalence consequently agree on matching instances of this class, even when the remaining core $D$ is arbitrary.

## Scope

The proof strengthens the earlier square-zero adjoint-grade criterion by giving an exact reduction through canonical exterior layers before using any adjoint grades. A single annihilator step is a special case of the same determinant bookkeeping, while the repeated procedure also handles even-dimensional intermediate spaces and free determinant corrections. Every conclusion concerns the represented alternating form space and has the explicit lifts in Sections 1 and 2. An arbitrary terminal pair may have full support, no full star, and large label and annihilator spaces. Such a pair is outside the proved orientation criteria unless another terminal theorem applies. Accordingly this is a sufficient same-field single-instance reduction, with new scalar-adjoint families, and the unrestricted question remains open. The theorem is a written proof.
