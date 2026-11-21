# Projective multiset transport with a pinned marked span

## GP-0348

Let two spanning multisets of points of $\operatorname{PG}(k-1,q)$ have some specified paired occurrences. Suppose the paired points pin their span pointwise projectively, in the sense that every linear automorphism of that span fixing all its indicated lines is scalar. Put $d$ equal to the codimension of the marked span. There is a deterministic algorithm in $q^{d^2}\operatorname{poly}(L)$ time, for input bit size $L$, testing and constructing an exact linear projective transporter. It is fixed-parameter tractable in $d$ over each fixed field. The span need not have a canonical complement. The pinning condition can be checked directly on the paired data and needs no projective frame among the marked points.

### Fixing the marked coordinates

Choose a basis from the source marked lines and check that the corresponding target lines give a basis of the target marked span. Reject if this fails. Every linear map respecting these basis lines is diagonal in those bases. Each additional paired point must have the same coordinate support and imposes fixed ratios between its diagonal coordinates. These ratios can be propagated and checked on a graph whose vertices are the basis indices, with an edge linking each pair that occurs in one support. The equations are consistent precisely when the circuit products are consistent. For a nonzero marked span, the scalar condition holds exactly when the support graph is connected or the field has two elements. Indeed every connected component permits an independent nonzero scalar and the multiplicative group of the two-element field is trivial. Under the scalar condition, find one valid diagonal tuple and change the target coordinates by its inverse, so that all candidate projective maps have a representative restricting to the identity on the marked span. Both the consistency test and the change of coordinates are polynomial. If the span is zero, the same construction below omits that restriction.

Choose any complements to the two spans and identify coordinates so that the candidate maps are
$$
(u,v)\longmapsto (u+S v,Qv),\qquad Q\in \mathrm{GL}_d(k_q),
$$
where $u$ is in the marked span, $v\in k_q^d$ and $k_q=\mathbb F_q$. Compare the multiset on the marked span using identity and enumerate $Q$ by enumerating all $d$ by $d$ arrays and rejecting singular ones.

### The shear is a coupled translation problem

For each nonzero quotient line $\ell$, select a representative $v_\ell$ and uniquely normalize every point above $\ell$ as $(u,v_\ell)$. Let $U_\ell$ be its multiset of first coordinates. If $Qv_\ell=\kappa_\ell v'_{Q\ell}$ in the chosen target coordinates, the required target multiset, after multiplying its first coordinates by $\kappa_\ell$, is exactly a translate of $U_\ell$ by $Sv_\ell$. Check the corresponding observed quotient-line supports. Empty pairs of fibres impose no constraint.

For a nonempty pair of fibres, fix one source entry and try its translations to all target entries, testing multiset equality. The collection of successful offsets is either empty or one coset of the additive stabilizer of $U_\ell$. This follows because the difference of any two successful offsets fixes the multiset, and adding any stabilizing offset preserves success. It is therefore an affine subspace over the prime field. From the enumerated list obtain one representative and a linear basis for its direction space. Require $Sv_\ell$ to belong to this affine subspace for every nonempty fibre. These conditions are one linear system over the prime field in the matrix entries of $S$, since multiplication by each known element of $k_q$ is prime-field linear. A solution gives the desired transporter. Matching repeated occurrences within an identical normalized point then supplies an explicit correspondence. All work per $Q$ is polynomial in the encoded input, including the field encoding. The argument checks each potential transporter and constructs one whenever a compatible $Q,S$ exist. [Projective code and matroid equivalence context](https://arxiv.org/abs/2202.02086)
