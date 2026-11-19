# How far may the allowed matrix basis changes be enlarged?

All conclusions are unconditional informal deductions about integral basis changes acting simultaneously on both inputs and the output of the 4 by 4 by 4 matrix multiplication tensor. Let F be a fixed finite-index free subgroup of SL₂(ℤ), let Q=F/R be a fixed finitely presented group with halting-complete word problem and no nontrivial finite quotients, and set H={(u,v):u and v agree in Q}. A pair acts on M₂(ℤ) by X↦uXv⁻¹. For T_s(X,Y)=XsY, the orbit of T_I under H is exactly the tensors with s∈R. The underlying four-dimensional module is fixed throughout.

| Relaxation | Exact conclusion |
|---|---|
| Add any fixed finite collection of new paired moves | Their discrepancies add relators to Q. The enlarged orbit is exactly the word problem in that quotient. [Overgroups](Overgroups.md) |
| Add whole infinite families, repeatedly | For any prescribed finite length there is a strictly increasing chain of finitely generated allowed groups, every one with halting-complete orbit. All have full projection to each F factor. [Positive chain theorem](Chains.md) |
| Permit the same changes as H modulo every integer | Every original target T_s becomes reachable. H already has every finite quotient image of the paired arithmetic ambient. [Arithmetic and closures](Arithmetic.md) |
| Require an overgroup to have finite index in F×F | The overgroup equals F×F. Every original target becomes reachable. This refers to index in the ambient group. [Overgroups](Overgroups.md) |
| Require an overgroup to be normal in F×F | Its minimum possible value is F×F. [Overgroups](Overgroups.md) |
| Permit every integral basis change preserving the determinant quadratic form det(X) | Every original target becomes reachable by its explicit L₁s. General orbit testing under an effectively described arithmetic group is decidable by classical algorithms. [Arithmetic](Arithmetic.md) |
| Stop at a maximal proper computably enumerable overgroup within F×F | The promised orbit problem is decidable by two parallel proof enumerations in the resulting simple quotient. Existence and construction of such an overgroup are not asserted. [Maximal endpoint](Maximal.md) |
| Close under normalizing or commensurating changes | If Q is chosen centerless, neither operation enlarges H. [Overgroups](Overgroups.md) |

For a single enlarged subgroup K in the paired ambient, the precise answer is its quotient. Put N={u:(u,1)∈K}. Then K={(u,v):uv⁻¹∈N}, and its reachable parameters are exactly N. If K is computably enumerable, orbit membership is computably enumerable. Halting-completeness survives exactly when the word problem of F/N is computably enumerable complete. Mere undecidability would be a weaker property.

The positive chain theorem provides sufficient constructions retaining halting after arbitrarily many strict enlargements. The arithmetic and maximal endpoints give terminating decision procedures or explicit transporters at the specified scope. These statements together locate several substantial changes in behavior. They do not classify subgroups of SL₄(ℤ) lying outside the paired ambient, nor assert a largest hard subgroup.

**Sources and status.** The source inputs are the earlier matrix multiplication transport construction, classical fiber products, Bridson's universal group, and Grunewald–Segal arithmetic orbit algorithms. All proofs here are informal and publication priority for the specific tensor formulations is unverified. There is no assumption that the integers are Diophantine over the rationals. [Earlier construction](https://github.com/Dugongue/MathProofs/blob/main/TensorTransportAndHalting/Profinite.md) · [Bridson](https://arxiv.org/abs/1907.08072) · [Grunewald and Segal](https://annals.math.princeton.edu/1980/112-3/p04)
