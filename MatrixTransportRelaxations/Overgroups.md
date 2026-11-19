# Exact classification of broader allowed groups inside the left-right action

The base construction chooses a fixed finitely presented group Q with no nontrivial finite quotients and a halting-complete word problem, a finite-rank free group F with epimorphism π onto Q, and R=ker π. Embed F faithfully in SL₂(ℤ). On V=M₂(ℤ), let L(u,v)(X)=uXv⁻¹ and write T_s(X,Y)=XsY. The original allowed subgroup is H={(u,v):π(u)=π(v)}. It contains the full diagonal subgroup ΔF. Transport by L(u,v) sends T_s to T_(vsu⁻¹). All conclusions below concern ordinary simultaneous integral basis changes of this fixed multiplication table, restricted to the indicated subgroup.

## Every broader subgroup has an exact quotient description

**Theorem.** For every subgroup K with H⊆K⊆F×F there is a unique normal subgroup N of F containing R such that

    K = {(u,v) : u⁻¹v belongs to N}.

Its orbit of T_I is precisely {T_s : s belongs to N}. Equivalently there is a unique normal subgroup M of Q with N=π⁻¹(M), and transport to a target T_s is possible precisely when the image of π(s) in Q/M is trivial. For parameter words s in F, the two decision questions reduce computably to one another.

**Proof.** Put N={v:(1,v)∈K}. Diagonal conjugation makes N normal in F. The inclusion H⊆K gives R⊆N. Multiplying (u,v) on the left by (u⁻¹,u⁻¹) shows that (u,v)∈K precisely when u⁻¹v∈N. Conversely any such N produces a subgroup containing H, proving uniqueness and the correspondence. Normality makes vu⁻¹∈N equivalent to u⁻¹v∈N, so the transport formula identifies the orbit. The coefficient T_s(I,I) is s itself and thus recovers the parameter. Given a word s, its integral matrix and table are computable. Given the parameter word, triviality in Q/M is exactly membership in N.

For a finite list of newly permitted pairs (u_j,v_j), the new N is the normal closure of R and the finitely many differences u_j⁻¹v_j. Thus the quotient is obtained from the presentation of Q by adding precisely those finitely many relators. This gives a sufficient theorem for preserving halting-completeness. If the resulting quotient has a halting-complete word problem, the enlarged tensor-transport problem is halting-complete as well. There is no requirement to keep the original list of moves or its original word metric.

## A finite-index ambient relaxation accepts every constructed target

**Theorem.** If K contains H and has finite index in F×F, then K=F×F.

Indeed the cosets of K are in bijection with those of N in F, using (u,v)↦u⁻¹v modulo N. Thus F/N is finite. It is a quotient of Q, so it is trivial. All targets T_s with s∈F become reachable.

The same conclusion holds if K is required to be normal in F×F. The quotient of F×F by the normal closure of ΔF is the abelianization of F, via (u,v)↦[v]−[u]. Imposing R in either factor then gives Q_ab. A finitely generated group with no finite quotients has trivial abelianization, since every nonzero finitely generated abelian group has a nontrivial finite quotient. Consequently the normal closure of H is all of F×F.

These are exact statements about enlargements of this particular construction. They do not rule out a different undecidability construction for a larger ambient action.

## Normalizers and commensurators

The normalizer of H inside F×F is

    {(u,v) : π(v)⁻¹π(u) belongs to the center of Q}.

This follows by passing to Q×Q. The image of H is ΔQ, and (a,b) normalizes ΔQ precisely when conjugation by a and by b agree on every element of Q, or b⁻¹a is central.

Its commensurator inside F×F is the same group. To see this, the common subgroup H∩gHg⁻¹ contains R×R. Its image in ΔQ consists of the elements whose corresponding coordinate centralizes b⁻¹a, where g has quotient coordinates (a,b). Its index in H is therefore the index of that centralizer in Q. If the index is finite, the centralizer equals Q, since a proper finite-index subgroup would yield a nontrivial finite permutation quotient. Thus commensuration forces normalization. Normalization plainly gives commensuration.

If desired the original source Q can be replaced by Q*Q. A free product of two nontrivial groups is centerless, remains finitely presented, has no nontrivial finite quotients, and retains the halting-hard word problem through either free factor. For this choice H is self-normalizing and equals its own commensurator.

## The free-group projections can already have finite index

The original embedding can be strengthened before the whole construction. The standard opposite elementary matrices with off-diagonal entries 2 generate a free rank-two subgroup F₂ of finite index in SL₂(ℤ). For each d≥1 the kernel of F₂→ℤ/d, sending the first free generator to 1 and the second to 0, is a finite-index free subgroup of rank d+1. A Schreier basis consists of the d conjugates a^j b a^(-j), for 0≤j<d, and a^d. Choose d large enough for a generating set of Q and map excess basis generators to the identity. This gives the needed epimorphism onto Q from a free subgroup F already of finite index in SL₂(ℤ). Thus both coordinate projections of the allowed H can have finite index in the full integral special-linear group on the two-dimensional factor. The coupling between the two projections still carries halting.

These are informal deductions from the base fiber-product construction. Quotient word problems and integral orbit undecidability have extensive prior literature. Publication priority for the tensor formulations is unverified. [Original tensor construction](https://github.com/Dugongue/MathProofs/blob/main/TensorTransportAndHalting/Profinite.md) · [Bridson's universal group](https://arxiv.org/abs/1907.08072) · [Bogopolski, Martino and Ventura on orbit decidability](https://arxiv.org/abs/0712.3104)