# Solvability of finitary-row orbit-finite linear systems

The decision argument concerns unrestricted solutions with the effective orbit data stated below.

## Setting
- Atoms: equality atoms 𝔸.
- C (unknowns) and R (equations) are orbit-finite sets.
- A ∈ K^{R×C} is finitely supported. **Finitary rows**: each row A(r,_) has finitely many non-zero entries.
- t ∈ K^R is finitely supported.
- An unrestricted solution is any function x : C → K with Σ_c A(r,c)x(c) = t(r) for all r. The sums are finite because the rows are finitary.

## Theorem Z4-D (proved, confidence 85%)
Let K be an effective field. Unrestricted solvability of orbit-finite systems with finitary rows over K is decidable. More precisely:

  A x = t has an unrestricted solution ⟺ there is NO finitary y ∈ K^{(R)} with Aᵀy = 0 and t·y = 1.

The right-hand side is a finitary-solvability instance FS(K) of the orbit-finite system B y = e. Here B = [Aᵀ ; tᵀ], with rows indexed by C ⊔ {∗} and columns by R, and e = (0,…,0,1). This instance is decidable by GHL Thm 6.1 (Ghosh thesis, finitary solvability). So the original problem is decidable.

*Proof.*
1. **Linear compactness.** K^C with the product of discrete topologies is linearly compact, being the algebraic dual of K^{(C)} (Lefschetz; Köthe, Topological vector spaces I §10.9). Each equation's solution set is empty or a closed affine subspace, closed because a finitary row depends on finitely many coordinates. A family of closed affine subspaces with the finite intersection property has non-empty intersection. So the system is solvable iff every finite subsystem is.
2. **Finite duality.** A finite subsystem A_0 x = t_0 over a field is unsolvable iff some finite combination of its rows gives 0 = 1 (Fredholm alternative, after rescaling). So every finite subsystem is solvable iff there is no finitary y with Aᵀy = 0 and t·y = 1.
   - Aᵀy is well defined for finitary y even when columns of A have infinite support.
   - Aᵀy = 0 is the system of equations indexed by c ∈ C.
3. **Orbit-finiteness.** B has orbit-finite row index set C ⊔ {∗} and orbit-finite column index set R, and finitely supported entries. GHL's FS(K) admits arbitrary finitely supported matrices; they reduce to finitary vectors by an orbit-finite basis change (GHL §6, "Simplifying assumptions"). Finitary solutions are automatically finitely supported. ∎

## Corollary Z4-E (proved, 80%)
The same holds over ℤ/n.
- Compactness is Tychonoff on (ℤ/n)^C.
- Duality: a finite system over ℤ/n is solvable iff t ⊥ ker Aᵀ under the perfect pairing (ℤ/n)^r × (ℤ/n)^r → ℤ/n. This is Pontryagin duality, since ℤ/n is self-injective.
- Decide the complement as n−1 FS(ℤ/n) instances: ∃ finitary y with Aᵀy = 0 and t·y = c, for c ≠ 0.
- The same works over any finite Frobenius (quasi-Frobenius) commutative ring. It is not claimed for general finite rings.
