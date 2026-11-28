# An arity bound for equivariant tensor reductions

The lower bound has the equivariance, degree, and representation hypotheses given below.

## Theorem A (arity barrier for Grochow–Qiao Open Question 7.8). Complete

Let F be a field and n ≥ 2. Let R : (F^n)^{⊗d} → F^{N₁} ⊗ F^{N₂} ⊗ F^{N₃} be a **nonconstant** polynomial map of degree < n that is equivariant through a homomorphism ρ = (ρ₁, ρ₂, ρ₃) : GL_n^d → GL_{N₁} × GL_{N₂} × GL_{N₃}.
- ρ is algebraic, or arbitrary when F is finite.
- It is enough that ρ be defined on SL_n^d.

Then **max_a N_a ≥ n^⌈d/3⌉**. More generally, for k-tensor targets max_a N_a ≥ n^⌈d/k⌉. For source dimensions n_i, max_a N_a ≥ min over partitions [d] = S₁ ⊔ S₂ ⊔ S₃ of max_a ∏_{i∈S_a} n_i.

Every kernel reduction is nonconstant, so this applies to every equivariant d-TI → 3-TI reduction of degree < n. The same bound holds for targets of actions (ii)–(v), where one ρ acts on several modes: apply the argument to the constituents of that one representation.

**Proof.**
1. **Pick a degree.** Write R = Σ_k R_k by degree. Some R_k with 1 ≤ k < n is nonzero. Each R_k is equivariant, so it factors through a nonzero equivariant linear map Sym^k((F^n)^{⊗d}) → W₁ ⊗ W₂ ⊗ W₃, where W_a = F^{N_a} via ρ_a.
2. **Find a matching irreducible.** Some composition factor E of Sym^k(⊗_i V_i) is a composition factor of W₁ ⊗ W₂ ⊗ W₃. Tensor products are exact over a field, so E is a composition factor of U₁ ⊗ U₂ ⊗ U₃ for some irreducible composition factors U_a of W_a. Over F̄, write U_a = ⊠_i U_{a,i} and E = ⊠_i E_i.
3. **E is nontrivial on every factor.** Each E_i is an irreducible polynomial representation of GL_n of degree k, since Sym^k(⊗V_i) has degree k in every factor. It is SL_n-trivial only if its highest weight is a rectangle with n rows, which has size ≥ n > k. So every E_i is SL_n-nontrivial.
4. **Some U_{a,i} is nontrivial.** Restricting to factor i, E_i is a composition factor of U_{1,i} ⊗ U_{2,i} ⊗ U_{3,i}. So not all U_{a,i} are SL_n-trivial. Let S_a = {i : U_{a,i} is SL_n-nontrivial}. Then S₁ ∪ S₂ ∪ S₃ = [d].
5. **Count dimensions.** A nontrivial irreducible representation of SL_n has dimension ≥ n in every characteristic (the natural module is minimal; over a finite field use Steinberg's theorem). So N_a ≥ dim U_a ≥ n^{|S_a|}, and max_a N_a ≥ n^⌈d/3⌉. ∎

**Tightness.** Our Lean theorem `BalancedOrdinaryReduction` gives a linear reduction with output dimension O(n^⌈d/3⌉), by grouping modes into three balanced parts plus gadget partition removal. Both steps are equivariant constructions, so

> **Among equivariant reductions of degree < n, the optimal side length for d-TI → 3-TI is Θ(n^⌈d/3⌉), over every field.**

**Consequence for Open Question 7.8.** The question asks for side length poly(d)·n^{(d/3)(1+o(1))}. For 3 | d this is achieved (Lean). For d ≡ 1, 2 (mod 3) it is **impossible for every equivariant reduction of degree < n**. Any positive answer must be non-equivariant (no transporter homomorphism) or of degree ≥ n.

The counting bound n^{d/3} is the only lower bound for continuous reductions, and the dimension/exchange-rate argument gives nothing more. So the remaining gap between n^{d/3} and n^⌈d/3⌉ is exactly the gap between continuous and equivariant reductions.
