import Mathlib.Computability.Reduce
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Quotient.Bilinear
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.RingTheory.Noetherian.Orzech
import Mathlib.RingTheory.Int.Basic
import Mathlib.Computability.RE
import Mathlib.Computability.Primrec.List
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Basis.Bilinear
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.Algebra.Module.Torsion.Pi
import Mathlib.Data.List.OfFn
import Mathlib.Computability.Partrec
import Mathlib.Data.List.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.PFun
import Mathlib.Data.Nat.Pairing
import Mathlib.Tactic.Ring
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Computability.PartrecCode
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.NumberTheory.Dioph
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Data.List.GetD
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Ring.Basic
import Mathlib.Computability.Primrec.Basic
import Mathlib.Tactic.Push
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.NumberTheory.SumFourSquares
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.Tactic.NormNum
import Mathlib.RingTheory.Trace.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Manin's Conjecture 7.2, provisional single-file formalization

This file uses Lean 4.33.0 and Mathlib revision
db584cd6d46c92f209a44c0f1c829460d327499d.

The conditional root is `ManinBilinear.manin_bilinear_of_numberRings`.
The provisional root is
`ManinBilinear.Provisional.manin_bilinear_pending_number_ring_proof`.
Its only placeholder is number-ring undecidability in the gate syntax.
The conditional reduction includes the prime-quotient, order, gate-compiler,
and bilinear steps. The alternate arithmetic route includes the integer DPRM
endpoint and the descent from totally real and quadratic relative definitions.

See Manin, Conjecture 7.2: https://arxiv.org/html/2007.10632#S7
See Koymans–Pagano: https://arxiv.org/html/2412.01768v3
See Poonen's exposition: https://math.mit.edu/~poonen/papers/h10_over_OK.pdf
See the Teamwork-LEAP announcement:
https://github.com/google-deepmind/superhuman/blob/848e793b950c8f1a12f84d070915b54594c71604/leap/README.md#latest-results

The adapted Ripple and Hilbert10 portions retain their original attribution
and are covered by Apache-2.0. Their license notices are included below.
-/

section BilinearReduction

namespace ManinBilinear

abbrev RawTerm := ℤ × ℕ × ℕ
abbrev RawEquation := List RawTerm × List ℤ
abbrev RawSystem := List RawEquation

def rhsVector {p : ℕ} (c : List ℤ) : Fin p → ℤ :=
  fun i => c[i.val]?.getD 0

def evalTerms {U V : Type*} [AddCommGroup U] [AddCommGroup V]
    [Module ℤ U] [Module ℤ V] {p : ℕ}
    (B : U →ₗ[ℤ] V →ₗ[ℤ] (Fin p → ℤ)) (u : ℕ → U) (v : ℕ → V)
    (ts : List RawTerm) : Fin p → ℤ :=
  (ts.map fun t => t.1 • B (u t.2.1) (v t.2.2)).sum

def rawSat {U V : Type*} [AddCommGroup U] [AddCommGroup V]
    [Module ℤ U] [Module ℤ V] {p : ℕ}
    (B : U →ₗ[ℤ] V →ₗ[ℤ] (Fin p → ℤ)) (S : RawSystem) : Prop :=
  ∃ (u : ℕ → U) (v : ℕ → V),
    ∀ e ∈ S, evalTerms B u v e.1 = rhsVector e.2

section Transport

variable {U V U' V' : Type*}
  [AddCommGroup U] [AddCommGroup V] [AddCommGroup U'] [AddCommGroup V']
  [Module ℤ U] [Module ℤ V] [Module ℤ U'] [Module ℤ V'] {p : ℕ}

theorem rawSat_iff_of_surjective
    (B : U →ₗ[ℤ] V →ₗ[ℤ] (Fin p → ℤ))
    (B' : U' →ₗ[ℤ] V' →ₗ[ℤ] (Fin p → ℤ))
    (f : U → U') (g : V → V') (hf : Function.Surjective f) (hg : Function.Surjective g)
    (h : ∀ x y, B' (f x) (g y) = B x y) (S : RawSystem) :
    rawSat B S ↔ rawSat B' S := by
  have evalEq (u : ℕ → U) (v : ℕ → V) (ts : List RawTerm) :
      evalTerms B' (f ∘ u) (g ∘ v) ts = evalTerms B u v ts := by
    simp [evalTerms, h]
  constructor
  · rintro ⟨u,v,huv⟩
    exact ⟨f ∘ u, g ∘ v, fun e he => (evalEq u v e.1).trans (huv e he)⟩
  · rintro ⟨u,v,huv⟩
    obtain ⟨f',hf'⟩ := hf.hasRightInverse
    obtain ⟨g',hg'⟩ := hg.hasRightInverse
    refine ⟨f' ∘ u, g' ∘ v, fun e he => ?_⟩
    rw [← evalEq]
    have hu : f ∘ (f' ∘ u) = u := funext fun i => hf' (u i)
    have hv : g ∘ (g' ∘ v) = v := funext fun i => hg' (v i)
    rw [hu, hv]
    exact huv e he

variable (B : U →ₗ[ℤ] V →ₗ[ℤ] (Fin p → ℤ))

abbrev LeftReduced := U ⧸ B.ker
abbrev RightReduced := V ⧸ B.flip.ker

def reduced : LeftReduced B →ₗ[ℤ] RightReduced B →ₗ[ℤ] (Fin p → ℤ) :=
  let L := B.liftQ₂ B.ker B.flip.ker le_rfl le_rfl
  AddMonoidHom.toIntLinearMap
    { toFun := fun x => (L x).toAddMonoidHom.toIntLinearMap
      map_zero' := by
        ext y : 1
        change L 0 y = 0
        exact congrArg (fun g => g.toFun y) L.toAddMonoidHom.map_zero
      map_add' := by
        intro x x'
        ext y : 1
        change L (x + x') y = L x y + L x' y
        exact congrArg (fun g => g.toFun y) (L.toAddMonoidHom.map_add x x') }

@[simp] theorem reduced_mk (u : U) (v : V) :
    reduced B (Submodule.Quotient.mk u) (Submodule.Quotient.mk v) = B u v :=
  rfl

theorem reduced_left_injective : Function.Injective (reduced B) := by
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.eq_bot_iff]
  intro x hx
  obtain ⟨u, rfl⟩ := (Submodule.Quotient.mk_surjective B.ker) x
  rw [Submodule.Quotient.mk_eq_zero]
  apply LinearMap.mem_ker.mpr
  ext v : 1
  have he := LinearMap.congr_fun (LinearMap.mem_ker.mp hx)
    (Submodule.Quotient.mk v : RightReduced B)
  simpa using he

theorem reduced_right_injective : Function.Injective (reduced B).flip := by
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.eq_bot_iff]
  intro y hy
  obtain ⟨v, rfl⟩ := (Submodule.Quotient.mk_surjective B.flip.ker) y
  rw [Submodule.Quotient.mk_eq_zero]
  apply LinearMap.mem_ker.mpr
  ext u : 1
  have he := LinearMap.congr_fun (LinearMap.mem_ker.mp hy)
    (Submodule.Quotient.mk u : LeftReduced B)
  simpa using he

theorem reduced_ne_zero (h : B ≠ 0) : reduced B ≠ 0 := by
  intro he
  apply h
  ext u v : 2
  have hz := LinearMap.congr_fun
    (LinearMap.congr_fun he (Submodule.Quotient.mk u : LeftReduced B))
    (Submodule.Quotient.mk v : RightReduced B)
  simpa using hz

theorem rawSat_reduced (S : RawSystem) : rawSat B S ↔ rawSat (reduced B) S :=
  rawSat_iff_of_surjective B (reduced B) Submodule.Quotient.mk Submodule.Quotient.mk
    (Submodule.Quotient.mk_surjective _) (Submodule.Quotient.mk_surjective _)
    (reduced_mk B) S

theorem rawSat_reduced_undecidable
    (h : ¬ ComputablePred (rawSat (reduced B))) : ¬ ComputablePred (rawSat B) := by
  intro hd
  exact h (hd.of_eq fun S => rawSat_reduced B S)

end Transport

section FiniteVariables

variable {U V : Type*} [AddCommGroup U] [AddCommGroup V]
  [Module ℤ U] [Module ℤ V] {p : ℕ}

def usedVariables (S : RawSystem) : List ℕ :=
  S.flatMap fun e => e.1.flatMap fun t => [t.2.1, t.2.2]

def variableBound (S : RawSystem) : ℕ :=
  (usedVariables S).foldr max 0 + 1

private theorem le_foldr_max_of_mem (x : ℕ) {xs : List ℕ} (h : x ∈ xs) :
    x ≤ xs.foldr max 0 := by
  induction xs with
  | nil => simp at h
  | cons a xs ih =>
    rw [List.mem_cons] at h
    change x ≤ max a (xs.foldr max 0)
    rcases h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem term_lt_variableBound {S : RawSystem} {e : RawEquation} {t : RawTerm}
    (he : e ∈ S) (ht : t ∈ e.1) :
    t.2.1 < variableBound S ∧ t.2.2 < variableBound S := by
  unfold variableBound
  constructor <;> apply Nat.lt_succ_of_le <;> apply le_foldr_max_of_mem
  · exact List.mem_flatMap.mpr ⟨e, he, List.mem_flatMap.mpr ⟨t, ht, by simp⟩⟩
  · exact List.mem_flatMap.mpr ⟨e, he, List.mem_flatMap.mpr ⟨t, ht, by simp⟩⟩

def extendAssignment {M : Type*} [Zero M] {k : ℕ} (a : Fin k → M) (i : ℕ) : M :=
  if h : i < k then a ⟨i, h⟩ else 0

theorem rawSat_iff_finiteAssignment
    (B : U →ₗ[ℤ] V →ₗ[ℤ] (Fin p → ℤ)) (S : RawSystem) :
    rawSat B S ↔
      ∃ (u : Fin (variableBound S) → U) (v : Fin (variableBound S) → V),
        ∀ e ∈ S, evalTerms B (extendAssignment u) (extendAssignment v) e.1 = rhsVector e.2 := by
  constructor
  · rintro ⟨u, v, h⟩
    refine ⟨fun i => u i, fun j => v j, fun e he => ?_⟩
    rw [← h e he]
    unfold evalTerms
    congr 1
    apply List.map_congr_left
    intro t ht
    obtain ⟨hi,hj⟩ := term_lt_variableBound he ht
    simp [extendAssignment, hi, hj]
  · rintro ⟨u, v, h⟩
    exact ⟨extendAssignment u, extendAssignment v, h⟩

end FiniteVariables


section LinearExpressions

variable {U V : Type*} [AddCommGroup U] [AddCommGroup V]
  [Module ℤ U] [Module ℤ V] {p : ℕ}

abbrev LinExpr := List (ℤ × ℕ)

def evalLinear {M : Type*} [AddCommGroup M] [Module ℤ M]
    (x : ℕ → M) (e : LinExpr) : M :=
  (e.map fun t => t.1 • x t.2).sum

def pairTerms (e f : LinExpr) : List RawTerm :=
  e.flatMap fun a => f.map fun b => (a.1 * b.1, a.2, b.2)

theorem evalTerms_append
    (B : U →ₗ[ℤ] V →ₗ[ℤ] (Fin p → ℤ)) (u : ℕ → U) (v : ℕ → V)
    (a b : List RawTerm) :
    evalTerms B u v (a ++ b) = evalTerms B u v a + evalTerms B u v b := by
  simp [evalTerms]

theorem evalTerms_pairTerms
    (B : U →ₗ[ℤ] V →ₗ[ℤ] (Fin p → ℤ)) (u : ℕ → U) (v : ℕ → V)
    (e f : LinExpr) :
    evalTerms B u v (pairTerms e f) = B (evalLinear u e) (evalLinear v f) := by
  have one (a : ℤ × ℕ) (fs : LinExpr) :
      evalTerms B u v (fs.map fun b => (a.1 * b.1, a.2, b.2)) =
        B (a.1 • u a.2) (evalLinear v fs) := by
    induction fs with
    | nil => simp [evalTerms, evalLinear]
    | cons b bs ih =>
      change (a.1 * b.1) • B (u a.2) (v b.2) +
          evalTerms B u v (bs.map fun t => (a.1 * t.1, a.2, t.2)) =
        B (a.1 • u a.2) (b.1 • v b.2 + evalLinear v bs)
      rw [ih, map_add]
      congr 1
      rw [map_zsmul, map_zsmul]
      change (a.1 * b.1) • B (u a.2) (v b.2) =
        b.1 • (a.1 • B (u a.2) (v b.2))
      rw [← mul_zsmul, mul_comm]
  induction e with
  | nil => simp [pairTerms, evalTerms, evalLinear]
  | cons a as ih =>
    rw [show pairTerms (a :: as) f =
      (f.map fun b => (a.1 * b.1, a.2, b.2)) ++ pairTerms as f from rfl]
    rw [evalTerms_append, one, ih]
    simp [evalLinear, LinearMap.add_apply]

end LinearExpressions

section GateCompiler

/-- Reserved even IDs are frame columns. Odd IDs encode gate variable and column. -/
def frameIndex (i : ℕ) : ℕ := 2 * i
def gateIndex (x i : ℕ) : ℕ := 2 * Nat.pair x i + 1

def single (i : ℕ) : LinExpr := [(1, i)]

def negTerms (ts : List RawTerm) : List RawTerm :=
  ts.map fun t => (-t.1, t.2)

def pairEq (a b c d : LinExpr) : RawEquation :=
  (pairTerms a b ++ negTerms (pairTerms c d), [])

def adjointEquation (x i j : ℕ) : RawEquation :=
  pairEq (single (gateIndex x i)) (single (frameIndex j))
    (single (frameIndex i)) (single (gateIndex x j))

def additionEquation (x y z i j : ℕ) : RawEquation :=
  ([(1, gateIndex x i, frameIndex j), (1, gateIndex y i, frameIndex j),
    (-1, gateIndex z i, frameIndex j)], [])

def multiplicationEquation (x y z i j : ℕ) : RawEquation :=
  pairEq (single (gateIndex y i)) (single (gateIndex x j))
    (single (gateIndex z i)) (single (frameIndex j))

end GateCompiler

section CompilerSemantics

variable {U V : Type*} [AddCommGroup U] [AddCommGroup V]
  [Module ℤ U] [Module ℤ V] {p : ℕ}
  (B : U →ₗ[ℤ] V →ₗ[ℤ] (Fin p → ℤ))

@[simp] theorem rhsVector_ofFn (w : Fin p → ℤ) : rhsVector (List.ofFn w) = w := by
  funext i
  simp [rhsVector]

@[simp] theorem rhsVector_nil : (rhsVector ([] : List ℤ) : Fin p → ℤ) = 0 := by
  funext i
  simp [rhsVector]

theorem evalTerms_negTerms (u : ℕ → U) (v : ℕ → V) (ts : List RawTerm) :
    evalTerms B u v (negTerms ts) = -evalTerms B u v ts := by
  induction ts with
  | nil => simp [evalTerms, negTerms]
  | cons t ts ih =>
    change (-t.1) • B (u t.2.1) (v t.2.2) + evalTerms B u v (negTerms ts) =
      -(t.1 • B (u t.2.1) (v t.2.2) + evalTerms B u v ts)
    rw [ih, neg_smul, neg_add]

def holdsEquation (u : ℕ → U) (v : ℕ → V) (e : RawEquation) : Prop :=
  evalTerms B u v e.1 = rhsVector e.2

theorem holds_pairEq (u : ℕ → U) (v : ℕ → V) (a b c d : LinExpr) :
    holdsEquation B u v (pairEq a b c d) ↔
      B (evalLinear u a) (evalLinear v b) = B (evalLinear u c) (evalLinear v d) := by
  simp [holdsEquation, pairEq, evalTerms_append, evalTerms_negTerms, evalTerms_pairTerms,
    ← sub_eq_add_neg, sub_eq_zero]

theorem holds_adjointEquation (u : ℕ → U) (v : ℕ → V) (x i j : ℕ) :
    holdsEquation B u v (adjointEquation x i j) ↔
      B (u (gateIndex x i)) (v (frameIndex j)) =
        B (u (frameIndex i)) (v (gateIndex x j)) := by
  rw [adjointEquation, holds_pairEq]
  simp [single, evalLinear]

theorem holds_multiplicationEquation (u : ℕ → U) (v : ℕ → V) (x y z i j : ℕ) :
    holdsEquation B u v (multiplicationEquation x y z i j) ↔
      B (u (gateIndex y i)) (v (gateIndex x j)) =
        B (u (gateIndex z i)) (v (frameIndex j)) := by
  rw [multiplicationEquation, holds_pairEq]
  simp [single, evalLinear]

theorem holds_additionEquation (u : ℕ → U) (v : ℕ → V) (x y z i j : ℕ) :
    holdsEquation B u v (additionEquation x y z i j) ↔
      B (u (gateIndex x i) + u (gateIndex y i)) (v (frameIndex j)) =
        B (u (gateIndex z i)) (v (frameIndex j)) := by
  simp [holdsEquation, additionEquation, evalTerms, LinearMap.add_apply,
    ← sub_eq_add_neg]
  rw [← add_sub_assoc, sub_eq_zero]

def frameEquations {m n : ℕ} (c : Fin m → Fin n → Fin p → ℤ) : RawSystem :=
  (List.finRange m).flatMap fun (i : Fin m) => (List.finRange n).map fun (j : Fin n) =>
    ([(1, frameIndex i, frameIndex j)], List.ofFn (c i j))

theorem holds_frameEquations {m n : ℕ} (c : Fin m → Fin n → Fin p → ℤ)
    (u : ℕ → U) (v : ℕ → V) :
    (∀ e ∈ frameEquations c, holdsEquation B u v e) ↔
      ∀ (i : Fin m) (j : Fin n), B (u (frameIndex i)) (v (frameIndex j)) = c i j := by
  constructor
  · intro h i j
    have hmem : ([(1, frameIndex i, frameIndex j)], List.ofFn (c i j)) ∈ frameEquations c :=
      List.mem_flatMap.mpr ⟨i, by simp, List.mem_map.mpr ⟨j, by simp, rfl⟩⟩
    simpa [holdsEquation, evalTerms] using h _ hmem
  · intro h q hq
    obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hq
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi
    simpa [holdsEquation, evalTerms] using h i j

end CompilerSemantics


end ManinBilinear

namespace ManinBilinear

section Frames

variable {R U H : Type*} [Ring R] [AddCommGroup U] [Module R U]
  [AddCommGroup H] [Module R H] [IsNoetherian R H]

/-- A left inverse realized by an endomorphism of a Noetherian ambient module
forces an endomorphism of the embedded module to be bijective. -/
theorem bijective_of_ambient_left_inverse (e : U →ₗ[R] H) (A : U →ₗ[R] U)
    (T : H →ₗ[R] H) (he : Function.Injective e) (h : ∀ x, T (e (A x)) = e x) :
    Function.Bijective A := by
  let chain : ℕ → Submodule R H :=
    Nat.rec (LinearMap.range e) (fun _ S => S.map T)
  have mono : Monotone chain := monotone_nat_of_le_succ (by
    intro n
    induction n with
    | zero =>
      rintro _ ⟨x, rfl⟩
      exact ⟨e (A x), ⟨A x, rfl⟩, h x⟩
    | succ n ih =>
      exact Submodule.map_mono ih)
  obtain ⟨N, stable⟩ := (monotone_stabilizes_iff_noetherian.mpr
    (inferInstance : IsNoetherian R H)) ⟨chain, mono⟩
  have hstable : chain N = (chain N).map T := stable (N + 1) (Nat.le_succ N)
  let T' := T.restrict (p := chain N) (q := chain N) (fun x hx =>
    hstable.symm ▸ Submodule.mem_map_of_mem hx)
  have Tsurj : Function.Surjective T' := by
    intro x
    have hx : (x : H) ∈ (chain N).map T := hstable ▸ x.property
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp hx
    exact ⟨⟨y, hy⟩, Subtype.ext hyx⟩
  have Tinj := @IsNoetherian.injective_of_surjective_endomorphism R ↥(chain N)
    ‹Ring R› (Submodule.addCommGroup (chain N)) (Submodule.module (chain N))
    (isNoetherian_submodule' (chain N)) T' Tsurj
  have cancel (x y : H) (hx : x ∈ chain N) (hy : y ∈ chain N)
      (hxy : T x = T y) : x = y :=
    congrArg Subtype.val (Tinj (show T' ⟨x, hx⟩ = T' ⟨y, hy⟩ from Subtype.ext hxy))
  have descend (n : ℕ) (hn : n ≤ N) (hs : chain n = chain (n + 1)) :
      chain 0 = chain 1 := by
    induction n with
    | zero => exact hs
    | succ n ih =>
      apply ih (Nat.le_trans (Nat.le_succ n) hn)
      refine le_antisymm (mono (Nat.le_succ n)) ?_
      intro x hx
      have htx : T x ∈ chain (n + 1) := hs.symm ▸ Submodule.mem_map_of_mem hx
      obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp htx
      exact cancel y x (mono (Nat.le_trans (Nat.le_succ n) hn) hy) (mono hn hx) hyx ▸ hy
  have eq₀ := descend N le_rfl hstable
  constructor
  · intro x y hxy
    exact he ((h x).symm.trans ((congrArg (fun z => T (e z)) hxy).trans (h y)))
  · intro x
    have hx : T (e x) ∈ chain 1 := Submodule.mem_map_of_mem (show e x ∈ chain 0 from ⟨x, rfl⟩)
    have hx' : T (e x) ∈ chain 0 := eq₀.symm ▸ hx
    obtain ⟨y, hy⟩ := hx'
    refine ⟨y, he (cancel (e (A y)) (e x) ?_ ?_ ((h y).trans hy))⟩
    · exact mono (Nat.zero_le N) ⟨A y, rfl⟩
    · exact mono (Nat.zero_le N) ⟨x, rfl⟩

end Frames

section Bilinear

variable {R U V W : Type*} [CommRing R] [AddCommGroup U] [Module R U]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/-- A pair of endomorphisms preserving a bilinear map with zero radicals is a
pair of automorphisms, provided the two ambient Hom modules are Noetherian. -/
theorem frame_bijective [IsNoetherian R (U →ₗ[R] W)] [IsNoetherian R (V →ₗ[R] W)]
    (B : U →ₗ[R] V →ₗ[R] W) (A : U →ₗ[R] U) (D : V →ₗ[R] V)
    (hleft : Function.Injective B) (hright : Function.Injective B.flip)
    (h : ∀ x y, B (A x) (D y) = B x y) :
    Function.Bijective A ∧ Function.Bijective D := by
  constructor
  · exact bijective_of_ambient_left_inverse B A (LinearMap.lcomp R _ D) hleft
      (fun x => LinearMap.ext (h x))
  · exact bijective_of_ambient_left_inverse B.flip D (LinearMap.lcomp R _ A) hright
      (fun y => LinearMap.ext (fun x => h x y))

/-- Frames satisfying only their pairwise equations arise from integral
linear equivalences. Applying their inverse normalizes the frame without
changing any pairing. -/
theorem frame_normalization [IsNoetherian R (U →ₗ[R] W)] [IsNoetherian R (V →ₗ[R] W)]
    {ι κ : Type*} (B : U →ₗ[R] V →ₗ[R] W) (e : Module.Basis ι R U)
    (f : Module.Basis κ R V) (a : ι → U) (b : κ → V)
    (hleft : Function.Injective B) (hright : Function.Injective B.flip)
    (h : ∀ i j, B (a i) (b j) = B (e i) (f j)) :
    ∃ A : U ≃ₗ[R] U, ∃ D : V ≃ₗ[R] V,
      (∀ i, A.symm (a i) = e i) ∧ (∀ j, D.symm (b j) = f j) ∧
      (∀ x y, B (A.symm x) (D.symm y) = B x y) := by
  let A := e.constr R a
  let D := f.constr R b
  have hm : (B.compl₂ D).comp A = B := by
    apply e.ext
    intro i
    apply f.ext
    intro j
    simpa only [LinearMap.comp_apply, LinearMap.compl₂_apply, A, D, Module.Basis.constr_basis]
      using h i j
  have hp (x : U) (y : V) : B (A x) (D y) = B x y :=
    DFunLike.congr_fun (DFunLike.congr_fun hm x) y
  obtain ⟨ha, hd⟩ := frame_bijective B A D hleft hright hp
  let A' := LinearEquiv.ofBijective A ha
  let D' := LinearEquiv.ofBijective D hd
  refine ⟨A', D', ?_, ?_, ?_⟩
  · intro i
    apply A'.injective
    rw [LinearEquiv.apply_symm_apply]
    exact (e.constr_basis R a i).symm
  · intro j
    apply D'.injective
    rw [LinearEquiv.apply_symm_apply]
    exact (f.constr_basis R b j).symm
  · intro x y
    have hv := (hp (A'.symm x) (D'.symm y)).symm
    change B (A'.symm x) (D'.symm y) = B (A' (A'.symm x)) (D' (D'.symm y)) at hv
    simpa only [LinearEquiv.apply_symm_apply] using hv

end Bilinear


end ManinBilinear

namespace ManinBilinear

/-- The effective source syntax. Variable identifiers are natural numbers. -/
abbrev Gate (κ : Type*) :=
  (ℕ × ℕ × ℕ) ⊕ ((ℕ × ℕ × ℕ) ⊕ (ℕ × κ))

namespace Gate

def add (i j k : ℕ) : Gate κ := Sum.inl (i, j, k)
def mul (i j k : ℕ) : Gate κ := Sum.inr (Sum.inl (i, j, k))
def const (i : ℕ) (c : κ) : Gate κ := Sum.inr (Sum.inr (i, c))

/-- A gate is a single equation in the assigned ring values. -/
def Holds {R : Type*} [Ring R] (decode : κ → R) (x : ℕ → R) : Gate κ → Prop
  | .inl (i, j, k) => x i + x j = x k
  | .inr (.inl (i, j, k)) => x i * x j = x k
  | .inr (.inr (i, c)) => x i = decode c

end Gate

/-- Solvability of a finite list of addition, multiplication and constant gates. -/
def gateSat {R : Type*} [Ring R] (decode : κ → R) (gs : List (Gate κ)) : Prop :=
  ∃ x : ℕ → R, ∀ g ∈ gs, g.Holds decode x

/-- A finite list stores the coordinates in the fixed integral basis. -/
noncomputable def basisDecode {R : Type*} [Ring R] {d : ℕ}
    (b : Module.Basis (Fin d) ℤ R) (cs : List ℤ) : R :=
  ∑ i : Fin d, cs[i.val]?.getD 0 • b i

theorem basisDecode_surjective {R : Type*} [Ring R] {d : ℕ}
    (b : Module.Basis (Fin d) ℤ R) : Function.Surjective (basisDecode b) := by
  intro r
  refine ⟨List.ofFn (fun i : Fin d => b.repr r i), ?_⟩
  simpa [basisDecode, List.getElem?_ofFn] using b.sum_repr r

/-- The finite-free characteristic-zero instance of the arithmetic dependency,
stated in the finite gate presentation. This is a proposition, not an axiom. -/
def KoymansPaganoFiniteFree : Prop :=
  ∀ (R : Type) [CommRing R] [Nontrivial R] (d : ℕ) (b : Module.Basis (Fin d) ℤ R),
    ¬ ComputablePred (gateSat (basisDecode b))

/-- Pull back a computable decision procedure along an effective reduction. -/
theorem computablePred_pullback {A B : Type*} [Primcodable A] [Primcodable B]
    {p : A → Prop} {q : B → Prop} {f : A → B}
    (hf : Computable f) (h : ∀ x, p x ↔ q (f x)) :
    ComputablePred q → ComputablePred p := by
  intro hq
  obtain ⟨g, hg, rfl⟩ := ComputablePred.computable_iff.mp hq
  exact (ComputablePred.computable_iff.mpr ⟨g ∘ f, hg.comp hf, rfl⟩).of_eq (fun x => (h x).symm)



/- The fresh-variable tape interface is inspired by Cameron Freer, Hilbert10/QuadraticGates.lean (Apache-2.0). The gate encoding and proofs below are self-contained. -/
namespace Gate

/-- Variable written by the gate when it is used as a circuit instruction. -/
def output : Gate κ → ℕ
  | .inl (_, _, k) => k
  | .inr (.inl (_, _, k)) => k
  | .inr (.inr (k, _)) => k

/-- Variables read by a gate used as a circuit instruction. -/
def reads : Gate κ → List ℕ
  | .inl (i, j, _) => [i, j]
  | .inr (.inl (i, j, _)) => [i, j]
  | .inr (.inr _) => []

/-- Evaluate the right-hand side of an instruction before its output is assigned. -/
def value {R : Type*} [Ring R] (decode : κ → R) (x : ℕ → R) : Gate κ → R
  | .inl (i, j, _) => x i + x j
  | .inr (.inl (i, j, _)) => x i * x j
  | .inr (.inr (_, c)) => decode c

theorem holds_iff_value {R : Type*} [Ring R] (decode : κ → R) (x : ℕ → R)
    (g : Gate κ) : g.Holds decode x ↔ g.value decode x = x g.output := by
  rcases g with ⟨i, j, k⟩ | (⟨i, j, k⟩ | ⟨k, c⟩)
  · rfl
  · rfl
  · exact eq_comm

theorem value_congr {R : Type*} [Ring R] (decode : κ → R)
    {x y : ℕ → R} (g : Gate κ) (h : ∀ i ∈ g.reads, x i = y i) :
    g.value decode x = g.value decode y := by
  rcases g with ⟨i, j, k⟩ | (⟨i, j, k⟩ | ⟨k, c⟩)
  · exact congrArg₂ (· + ·) (h i (by simp [reads])) (h j (by simp [reads]))
  · exact congrArg₂ (· * ·) (h i (by simp [reads])) (h j (by simp [reads]))
  · rfl

end Gate

/-- Each instruction writes the next unused index, and reads only earlier indices. -/
def WellOrdered : ℕ → List (Gate κ) → Prop
  | _, [] => True
  | n, g :: gs =>
      g.output = n ∧ (∀ i ∈ g.reads, i < n) ∧ WellOrdered (n + 1) gs

/-- Evaluate a straight-line polynomial tape. Inputs are the variables below the start index. -/
def evalTape {R : Type*} [Ring R] (decode : κ → R) :
    List (Gate κ) → (ℕ → R) → ℕ → R
  | [], x => x
  | g :: gs, x => evalTape decode gs (Function.update x g.output (g.value decode x))

theorem evalTape_agrees {R : Type*} [Ring R] (decode : κ → R)
    (gs : List (Gate κ)) (n : ℕ) (hw : WellOrdered n gs) (x : ℕ → R) :
    ∀ i < n, evalTape decode gs x i = x i := by
  induction gs generalizing n x with
  | nil => simp [evalTape]
  | cons g gs ih =>
    obtain ⟨ho, _, ht⟩ := hw
    intro i hi
    rw [evalTape, ih (n + 1) ht _ i (Nat.lt_succ_of_lt hi)]
    simp [Function.update, ho, Nat.ne_of_lt hi]

theorem evalTape_holds {R : Type*} [Ring R] (decode : κ → R)
    (gs : List (Gate κ)) (n : ℕ) (hw : WellOrdered n gs) (x : ℕ → R) :
    ∀ g ∈ gs, g.Holds decode (evalTape decode gs x) := by
  induction gs generalizing n x with
  | nil => simp
  | cons g gs ih =>
    obtain ⟨ho, hr, ht⟩ := hw
    rw [evalTape, List.forall_mem_cons]
    set y := Function.update x g.output (g.value decode x)
    refine ⟨?_, ih (n + 1) ht y⟩
    have hval : g.value decode (evalTape decode gs y) = g.value decode x := by
      apply Gate.value_congr
      intro i hi
      rw [evalTape_agrees decode gs (n + 1) ht y i (Nat.lt_succ_of_lt (hr i hi))]
      simp [y, ho, Nat.ne_of_lt (hr i hi)]
    rw [Gate.holds_iff_value, hval, evalTape_agrees decode gs (n + 1) ht y _ (by omega)]
    simp [y]

theorem evalTape_eq_of_holds {R : Type*} [Ring R] (decode : κ → R)
    (gs : List (Gate κ)) (x : ℕ → R) (h : ∀ g ∈ gs, g.Holds decode x) :
    evalTape decode gs x = x := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    have hg := (g.holds_iff_value decode x).mp (h g (by simp))
    rw [evalTape, hg, Function.update_eq_self]
    exact ih (fun a ha => h a (by simp [ha]))

/-- Add output-to-zero equations to a tape to obtain the finite gate system. -/
def compileTape (zero : κ) (gs : List (Gate κ)) (outputs : List ℕ) : List (Gate κ) :=
  gs ++ outputs.map (fun i => Gate.const i zero)

/-- The compiled equations have exactly the solvability of the polynomial tape. -/
theorem gateSat_compileTape_iff {R : Type*} [Ring R] (decode : κ → R)
    (gs : List (Gate κ)) (outputs : List ℕ) (zero : κ) (hz : decode zero = 0)
    (n : ℕ) (hw : WellOrdered n gs) :
    gateSat decode (compileTape zero gs outputs) ↔
      ∃ x : ℕ → R, ∀ i ∈ outputs, evalTape decode gs x i = 0 := by
  simp only [gateSat, compileTape, List.mem_append, List.mem_map]
  constructor
  · rintro ⟨x, hx⟩
    have heq := evalTape_eq_of_holds decode gs x (fun g hg => hx g (Or.inl hg))
    refine ⟨x, fun i hi => ?_⟩
    rw [heq, ← hz]
    exact hx (Gate.const i zero) (Or.inr ⟨i, hi, rfl⟩)
  · rintro ⟨x, hx⟩
    refine ⟨evalTape decode gs x, ?_⟩
    rintro g (hg | ⟨i, hi, rfl⟩)
    · exact evalTape_holds decode gs n hw x g hg
    · change evalTape decode gs x i = decode zero
      rw [hx i hi, hz]


/-- The tape-to-equations transformation is executable on the finite encoding. -/
theorem primrec_compileTape [Primcodable κ] (zero : κ) :
    Primrec (fun p : List (Gate κ) × List ℕ => compileTape zero p.1 p.2) := by
  unfold compileTape
  apply Primrec.list_append.comp Primrec.fst
  apply Primrec.list_map Primrec.snd
  change Primrec (fun p : (List (Gate κ) × List ℕ) × ℕ => Gate.const p.2 zero)
  exact Primrec.sumInr.comp (Primrec.sumInr.comp (Primrec.snd.pair (Primrec.const zero)))


end ManinBilinear

/-! Integral adjoints and their central multiplication encoding for Manin's conjecture. -/

namespace ManinBilinear

set_option linter.style.haveILetI false

variable {U V W : Type*}
  [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
  [Module ℤ U] [Module ℤ V] [Module ℤ W]

abbrev EndPair (U V : Type*) [AddCommGroup U] [AddCommGroup V] [Module ℤ U] [Module ℤ V] :=
  Module.End ℤ U × (Module.End ℤ V)ᵐᵒᵖ

def IsAdjoint (β : U →ₗ[ℤ] V →ₗ[ℤ] W) (a : EndPair U V) : Prop :=
  ∀ u v, β (a.1 u) v = β u (MulOpposite.unop a.2 v)

def adjointRing (β : U →ₗ[ℤ] V →ₗ[ℤ] W) : Subring (EndPair U V) where
  carrier := { a | IsAdjoint β a }
  zero_mem' := by
    intro u v
    change β 0 v = β u 0
    simp
  one_mem' := fun _ _ => rfl
  add_mem' {a b} ha hb := by
    intro u v
    change β (a.1 u + b.1 u) v = β u (MulOpposite.unop a.2 v + MulOpposite.unop b.2 v)
    simp only [map_add, LinearMap.add_apply]
    rw [ha u v, hb u v]
  neg_mem' {a} ha := by
    intro u v
    change β (-a.1 u) v = β u (-MulOpposite.unop a.2 v)
    simp only [map_neg, LinearMap.neg_apply]
    rw [ha u v]
  mul_mem' {a b} ha hb := by
    intro u v
    change β (a.1 (b.1 u)) v = β u (MulOpposite.unop b.2 (MulOpposite.unop a.2 v))
    rw [ha (b.1 u) v, hb u (MulOpposite.unop a.2 v)]

abbrev Adjoint (β : U →ₗ[ℤ] V →ₗ[ℤ] W) := ↥(adjointRing β)

abbrev centerRing (β : U →ₗ[ℤ] V →ₗ[ℤ] W) : Subring (Adjoint β) :=
  Subring.center (Adjoint β)

abbrev Center (β : U →ₗ[ℤ] V →ₗ[ℤ] W) := ↥(centerRing β)

variable {β : U →ₗ[ℤ] V →ₗ[ℤ] W}

def left (a : Adjoint β) : Module.End ℤ U := a.val.1

def right (a : Adjoint β) : Module.End ℤ V := MulOpposite.unop a.val.2

theorem adjoint_spec (a : Adjoint β) (u : U) (v : V) : β (left a u) v = β u (right a v) :=
  a.property u v

@[simp] theorem left_add (a b : Adjoint β) : left (a+b) = left a + left b := rfl
@[simp] theorem left_mul (a b : Adjoint β) : left (a*b) = left a * left b := rfl
@[simp] theorem left_zero : left (0 : Adjoint β) = 0 := rfl

theorem left_injective (hβ : ∀ v : V, (∀ u : U, β u v = 0) → v = 0) :
    Function.Injective (left (β := β)) := by
  intro a b h
  have hright : right a = right b := by
    ext v
    apply sub_eq_zero.mp
    apply hβ
    intro u
    rw [map_sub, ← adjoint_spec a, ← adjoint_spec b, h, sub_self]
  apply Subtype.ext
  exact Prod.ext h (MulOpposite.unop_injective hright)

theorem isAdjoint_iff_basis {ι κ : Type*} (e : Module.Basis ι ℤ U)
    (f : Module.Basis κ ℤ V) (a : EndPair U V) :
    IsAdjoint β a ↔ ∀ i j, β (a.1 (e i)) (f j) = β (e i) (MulOpposite.unop a.2 (f j)) := by
  refine ⟨fun h i j => h (e i) (f j), fun h => ?_⟩
  let g : U →ₗ[ℤ] V →ₗ[ℤ] W := β.comp a.1
  let precomp : (V →ₗ[ℤ] W) →+ (V →ₗ[ℤ] W) :=
    { toFun := fun T => T.comp (MulOpposite.unop a.2)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let k : U →ₗ[ℤ] V →ₗ[ℤ] W := precomp.toIntLinearMap.comp β
  have eq : g = k := e.ext (fun i => f.ext (fun j => h i j))
  intro u v
  exact congrArg (fun b : U →ₗ[ℤ] V →ₗ[ℤ] W => b u v) eq

theorem left_eq_iff_basis {ι κ : Type*} (e : Module.Basis ι ℤ U)
    (f : Module.Basis κ ℤ V) (hβ : ∀ u : U, (∀ v : V, β u v = 0) → u = 0)
    (A B : Module.End ℤ U) :
    A = B ↔ ∀ i j, β (A (e i)) (f j) = β (B (e i)) (f j) := by
  refine ⟨fun h i j => h ▸ rfl, fun h => e.ext fun i => ?_⟩
  apply sub_eq_zero.mp
  apply hβ
  intro v
  have eq : β (A (e i)) = β (B (e i)) := f.ext (h i)
  have hval := LinearMap.congr_fun eq v
  simp only [map_sub, LinearMap.sub_apply, hval, sub_self]

theorem adjoint_eq_iff_basis {ι κ : Type*} (e : Module.Basis ι ℤ U)
    (f : Module.Basis κ ℤ V) (hl : ∀ u : U, (∀ v : V, β u v = 0) → u = 0)
    (hr : ∀ v : V, (∀ u : U, β u v = 0) → v = 0) (a b : Adjoint β) :
    a = b ↔ ∀ i j, β (left a (e i)) (f j) = β (left b (e i)) (f j) :=
  (left_injective (β := β) hr).eq_iff.symm.trans (left_eq_iff_basis e f hl _ _)

theorem mul_eq_iff_basis {ι κ : Type*} (e : Module.Basis ι ℤ U)
    (f : Module.Basis κ ℤ V) (hl : ∀ u : U, (∀ v : V, β u v = 0) → u = 0)
    (hr : ∀ v : V, (∀ u : U, β u v = 0) → v = 0) (a b c : Adjoint β) :
    a * b = c ↔ ∀ i j, β (left b (e i)) (right a (f j)) = β (left c (e i)) (f j) := by
  rw [adjoint_eq_iff_basis e f hl hr]
  simp only [left_mul, Module.End.mul_apply, adjoint_spec]

theorem add_eq_iff_basis {ι κ : Type*} (e : Module.Basis ι ℤ U)
    (f : Module.Basis κ ℤ V) (hl : ∀ u : U, (∀ v : V, β u v = 0) → u = 0)
    (hr : ∀ v : V, (∀ u : U, β u v = 0) → v = 0) (a b c : Adjoint β) :
    a + b = c ↔ ∀ i j, β (left a (e i)) (f j) + β (left b (e i)) (f j) =
      β (left c (e i)) (f j) := by
  rw [adjoint_eq_iff_basis e f hl hr]
  simp only [left_add, LinearMap.add_apply, map_add]

theorem commute_iff_basis {ι κ : Type*} (e : Module.Basis ι ℤ U)
    (f : Module.Basis κ ℤ V) (hl : ∀ u : U, (∀ v : V, β u v = 0) → u = 0)
    (hr : ∀ v : V, (∀ u : U, β u v = 0) → v = 0) (a b : Adjoint β) :
    b * a = a * b ↔ ∀ i j, β (left a (e i)) (right b (f j)) =
      β (left b (e i)) (right a (f j)) := by
  rw [← (left_injective (β := β) hr).eq_iff, left_eq_iff_basis e f hl]
  simp only [left_mul, Module.End.mul_apply, adjoint_spec]

noncomputable def adjointEmbedding (β : U →ₗ[ℤ] V →ₗ[ℤ] W) :
    Adjoint β →ₗ[ℤ] EndPair U V :=
  (adjointRing β).subtype.toAddMonoidHom.toIntLinearMap

private noncomputable def endCoordinates {ι : Type*} (e : Module.Basis ι ℤ U) :
    Module.End ℤ U →+ (ι → ι → ℤ) where
  toFun A i j := e.repr (A (e i)) j
  map_zero' := by
    funext i j
    simp
  map_add' A B := by
    funext i j
    simp

private theorem endCoordinates_injective {ι : Type*} (e : Module.Basis ι ℤ U) :
    Function.Injective (endCoordinates e) := by
  intro A B eq
  apply e.ext
  intro i
  apply e.repr.injective
  exact Finsupp.ext fun j => congrFun (congrFun eq i) j

private theorem endFinite [Module.Free ℤ U] [Module.Finite ℤ U] :
    Module.Finite ℤ (Module.End ℤ U) :=
  Module.Finite.of_injective (endCoordinates (Module.finBasis ℤ U)).toIntLinearMap
    (endCoordinates_injective (Module.finBasis ℤ U))

theorem adjointFinite [Module.Free ℤ U] [Module.Finite ℤ U]
    [Module.Free ℤ V] [Module.Finite ℤ V] : Module.Finite ℤ (Adjoint β) := by
  haveI : Module.Finite ℤ (Module.End ℤ U) := endFinite
  haveI : Module.Finite ℤ (Module.End ℤ V) := endFinite
  haveI : IsNoetherian ℤ ((Module.End ℤ V)ᵐᵒᵖ) :=
    isNoetherian_of_linearEquiv (MulOpposite.opLinearEquiv ℤ)
  haveI : IsNoetherian ℤ (EndPair U V) := isNoetherian_prod
  exact Module.Finite.of_injective (adjointEmbedding β) Subtype.val_injective

theorem centerFinite [Module.Free ℤ U] [Module.Finite ℤ U]
    [Module.Free ℤ V] [Module.Finite ℤ V] : Module.Finite ℤ (Center β) := by
  haveI := adjointFinite (β := β)
  exact Module.Finite.of_injective
    (centerRing β).subtype.toAddMonoidHom.toIntLinearMap Subtype.val_injective

theorem adjointGenerators [Module.Free ℤ U] [Module.Finite ℤ U]
    [Module.Free ℤ V] [Module.Finite ℤ V] :
    ∃ d, ∃ g : Fin d → Adjoint β, Submodule.span ℤ (Set.range g) = ⊤ := by
  haveI := adjointFinite (β := β)
  exact Module.Finite.exists_fin

theorem centerFiniteType [Module.Free ℤ U] [Module.Finite ℤ U]
    [Module.Free ℤ V] [Module.Finite ℤ V] : Algebra.FiniteType ℤ (Center β) := by
  haveI := centerFinite (β := β)
  infer_instance

theorem centerCharZero [Nontrivial U] [Module.IsTorsionFree ℤ U] : CharZero (Center β) := by
  refine ⟨fun m n h => ?_⟩
  obtain ⟨u, hu⟩ := exists_ne (0 : U)
  let φ : Adjoint β →+* Module.End ℤ U :=
    (RingHom.fst _ _).comp (adjointRing β).subtype
  have eq := congrArg (fun a : Center β => φ ((centerRing β).subtype a) u) h
  have hs : (m : ℤ) • u = (n : ℤ) • u := by
    simpa only [map_natCast, Module.End.natCast_apply, natCast_zsmul] using eq
  have he : (m : ℤ) = (n : ℤ) := by
    apply smul_left_injective ℤ hu
    change (inferInstance : Module ℤ U).smul (m : ℤ) u =
      (inferInstance : Module ℤ U).smul (n : ℤ) u
    simpa only [int_smul_eq_zsmul] using hs
  exact Int.natCast_inj.mp he

theorem center_mem_iff_generators {ι : Type*} (g : ι → Adjoint β)
    (hg : Submodule.span ℤ (Set.range g) = ⊤) (a : Adjoint β) :
    a ∈ centerRing β ↔ ∀ i, g i * a = a * g i := by
  rw [centerRing, Subring.mem_center_iff]
  refine ⟨fun h i => h (g i), fun h b => ?_⟩
  have hb : b ∈ Submodule.span ℤ (Set.range g) := by rw [hg]; exact Submodule.mem_top
  exact Submodule.span_induction (s := Set.range g) (p := fun b _ => b * a = a * b)
    (fun b hb => by obtain ⟨i, rfl⟩ := hb; exact h i)
    (by simp)
    (fun b c _ _ hb hc => by simp only [add_mul, mul_add, hb, hc])
    (fun z b _ hb => by
      change AddMonoidHom.mulRight a (z • b) = AddMonoidHom.mulLeft a (z • b)
      rw [map_zsmul, map_zsmul]
      exact congrArg (z • ·) hb)
    hb

theorem center_mem_iff_generator_equations {ι κ σ : Type*}
    (e : Module.Basis ι ℤ U) (f : Module.Basis κ ℤ V)
    (hl : ∀ u : U, (∀ v : V, β u v = 0) → u = 0)
    (hr : ∀ v : V, (∀ u : U, β u v = 0) → v = 0)
    (g : σ → Adjoint β) (hg : Submodule.span ℤ (Set.range g) = ⊤) (a : Adjoint β) :
    a ∈ centerRing β ↔ ∀ s i j, β (left a (e i)) (right (g s) (f j)) =
      β (left (g s) (e i)) (right a (f j)) := by
  simp only [center_mem_iff_generators g hg, commute_iff_basis e f hl hr]

noncomputable def centerBasis [Module.Free ℤ U] [Module.Finite ℤ U]
    [Module.Free ℤ V] [Module.Finite ℤ V]
    (hr : ∀ v : V, (∀ u : U, β u v = 0) → v = 0) :
    Σ n, Module.Basis (Fin n) ℤ (Center β) := by
  haveI := centerFinite (β := β)
  let φ : Adjoint β →+* Module.End ℤ U :=
    (RingHom.fst _ _).comp (adjointRing β).subtype
  let ψ : Center β →ₗ[ℤ] Module.End ℤ U :=
    (φ.comp (centerRing β).subtype).toAddMonoidHom.toIntLinearMap
  have hψ : Function.Injective ψ := by
    intro a b hab
    exact Subtype.val_injective (left_injective (β := β) hr hab)
  let e := Module.finBasis ℤ U
  let coord := (endCoordinates e).toIntLinearMap.comp ψ
  have hcoord : Function.Injective coord := (endCoordinates_injective e).comp hψ
  letI : Module.IsTorsionFree ℤ (Center β) :=
    Function.Injective.moduleIsTorsionFree coord hcoord (fun r a => map_smul coord r a)
  exact Module.basisOfFiniteTypeTorsionFree'

theorem center_eq_iff_basis {ι κ : Type*} (e : Module.Basis ι ℤ U)
    (f : Module.Basis κ ℤ V) (hl : ∀ u : U, (∀ v : V, β u v = 0) → u = 0)
    (hr : ∀ v : V, (∀ u : U, β u v = 0) → v = 0) (a b : Center β) :
    a = b ↔ ∀ i j, β (left a.val (e i)) (f j) = β (left b.val (e i)) (f j) :=
  Subtype.val_injective.eq_iff.symm.trans (adjoint_eq_iff_basis e f hl hr _ _)

theorem center_mul_eq_iff_basis {ι κ : Type*} (e : Module.Basis ι ℤ U)
    (f : Module.Basis κ ℤ V) (hl : ∀ u : U, (∀ v : V, β u v = 0) → u = 0)
    (hr : ∀ v : V, (∀ u : U, β u v = 0) → v = 0) (a b c : Center β) :
    a * b = c ↔ ∀ i j, β (left b.val (e i)) (right a.val (f j)) = β (left c.val (e i)) (f j) :=
  Subtype.val_injective.eq_iff.symm.trans (mul_eq_iff_basis e f hl hr _ _ _)

theorem center_add_eq_iff_basis {ι κ : Type*} (e : Module.Basis ι ℤ U)
    (f : Module.Basis κ ℤ V) (hl : ∀ u : U, (∀ v : V, β u v = 0) → u = 0)
    (hr : ∀ v : V, (∀ u : U, β u v = 0) → v = 0) (a b c : Center β) :
    a + b = c ↔ ∀ i j, β (left a.val (e i)) (f j) + β (left b.val (e i)) (f j) =
      β (left c.val (e i)) (f j) :=
  Subtype.val_injective.eq_iff.symm.trans (add_eq_iff_basis e f hl hr _ _ _)

theorem exists_center_of_columns_iff {ι κ σ : Type*}
    (e : Module.Basis ι ℤ U) (f : Module.Basis κ ℤ V)
    (hl : ∀ u : U, (∀ v : V, β u v = 0) → u = 0)
    (hr : ∀ v : V, (∀ u : U, β u v = 0) → v = 0)
    (g : σ → Adjoint β) (hg : Submodule.span ℤ (Set.range g) = ⊤)
    (x : ι → U) (y : κ → V) :
    (∃ a : Center β, (∀ i, left a.val (e i) = x i) ∧ (∀ j, right a.val (f j) = y j)) ↔
    (∀ i j, β (x i) (f j) = β (e i) (y j)) ∧
      (∀ s i j, β (x i) (right (g s) (f j)) = β (left (g s) (e i)) (y j)) := by
  constructor
  · rintro ⟨a, hx, hy⟩
    refine ⟨?_, ?_⟩
    · intro i j
      rw [← hx i, ← hy j]
      exact adjoint_spec a.val _ _
    · intro s i j
      rw [← hx i, ← hy j]
      exact (center_mem_iff_generator_equations e f hl hr g hg a.val).mp a.property s i j
  · rintro ⟨hm, hc⟩
    classical
    let L : Module.End ℤ U := (Finsupp.linearCombination ℤ x).comp e.repr.toLinearMap
    let R : Module.End ℤ V := (Finsupp.linearCombination ℤ y).comp f.repr.toLinearMap
    have hL (i : ι) : L (e i) = x i := by
      simp only [L, LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.repr_self,
        Finsupp.linearCombination_single]
      exact (inferInstance : Module ℤ U).one_smul _
    have hR (j : κ) : R (f j) = y j := by
      simp only [R, LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.repr_self,
        Finsupp.linearCombination_single]
      exact (inferInstance : Module ℤ V).one_smul _
    have hp : IsAdjoint β (L, MulOpposite.op R) := by
      apply (isAdjoint_iff_basis e f _).mpr
      intro i j
      change β (L (e i)) (f j) = β (e i) (R (f j))
      rw [hL, hR]
      exact hm i j
    let a : Adjoint β := ⟨(L, MulOpposite.op R), hp⟩
    have hx : ∀ i, left a (e i) = x i := hL
    have hy : ∀ j, right a (f j) = y j := hR
    have ha : a ∈ centerRing β := by
      apply (center_mem_iff_generator_equations e f hl hr g hg a).mpr
      intro s i j
      rw [hx, hy]
      exact hc s i j
    exact ⟨⟨a, ha⟩, hx, hy⟩


end ManinBilinear

/-! The radical quotients in Manin's reduction are finite free integer lattices. -/

namespace ManinBilinear

private theorem quotientFinite {M : Type*} [AddCommGroup M] [Module ℤ M]
    [Module.Free ℤ M] [Module.Finite ℤ M] (S : Submodule ℤ M) :
    Module.Finite ℤ (M ⧸ S) := by
  let e := Module.finBasis ℤ M
  let q := S.mkQ.toAddMonoidHom.comp e.equivFun.symm.toAddEquiv.toAddMonoidHom
  apply Module.Finite.of_surjective q.toIntLinearMap
  exact (Submodule.Quotient.mk_surjective S).comp e.equivFun.symm.surjective

private theorem torsionFree_of_injective_bilinear
    {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    {p : ℕ} (C : M →ₗ[ℤ] N →ₗ[ℤ] (Fin p → ℤ)) (hC : Function.Injective C) :
    Module.IsTorsionFree ℤ M := by
  let q : M →+ (N → Fin p → ℤ) :=
    { toFun := fun x y => C x y
      map_zero' := by funext y; simp
      map_add' := by intro x x'; funext y; simp [LinearMap.add_apply] }
  have hq : Function.Injective q := by
    intro a b h
    apply hC
    exact LinearMap.ext (fun y => congrFun h y)
  let f := q.toIntLinearMap
  exact Function.Injective.moduleIsTorsionFree f hq (fun r x => map_smul f r x)

section ReducedLattices

variable {U V : Type*} [AddCommGroup U] [AddCommGroup V]
    [Module ℤ U] [Module ℤ V] {p : ℕ}
    (B : U →ₗ[ℤ] V →ₗ[ℤ] (Fin p → ℤ))

instance leftReducedFinite [Module.Free ℤ U] [Module.Finite ℤ U] :
    Module.Finite ℤ (LeftReduced B) := quotientFinite B.ker

instance rightReducedFinite [Module.Free ℤ V] [Module.Finite ℤ V] :
    Module.Finite ℤ (RightReduced B) := quotientFinite B.flip.ker

instance leftReducedTorsionFree : Module.IsTorsionFree ℤ (LeftReduced B) :=
  torsionFree_of_injective_bilinear (reduced B) (reduced_left_injective B)

instance rightReducedTorsionFree : Module.IsTorsionFree ℤ (RightReduced B) :=
  torsionFree_of_injective_bilinear (reduced B).flip (reduced_right_injective B)

noncomputable def reducedBasis [Module.Free ℤ U] [Module.Finite ℤ U]
    [Module.Free ℤ V] [Module.Finite ℤ V] :
    (Σ n, Module.Basis (Fin n) ℤ (LeftReduced B)) ×
    (Σ n, Module.Basis (Fin n) ℤ (RightReduced B)) :=
  ⟨Module.basisOfFiniteTypeTorsionFree', Module.basisOfFiniteTypeTorsionFree'⟩

theorem leftReduced_nontrivial (h : B ≠ 0) : Nontrivial (LeftReduced B) := by
  by_contra hn
  letI : Subsingleton (LeftReduced B) := not_nontrivial_iff_subsingleton.mp hn
  apply reduced_ne_zero B h
  apply LinearMap.ext
  intro u
  rw [Subsingleton.elim u 0, map_zero]
  rfl


end ReducedLattices
end ManinBilinear

namespace ManinBilinear

section NormalizedFrames

variable {U V : Type*} [AddCommGroup U] [AddCommGroup V]
  [Module ℤ U] [Module ℤ V] [Module.Finite ℤ U] [Module.Finite ℤ V] {p : ℕ}
  (B : U →ₗ[ℤ] V →ₗ[ℤ] (Fin p → ℤ))

/-- The coefficient-only frame equations allow exactly the same satisfiability
test as fixed frame vectors: normalize any solution by the inverse frame maps. -/
theorem rawSat_frameEquations_iff {m n : ℕ} (e : Module.Basis (Fin m) ℤ U)
    (f : Module.Basis (Fin n) ℤ V) (hleft : Function.Injective B)
    (hright : Function.Injective B.flip) (S : RawSystem) :
    rawSat B (frameEquations (fun i j => B (e i) (f j)) ++ S) ↔
      ∃ (u : ℕ → U) (v : ℕ → V),
        (∀ i : Fin m, u (frameIndex i) = e i) ∧
        (∀ j : Fin n, v (frameIndex j) = f j) ∧
        ∀ q ∈ S, holdsEquation B u v q := by
  constructor
  · rintro ⟨u, v, huv⟩
    have hframe :=
      (holds_frameEquations B (fun i j => B (e i) (f j)) u v).mp
        (fun q hq => huv q (List.mem_append.mpr (Or.inl hq)))
    obtain ⟨A, D, hA, hD, hpair⟩ :=
      frame_normalization B e f (fun i => u (frameIndex i)) (fun j => v (frameIndex j))
        hleft hright hframe
    refine ⟨A.symm ∘ u, D.symm ∘ v, hA, hD, ?_⟩
    intro q hq
    have hq' := huv q (List.mem_append.mpr (Or.inr hq))
    simpa only [holdsEquation, evalTerms, Function.comp_apply, hpair] using hq'
  · rintro ⟨u, v, hu, hv, hS⟩
    refine ⟨u, v, fun q hq => ?_⟩
    rcases List.mem_append.mp hq with hq | hq
    · exact (holds_frameEquations B (fun i j => B (e i) (f j)) u v).mpr
        (fun i j => by rw [hu i, hv j]) q hq
    · exact hS q hq

end NormalizedFrames

section CoefficientAnchors

variable {M : Type*} [AddCommGroup M] [Module ℤ M] {n : ℕ}

noncomputable def anchorExpr (b : Module.Basis (Fin n) ℤ M) (x : M) : LinExpr :=
  List.ofFn fun i => (b.repr x i, frameIndex i)

theorem evalLinear_anchorExpr (b : Module.Basis (Fin n) ℤ M) (x : M)
    (a : ℕ → M) (ha : ∀ i : Fin n, a (frameIndex i) = b i) :
    evalLinear a (anchorExpr b x) = x := by
  unfold evalLinear anchorExpr
  rw [List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp_apply, ha]
  calc
    _ = ∑ i : Fin n, (inferInstance : Module ℤ M).smul (b.repr x i) (b i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (int_smul_eq_zsmul (inferInstance : Module ℤ M) _ _).symm
    _ = x := b.sum_repr x

def installColumns (b : Fin n → M) (x : ℕ → Fin n → M) (k : ℕ) : M :=
  if k % 2 = 0 then
    if h : k / 2 < n then b ⟨k / 2, h⟩ else 0
  else
    let z := Nat.unpair (k / 2)
    if h : z.2 < n then x z.1 ⟨z.2, h⟩ else 0

omit [Module ℤ M] in
@[simp] theorem installColumns_frame (b : Fin n → M) (x : ℕ → Fin n → M) (i : Fin n) :
    installColumns b x (frameIndex i) = b i := by
  have hm : (2 * i.val) % 2 = 0 := by omega
  have hd : (2 * i.val) / 2 = i.val := by omega
  simp [installColumns, frameIndex, hm, hd, i.isLt]

omit [Module ℤ M] in
@[simp] theorem installColumns_gate (b : Fin n → M) (x : ℕ → Fin n → M)
    (r : ℕ) (i : Fin n) :
    installColumns b x (gateIndex r i) = x r i := by
  have hd : (2 * Nat.pair r i.val + 1) / 2 = Nat.pair r i.val := by omega
  simp [installColumns, gateIndex, hd, i.isLt, Nat.unpair_pair]

end CoefficientAnchors

end ManinBilinear

namespace ManinBilinear

section Assembly

variable {U V : Type*} [AddCommGroup U] [AddCommGroup V]
  [Module ℤ U] [Module ℤ V] [Module.Finite ℤ U] [Module.Finite ℤ V]
  {p m n s d : ℕ}
  (B : U →ₗ[ℤ] V →ₗ[ℤ] (Fin p → ℤ))
  (e : Module.Basis (Fin m) ℤ U) (f : Module.Basis (Fin n) ℤ V)
  (g : Fin s → Adjoint B) (b : Module.Basis (Fin d) ℤ (Center B))

def equationGrid (F : Fin m → Fin n → RawEquation) : RawSystem :=
  (List.finRange m).flatMap fun i => (List.finRange n).map (F i)

private theorem allGrid {P : RawEquation → Prop} {F : Fin m → Fin n → RawEquation} :
    (∀ q ∈ equationGrid F, P q) ↔ ∀ i j, P (F i j) := by
  constructor
  · intro h i j
    exact h _ (List.mem_flatMap.mpr ⟨i, by simp, List.mem_map.mpr ⟨j, by simp, rfl⟩⟩)
  · intro h q hq
    obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hq
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi
    exact h i j

def gateRegisters : Gate κ → List ℕ
  | .inl (x,y,z) => [x,y,z]
  | .inr (.inl (x,y,z)) => [x,y,z]
  | .inr (.inr (x,_)) => [x]

noncomputable def centerConstraints (x : ℕ) : RawSystem :=
  equationGrid (fun (i : Fin m) (j : Fin n) => adjointEquation x i j) ++
  (List.finRange s).flatMap fun k => equationGrid fun i j =>
    pairEq (single (gateIndex x i)) (anchorExpr f (right (g k) (f j)))
      (anchorExpr e (left (g k) (e i))) (single (gateIndex x j))

noncomputable def gateConstraint (t : Gate (List ℤ)) (i : Fin m) (j : Fin n) : RawEquation :=
  match t with
  | .inl (x,y,z) => additionEquation x y z i j
  | .inr (.inl (x,y,z)) => multiplicationEquation x y z i j
  | .inr (.inr (x,c)) =>
      pairEq (single (gateIndex x i)) (single (frameIndex j))
        (anchorExpr e (left (basisDecode b c).val (e i))) (single (frameIndex j))

noncomputable def compileCenterSystem (gs : List (Gate (List ℤ))) : RawSystem :=
  frameEquations (fun i j => B (e i) (f j)) ++
    gs.flatMap fun t =>
      (gateRegisters t).flatMap (centerConstraints B e f g) ++
        equationGrid (gateConstraint (n := n) B e b t)

def matchesColumns (u : ℕ → U) (v : ℕ → V) (x : ℕ) (c : Center B) : Prop :=
  (∀ i : Fin m, left c.val (e i) = u (gateIndex x i)) ∧
  (∀ j : Fin n, right c.val (f j) = v (gateIndex x j))

theorem centerConstraints_iff (hl : ∀ u : U, (∀ v : V, B u v = 0) → u = 0)
    (hr : ∀ v : V, (∀ u : U, B u v = 0) → v = 0)
    (hg : Submodule.span ℤ (Set.range g) = ⊤) (u : ℕ → U) (v : ℕ → V)
    (hu : ∀ i : Fin m, u (frameIndex i) = e i)
    (hv : ∀ j : Fin n, v (frameIndex j) = f j) (x : ℕ) :
    (∀ q ∈ centerConstraints B e f g x, holdsEquation B u v q) ↔
      ∃ c : Center B, matchesColumns B e f u v x c := by
  let L : Module.End ℤ U :=
    (Finsupp.linearCombination ℤ fun i : Fin m => u (gateIndex x i)).comp e.repr.toLinearMap
  let R : Module.End ℤ V :=
    (Finsupp.linearCombination ℤ fun j : Fin n => v (gateIndex x j)).comp f.repr.toLinearMap
  have hL (i : Fin m) : L (e i) = u (gateIndex x i) := by
    simp only [L, LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.repr_self, Finsupp.linearCombination_single]
    exact (inferInstance : Module ℤ U).one_smul _
  have hR (j : Fin n) : R (f j) = v (gateIndex x j) := by
    simp only [R, LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.repr_self, Finsupp.linearCombination_single]
    exact (inferInstance : Module ℤ V).one_smul _
  have cEval (k : Fin s) (i : Fin m) (j : Fin n) :
      holdsEquation B u v
          (pairEq (single (gateIndex x i)) (anchorExpr f (right (g k) (f j)))
            (anchorExpr e (left (g k) (e i))) (single (gateIndex x j))) ↔
        B (u (gateIndex x i)) (right (g k) (f j)) =
          B (left (g k) (e i)) (v (gateIndex x j)) := by
    rw [holds_pairEq, evalLinear_anchorExpr f _ v hv, evalLinear_anchorExpr e _ u hu]
    simp [single, evalLinear]
  constructor
  · intro h
    have h₀ := allGrid.mp fun q hq => h q (List.mem_append_left _ hq)
    have hPair : IsAdjoint B (L, MulOpposite.op R) := by
      apply (isAdjoint_iff_basis e f _).mpr
      intro i j
      simpa [hL, hR, hu, hv] using (holds_adjointEquation B u v x i j).mp (h₀ i j)
    let a : Adjoint B := ⟨(L, MulOpposite.op R), hPair⟩
    have ha : a ∈ centerRing B := by
      apply (center_mem_iff_generator_equations e f hl hr g hg a).mpr
      intro k i j
      have h₁ := allGrid.mp fun q hq =>
        h q (List.mem_append_right _ (List.mem_flatMap.mpr ⟨k, by simp, hq⟩))
      simpa [a, left, right, hL, hR] using (cEval k i j).mp (h₁ i j)
    exact ⟨⟨a, ha⟩, hL, hR⟩
  · rintro ⟨c, hcl, hcr⟩ q hq
    rcases List.mem_append.mp hq with hq | hq
    · apply ((allGrid (P := holdsEquation B u v)).mpr ?_) q hq
      intro i j
      exact (holds_adjointEquation B u v x i j).mpr (by
        rw [hu, hv, ← hcl, ← hcr]
        exact adjoint_spec c.val (e i) (f j))
    · obtain ⟨k, _, hq⟩ := List.mem_flatMap.mp hq
      apply ((allGrid (P := holdsEquation B u v)).mpr ?_) q hq
      intro i j
      exact (cEval k i j).mpr (by
        rw [← hcl, ← hcr]
        exact (center_mem_iff_generator_equations e f hl hr g hg c.val).mp c.property k i j)

omit [Module.Finite ℤ U] [Module.Finite ℤ V] in
theorem gateConstraint_iff (hl : ∀ u : U, (∀ v : V, B u v = 0) → u = 0)
    (hr : ∀ v : V, (∀ u : U, B u v = 0) → v = 0)
    (u : ℕ → U) (v : ℕ → V)
    (hu : ∀ i : Fin m, u (frameIndex i) = e i)
    (hv : ∀ j : Fin n, v (frameIndex j) = f j)
    (z : ℕ → Center B) (t : Gate (List ℤ))
    (hz : ∀ x ∈ gateRegisters t, matchesColumns B e f u v x (z x)) :
    (∀ (i : Fin m) (j : Fin n), holdsEquation B u v (gateConstraint (n := n) B e b t i j)) ↔
      t.Holds (basisDecode b) z := by
  rcases t with ⟨x,y,w⟩ | ⟨x,y,w⟩ | ⟨x,c⟩
  · obtain ⟨hx,_⟩ := hz x (by simp [gateRegisters])
    obtain ⟨hy,_⟩ := hz y (by simp [gateRegisters])
    obtain ⟨hw,_⟩ := hz w (by simp [gateRegisters])
    change (∀ (i : Fin m) (j : Fin n), holdsEquation B u v (additionEquation x y w i j)) ↔ z x + z y = z w
    rw [center_add_eq_iff_basis e f hl hr]
    simp only [holds_additionEquation, hv, ← hx, ← hy, ← hw, map_add, LinearMap.add_apply]
  · obtain ⟨_,hx⟩ := hz x (by simp [gateRegisters])
    obtain ⟨hy,_⟩ := hz y (by simp [gateRegisters])
    obtain ⟨hw,_⟩ := hz w (by simp [gateRegisters])
    change (∀ (i : Fin m) (j : Fin n), holdsEquation B u v (multiplicationEquation x y w i j)) ↔ z x * z y = z w
    rw [center_mul_eq_iff_basis e f hl hr]
    simp only [holds_multiplicationEquation, hv, ← hx, ← hy, ← hw]
  · obtain ⟨hx,_⟩ := hz x (by simp [gateRegisters])
    change _ ↔ z x = basisDecode b c
    rw [center_eq_iff_basis e f hl hr]
    apply forall_congr'
    intro i
    apply forall_congr'
    intro j
    rw [gateConstraint, holds_pairEq, evalLinear_anchorExpr e _ u hu]
    simp [single, evalLinear, hv, ← hx]

theorem compileCenterSystem_correct (hleft : Function.Injective B)
    (hright : Function.Injective B.flip)
    (hg : Submodule.span ℤ (Set.range g) = ⊤) (gs : List (Gate (List ℤ))) :
    rawSat B (compileCenterSystem B e f g b gs) ↔ gateSat (basisDecode b) gs := by
  classical
  have hl (u : U) (h : ∀ v : V, B u v = 0) : u = 0 := by
    apply hleft
    ext v : 1
    simpa using h v
  have hr (v : V) (h : ∀ u : U, B u v = 0) : v = 0 := by
    apply hright
    ext u : 1
    simpa using h u
  unfold compileCenterSystem
  rw [rawSat_frameEquations_iff B e f hleft hright]
  constructor
  · rintro ⟨u,v,hu,hv,h⟩
    let z (x : ℕ) : Center B :=
      if q : ∃ c : Center B, matchesColumns B e f u v x c then Classical.choose q else 0
    refine ⟨z, fun t ht => ?_⟩
    have ht' q (hq : q ∈ (gateRegisters t).flatMap (centerConstraints B e f g) ++
        equationGrid (gateConstraint (n := n) B e b t)) := h q (List.mem_flatMap.mpr ⟨t,ht,hq⟩)
    have hmatch x (hx : x ∈ gateRegisters t) : matchesColumns B e f u v x (z x) := by
      have h₀ := (centerConstraints_iff B e f g hl hr hg u v hu hv x).mp
        (fun q hq => ht' q (List.mem_append_left _ (List.mem_flatMap.mpr ⟨x,hx,hq⟩)))
      unfold z
      rw [dif_pos h₀]
      exact Classical.choose_spec h₀
    apply (gateConstraint_iff B e f b hl hr u v hu hv z t hmatch).mp
    exact allGrid.mp (fun q hq => ht' q (List.mem_append_right _ hq))
  · rintro ⟨z,hz⟩
    let u := installColumns e (fun x i => left (z x).val (e i))
    let v := installColumns f (fun x j => right (z x).val (f j))
    have hu (i : Fin m) : u (frameIndex i) = e i := by simp [u]
    have hv (j : Fin n) : v (frameIndex j) = f j := by simp [v]
    have hm (x : ℕ) : matchesColumns B e f u v x (z x) := by
      constructor <;> intro i <;> simp [u,v]
    refine ⟨u,v,hu,hv,fun q hq => ?_⟩
    obtain ⟨t,ht,hq⟩ := List.mem_flatMap.mp hq
    rcases List.mem_append.mp hq with hq | hq
    · obtain ⟨x,_,hq⟩ := List.mem_flatMap.mp hq
      exact (centerConstraints_iff B e f g hl hr hg u v hu hv x).mpr ⟨z x,hm x⟩ q hq
    · apply (allGrid (P := holdsEquation B u v)).mpr ?_ q hq
      exact (gateConstraint_iff B e f b hl hr u v hu hv z t (fun x _ => hm x)).mpr (hz t ht)


end Assembly

end ManinBilinear

namespace ManinBilinear

section Effective

variable {A X Y : Type*} [Primcodable A] [Primcodable X]

private theorem pr_map_fixed (l : List Y) (f : Y → A → X)
    (hf : ∀ y, Primrec (f y)) : Primrec (fun a => l.map (fun y => f y a)) := by
  induction l with
  | nil => exact Primrec.const []
  | cons y l ih => exact Primrec.list_cons.comp (hf y) ih

private theorem pr_flatMap_fixed (l : List Y) (f : Y → A → List X)
    (hf : ∀ y, Primrec (f y)) : Primrec (fun a => l.flatMap (fun y => f y a)) := by
  induction l with
  | nil => exact Primrec.const []
  | cons y l ih => exact Primrec.list_append.comp (hf y) ih

private theorem pr_pairTerms (mul : Primrec₂ ((· * ·) : ℤ → ℤ → ℤ))
    {a b : A → LinExpr} (ha : Primrec a) (hb : Primrec b) :
    Primrec (fun x => pairTerms (a x) (b x)) := by
  unfold pairTerms
  apply Primrec.list_flatMap ha
  change Primrec (fun q : A × (ℤ × ℕ) =>
    (b q.1).map (fun c => (q.2.1 * c.1, q.2.2, c.2)))
  apply Primrec.list_map (hb.comp Primrec.fst)
  change Primrec (fun q : (A × (ℤ × ℕ)) × (ℤ × ℕ) =>
    (q.1.2.1 * q.2.1, q.1.2.2, q.2.2))
  exact (mul.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
    (Primrec.fst.comp Primrec.snd)).pair
    ((Primrec.snd.comp (Primrec.snd.comp Primrec.fst)).pair (Primrec.snd.comp Primrec.snd))

private theorem pr_negTerms (neg : Primrec (fun x : ℤ => -x)) {a : A → List RawTerm}
    (ha : Primrec a) : Primrec (fun x => negTerms (a x)) := by
  unfold negTerms
  apply Primrec.list_map ha
  exact ((neg.comp Primrec.fst).pair Primrec.snd).comp₂ Primrec₂.right

private theorem pr_pairEq (mul : Primrec₂ ((· * ·) : ℤ → ℤ → ℤ))
    (neg : Primrec (fun x : ℤ => -x)) {a b c d : A → LinExpr}
    (ha : Primrec a) (hb : Primrec b) (hc : Primrec c) (hd : Primrec d) :
    Primrec (fun x => pairEq (a x) (b x) (c x) (d x)) :=
  (Primrec.list_append.comp (pr_pairTerms mul ha hb)
    (pr_negTerms neg (pr_pairTerms mul hc hd))).pair (Primrec.const [])

private theorem pr_single {f : A → ℕ} (hf : Primrec f) :
    Primrec (fun x => single (f x)) :=
  Primrec.list_cons.comp ((Primrec.const (1 : ℤ)).pair hf) (Primrec.const [])

private theorem pr_gateIndex (i : ℕ) : Primrec (fun x => gateIndex x i) :=
  Primrec.nat_double_succ.comp (Primrec₂.natPair.comp Primrec.id (Primrec.const i))

private theorem pr_grid {m n : ℕ} {f : Fin m → Fin n → A → RawEquation}
    (hf : ∀ i j, Primrec (f i j)) :
    Primrec (fun a => equationGrid (fun i j => f i j a)) :=
  pr_flatMap_fixed (List.finRange m) _ fun i =>
    pr_map_fixed (List.finRange n) _ (hf i)

private theorem pr_sum {L R S : Type*} [Primcodable L] [Primcodable R] [Primcodable S]
    {f : L → S} {g : R → S} (hf : Primrec f) (hg : Primrec g) :
    Primrec (Sum.elim f g) :=
  (Primrec.sumCasesOn Primrec.id (hf.comp₂ Primrec₂.right)
    (hg.comp₂ Primrec₂.right)).of_eq (fun a => by cases a <;> rfl)

private theorem pr_ofFn {k : ℕ} {f : Fin k → A → X} (hf : ∀ i, Primrec (f i)) :
    Primrec (fun a => List.ofFn fun i => f i a) := by
  induction k with
  | zero => simpa using (Primrec.const ([] : List X) : Primrec (fun _ : A => []))
  | succ k ih =>
    simp only [List.ofFn_succ]
    exact Primrec.list_cons.comp (hf 0) (ih (fun i => hf i.succ))

private theorem pr_intFinSum (add : Primrec₂ ((· + ·) : ℤ → ℤ → ℤ))
    {k : ℕ} {f : Fin k → A → ℤ} (hf : ∀ i, Primrec (f i)) :
    Primrec (fun a => ∑ i, f i a) := by
  induction k with
  | zero => simpa using (Primrec.const (0 : ℤ) : Primrec (fun _ : A => (0 : ℤ)))
  | succ k ih =>
    simp only [Fin.sum_univ_succ]
    exact add.comp (hf 0) (ih (fun i => hf i.succ))

private theorem pr_anchorDecode
    (add : Primrec₂ ((· + ·) : ℤ → ℤ → ℤ))
    (mul : Primrec₂ ((· * ·) : ℤ → ℤ → ℤ))
    {U V : Type*} [AddCommGroup U] [AddCommGroup V] [Module ℤ U] [Module ℤ V]
    {p m d : ℕ} (B : U →ₗ[ℤ] V →ₗ[ℤ] (Fin p → ℤ))
    (e : Module.Basis (Fin m) ℤ U) (b : Module.Basis (Fin d) ℤ (Center B)) (i : Fin m) :
    Primrec (fun c => anchorExpr e (left (basisDecode b c).val (e i))) := by
  unfold anchorExpr
  apply pr_ofFn
  intro j
  apply Primrec.pair _ (Primrec.const _)
  let coord : Center B →+ ℤ :=
    { toFun := fun x => e.repr (left x.val (e i)) j
      map_zero' := by simp [left]
      map_add' := fun x y => by simp [left_add, LinearMap.add_apply, Finsupp.add_apply] }
  have h (c : List ℤ) :
      coord (basisDecode b c) = ∑ k : Fin d, c[k.val]?.getD 0 * coord (b k) := by
    unfold basisDecode
    simp only [map_sum, map_zsmul, Int.zsmul_eq_mul]
  apply Primrec.of_eq (pr_intFinSum add (f := fun k c => c[k.val]?.getD 0 * coord (b k)) ?_)
  · intro c
    exact (h c).symm
  · intro k
    exact mul.comp ((Primrec.list_getD (0 : ℤ)).comp Primrec.id (Primrec.const k.val))
      (Primrec.const (coord (b k)))

private theorem pr_addEquation {x y z : A → ℕ} (hx : Primrec x) (hy : Primrec y)
    (hz : Primrec z) (i j : ℕ) :
    Primrec (fun a => additionEquation (x a) (y a) (z a) i j) := by
  refine (Primrec.list_cons.comp ?_ (Primrec.list_cons.comp ?_
    (Primrec.list_cons.comp ?_ (Primrec.const [])))).pair (Primrec.const [])
  · exact (Primrec.const (1 : ℤ)).pair (((pr_gateIndex i).comp hx).pair (Primrec.const (frameIndex j)))
  · exact (Primrec.const (1 : ℤ)).pair (((pr_gateIndex i).comp hy).pair (Primrec.const (frameIndex j)))
  · exact (Primrec.const (-1 : ℤ)).pair (((pr_gateIndex i).comp hz).pair (Primrec.const (frameIndex j)))

theorem compileCenterSystem_primrec_of_int
    (add : Primrec₂ ((· + ·) : ℤ → ℤ → ℤ))
    (mul : Primrec₂ ((· * ·) : ℤ → ℤ → ℤ))
    (neg : Primrec (fun x : ℤ => -x))
    {U V : Type*} [AddCommGroup U] [AddCommGroup V] [Module ℤ U] [Module ℤ V]
    {p m n s d : ℕ} (B : U →ₗ[ℤ] V →ₗ[ℤ] (Fin p → ℤ))
    (e : Module.Basis (Fin m) ℤ U) (f : Module.Basis (Fin n) ℤ V)
    (g : Fin s → Adjoint B) (b : Module.Basis (Fin d) ℤ (Center B)) :
    Primrec (compileCenterSystem B e f g b) := by
  have sanity : Primrec (centerConstraints B e f g) := by
    unfold centerConstraints
    apply Primrec.list_append.comp
    · apply pr_grid
      intro i j
      exact pr_pairEq mul neg (pr_single (pr_gateIndex i)) (Primrec.const _)
        (Primrec.const _) (pr_single (pr_gateIndex j))
    · apply pr_flatMap_fixed
      intro k
      apply pr_grid
      intro i j
      exact pr_pairEq mul neg (pr_single (pr_gateIndex i)) (Primrec.const _)
        (Primrec.const _) (pr_single (pr_gateIndex j))
  have regs : Primrec (gateRegisters (κ := List ℤ)) := by
    have three : Primrec (fun t : ℕ × ℕ × ℕ => [t.1,t.2.1,t.2.2]) :=
      Primrec.list_cons.comp Primrec.fst (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.list_cons.comp (Primrec.snd.comp Primrec.snd) (Primrec.const [])))
    have one : Primrec (fun t : ℕ × List ℤ => [t.1]) :=
      Primrec.list_cons.comp Primrec.fst (Primrec.const [])
    exact (pr_sum three (pr_sum three one)).of_eq (fun t => by
      rcases t with ⟨x,y,z⟩ | ⟨x,y,z⟩ | ⟨x,c⟩ <;> rfl)
  have gate (i : Fin m) (j : Fin n) : Primrec (fun t => gateConstraint B e b t i j) := by
    have hAdd : Primrec (fun t : ℕ × ℕ × ℕ => additionEquation t.1 t.2.1 t.2.2 i j) :=
      pr_addEquation Primrec.fst (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd) i j
    have hMul : Primrec (fun t : ℕ × ℕ × ℕ => multiplicationEquation t.1 t.2.1 t.2.2 i j) :=
      pr_pairEq mul neg
        (pr_single ((pr_gateIndex i).comp (Primrec.fst.comp Primrec.snd)))
        (pr_single ((pr_gateIndex j).comp Primrec.fst))
        (pr_single ((pr_gateIndex i).comp (Primrec.snd.comp Primrec.snd)))
        (Primrec.const _)
    have hConst : Primrec (fun t : ℕ × List ℤ =>
      pairEq (single (gateIndex t.1 i)) (single (frameIndex j))
        (anchorExpr e (left (basisDecode b t.2).val (e i))) (single (frameIndex j))) :=
      pr_pairEq mul neg (pr_single ((pr_gateIndex i).comp Primrec.fst))
        (Primrec.const _) ((pr_anchorDecode add mul B e b i).comp Primrec.snd) (Primrec.const _)
    exact (pr_sum hAdd (pr_sum hMul hConst)).of_eq (fun t => by
      rcases t with ⟨x,y,z⟩ | ⟨x,y,z⟩ | ⟨x,c⟩ <;> rfl)

  unfold compileCenterSystem
  refine Primrec.list_append.comp (Primrec.const _) (Primrec.list_flatMap Primrec.id ?_)
  apply (Primrec.list_append.comp (Primrec.list_flatMap regs (sanity.comp₂ Primrec₂.right))
    (pr_grid gate)).comp₂ Primrec₂.right


end Effective

end ManinBilinear

/-
Int encodings below are adapted from Ripple.BoundedUniversality.BGP.IntComputable,
https://github.com/zinan-huang/Ripple at e9ce148d3975f9e75bb9724e01ec763ad9b368a9.
Original copyright holders and Apache-2.0 license apply.
Adaptation replaces the heavy Ripple import with Mathlib and reuses its canonical
integer encoding instance.
-/

noncomputable section IntComputablePort

namespace Ripple.BoundedUniversality.BGP

-- Mathlib supplies this Primcodable instance via Denumerable.

@[simp] lemma int_ofNat_even_code (m : ℕ) :
    Denumerable.ofNat ℤ (2 * m) = (m : ℤ) := by
  rw [show Denumerable.ofNat ℤ (2 * m) = Equiv.intEquivNat.symm (2 * m) from rfl]
  simp [Equiv.intEquivNat, Equiv.intEquivNatSumNat,
    Equiv.natSumNatEquivNat_symm_apply, Nat.div2_bit0]

@[simp] lemma int_ofNat_odd_code (m : ℕ) :
    Denumerable.ofNat ℤ (2 * m + 1) = Int.negSucc m := by
  rw [show Denumerable.ofNat ℤ (2 * m + 1) =
    Equiv.intEquivNat.symm (2 * m + 1) from rfl]
  simp [Equiv.intEquivNat, Equiv.intEquivNatSumNat,
    Equiv.natSumNatEquivNat_symm_apply]

-- 4.30: downstream goals surface the decode in the defeq `Equiv.intEquivNat.symm` form
-- (not the `Denumerable.ofNat ℤ` form), so the two lemmas above no longer fire as `simp`.
-- These `Equiv.intEquivNat.symm`-form mirrors restore the rewrites.
@[simp] lemma intEquivNat_symm_two_mul (m : ℕ) :
    Equiv.intEquivNat.symm (2 * m) = (m : ℤ) := int_ofNat_even_code m

@[simp] lemma intEquivNat_symm_two_mul_add_one (m : ℕ) :
    Equiv.intEquivNat.symm (2 * m + 1) = Int.negSucc m := int_ofNat_odd_code m

@[simp] lemma int_encode_natCast (m : ℕ) :
    Encodable.encode (m : ℤ) = 2 * m := rfl

@[simp] lemma int_encode_negSucc (m : ℕ) :
    Encodable.encode (Int.negSucc m) = 2 * m + 1 := rfl

theorem primrec_int_natAbs : Primrec (fun z : ℤ => z.natAbs) := by
  rw [Primrec.ofNat_iff]
  refine (Primrec.cond Primrec.nat_bodd
    (Primrec.succ.comp Primrec.nat_div2) Primrec.nat_div2).of_eq ?_
  intro n
  have hn := (Nat.bit_bodd_div2 n).symm
  cases hb : n.bodd
  · rw [hn, hb]
    simp [Nat.bit, Nat.div2_bit0]
  · rw [hn, hb]
    simp [Nat.bit]

theorem primrec_int_ofNat : Primrec (fun n : ℕ => (n : ℤ)) := by
  rw [← Primrec.encode_iff]
  simpa using Primrec.nat_double

theorem computable_int_natAbs : Computable (fun z : ℤ => z.natAbs) :=
  primrec_int_natAbs.to_comp

theorem computable_int_ofNat : Computable (fun n : ℕ => (n : ℤ)) :=
  primrec_int_ofNat.to_comp

private def intAddCode (m n : ℕ) : ℕ :=
  let a := m.div2
  let b := n.div2
  if m.bodd then
    if n.bodd then
      2 * (a + b + 1) + 1
    else if a < b then
      2 * (b - a - 1)
    else
      2 * (a - b) + 1
  else
    if n.bodd then
      if b < a then
        2 * (a - b - 1)
      else
        2 * (b - a) + 1
    else
      2 * (a + b)

private def intMulCode (m n : ℕ) : ℕ :=
  let a := if m.bodd then m.div2 + 1 else m.div2
  let b := if n.bodd then n.div2 + 1 else n.div2
  let mag := a * b
  if m.bodd = n.bodd then
    2 * mag
  else if mag = 0 then
    0
  else
    2 * (mag - 1) + 1

private theorem primrec2_intAddCode : Primrec₂ intAddCode := by
  unfold intAddCode
  let a : ℕ → ℕ → ℕ := fun m _ => m.div2
  let b : ℕ → ℕ → ℕ := fun _ n => n.div2
  have ha : Primrec₂ a := Primrec.nat_div2.comp₂ Primrec₂.left
  have hb : Primrec₂ b := Primrec.nat_div2.comp₂ Primrec₂.right
  have hma : Primrec₂ (fun m n => a m n + b m n) := Primrec.nat_add.comp₂ ha hb
  have hsameEven : Primrec₂ (fun m n => 2 * (a m n + b m n)) :=
    Primrec.nat_double.comp₂ hma
  have hsameOdd : Primrec₂ (fun m n => 2 * (a m n + b m n + 1) + 1) :=
    Primrec.nat_double_succ.comp₂ (Primrec.succ.comp₂ hma)
  have hba : Primrec₂ (fun m n => b m n - a m n) := Primrec.nat_sub.comp₂ hb ha
  have hab : Primrec₂ (fun m n => a m n - b m n) := Primrec.nat_sub.comp₂ ha hb
  have hbaPred : Primrec₂ (fun m n => b m n - a m n - 1) :=
    Primrec.nat_sub.comp₂ hba (Primrec₂.const 1)
  have habPred : Primrec₂ (fun m n => a m n - b m n - 1) :=
    Primrec.nat_sub.comp₂ hab (Primrec₂.const 1)
  have hEvenOddLt : Primrec₂ (fun m n => 2 * (a m n - b m n - 1)) :=
    Primrec.nat_double.comp₂ habPred
  have hEvenOddGe : Primrec₂ (fun m n => 2 * (b m n - a m n) + 1) :=
    Primrec.nat_double_succ.comp₂ hba
  have hOddEvenLt : Primrec₂ (fun m n => 2 * (b m n - a m n - 1)) :=
    Primrec.nat_double.comp₂ hbaPred
  have hOddEvenGe : Primrec₂ (fun m n => 2 * (a m n - b m n) + 1) :=
    Primrec.nat_double_succ.comp₂ hab
  have hmOdd : Primrec₂ (fun m _ : ℕ => m.bodd) :=
    Primrec.nat_bodd.comp₂ Primrec₂.left
  have hnOdd : Primrec₂ (fun _ n : ℕ => n.bodd) :=
    Primrec.nat_bodd.comp₂ Primrec₂.right
  have hblta : PrimrecPred (fun p : ℕ × ℕ => b p.1 p.2 < a p.1 p.2) :=
    Primrec.nat_lt.comp hb ha
  have haltb : PrimrecPred (fun p : ℕ × ℕ => a p.1 p.2 < b p.1 p.2) :=
    Primrec.nat_lt.comp ha hb
  have hEvenOdd : Primrec₂
      (fun m n => if b m n < a m n then
        2 * (a m n - b m n - 1) else 2 * (b m n - a m n) + 1) :=
    Primrec.ite hblta hEvenOddLt hEvenOddGe
  have hOddEven : Primrec₂
      (fun m n => if a m n < b m n then
        2 * (b m n - a m n - 1) else 2 * (a m n - b m n) + 1) :=
    Primrec.ite haltb hOddEvenLt hOddEvenGe
  have hOdd : Primrec₂
      (fun m n => if n.bodd then
        2 * (a m n + b m n + 1) + 1
      else if a m n < b m n then
        2 * (b m n - a m n - 1)
      else
        2 * (a m n - b m n) + 1) :=
    (Primrec.cond hnOdd hsameOdd hOddEven).of_eq fun p => by
      cases p
      simp
  have hEven : Primrec₂
      (fun m n => if n.bodd then
        (if b m n < a m n then
          2 * (a m n - b m n - 1)
        else
          2 * (b m n - a m n) + 1)
      else
        2 * (a m n + b m n)) :=
    (Primrec.cond hnOdd hEvenOdd hsameEven).of_eq fun p => by
      cases p
      simp
  exact (Primrec.cond hmOdd hOdd hEven).of_eq fun p => by
    cases p
    simp [a, b]

private theorem primrec2_intMulCode : Primrec₂ intMulCode := by
  unfold intMulCode
  let a : ℕ → ℕ → ℕ := fun m _ => if m.bodd then m.div2 + 1 else m.div2
  let b : ℕ → ℕ → ℕ := fun _ n => if n.bodd then n.div2 + 1 else n.div2
  have hmOdd : Primrec₂ (fun m _ : ℕ => m.bodd) :=
    Primrec.nat_bodd.comp₂ Primrec₂.left
  have hnOdd : Primrec₂ (fun _ n : ℕ => n.bodd) :=
    Primrec.nat_bodd.comp₂ Primrec₂.right
  have ha : Primrec₂ a :=
    (Primrec.cond hmOdd
      (Primrec.succ.comp₂ (Primrec.nat_div2.comp₂ Primrec₂.left))
      (Primrec.nat_div2.comp₂ Primrec₂.left)).of_eq fun p => by
        cases p
        simp [a]
  have hb : Primrec₂ b :=
    (Primrec.cond hnOdd
      (Primrec.succ.comp₂ (Primrec.nat_div2.comp₂ Primrec₂.right))
      (Primrec.nat_div2.comp₂ Primrec₂.right)).of_eq fun p => by
        cases p
        simp [b]
  let mag : ℕ → ℕ → ℕ := fun m n => a m n * b m n
  have hmag : Primrec₂ mag := Primrec.nat_mul.comp₂ ha hb
  have hsame : Primrec₂ (fun m n => 2 * mag m n) :=
    Primrec.nat_double.comp₂ hmag
  have hzero : PrimrecPred (fun p : ℕ × ℕ => mag p.1 p.2 = 0) :=
    Primrec.eq.comp hmag (Primrec.const 0)
  have hdiffNeg : Primrec₂ (fun m n => if mag m n = 0 then 0 else 2 * (mag m n - 1) + 1) :=
    Primrec.ite hzero (Primrec₂.const 0)
      (Primrec.nat_double_succ.comp₂
        (Primrec.nat_sub.comp₂ hmag (Primrec₂.const 1)))
  have hsameParity : PrimrecPred (fun p : ℕ × ℕ => p.1.bodd = p.2.bodd) :=
    Primrec.eq.comp hmOdd hnOdd
  exact Primrec.ite hsameParity hsame hdiffNeg

private lemma encode_add_even_even (a b : ℕ) :
    Encodable.encode ((a : ℤ) + (b : ℤ)) = 2 * (a + b) := by
  rw [Int.ofNat_add_ofNat, int_encode_natCast]

private lemma encode_add_even_odd_pos (a b : ℕ) (h : b < a) :
    Encodable.encode ((a : ℤ) + Int.negSucc b) = 2 * (a - b - 1) := by
  change Encodable.encode (Int.ofNat a + Int.negSucc b) = 2 * (a - b - 1)
  rw [Int.ofNat_add_negSucc_of_ge (by omega : b.succ ≤ a)]
  have hsub : a - b.succ = a - b - 1 := by omega
  rw [hsub]
  change Encodable.encode (((a - b - 1 : ℕ) : ℤ)) = 2 * (a - b - 1)
  rw [int_encode_natCast]

private lemma encode_add_even_odd_neg (a b : ℕ) (h : ¬ b < a) :
    Encodable.encode ((a : ℤ) + Int.negSucc b) = 2 * (b - a) + 1 := by
  rw [Int.ofNat_add_negSucc, Int.subNatNat_of_lt (by omega : a < b.succ)]
  have hpred : (b.succ - a).pred = b - a := by
    rw [Nat.pred_eq_sub_one]
    omega
  rw [hpred, int_encode_negSucc]

private lemma encode_add_odd_even_pos (a b : ℕ) (h : a < b) :
    Encodable.encode (Int.negSucc a + (b : ℤ)) = 2 * (b - a - 1) := by
  rw [Int.negSucc_add_ofNat, Int.subNatNat_eq_coe]
  have hEq : Int.ofNat b - Int.ofNat a.succ = Int.ofNat (b - a - 1) := by
    change ((b : ℤ) - (a.succ : ℤ)) = ((b - a - 1 : ℕ) : ℤ)
    rw [← Int.natCast_sub (by omega : a.succ ≤ b)]
    have hn : b - a.succ = b - a - 1 := by omega
    rw [hn]
  change Encodable.encode (Int.ofNat b - Int.ofNat a.succ) = 2 * (b - a - 1)
  rw [hEq]
  change Encodable.encode (((b - a - 1 : ℕ) : ℤ)) = 2 * (b - a - 1)
  rw [int_encode_natCast]

private lemma encode_add_odd_even_neg (a b : ℕ) (h : ¬ a < b) :
    Encodable.encode (Int.negSucc a + (b : ℤ)) = 2 * (a - b) + 1 := by
  rw [Int.negSucc_add_ofNat, Int.subNatNat_of_lt (by omega : b < a.succ)]
  have hpred : (a.succ - b).pred = a - b := by
    rw [Nat.pred_eq_sub_one]
    omega
  rw [hpred, int_encode_negSucc]

private lemma encode_add_odd_odd (a b : ℕ) :
    Encodable.encode (Int.negSucc a + Int.negSucc b) = 2 * (a + b + 1) + 1 := by
  rw [Int.negSucc_add_negSucc, int_encode_negSucc]

private lemma negSucc_pred_eq_neg_cast (p : ℕ) (hp : p ≠ 0) :
    Int.negSucc (p - 1) = -(p : ℤ) := by
  rw [Int.negSucc_eq, ← Int.natCast_succ]
  rw [Nat.succ_eq_add_one, Nat.sub_one_add_one hp]

private lemma encode_mul_even_even (a b : ℕ) :
    Encodable.encode ((a : ℤ) * (b : ℤ)) = 2 * (a * b) := by
  rw [Int.ofNat_mul_ofNat, int_encode_natCast]

private lemma encode_mul_even_odd_zero (a b : ℕ) (h : a * (b + 1) = 0) :
    Encodable.encode ((a : ℤ) * Int.negSucc b) = 0 := by
  rw [Int.ofNat_mul_negSucc, h]
  rfl

private lemma encode_mul_even_odd_neg (a b : ℕ) (h : a * (b + 1) ≠ 0) :
    Encodable.encode ((a : ℤ) * Int.negSucc b) =
      2 * (a * (b + 1) - 1) + 1 := by
  rw [Int.ofNat_mul_negSucc]
  have hneg := negSucc_pred_eq_neg_cast (a * (b + 1)) h
  rw [← hneg, int_encode_negSucc]

private lemma encode_mul_odd_even_zero (a b : ℕ) (h : (a + 1) * b = 0) :
    Encodable.encode (Int.negSucc a * (b : ℤ)) = 0 := by
  rw [Int.negSucc_mul_ofNat]
  change Encodable.encode (-(((a + 1) * b : ℕ) : ℤ)) = 0
  rw [h]
  rfl

private lemma encode_mul_odd_even_neg (a b : ℕ) (h : (a + 1) * b ≠ 0) :
    Encodable.encode (Int.negSucc a * (b : ℤ)) =
      2 * ((a + 1) * b - 1) + 1 := by
  rw [Int.negSucc_mul_ofNat]
  change Encodable.encode (-(((a + 1) * b : ℕ) : ℤ)) =
    2 * ((a + 1) * b - 1) + 1
  have hneg := negSucc_pred_eq_neg_cast ((a + 1) * b) h
  rw [← hneg, int_encode_negSucc]

private lemma encode_mul_odd_odd (a b : ℕ) :
    Encodable.encode (Int.negSucc a * Int.negSucc b) =
      2 * ((a + 1) * (b + 1)) := by
  rw [Int.negSucc_mul_negSucc]
  change Encodable.encode ((((a.succ * b.succ : ℕ) : ℤ))) =
    2 * ((a + 1) * (b + 1))
  rw [int_encode_natCast]

private lemma intAddCode_spec (m n : ℕ) :
    intAddCode m n =
      Encodable.encode (Denumerable.ofNat ℤ m + Denumerable.ofNat ℤ n) := by
  have hm := (Nat.bit_bodd_div2 m).symm
  have hn := (Nat.bit_bodd_div2 n).symm
  rcases hboddm : m.bodd with _ | _
  · rcases hboddn : n.bodd with _ | _
    · rw [hm, hn, hboddm, hboddn]
      simp [intAddCode, Nat.bit, Nat.div2_bit0, encode_add_even_even]
    · rw [hm, hn, hboddm, hboddn]
      by_cases h : n.div2 < m.div2
      · simp [intAddCode, h, Nat.bit, Nat.div2_bit0, encode_add_even_odd_pos _ _ h]
      · simp [intAddCode, h, Nat.bit, Nat.div2_bit0, encode_add_even_odd_neg _ _ h]
  · rcases hboddn : n.bodd with _ | _
    · rw [hm, hn, hboddm, hboddn]
      by_cases h : m.div2 < n.div2
      · simp [intAddCode, h, Nat.bit, Nat.div2_bit0, encode_add_odd_even_pos _ _ h]
      · simp [intAddCode, h, Nat.bit, Nat.div2_bit0, encode_add_odd_even_neg _ _ h]
    · rw [hm, hn, hboddm, hboddn]
      simp [intAddCode, Nat.bit, encode_add_odd_odd]

private lemma intMulCode_spec (m n : ℕ) :
    intMulCode m n =
      Encodable.encode (Denumerable.ofNat ℤ m * Denumerable.ofNat ℤ n) := by
  have hm := (Nat.bit_bodd_div2 m).symm
  have hn := (Nat.bit_bodd_div2 n).symm
  rcases hboddm : m.bodd with _ | _
  · rcases hboddn : n.bodd with _ | _
    · rw [hm, hn, hboddm, hboddn]
      simp [intMulCode, Nat.bit, Nat.div2_bit0, encode_mul_even_even]
    · rw [hm, hn, hboddm, hboddn]
      by_cases hzero : m.div2 * (n.div2 + 1) = 0
      · simp [intMulCode, hzero, Nat.bit, Nat.div2_bit0,
          encode_mul_even_odd_zero _ _ hzero]
      · simp [intMulCode, hzero, Nat.bit, Nat.div2_bit0,
          encode_mul_even_odd_neg _ _ hzero]
  · rcases hboddn : n.bodd with _ | _
    · rw [hm, hn, hboddm, hboddn]
      by_cases hzero : (m.div2 + 1) * n.div2 = 0
      · simp [intMulCode, hzero, Nat.bit, Nat.div2_bit0,
          encode_mul_odd_even_zero _ _ hzero]
      · simp [intMulCode, hzero, Nat.bit, Nat.div2_bit0,
          encode_mul_odd_even_neg _ _ hzero]
    · rw [hm, hn, hboddm, hboddn]
      simp [intMulCode, Nat.bit, encode_mul_odd_odd]

theorem primrec2_int_add : Primrec₂ ((· + ·) : ℤ → ℤ → ℤ) := by
  rw [Primrec₂.ofNat_iff, ← Primrec₂.encode_iff]
  exact primrec2_intAddCode.of_eq intAddCode_spec

theorem primrec2_int_mul : Primrec₂ ((· * ·) : ℤ → ℤ → ℤ) := by
  rw [Primrec₂.ofNat_iff, ← Primrec₂.encode_iff]
  exact primrec2_intMulCode.of_eq intMulCode_spec

theorem computable2_int_add : Computable₂ ((· + ·) : ℤ → ℤ → ℤ) :=
  primrec2_int_add.to_comp

theorem computable2_int_mul : Computable₂ ((· * ·) : ℤ → ℤ → ℤ) :=
  primrec2_int_mul.to_comp

end Ripple.BoundedUniversality.BGP
end IntComputablePort

namespace ManinBilinear

/-- Manin's integral conjecture follows from the finite-free case of the
Koymans–Pagano arithmetic theorem. The arithmetic input is explicit. -/
theorem manin_bilinear_of_koymans_pagano {m n p : ℕ}
    (B : (Fin m → ℤ) →ₗ[ℤ] (Fin n → ℤ) →ₗ[ℤ] (Fin p → ℤ)) (hB : B ≠ 0)
    (hKP : KoymansPaganoFiniteFree) :
    ¬ ComputablePred (rawSat B) := by
  apply rawSat_reduced_undecidable B
  let C := reduced B
  let (e, f) := reducedBasis B
  have hright (v : RightReduced B) (hv : ∀ u : LeftReduced B, C u v = 0) : v = 0 := by
    have he : (reduced B).flip v = (reduced B).flip 0 :=
      LinearMap.ext (fun u => by simpa [C] using hv u)
    exact reduced_right_injective B he
  obtain ⟨s, g, hg⟩ := adjointGenerators (β := C)
  let b := centerBasis (β := C) hright
  let : Nontrivial (LeftReduced B) := leftReduced_nontrivial B hB
  let : CharZero (Center C) := centerCharZero (β := C)
  let : Nontrivial (Center C) := by
    refine ⟨⟨(0 : Center C), 1, ?_⟩⟩
    intro h
    exact Nat.zero_ne_one (Nat.cast_injective (R := Center C) (by simp [h]))
  have hneg : Primrec (fun x : ℤ => -x) :=
    (Ripple.BoundedUniversality.BGP.primrec2_int_mul.comp
      (Primrec.const (-1 : ℤ)) Primrec.id).of_eq (fun x => by simp)
  have hcomp := (compileCenterSystem_primrec_of_int
    Ripple.BoundedUniversality.BGP.primrec2_int_add
    Ripple.BoundedUniversality.BGP.primrec2_int_mul hneg C e.2 f.2 g b.2).to_comp
  intro h
  apply hKP (Center C) b.1 b.2
  exact computablePred_pullback hcomp
    (fun gs => (compileCenterSystem_correct C e.2 f.2 g b.2
      (reduced_left_injective B) (reduced_right_injective B) hg gs).symm) h

end ManinBilinear

end BilinearReduction

section IntegerDPRM

/-
Adapted from Cameron Freer, Hilbert10 v2.3.0, revision
082fc231a330aa44958d7f6ecf384c8971263d84.
https://github.com/cameronfreer/hilbert10

Apache-2.0. Original module notices are retained below.
The dependency closure is combined into one source. A search lemma uses
the current spelling of Nat.mem_rfind, and one private lemma was renamed
to distinguish it from an identically named lemma in another module.
-/



/- Source: Hilbert10.Computability, Hilbert10 v2.3.0, Apache-2.0. -/
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# Computability closure used before DPRM

Generic facts about recursively enumerable predicates that this development needs *below* the
DPRM theorem. Nothing here mentions `Dioph`, and nothing here may depend on `REPred.dioph`.

## Why this is its own module

The import direction is the point:

```
Computability  →  DPRM  →  DerivedDioph  →  endpoints and examples
```

`REPred.of_manyOneReducible` is pure computability theory: it is proved from `Partrec.comp`
and may be used anywhere, the DPRM proof included. What must *not* be used inside DPRM is its
Diophantine shadow, `Dioph.of_manyOneReducible`, since that goes through DPRM itself. Placing this
module below `DPRM` and the shadow in `DerivedDioph` above it makes the two directions visible in
the import graph rather than in a comment: the pre-DPRM closure sits here, the post-DPRM
consequences there.

Its consumers are the integer formulation (`rePred_intSolvable`) and that derived layer.

## Main results

* `Hilbert10.REPred.of_manyOneReducible`
-/

namespace Hilbert10

/-- **Recursive enumerability transfers backwards along a many-one reduction.** -/
theorem REPred.of_manyOneReducible {α β : Type*} [Primcodable α] [Primcodable β] {p : α → Prop}
    {q : β → Prop} (h : p ≤₀ q) (hq : REPred q) : REPred p := by
  obtain ⟨f, hf, hfp⟩ := h
  refine (Partrec.comp hq hf).of_eq fun a => ?_
  rw [propext (hfp a)]

end Hilbert10


/- Source: Hilbert10.Internal.RegisterMachine, Hilbert10 v2.3.0, Apache-2.0. -/
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# Register machines

Issue #19: the smallest machine model that can be arithmetised. A program is a list of
instructions over `Fin k` registers; a configuration is a program counter together with a
register file.

Mathlib has no register, Minsky or FRACTRAN machine at the pinned revision — `TMToPartrec` and
the `Turing.TM*` files are tape-flavoured, which is the wrong shape here. The point of this
model is that a configuration is a *number*, and tapes are not.

## Design

Three decisions, each made to keep #20 and #21 cheap, since every feature here is paid for twice.

**No `halt` instruction.** A configuration is halted exactly when its program counter is out of
range. This makes list concatenation the sequential-composition operator: a machine "exits" by
jumping to `P.length`, and in `P ++ Q` that same jump is `Q`'s entry point. An explicit `halt`
would need a separate rule for what concatenation does to it.

**Every instruction carries its jump targets**, including `inc`, which could have fallen through
to `pc + 1`. Uniform shape means relocating a program is a single map over targets rather than a
case split, which is what #39 consumes.

**No configuration encoding here.** The acceptance criteria originally asked for the encoded
configuration and its step lemma; that obligation now lives in #45, where the base and guard-bit
width are chosen together with the run packing they have to fit.

## Main definitions

* `RegisterMachine.Instr`, `Program`, `Config`
* `RegisterMachine.step`, `run`, `Halted`, `Halts`
-/

namespace Hilbert10

namespace RegisterMachine

variable {k : ℕ}

/-- An instruction over `k` registers.

`inc r j` increments register `r` and jumps to `j`. `dec r jpos jzero` jumps to `jzero` leaving
the registers alone if register `r` is zero, and otherwise decrements it and jumps to `jpos`. -/
inductive Instr (k : ℕ) where
  | inc (r : Fin k) (j : ℕ)
  | dec (r : Fin k) (jpos jzero : ℕ)
  deriving DecidableEq, Repr

/-- A program is a list of instructions; the program counter indexes into it. -/
abbrev Program (k : ℕ) := List (Instr k)

/-- A configuration: a program counter and a register file. -/
structure Config (k : ℕ) where
  /-- The program counter. Out of range means halted. -/
  pc : ℕ
  /-- The contents of the registers. -/
  regs : Fin k → ℕ

/-- The configuration reached by executing `i` on the register file `regs`. -/
def Instr.exec (i : Instr k) (regs : Fin k → ℕ) : Config k :=
  match i with
  | .inc r j => ⟨j, Function.update regs r (regs r + 1)⟩
  | .dec r jpos jzero =>
      if regs r = 0 then ⟨jzero, regs⟩ else ⟨jpos, Function.update regs r (regs r - 1)⟩

/-- One step of `P`. A configuration whose program counter is out of range steps to itself. -/
def step (P : Program k) (c : Config k) : Config k :=
  match P[c.pc]? with
  | none => c
  | some i => i.exec c.regs

/-- `c` is halted for `P` when its program counter is out of range. -/
def Halted (P : Program k) (c : Config k) : Prop := P.length ≤ c.pc

instance (P : Program k) (c : Config k) : Decidable (Halted P c) := Nat.decLe _ _

theorem halted_iff_getElem?_eq_none {P : Program k} {c : Config k} :
    Halted P c ↔ P[c.pc]? = none :=
  List.getElem?_eq_none_iff.symm

@[simp] theorem step_of_halted {P : Program k} {c : Config k} (h : Halted P c) : step P c = c := by
  simp [step, halted_iff_getElem?_eq_none.mp h]

theorem step_of_getElem? {P : Program k} {c : Config k} {i : Instr k} (h : P[c.pc]? = some i) :
    step P c = i.exec c.regs := by
  simp [step, h]

/-- `run P c n` is the configuration after `n` steps of `P` from `c`. -/
def run (P : Program k) (c : Config k) (n : ℕ) : Config k := (step P)^[n] c

@[simp] theorem run_zero (P : Program k) (c : Config k) : run P c 0 = c := rfl

theorem run_succ (P : Program k) (c : Config k) (n : ℕ) :
    run P c (n + 1) = step P (run P c n) :=
  Function.iterate_succ_apply' _ _ _

theorem run_succ' (P : Program k) (c : Config k) (n : ℕ) :
    run P c (n + 1) = run P (step P c) n :=
  Function.iterate_succ_apply _ _ _

theorem run_add (P : Program k) (c : Config k) (m n : ℕ) :
    run P c (m + n) = run P (run P c m) n := by
  simp [run, Nat.add_comm m n, Function.iterate_add_apply]

/-- Halting is stable: once out of range, the program counter stays out of range. -/
theorem run_of_halted {P : Program k} {c : Config k} {n : ℕ} (h : Halted P (run P c n)) (m : ℕ) :
    run P c (n + m) = run P c n := by
  induction m with
  | zero => rfl
  | succ m ih => rw [← Nat.add_assoc, run_succ, ih, step_of_halted h]

theorem halted_run_of_le {P : Program k} {c : Config k} {n m : ℕ} (h : Halted P (run P c n))
    (hnm : n ≤ m) : Halted P (run P c m) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
  rw [run_of_halted h]
  exact h

/-- `P` halts from `c` when some run reaches an out-of-range program counter. -/
def Halts (P : Program k) (c : Config k) : Prop := ∃ n, Halted P (run P c n)

theorem Halts.of_halted {P : Program k} {c : Config k} (h : Halted P c) : Halts P c :=
  ⟨0, h⟩

theorem halts_iff_step {P : Program k} {c : Config k} :
    Halts P c ↔ Halted P c ∨ Halts P (step P c) := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => exact Or.inl hn
    | succ n => exact Or.inr ⟨n, by rwa [← run_succ']⟩
  · rintro (h | ⟨n, hn⟩)
    · exact ⟨0, h⟩
    · exact ⟨n + 1, by rwa [run_succ']⟩

/-!
## A smoke test

The decrement loop of the route spike (#15), as a one-register, one-instruction machine. It
exercises the only nonstandard choice in the model — that halting is a program counter out of
range rather than an instruction — and confirms that a `dec` whose zero-branch jumps to
`P.length` does in fact stop.
-/

/-- Decrement register `0` until it is zero. -/
def decLoop : Program 1 := [.dec 0 0 1]

theorem step_decLoop_succ (n : ℕ) : step decLoop ⟨0, fun _ => n + 1⟩ = ⟨0, fun _ => n⟩ := by
  rw [step_of_getElem? (i := .dec 0 0 1) rfl]
  simp only [Instr.exec, Nat.succ_ne_zero, if_false, Config.mk.injEq, true_and]
  funext i
  obtain rfl : i = 0 := Subsingleton.elim i 0
  simp

theorem run_decLoop (n : ℕ) : run decLoop ⟨0, fun _ => n⟩ n = ⟨0, fun _ => 0⟩ := by
  induction n with
  | zero => rfl
  | succ n ih => rw [run_succ', step_decLoop_succ, ih]

theorem halts_decLoop (n : ℕ) : Halts decLoop ⟨0, fun _ => n⟩ := by
  refine ⟨n + 1, ?_⟩
  rw [run_succ, run_decLoop, step_of_getElem? (i := .dec 0 0 1) rfl]
  simp [Instr.exec, Halted, decLoop]

end RegisterMachine

end Hilbert10


/- Source: Hilbert10.Internal.RegisterMachineComp, Hilbert10 v2.3.0, Apache-2.0. -/
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# Combining register machines

Issue #39: the two operations every constructor case in #40–#43 uses, together with the lemmas
that say they are semantically harmless.

**Renaming** moves a machine's registers into a larger register file along an injective
`σ : Fin k → Fin k'`. **Relocation** adds a constant to every jump target, so that `P ++ shiftJumps
P.length Q` runs `P` and then `Q`.

## Scope

This file proves that renaming and relocation are harmless; it does not choose names. There is
no fresh-register allocator, no name supply and no constraint generation here — choosing which
registers a compiled program uses is ordinary bookkeeping done case by case in #40–#43. The
distinction matters because the general version of "choose names for me" is #29, the deferred
DSL, arriving through the side door.

For the same reason there is no well-formedness predicate on programs. Sequencing needs to know
that `P` exits at exactly `P.length` rather than jumping past it, but that is a hypothesis on the
particular run, discharged where the program is built, not a global invariant every lemma has to
carry. This follows the project's rule of giving encoded objects total semantics and proving the
completeness side separately.

## Main results

* `Renamed.run`, `halts_renameRegs_iff` — execution equivariance under renaming
* `run_append_of_lt` — a prefix runs unchanged inside a longer program
* `run_append_shiftJumps` — the relocated suffix runs as itself, offset by `P.length`
* `halts_append_of_exits` — sequencing, given that the prefix exits at exactly `P.length`
-/

namespace Hilbert10

namespace RegisterMachine

variable {k k' k'' : ℕ}

/-! ## Renaming registers -/

/-- Rename the register an instruction touches. Jump targets are untouched. -/
def Instr.renameRegs (σ : Fin k → Fin k') : Instr k → Instr k'
  | .inc r j => .inc (σ r) j
  | .dec r jpos jzero => .dec (σ r) jpos jzero

/-- Rename every register of a program. -/
def renameRegs (σ : Fin k → Fin k') (P : Program k) : Program k' :=
  P.map (Instr.renameRegs σ)

@[simp] theorem Instr.renameRegs_id (i : Instr k) : i.renameRegs id = i := by
  cases i <;> rfl

@[simp] theorem Instr.renameRegs_comp (σ : Fin k → Fin k') (τ : Fin k' → Fin k'') (i : Instr k) :
    (i.renameRegs σ).renameRegs τ = i.renameRegs (τ ∘ σ) := by
  cases i <;> rfl

@[simp] theorem renameRegs_id (P : Program k) : renameRegs id P = P := by
  have : Instr.renameRegs (k := k) id = id := funext fun i => i.renameRegs_id
  simp [renameRegs, this]

@[simp] theorem renameRegs_comp (σ : Fin k → Fin k') (τ : Fin k' → Fin k'') (P : Program k) :
    renameRegs τ (renameRegs σ P) = renameRegs (τ ∘ σ) P := by
  simp [renameRegs, List.map_map, Function.comp_def]

@[simp] theorem length_renameRegs (σ : Fin k → Fin k') (P : Program k) :
    (renameRegs σ P).length = P.length :=
  List.length_map _

theorem getElem?_renameRegs (σ : Fin k → Fin k') (P : Program k) (n : ℕ) :
    (renameRegs σ P)[n]? = P[n]?.map (Instr.renameRegs σ) :=
  List.getElem?_map

/-- `c'` is `c` placed in a larger register file along `σ`: same program counter, and every
renamed register holds what the original did. Registers outside the image of `σ` are
unconstrained — that is the point, since they belong to the other machine. -/
structure Renamed (σ : Fin k → Fin k') (c : Config k) (c' : Config k') : Prop where
  /-- The program counters agree. -/
  pc : c'.pc = c.pc
  /-- Each renamed register holds the original's contents. -/
  regs : ∀ i, c'.regs (σ i) = c.regs i

theorem Renamed.exec {σ : Fin k → Fin k'} (hσ : Function.Injective σ) {c : Config k}
    {c' : Config k'} (h : Renamed σ c c') (i : Instr k) :
    Renamed σ (i.exec c.regs) ((i.renameRegs σ).exec c'.regs) := by
  have key : ∀ (r m : Fin k) (v : ℕ),
      Function.update c'.regs (σ r) v (σ m) = Function.update c.regs r v m := by
    intro r m v
    by_cases hm : m = r
    · subst hm; simp
    · rw [Function.update_of_ne (fun hc => hm (hσ hc)), Function.update_of_ne hm, h.regs]
  cases i with
  | inc r j =>
    refine ⟨rfl, fun m => ?_⟩
    change Function.update c'.regs (σ r) (c'.regs (σ r) + 1) (σ m)
      = Function.update c.regs r (c.regs r + 1) m
    rw [h.regs r]
    exact key r m _
  | dec r jpos jzero =>
    have hr : c'.regs (σ r) = c.regs r := h.regs r
    simp only [Instr.renameRegs, Instr.exec, hr]
    split
    · exact ⟨rfl, h.regs⟩
    · exact ⟨rfl, fun m => key r m _⟩

theorem Renamed.halted_iff {σ : Fin k → Fin k'} {P : Program k} {c : Config k} {c' : Config k'}
    (h : Renamed σ c c') : Halted (renameRegs σ P) c' ↔ Halted P c := by
  simp [Halted, h.pc]

theorem Renamed.step {σ : Fin k → Fin k'} (hσ : Function.Injective σ) {P : Program k}
    {c : Config k} {c' : Config k'} (h : Renamed σ c c') :
    Renamed σ (RegisterMachine.step P c) (RegisterMachine.step (renameRegs σ P) c') := by
  cases hp : P[c.pc]? with
  | none =>
    have hc : Halted P c := halted_iff_getElem?_eq_none.mpr hp
    rw [step_of_halted hc, step_of_halted (h.halted_iff.mpr hc)]
    exact h
  | some i =>
    have hp' : (renameRegs σ P)[c'.pc]? = some (i.renameRegs σ) := by
      rw [getElem?_renameRegs, h.pc, hp]; rfl
    rw [step_of_getElem? hp, step_of_getElem? hp']
    exact h.exec hσ i

theorem Renamed.run {σ : Fin k → Fin k'} (hσ : Function.Injective σ) {P : Program k}
    {c : Config k} {c' : Config k'} (h : Renamed σ c c') (n : ℕ) :
    Renamed σ (RegisterMachine.run P c n) (RegisterMachine.run (renameRegs σ P) c' n) := by
  induction n with
  | zero => simpa using h
  | succ n ih => rw [run_succ, run_succ]; exact ih.step hσ

/-- Renaming does not touch registers outside the image of `σ`. -/
theorem Instr.regs_exec_renameRegs_of_ne {σ : Fin k → Fin k'} {r : Fin k'} (hr : ∀ i, r ≠ σ i)
    (i : Instr k) (regs : Fin k' → ℕ) : ((i.renameRegs σ).exec regs).regs r = regs r := by
  cases i with
  | inc s j => exact Function.update_of_ne (hr s) _ _
  | dec s jpos jzero =>
    by_cases h : regs (σ s) = 0 <;>
      simp [Instr.renameRegs, Instr.exec, h, Function.update_of_ne (hr s)]

theorem regs_run_renameRegs_of_ne {σ : Fin k → Fin k'} {P : Program k} {c' : Config k'}
    {r : Fin k'} (hr : ∀ i, r ≠ σ i) (n : ℕ) :
    (RegisterMachine.run (renameRegs σ P) c' n).regs r = c'.regs r := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [run_succ]
    cases hp : (renameRegs σ P)[(RegisterMachine.run (renameRegs σ P) c' n).pc]? with
    | none => rw [step_of_halted (halted_iff_getElem?_eq_none.mpr hp)]; exact ih
    | some i =>
      rw [step_of_getElem? hp, getElem?_renameRegs] at *
      obtain ⟨i0, _, rfl⟩ := Option.map_eq_some_iff.mp hp
      rw [Instr.regs_exec_renameRegs_of_ne hr]
      exact ih

/-- **Execution equivariance.** Renaming registers along an injection does not change whether a
machine halts. -/
theorem halts_renameRegs_iff {σ : Fin k → Fin k'} (hσ : Function.Injective σ) {P : Program k}
    {c : Config k} {c' : Config k'} (h : Renamed σ c c') :
    Halts (renameRegs σ P) c' ↔ Halts P c :=
  exists_congr fun n => (h.run hσ n).halted_iff

/-! ## Relocating jump targets -/

/-- Add `d` to every jump target of an instruction. -/
def Instr.shiftJumps (d : ℕ) : Instr k → Instr k
  | .inc r j => .inc r (j + d)
  | .dec r jpos jzero => .dec r (jpos + d) (jzero + d)

/-- Add `d` to every jump target of a program. -/
def shiftJumps (d : ℕ) (P : Program k) : Program k := P.map (Instr.shiftJumps d)

@[simp] theorem length_shiftJumps (d : ℕ) (P : Program k) : (shiftJumps d P).length = P.length :=
  List.length_map _

theorem getElem?_shiftJumps (d : ℕ) (P : Program k) (n : ℕ) :
    (shiftJumps d P)[n]? = P[n]?.map (Instr.shiftJumps d) :=
  List.getElem?_map

theorem Instr.exec_shiftJumps (d : ℕ) (i : Instr k) (regs : Fin k → ℕ) :
    (i.shiftJumps d).exec regs = ⟨(i.exec regs).pc + d, (i.exec regs).regs⟩ := by
  cases i with
  | inc r j => rfl
  | dec r jpos jzero => by_cases h : regs r = 0 <;> simp [Instr.shiftJumps, Instr.exec, h]

/-! ## Concatenation -/

/-- Inside a longer program, a step taken strictly within the prefix is a step of the prefix. -/
theorem step_append_of_lt {P R : Program k} {c : Config k} (h : c.pc < P.length) :
    step (P ++ R) c = step P c := by
  rw [step, step, List.getElem?_append_left h]

/-- A run that never leaves the prefix is unchanged by appending to it. -/
theorem run_append_of_lt {P R : Program k} {c : Config k} {n : ℕ}
    (h : ∀ m < n, (run P c m).pc < P.length) : run (P ++ R) c n = run P c n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hstep := ih fun m hm => h m (Nat.lt_succ_of_lt hm)
    rw [run_succ, run_succ, hstep, step_append_of_lt (h n (Nat.lt_succ_self n))]

/-- One step of the relocated suffix, seen from inside the concatenation. -/
theorem step_append_shiftJumps (P Q : Program k) (p : ℕ) (regs : Fin k → ℕ) :
    step (P ++ shiftJumps P.length Q) ⟨p + P.length, regs⟩ =
      ⟨(step Q ⟨p, regs⟩).pc + P.length, (step Q ⟨p, regs⟩).regs⟩ := by
  rw [step, step, List.getElem?_append_right (Nat.le_add_left _ _)]
  simp only [Nat.add_sub_cancel, getElem?_shiftJumps]
  cases hp : Q[p]? with
  | none => simp
  | some i => simp [Instr.exec_shiftJumps]

/-- **Sequencing.** Once control reaches the relocated suffix, it runs as `Q` does, with every
program counter offset by `P.length`. -/
theorem run_append_shiftJumps (P Q : Program k) (p : ℕ) (regs : Fin k → ℕ) (n : ℕ) :
    run (P ++ shiftJumps P.length Q) ⟨p + P.length, regs⟩ n =
      ⟨(run Q ⟨p, regs⟩ n).pc + P.length, (run Q ⟨p, regs⟩ n).regs⟩ := by
  induction n with
  | zero => rfl
  | succ n ih => rw [run_succ, run_succ, ih, step_append_shiftJumps]

theorem halted_append_shiftJumps_iff (P Q : Program k) (p : ℕ) (regs : Fin k → ℕ) :
    Halted (P ++ shiftJumps P.length Q) ⟨p + P.length, regs⟩ ↔ Halted Q ⟨p, regs⟩ := by
  simp only [Halted, List.length_append, length_shiftJumps]
  omega

/-- The suffix halts inside the concatenation exactly when it halts on its own. -/
theorem halts_append_shiftJumps_iff (P Q : Program k) (p : ℕ) (regs : Fin k → ℕ) :
    Halts (P ++ shiftJumps P.length Q) ⟨p + P.length, regs⟩ ↔ Halts Q ⟨p, regs⟩ :=
  exists_congr fun n => by
    rw [run_append_shiftJumps]
    exact halted_append_shiftJumps_iff P Q _ _

/-- **Composition.** If `P` exits at exactly `P.length` after `n` steps without leaving itself
first, then the concatenation halts iff `Q` halts from the register file `P` produced.

The two hypotheses are what each constructor case in #40–#43 must supply about the program it
builds; they are deliberately not packaged as a well-formedness predicate. -/
theorem halts_append_of_exits {P Q : Program k} {c : Config k} {n : ℕ}
    (hin : ∀ m < n, (run P c m).pc < P.length) (hexit : (run P c n).pc = P.length) :
    Halts (P ++ shiftJumps P.length Q) c ↔ Halts Q ⟨0, (run P c n).regs⟩ := by
  have hn : run (P ++ shiftJumps P.length Q) c n = ⟨0 + P.length, (run P c n).regs⟩ := by
    rw [run_append_of_lt hin, Nat.zero_add, ← hexit]
  constructor
  · rintro ⟨m, hm⟩
    refine (halts_append_shiftJumps_iff P Q 0 _).mp ⟨m, ?_⟩
    rw [← hn, ← run_add]
    exact halted_run_of_le hm (Nat.le_add_left m n)
  · intro hq
    obtain ⟨m, hm⟩ := (halts_append_shiftJumps_iff P Q 0 _).mpr hq
    exact ⟨n + m, by rw [run_add, hn]; exact hm⟩

end RegisterMachine

end Hilbert10


/- Source: Hilbert10.Internal.RegisterMachineRealises, Hilbert10 v2.3.0, Apache-2.0. -/
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# The exit contract

Issue #40. What a compiled program has to satisfy for #41 to be able to compose it.

A bare halting equivalence is too weak: `halts_append_of_exits` (#39) needs to know *where* a
program stops and *what* it leaves behind, not merely that it stops. So the contract is a single
predicate on runs:

```lean
Realises P F ↔ from every register file, `P` starts at 0, stays inside itself, exits at exactly
  `P.length`, and leaves the register file `F regs`
```

Two things follow from stating it this way rather than as a list of clauses.

*Output and preservation are one clause, not two.* `F` describes the whole final register file,
so a constructor's statement — say `fun regs => Function.update regs r 0` — says both what was
produced and that nothing else moved. There is no separate "owns these registers" side condition
to carry, and no way for the two halves to drift apart.

*It is exactly the hypothesis `halts_append_of_exits` wants.* `Realises.append` discharges that
lemma once and for all, so #41 composes machines without ever reasoning about program counters
again.

## Totality

`Realises` describes machines that always halt, which is what the constructors here are, and it
stays the right contract for total macros: register plumbing, and later the pairing arithmetic
of #51.

It is *not* enough for the compiler. `rfind'` is where divergence originates, but divergence
propagates: `comp cf cg` diverges wherever `cg` does, and so does `prec`, and so does `pair`. So
the recursive compilation already needs a partial contract at #41, not at #43. `PartRealises`
below is that companion, and `Realises.toPartRealises` embeds the total machines into it.
-/

namespace Hilbert10

namespace RegisterMachine

variable {k : ℕ}

/-- `P` transforms the register file by `F`: from program counter `0` it stays inside itself,
exits at exactly `P.length`, and leaves `F regs`.

The exit position matters as much as the fact of halting. A program that jumps past its own end
would still halt, but concatenating it would drop control into the middle of whatever follows. -/
def Realises (P : Program k) (F : (Fin k → ℕ) → Fin k → ℕ) : Prop :=
  ∀ regs : Fin k → ℕ, ∃ n,
    (∀ m < n, (run P ⟨0, regs⟩ m).pc < P.length) ∧
      run P ⟨0, regs⟩ n = ⟨P.length, F regs⟩

theorem Realises.halts {P : Program k} {F} (h : Realises P F) (regs : Fin k → ℕ) :
    Halts P ⟨0, regs⟩ := by
  obtain ⟨n, _, hn⟩ := h regs
  exact ⟨n, by rw [hn]; exact Nat.le_refl _⟩

theorem Realises.congr {P : Program k} {F G : (Fin k → ℕ) → Fin k → ℕ} (h : Realises P F)
    (hFG : ∀ regs, F regs = G regs) : Realises P G := by
  intro regs
  obtain ⟨n, hin, hex⟩ := h regs
  exact ⟨n, hin, by rw [hex, hFG]⟩

/-- The empty program realises the identity. It is the unit for `Realises.append`. -/
theorem realises_nil : Realises ([] : Program k) id := fun _ => ⟨0, by omega, rfl⟩

theorem length_append_shiftJumps (P Q : Program k) :
    (P ++ shiftJumps P.length Q).length = P.length + Q.length := by simp

/-- Once the prefix has exited into the join, the rest of the concatenation's run is `Q`'s,
offset by `P.length`. -/
theorem run_join {P Q : Program k} {regs mid : Fin k → ℕ} {nP : ℕ}
    (hPin : ∀ m < nP, (run P ⟨0, regs⟩ m).pc < P.length)
    (hPex : run P ⟨0, regs⟩ nP = ⟨P.length, mid⟩) (j : ℕ) :
    run (P ++ shiftJumps P.length Q) ⟨0, regs⟩ (nP + j) =
      ⟨(run Q ⟨0, mid⟩ j).pc + P.length, (run Q ⟨0, mid⟩ j).regs⟩ := by
  have hmid : run (P ++ shiftJumps P.length Q) ⟨0, regs⟩ nP = ⟨0 + P.length, mid⟩ := by
    rw [run_append_of_lt hPin, hPex, Nat.zero_add]
  rw [run_add, hmid, run_append_shiftJumps]

/-- Two exact exits splice into one. Shared by the total and partial sequencing lemmas, which
differ only in where the two halves' data comes from. -/
theorem join_exit {P Q : Program k} {regs mid out : Fin k → ℕ} {nP nQ : ℕ}
    (hPin : ∀ m < nP, (run P ⟨0, regs⟩ m).pc < P.length)
    (hPex : run P ⟨0, regs⟩ nP = ⟨P.length, mid⟩)
    (hQin : ∀ m < nQ, (run Q ⟨0, mid⟩ m).pc < Q.length)
    (hQex : run Q ⟨0, mid⟩ nQ = ⟨Q.length, out⟩) :
    (∀ m < nP + nQ, (run (P ++ shiftJumps P.length Q) ⟨0, regs⟩ m).pc <
        (P ++ shiftJumps P.length Q).length) ∧
      run (P ++ shiftJumps P.length Q) ⟨0, regs⟩ (nP + nQ) =
        ⟨(P ++ shiftJumps P.length Q).length, out⟩ := by
  have hlen := length_append_shiftJumps P Q
  refine ⟨fun m hm => ?_, ?_⟩
  · by_cases hmP : m < nP
    · rw [run_append_of_lt fun j hj => hPin j (Nat.lt_trans hj hmP)]
      exact Nat.lt_of_lt_of_le (hPin m hmP) (hlen ▸ Nat.le_add_right _ _)
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.not_lt.mp hmP)
      have hj := hQin j (by omega)
      rw [run_join hPin hPex j, hlen]
      -- the goal projects out of a `Config` literal, which `omega` treats as an opaque atom
      exact show (run Q ⟨0, mid⟩ j).pc + P.length < P.length + Q.length by omega
  · rw [run_join hPin hPex nQ, hQex, hlen]
    simp [Nat.add_comm]



/-- **Two in-range segments of one program compose.** Both loops in #51 chain segments this way:
the counted loop over its turns, and the terminating enumeration within a single turn. -/
theorem run_segment_trans {P : Program k} {c d e : Config k} {n₁ n₂ : ℕ}
    (h1in : ∀ m < n₁, (run P c m).pc < P.length) (h1ex : run P c n₁ = d)
    (h2in : ∀ m < n₂, (run P d m).pc < P.length) (h2ex : run P d n₂ = e) :
    (∀ m < n₁ + n₂, (run P c m).pc < P.length) ∧ run P c (n₁ + n₂) = e := by
  refine ⟨fun m hm => ?_, ?_⟩
  · by_cases hms : m < n₁
    · exact h1in m hms
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.not_lt.mp hms)
      rw [run_add, h1ex]
      exact h2in j (by omega)
  · rw [run_add, h1ex, h2ex]

/-- **A relocated segment with programs on both sides.** `run_append_shiftJumps` covers a
relocated suffix; a loop body has an instruction after it as well.

Validated by both loop shapes in #51: the counted loop of `unpair` and the
terminating-enumeration loop of `pair`. -/
theorem run_middle {A B C : Program k} {regs : Fin k → ℕ} {n : ℕ}
    (hin : ∀ m < n, (run B ⟨0, regs⟩ m).pc < B.length) (m : ℕ) (hm : m ≤ n) :
    run (A ++ shiftJumps A.length B ++ C) ⟨0 + A.length, regs⟩ m =
      ⟨(run B ⟨0, regs⟩ m).pc + A.length, (run B ⟨0, regs⟩ m).regs⟩ := by
  have hpre : ∀ j < m, (run (A ++ shiftJumps A.length B) ⟨0 + A.length, regs⟩ j).pc <
      (A ++ shiftJumps A.length B).length := by
    intro j hj
    rw [run_append_shiftJumps, length_append_shiftJumps]
    have hj' := hin j (by omega)
    exact show (run B ⟨0, regs⟩ j).pc + A.length < A.length + B.length by omega
  rw [run_append_of_lt hpre, run_append_shiftJumps]

/-- **Sequencing.** Composing realised machines needs no reasoning about program counters at
the call site. -/
theorem Realises.append {P Q : Program k} {F G : (Fin k → ℕ) → Fin k → ℕ}
    (hP : Realises P F) (hQ : Realises Q G) :
    Realises (P ++ shiftJumps P.length Q) fun regs => G (F regs) := by
  intro regs
  obtain ⟨nP, hPin, hPex⟩ := hP regs
  obtain ⟨nQ, hQin, hQex⟩ := hQ (F regs)
  exact ⟨nP + nQ, join_exit hPin hPex hQin hQex⟩


/-- **Exact exits are unique.** Execution is deterministic, so a run that stops exactly at
`P.length` without leaving the program first does so at one time and in one state. -/
theorem exit_unique {P : Program k} {c : Config k} {o₁ o₂ : Fin k → ℕ} {n₁ n₂ : ℕ}
    (h1in : ∀ m < n₁, (run P c m).pc < P.length) (h1ex : run P c n₁ = ⟨P.length, o₁⟩)
    (h2in : ∀ m < n₂, (run P c m).pc < P.length) (h2ex : run P c n₂ = ⟨P.length, o₂⟩) :
    n₁ = n₂ ∧ o₁ = o₂ := by
  have hn : n₁ = n₂ := by
    rcases Nat.lt_trichotomy n₁ n₂ with h | h | h
    · exact absurd (h2in n₁ h) (by rw [h1ex]; exact Nat.not_lt.mpr (Nat.le_refl _))
    · exact h
    · exact absurd (h1in n₂ h) (by rw [h2ex]; exact Nat.not_lt.mpr (Nat.le_refl _))
  subst hn
  exact ⟨rfl, congrArg Config.regs (h1ex.symm.trans h2ex)⟩

/-! ## The partial contract

`rfind'` is where divergence originates, but it propagates: `comp cf cg` diverges wherever `cg`
does, and so do `prec` and `pair`. So the recursive compilation needs this companion from #41
onward, and `Realises` remains the contract for total macros. -/

/-- `P` partially transforms the register file by `F`.

Both clauses are load-bearing. Every value of `F` is reached by an *exact* exit at `P.length`;
and conversely, whenever `P` halts at all, `F` is defined there.

The converse clause is what rules out halting by jumping past the end. Without it a machine
could satisfy the first clause vacuously on an input where `F` diverges and still stop, and
concatenating that machine would drop control into the middle of whatever follows. -/
def PartRealises (P : Program k) (F : (Fin k → ℕ) →. (Fin k → ℕ)) : Prop :=
  ∀ regs : Fin k → ℕ,
    (∀ out ∈ F regs, ∃ n, (∀ m < n, (run P ⟨0, regs⟩ m).pc < P.length) ∧
        run P ⟨0, regs⟩ n = ⟨P.length, out⟩) ∧
      (Halts P ⟨0, regs⟩ → (F regs).Dom)

theorem PartRealises.exit {P : Program k} {F} (h : PartRealises P F) {regs out}
    (hout : out ∈ F regs) :
    ∃ n, (∀ m < n, (run P ⟨0, regs⟩ m).pc < P.length) ∧
      run P ⟨0, regs⟩ n = ⟨P.length, out⟩ :=
  (h regs).1 out hout

theorem PartRealises.dom {P : Program k} {F} (h : PartRealises P F) {regs}
    (hh : Halts P ⟨0, regs⟩) : (F regs).Dom :=
  (h regs).2 hh

/-- Halting and convergence coincide — the statement the two clauses exist to make true. -/
theorem PartRealises.halts_iff {P : Program k} {F} (h : PartRealises P F) (regs : Fin k → ℕ) :
    Halts P ⟨0, regs⟩ ↔ (F regs).Dom := by
  refine ⟨h.dom, fun hd => ?_⟩
  obtain ⟨n, _, hn⟩ := h.exit (Part.get_mem hd)
  exact ⟨n, by rw [hn]; exact Nat.le_refl _⟩

/-- The second clause is not redundant. `[inc r 5]` halts by jumping past its own end, and on an
input where the intended function diverges the first clause is vacuous — so only the converse
clause rejects it. -/
example (r : Fin k) (regs : Fin k → ℕ) :
    ¬ PartRealises [Instr.inc r 5] fun _ => (Part.none : Part (Fin k → ℕ)) := by
  intro h
  refine (h regs).2 ⟨1, ?_⟩
  rw [run_succ, run_zero, step_of_getElem? (i := .inc r 5) rfl]
  simp [Halted, Instr.exec]

theorem PartRealises.congr {P : Program k} {F G : (Fin k → ℕ) →. (Fin k → ℕ)}
    (h : PartRealises P F) (hFG : ∀ regs, F regs = G regs) : PartRealises P G := by
  intro regs
  rw [← hFG]
  exact h regs

/-- A total machine is a partial one. -/
theorem Realises.toPartRealises {P : Program k} {F} (h : Realises P F) :
    PartRealises P fun regs => Part.some (F regs) := by
  refine fun regs => ⟨fun out hout => ?_, fun _ => trivial⟩
  have hEq : out = F regs := by simpa using hout
  subst hEq
  exact h regs

/-- If a concatenation halts then its prefix does: a run that never leaves `P` never leaves
`P ++ R` either. -/
theorem halts_prefix_of_halts_append {P R : Program k} {c : Config k} (h : Halts (P ++ R) c) :
    Halts P c := by
  by_contra hn
  simp only [Halts, not_exists] at hn
  have hlt : ∀ m, (run P c m).pc < P.length := fun m => Nat.lt_of_not_le (hn m)
  obtain ⟨N, hN⟩ := h
  rw [run_append_of_lt fun j _ => hlt j] at hN
  exact absurd hN (Nat.not_le.mpr (Nat.lt_of_lt_of_le (hlt N) (by simp)))

/-- **Partial sequencing**, realising Kleisli composition. This is what #41 consumes for
`Code.comp`, where either half may diverge. -/
theorem PartRealises.append {P Q : Program k} {F G : (Fin k → ℕ) →. (Fin k → ℕ)}
    (hP : PartRealises P F) (hQ : PartRealises Q G) :
    PartRealises (P ++ shiftJumps P.length Q) fun regs => F regs >>= G := by
  refine fun regs => ⟨fun out hout => ?_, fun hh => ?_⟩
  · obtain ⟨mid, hmid, hout'⟩ := Part.mem_bind_iff.mp hout
    obtain ⟨nP, hPin, hPex⟩ := hP.exit hmid
    obtain ⟨nQ, hQin, hQex⟩ := hQ.exit hout'
    exact ⟨nP + nQ, join_exit hPin hPex hQin hQex⟩
  · -- the concatenation halted, so the prefix did, so `F regs` converges
    have hFd : (F regs).Dom := hP.dom (halts_prefix_of_halts_append hh)
    have hmid : (F regs).get hFd ∈ F regs := Part.get_mem hFd
    obtain ⟨nP, hPin, hPex⟩ := hP.exit hmid
    obtain ⟨N, hN⟩ := hh
    -- it cannot have halted before reaching the join, since the prefix stays in range there
    have hNge : nP ≤ N := by
      by_contra hlt
      rw [run_append_of_lt fun j hj => hPin j (Nat.lt_trans hj (Nat.not_le.mp hlt))] at hN
      exact absurd hN (Nat.not_le.mpr (Nat.lt_of_lt_of_le (hPin N (Nat.not_le.mp hlt)) (by simp)))
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hNge
    rw [run_join hPin hPex j] at hN
    have hQh : Halts Q ⟨0, (F regs).get hFd⟩ := by
      refine ⟨j, ?_⟩
      have hle : (P ++ shiftJumps P.length Q).length
          ≤ (run Q ⟨0, (F regs).get hFd⟩ j).pc + P.length := hN
      rw [length_append_shiftJumps] at hle
      exact show Q.length ≤ (run Q ⟨0, (F regs).get hFd⟩ j).pc by omega
    have hGd := hQ.dom hQh
    exact Part.dom_iff_mem.mpr ⟨_, Part.mem_bind hmid (Part.get_mem hGd)⟩


/-- **Width lifting for total machines.** The caller supplies the lifted transformation `G` and
says how it behaves on the image of `σ` and off it; nothing here chooses registers.

The partial companion `PartComputesUnary.renameRegs` cannot be derived from this and vice versa,
so both exist. -/
theorem Realises.renameRegs {k' : ℕ} {σ : Fin k → Fin k'} (hσ : Function.Injective σ)
    {P : Program k} {F : (Fin k → ℕ) → Fin k → ℕ} {G : (Fin k' → ℕ) → Fin k' → ℕ}
    (h : Realises P F) (hon : ∀ regs i, G regs (σ i) = F (regs ∘ σ) i)
    (hoff : ∀ regs r, (∀ i, r ≠ σ i) → G regs r = regs r) :
    Realises (RegisterMachine.renameRegs σ P) G := by
  classical
  intro regs
  have hren : Renamed σ ⟨0, regs ∘ σ⟩ ⟨0, regs⟩ := ⟨rfl, fun _ => rfl⟩
  obtain ⟨n, hin, hex⟩ := h (regs ∘ σ)
  have hr := hren.run (P := P) hσ n
  have hexr : (run P ⟨0, regs ∘ σ⟩ n).regs = F (regs ∘ σ) := by rw [hex]
  refine ⟨n, fun m hm => ?_, ?_⟩
  · rw [(hren.run (P := P) hσ m).pc, length_renameRegs]
    exact hin m hm
  · have hpc : (run (RegisterMachine.renameRegs σ P) ⟨0, regs⟩ n).pc =
        (RegisterMachine.renameRegs σ P).length := by
      rw [hr.pc, hex, length_renameRegs]
    have hregs : (run (RegisterMachine.renameRegs σ P) ⟨0, regs⟩ n).regs = G regs := by
      funext r
      by_cases hrng : ∃ i, r = σ i
      · obtain ⟨i, rfl⟩ := hrng
        rw [hr.regs i, hexr, hon]
      · push Not at hrng
        rw [regs_run_renameRegs_of_ne hrng n, hoff regs r hrng]
    rw [← hpc, ← hregs]


/-! ### The register file a total block produces

`Realises.renameRegs` lets the caller name the lifted transformation, which is right when there
is something specific to say. When there is not — when the answer is just "`F` on the block,
identity off it" — this packages it, so a renamed total machine is as opaque a state transition
as a call is. It is the total counterpart of `callState` in `CleanScratch`. -/

/-- `F` applied inside the block along `σ`, with everything outside it untouched. -/
noncomputable def blockState {k' : ℕ} (σ : Fin k → Fin k')
    (F : (Fin k → ℕ) → Fin k → ℕ) (regs : Fin k' → ℕ) : Fin k' → ℕ :=
  Function.extend σ (F (regs ∘ σ)) regs

theorem blockState_apply {k' : ℕ} {σ : Fin k → Fin k'} (hσ : Function.Injective σ)
    (F : (Fin k → ℕ) → Fin k → ℕ) (regs : Fin k' → ℕ) (i : Fin k) :
    blockState σ F regs (σ i) = F (regs ∘ σ) i :=
  hσ.extend_apply _ _ _

theorem blockState_of_not_mem {k' : ℕ} {σ : Fin k → Fin k'} (F : (Fin k → ℕ) → Fin k → ℕ)
    (regs : Fin k' → ℕ) {r : Fin k'} (hr : ∀ i, r ≠ σ i) : blockState σ F regs r = regs r :=
  Function.extend_apply' _ _ _ (by rintro ⟨i, rfl⟩; exact hr i rfl)

theorem Realises.renameRegs_blockState {k' : ℕ} {σ : Fin k → Fin k'} (hσ : Function.Injective σ)
    {P : Program k} {F : (Fin k → ℕ) → Fin k → ℕ} (h : Realises P F) :
    Realises (RegisterMachine.renameRegs σ P) (blockState σ F) :=
  h.renameRegs hσ (fun regs i => blockState_apply hσ F regs i)
    (fun regs _ hr => blockState_of_not_mem F regs hr)


/-- **Running a renamed machine from a matching state.** The run-level analogue of
`Realises.renameRegs_blockState`: it transports a single exact run rather than a `Realises`, which
is what a machine with more than one output register needs. -/
theorem run_renameRegs_of_exit {k' : ℕ} {σ : Fin k → Fin k'} (hσ : Function.Injective σ)
    {P : Program k} {inRegs outRegs : Fin k → ℕ} {n : ℕ}
    (hin : ∀ m < n, (run P ⟨0, inRegs⟩ m).pc < P.length)
    (hex : run P ⟨0, inRegs⟩ n = ⟨P.length, outRegs⟩)
    {regs : Fin k' → ℕ} (hreg : ∀ i, regs (σ i) = inRegs i) :
    (∀ m < n, (run (RegisterMachine.renameRegs σ P) ⟨0, regs⟩ m).pc <
        (RegisterMachine.renameRegs σ P).length) ∧
      run (RegisterMachine.renameRegs σ P) ⟨0, regs⟩ n =
        ⟨(RegisterMachine.renameRegs σ P).length, Function.extend σ outRegs regs⟩ := by
  classical
  have hcomp : regs ∘ σ = inRegs := funext hreg
  have hren : Renamed σ ⟨0, inRegs⟩ ⟨0, regs⟩ := ⟨rfl, fun i => congrFun hcomp i⟩
  have hexr : (run P ⟨0, inRegs⟩ n).regs = outRegs := by rw [hex]
  refine ⟨fun m hm => ?_, ?_⟩
  · rw [(hren.run (P := P) hσ m).pc, length_renameRegs]
    exact hin m hm
  · have hpc : (run (RegisterMachine.renameRegs σ P) ⟨0, regs⟩ n).pc =
        (RegisterMachine.renameRegs σ P).length := by
      rw [(hren.run (P := P) hσ n).pc, hex, length_renameRegs]
    have hregs : (run (RegisterMachine.renameRegs σ P) ⟨0, regs⟩ n).regs =
        Function.extend σ outRegs regs := by
      funext r
      by_cases hrng : ∃ i, r = σ i
      · obtain ⟨i, rfl⟩ := hrng
        rw [(hren.run (P := P) hσ n).regs i, hexr, hσ.extend_apply]
      · push Not at hrng
        rw [regs_run_renameRegs_of_ne hrng n,
          Function.extend_apply' _ _ _ (by rintro ⟨i, rfl⟩; exact hrng i rfl)]
    rw [← hpc, ← hregs]

/-! ## Primitive machines

The two one-instruction programs. `incr` exercises the exit contract on a straight-line
program, `clear` on a loop, and `Realises.append` glues them; nothing here needs a
well-formedness predicate, a register allocator, or a name supply. -/

/-- Increment register `r`. -/
def incr (r : Fin k) : Program k := [.inc r 1]

theorem realises_incr (r : Fin k) :
    Realises (incr r) fun regs => Function.update regs r (regs r + 1) := by
  intro regs
  refine ⟨1, fun m hm => ?_, ?_⟩
  · rw [Nat.lt_one_iff.mp hm]
    exact Nat.zero_lt_one
  · rw [run_succ, run_zero, step_of_getElem? (i := .inc r 1) rfl]
    rfl

/-- Set register `r` to zero, by decrementing until it is. -/
def clear (r : Fin k) : Program k := [.dec r 0 1]

private theorem run_clear (r : Fin k) (regs : Fin k → ℕ) :
    ∀ j ≤ regs r, run (clear r) ⟨0, regs⟩ j = ⟨0, Function.update regs r (regs r - j)⟩ := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    have hlt : j < regs r := by omega
    rw [run_succ, ih (by omega), step_of_getElem? (i := .dec r 0 1) rfl]
    have hval : Function.update regs r (regs r - j) r = regs r - j := by simp
    simp only [Instr.exec, hval]
    rw [if_neg (by omega), Function.update_idem,
      show regs r - j - 1 = regs r - (j + 1) by omega]

theorem realises_clear (r : Fin k) :
    Realises (clear r) fun regs => Function.update regs r 0 := by
  intro regs
  refine ⟨regs r + 1, fun m hm => ?_, ?_⟩
  · rw [run_clear r regs m (by omega)]
    exact Nat.zero_lt_one
  · rw [run_succ, run_clear r regs _ (Nat.le_refl _), step_of_getElem? (i := .dec r 0 1) rfl]
    simp [Instr.exec, clear]

/-- A machine that never halts: increment and jump back to the start. Needed to exercise the
partial contract, since a diverging component is not otherwise constructible here. -/
def loopMachine (r : Fin k) : Program k := [.inc r 0]

private theorem pc_run_loopMachine (r : Fin k) (regs : Fin k → ℕ) :
    ∀ n, (run (loopMachine r) ⟨0, regs⟩ n).pc = 0 := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [run_succ, step_of_getElem? (i := .inc r 0) (by rw [ih]; rfl)]
    rfl

theorem not_halts_loopMachine (r : Fin k) (regs : Fin k → ℕ) :
    ¬ Halts (loopMachine r) ⟨0, regs⟩ := by
  rintro ⟨n, hn⟩
  rw [Halted, pc_run_loopMachine] at hn
  simp [loopMachine] at hn

/-! ## The constructors

`Nat.Partrec.Code` denotes unary functions, so a compiled machine reads its input from and
writes its result to register `0`. `ComputesUnary` fixes that convention, and by being stated
through `Function.update` it says in the same breath that every other register survives. -/

/-- `P` computes the unary function `f` in register `0`, leaving every other register alone. -/
def ComputesUnary (P : Program (k + 1)) (f : ℕ → ℕ) : Prop :=
  Realises P fun regs => Function.update regs 0 (f (regs 0))

/-- The machine for `Nat.Partrec.Code.zero`. -/
def zeroMachine (k : ℕ) : Program (k + 1) := clear 0

theorem computesUnary_zeroMachine : ComputesUnary (zeroMachine k) fun _ => 0 :=
  realises_clear 0

/-- The machine for `Nat.Partrec.Code.succ`. -/
def succMachine (k : ℕ) : Program (k + 1) := incr 0

theorem computesUnary_succMachine : ComputesUnary (succMachine k) fun n => n + 1 :=
  realises_incr 0

/-- `P` computes the unary partial function `f` in register `0`, leaving every other register
alone wherever it converges. -/
def PartComputesUnary (P : Program (k + 1)) (f : ℕ →. ℕ) : Prop :=
  PartRealises P fun regs => (f (regs 0)).map fun y => Function.update regs 0 y

theorem ComputesUnary.toPart {P : Program (k + 1)} {f : ℕ → ℕ} (h : ComputesUnary P f) :
    PartComputesUnary P fun n => Part.some (f n) :=
  h.toPartRealises.congr fun regs => by simp

theorem PartComputesUnary.congr {P : Program (k + 1)} {f g : ℕ →. ℕ} (h : PartComputesUnary P f)
    (hfg : ∀ x, f x = g x) : PartComputesUnary P g :=
  PartRealises.congr h fun regs => by rw [hfg]

/-- **Width lifting.** Renaming a compiled machine into a larger register file along an injection
that fixes register `0` preserves what it computes.

This is where #39 is consumed. `Renamed` pins the image and `regs_run_renameRegs_of_ne` pins the
complement, so the lifted machine still disturbs nothing but register `0` — with no allocator,
because the injection is supplied by the caller rather than chosen here. -/
theorem PartComputesUnary.renameRegs {k' : ℕ} {P : Program (k + 1)} {f : ℕ →. ℕ}
    (h : PartComputesUnary P f) {σ : Fin (k + 1) → Fin (k' + 1)} (hσ : Function.Injective σ)
    (hσ0 : σ 0 = 0) : PartComputesUnary (RegisterMachine.renameRegs σ P) f := by
  classical
  intro regs'
  have hren : Renamed σ ⟨0, regs' ∘ σ⟩ ⟨0, regs'⟩ := ⟨rfl, fun _ => rfl⟩
  have h0 : (regs' ∘ σ) 0 = regs' 0 := by simp [hσ0]
  refine ⟨fun out' hout' => ?_, fun hh => ?_⟩
  · obtain ⟨z, hz, rfl⟩ := (Part.mem_map_iff _).mp hout'
    obtain ⟨n, hin, hex⟩ := h.exit (Part.mem_map _ (show z ∈ f ((regs' ∘ σ) 0) from h0 ▸ hz))
    have hr := hren.run (P := P) hσ n
    refine ⟨n, fun m hm => ?_, ?_⟩
    · rw [(hren.run (P := P) hσ m).pc, length_renameRegs]
      exact hin m hm
    · have hpc : (run (RegisterMachine.renameRegs σ P) ⟨0, regs'⟩ n).pc =
          (RegisterMachine.renameRegs σ P).length := by rw [hr.pc, hex, length_renameRegs]
      have hregs : (run (RegisterMachine.renameRegs σ P) ⟨0, regs'⟩ n).regs =
          Function.update regs' 0 z := by
        have hexr : (run P ⟨0, regs' ∘ σ⟩ n).regs = Function.update (regs' ∘ σ) 0 z := by
          rw [hex]
        funext r
        by_cases hrng : ∃ i, r = σ i
        · obtain ⟨i, rfl⟩ := hrng
          rw [hr.regs i, hexr]
          by_cases hi : i = 0
          · subst hi; simp [hσ0]
          · rw [Function.update_of_ne hi,
              Function.update_of_ne (fun hc => hi (hσ (hc.trans hσ0.symm)))]
            rfl
        · push Not at hrng
          rw [regs_run_renameRegs_of_ne hrng n,
            Function.update_of_ne (by rintro rfl; exact hrng 0 hσ0.symm)]
      rw [← hpc, ← hregs]
  · have hd : (f ((regs' ∘ σ) 0)).Dom := h.dom ((halts_renameRegs_iff hσ hren).mp hh)
    rw [h0] at hd
    exact hd

/-- The diverging machine computes the everywhere-undefined function. -/
theorem partComputesUnary_loopMachine (r : Fin (k + 1)) :
    PartComputesUnary (loopMachine r) fun _ => Part.none := fun regs =>
  ⟨fun _ hout => absurd hout (by simp), fun hh => absurd hh (not_halts_loopMachine r regs)⟩

/-! ## A composite

`clear` then `incr`, on the same register: the first machine whose run genuinely moves through a
concatenation, and a check that `Realises.append` is usable without unfolding it. -/

example (r : Fin k) :
    Realises (clear r ++ shiftJumps (clear r).length (incr r))
      fun regs => Function.update regs r 1 := by
  refine ((realises_clear r).append (realises_incr r)).congr fun regs => ?_
  simp

end RegisterMachine

end Hilbert10


/- Source: Hilbert10.Internal.RegisterMachineMacros, Hilbert10 v2.3.0, Apache-2.0. -/
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# Register plumbing

Issue #51, step 2. The total macros the pairing machines are built from.

Each is stated as a `Realises` fact with an explicit whole-register transformation, so the
statement says at once what was produced *and* that every temporary was left at zero. A macro
that returned the right value while leaving a counter dirty would not typecheck against these
statements, which is the point: the clean-scratch convention of `CleanScratch` is only worth
something if the macros actually give back what they borrow.

Every macro takes the registers it uses as arguments, with distinctness as explicit hypotheses.
There is no allocator and no name supply here, per the standing guard from #39.

## Proving loops

Two small pieces of technique, both learned the hard way.

`step_dec_pos`, `step_dec_zero` and `step_inc` turn one machine step into one equation about
register files, so a loop body becomes a chain of rewrites rather than a nest of `step`
applications.

Each loop's body is proved *once*, for an arbitrary register file, as a `run … c p` fact for the
body's length `p`. The induction over turns of the loop then goes through `run_add`, never
through `run_succ`. This matters: `Config` is a structure, so structure eta lets the pattern
`step P ⟨p, regs⟩` match *any* `step P c`, and `rw` will happily aim a step lemma at the
outermost step of a nest instead of the innermost one.
-/

namespace Hilbert10

namespace RegisterMachine

variable {k : ℕ}

theorem run_one (P : Program k) (c : Config k) : run P c 1 = step P c := rfl

theorem step_dec_pos {P : Program k} {r : Fin k} {a b p : ℕ} {regs : Fin k → ℕ}
    (hp : P[p]? = some (.dec r a b)) (h : regs r ≠ 0) :
    step P ⟨p, regs⟩ = ⟨a, Function.update regs r (regs r - 1)⟩ := by
  rw [step_of_getElem? hp]
  simp [Instr.exec, h]

theorem step_dec_zero {P : Program k} {r : Fin k} {a b p : ℕ} {regs : Fin k → ℕ}
    (hp : P[p]? = some (.dec r a b)) (h : regs r = 0) : step P ⟨p, regs⟩ = ⟨b, regs⟩ := by
  rw [step_of_getElem? hp]
  simp [Instr.exec, h]

theorem step_inc {P : Program k} {r : Fin k} {a p : ℕ} {regs : Fin k → ℕ}
    (hp : P[p]? = some (.inc r a)) :
    step P ⟨p, regs⟩ = ⟨a, Function.update regs r (regs r + 1)⟩ := by
  rw [step_of_getElem? hp]
  rfl

/-- Sequential composition: `++` with the second program relocated. Named because the macros
below chain four of them and the raw form is unreadable at that length. -/
def seq (P Q : Program k) : Program k := P ++ shiftJumps P.length Q

@[simp] theorem length_seq (P Q : Program k) : (seq P Q).length = P.length + Q.length :=
  length_append_shiftJumps P Q

theorem Realises.seq {P Q : Program k} {F G : (Fin k → ℕ) → Fin k → ℕ} (hP : Realises P F)
    (hQ : Realises Q G) : Realises (RegisterMachine.seq P Q) fun regs => G (F regs) :=
  hP.append hQ

/-! ## Moving

`move` empties one register into another; `moveTwo` empties it into two at once, which is what
makes a non-destructive copy possible. -/

/-- Add `r` into `s`, leaving `r` at zero. -/
def move (r s : Fin k) : Program k := [.dec r 1 2, .inc s 0]

/-- The register file after `j` turns of `move`'s loop. -/
private def moveState (r s : Fin k) (regs : Fin k → ℕ) (j : ℕ) : Fin k → ℕ :=
  fun i => if i = r then regs r - j else if i = s then regs s + j else regs i

/-- One turn of `move`'s loop, for an arbitrary register file. -/
private theorem run_move_body {r s : Fin k} (hrs : r ≠ s) (R : Fin k → ℕ) (hR : R r ≠ 0) :
    run (move r s) ⟨0, R⟩ 2 =
      ⟨0, fun i => if i = r then R r - 1 else if i = s then R s + 1 else R i⟩ := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, run_add, run_one, run_one,
    step_dec_pos (P := move r s) (b := 2) rfl hR,
    step_inc (P := move r s) (p := 1) (a := 0) rfl]
  refine congrArg _ (funext fun i => ?_)
  simp only [Function.update_apply]
  split_ifs <;> simp_all

private theorem run_move {r s : Fin k} (hrs : r ≠ s) (regs : Fin k → ℕ) : ∀ j ≤ regs r,
    run (move r s) ⟨0, regs⟩ (2 * j) = ⟨0, moveState r s regs j⟩ := by
  intro j
  induction j with
  | zero =>
    intro _
    refine congrArg _ (funext fun i => ?_)
    simp only [moveState]
    split_ifs <;> simp_all
  | succ j ih =>
    intro hj
    have hval : moveState r s regs j r = regs r - j := by simp [moveState]
    rw [show 2 * (j + 1) = 2 * j + 2 by omega, run_add, ih (by omega),
      run_move_body hrs _ (by rw [hval]; omega)]
    refine congrArg _ (funext fun i => ?_)
    simp only [moveState]
    split_ifs <;> simp_all <;> omega

private theorem pc_run_move {r s : Fin k} (hrs : r ≠ s) (regs : Fin k → ℕ) :
    ∀ m < 2 * regs r + 1, (run (move r s) ⟨0, regs⟩ m).pc < (move r s).length := by
  intro m hm
  obtain ⟨j, c, hc, rfl⟩ : ∃ j c, c < 2 ∧ m = 2 * j + c :=
    ⟨m / 2, m % 2, Nat.mod_lt _ (by omega), by omega⟩
  have hval : moveState r s regs j r = regs r - j := by simp [moveState]
  rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl
  · rw [Nat.add_zero, run_move hrs regs j (by omega)]
    simp [move]
  · rw [run_add, run_move hrs regs j (by omega), run_one,
      step_dec_pos (P := move r s) (b := 2) rfl (by rw [hval]; omega)]
    simp [move]

theorem realises_move {r s : Fin k} (hrs : r ≠ s) :
    Realises (move r s) fun regs i =>
      if i = r then 0 else if i = s then regs s + regs r else regs i := by
  intro regs
  refine ⟨2 * regs r + 1, pc_run_move hrs regs, ?_⟩
  have hval : moveState r s regs (regs r) r = 0 := by simp [moveState]
  rw [run_add, run_move hrs regs _ (Nat.le_refl _), run_one,
    step_dec_zero (P := move r s) (a := 1) rfl hval, show (move r s).length = 2 from rfl]
  refine congrArg _ (funext fun i => ?_)
  simp only [moveState]
  split_ifs <;> simp_all

/-- Add `r` into both `s` and `t`, leaving `r` at zero. -/
def moveTwo (r s t : Fin k) : Program k := [.dec r 1 3, .inc s 2, .inc t 0]

/-- The register file after `j` turns of `moveTwo`'s loop. -/
private def moveTwoState (r s t : Fin k) (regs : Fin k → ℕ) (j : ℕ) : Fin k → ℕ :=
  fun i => if i = r then regs r - j else if i = s then regs s + j
    else if i = t then regs t + j else regs i

/-- One turn of `moveTwo`'s loop, for an arbitrary register file. -/
private theorem run_moveTwo_body {r s t : Fin k} (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
    (R : Fin k → ℕ) (hR : R r ≠ 0) :
    run (moveTwo r s t) ⟨0, R⟩ 3 =
      ⟨0, fun i => if i = r then R r - 1 else if i = s then R s + 1
        else if i = t then R t + 1 else R i⟩ := by
  rw [show (3 : ℕ) = 1 + 1 + 1 from rfl, run_add, run_add, run_one, run_one, run_one,
    step_dec_pos (P := moveTwo r s t) (b := 3) rfl hR,
    step_inc (P := moveTwo r s t) (p := 1) (a := 2) rfl,
    step_inc (P := moveTwo r s t) (p := 2) (a := 0) rfl]
  refine congrArg _ (funext fun i => ?_)
  simp only [Function.update_apply]
  split_ifs <;> simp_all

private theorem run_moveTwo {r s t : Fin k} (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
    (regs : Fin k → ℕ) : ∀ j ≤ regs r,
    run (moveTwo r s t) ⟨0, regs⟩ (3 * j) = ⟨0, moveTwoState r s t regs j⟩ := by
  intro j
  induction j with
  | zero =>
    intro _
    refine congrArg _ (funext fun i => ?_)
    simp only [moveTwoState]
    split_ifs <;> simp_all
  | succ j ih =>
    intro hj
    have hval : moveTwoState r s t regs j r = regs r - j := by simp [moveTwoState]
    rw [show 3 * (j + 1) = 3 * j + 3 by omega, run_add, ih (by omega),
      run_moveTwo_body hrs hrt hst _ (by rw [hval]; omega)]
    refine congrArg _ (funext fun i => ?_)
    simp only [moveTwoState]
    split_ifs <;> simp_all <;> omega

private theorem pc_run_moveTwo {r s t : Fin k} (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
    (regs : Fin k → ℕ) : ∀ m < 3 * regs r + 1,
    (run (moveTwo r s t) ⟨0, regs⟩ m).pc < (moveTwo r s t).length := by
  intro m hm
  obtain ⟨j, c, hc, rfl⟩ : ∃ j c, c < 3 ∧ m = 3 * j + c :=
    ⟨m / 3, m % 3, Nat.mod_lt _ (by omega), by omega⟩
  have hjr : j ≤ regs r := by omega
  have hval : moveTwoState r s t regs j r = regs r - j := by simp [moveTwoState]
  -- `hstep` is only available once we know the loop has not already exited, which is exactly
  -- the case `c ≠ 0`: at `c = 0` the machine is sitting on the zero test.
  rcases (show c = 0 ∨ c = 1 ∨ c = 2 by omega) with rfl | rfl | rfl
  · rw [Nat.add_zero, run_moveTwo hrs hrt hst regs j hjr]
    simp [moveTwo]
  · rw [run_add, run_moveTwo hrs hrt hst regs j hjr, run_one,
      step_dec_pos (P := moveTwo r s t) (b := 3) rfl (by rw [hval]; omega)]
    simp [moveTwo]
  · rw [show 3 * j + 2 = 3 * j + 1 + 1 by omega, run_add, run_add,
      run_moveTwo hrs hrt hst regs j hjr, run_one, run_one,
      step_dec_pos (P := moveTwo r s t) (regs := moveTwoState r s t regs j) (b := 3) rfl
        (by rw [hval]; omega),
      step_inc (P := moveTwo r s t) (p := 1) (a := 2) rfl]
    simp [moveTwo]

theorem realises_moveTwo {r s t : Fin k} (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) :
    Realises (moveTwo r s t) fun regs i => if i = r then 0 else if i = s then regs s + regs r
      else if i = t then regs t + regs r else regs i := by
  intro regs
  refine ⟨3 * regs r + 1, pc_run_moveTwo hrs hrt hst regs, ?_⟩
  have hval : moveTwoState r s t regs (regs r) r = 0 := by simp [moveTwoState]
  rw [run_add, run_moveTwo hrs hrt hst regs _ (Nat.le_refl _), run_one,
    step_dec_zero (P := moveTwo r s t) (a := 1) rfl hval,
    show (moveTwo r s t).length = 3 from rfl]
  refine congrArg _ (funext fun i => ?_)
  simp only [moveTwoState]
  split_ifs <;> simp_all

/-! ## Copying

`copy` is the first macro whose statement carries a cleanliness claim: `t` is borrowed as working
storage and handed back at zero, whatever it held before. -/

/-- Copy `r` into `s`, using `t` as working storage and returning it at zero. `r` is unchanged. -/
def copy (r s t : Fin k) : Program k :=
  seq (clear s) (seq (clear t) (seq (moveTwo r s t) (move t r)))

theorem realises_copy {r s t : Fin k} (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) :
    Realises (copy r s t) fun regs i =>
      if i = s then regs r else if i = t then 0 else regs i := by
  refine (((realises_clear s).seq ((realises_clear t).seq
    ((realises_moveTwo hrs hrt hst).seq (realises_move (Ne.symm hrt))))).congr fun regs => ?_)
  funext i
  simp only [Function.update_apply]
  split_ifs <;> simp_all


/-! ## Comparison

The synchronised-decrement loop returns **both** residuals rather than a Boolean or an encoded
ordering:

```
lo := regs b - regs a      hi := regs a - regs b
```

That is what the implementation naturally produces, and it is exactly what `pairNext` needs: one
call settles all four of its branches. `lo > 0` says `a < b`; under that, `lo = 1` distinguishes
the shell rollover from an ordinary increment; and if `lo = 0` then `hi` distinguishes equality
from `a > b`. A Boolean would have thrown away the information and forced a second comparison.

`lo` and `hi` are *owned outputs*: they overwrite whatever they held. Only `tmp` is borrowed, and
it comes back at zero. -/

/-- Decrement `hi` and `lo` together until one runs out.

Both exits land at exactly `length`. The `inc hi` at position 2 undoes the decrement taken on the
turn that discovered `lo = 0`, which is why the loop tests `hi` first: the register whose test
can fail mid-turn has to be the one that is cheap to restore. -/
def syncDec (hi lo : Fin k) : Program k := [.dec hi 1 3, .dec lo 0 2, .inc hi 3]

/-- The register file after `j` synchronised decrements. -/
private def syncDecState (hi lo : Fin k) (regs : Fin k → ℕ) (j : ℕ) : Fin k → ℕ :=
  fun i => if i = hi then regs hi - j else if i = lo then regs lo - j else regs i

private theorem run_syncDec_body {hi lo : Fin k} (hne : hi ≠ lo) (R : Fin k → ℕ)
    (hH : R hi ≠ 0) (hL : R lo ≠ 0) :
    run (syncDec hi lo) ⟨0, R⟩ 2 =
      ⟨0, fun i => if i = hi then R hi - 1 else if i = lo then R lo - 1 else R i⟩ := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, run_add, run_one, run_one,
    step_dec_pos (P := syncDec hi lo) (b := 3) rfl hH,
    step_dec_pos (P := syncDec hi lo) (p := 1) (a := 0) (b := 2) rfl
      (by rwa [Function.update_of_ne hne.symm])]
  refine congrArg _ (funext fun i => ?_)
  simp only [Function.update_apply]
  split_ifs <;> simp_all

private theorem run_syncDec {hi lo : Fin k} (hne : hi ≠ lo) (regs : Fin k → ℕ) :
    ∀ j ≤ min (regs hi) (regs lo),
      run (syncDec hi lo) ⟨0, regs⟩ (2 * j) = ⟨0, syncDecState hi lo regs j⟩ := by
  intro j
  induction j with
  | zero =>
    intro _
    refine congrArg _ (funext fun i => ?_)
    simp only [syncDecState]
    split_ifs <;> simp_all
  | succ j ih =>
    intro hj
    have hvH : syncDecState hi lo regs j hi = regs hi - j := by simp [syncDecState]
    have hvL : syncDecState hi lo regs j lo = regs lo - j := by simp [syncDecState, hne.symm]
    rw [show 2 * (j + 1) = 2 * j + 2 by omega, run_add, ih (by omega),
      run_syncDec_body hne _ (by rw [hvH]; omega) (by rw [hvL]; omega)]
    refine congrArg _ (funext fun i => ?_)
    simp only [syncDecState]
    split_ifs <;> simp_all <;> omega

theorem realises_syncDec {hi lo : Fin k} (hne : hi ≠ lo) :
    Realises (syncDec hi lo) fun regs i =>
      if i = hi then regs hi - regs lo else if i = lo then regs lo - regs hi else regs i := by
  intro regs
  have hstate : ∀ j, syncDecState hi lo regs j hi = regs hi - j := by
    intro j; simp [syncDecState]
  have hstateL : ∀ j, syncDecState hi lo regs j lo = regs lo - j := by
    intro j; simp [syncDecState, hne.symm]
  by_cases hle : regs hi ≤ regs lo
  · -- `hi` runs out first: the loop exits on its own zero test.
    refine ⟨2 * regs hi + 1, fun m hm => ?_, ?_⟩
    · obtain ⟨j, c, hc, rfl⟩ : ∃ j c, c < 2 ∧ m = 2 * j + c :=
        ⟨m / 2, m % 2, Nat.mod_lt _ (by omega), by omega⟩
      rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl
      · rw [Nat.add_zero, run_syncDec hne regs j (by omega)]
        simp [syncDec]
      · rw [run_add, run_syncDec hne regs j (by omega), run_one,
          step_dec_pos (P := syncDec hi lo) (b := 3) rfl (by rw [hstate]; omega)]
        simp [syncDec]
    · rw [run_add, run_syncDec hne regs (regs hi) (by omega), run_one,
        step_dec_zero (P := syncDec hi lo) (a := 1) rfl (by rw [hstate]; omega),
        show (syncDec hi lo).length = 3 from rfl]
      refine congrArg _ (funext fun i => ?_)
      simp only [syncDecState]
      split_ifs <;> simp_all
  · -- `lo` runs out first: the turn that discovers it must give `hi` its decrement back.
    refine ⟨2 * regs lo + 3, fun m hm => ?_, ?_⟩
    · obtain ⟨j, c, hc, rfl⟩ : ∃ j c, c < 2 ∧ m = 2 * j + c :=
        ⟨m / 2, m % 2, Nat.mod_lt _ (by omega), by omega⟩
      rcases (show j ≤ regs lo ∨ j = regs lo + 1 by omega) with hjL | rfl
      · rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl
        · rw [Nat.add_zero, run_syncDec hne regs j (by omega)]
          simp [syncDec]
        · rw [run_add, run_syncDec hne regs j (by omega), run_one,
            step_dec_pos (P := syncDec hi lo) (b := 3) rfl (by rw [hstate]; omega)]
          simp [syncDec]
      · have hc0 : c = 0 := by omega
        subst hc0
        rw [show 2 * (regs lo + 1) + 0 = 2 * regs lo + 1 + 1 by omega, run_add, run_add,
          run_syncDec hne regs (regs lo) (by omega), run_one, run_one,
          step_dec_pos (P := syncDec hi lo) (regs := syncDecState hi lo regs (regs lo))
            (b := 3) rfl
            (by rw [hstate]; omega),
          step_dec_zero (P := syncDec hi lo) (p := 1) (a := 0) (b := 2) rfl
            (by rw [Function.update_of_ne hne.symm, hstateL]; omega)]
        simp [syncDec]
    · rw [show 2 * regs lo + 3 = 2 * regs lo + 1 + 1 + 1 by omega, run_add, run_add, run_add,
        run_syncDec hne regs (regs lo) (by omega), run_one, run_one, run_one,
        step_dec_pos (P := syncDec hi lo) (regs := syncDecState hi lo regs (regs lo)) (b := 3)
          rfl (by rw [hstate]; omega),
        step_dec_zero (P := syncDec hi lo) (p := 1) (a := 0) (b := 2) rfl
          (by rw [Function.update_of_ne hne.symm, hstateL]; omega),
        step_inc (P := syncDec hi lo) (p := 2) (a := 3) rfl,
        show (syncDec hi lo).length = 3 from rfl]
      refine congrArg _ (funext fun i => ?_)
      simp only [Function.update_apply, syncDecState]
      split_ifs <;> simp_all <;> omega

/-- Compare `a` and `b`, leaving both residuals: `lo = b - a` and `hi = a - b`.

`a` and `b` are untouched, `lo` and `hi` are overwritten, and `tmp` is returned at zero.

Note the absence of a `b ≠ hi` hypothesis, which the other eight distinctness conditions might
lead one to expect. It is genuinely unnecessary: `b` is read into `lo` before `hi` is written, so
if `b` and `hi` coincide the statement's `i = hi` branch describes what happens and the `regs b`
on the right still refers to the original contents. `a ≠ lo` is *not* similarly droppable — there
the overwrite happens before the read. -/
def compare (a b lo hi tmp : Fin k) : Program k :=
  seq (copy b lo tmp) (seq (copy a hi tmp) (syncDec hi lo))

theorem realises_compare {a b lo hi tmp : Fin k} (hlh : lo ≠ hi) (hlt : lo ≠ tmp)
    (hht : hi ≠ tmp) (hal : a ≠ lo) (hah : a ≠ hi) (hat : a ≠ tmp) (hbl : b ≠ lo)
    (hbt : b ≠ tmp) :
    Realises (compare a b lo hi tmp) fun regs i =>
      if i = lo then regs b - regs a else if i = hi then regs a - regs b
        else if i = tmp then 0 else regs i := by
  refine (((realises_copy hbl hbt hlt).seq
    ((realises_copy hah hat hht).seq (realises_syncDec hlh.symm))).congr fun regs => ?_)
  funext i
  split_ifs <;> simp_all


/-! ## Draining in place

A `dec` whose positive branch targets its own position is a loop that empties one register and
falls through. It is the shape every branch of a hand-laid-out program uses to clean up, and
unlike `clear` it is not a standalone program: it sits at a fixed position inside a larger one,
so it is stated against an arbitrary `P` and position. -/

/-- Partway through draining: after `m` turns the register is down by `m` and control has not
moved. -/
theorem run_drain_partial {P : Program k} {r : Fin k} {p e : ℕ}
    (hp : P[p]? = some (.dec r p e)) (regs : Fin k → ℕ) :
    ∀ m ≤ regs r, run P ⟨p, regs⟩ m = ⟨p, Function.update regs r (regs r - m)⟩ := by
  intro m
  induction m with
  | zero =>
    intro _
    refine congrArg _ (funext fun i => ?_)
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  | succ m ih =>
    intro hm
    rw [show m + 1 = m + 1 from rfl, run_add, ih (by omega), run_one,
      step_dec_pos (P := P) hp (by rw [Function.update_self]; omega)]
    refine congrArg _ (funext fun i => ?_)
    simp only [Function.update_apply]
    split_ifs <;> omega

/-- Draining takes one turn per unit plus the turn that finds zero, then falls through to `e`. -/
theorem run_drain {P : Program k} {r : Fin k} {p e : ℕ} (hp : P[p]? = some (.dec r p e))
    (regs : Fin k → ℕ) :
    run P ⟨p, regs⟩ (regs r + 1) = ⟨e, Function.update regs r 0⟩ := by
  rw [run_add, run_drain_partial hp regs _ (Nat.le_refl _), run_one,
    step_dec_zero (P := P) hp (by rw [Function.update_self]; omega)]
  refine congrArg _ (funext fun i => ?_)
  simp only [Function.update_apply]
  split_ifs <;> simp_all

end RegisterMachine

end Hilbert10


/- Source: Hilbert10.Internal.ForMathlib.PairingEnumeration, Hilbert10 v2.3.0, Apache-2.0. -/
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# The pairing enumeration has a successor function

`Nat.pair` and `Nat.unpair` are stated with multiplication and `Nat.sqrt`. Taking those
definitions at face value would make a register-machine implementation a verified-arithmetic
project: a multiplier, a square root, and their correctness proofs.

But the pairing is an *enumeration* of `ℕ × ℕ`, and enumerations have successors. `pairNext` is
that successor, and the theorems below say it is correct:

```lean
Nat.pair (pairNext p).1 (pairNext p).2 = Nat.pair p.1 p.2 + 1
pairNext^[n] (0, 0) = Nat.unpair n
```

Neither statement mentions a square root, and neither proof needs one — `pairNext` is built from
comparison, increment and zeroing alone.

## Why this shape

The consumer is #51, which compiles `Nat.unpair` and `Nat.pair` into register machines.

`unpair n` becomes `pairNext` iterated `n` times from `(0, 0)`: a counted loop.

`pair a b` becomes the enumeration run until the state is `(a, b)`, counting steps.
`iterate_pairNext_pair` is what makes that terminate — after exactly `Nat.pair a b` steps the
state *is* `(a, b)` — so termination is proved directly rather than through a general unbounded
search, which would make #51 depend on the `rfind'` compiler it is supposed to precede.

Self-contained, and a plausible mathlib addition: nothing here depends on the rest of this
development. Tracked for upstreaming in #37.

## The enumeration

Values `s ^ 2 .. s ^ 2 + 2 * s` form the shell `max a b = s`: first `(a, s)` for `a < s`, then
`(s, b)` for `b ≤ s`. `pairNext` walks that, and rolls over from `(s, s)` to `(0, s + 1)`.
-/

namespace Nat

/-- The successor in the pairing enumeration: the unique step from `p` to the pair whose code is
one greater. -/
def pairNext : ℕ × ℕ → ℕ × ℕ
  | (a, b) =>
      if a < b then (if a + 1 < b then (a + 1, b) else (b, 0))
      else if a = b then (0, a + 1)
      else (a, b + 1)

/-- **`pairNext` is the successor.** Proved by four cases on the shell position; no square root
and no reasoning about `Nat.sqrt` appears. -/
theorem pair_pairNext (p : ℕ × ℕ) :
    Nat.pair (pairNext p).1 (pairNext p).2 = Nat.pair p.1 p.2 + 1 := by
  obtain ⟨a, b⟩ := p
  rcases lt_trichotomy a b with h | h | h
  · by_cases h2 : a + 1 < b
    · rw [show pairNext (a, b) = (a + 1, b) by simp [pairNext, h, h2]]
      simp only [Nat.pair, if_pos h, if_pos h2]
      ring
    · have hb : b = a + 1 := by omega
      subst hb
      rw [show pairNext (a, a + 1) = (a + 1, 0) by simp [pairNext]]
      simp only [Nat.pair, if_pos h, if_neg (by omega : ¬ a + 1 < 0)]
      ring
  · subst h
    rw [show pairNext (a, a) = (0, a + 1) by simp [pairNext]]
    simp only [Nat.pair, if_pos (by omega : (0 : ℕ) < a + 1), if_neg (by omega : ¬ a < a)]
    ring
  · have hnlt : ¬ a < b := by omega
    have hne : ¬ a = b := by omega
    rw [show pairNext (a, b) = (a, b + 1) by simp [pairNext, hnlt, hne]]
    simp only [Nat.pair, if_neg (by omega : ¬ a < b + 1), if_neg (by omega : ¬ a < b)]
    ring

/-- **The `q`th pair of the enumeration has code `q`.** The counted-loop and
terminating-enumeration machines both need this, the second in the contrapositive form
`iterate_pairNext_ne_of_lt`. -/
theorem pair_iterate_pairNext (q : ℕ) :
    Nat.pair (pairNext^[q] (0, 0)).1 (pairNext^[q] (0, 0)).2 = q := by
  induction q with
  | zero => rfl
  | succ q ih => rw [Function.iterate_succ_apply', pair_pairNext, ih]

/-- Iterating from the origin enumerates the pairs in code order. -/
theorem iterate_pairNext (n : ℕ) : pairNext^[n] (0, 0) = Nat.unpair n := by
  conv_rhs => rw [← pair_iterate_pairNext n]
  rw [Nat.unpair_pair]

/-- **No early match.** Before step `Nat.pair a b` the enumeration has not reached `(a, b)`, so a
machine that walks it until its state matches stops exactly there. -/
theorem iterate_pairNext_ne_of_lt {q a b : ℕ} (h : q < Nat.pair a b) :
    pairNext^[q] (0, 0) ≠ (a, b) := by
  intro hq
  rw [← pair_iterate_pairNext q, hq] at h
  exact Nat.lt_irrefl _ h

/-- **The termination certificate for the `pair` direction.** Enumerating from the origin reaches
`(a, b)` after exactly `Nat.pair a b` steps, so a machine that walks the enumeration until its
state matches halts, and does so without an unbounded search. -/
theorem iterate_pairNext_pair (a b : ℕ) : pairNext^[Nat.pair a b] (0, 0) = (a, b) := by
  rw [iterate_pairNext, Nat.unpair_pair]

/-! ## Regression checks against the definitions -/

example : pairNext^[5] (0, 0) = (1, 2) := by decide
example : Nat.pair 1 2 = 5 := by decide
example : pairNext (2, 2) = (0, 3) := by decide

end Nat


/- Source: Hilbert10.Internal.RegisterMachinePairing, Hilbert10 v2.3.0, Apache-2.0. -/
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# The pairing enumeration as a register machine

Issue #51, step 3. `pairNextMachine` advances a pair of registers one place along `Nat.pair`'s
enumeration, and is proved against the semantic `Nat.pairNext`.

## Roles, not parameters

This machine fixes a `Fin 5` layout — `0 = a`, `1 = b`, `2 = lo`, `3 = hi`, `4 = tmp` — rather
than taking five register arguments with ten distinctness hypotheses. Callers place it in a
larger register file with `renameRegs` (#39) or `CleanPartComputesUnary.call`, supplying the
injection themselves. That is still no allocator, and it keeps the statement readable.

## The finishing program

After `compare` the registers hold `lo = b - a` and `hi = a - b`, and one branch on those two
settles all four cases of `pairNext`:

| condition | result |
|---|---|
| `lo ≥ 2` | `(a + 1, b)` |
| `lo = 1` | `(a + 1, 0)`, which is `(b, 0)` since `b = a + 1` |
| `lo = 0`, `hi = 0` | `(0, a + 1)` |
| `lo = 0`, `hi > 0` | `(a, b + 1)` |

The `lo = 1` case is the shell rollover, and it needs no copy: `a + 1` *is* `b` there.

The program does its own cleanup by consuming the residuals rather than calling `clear`, so it is
one flat ten-instruction list with no control-flow combinator, no jump gadget and no scratch
beyond what `compare` already used. Each branch ends by draining a register in place, which is
what `run_drain` is for.
-/

namespace Hilbert10

namespace RegisterMachine

/-- Turn `compare`'s residuals into `pairNext`'s answer.

Positions 2, 5, 6 and 9 are drains: a `dec` whose positive branch is its own position. -/
def pairNextFinish : Program 5 :=
  [.dec 2 1 4,   -- 0: lo > 0 → 1;  lo = 0 → 4
   .dec 2 2 3,   -- 1: lo ≥ 2 → 2;  lo = 1 → 3
   .dec 2 2 8,   -- 2: drain lo → 8
   .inc 0 9,     -- 3: a++ → 9
   .dec 3 5 6,   -- 4: hi > 0 → 5;  hi = 0 → 6
   .dec 3 5 7,   -- 5: drain hi → 7
   .dec 0 6 7,   -- 6: drain a → 7
   .inc 1 10,    -- 7: b++, exit
   .inc 0 10,    -- 8: a++, exit
   .dec 1 9 10]  -- 9: drain b, exit

/-- The register file `pairNextFinish` produces, as a function of the one it is given. -/
def finishState (regs : Fin 5 → ℕ) : Fin 5 → ℕ :=
  if 2 ≤ regs 2 then fun i => if i = 0 then regs 0 + 1 else if i = 2 then 0 else regs i
  else if regs 2 = 1 then
    fun i => if i = 0 then regs 0 + 1 else if i = 1 then 0 else if i = 2 then 0 else regs i
  else if regs 3 = 0 then fun i => if i = 0 then 0 else if i = 1 then regs 1 + 1 else regs i
  else fun i => if i = 1 then regs 1 + 1 else if i = 3 then 0 else regs i

theorem realises_pairNextFinish : Realises pairNextFinish finishState := by
  intro regs
  by_cases h2 : 2 ≤ regs 2
  · -- `lo ≥ 2`: consume two, drain the rest, then `a++`
    have hL : regs 2 ≠ 0 := by omega
    have hpre : run pairNextFinish ⟨0, regs⟩ 2 =
        ⟨2, Function.update regs 2 (regs 2 - 2)⟩ := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, run_add, run_one, run_one,
        step_dec_pos (P := pairNextFinish) (p := 0) (a := 1) (b := 4) rfl hL,
        step_dec_pos (P := pairNextFinish) (p := 1) (a := 2) (b := 3) rfl
          (by rw [Function.update_self]; omega)]
      refine congrArg _ (funext fun i => ?_)
      simp only [Function.update_apply]
      split_ifs <;> omega
    have hdrain : run pairNextFinish ⟨2, Function.update regs 2 (regs 2 - 2)⟩
        (regs 2 - 2 + 1) = ⟨8, Function.update regs 2 0⟩ := by
      have h := run_drain (P := pairNextFinish) (r := 2) (p := 2) (e := 8) rfl
        (Function.update regs 2 (regs 2 - 2))
      rwa [Function.update_self, Function.update_idem] at h
    refine ⟨regs 2 + 2, fun m hm => ?_, ?_⟩
    · rcases (show m = 0 ∨ m = 1 ∨ (2 ≤ m ∧ m ≤ regs 2) ∨ m = regs 2 + 1 by omega)
        with rfl | rfl | ⟨hm2, hm3⟩ | rfl
      · simp [pairNextFinish]
      · rw [run_one, step_dec_pos (P := pairNextFinish) (p := 0) (a := 1) (b := 4) rfl hL]
        simp [pairNextFinish]
      · rw [show m = 2 + (m - 2) by omega, run_add, hpre,
          run_drain_partial (P := pairNextFinish) (r := 2) (p := 2) (e := 8) rfl _ (m - 2)
            (by rw [Function.update_self]; omega)]
        simp [pairNextFinish]
      · rw [show regs 2 + 1 = 2 + (regs 2 - 2 + 1) by omega, run_add, hpre, hdrain]
        simp [pairNextFinish]
    · rw [show regs 2 + 2 = 2 + (regs 2 - 2 + 1) + 1 by omega, run_add, run_add, hpre, hdrain,
        run_one, step_inc (P := pairNextFinish) (p := 8) (a := 10) rfl,
        show pairNextFinish.length = 10 from rfl]
      refine congrArg _ (funext fun i => ?_)
      simp only [finishState, if_pos h2, Function.update_apply]
      split_ifs <;> simp_all
  · by_cases h1 : regs 2 = 1
    · -- `lo = 1`: the shell rollover, `a++` and `b := 0`
      have hpre : run pairNextFinish ⟨0, regs⟩ 3 =
          ⟨9, Function.update (Function.update regs 2 0) 0 (regs 0 + 1)⟩ := by
        rw [show (3 : ℕ) = 1 + 1 + 1 from rfl, run_add, run_add, run_one, run_one, run_one,
          step_dec_pos (P := pairNextFinish) (p := 0) (a := 1) (b := 4) rfl (by omega),
          step_dec_zero (P := pairNextFinish) (p := 1) (a := 2) (b := 3) rfl
            (by rw [Function.update_self]; omega),
          step_inc (P := pairNextFinish) (p := 3) (a := 9) rfl]
        refine congrArg _ (funext fun i => ?_)
        simp only [Function.update_apply]
        split_ifs <;> simp_all
      have hdrain : run pairNextFinish
          ⟨9, Function.update (Function.update regs 2 0) 0 (regs 0 + 1)⟩ (regs 1 + 1) =
          ⟨10, Function.update
            (Function.update (Function.update regs 2 0) 0 (regs 0 + 1)) 1 0⟩ := by
        have h := run_drain (P := pairNextFinish) (r := 1) (p := 9) (e := 10) rfl
          (Function.update (Function.update regs 2 0) 0 (regs 0 + 1))
        rwa [show Function.update (Function.update regs 2 0) 0 (regs 0 + 1) 1 = regs 1 by
          simp] at h
      refine ⟨regs 1 + 4, fun m hm => ?_, ?_⟩
      · rcases (show m = 0 ∨ m = 1 ∨ m = 2 ∨ (3 ≤ m ∧ m ≤ regs 1 + 3) by omega)
          with rfl | rfl | rfl | ⟨hm3, hm4⟩
        · simp [pairNextFinish]
        · rw [run_one, step_dec_pos (P := pairNextFinish) (p := 0) (a := 1) (b := 4) rfl
            (by omega)]
          simp [pairNextFinish]
        · rw [show (2 : ℕ) = 1 + 1 from rfl, run_add, run_one, run_one,
            step_dec_pos (P := pairNextFinish) (p := 0) (a := 1) (b := 4) rfl (by omega),
            step_dec_zero (P := pairNextFinish) (p := 1) (a := 2) (b := 3) rfl
              (by rw [Function.update_self]; omega)]
          simp [pairNextFinish]
        · rw [show m = 3 + (m - 3) by omega, run_add, hpre,
            run_drain_partial (P := pairNextFinish) (r := 1) (p := 9) (e := 10) rfl _ (m - 3)
              (by rw [show Function.update (Function.update regs 2 0) 0 (regs 0 + 1) 1 = regs 1 by
                simp]; omega)]
          simp [pairNextFinish]
      · rw [show regs 1 + 4 = 3 + (regs 1 + 1) by omega, run_add, hpre, hdrain,
          show pairNextFinish.length = 10 from rfl]
        refine congrArg _ (funext fun i => ?_)
        simp only [finishState, if_neg h2, if_pos h1, Function.update_apply]
        split_ifs <;> simp_all
    · by_cases h3 : regs 3 = 0
      · -- `lo = 0`, `hi = 0`: the diagonal, `a := 0` and `b++`
        have hpre : run pairNextFinish ⟨0, regs⟩ 2 = ⟨6, regs⟩ := by
          rw [show (2 : ℕ) = 1 + 1 from rfl, run_add, run_one, run_one,
            step_dec_zero (P := pairNextFinish) (p := 0) (a := 1) (b := 4) rfl (by omega),
            step_dec_zero (P := pairNextFinish) (p := 4) (a := 5) (b := 6) rfl h3]
        have hdrain : run pairNextFinish ⟨6, regs⟩ (regs 0 + 1) =
            ⟨7, Function.update regs 0 0⟩ :=
          run_drain (P := pairNextFinish) (r := 0) (p := 6) (e := 7) rfl regs
        refine ⟨regs 0 + 4, fun m hm => ?_, ?_⟩
        · rcases (show m = 0 ∨ m = 1 ∨ (2 ≤ m ∧ m ≤ regs 0 + 2) ∨ m = regs 0 + 3 by omega)
            with rfl | rfl | ⟨hm2, hm3⟩ | rfl
          · simp [pairNextFinish]
          · rw [run_one, step_dec_zero (P := pairNextFinish) (p := 0) (a := 1) (b := 4) rfl
              (by omega)]
            simp [pairNextFinish]
          · rw [show m = 2 + (m - 2) by omega, run_add, hpre,
              run_drain_partial (P := pairNextFinish) (r := 0) (p := 6) (e := 7) rfl _ (m - 2)
                (by omega)]
            simp [pairNextFinish]
          · rw [show regs 0 + 3 = 2 + (regs 0 + 1) by omega, run_add, hpre, hdrain]
            simp [pairNextFinish]
        · rw [show regs 0 + 4 = 2 + (regs 0 + 1) + 1 by omega, run_add, run_add, hpre, hdrain,
            run_one, step_inc (P := pairNextFinish) (p := 7) (a := 10) rfl,
            show pairNextFinish.length = 10 from rfl]
          refine congrArg _ (funext fun i => ?_)
          simp only [finishState, if_neg h2, if_neg h1, if_pos h3, Function.update_apply]
          split_ifs <;> simp_all
      · -- `lo = 0`, `hi > 0`: below the diagonal, `b++`
        have hpre : run pairNextFinish ⟨0, regs⟩ 2 =
            ⟨5, Function.update regs 3 (regs 3 - 1)⟩ := by
          rw [show (2 : ℕ) = 1 + 1 from rfl, run_add, run_one, run_one,
            step_dec_zero (P := pairNextFinish) (p := 0) (a := 1) (b := 4) rfl (by omega),
            step_dec_pos (P := pairNextFinish) (p := 4) (a := 5) (b := 6) rfl h3]
        have hdrain : run pairNextFinish ⟨5, Function.update regs 3 (regs 3 - 1)⟩
            (regs 3 - 1 + 1) = ⟨7, Function.update regs 3 0⟩ := by
          have h := run_drain (P := pairNextFinish) (r := 3) (p := 5) (e := 7) rfl
            (Function.update regs 3 (regs 3 - 1))
          rwa [Function.update_self, Function.update_idem] at h
        refine ⟨regs 3 + 3, fun m hm => ?_, ?_⟩
        · rcases (show m = 0 ∨ m = 1 ∨ (2 ≤ m ∧ m ≤ regs 3 + 1) ∨ m = regs 3 + 2 by omega)
            with rfl | rfl | ⟨hm2, hm3⟩ | rfl
          · simp [pairNextFinish]
          · rw [run_one, step_dec_zero (P := pairNextFinish) (p := 0) (a := 1) (b := 4) rfl
              (by omega)]
            simp [pairNextFinish]
          · rw [show m = 2 + (m - 2) by omega, run_add, hpre,
              run_drain_partial (P := pairNextFinish) (r := 3) (p := 5) (e := 7) rfl _ (m - 2)
                (by rw [Function.update_self]; omega)]
            simp [pairNextFinish]
          · rw [show regs 3 + 2 = 2 + (regs 3 - 1 + 1) by omega, run_add, hpre, hdrain]
            simp [pairNextFinish]
        · rw [show regs 3 + 3 = 2 + (regs 3 - 1 + 1) + 1 by omega, run_add, run_add, hpre,
            hdrain, run_one, step_inc (P := pairNextFinish) (p := 7) (a := 10) rfl,
            show pairNextFinish.length = 10 from rfl]
          refine congrArg _ (funext fun i => ?_)
          simp only [finishState, if_neg h2, if_neg h1, if_neg h3, Function.update_apply]
          split_ifs <;> simp_all

/-! ## The machine -/

/-- One step along the pairing enumeration, on registers `0` and `1`. -/
def pairNextMachine : Program 5 := seq (compare 0 1 2 3 4) pairNextFinish

/-- **`pairNextMachine` realises `Nat.pairNext`.** Registers `0` and `1` become the components of
the successor pair; `2`, `3` and `4` come back at zero whatever they held.

The four `by_cases` fix which branch of `pairNext` applies *before* the register-by-register
comparison, rather than letting `split_ifs` enumerate the product of the two. That ordering is
not cosmetic: the other way round exhausts a million heartbeats. -/
theorem realises_pairNextMachine :
    Realises pairNextMachine fun regs i =>
      if i = 0 then (Nat.pairNext (regs 0, regs 1)).1
      else if i = 1 then (Nat.pairNext (regs 0, regs 1)).2
      else 0 := by
  refine ((realises_compare (a := 0) (b := 1) (lo := 2) (hi := 3) (tmp := 4)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)).seq realises_pairNextFinish).congr fun regs => ?_
  rw [finishState]
  simp only [Fin.reduceEq, if_true, if_false]
  by_cases h2 : 2 ≤ regs 1 - regs 0
  · rw [if_pos h2, show Nat.pairNext (regs 0, regs 1) = (regs 0 + 1, regs 1) by
      simp only [Nat.pairNext]
      rw [if_pos (show regs 0 < regs 1 by omega), if_pos (show regs 0 + 1 < regs 1 by omega)]]
    funext i
    fin_cases i <;> simp
    all_goals omega
  · rw [if_neg h2]
    by_cases h1 : regs 1 - regs 0 = 1
    · rw [if_pos h1, show Nat.pairNext (regs 0, regs 1) = (regs 0 + 1, 0) by
        simp only [Nat.pairNext]
        rw [if_pos (show regs 0 < regs 1 by omega), if_neg (show ¬ regs 0 + 1 < regs 1 by omega)]
        exact congrArg (fun x => (x, 0)) (by omega)]
      funext i
      fin_cases i <;> simp
      all_goals omega
    · rw [if_neg h1]
      by_cases h3 : regs 0 - regs 1 = 0
      · rw [if_pos h3, show Nat.pairNext (regs 0, regs 1) = (0, regs 0 + 1) by
          simp only [Nat.pairNext]
          rw [if_neg (show ¬ regs 0 < regs 1 by omega), if_pos (show regs 0 = regs 1 by omega)]]
        funext i
        fin_cases i <;> simp
        all_goals omega
      · rw [if_neg h3, show Nat.pairNext (regs 0, regs 1) = (regs 0, regs 1 + 1) by
          simp only [Nat.pairNext]
          rw [if_neg (show ¬ regs 0 < regs 1 by omega), if_neg (show ¬ regs 0 = regs 1 by omega)]]
        funext i
        fin_cases i <;> simp
        all_goals omega

end RegisterMachine

end Hilbert10


/- Source: Hilbert10.Internal.CleanScratch, Hilbert10 v2.3.0, Apache-2.0. -/
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# The clean-scratch calling convention

`PartComputesUnary` makes every register except `0` caller-owned: a machine must work from
arbitrary contents and give them back unchanged. That is the right contract for `zero`, `succ`
and for composition, but it is the wrong one for a machine that needs working storage.

A machine with counters has two bad options under it. Assuming the counters start at zero would
be a silent extra hypothesis, true of the callers we happen to write and invisible in the
statement. Saving and restoring arbitrary contents would be a large amount of work about a
question nobody asked.

So there is a second contract. The caller hands over a *clean* register file — input in `0`, the
rest zero — and gets one back in the same shape. `CleanPartComputesUnary` says exactly that.

## The call lemma

`CleanPartComputesUnary.call` is what makes the convention usable. Renaming along a
caller-supplied injection gives the callee a private scratch block that starts and ends zero,
while every register outside the block is preserved. Controller state therefore lives *outside*
the callee's image, which is the arrangement `prec` (#42) needs: a loop counter the callee
cannot see, and a callee that cannot leak into it.

The injection is still supplied by the caller, so this introduces no allocator — the standing
guard from #39.
-/

namespace Hilbert10

namespace RegisterMachine

variable {k : ℕ}

/-- The register file a clean machine is called with, and returns: the value in register `0` and
zero everywhere else. -/
def unaryConfig (k : ℕ) (x : ℕ) : Fin (k + 1) → ℕ := Function.update (fun _ => 0) 0 x

@[simp] theorem unaryConfig_zero (k x : ℕ) : unaryConfig k x 0 = x := by simp [unaryConfig]

theorem unaryConfig_of_ne {x : ℕ} {i : Fin (k + 1)} (h : i ≠ 0) : unaryConfig k x i = 0 := by
  simp [unaryConfig, h]

@[simp] theorem update_unaryConfig (k x y : ℕ) :
    Function.update (unaryConfig k x) 0 y = unaryConfig k y := by
  simp [unaryConfig, Function.update_idem]

/-- `P` computes `f` from a clean register file to a clean register file. -/
def CleanPartComputesUnary (P : Program (k + 1)) (f : ℕ →. ℕ) : Prop :=
  ∀ x : ℕ,
    (∀ y ∈ f x, ∃ n, (∀ m < n, (run P ⟨0, unaryConfig k x⟩ m).pc < P.length) ∧
        run P ⟨0, unaryConfig k x⟩ n = ⟨P.length, unaryConfig k y⟩) ∧
      (Halts P ⟨0, unaryConfig k x⟩ → (f x).Dom)

theorem CleanPartComputesUnary.exit {P : Program (k + 1)} {f} (h : CleanPartComputesUnary P f)
    {x y : ℕ} (hy : y ∈ f x) :
    ∃ n, (∀ m < n, (run P ⟨0, unaryConfig k x⟩ m).pc < P.length) ∧
      run P ⟨0, unaryConfig k x⟩ n = ⟨P.length, unaryConfig k y⟩ :=
  (h x).1 y hy

theorem CleanPartComputesUnary.dom {P : Program (k + 1)} {f} (h : CleanPartComputesUnary P f)
    {x : ℕ} (hh : Halts P ⟨0, unaryConfig k x⟩) : (f x).Dom :=
  (h x).2 hh

/-- Halting from a clean register file is convergence. As in `PartRealises`, only one direction
is taken as the definition; the other follows from the exit clause. -/
theorem CleanPartComputesUnary.halts_iff {P : Program (k + 1)} {f}
    (h : CleanPartComputesUnary P f) (x : ℕ) :
    Halts P ⟨0, unaryConfig k x⟩ ↔ (f x).Dom := by
  refine ⟨h.dom, fun hd => ?_⟩
  obtain ⟨n, _, hn⟩ := h.exit (Part.get_mem hd)
  exact ⟨n, by rw [hn]; exact Nat.le_refl _⟩

theorem CleanPartComputesUnary.congr {P : Program (k + 1)} {f g : ℕ →. ℕ}
    (h : CleanPartComputesUnary P f) (hfg : ∀ x, f x = g x) : CleanPartComputesUnary P g := by
  intro x
  rw [← hfg]
  exact h x

/-- The framed contract is the stronger one: a machine that tolerates arbitrary scratch in
particular tolerates clean scratch. -/
theorem PartComputesUnary.toClean {P : Program (k + 1)} {f : ℕ →. ℕ}
    (h : PartComputesUnary P f) : CleanPartComputesUnary P f := by
  intro x
  refine ⟨fun y hy => ?_, fun hh => ?_⟩
  · have hy' : y ∈ f (unaryConfig k x 0) := by simpa using hy
    obtain ⟨n, hin, hex⟩ := h.exit (regs := unaryConfig k x)
      (Part.mem_map (fun z => Function.update (unaryConfig k x) 0 z) hy')
    exact ⟨n, hin, by rw [hex]; simp⟩
  · have hd : (f (unaryConfig k x 0)).Dom := h.dom hh
    simpa using hd

/-- Clean contracts compose, by the same splicing argument as `PartRealises.append`. -/
theorem CleanPartComputesUnary.comp {P Q : Program (k + 1)} {inner outer : ℕ →. ℕ}
    (hP : CleanPartComputesUnary P inner) (hQ : CleanPartComputesUnary Q outer) :
    CleanPartComputesUnary (P ++ shiftJumps P.length Q) fun x => inner x >>= outer := by
  intro x
  refine ⟨fun z hz => ?_, fun hh => ?_⟩
  · obtain ⟨y, hy, hz'⟩ := Part.mem_bind_iff.mp hz
    obtain ⟨nP, hPin, hPex⟩ := hP.exit hy
    obtain ⟨nQ, hQin, hQex⟩ := hQ.exit hz'
    exact ⟨nP + nQ, join_exit hPin hPex hQin hQex⟩
  · have hPd : (inner x).Dom := hP.dom (halts_prefix_of_halts_append hh)
    have hy : (inner x).get hPd ∈ inner x := Part.get_mem hPd
    obtain ⟨nP, hPin, hPex⟩ := hP.exit hy
    obtain ⟨N, hN⟩ := hh
    have hNge : nP ≤ N := by
      by_contra hlt
      rw [run_append_of_lt fun j hj => hPin j (Nat.lt_trans hj (Nat.not_le.mp hlt))] at hN
      exact absurd hN (Nat.not_le.mpr (Nat.lt_of_lt_of_le (hPin N (Nat.not_le.mp hlt)) (by simp)))
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hNge
    rw [run_join hPin hPex j] at hN
    have hQh : Halts Q ⟨0, unaryConfig k ((inner x).get hPd)⟩ := by
      refine ⟨j, ?_⟩
      have hle : (P ++ shiftJumps P.length Q).length
          ≤ (run Q ⟨0, unaryConfig k ((inner x).get hPd)⟩ j).pc + P.length := hN
      rw [length_append_shiftJumps] at hle
      exact show Q.length ≤ (run Q ⟨0, unaryConfig k ((inner x).get hPd)⟩ j).pc by omega
    exact Part.dom_iff_mem.mpr ⟨_, Part.mem_bind hy (Part.get_mem (hQ.dom hQh))⟩

/-- **Calling a clean machine from a wider register file.**

The caller picks the injection, seeds `σ 0` with the input and zeroes the rest of the image. On
return the image holds the output in `σ 0` and zeros elsewhere, and every register outside the
image is exactly as it was — so the caller may keep controller state there and the callee cannot
disturb it. -/
theorem CleanPartComputesUnary.call {k' : ℕ} {P : Program (k + 1)} {f : ℕ →. ℕ}
    (h : CleanPartComputesUnary P f) {σ : Fin (k + 1) → Fin (k' + 1)} (hσ : Function.Injective σ)
    {regs : Fin (k' + 1) → ℕ} {x : ℕ} (hx : regs (σ 0) = x)
    (hclean : ∀ i, i ≠ 0 → regs (σ i) = 0) :
    (∀ y ∈ f x, ∃ n out,
        (∀ m < n, (run (renameRegs σ P) ⟨0, regs⟩ m).pc < (renameRegs σ P).length) ∧
        run (renameRegs σ P) ⟨0, regs⟩ n = ⟨(renameRegs σ P).length, out⟩ ∧
        out (σ 0) = y ∧ (∀ i, i ≠ 0 → out (σ i) = 0) ∧
        ∀ r, (∀ i, r ≠ σ i) → out r = regs r) ∧
      (Halts (renameRegs σ P) ⟨0, regs⟩ → (f x).Dom) := by
  have hcomp : regs ∘ σ = unaryConfig k x := by
    funext i
    by_cases hi : i = 0
    · subst hi; simpa using hx
    · simpa [unaryConfig_of_ne hi] using hclean i hi
  have hren : Renamed σ ⟨0, unaryConfig k x⟩ ⟨0, regs⟩ := ⟨rfl, fun i => congrFun hcomp i⟩
  refine ⟨fun y hy => ?_, fun hh => h.dom ((halts_renameRegs_iff hσ hren).mp hh)⟩
  obtain ⟨n, hin, hex⟩ := h.exit hy
  have hexr : (run P ⟨0, unaryConfig k x⟩ n).regs = unaryConfig k y := by rw [hex]
  refine ⟨n, (run (renameRegs σ P) ⟨0, regs⟩ n).regs, fun m hm => ?_, ?_, ?_, fun i hi => ?_,
    fun r hr => ?_⟩
  · rw [(hren.run (P := P) hσ m).pc, length_renameRegs]
    exact hin m hm
  · have hpc : (run (renameRegs σ P) ⟨0, regs⟩ n).pc = (renameRegs σ P).length := by
      rw [(hren.run (P := P) hσ n).pc, hex, length_renameRegs]
    rw [← hpc]
  · rw [(hren.run (P := P) hσ n).regs 0, hexr, unaryConfig_zero]
  · rw [(hren.run (P := P) hσ n).regs i, hexr, unaryConfig_of_ne hi]
  · exact regs_run_renameRegs_of_ne hr n


/-! ## The register file a call produces

`call` gives the image and the complement as separate pointwise clauses. Every controller that
makes a call would then repeat the same `funext` split into the image of `σ` and its complement,
so the two clauses are packaged here into one function equality instead. -/

/-- The register file after calling a clean machine through `σ` and getting `y`: the block along
`σ` holds `unaryConfig _ y`, and everything outside it is untouched. -/
noncomputable def callState {k k' : ℕ} (σ : Fin (k + 1) → Fin (k' + 1))
    (regs : Fin (k' + 1) → ℕ) (y : ℕ) : Fin (k' + 1) → ℕ :=
  Function.extend σ (unaryConfig k y) regs

variable {k' : ℕ} {σ : Fin (k + 1) → Fin (k' + 1)}

@[simp] theorem callState_apply (hσ : Function.Injective σ) (regs : Fin (k' + 1) → ℕ) (y : ℕ)
    (i : Fin (k + 1)) : callState σ regs y (σ i) = unaryConfig k y i :=
  hσ.extend_apply _ _ _

theorem callState_zero (hσ : Function.Injective σ) (regs : Fin (k' + 1) → ℕ) (y : ℕ) :
    callState σ regs y (σ 0) = y := by rw [callState_apply hσ, unaryConfig_zero]

theorem callState_of_ne (hσ : Function.Injective σ) (regs : Fin (k' + 1) → ℕ) (y : ℕ)
    {i : Fin (k + 1)} (hi : i ≠ 0) : callState σ regs y (σ i) = 0 := by
  rw [callState_apply hσ, unaryConfig_of_ne hi]

theorem callState_of_not_mem (regs : Fin (k' + 1) → ℕ) (y : ℕ) {r : Fin (k' + 1)}
    (hr : ∀ i, r ≠ σ i) : callState σ regs y r = regs r :=
  Function.extend_apply' _ _ _ (by rintro ⟨i, rfl⟩; exact hr i rfl)

/-- **The exit of a call, as one register file.** -/
theorem CleanPartComputesUnary.call_exit {P : Program (k + 1)} {f : ℕ →. ℕ}
    (h : CleanPartComputesUnary P f) (hσ : Function.Injective σ) {regs : Fin (k' + 1) → ℕ}
    {x : ℕ} (hx : regs (σ 0) = x) (hclean : ∀ i, i ≠ 0 → regs (σ i) = 0) {y : ℕ}
    (hy : y ∈ f x) :
    ∃ n, (∀ m < n, (run (renameRegs σ P) ⟨0, regs⟩ m).pc < (renameRegs σ P).length) ∧
      run (renameRegs σ P) ⟨0, regs⟩ n =
        ⟨(renameRegs σ P).length, callState σ regs y⟩ := by
  classical
  obtain ⟨n, out, hin, hex, h0, hne, hoff⟩ := (h.call hσ hx hclean).1 y hy
  refine ⟨n, hin, ?_⟩
  rw [hex]
  refine congrArg _ (funext fun r => ?_)
  by_cases hrng : ∃ i, r = σ i
  · obtain ⟨i, rfl⟩ := hrng
    rw [callState_apply hσ]
    by_cases hi : i = 0
    · subst hi; rw [h0, unaryConfig_zero]
    · rw [hne i hi, unaryConfig_of_ne hi]
  · push Not at hrng
    rw [callState_of_not_mem regs y hrng, hoff r hrng]

/-- **Halting of a call.** -/
theorem CleanPartComputesUnary.call_halts_iff {P : Program (k + 1)} {f : ℕ →. ℕ}
    (h : CleanPartComputesUnary P f) (hσ : Function.Injective σ) {regs : Fin (k' + 1) → ℕ}
    {x : ℕ} (hx : regs (σ 0) = x) (hclean : ∀ i, i ≠ 0 → regs (σ i) = 0) :
    Halts (renameRegs σ P) ⟨0, regs⟩ ↔ (f x).Dom := by
  refine ⟨(h.call hσ hx hclean).2, fun hd => ?_⟩
  obtain ⟨n, _, hn⟩ := h.call_exit hσ hx hclean (Part.get_mem hd)
  exact ⟨n, by rw [hn]; exact Nat.le_refl _⟩

/-! ## The graph relation

What #21 arithmetises: a *trace-level* statement about the machine, with no reference to the
function it computes. `accepts_iff` is the bridge, and it is the only place the two meet. -/

/-- `P` takes the clean configuration for `x` to the clean configuration for `y`, exactly. -/
def Accepts (P : Program (k + 1)) (x y : ℕ) : Prop :=
  ∃ n, (∀ m < n, (run P ⟨0, unaryConfig k x⟩ m).pc < P.length) ∧
    run P ⟨0, unaryConfig k x⟩ n = ⟨P.length, unaryConfig k y⟩

theorem CleanPartComputesUnary.accepts_iff {P : Program (k + 1)} {f : ℕ →. ℕ}
    (h : CleanPartComputesUnary P f) (x y : ℕ) : Accepts P x y ↔ y ∈ f x := by
  constructor
  · rintro ⟨n, hin, hex⟩
    have hdom : (f x).Dom := h.dom ⟨n, by rw [hex]; exact Nat.le_refl _⟩
    obtain ⟨n', hin', hex'⟩ := h.exit (Part.get_mem hdom)
    obtain ⟨-, hoo⟩ := exit_unique hin hex hin' hex'
    have hy : y = (f x).get hdom := by simpa using congrFun hoo 0
    rw [hy]
    exact Part.get_mem hdom
  · intro hy
    exact h.exit hy

/-- **Width lifting for the clean contract.** The clean analogue of
`PartComputesUnary.renameRegs`, and a direct consequence of `call`. Named `widen` rather than
`renameRegs` because a theorem in the `CleanPartComputesUnary` namespace shadows the top-level
`renameRegs` inside every other theorem in that namespace: it is what lets two machines
obtained independently be brought to a common width before composing. -/
theorem CleanPartComputesUnary.widen {P : Program (k + 1)} {f : ℕ →. ℕ}
    (h : CleanPartComputesUnary P f) {σ : Fin (k + 1) → Fin (k' + 1)}
    (hσ : Function.Injective σ) (hσ0 : σ 0 = 0) :
    CleanPartComputesUnary (RegisterMachine.renameRegs σ P) f := by
  classical
  have hne : ∀ i, i ≠ 0 → σ i ≠ 0 := fun i hi hc => hi (hσ (hc.trans hσ0.symm))
  intro x
  have hx : unaryConfig k' x (σ 0) = x := by rw [hσ0, unaryConfig_zero]
  have hcl : ∀ i, i ≠ 0 → unaryConfig k' x (σ i) = 0 := fun i hi =>
    unaryConfig_of_ne (hne i hi)
  refine ⟨fun y hy => ?_, fun hh => (h.call_halts_iff hσ hx hcl).mp hh⟩
  obtain ⟨n, hin, hex⟩ := h.call_exit hσ hx hcl hy
  refine ⟨n, hin, ?_⟩
  rw [hex]
  refine congrArg _ (funext fun r => ?_)
  by_cases hrng : ∃ i, r = σ i
  · obtain ⟨i, rfl⟩ := hrng
    rw [callState_apply hσ]
    by_cases hi : i = 0
    · subst hi; rw [hσ0, unaryConfig_zero, unaryConfig_zero]
    · rw [unaryConfig_of_ne hi, unaryConfig_of_ne (hne i hi)]
  · push Not at hrng
    rw [callState_of_not_mem _ _ hrng,
      unaryConfig_of_ne (by rintro rfl; exact hrng 0 hσ0.symm),
      unaryConfig_of_ne (by rintro rfl; exact hrng 0 hσ0.symm)]

end RegisterMachine

end Hilbert10


/- Source: Hilbert10.Internal.RegisterMachineUnpair, Hilbert10 v2.3.0, Apache-2.0. -/
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# `Nat.unpair` as a counted loop

Issue #51, step 4. Iterating `pairNextMachine` exactly `n` times from `(0, 0)` computes
`Nat.unpair n`, by `Nat.iterate_pairNext`. There is no search here and so nothing to prove sound
about one: the loop runs a known number of times.

## Layout

`Fin 6`, with `0` the remaining count and `1`–`5` the `pairNextMachine` block renamed along
`Fin.succ`:

| register | role |
|---|---|
| `0` | remaining iterations |
| `1`, `2` | the candidate pair |
| `3`, `4`, `5` | `pairNextMachine`'s `lo`, `hi`, `tmp` |

```
0          decrement the count; positive → body, zero → exit
1 … L      the relocated pairNextMachine
L + 1      decrement register 5; both targets 0
```

The last instruction is a jump back to the top. It is safe *because* of what
`realises_pairNextMachine` says: register `5` is zero on exit, so the decrement has no effect and
both branches lead to `0`. A general jump combinator would have been the alternative, and this
loop is the only place one would be needed.

## Two things the proof does deliberately

The invariant counts **logical iterations**, not machine steps. Each turn of `pairNextMachine`
runs for an input-dependent time, so the step counts are accumulated as existentials through
`run_add` rather than computed.

`Nat.pairNext^[q] (0, 0)` stays **opaque** for the whole induction, and `Nat.iterate_pairNext` is
applied once at `q = n`. Unfolding `pairNext` while simultaneously comparing `Fin 6` register
files would recreate the branch-product blow-up that #51 step 3 had to work around.
-/

namespace Hilbert10

namespace RegisterMachine

variable {k : ℕ}

/-! ## The loop -/

/-- `pairNextMachine` moved off register `0`, which the loop keeps for its counter. -/
def unpairBody : Program 6 := renameRegs Fin.succ pairNextMachine

theorem realises_unpairBody : Realises unpairBody fun regs i =>
    if i = 0 then regs 0
    else if i = 1 then (Nat.pairNext (regs 1, regs 2)).1
    else if i = 2 then (Nat.pairNext (regs 1, regs 2)).2
    else 0 := by
  refine realises_pairNextMachine.renameRegs (Fin.succ_injective 5) ?_ ?_
  · intro regs i
    fin_cases i <;> simp
  · intro regs r hr
    rcases Fin.eq_zero_or_eq_succ r with rfl | ⟨i, rfl⟩
    · simp
    · exact absurd rfl (hr i)

/-- Count down, advancing the candidate pair each turn. -/
def unpairLoop : Program 6 :=
  [Instr.dec 0 1 (unpairBody.length + 2)] ++ shiftJumps 1 unpairBody ++ [Instr.dec 5 0 0]

theorem length_unpairLoop : unpairLoop.length = unpairBody.length + 2 := by
  simp [unpairLoop]

/-- One turn: decrement the counter, advance the pair, jump back. -/
private theorem run_turn (R : Fin 6 → ℕ) (hR : R 0 ≠ 0) :
    ∃ n, (∀ m < n, (run unpairLoop ⟨0, R⟩ m).pc < unpairLoop.length) ∧
      run unpairLoop ⟨0, R⟩ n = ⟨0, fun i => if i = 0 then R 0 - 1
        else if i = 1 then (Nat.pairNext (R 1, R 2)).1
        else if i = 2 then (Nat.pairNext (R 1, R 2)).2 else 0⟩ := by
  set R1 := Function.update R 0 (R 0 - 1) with hR1
  have hstep : step unpairLoop ⟨0, R⟩ = ⟨1, R1⟩ :=
    step_dec_pos (P := unpairLoop) (p := 0) (a := 1) (b := unpairBody.length + 2) rfl hR
  obtain ⟨nb, hbin, hbex⟩ := realises_unpairBody R1
  have hmid : ∀ m ≤ nb, run unpairLoop ⟨1, R1⟩ m =
      ⟨(run unpairBody ⟨0, R1⟩ m).pc + 1, (run unpairBody ⟨0, R1⟩ m).regs⟩ := fun m hm =>
    run_middle (A := [Instr.dec 0 1 (unpairBody.length + 2)]) (C := [Instr.dec 5 0 0])
      hbin m hm
  have hbody : run unpairLoop ⟨1, R1⟩ nb =
      ⟨unpairBody.length + 1, fun i => if i = 0 then R1 0
        else if i = 1 then (Nat.pairNext (R1 1, R1 2)).1
        else if i = 2 then (Nat.pairNext (R1 1, R1 2)).2 else 0⟩ := by
    rw [hmid nb (Nat.le_refl _), hbex]
  refine ⟨nb + 2, fun m hm => ?_, ?_⟩
  · rcases (show m = 0 ∨ (1 ≤ m ∧ m ≤ nb) ∨ m = nb + 1 by omega) with rfl | ⟨hm1, hm2⟩ | rfl
    · rw [length_unpairLoop]; simp
    · rw [show m = 1 + (m - 1) by omega, run_add, run_one, hstep, hmid (m - 1) (by omega),
        length_unpairLoop]
      have := hbin (m - 1) (by omega)
      exact show (run unpairBody ⟨0, R1⟩ (m - 1)).pc + 1 < unpairBody.length + 2 by omega
    · rw [show nb + 1 = 1 + nb by omega, run_add, run_one, hstep, hbody, length_unpairLoop]
      exact show unpairBody.length + 1 < unpairBody.length + 2 by omega
  · have hidx : unpairLoop[unpairBody.length + 1]? = some (Instr.dec 5 0 0) := by
      rw [unpairLoop, List.getElem?_append_right (by simp)]
      simp
    have hzero : (fun i : Fin 6 => if i = 0 then R1 0
        else if i = 1 then (Nat.pairNext (R1 1, R1 2)).1
        else if i = 2 then (Nat.pairNext (R1 1, R1 2)).2 else 0) 5 = 0 := by
      simp only [Fin.reduceEq, if_false]
    rw [show nb + 2 = 1 + nb + 1 by omega, run_add, run_add, run_one, run_one, hstep, hbody,
      step_dec_zero (P := unpairLoop) (p := unpairBody.length + 1) (a := 0) (b := 0) hidx hzero]
    refine congrArg _ (funext fun i => ?_)
    simp only [hR1, Function.update_apply]
    split_ifs <;> simp_all


/-! ## The counted loop -/

/-- The register file after `q` turns, from the clean input configuration. `Nat.pairNext^[q]`
stays opaque here on purpose. -/
private def loopState (n q : ℕ) : Fin 6 → ℕ :=
  fun i => if i = 0 then n - q
    else if i = 1 then (Nat.pairNext^[q] (0, 0)).1
    else if i = 2 then (Nat.pairNext^[q] (0, 0)).2 else 0

private theorem run_loop (n : ℕ) : ∀ q ≤ n, ∃ steps,
    (∀ m < steps, (run unpairLoop ⟨0, unaryConfig 5 n⟩ m).pc < unpairLoop.length) ∧
      run unpairLoop ⟨0, unaryConfig 5 n⟩ steps = ⟨0, loopState n q⟩ := by
  intro q
  induction q with
  | zero =>
    intro _
    refine ⟨0, fun m hm => absurd hm (Nat.not_lt_zero m), ?_⟩
    refine congrArg _ (funext fun i => ?_)
    simp only [loopState, unaryConfig, Function.update_apply, Function.iterate_zero_apply]
    split_ifs <;> simp_all
  | succ q ih =>
    intro hq
    obtain ⟨steps, hin, hex⟩ := ih (by omega)
    have hne : loopState n q 0 ≠ 0 := by simp [loopState]; omega
    obtain ⟨nt, htin, htex⟩ := run_turn (loopState n q) hne
    refine ⟨steps + nt, (run_segment_trans hin hex htin htex).1, ?_⟩
    · rw [(run_segment_trans hin hex htin htex).2]
      have hiter : Nat.pairNext^[q + 1] (0, 0) = Nat.pairNext (Nat.pairNext^[q] (0, 0)) :=
        Function.iterate_succ_apply' _ _ _
      refine congrArg _ (funext fun i => ?_)
      simp only [loopState, hiter, Fin.reduceEq, if_true, if_false, Prod.mk.eta]
      split_ifs <;> simp_all
      all_goals omega

/-- **The counted loop computes `Nat.unpair`.** From the clean input configuration it exits with
the two components in registers `1` and `2` and everything else at zero.

`Nat.iterate_pairNext` is used exactly here, at `q = n`, and nowhere inside the induction. -/
theorem run_unpairLoop (n : ℕ) : ∃ steps,
    (∀ m < steps, (run unpairLoop ⟨0, unaryConfig 5 n⟩ m).pc < unpairLoop.length) ∧
      run unpairLoop ⟨0, unaryConfig 5 n⟩ steps =
        ⟨unpairLoop.length, fun i => if i = 1 then (Nat.unpair n).1
          else if i = 2 then (Nat.unpair n).2 else 0⟩ := by
  obtain ⟨steps, hin, hex⟩ := run_loop n n (Nat.le_refl _)
  have hz : loopState n n 0 = 0 := by simp [loopState]
  refine ⟨steps + 1, fun m hm => ?_, ?_⟩
  · rcases (show m < steps ∨ m = steps by omega) with h | rfl
    · exact hin m h
    · rw [hex, length_unpairLoop]
      exact show 0 < unpairBody.length + 2 by omega
  · rw [run_add, hex, run_one,
      step_dec_zero (P := unpairLoop) (p := 0) (a := 1) (b := unpairBody.length + 2) rfl hz,
      length_unpairLoop]
    refine congrArg _ (funext fun i => ?_)
    simp only [loopState, Nat.iterate_pairNext]
    split_ifs <;> simp_all

/-! ## The two constructors

The loop theorem is proved once; `left` and `right` differ only in which component they move into
register `0`. -/

/-- `Nat.Partrec.Code.left`. -/
def leftMachine : Program 6 := seq unpairLoop (seq (move 1 0) (clear 2))

/-- `Nat.Partrec.Code.right`. -/
def rightMachine : Program 6 := seq unpairLoop (seq (move 2 0) (clear 1))

theorem cleanPartComputesUnary_leftMachine :
    CleanPartComputesUnary leftMachine fun n => Part.some (Nat.unpair n).1 := by
  intro n
  refine ⟨fun y hy => ?_, fun _ => trivial⟩
  obtain rfl : y = (Nat.unpair n).1 := by simpa using hy
  obtain ⟨s1, h1in, h1ex⟩ := run_unpairLoop n
  obtain ⟨s2, h2in, h2ex⟩ := ((realises_move (show (1 : Fin 6) ≠ 0 by decide)).seq
    (realises_clear 2)) (fun i => if i = 1 then (Nat.unpair n).1
      else if i = 2 then (Nat.unpair n).2 else 0)
  refine ⟨s1 + s2, join_exit h1in h1ex h2in ?_⟩
  rw [h2ex]
  refine congrArg _ (funext fun i => ?_)
  simp only [unaryConfig, Function.update_apply, Fin.reduceEq, if_true, if_false]
  split_ifs <;> simp_all

theorem cleanPartComputesUnary_rightMachine :
    CleanPartComputesUnary rightMachine fun n => Part.some (Nat.unpair n).2 := by
  intro n
  refine ⟨fun y hy => ?_, fun _ => trivial⟩
  obtain rfl : y = (Nat.unpair n).2 := by simpa using hy
  obtain ⟨s1, h1in, h1ex⟩ := run_unpairLoop n
  obtain ⟨s2, h2in, h2ex⟩ := ((realises_move (show (2 : Fin 6) ≠ 0 by decide)).seq
    (realises_clear 1)) (fun i => if i = 1 then (Nat.unpair n).1
      else if i = 2 then (Nat.unpair n).2 else 0)
  refine ⟨s1 + s2, join_exit h1in h1ex h2in ?_⟩
  rw [h2ex]
  refine congrArg _ (funext fun i => ?_)
  simp only [unaryConfig, Function.update_apply, Fin.reduceEq, if_true, if_false]
  split_ifs <;> simp_all

end RegisterMachine

end Hilbert10


/- Source: Hilbert10.Internal.RegisterMachinePair, Hilbert10 v2.3.0, Apache-2.0. -/
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# `Nat.pair` by walking the enumeration

Issue #51, step 5. Enumerate from `(0, 0)`, counting steps, until the candidate is the target.
`Nat.iterate_pairNext_pair` says that happens after exactly `Nat.pair a b` steps, so the loop
terminates and the count is the answer. No unbounded search and no `rfind'`.

## Layout

`Fin 9`:

| register | role |
|---|---|
| `0`, `1` | the target pair, preserved |
| `2` | the step count, and the result |
| `3`, `4` | the candidate pair |
| `5` | accumulated distance from candidate to target |
| `6`, `7`, `8` | `compare`'s residuals and temporary |

**On the extra register.** Testing a *pair* for equality needs two comparisons, and `compare`
needs three scratch registers of its own, which is eight before an accumulator. With one more the
loop body is a straight line ending in a single branch, and its proof is one splice. Testing the
coordinates separately fits in eight registers but branches forward out of the middle of the
body from two places, giving four entry paths into the advance block and four splices. The
register is cheaper than the proof.

## The loop

```
0 … T-1    measure the distance into register 5
T          decrement 5; positive → drain and advance, zero → exit
T+1        drain the rest of 5
T+2 … T+M+1  the relocated pairNextMachine
T+M+2      increment the count, jump back to 0
```

The advance block cleans registers `6`, `7`, `8` whatever they held, so the drain at `T+1` is the
only cleanup the loop performs — the measurement's leftovers are somebody else's problem, and
that somebody already handles them.
-/

namespace Hilbert10

namespace RegisterMachine

/-! ## Measuring the distance -/

/-- Add the coordinatewise distance from `(3, 4)` to `(0, 1)` into register `5`. -/
def measure : Program 9 :=
  seq (compare 3 0 6 7 8)
    (seq (move 6 5) (seq (move 7 5)
      (seq (compare 4 1 6 7 8) (seq (move 6 5) (move 7 5)))))

theorem realises_measure : Realises measure fun regs i =>
    if i = 5 then regs 5 + ((regs 0 - regs 3) + (regs 3 - regs 0))
        + ((regs 1 - regs 4) + (regs 4 - regs 1))
      else if i = 6 then 0 else if i = 7 then 0 else if i = 8 then 0 else regs i := by
  refine (((realises_compare (a := 3) (b := 0) (lo := 6) (hi := 7) (tmp := 8)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)).seq
      ((realises_move (show (6 : Fin 9) ≠ 5 by decide)).seq
        ((realises_move (show (7 : Fin 9) ≠ 5 by decide)).seq
          ((realises_compare (a := 4) (b := 1) (lo := 6) (hi := 7) (tmp := 8)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide)).seq
              ((realises_move (show (6 : Fin 9) ≠ 5 by decide)).seq
                (realises_move (show (7 : Fin 9) ≠ 5 by decide))))))).congr fun regs => ?_)
  funext i
  fin_cases i <;> simp
  all_goals omega

/-! ## Advancing the candidate -/

/-- Where `pairNextMachine`'s five registers go: the candidate pair and the top three scratch
registers. The accumulator, register `5`, is deliberately outside the block. -/
def pairAdvanceIdx (i : Fin 5) : Fin 9 :=
  if i = 0 then 3 else if i = 1 then 4 else if i = 2 then 6 else if i = 3 then 7 else 8

def pairAdvance : Program 9 := renameRegs pairAdvanceIdx pairNextMachine

theorem realises_pairAdvance : Realises pairAdvance fun regs i =>
    if i = 3 then (Nat.pairNext (regs 3, regs 4)).1
    else if i = 4 then (Nat.pairNext (regs 3, regs 4)).2
    else if i = 6 then 0 else if i = 7 then 0 else if i = 8 then 0 else regs i := by
  refine realises_pairNextMachine.renameRegs
    (show Function.Injective pairAdvanceIdx by decide) ?_ ?_
  · intro regs i
    fin_cases i <;> simp [pairAdvanceIdx]
  · intro regs r hr
    have h3 : r ≠ 3 := by simpa [pairAdvanceIdx] using hr 0
    have h4 : r ≠ 4 := by simpa [pairAdvanceIdx] using hr 1
    have h6 : r ≠ 6 := by simpa [pairAdvanceIdx] using hr 2
    have h7 : r ≠ 7 := by simpa [pairAdvanceIdx] using hr 3
    have h8 : r ≠ 8 := by simpa [pairAdvanceIdx] using hr 4
    simp [h3, h4, h6, h7, h8]

/-- The distance is zero exactly when the candidate is the target. -/
theorem measure_eq_zero_iff (regs : Fin 9 → ℕ) :
    ((regs 0 - regs 3) + (regs 3 - regs 0)) + ((regs 1 - regs 4) + (regs 4 - regs 1)) = 0 ↔
      (regs 3, regs 4) = (regs 0, regs 1) := by
  rw [Prod.mk.injEq]
  omega


/-! ## The loop -/

/-- The header state after `q` turns: the targets, the count, the `q`th pair of the enumeration,
and clean scratch. -/
def pairState (a b q : ℕ) : Fin 9 → ℕ :=
  fun i => if i = 0 then a else if i = 1 then b else if i = 2 then q
    else if i = 3 then (Nat.pairNext^[q] (0, 0)).1
    else if i = 4 then (Nat.pairNext^[q] (0, 0)).2 else 0

/-- The measurement, then the branch on its result. -/
private def pairPre : Program 9 :=
  measure ++ [Instr.dec 5 (measure.length + 1) (measure.length + pairAdvance.length + 3),
              Instr.dec 5 (measure.length + 1) (measure.length + 2)]

/-- Walk the enumeration, counting, until the candidate is the target. -/
def pairLoop : Program 9 := pairPre ++ shiftJumps pairPre.length pairAdvance ++ [Instr.inc 2 0]

private theorem length_pairPre : pairPre.length = measure.length + 2 := by simp [pairPre]

theorem length_pairLoop : pairLoop.length = measure.length + pairAdvance.length + 3 := by
  simp [pairLoop, pairPre]
  omega

private theorem getElem?_test : pairLoop[measure.length]? =
    some (Instr.dec 5 (measure.length + 1) (measure.length + pairAdvance.length + 3)) := by
  rw [pairLoop, List.getElem?_append_left (by simp [length_pairPre]; omega),
    List.getElem?_append_left (by rw [length_pairPre]; omega), pairPre,
    List.getElem?_append_right (Nat.le_refl _)]
  simp

private theorem getElem?_drain : pairLoop[measure.length + 1]? =
    some (Instr.dec 5 (measure.length + 1) (measure.length + 2)) := by
  rw [pairLoop, List.getElem?_append_left (by simp [length_pairPre]; omega),
    List.getElem?_append_left (by rw [length_pairPre]; omega), pairPre,
    List.getElem?_append_right (by simp)]
  simp

private theorem getElem?_inc :
    pairLoop[measure.length + pairAdvance.length + 2]? = some (Instr.inc 2 0) := by
  rw [pairLoop, List.getElem?_append_right (by simp [length_pairPre]; omega)]
  simp only [List.length_append, length_pairPre, length_shiftJumps]
  rw [show measure.length + pairAdvance.length + 2 -
    (measure.length + 2 + pairAdvance.length) = 0 by omega]
  rfl

private theorem pairLoop_eq :
    pairLoop = measure ++ ([Instr.dec 5 (measure.length + 1)
        (measure.length + pairAdvance.length + 3),
      Instr.dec 5 (measure.length + 1) (measure.length + 2)]
      ++ shiftJumps pairPre.length pairAdvance ++ [Instr.inc 2 0]) := by
  simp [pairLoop, pairPre]

private theorem run_measure_seg {R : Fin 9 → ℕ} {n : ℕ}
    (hin : ∀ m < n, (run measure ⟨0, R⟩ m).pc < measure.length) (m : ℕ) (hm : m ≤ n) :
    run pairLoop ⟨0, R⟩ m = run measure ⟨0, R⟩ m := by
  rw [pairLoop_eq, run_append_of_lt (fun j hj => hin j (by omega))]

/-- The measurement, inside the loop, from a header state. `q` is kept abstract throughout: the
terminal turn instantiates it to `Nat.pair a b` only at the very end, since substituting it early
makes every subterm large enough to defeat `split_ifs`. -/
private theorem run_measure_header (a b q : ℕ) :
    ∃ nm, (∀ m < nm, (run pairLoop ⟨0, pairState a b q⟩ m).pc < pairLoop.length) ∧
      run pairLoop ⟨0, pairState a b q⟩ nm = ⟨measure.length, fun i =>
        if i = 5 then ((a - (Nat.pairNext^[q] (0, 0)).1) + ((Nat.pairNext^[q] (0, 0)).1 - a))
          + ((b - (Nat.pairNext^[q] (0, 0)).2) + ((Nat.pairNext^[q] (0, 0)).2 - b))
        else pairState a b q i⟩ := by
  obtain ⟨nm, hmin, hmex⟩ := realises_measure (pairState a b q)
  refine ⟨nm, fun m hm => ?_, ?_⟩
  · rw [run_measure_seg hmin m (Nat.le_of_lt hm), length_pairLoop]
    have := hmin m hm
    omega
  · rw [run_measure_seg hmin nm (Nat.le_refl _), hmex]
    refine congrArg _ (funext fun i => ?_)
    fin_cases i <;> simp [pairState]

/-- The terminal turn: the candidate is the target, so the branch exits. -/
private theorem run_turn_eq (a b q : ℕ) (hcand : Nat.pairNext^[q] (0, 0) = (a, b)) :
    ∃ n, (∀ m < n, (run pairLoop ⟨0, pairState a b q⟩ m).pc < pairLoop.length) ∧
      run pairLoop ⟨0, pairState a b q⟩ n = ⟨pairLoop.length, pairState a b q⟩ := by
  obtain ⟨nm, h1in, h1ex⟩ := run_measure_header a b q
  have hfix : (fun i : Fin 9 =>
      if i = 5 then ((a - (Nat.pairNext^[q] (0, 0)).1) + ((Nat.pairNext^[q] (0, 0)).1 - a))
        + ((b - (Nat.pairNext^[q] (0, 0)).2) + ((Nat.pairNext^[q] (0, 0)).2 - b))
      else pairState a b q i) = pairState a b q := by
    funext i
    rw [hcand]
    by_cases h : i = 5
    · subst h; simp [pairState]
    · rw [if_neg h]
  rw [hfix] at h1ex
  have hzero : pairState a b q 5 = 0 := by simp [pairState]
  have h2ex : run pairLoop ⟨measure.length, pairState a b q⟩ 1 =
      ⟨pairLoop.length, pairState a b q⟩ := by
    rw [run_one, step_dec_zero getElem?_test hzero, length_pairLoop]
  exact ⟨nm + 1, run_segment_trans h1in h1ex (fun m hm => by
    rw [show m = 0 by omega, run_zero, length_pairLoop]
    exact show measure.length < measure.length + pairAdvance.length + 3 by omega) h2ex⟩


private theorem run_advance_seg {R : Fin 9 → ℕ} {n : ℕ}
    (hin : ∀ m < n, (run pairAdvance ⟨0, R⟩ m).pc < pairAdvance.length) (m : ℕ) (hm : m ≤ n) :
    run pairLoop ⟨0 + pairPre.length, R⟩ m =
      ⟨(run pairAdvance ⟨0, R⟩ m).pc + pairPre.length, (run pairAdvance ⟨0, R⟩ m).regs⟩ :=
  run_middle (A := pairPre) (C := [Instr.inc 2 0]) hin m hm

/-- An ordinary turn: the candidate is not the target, so the loop drains the distance, advances
the enumeration, counts, and jumps back. -/
private theorem run_turn_ne (a b q : ℕ) (hne : Nat.pairNext^[q] (0, 0) ≠ (a, b)) :
    ∃ n, (∀ m < n, (run pairLoop ⟨0, pairState a b q⟩ m).pc < pairLoop.length) ∧
      run pairLoop ⟨0, pairState a b q⟩ n = ⟨0, pairState a b (q + 1)⟩ := by
  obtain ⟨nm, h1in, h1ex⟩ := run_measure_header a b q
  have hLp : pairLoop.length = measure.length + pairAdvance.length + 3 := length_pairLoop
  have hpre : (0 : ℕ) + pairPre.length = measure.length + 2 := by
    rw [Nat.zero_add, length_pairPre]
  -- the measured distance is positive, because the candidate misses the target
  set Rm : Fin 9 → ℕ := fun i =>
    if i = 5 then ((a - (Nat.pairNext^[q] (0, 0)).1) + ((Nat.pairNext^[q] (0, 0)).1 - a))
      + ((b - (Nat.pairNext^[q] (0, 0)).2) + ((Nat.pairNext^[q] (0, 0)).2 - b))
    else pairState a b q i with hRm
  have hd : Rm 5 ≠ 0 := by
    simp only [hRm, if_pos rfl]
    intro h0
    exact hne (Prod.ext_iff.mpr ⟨by omega, by omega⟩)
  -- step 2: the branch takes the mismatch side
  have h2ex : run pairLoop ⟨measure.length, Rm⟩ 1 =
      ⟨measure.length + 1, Function.update Rm 5 (Rm 5 - 1)⟩ := by
    rw [run_one, step_dec_pos getElem?_test hd]
  -- step 3: drain what is left of the distance
  have h3ex : run pairLoop ⟨measure.length + 1, Function.update Rm 5 (Rm 5 - 1)⟩ (Rm 5) =
      ⟨measure.length + 2, Function.update Rm 5 0⟩ := by
    have h := run_drain getElem?_drain (Function.update Rm 5 (Rm 5 - 1))
    rw [Function.update_self, Function.update_idem] at h
    rw [show Rm 5 = Rm 5 - 1 + 1 by omega]
    exact h
  -- step 4: advance the enumeration
  obtain ⟨na, hain, haex⟩ := realises_pairAdvance (Function.update Rm 5 0)
  set Ra : Fin 9 → ℕ := fun i =>
    if i = 3 then (Nat.pairNext (Function.update Rm 5 0 3, Function.update Rm 5 0 4)).1
    else if i = 4 then (Nat.pairNext (Function.update Rm 5 0 3, Function.update Rm 5 0 4)).2
    else if i = 6 then 0 else if i = 7 then 0 else if i = 8 then 0
    else Function.update Rm 5 0 i with hRa
  have h4ex : run pairLoop ⟨measure.length + 2, Function.update Rm 5 0⟩ na =
      ⟨pairAdvance.length + pairPre.length, Ra⟩ := by
    rw [← hpre, run_advance_seg hain na (Nat.le_refl _), haex]
  -- step 5: count and jump back
  have h5ex : run pairLoop ⟨pairAdvance.length + pairPre.length, Ra⟩ 1 =
      ⟨0, pairState a b (q + 1)⟩ := by
    rw [show pairAdvance.length + pairPre.length = measure.length + pairAdvance.length + 2 by
      rw [length_pairPre]; omega, run_one, step_inc getElem?_inc]
    have hiter : Nat.pairNext^[q + 1] (0, 0) = Nat.pairNext (Nat.pairNext^[q] (0, 0)) :=
      Function.iterate_succ_apply' _ _ _
    refine congrArg _ (funext fun i => ?_)
    fin_cases i <;>
      simp [hRa, hRm, pairState, hiter, Function.update_apply, Prod.mk.eta]
  -- the four in-range obligations
  have i2 : ∀ m < 1, (run pairLoop ⟨measure.length, Rm⟩ m).pc < pairLoop.length := by
    intro m hm
    rw [show m = 0 by omega, run_zero, hLp]
    exact show measure.length < measure.length + pairAdvance.length + 3 by omega
  have i3 : ∀ m < Rm 5, (run pairLoop ⟨measure.length + 1,
      Function.update Rm 5 (Rm 5 - 1)⟩ m).pc < pairLoop.length := by
    intro m hm
    rw [run_drain_partial getElem?_drain (Function.update Rm 5 (Rm 5 - 1)) m
      (by rw [Function.update_self]; omega), hLp]
    exact show measure.length + 1 < measure.length + pairAdvance.length + 3 by omega
  have i4 : ∀ m < na, (run pairLoop ⟨measure.length + 2, Function.update Rm 5 0⟩ m).pc <
      pairLoop.length := by
    intro m hm
    rw [← hpre, run_advance_seg hain m (Nat.le_of_lt hm), hLp, length_pairPre]
    have := hain m hm
    exact show (run pairAdvance ⟨0, Function.update Rm 5 0⟩ m).pc + (measure.length + 2) <
      measure.length + pairAdvance.length + 3 by omega
  have i5 : ∀ m < 1, (run pairLoop ⟨pairAdvance.length + pairPre.length, Ra⟩ m).pc <
      pairLoop.length := by
    intro m hm
    rw [show m = 0 by omega, run_zero, hLp, length_pairPre]
    exact show pairAdvance.length + (measure.length + 2) <
      measure.length + pairAdvance.length + 3 by omega
  obtain ⟨j2in, j2ex⟩ := run_segment_trans i4 h4ex i5 h5ex
  obtain ⟨j3in, j3ex⟩ := run_segment_trans i3 h3ex j2in j2ex
  obtain ⟨j4in, j4ex⟩ := run_segment_trans i2 h2ex j3in j3ex
  exact ⟨nm + (1 + (Rm 5 + (na + 1))), run_segment_trans h1in h1ex j4in j4ex⟩


/-! ## From the origin to the target -/

private theorem run_loop_to (a b : ℕ) : ∀ q ≤ Nat.pair a b, ∃ n,
    (∀ m < n, (run pairLoop ⟨0, pairState a b 0⟩ m).pc < pairLoop.length) ∧
      run pairLoop ⟨0, pairState a b 0⟩ n = ⟨0, pairState a b q⟩ := by
  intro q
  induction q with
  | zero => intro _; exact ⟨0, fun m hm => absurd hm (Nat.not_lt_zero m), rfl⟩
  | succ q ih =>
    intro hq
    obtain ⟨n, hin, hex⟩ := ih (by omega)
    obtain ⟨nt, htin, htex⟩ := run_turn_ne a b q (Nat.iterate_pairNext_ne_of_lt (by omega))
    exact ⟨n + nt, run_segment_trans hin hex htin htex⟩

/-- **The loop terminates, after exactly `Nat.pair a b` turns.** `Nat.iterate_pairNext_ne_of_lt`
rules out an earlier match and `Nat.iterate_pairNext_pair` supplies the terminal one. -/
theorem run_pairLoop (a b : ℕ) : ∃ n,
    (∀ m < n, (run pairLoop ⟨0, pairState a b 0⟩ m).pc < pairLoop.length) ∧
      run pairLoop ⟨0, pairState a b 0⟩ n =
        ⟨pairLoop.length, pairState a b (Nat.pair a b)⟩ := by
  obtain ⟨n, hin, hex⟩ := run_loop_to a b (Nat.pair a b) (Nat.le_refl _)
  obtain ⟨nt, htin, htex⟩ := run_turn_eq a b (Nat.pair a b) (Nat.iterate_pairNext_pair a b)
  exact ⟨n + nt, run_segment_trans hin hex htin htex⟩

/-! ## The machine

The loop exits with the candidate still in registers `3` and `4`. Those have to be cleared for
the result to satisfy the clean-scratch contract of `CleanScratch`, which is what step 6 will
call through, so the epilogue is not optional. -/

/-- Clear everything but the two targets. -/
def pairPrologue : Program 9 :=
  seq (clear 2) (seq (clear 3) (seq (clear 4) (seq (clear 5) (seq (clear 6)
    (seq (clear 7) (clear 8))))))

/-- Clear the candidate the loop matched on. -/
def pairEpilogue : Program 9 := seq (clear 3) (clear 4)

/-- `Nat.pair` on registers `0` and `1`, with the answer in register `2`. -/
def pairMachine : Program 9 := seq pairPrologue (seq pairLoop pairEpilogue)

theorem realises_pairPrologue : Realises pairPrologue fun regs i =>
    if i = 0 then regs 0 else if i = 1 then regs 1 else 0 := by
  refine (((realises_clear 2).seq ((realises_clear 3).seq ((realises_clear 4).seq
    ((realises_clear 5).seq ((realises_clear 6).seq
      ((realises_clear 7).seq (realises_clear 8))))))).congr fun regs => ?_)
  funext i
  fin_cases i <;> simp

theorem realises_pairEpilogue : Realises pairEpilogue fun regs i =>
    if i = 3 then 0 else if i = 4 then 0 else regs i := by
  refine (((realises_clear 3).seq (realises_clear 4)).congr fun regs => ?_)
  funext i
  fin_cases i <;> simp

/-- **`pairMachine` computes `Nat.pair`.** The targets survive, the answer lands in register `2`,
and every other register comes back at zero whatever it held. -/
theorem realises_pairMachine : Realises pairMachine fun regs i =>
    if i = 0 then regs 0 else if i = 1 then regs 1
    else if i = 2 then Nat.pair (regs 0) (regs 1) else 0 := by
  intro regs
  obtain ⟨n0, h0in, h0ex⟩ := realises_pairPrologue regs
  have h0ex' : run pairPrologue ⟨0, regs⟩ n0 =
      ⟨pairPrologue.length, pairState (regs 0) (regs 1) 0⟩ := by
    rw [h0ex]
    refine congrArg _ (funext fun i => ?_)
    fin_cases i <;> simp [pairState]
  obtain ⟨n1, h1in, h1ex⟩ := run_pairLoop (regs 0) (regs 1)
  obtain ⟨n2, h2in, h2ex⟩ :=
    realises_pairEpilogue (pairState (regs 0) (regs 1) (Nat.pair (regs 0) (regs 1)))
  have h2ex' : run pairEpilogue
      ⟨0, pairState (regs 0) (regs 1) (Nat.pair (regs 0) (regs 1))⟩ n2 =
      ⟨pairEpilogue.length, fun i => if i = 0 then regs 0 else if i = 1 then regs 1
        else if i = 2 then Nat.pair (regs 0) (regs 1) else 0⟩ := by
    rw [h2ex]
    refine congrArg _ (funext fun i => ?_)
    fin_cases i <;> simp [pairState]
  obtain ⟨jin, jex⟩ := join_exit h1in h1ex h2in h2ex'
  exact ⟨n0 + (n1 + n2), join_exit h0in h0ex' jin jex⟩

end RegisterMachine

end Hilbert10


/- Source: Hilbert10.Internal.CodePair, Hilbert10 v2.3.0, Apache-2.0. -/
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# Compiling `Nat.Partrec.Code.pair`

Issue #51, step 6. The closure theorem for `pair`: given clean machines for two subcodes, build
one for `fun n => Nat.pair <$> cf n <*> cg n`. Assembling this over `Code.rec` is #44.

This is a controller and calling-convention proof rather than an arithmetic one. The arithmetic
was step 5.

## The source semantics, once

Mathlib evaluates `pair cf cg` applicatively. `mem_eval_pair` below turns that into an explicit
existential, so no `Seq.seq` or `Part.bind` reasoning reaches the machine proof, and the
`cf`-before-`cg` order is fixed in one place.
-/

namespace Hilbert10

namespace RegisterMachine

/-- The applicative source semantics of `Code.pair`, as an existential. `cf`'s value is `a`,
`cg`'s is `b`, and the result is `Nat.pair a b` in that order. -/
theorem mem_eval_pair {f g : ℕ →. ℕ} {n y : ℕ} :
    y ∈ (Nat.pair <$> f n <*> g n) ↔ ∃ a ∈ f n, ∃ b ∈ g n, y = Nat.pair a b := by
  simp only [Seq.seq, Part.map_eq_map, Part.mem_bind_iff, Part.mem_map_iff]
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, b, hb, rfl⟩
    exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨_, ⟨a, ha, rfl⟩, b, hb, rfl⟩

/-- The evaluation of `Code.pair` really is that applicative expression. -/
theorem mem_eval_code_pair {cf cg : Nat.Partrec.Code} {n y : ℕ} :
    y ∈ (Nat.Partrec.Code.pair cf cg).eval n ↔
      ∃ a ∈ cf.eval n, ∃ b ∈ cg.eval n, y = Nat.pair a b :=
  mem_eval_pair


/-! ## The controller's register layout

One explicit layout, over `Fin (k + k' + 13)`:

| register | role |
|---|---|
| `0` | the original input, preserved across both calls, then the output |
| `1`, `2` | the two subresults, and `pairMachine`'s targets |
| `3` | `pairMachine`'s answer |
| `4`–`9` | `pairMachine`'s candidate, accumulator and scratch |
| `10` | the temporary `copy` borrows |
| `11 …` | `cf`'s block, then `cg`'s block |

The facts below are arithmetic about *this* layout, nothing more: three embeddings are
injective, their images are pairwise disjoint, and the fixed registers `0` and `10` lie outside
all of them. They are proved once so that `Fin` index juggling stays out of the semantic proof.

This is not an allocator. The embeddings are three explicit offsets, written down here and
supplied to `CleanPartComputesUnary.call` by hand. -/

variable (k k' : ℕ)

/-- `cf`'s block, starting at register `11`. -/
def embedF (i : Fin (k + 1)) : Fin (k + k' + 13) := ⟨11 + i.val, by omega⟩

/-- `cg`'s block, immediately after `cf`'s. -/
def embedG (j : Fin (k' + 1)) : Fin (k + k' + 13) := ⟨12 + k + j.val, by omega⟩

/-- `pairMachine`'s nine registers, onto `1`–`9`. -/
def embedP (i : Fin 9) : Fin (k + k' + 13) := ⟨1 + i.val, by omega⟩

variable {k k'}

@[simp] theorem embedF_val (i : Fin (k + 1)) : (embedF k k' i).val = 11 + i.val := rfl
@[simp] theorem embedG_val (j : Fin (k' + 1)) : (embedG k k' j).val = 12 + k + j.val := rfl
@[simp] theorem embedP_val (i : Fin 9) : (embedP k k' i).val = 1 + i.val := rfl

/-- The temporary that `copy` borrows: the one fixed controller register outside `0`–`9`. -/
def ten : Fin (k + k' + 13) := ⟨10, by omega⟩

theorem embedF_injective : Function.Injective (embedF k k') := by
  intro i j h
  exact Fin.ext (by have := congrArg Fin.val h; simp at this; omega)

theorem embedG_injective : Function.Injective (embedG k k') := by
  intro i j h
  exact Fin.ext (by have := congrArg Fin.val h; simp at this; omega)

theorem embedP_injective : Function.Injective (embedP k k') := by
  intro i j h
  exact Fin.ext (by have := congrArg Fin.val h; simp at this; omega)

/-! ### Register `0` and the borrowed temporary lie outside every block -/

theorem zero_ne_embedF (i : Fin (k + 1)) : (0 : Fin (k + k' + 13)) ≠ embedF k k' i := by
  intro h; have := congrArg Fin.val h; simp at this; omega

theorem zero_ne_embedG (j : Fin (k' + 1)) : (0 : Fin (k + k' + 13)) ≠ embedG k k' j := by
  intro h; have := congrArg Fin.val h; simp at this; omega

theorem ten_ne_embedF (i : Fin (k + 1)) : (ten : Fin (k + k' + 13)) ≠ embedF k k' i := by
  intro h; have := congrArg Fin.val h; simp [ten] at this; omega

theorem ten_ne_embedG (j : Fin (k' + 1)) :
    (ten : Fin (k + k' + 13)) ≠ embedG k k' j := by
  intro h; have := congrArg Fin.val h; simp [ten] at this; omega

/-! ### The three blocks are pairwise disjoint -/

theorem embedF_ne_embedG (i : Fin (k + 1)) (j : Fin (k' + 1)) :
    embedF k k' i ≠ embedG k k' j := by
  intro h
  have := congrArg Fin.val h
  simp at this
  omega

theorem embedP_ne_embedF (i : Fin 9) (j : Fin (k + 1)) : embedP k k' i ≠ embedF k k' j := by
  intro h
  have := congrArg Fin.val h
  simp at this
  omega

theorem embedP_ne_embedG (i : Fin 9) (j : Fin (k' + 1)) : embedP k k' i ≠ embedG k k' j := by
  intro h
  have := congrArg Fin.val h
  simp at this
  omega

/-- `pairMachine`'s block is exactly registers `1`–`9`, so the controller's fixed registers `0`
and `10` are outside it too. -/
theorem embedP_ne_zero (i : Fin 9) : embedP k k' i ≠ 0 := by
  intro h; have := congrArg Fin.val h; simp at this

theorem embedP_ne_ten (i : Fin 9) : embedP k k' i ≠ (ten : Fin (k + k' + 13)) := by
  intro h
  have := congrArg Fin.val h
  simp [ten] at this
  omega

/-! ### The layout is exhaustive

The lemmas above say the blocks are separated. This one says they cover: registers `0`, `1`–`9`,
`10`, `cf`'s block and `cg`'s block account for every register, with nothing left over.

It is the eliminator for the final `funext` — showing the controller returns a clean unary
configuration means saying something about *every* register, and without this the proof would
rediscover the offset arithmetic one register at a time. -/
theorem layout_cases (r : Fin (k + k' + 13)) :
    r = 0 ∨ (∃ i, r = embedP k k' i) ∨ r = ten ∨
      (∃ i, r = embedF k k' i) ∨ ∃ j, r = embedG k k' j := by
  have hr := r.isLt
  rcases (show r.val = 0 ∨ (1 ≤ r.val ∧ r.val ≤ 9) ∨ r.val = 10 ∨
      (11 ≤ r.val ∧ r.val ≤ 11 + k) ∨ 12 + k ≤ r.val by omega) with h | h | h | h | h
  · exact Or.inl (Fin.ext (by simpa using h))
  · exact Or.inr (Or.inl ⟨⟨r.val - 1, by omega⟩, Fin.ext (by simp [embedP]; omega)⟩)
  · exact Or.inr (Or.inr (Or.inl (Fin.ext (by simpa [ten] using h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨⟨r.val - 11, by omega⟩, Fin.ext (by simp [embedF]; omega)⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      ⟨⟨r.val - 12 - k, by omega⟩, Fin.ext (by simp [embedG]; omega)⟩)))

/-! ## The controller

Eight named blocks, grouped into five units so that adjacent total blocks splice once instead of
four times. The two partial units are the calls; everything else is a `Realises` macro. -/

variable (P : Program (k + 1)) (Q : Program (k' + 1))

/-- Unit 1: put the input where `cf` will read it. -/
def seedF : Program (k + k' + 13) := copy 0 (embedF k k' 0) ten

/-- Unit 3: save `cf`'s answer into register `1`, then seed `cg` from the untouched input.

Registers `1`, `2`, `3` are written as `embedP 0`, `embedP 1`, `embedP 2` throughout. They *are*
`pairMachine`'s two targets and its answer, so naming them that way records the connection and
keeps `Fin` numerals — whose `OfNat` goes through `%` — out of every proof. -/
def saveFSeedG : Program (k + k' + 13) :=
  seq (move (embedF k k' 0) (embedP k k' 0)) (copy 0 (embedG k k' 0) ten)

/-- Unit 5: save `cg`'s answer into register `2`, pair the two, and return the answer in `0`. -/
def saveGPair : Program (k + k' + 13) :=
  seq (move (embedG k k' 0) (embedP k k' 1)) (renameRegs (embedP k k') pairMachine)

/-- Unit 5b: discard the two operands and return the answer in register `0`. -/
def finishPair : Program (k + k' + 13) :=
  seq (clear (embedP k k' 0))
    (seq (clear (embedP k k' 1)) (seq (clear 0) (move (embedP k k' 2) 0)))

/-- Unit 5. -/
def saveGFinish : Program (k + k' + 13) :=
  seq (saveGPair (k := k) (k' := k')) (finishPair (k := k) (k' := k'))

/-- The whole controller. -/
def pairController : Program (k + k' + 13) :=
  seq (seedF (k := k) (k' := k'))
    (seq (renameRegs (embedF k k') P)
      (seq (saveFSeedG (k := k) (k' := k'))
        (seq (renameRegs (embedG k k') Q) (saveGFinish (k := k) (k' := k')))))

/-! ### The fixed registers are distinct from the blocks -/

theorem zero_ne_ten : (0 : Fin (k + k' + 13)) ≠ ten := by
  intro h; have := congrArg Fin.val h; simp [ten] at this

/-! ### Interface states

The register file expected between units, written down before the transition lemmas so that each
splice has a small stated interface and no proof accumulates an unfolded register function. -/

/-- After unit 1: the input, and a copy of it where `cf` will read it. -/
def state1 (n : ℕ) : Fin (k + k' + 13) → ℕ :=
  fun r => if r = 0 then n else if r = embedF k k' 0 then n else 0

/-- After calling `cf`: its answer sits in its own input register, the input is untouched. -/
def state2 (n a : ℕ) : Fin (k + k' + 13) → ℕ :=
  fun r => if r = 0 then n else if r = embedF k k' 0 then a else 0

/-- After unit 3: `cf`'s answer saved, `cg` seeded from the still-untouched input. -/
def state3 (n a : ℕ) : Fin (k + k' + 13) → ℕ :=
  fun r => if r = 0 then n else if r = embedP k k' 0 then a
    else if r = embedG k k' 0 then n else 0

/-- After calling `cg`. -/
def state4 (n a b : ℕ) : Fin (k + k' + 13) → ℕ :=
  fun r => if r = 0 then n else if r = embedP k k' 0 then a
    else if r = embedG k k' 0 then b else 0

/-! ### The three total units -/

theorem run_seedF (n : ℕ) :
    ∃ N, (∀ m < N, (run (seedF (k := k) (k' := k')) ⟨0, unaryConfig (k + k' + 12) n⟩ m).pc <
        (seedF (k := k) (k' := k')).length) ∧
      run (seedF (k := k) (k' := k')) ⟨0, unaryConfig (k + k' + 12) n⟩ N =
        ⟨(seedF (k := k) (k' := k')).length, state1 n⟩ := by
  rw [seedF]
  obtain ⟨N, hin, hex⟩ :=
    realises_copy (r := (0 : Fin (k + k' + 13))) (s := embedF k k' 0) (t := ten)
      (zero_ne_embedF 0) zero_ne_ten (Ne.symm (ten_ne_embedF 0)) (unaryConfig (k + k' + 12) n)
  refine ⟨N, hin, ?_⟩
  rw [hex]
  refine congrArg _ (funext fun r => ?_)
  simp only [state1, unaryConfig, Function.update_apply]
  by_cases h1 : r = embedF k k' 0
  · subst h1; simp [(zero_ne_embedF 0).symm]
  · by_cases h2 : r = ten
    · subst h2; simp [h1, zero_ne_ten.symm]
    · simp [h1, h2]

/-- The disequalities among the controller's fixed registers and the two block entry points.
Collected once; every state transition below simplifies with the whole set. -/
theorem entry_ne (k k' : ℕ) :
    embedF k k' 0 ≠ 0 ∧ embedG k k' 0 ≠ 0 ∧ embedP k k' 0 ≠ 0 ∧ embedP k k' 1 ≠ 0 ∧
      embedP k k' 2 ≠ 0 ∧ (ten : Fin (k + k' + 13)) ≠ 0 ∧
      embedF k k' 0 ≠ embedG k k' 0 ∧ embedF k k' 0 ≠ embedP k k' 0 ∧
      embedF k k' 0 ≠ embedP k k' 1 ∧ embedF k k' 0 ≠ ten ∧
      embedG k k' 0 ≠ embedP k k' 0 ∧ embedG k k' 0 ≠ embedP k k' 1 ∧
      embedG k k' 0 ≠ ten ∧ embedP k k' 0 ≠ ten ∧ embedP k k' 1 ≠ ten ∧
      embedP k k' 0 ≠ embedP k k' 1 :=
  ⟨(zero_ne_embedF 0).symm, (zero_ne_embedG 0).symm, embedP_ne_zero 0, embedP_ne_zero 1,
    embedP_ne_zero 2, zero_ne_ten.symm, embedF_ne_embedG 0 0, (embedP_ne_embedF 0 0).symm,
    (embedP_ne_embedF 1 0).symm, (ten_ne_embedF 0).symm, (embedP_ne_embedG 0 0).symm,
    (embedP_ne_embedG 1 0).symm, (ten_ne_embedG 0).symm, embedP_ne_ten 0, embedP_ne_ten 1,
    fun h => absurd (embedP_injective h) (by decide)⟩

theorem run_saveFSeedG (n a : ℕ) :
    ∃ N, (∀ m < N, (run (saveFSeedG (k := k) (k' := k')) ⟨0, state2 n a⟩ m).pc <
        (saveFSeedG (k := k) (k' := k')).length) ∧
      run (saveFSeedG (k := k) (k' := k')) ⟨0, state2 n a⟩ N =
        ⟨(saveFSeedG (k := k) (k' := k')).length, state3 n a⟩ := by
  obtain ⟨f0, g0, p0, p1, p2, t0, fg, fp0, fp1, ft, gp0, gp1, gt, p0t, p1t, p01⟩ := entry_ne k k'
  have f0' := f0.symm; have g0' := g0.symm; have p0' := p0.symm; have p1' := p1.symm
  have p2' := p2.symm; have t0' := t0.symm; have fg' := fg.symm; have fp0' := fp0.symm
  have fp1' := fp1.symm; have ft' := ft.symm; have gp0' := gp0.symm; have gp1' := gp1.symm
  have gt' := gt.symm; have p0t' := p0t.symm; have p1t' := p1t.symm; have p01' := p01.symm
  rw [saveFSeedG]
  obtain ⟨N, hin, hex⟩ :=
    ((realises_move (Ne.symm (embedP_ne_embedF 0 0))).seq
      (realises_copy (r := (0 : Fin (k + k' + 13))) (s := embedG k k' 0) (t := ten)
        (zero_ne_embedG 0) zero_ne_ten (Ne.symm (ten_ne_embedG 0)))) (state2 n a)
  refine ⟨N, hin, ?_⟩
  rw [hex]
  refine congrArg _ (funext fun r => ?_)
  simp only [state2, state3]
  by_cases h1 : r = embedG k k' 0
  · subst h1
    simp_all
  · by_cases h2 : r = ten
    · subst h2
      simp_all
    · by_cases h3 : r = embedF k k' 0
      · subst h3
        simp_all
      · by_cases h4 : r = embedP k k' 0
        · subst h4
          simp_all
        · simp_all


/-! ### The two calls, as state transitions

`callState` is never expanded; only its two accessors are used, and only at the handful of
registers the controller cares about. -/

theorem callState_state1 (n a : ℕ) :
    callState (embedF k k') (state1 (k := k) (k' := k') n) a = state2 n a := by
  classical
  funext r
  by_cases hrng : ∃ i, r = embedF k k' i
  · obtain ⟨i, rfl⟩ := hrng
    rw [callState_apply embedF_injective]
    simp only [state2, if_neg (Ne.symm (zero_ne_embedF i))]
    by_cases hi : i = 0
    · subst hi; simp
    · rw [if_neg fun h => hi (embedF_injective h), unaryConfig_of_ne hi]
  · push Not at hrng
    rw [callState_of_not_mem _ _ hrng]
    simp only [state1, state2, if_neg (hrng 0)]

theorem callState_state3 (n a b : ℕ) :
    callState (embedG k k') (state3 (k := k) (k' := k') n a) b = state4 n a b := by
  classical
  funext r
  by_cases hrng : ∃ j, r = embedG k k' j
  · obtain ⟨j, rfl⟩ := hrng
    rw [callState_apply embedG_injective]
    simp only [state4, if_neg (Ne.symm (zero_ne_embedG j)),
      if_neg (embedP_ne_embedG 0 j).symm]
    by_cases hj : j = 0
    · subst hj; simp
    · rw [if_neg fun h => hj (embedG_injective h), unaryConfig_of_ne hj]
  · push Not at hrng
    rw [callState_of_not_mem _ _ hrng]
    simp only [state3, state4, if_neg (hrng 0)]


/-! ### Unit 5, in two halves

Six blocks in one splice made the goals unmanageable — the composite unfolds at every register
class at once. Splitting at `state5`, with `pairMachine` on one side and the cleanup on the
other, is the same interface discipline the earlier units use.

`pairMachine` goes through `blockState`, the *total* renaming API, which is what keeps it from
becoming a fourth partiality case: it is a call in the layout sense but not in the semantic one. -/

/-- After `pairMachine`: both operands still present, the answer beside them. -/
def state5 (n a b : ℕ) : Fin (k + k' + 13) → ℕ :=
  fun r => if r = 0 then n else if r = embedP k k' 0 then a
    else if r = embedP k k' 1 then b
    else if r = embedP k k' 2 then Nat.pair a b else 0

theorem run_saveGPair (n a b : ℕ) :
    ∃ N, (∀ m < N, (run (saveGPair (k := k) (k' := k')) ⟨0, state4 n a b⟩ m).pc <
        (saveGPair (k := k) (k' := k')).length) ∧
      run (saveGPair (k := k) (k' := k')) ⟨0, state4 n a b⟩ N =
        ⟨(saveGPair (k := k) (k' := k')).length, state5 n a b⟩ := by
  obtain ⟨f0, g0, p0, p1, p2, t0, fg, fp0, fp1, ft, gp0, gp1, gt, p0t, p1t, p01⟩ := entry_ne k k'
  have f0' := f0.symm; have g0' := g0.symm; have p0' := p0.symm; have p1' := p1.symm
  have p2' := p2.symm; have t0' := t0.symm; have fg' := fg.symm; have fp0' := fp0.symm
  have fp1' := fp1.symm; have ft' := ft.symm; have gp0' := gp0.symm; have gp1' := gp1.symm
  have gt' := gt.symm; have p0t' := p0t.symm; have p1t' := p1t.symm; have p01' := p01.symm
  have pz : ∀ i : Fin 9, embedP k k' i ≠ 0 := embedP_ne_zero
  have pz' : ∀ i : Fin 9, (0 : Fin (k + k' + 13)) ≠ embedP k k' i :=
    fun i => (embedP_ne_zero i).symm
  have pt : ∀ i : Fin 9, embedP k k' i ≠ ten := embedP_ne_ten
  have pt' : ∀ i : Fin 9, (ten : Fin (k + k' + 13)) ≠ embedP k k' i :=
    fun i => (embedP_ne_ten i).symm
  have pf : ∀ (i : Fin 9) (j : Fin (k + 1)), embedP k k' i ≠ embedF k k' j := embedP_ne_embedF
  have pf' : ∀ (j : Fin (k + 1)) (i : Fin 9), embedF k k' j ≠ embedP k k' i :=
    fun j i => (embedP_ne_embedF i j).symm
  have pg : ∀ (i : Fin 9) (j : Fin (k' + 1)), embedP k k' i ≠ embedG k k' j := embedP_ne_embedG
  have pg' : ∀ (j : Fin (k' + 1)) (i : Fin 9), embedG k k' j ≠ embedP k k' i :=
    fun j i => (embedP_ne_embedG i j).symm
  have fz : ∀ i : Fin (k + 1), embedF k k' i ≠ 0 := fun i => (zero_ne_embedF i).symm
  have gz : ∀ j : Fin (k' + 1), embedG k k' j ≠ 0 := fun j => (zero_ne_embedG j).symm
  have hblock : (fun i => if i = embedG k k' 0 then 0
      else if i = embedP k k' 1 then
        state4 (k := k) (k' := k') n a b (embedP k k' 1) +
          state4 (k := k) (k' := k') n a b (embedG k k' 0)
      else state4 (k := k) (k' := k') n a b i) ∘ embedP k k' =
      fun j => if j = 0 then a else if j = 1 then b else 0 := by
    funext j
    fin_cases j <;>
      simp_all [state4, embedP_injective.eq_iff, embedP_ne_zero, embedP_ne_embedG]
  rw [saveGPair]
  obtain ⟨N, hin, hex⟩ :=
    ((realises_move gp1).seq
      (realises_pairMachine.renameRegs_blockState embedP_injective)) (state4 n a b)
  refine ⟨N, hin, ?_⟩
  rw [hex]
  clear hex hin
  refine congrArg _ (funext fun r => ?_)
  dsimp only
  rcases layout_cases r with rfl | ⟨i, rfl⟩ | rfl | ⟨i, rfl⟩ | ⟨j, rfl⟩
  · rw [blockState_of_not_mem _ _ (fun i => (embedP_ne_zero i).symm)]
    simp_all [state4, state5]
  · rw [blockState_apply embedP_injective, hblock]
    simp only [state5]
    fin_cases i <;> simp_all [state4, embedP_injective.eq_iff]
  · rw [blockState_of_not_mem _ _ (fun i => (embedP_ne_ten i).symm)]
    simp_all [state4, state5]
  · rw [blockState_of_not_mem _ _ (fun j => (embedP_ne_embedF j i).symm)]
    simp_all [state4, state5]
  · rw [blockState_of_not_mem _ _ (fun i => (embedP_ne_embedG i j).symm)]
    simp_all [state4, state5, embedG_injective.eq_iff]

theorem run_finishPair (n a b : ℕ) :
    ∃ N, (∀ m < N, (run (finishPair (k := k) (k' := k')) ⟨0, state5 n a b⟩ m).pc <
        (finishPair (k := k) (k' := k')).length) ∧
      run (finishPair (k := k) (k' := k')) ⟨0, state5 n a b⟩ N =
        ⟨(finishPair (k := k) (k' := k')).length,
          unaryConfig (k + k' + 12) (Nat.pair a b)⟩ := by
  obtain ⟨f0, g0, p0, p1, p2, t0, fg, fp0, fp1, ft, gp0, gp1, gt, p0t, p1t, p01⟩ := entry_ne k k'
  have f0' := f0.symm; have g0' := g0.symm; have p0' := p0.symm; have p1' := p1.symm
  have p2' := p2.symm; have t0' := t0.symm; have p01' := p01.symm
  have pz : ∀ i : Fin 9, embedP k k' i ≠ 0 := embedP_ne_zero
  have pz' : ∀ i : Fin 9, (0 : Fin (k + k' + 13)) ≠ embedP k k' i :=
    fun i => (embedP_ne_zero i).symm
  have pt : ∀ i : Fin 9, embedP k k' i ≠ ten := embedP_ne_ten
  have pt' : ∀ i : Fin 9, (ten : Fin (k + k' + 13)) ≠ embedP k k' i :=
    fun i => (embedP_ne_ten i).symm
  have pf : ∀ (i : Fin 9) (j : Fin (k + 1)), embedP k k' i ≠ embedF k k' j := embedP_ne_embedF
  have pf' : ∀ (j : Fin (k + 1)) (i : Fin 9), embedF k k' j ≠ embedP k k' i :=
    fun j i => (embedP_ne_embedF i j).symm
  have pg : ∀ (i : Fin 9) (j : Fin (k' + 1)), embedP k k' i ≠ embedG k k' j := embedP_ne_embedG
  have pg' : ∀ (j : Fin (k' + 1)) (i : Fin 9), embedG k k' j ≠ embedP k k' i :=
    fun j i => (embedP_ne_embedG i j).symm
  have fz : ∀ i : Fin (k + 1), embedF k k' i ≠ 0 := fun i => (zero_ne_embedF i).symm
  have gz : ∀ j : Fin (k' + 1), embedG k k' j ≠ 0 := fun j => (zero_ne_embedG j).symm
  rw [finishPair]
  obtain ⟨N, hin, hex⟩ :=
    ((realises_clear (embedP k k' 0)).seq
      ((realises_clear (embedP k k' 1)).seq
        ((realises_clear (0 : Fin (k + k' + 13))).seq (realises_move p2)))) (state5 n a b)
  refine ⟨N, hin, ?_⟩
  rw [hex]
  clear hex hin
  refine congrArg _ (funext fun r => ?_)
  dsimp only
  rcases layout_cases r with rfl | ⟨i, rfl⟩ | rfl | ⟨i, rfl⟩ | ⟨j, rfl⟩
  · simp_all [state5, unaryConfig, embedP_injective.eq_iff]
  · simp only [Function.update_apply]
    fin_cases i <;>
      simp_all [state5, unaryConfig, embedP_injective.eq_iff]
  · simp_all [state5, unaryConfig]
  · simp_all [state5, unaryConfig]
  · simp_all [state5, unaryConfig]

/-- Unit 5, the two halves spliced. -/
theorem run_saveGFinish (n a b : ℕ) :
    ∃ N, (∀ m < N, (run (saveGFinish (k := k) (k' := k')) ⟨0, state4 n a b⟩ m).pc <
        (saveGFinish (k := k) (k' := k')).length) ∧
      run (saveGFinish (k := k) (k' := k')) ⟨0, state4 n a b⟩ N =
        ⟨(saveGFinish (k := k) (k' := k')).length,
          unaryConfig (k + k' + 12) (Nat.pair a b)⟩ := by
  obtain ⟨N1, h1in, h1ex⟩ := run_saveGPair (k := k) (k' := k') n a b
  obtain ⟨N2, h2in, h2ex⟩ := run_finishPair (k := k) (k' := k') n a b
  exact ⟨N1 + N2, join_exit h1in h1ex h2in h2ex⟩

/-! ## The closure theorem

Neither clause needs a case split. The exit clause gets `a` and `b` from `mem_eval_pair` and
splices the five exits; the halting clause peels the controller forwards, and the three
operational cases — the first call cannot halt, the first does and the second cannot, both do —
are where that argument can *stop*, not branches Lean has to enumerate. -/

theorem CleanPartComputesUnary.pair {P : Program (k + 1)} {Q : Program (k' + 1)}
    {f g : ℕ →. ℕ} (hf : CleanPartComputesUnary P f) (hg : CleanPartComputesUnary Q g) :
    CleanPartComputesUnary (pairController P Q) fun n => Nat.pair <$> f n <*> g n := by
  intro n
  have hxF : state1 (k := k) (k' := k') n (embedF k k' 0) = n := by
    simp [state1, (zero_ne_embedF 0).symm]
  have hcF : ∀ i, i ≠ 0 → state1 (k := k) (k' := k') n (embedF k k' i) = 0 := by
    intro i hi
    have hne : embedF k k' i ≠ embedF k k' 0 := fun h => hi (embedF_injective h)
    simp [state1, (zero_ne_embedF i).symm, hne]
  have hxG : ∀ a, state3 (k := k) (k' := k') n a (embedG k k' 0) = n := by
    intro a
    simp [state3, (zero_ne_embedG 0).symm, (embedP_ne_embedG 0 0).symm]
  have hcG : ∀ a j, j ≠ 0 → state3 (k := k) (k' := k') n a (embedG k k' j) = 0 := by
    intro a j hj
    have hne : embedG k k' j ≠ embedG k k' 0 := fun h => hj (embedG_injective h)
    simp [state3, (zero_ne_embedG j).symm, (embedP_ne_embedG 0 j).symm, hne]
  refine ⟨fun y hy => ?_, fun hh => ?_⟩
  · obtain ⟨a, ha, b, hb, rfl⟩ := mem_eval_pair.mp hy
    obtain ⟨N1, i1, e1⟩ := run_seedF (k := k) (k' := k') n
    obtain ⟨N2, i2, e2⟩ := hf.call_exit embedF_injective hxF hcF ha
    rw [callState_state1] at e2
    obtain ⟨N3, i3, e3⟩ := run_saveFSeedG (k := k) (k' := k') n a
    obtain ⟨N4, i4, e4⟩ := hg.call_exit embedG_injective (hxG a) (hcG a) hb
    rw [callState_state3] at e4
    obtain ⟨N5, i5, e5⟩ := run_saveGFinish (k := k) (k' := k') n a b
    obtain ⟨j45, f45⟩ := join_exit i4 e4 i5 e5
    obtain ⟨j345, f345⟩ := join_exit i3 e3 j45 f45
    obtain ⟨j2345, f2345⟩ := join_exit i2 e2 j345 f345
    exact ⟨N1 + (N2 + (N3 + (N4 + N5))), join_exit i1 e1 j2345 f2345⟩
  · -- peel the seeding block, reaching the first call
    obtain ⟨N1, i1, e1⟩ := run_seedF (k := k) (k' := k') n
    have h1 := (halts_append_of_exits i1 (by rw [e1])).mp hh
    rw [show (run (seedF (k := k) (k' := k')) ⟨0, unaryConfig (k + k' + 12) n⟩ N1).regs =
      state1 n from by rw [e1]] at h1
    -- the first call halts, so `f n` converges
    have hdf := (hf.call_halts_iff embedF_injective hxF hcF).mp (halts_prefix_of_halts_append h1)
    obtain ⟨N2, i2, e2⟩ := hf.call_exit embedF_injective hxF hcF (Part.get_mem hdf)
    rw [callState_state1] at e2
    have h2 := (halts_append_of_exits i2 (by rw [e2])).mp h1
    rw [show (run (renameRegs (embedF k k') P) ⟨0, state1 n⟩ N2).regs =
      state2 n ((f n).get hdf) from by rw [e2]] at h2
    -- peel the saving-and-seeding block, reaching the second call
    obtain ⟨N3, i3, e3⟩ := run_saveFSeedG (k := k) (k' := k') n ((f n).get hdf)
    have h3 := (halts_append_of_exits i3 (by rw [e3])).mp h2
    rw [show (run (saveFSeedG (k := k) (k' := k')) ⟨0, state2 n ((f n).get hdf)⟩ N3).regs =
      state3 n ((f n).get hdf) from by rw [e3]] at h3
    have hdg := (hg.call_halts_iff embedG_injective (hxG _) (hcG _)).mp
      (halts_prefix_of_halts_append h3)
    exact Part.dom_iff_mem.mpr ⟨Nat.pair ((f n).get hdf) ((g n).get hdg),
      mem_eval_pair.mpr ⟨_, Part.get_mem hdf, _, Part.get_mem hdg, rfl⟩⟩

/-- **`Code.pair`.** A corollary of the closure theorem and nothing else: the two `mem_` lemmas
identify the applicative source semantics with the existential the machine proof used. -/
theorem CleanPartComputesUnary.codePair {P : Program (k + 1)} {Q : Program (k' + 1)}
    {cf cg : Nat.Partrec.Code} (hf : CleanPartComputesUnary P cf.eval)
    (hg : CleanPartComputesUnary Q cg.eval) :
    CleanPartComputesUnary (pairController P Q) (Nat.Partrec.Code.pair cf cg).eval :=
  (hf.pair hg).congr fun n => Part.ext fun y => by rw [mem_eval_code_pair, mem_eval_pair]

end RegisterMachine

end Hilbert10


/- Source: Hilbert10.Internal.CodePrec, Hilbert10 v2.3.0, Apache-2.0. -/
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# The source semantics of `Nat.Partrec.Code.prec`

Issue #42, before any register is chosen. `Code.prec`'s evaluation is written with `Nat.rec`
inside `Nat.unpaired`, and the recursion, the nested pairing and the `Part` bind would all reach
the machine proof if it were used in that form.

`precSem` names the recurrence instead, and `eval_prec_eq` is the bridge, proved once:

```lean
precSem f g a 0       = f a
precSem f g a (k + 1) = precSem f g a k >>= fun acc => g (Nat.pair a (Nat.pair k acc))
```

Mathlib's `eval_prec_zero` and `eval_prec_succ` supply both cases, so the bridge is an induction
and nothing more.
-/

namespace Hilbert10

namespace RegisterMachine

open Nat.Partrec (Code)

/-- The primitive-recursion recurrence, named. `a` is the preserved parameter, `k` the index, and
the accumulator is threaded through the bind. -/
def precSem (f g : ℕ →. ℕ) (a : ℕ) : ℕ → Part ℕ
  | 0 => f a
  | k + 1 => precSem f g a k >>= fun acc => g (Nat.pair a (Nat.pair k acc))

@[simp] theorem precSem_zero (f g : ℕ →. ℕ) (a : ℕ) : precSem f g a 0 = f a := rfl

theorem precSem_succ (f g : ℕ →. ℕ) (a k : ℕ) :
    precSem f g a (k + 1) = precSem f g a k >>= fun acc => g (Nat.pair a (Nat.pair k acc)) :=
  rfl

/-- The step of the recurrence, as an existential — the form the loop's one-turn theorem wants. -/
theorem mem_precSem_succ {f g : ℕ →. ℕ} {a k y : ℕ} :
    y ∈ precSem f g a (k + 1) ↔
      ∃ acc ∈ precSem f g a k, y ∈ g (Nat.pair a (Nat.pair k acc)) := by
  rw [precSem_succ]
  exact Part.mem_bind_iff

/-- The base case converges whenever any later stage does. This is what lets the controller's
completeness proof invoke the base machine at all. -/
theorem mem_precSem_base {f g : ℕ →. ℕ} {a n y : ℕ} (hy : y ∈ precSem f g a n) :
    ∃ acc, acc ∈ f a := by
  induction n generalizing y with
  | zero => exact ⟨y, hy⟩
  | succ n ih =>
    obtain ⟨mid, hmid, _⟩ := mem_precSem_succ.mp hy
    exact ih hmid

/-- **The bridge.** `Code.prec`'s evaluation on a paired input is the recurrence. -/
theorem eval_prec_eq (cf cg : Code) (a n : ℕ) :
    (Code.prec cf cg).eval (Nat.pair a n) = precSem cf.eval cg.eval a n := by
  induction n with
  | zero => rw [Code.eval_prec_zero, precSem_zero]
  | succ n ih => rw [Code.eval_prec_succ, ih, precSem_succ]

/-- The same for an arbitrary input, which is what the machine actually receives. -/
theorem eval_prec_unpair (cf cg : Code) (x : ℕ) :
    (Code.prec cf cg).eval x = precSem cf.eval cg.eval x.unpair.1 x.unpair.2 := by
  conv_lhs => rw [← Nat.pair_unpair x]
  exact eval_prec_eq cf cg _ _

/-- The loop invariant's semantic step: one successful call to the step machine advances the
accumulator from stage `k` to stage `k + 1`. -/
theorem mem_precSem_step {f g : ℕ →. ℕ} {a k acc acc' : ℕ} (h : acc ∈ precSem f g a k)
    (h' : acc' ∈ g (Nat.pair a (Nat.pair k acc))) : acc' ∈ precSem f g a (k + 1) :=
  mem_precSem_succ.mpr ⟨acc, h, h'⟩

/-! ## The controller's register layout

`Fin (k + k' + 32)`:

| register | role |
|---|---|
| `0` | the input, and at the end the answer |
| `1` | the parameter `a` |
| `2` | the current index `k` |
| `3` | the remaining iterations `r` |
| `4` | the accumulator |
| `5` | the temporary `copy` borrows |
| `6`–`14` | the inner `pairMachine` block, computing `Nat.pair k acc` |
| `15`–`23` | the outer `pairMachine` block, computing `Nat.pair a` of that |
| `24`–`29` | the `unpairLoop` block, used once on the way in |
| `30 …` | the base callee's block, then the step callee's |

**Two pairing blocks, not one.** Sharing a single block is safe — the two pairings are
sequential and `pairMachine` returns its scratch clean — but reusing it costs a clear-and-move
phase between them, which is four more blocks and two more interface states in the turn proof.
Nine registers are cheaper than that.

**The outer pairing's result reaches the step callee by `copy`.** Making `pairMachine`'s result
register *be* the callee's input would save the copy, but the two embeddings would then overlap
in one point and every separation lemma below would acquire a case split. Keeping this section
flat is what it is for.

None of this is allocation: five explicit offsets, written down once. -/

variable (k k')

/-- The parameter `a`. -/ def rA : Fin (k + k' + 32) := ⟨1, by omega⟩
/-- The current index. -/ def rK : Fin (k + k' + 32) := ⟨2, by omega⟩
/-- The remaining iterations. -/ def rR : Fin (k + k' + 32) := ⟨3, by omega⟩
/-- The accumulator. -/ def rAcc : Fin (k + k' + 32) := ⟨4, by omega⟩
/-- The temporary `copy` borrows. -/ def rTmp : Fin (k + k' + 32) := ⟨5, by omega⟩

/-- The inner pairing block, for `Nat.pair k acc`. -/
def embedPairA (i : Fin 9) : Fin (k + k' + 32) := ⟨6 + i.val, by omega⟩

/-- The outer pairing block, for `Nat.pair a` of the inner result. -/
def embedPairB (i : Fin 9) : Fin (k + k' + 32) := ⟨15 + i.val, by omega⟩

/-- The `unpairLoop` block. -/
def embedUnpair (i : Fin 6) : Fin (k + k' + 32) := ⟨24 + i.val, by omega⟩

/-- The base callee's block. -/
def embedBase (i : Fin (k + 1)) : Fin (k + k' + 32) := ⟨30 + i.val, by omega⟩

/-- The step callee's block. -/
def embedStep (j : Fin (k' + 1)) : Fin (k + k' + 32) := ⟨31 + k + j.val, by omega⟩

variable {k k'}

@[simp] theorem rA_val : (rA k k').val = 1 := rfl
@[simp] theorem rK_val : (rK k k').val = 2 := rfl
@[simp] theorem rR_val : (rR k k').val = 3 := rfl
@[simp] theorem rAcc_val : (rAcc k k').val = 4 := rfl
@[simp] theorem rTmp_val : (rTmp k k').val = 5 := rfl
@[simp] theorem embedPairA_val (i : Fin 9) : (embedPairA k k' i).val = 6 + i.val := rfl
@[simp] theorem embedPairB_val (i : Fin 9) : (embedPairB k k' i).val = 15 + i.val := rfl
@[simp] theorem embedUnpair_val (i : Fin 6) : (embedUnpair k k' i).val = 24 + i.val := rfl
@[simp] theorem embedBase_val (i : Fin (k + 1)) : (embedBase k k' i).val = 30 + i.val := rfl
@[simp] theorem embedStep_val (j : Fin (k' + 1)) :
    (embedStep k k' j).val = 31 + k + j.val := rfl

theorem embedPairA_injective : Function.Injective (embedPairA k k') := fun i j h =>
  Fin.ext (by have := congrArg Fin.val h; simp at this; omega)

theorem embedPairB_injective : Function.Injective (embedPairB k k') := fun i j h =>
  Fin.ext (by have := congrArg Fin.val h; simp at this; omega)

theorem embedUnpair_injective : Function.Injective (embedUnpair k k') := fun i j h =>
  Fin.ext (by have := congrArg Fin.val h; simp at this; omega)

theorem embedBase_injective : Function.Injective (embedBase k k') := fun i j h =>
  Fin.ext (by have := congrArg Fin.val h; simp at this; omega)

theorem embedStep_injective : Function.Injective (embedStep k k') := fun i j h =>
  Fin.ext (by have := congrArg Fin.val h; simp at this; omega)

/-- **The layout is exhaustive**: `6 + 9 + 9 + 6 + (k+1) + (k'+1) = k + k' + 32`. -/
theorem precLayout_cases (r : Fin (k + k' + 32)) :
    r = 0 ∨ r = rA k k' ∨ r = rK k k' ∨ r = rR k k' ∨ r = rAcc k k' ∨ r = rTmp k k' ∨
      (∃ i, r = embedPairA k k' i) ∨ (∃ i, r = embedPairB k k' i) ∨
      (∃ i, r = embedUnpair k k' i) ∨ (∃ i, r = embedBase k k' i) ∨
      ∃ j, r = embedStep k k' j := by
  have hr := r.isLt
  rcases (show r.val = 0 ∨ r.val = 1 ∨ r.val = 2 ∨ r.val = 3 ∨ r.val = 4 ∨ r.val = 5 ∨
      (6 ≤ r.val ∧ r.val ≤ 14) ∨ (15 ≤ r.val ∧ r.val ≤ 23) ∨ (24 ≤ r.val ∧ r.val ≤ 29) ∨
      (30 ≤ r.val ∧ r.val ≤ 30 + k) ∨ 31 + k ≤ r.val by omega)
    with h | h | h | h | h | h | h | h | h | h | h
  · exact Or.inl (Fin.ext (by simpa using h))
  · exact Or.inr (Or.inl (Fin.ext (by simpa using h)))
  · exact Or.inr (Or.inr (Or.inl (Fin.ext (by simpa using h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext (by simpa using h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext (by simpa using h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext (by simpa using h)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨⟨r.val - 6, by omega⟩, Fin.ext (by simp; omega)⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨⟨r.val - 15, by omega⟩, Fin.ext (by simp; omega)⟩)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨⟨r.val - 24, by omega⟩, Fin.ext (by simp; omega)⟩))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨⟨r.val - 30, by omega⟩, Fin.ext (by simp; omega)⟩)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨⟨r.val - 31 - k, by omega⟩, Fin.ext (by simp; omega)⟩)))))))))

/-! ### Separation

Bundled per block rather than per pair: the register case analysis quantifies over whole blocks,
so that is the shape the proofs consume. -/

theorem precFixed_ne :
    (0 : Fin (k + k' + 32)) ≠ rA k k' ∧ (0 : Fin (k + k' + 32)) ≠ rK k k' ∧
    (0 : Fin (k + k' + 32)) ≠ rR k k' ∧ (0 : Fin (k + k' + 32)) ≠ rAcc k k' ∧
    (0 : Fin (k + k' + 32)) ≠ rTmp k k' ∧ rA k k' ≠ rK k k' ∧ rA k k' ≠ rR k k' ∧
    rA k k' ≠ rAcc k k' ∧ rA k k' ≠ rTmp k k' ∧ rK k k' ≠ rR k k' ∧ rK k k' ≠ rAcc k k' ∧
    rK k k' ≠ rTmp k k' ∧ rR k k' ≠ rAcc k k' ∧ rR k k' ≠ rTmp k k' ∧ rAcc k k' ≠ rTmp k k' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (intro h; have := congrArg Fin.val h; simp at this)

theorem embedPairA_ne_fixed (i : Fin 9) :
    embedPairA k k' i ≠ 0 ∧ embedPairA k k' i ≠ rA k k' ∧ embedPairA k k' i ≠ rK k k' ∧
    embedPairA k k' i ≠ rR k k' ∧ embedPairA k k' i ≠ rAcc k k' ∧
    embedPairA k k' i ≠ rTmp k k' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (intro h; have := congrArg Fin.val h; simp at this; all_goals omega)

theorem embedPairB_ne_fixed (i : Fin 9) :
    embedPairB k k' i ≠ 0 ∧ embedPairB k k' i ≠ rA k k' ∧ embedPairB k k' i ≠ rK k k' ∧
    embedPairB k k' i ≠ rR k k' ∧ embedPairB k k' i ≠ rAcc k k' ∧
    embedPairB k k' i ≠ rTmp k k' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (intro h; have := congrArg Fin.val h; simp at this; all_goals omega)

theorem embedUnpair_ne_fixed (i : Fin 6) :
    embedUnpair k k' i ≠ 0 ∧ embedUnpair k k' i ≠ rA k k' ∧ embedUnpair k k' i ≠ rK k k' ∧
    embedUnpair k k' i ≠ rR k k' ∧ embedUnpair k k' i ≠ rAcc k k' ∧
    embedUnpair k k' i ≠ rTmp k k' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (intro h; have := congrArg Fin.val h; simp at this; all_goals omega)

theorem embedBase_ne_fixed (i : Fin (k + 1)) :
    embedBase k k' i ≠ 0 ∧ embedBase k k' i ≠ rA k k' ∧ embedBase k k' i ≠ rK k k' ∧
    embedBase k k' i ≠ rR k k' ∧ embedBase k k' i ≠ rAcc k k' ∧
    embedBase k k' i ≠ rTmp k k' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (intro h; have := congrArg Fin.val h; simp at this; all_goals omega)

theorem embedStep_ne_fixed (j : Fin (k' + 1)) :
    embedStep k k' j ≠ 0 ∧ embedStep k k' j ≠ rA k k' ∧ embedStep k k' j ≠ rK k k' ∧
    embedStep k k' j ≠ rR k k' ∧ embedStep k k' j ≠ rAcc k k' ∧
    embedStep k k' j ≠ rTmp k k' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (intro h; have := congrArg Fin.val h; simp at this; all_goals omega)

theorem embedPairA_ne_embedPairB (i j : Fin 9) : embedPairA k k' i ≠ embedPairB k k' j := by
  intro h; have := congrArg Fin.val h; simp at this; omega

theorem embedPairA_ne_embedUnpair (i : Fin 9) (j : Fin 6) :
    embedPairA k k' i ≠ embedUnpair k k' j := by
  intro h; have := congrArg Fin.val h; simp at this; omega

theorem embedPairA_ne_embedBase (i : Fin 9) (j : Fin (k + 1)) :
    embedPairA k k' i ≠ embedBase k k' j := by
  intro h; have := congrArg Fin.val h; simp at this; omega

theorem embedPairA_ne_embedStep (i : Fin 9) (j : Fin (k' + 1)) :
    embedPairA k k' i ≠ embedStep k k' j := by
  intro h; have := congrArg Fin.val h; simp at this; omega

theorem embedPairB_ne_embedUnpair (i : Fin 9) (j : Fin 6) :
    embedPairB k k' i ≠ embedUnpair k k' j := by
  intro h; have := congrArg Fin.val h; simp at this; omega

theorem embedPairB_ne_embedBase (i : Fin 9) (j : Fin (k + 1)) :
    embedPairB k k' i ≠ embedBase k k' j := by
  intro h; have := congrArg Fin.val h; simp at this; omega

theorem embedPairB_ne_embedStep (i : Fin 9) (j : Fin (k' + 1)) :
    embedPairB k k' i ≠ embedStep k k' j := by
  intro h; have := congrArg Fin.val h; simp at this; omega

theorem embedUnpair_ne_embedBase (i : Fin 6) (j : Fin (k + 1)) :
    embedUnpair k k' i ≠ embedBase k k' j := by
  intro h; have := congrArg Fin.val h; simp at this; omega

theorem embedUnpair_ne_embedStep (i : Fin 6) (j : Fin (k' + 1)) :
    embedUnpair k k' i ≠ embedStep k k' j := by
  intro h; have := congrArg Fin.val h; simp at this; omega

theorem embedBase_ne_embedStep (i : Fin (k + 1)) (j : Fin (k' + 1)) :
    embedBase k k' i ≠ embedStep k k' j := by
  intro h; have := congrArg Fin.val h; simp at this; omega

/- The same facts in the reverse orientation.

A register condition reaches `simp` as an *equation*, so the canonical disequality bundle only
fires if the equation is already the right way round. `ne_comm` cannot help — it acts on
disequalities. `eq_comm` can, but only sometimes: it normalises by term order, which puts
`rA k k' = embedPairA k k' i` the useful way round but leaves `0 = embedPairA k k' i` and
`embedBase k k' i = embedPairA k k' j` untouched, because a numeral and a differently-named
embedding order the other way. Rather than depend on which way `simp` happens to orient a given
pair, both directions are stated. Bundled, so this is sixteen declarations rather than
fifty-five. -/
theorem precFixed_ne' :
    rA k k' ≠ (0 : Fin (k + k' + 32)) ∧ rK k k' ≠ (0 : Fin (k + k' + 32)) ∧
    rR k k' ≠ (0 : Fin (k + k' + 32)) ∧ rAcc k k' ≠ (0 : Fin (k + k' + 32)) ∧
    rTmp k k' ≠ (0 : Fin (k + k' + 32)) ∧ rK k k' ≠ rA k k' ∧ rR k k' ≠ rA k k' ∧
    rAcc k k' ≠ rA k k' ∧ rTmp k k' ≠ rA k k' ∧ rR k k' ≠ rK k k' ∧ rAcc k k' ≠ rK k k' ∧
    rTmp k k' ≠ rK k k' ∧ rAcc k k' ≠ rR k k' ∧ rTmp k k' ≠ rR k k' ∧ rTmp k k' ≠ rAcc k k' :=
  ⟨precFixed_ne.1.symm, precFixed_ne.2.1.symm, precFixed_ne.2.2.1.symm,
    precFixed_ne.2.2.2.1.symm, precFixed_ne.2.2.2.2.1.symm, precFixed_ne.2.2.2.2.2.1.symm,
    precFixed_ne.2.2.2.2.2.2.1.symm, precFixed_ne.2.2.2.2.2.2.2.1.symm,
    precFixed_ne.2.2.2.2.2.2.2.2.1.symm, precFixed_ne.2.2.2.2.2.2.2.2.2.1.symm,
    precFixed_ne.2.2.2.2.2.2.2.2.2.2.1.symm, precFixed_ne.2.2.2.2.2.2.2.2.2.2.2.1.symm,
    precFixed_ne.2.2.2.2.2.2.2.2.2.2.2.2.1.symm,
    precFixed_ne.2.2.2.2.2.2.2.2.2.2.2.2.2.1.symm,
    precFixed_ne.2.2.2.2.2.2.2.2.2.2.2.2.2.2.symm⟩

theorem embedPairA_ne_fixed' (i : Fin 9) :
    (0 : Fin (k + k' + 32)) ≠ embedPairA k k' i ∧ rA k k' ≠ embedPairA k k' i ∧
    rK k k' ≠ embedPairA k k' i ∧
    rR k k' ≠ embedPairA k k' i ∧ rAcc k k' ≠ embedPairA k k' i ∧ rTmp k k' ≠ embedPairA k k' i :=
  ⟨(embedPairA_ne_fixed i).1.symm, (embedPairA_ne_fixed i).2.1.symm,
    (embedPairA_ne_fixed i).2.2.1.symm,
    (embedPairA_ne_fixed i).2.2.2.1.symm, (embedPairA_ne_fixed i).2.2.2.2.1.symm,
    (embedPairA_ne_fixed i).2.2.2.2.2.symm⟩

theorem embedPairB_ne_fixed' (i : Fin 9) :
    (0 : Fin (k + k' + 32)) ≠ embedPairB k k' i ∧ rA k k' ≠ embedPairB k k' i ∧
    rK k k' ≠ embedPairB k k' i ∧
    rR k k' ≠ embedPairB k k' i ∧ rAcc k k' ≠ embedPairB k k' i ∧ rTmp k k' ≠ embedPairB k k' i :=
  ⟨(embedPairB_ne_fixed i).1.symm, (embedPairB_ne_fixed i).2.1.symm,
    (embedPairB_ne_fixed i).2.2.1.symm,
    (embedPairB_ne_fixed i).2.2.2.1.symm, (embedPairB_ne_fixed i).2.2.2.2.1.symm,
    (embedPairB_ne_fixed i).2.2.2.2.2.symm⟩

theorem embedUnpair_ne_fixed' (i : Fin 6) :
    (0 : Fin (k + k' + 32)) ≠ embedUnpair k k' i ∧ rA k k' ≠ embedUnpair k k' i ∧
    rK k k' ≠ embedUnpair k k' i ∧
    rR k k' ≠ embedUnpair k k' i ∧ rAcc k k' ≠ embedUnpair k k' i ∧
    rTmp k k' ≠ embedUnpair k k' i :=
  ⟨(embedUnpair_ne_fixed i).1.symm, (embedUnpair_ne_fixed i).2.1.symm,
    (embedUnpair_ne_fixed i).2.2.1.symm,
    (embedUnpair_ne_fixed i).2.2.2.1.symm, (embedUnpair_ne_fixed i).2.2.2.2.1.symm,
    (embedUnpair_ne_fixed i).2.2.2.2.2.symm⟩

theorem embedBase_ne_fixed' (i : Fin (k + 1)) :
    (0 : Fin (k + k' + 32)) ≠ embedBase k k' i ∧ rA k k' ≠ embedBase k k' i ∧
    rK k k' ≠ embedBase k k' i ∧
    rR k k' ≠ embedBase k k' i ∧ rAcc k k' ≠ embedBase k k' i ∧ rTmp k k' ≠ embedBase k k' i :=
  ⟨(embedBase_ne_fixed i).1.symm, (embedBase_ne_fixed i).2.1.symm,
    (embedBase_ne_fixed i).2.2.1.symm,
    (embedBase_ne_fixed i).2.2.2.1.symm, (embedBase_ne_fixed i).2.2.2.2.1.symm,
    (embedBase_ne_fixed i).2.2.2.2.2.symm⟩

theorem embedStep_ne_fixed' (i : Fin (k' + 1)) :
    (0 : Fin (k + k' + 32)) ≠ embedStep k k' i ∧ rA k k' ≠ embedStep k k' i ∧
    rK k k' ≠ embedStep k k' i ∧
    rR k k' ≠ embedStep k k' i ∧ rAcc k k' ≠ embedStep k k' i ∧ rTmp k k' ≠ embedStep k k' i :=
  ⟨(embedStep_ne_fixed i).1.symm, (embedStep_ne_fixed i).2.1.symm,
    (embedStep_ne_fixed i).2.2.1.symm,
    (embedStep_ne_fixed i).2.2.2.1.symm, (embedStep_ne_fixed i).2.2.2.2.1.symm,
    (embedStep_ne_fixed i).2.2.2.2.2.symm⟩

theorem embedPairB_ne_embedPairA (i : Fin 9) (j : Fin 9) : embedPairB k k' i ≠ embedPairA k k' j :=
  (embedPairA_ne_embedPairB j i).symm

theorem embedUnpair_ne_embedPairA (i : Fin 6) (j : Fin 9) :
    embedUnpair k k' i ≠ embedPairA k k' j :=
  (embedPairA_ne_embedUnpair j i).symm

theorem embedBase_ne_embedPairA (i : Fin (k + 1)) (j : Fin 9) :
    embedBase k k' i ≠ embedPairA k k' j :=
  (embedPairA_ne_embedBase j i).symm

theorem embedStep_ne_embedPairA (i : Fin (k' + 1)) (j : Fin 9) :
    embedStep k k' i ≠ embedPairA k k' j :=
  (embedPairA_ne_embedStep j i).symm

theorem embedUnpair_ne_embedPairB (i : Fin 6) (j : Fin 9) :
    embedUnpair k k' i ≠ embedPairB k k' j :=
  (embedPairB_ne_embedUnpair j i).symm

theorem embedBase_ne_embedPairB (i : Fin (k + 1)) (j : Fin 9) :
    embedBase k k' i ≠ embedPairB k k' j :=
  (embedPairB_ne_embedBase j i).symm

theorem embedStep_ne_embedPairB (i : Fin (k' + 1)) (j : Fin 9) :
    embedStep k k' i ≠ embedPairB k k' j :=
  (embedPairB_ne_embedStep j i).symm

theorem embedBase_ne_embedUnpair (i : Fin (k + 1)) (j : Fin 6) :
    embedBase k k' i ≠ embedUnpair k k' j :=
  (embedUnpair_ne_embedBase j i).symm

theorem embedStep_ne_embedUnpair (i : Fin (k' + 1)) (j : Fin 6) :
    embedStep k k' i ≠ embedUnpair k k' j :=
  (embedUnpair_ne_embedStep j i).symm

theorem embedStep_ne_embedBase (i : Fin (k' + 1)) (j : Fin (k + 1)) :
    embedStep k k' i ≠ embedBase k k' j :=
  (embedBase_ne_embedStep j i).symm

/- Registering the separation theorems as *declarations* rather than passing them as
hypotheses is what makes them usable: `simp` decomposes a conjunction on registration, but
`simp_all` cannot decompose a local conjunction hypothesis into rewrite rules. The reversed
bundles above cover orientation. Kept file-local — this is arithmetic
about one layout, not a fact anyone else should be simplifying with. -/
attribute [local simp] precFixed_ne embedPairA_ne_fixed embedPairB_ne_fixed
  embedUnpair_ne_fixed embedBase_ne_fixed embedStep_ne_fixed
  embedPairA_ne_embedPairB embedPairA_ne_embedUnpair embedPairA_ne_embedBase
  embedPairA_ne_embedStep embedPairB_ne_embedUnpair embedPairB_ne_embedBase
  embedPairB_ne_embedStep embedUnpair_ne_embedBase embedUnpair_ne_embedStep
  embedBase_ne_embedStep
  precFixed_ne' embedPairA_ne_fixed' embedPairB_ne_fixed' embedUnpair_ne_fixed'
  embedBase_ne_fixed' embedStep_ne_fixed'
  embedPairB_ne_embedPairA embedUnpair_ne_embedPairA embedBase_ne_embedPairA
  embedStep_ne_embedPairA embedUnpair_ne_embedPairB embedBase_ne_embedPairB
  embedStep_ne_embedPairB embedBase_ne_embedUnpair embedStep_ne_embedUnpair
  embedStep_ne_embedBase

/-! ### The loop head

The interface the whole loop is proved against, parameterised by the index and the accumulator
exactly as #51's `state1`–`state5` were parameterised by their contents.

The remaining count `rem` is what the loop branches on. There is no stored target and no
comparison: the `dec` that tests `rem` *is* the branch, so `idx ≤ n` never has to be maintained
and no residual has to be related back to the run length. -/

/-- The register file at a loop head. -/
def precLoopState (a idx rem acc : ℕ) : Fin (k + k' + 32) → ℕ :=
  fun r => if r = rA k k' then a else if r = rK k k' then idx
    else if r = rR k k' then rem else if r = rAcc k k' then acc else 0

/-! ## The turn body

Five units, `B1`–`B5`, with an interface state after each. `B4` is the only partial one; the
other four are `Realises` macros. -/

variable (P : Program (k + 1)) (Q : Program (k' + 1))

/-- `B1`: compute `Nat.pair k acc` in the inner block. -/
def precInner : Program (k + k' + 32) :=
  seq (copy (rK k k') (embedPairA k k' 0) (rTmp k k'))
    (seq (copy (rAcc k k') (embedPairA k k' 1) (rTmp k k'))
      (renameRegs (embedPairA k k') pairMachine))

/-- `B2`: compute `Nat.pair a` of that in the outer block. -/
def precOuter : Program (k + k' + 32) :=
  seq (copy (rA k k') (embedPairB k k' 0) (rTmp k k'))
    (seq (copy (embedPairA k k' 2) (embedPairB k k' 1) (rTmp k k'))
      (renameRegs (embedPairB k k') pairMachine))

/-- `B3`: hand the argument to the step callee and give both pairing blocks back clean. -/
def precSeedStep : Program (k + k' + 32) :=
  seq (copy (embedPairB k k' 2) (embedStep k k' 0) (rTmp k k'))
    (seq (clear (embedPairA k k' 0))
      (seq (clear (embedPairA k k' 1))
        (seq (clear (embedPairA k k' 2))
          (seq (clear (embedPairB k k' 0))
            (seq (clear (embedPairB k k' 1)) (clear (embedPairB k k' 2)))))))

/-- `B5`: replace the accumulator with the step callee's answer. -/
def precSaveAcc : Program (k + k' + 32) :=
  seq (clear (rAcc k k')) (move (embedStep k k' 0) (rAcc k k'))

/-- The whole turn body: the four total units around the one call. -/
def precBody : Program (k + k' + 32) :=
  seq (precInner (k := k) (k' := k'))
    (seq (precOuter (k := k) (k' := k'))
      (seq (precSeedStep (k := k) (k' := k'))
        (seq (renameRegs (embedStep k k') Q) (precSaveAcc (k := k) (k' := k')))))

/-- The loop: test the remaining count, run a turn, increment the index, jump back.

The `dec` at position `0` is the branch; there is no comparison and no stored target. The `inc`
at the end both counts and jumps back, so no jump gadget is needed either. -/
def precLoop : Program (k + k' + 32) :=
  [Instr.dec (rR k k') 1 ((precBody (k := k) (k' := k') Q).length + 2)] ++
    shiftJumps 1 (precBody (k := k) (k' := k') Q) ++ [Instr.inc (rK k k') 0]

theorem length_precLoop :
    (precLoop (k := k) (k' := k') Q).length = (precBody (k := k) (k' := k') Q).length + 2 := by
  simp [precLoop]

/-! ### The body's interface states -/

/-- After `B1`: the inner pairing done. -/
def precState2 (a idx rem acc : ℕ) : Fin (k + k' + 32) → ℕ :=
  fun r => if r = rA k k' then a else if r = rK k k' then idx
    else if r = rR k k' then rem else if r = rAcc k k' then acc
    else if r = embedPairA k k' 0 then idx else if r = embedPairA k k' 1 then acc
    else if r = embedPairA k k' 2 then Nat.pair idx acc else 0

/-- After `B2`: the outer pairing done. -/
def precState3 (a idx rem acc : ℕ) : Fin (k + k' + 32) → ℕ :=
  fun r => if r = rA k k' then a else if r = rK k k' then idx
    else if r = rR k k' then rem else if r = rAcc k k' then acc
    else if r = embedPairA k k' 0 then idx else if r = embedPairA k k' 1 then acc
    else if r = embedPairA k k' 2 then Nat.pair idx acc
    else if r = embedPairB k k' 0 then a
    else if r = embedPairB k k' 1 then Nat.pair idx acc
    else if r = embedPairB k k' 2 then Nat.pair a (Nat.pair idx acc) else 0

/-- After `B3`: the step callee seeded, both pairing blocks clean. -/
def precState4 (a idx rem acc : ℕ) : Fin (k + k' + 32) → ℕ :=
  fun r => if r = rA k k' then a else if r = rK k k' then idx
    else if r = rR k k' then rem else if r = rAcc k k' then acc
    else if r = embedStep k k' 0 then Nat.pair a (Nat.pair idx acc) else 0

/-- After the call: the step callee's answer in its own input register. -/
def precState5 (a idx rem acc acc' : ℕ) : Fin (k + k' + 32) → ℕ :=
  fun r => if r = rA k k' then a else if r = rK k k' then idx
    else if r = rR k k' then rem else if r = rAcc k k' then acc
    else if r = embedStep k k' 0 then acc' else 0

/-! ### Separation facts, regrouped

The body's transitions each need the fixed-register disequalities in context so that `simp_all`
can use them without an explicit argument list. Grouped rather than flat because a fifteen-way
`obtain` pattern is unreadable at every use site. -/

/-- The separation facts every body transition needs, in context. -/
theorem precFacts (k k' : ℕ) :
    ((0 : Fin (k + k' + 32)) ≠ rA k k' ∧ (0 : Fin (k + k' + 32)) ≠ rK k k' ∧
      (0 : Fin (k + k' + 32)) ≠ rR k k' ∧ (0 : Fin (k + k' + 32)) ≠ rAcc k k' ∧
      (0 : Fin (k + k' + 32)) ≠ rTmp k k') ∧
    (rA k k' ≠ rK k k' ∧ rA k k' ≠ rR k k' ∧ rA k k' ≠ rAcc k k' ∧ rA k k' ≠ rTmp k k') ∧
    (rK k k' ≠ rR k k' ∧ rK k k' ≠ rAcc k k' ∧ rK k k' ≠ rTmp k k') ∧
    (rR k k' ≠ rAcc k k' ∧ rR k k' ≠ rTmp k k') ∧ rAcc k k' ≠ rTmp k k' :=
  ⟨⟨precFixed_ne.1, precFixed_ne.2.1, precFixed_ne.2.2.1, precFixed_ne.2.2.2.1,
      precFixed_ne.2.2.2.2.1⟩,
    ⟨precFixed_ne.2.2.2.2.2.1, precFixed_ne.2.2.2.2.2.2.1, precFixed_ne.2.2.2.2.2.2.2.1,
      precFixed_ne.2.2.2.2.2.2.2.2.1⟩,
    ⟨precFixed_ne.2.2.2.2.2.2.2.2.2.1, precFixed_ne.2.2.2.2.2.2.2.2.2.2.1,
      precFixed_ne.2.2.2.2.2.2.2.2.2.2.2.1⟩,
    ⟨precFixed_ne.2.2.2.2.2.2.2.2.2.2.2.2.1, precFixed_ne.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩,
    precFixed_ne.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩


/-! ### `precInner`'s interior

A unit that ends in a renamed block call needs its *own* interior named. `blockState` takes the
incoming register file as an argument, so that argument has to be small — and after two `copy`
transformations it is a composite several lines long. `precInnerA` and `precInnerB` name the two
intermediate files, and the projection lemma is then stated about a name.

The same will be true of `precOuter`, whose block call is also preceded by two copies. -/

/-- After copying the index into the inner block's first target. -/
def precInnerA (a idx rem acc : ℕ) : Fin (k + k' + 32) → ℕ :=
  fun r => if r = rA k k' then a else if r = rK k k' then idx
    else if r = rR k k' then rem else if r = rAcc k k' then acc
    else if r = embedPairA k k' 0 then idx else 0

/-- After copying the accumulator into the inner block's second target. -/
def precInnerB (a idx rem acc : ℕ) : Fin (k + k' + 32) → ℕ :=
  fun r => if r = rA k k' then a else if r = rK k k' then idx
    else if r = rR k k' then rem else if r = rAcc k k' then acc
    else if r = embedPairA k k' 1 then acc
    else if r = embedPairA k k' 0 then idx else 0

/-- What `pairMachine` sees inside the inner block. Domain `Fin 9`, so `fin_cases` settles it and
no layout case split enters. -/
theorem precInnerB_comp_embedPairA (a idx rem acc : ℕ) :
    precInnerB (k := k) (k' := k') a idx rem acc ∘ embedPairA k k' =
      fun i => if i = 0 then idx else if i = 1 then acc else 0 := by
  have ha := fun j => (embedPairA_ne_fixed (k := k) (k' := k') j).2.1
  have hk := fun j => (embedPairA_ne_fixed (k := k) (k' := k') j).2.2.1
  have hr := fun j => (embedPairA_ne_fixed (k := k) (k' := k') j).2.2.2.1
  have hacc := fun j => (embedPairA_ne_fixed (k := k) (k' := k') j).2.2.2.2.1
  funext i
  fin_cases i <;>
    simp [precInnerB, embedPairA_injective.eq_iff, ha, hk, hr, hacc]


/-! ### `precInner`'s three stages

Each is its own top-level lemma so that no earlier exit equation is in scope when its register
case analysis runs. With the separation theorems registered above, every branch is `simp` against
the state definitions — no argument list of disequalities and no `split_ifs`. -/

/-- Stage 1: the index reaches the inner block's first target. -/
theorem run_precInner_copyK (a idx rem acc : ℕ) :
    ∃ N, (∀ m < N, (run (copy (rK k k') (embedPairA k k' 0) (rTmp k k'))
          ⟨0, precLoopState a idx rem acc⟩ m).pc <
        (copy (rK k k') (embedPairA k k' 0) (rTmp k k')).length) ∧
      run (copy (rK k k') (embedPairA k k' 0) (rTmp k k'))
        ⟨0, precLoopState a idx rem acc⟩ N =
        ⟨(copy (rK k k') (embedPairA k k' 0) (rTmp k k')).length,
          precInnerA a idx rem acc⟩ := by
  obtain ⟨N, hin, hex⟩ :=
    realises_copy (r := rK k k') (s := embedPairA k k' 0) (t := rTmp k k')
      (by simp) (by simp) (by simp)
      (precLoopState (k := k) (k' := k') a idx rem acc)
  refine ⟨N, hin, ?_⟩
  rw [hex]
  clear hex hin
  refine congrArg _ (funext fun r => ?_)
  rcases precLayout_cases r with rfl | rfl | rfl | rfl | rfl | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ |
    ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ <;>
    simp [precLoopState, precInnerA, embedPairA_injective.eq_iff]

/-- Stage 2: the accumulator reaches the second target. -/
theorem run_precInner_copyAcc (a idx rem acc : ℕ) :
    ∃ N, (∀ m < N, (run (copy (rAcc k k') (embedPairA k k' 1) (rTmp k k'))
          ⟨0, precInnerA a idx rem acc⟩ m).pc <
        (copy (rAcc k k') (embedPairA k k' 1) (rTmp k k')).length) ∧
      run (copy (rAcc k k') (embedPairA k k' 1) (rTmp k k'))
        ⟨0, precInnerA a idx rem acc⟩ N =
        ⟨(copy (rAcc k k') (embedPairA k k' 1) (rTmp k k')).length,
          precInnerB a idx rem acc⟩ := by
  obtain ⟨N, hin, hex⟩ :=
    realises_copy (r := rAcc k k') (s := embedPairA k k' 1) (t := rTmp k k')
      (by simp) (by simp) (by simp)
      (precInnerA (k := k) (k' := k') a idx rem acc)
  refine ⟨N, hin, ?_⟩
  rw [hex]
  clear hex hin
  refine congrArg _ (funext fun r => ?_)
  rcases precLayout_cases r with rfl | rfl | rfl | rfl | rfl | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ |
    ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ <;>
    simp [precInnerA, precInnerB, embedPairA_injective.eq_iff]

/-- Stage 3: the block call. Its argument is `precInnerB`, a name — which is the point of having
named the interior at all. -/
theorem run_precInner_pair (a idx rem acc : ℕ) :
    ∃ N, (∀ m < N, (run (renameRegs (embedPairA k k') pairMachine)
          ⟨0, precInnerB a idx rem acc⟩ m).pc <
        (renameRegs (embedPairA k k') pairMachine).length) ∧
      run (renameRegs (embedPairA k k') pairMachine) ⟨0, precInnerB a idx rem acc⟩ N =
        ⟨(renameRegs (embedPairA k k') pairMachine).length, precState2 a idx rem acc⟩ := by
  obtain ⟨N, hin, hex⟩ :=
    (realises_pairMachine.renameRegs_blockState embedPairA_injective)
      (precInnerB (k := k) (k' := k') a idx rem acc)
  refine ⟨N, hin, ?_⟩
  rw [hex]
  clear hex hin
  refine congrArg _ (funext fun r => ?_)
  rcases precLayout_cases r with rfl | rfl | rfl | rfl | rfl | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ |
    ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rw [blockState_of_not_mem _ _ (fun i => by simp)]
    simp [precInnerB, precState2]
  · rw [blockState_of_not_mem _ _ (fun i => by simp)]
    simp [precInnerB, precState2]
  · rw [blockState_of_not_mem _ _ (fun i => by simp)]
    simp [precInnerB, precState2]
  · rw [blockState_of_not_mem _ _ (fun i => by simp)]
    simp [precInnerB, precState2]
  · rw [blockState_of_not_mem _ _ (fun i => by simp)]
    simp [precInnerB, precState2]
  · rw [blockState_of_not_mem _ _ (fun i => by simp)]
    simp [precInnerB, precState2]
  · rw [blockState_apply embedPairA_injective, precInnerB_comp_embedPairA]
    simp only [precState2]
    fin_cases i <;> simp [embedPairA_injective.eq_iff]
  · rw [blockState_of_not_mem _ _ (fun j => by simp)]
    simp [precInnerB, precState2]
  · rw [blockState_of_not_mem _ _ (fun j => by simp)]
    simp [precInnerB, precState2]
  · rw [blockState_of_not_mem _ _ (fun j => by simp)]
    simp [precInnerB, precState2]
  · rw [blockState_of_not_mem _ _ (fun j => by simp)]
    simp [precInnerB, precState2]

/-- `B1`, the three stages spliced. -/
theorem run_precInner (a idx rem acc : ℕ) :
    ∃ N, (∀ m < N, (run (precInner (k := k) (k' := k'))
          ⟨0, precLoopState a idx rem acc⟩ m).pc < (precInner (k := k) (k' := k')).length) ∧
      run (precInner (k := k) (k' := k')) ⟨0, precLoopState a idx rem acc⟩ N =
        ⟨(precInner (k := k) (k' := k')).length, precState2 a idx rem acc⟩ := by
  rw [precInner]
  obtain ⟨N1, i1, e1⟩ := run_precInner_copyK (k := k) (k' := k') a idx rem acc
  obtain ⟨N2, i2, e2⟩ := run_precInner_copyAcc (k := k) (k' := k') a idx rem acc
  obtain ⟨N3, i3, e3⟩ := run_precInner_pair (k := k) (k' := k') a idx rem acc
  obtain ⟨j23, f23⟩ := join_exit i2 e2 i3 e3
  exact ⟨N1 + (N2 + N3), join_exit i1 e1 j23 f23⟩

/-! ### `precOuter`'s interior and three stages

The same shape as `precInner`: two named interior states, a projection lemma over `Fin 9`, three
top-level stage lemmas, spliced. -/

/-- After copying the parameter into the outer block's first target. -/
def precOuterA (a idx rem acc : ℕ) : Fin (k + k' + 32) → ℕ :=
  fun r => if r = embedPairB k k' 0 then a
    else if r = rA k k' then a else if r = rK k k' then idx
    else if r = rR k k' then rem else if r = rAcc k k' then acc
    else if r = embedPairA k k' 0 then idx else if r = embedPairA k k' 1 then acc
    else if r = embedPairA k k' 2 then Nat.pair idx acc else 0

/-- After copying the inner pairing's result into the outer block's second target. -/
def precOuterB (a idx rem acc : ℕ) : Fin (k + k' + 32) → ℕ :=
  fun r => if r = embedPairB k k' 1 then Nat.pair idx acc
    else if r = embedPairB k k' 0 then a
    else if r = rA k k' then a else if r = rK k k' then idx
    else if r = rR k k' then rem else if r = rAcc k k' then acc
    else if r = embedPairA k k' 0 then idx else if r = embedPairA k k' 1 then acc
    else if r = embedPairA k k' 2 then Nat.pair idx acc else 0

/-- What `pairMachine` sees inside the outer block. -/
theorem precOuterB_comp_embedPairB (a idx rem acc : ℕ) :
    precOuterB (k := k) (k' := k') a idx rem acc ∘ embedPairB k k' =
      fun i => if i = 0 then a else if i = 1 then Nat.pair idx acc else 0 := by
  funext i
  fin_cases i <;> simp [precOuterB, embedPairB_injective.eq_iff]

/-- Stage 1: the parameter reaches the outer block's first target. -/
theorem run_precOuter_copyA (a idx rem acc : ℕ) :
    ∃ N, (∀ m < N, (run (copy (rA k k') (embedPairB k k' 0) (rTmp k k'))
          ⟨0, precState2 a idx rem acc⟩ m).pc <
        (copy (rA k k') (embedPairB k k' 0) (rTmp k k')).length) ∧
      run (copy (rA k k') (embedPairB k k' 0) (rTmp k k'))
        ⟨0, precState2 a idx rem acc⟩ N =
        ⟨(copy (rA k k') (embedPairB k k' 0) (rTmp k k')).length,
          precOuterA a idx rem acc⟩ := by
  obtain ⟨N, hin, hex⟩ :=
    realises_copy (r := rA k k') (s := embedPairB k k' 0) (t := rTmp k k')
      (by simp) (by simp) (by simp) (precState2 (k := k) (k' := k') a idx rem acc)
  refine ⟨N, hin, ?_⟩
  rw [hex]
  clear hex hin
  refine congrArg _ (funext fun r => ?_)
  rcases precLayout_cases r with rfl | rfl | rfl | rfl | rfl | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ |
    ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ <;>
    simp [precState2, precOuterA, embedPairA_injective.eq_iff, embedPairB_injective.eq_iff]

/-- Stage 2: the inner result reaches the second target. -/
theorem run_precOuter_copyInner (a idx rem acc : ℕ) :
    ∃ N, (∀ m < N, (run (copy (embedPairA k k' 2) (embedPairB k k' 1) (rTmp k k'))
          ⟨0, precOuterA a idx rem acc⟩ m).pc <
        (copy (embedPairA k k' 2) (embedPairB k k' 1) (rTmp k k')).length) ∧
      run (copy (embedPairA k k' 2) (embedPairB k k' 1) (rTmp k k'))
        ⟨0, precOuterA a idx rem acc⟩ N =
        ⟨(copy (embedPairA k k' 2) (embedPairB k k' 1) (rTmp k k')).length,
          precOuterB a idx rem acc⟩ := by
  obtain ⟨N, hin, hex⟩ :=
    realises_copy (r := embedPairA k k' 2) (s := embedPairB k k' 1) (t := rTmp k k')
      (by simp) (by simp) (by simp) (precOuterA (k := k) (k' := k') a idx rem acc)
  refine ⟨N, hin, ?_⟩
  rw [hex]
  clear hex hin
  refine congrArg _ (funext fun r => ?_)
  rcases precLayout_cases r with rfl | rfl | rfl | rfl | rfl | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ |
    ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ <;>
    simp [precOuterA, precOuterB, embedPairA_injective.eq_iff, embedPairB_injective.eq_iff]

/-- Stage 3: the block call. -/
theorem run_precOuter_pair (a idx rem acc : ℕ) :
    ∃ N, (∀ m < N, (run (renameRegs (embedPairB k k') pairMachine)
          ⟨0, precOuterB a idx rem acc⟩ m).pc <
        (renameRegs (embedPairB k k') pairMachine).length) ∧
      run (renameRegs (embedPairB k k') pairMachine) ⟨0, precOuterB a idx rem acc⟩ N =
        ⟨(renameRegs (embedPairB k k') pairMachine).length, precState3 a idx rem acc⟩ := by
  obtain ⟨N, hin, hex⟩ :=
    (realises_pairMachine.renameRegs_blockState embedPairB_injective)
      (precOuterB (k := k) (k' := k') a idx rem acc)
  refine ⟨N, hin, ?_⟩
  rw [hex]
  clear hex hin
  refine congrArg _ (funext fun r => ?_)
  rcases precLayout_cases r with rfl | rfl | rfl | rfl | rfl | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ |
    ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rw [blockState_of_not_mem _ _ (fun i => by simp)]; simp [precOuterB, precState3]
  · rw [blockState_of_not_mem _ _ (fun i => by simp)]; simp [precOuterB, precState3]
  · rw [blockState_of_not_mem _ _ (fun i => by simp)]; simp [precOuterB, precState3]
  · rw [blockState_of_not_mem _ _ (fun i => by simp)]; simp [precOuterB, precState3]
  · rw [blockState_of_not_mem _ _ (fun i => by simp)]; simp [precOuterB, precState3]
  · rw [blockState_of_not_mem _ _ (fun i => by simp)]; simp [precOuterB, precState3]
  · rw [blockState_of_not_mem _ _ (fun j => by simp)]
    simp [precOuterB, precState3, embedPairA_injective.eq_iff]
  · rw [blockState_apply embedPairB_injective, precOuterB_comp_embedPairB]
    simp only [precState3]
    fin_cases i <;> simp [embedPairB_injective.eq_iff]
  · rw [blockState_of_not_mem _ _ (fun j => by simp)]; simp [precOuterB, precState3]
  · rw [blockState_of_not_mem _ _ (fun j => by simp)]; simp [precOuterB, precState3]
  · rw [blockState_of_not_mem _ _ (fun j => by simp)]; simp [precOuterB, precState3]

/-- `B2`, the three stages spliced. -/
theorem run_precOuter (a idx rem acc : ℕ) :
    ∃ N, (∀ m < N, (run (precOuter (k := k) (k' := k'))
          ⟨0, precState2 a idx rem acc⟩ m).pc < (precOuter (k := k) (k' := k')).length) ∧
      run (precOuter (k := k) (k' := k')) ⟨0, precState2 a idx rem acc⟩ N =
        ⟨(precOuter (k := k) (k' := k')).length, precState3 a idx rem acc⟩ := by
  rw [precOuter]
  obtain ⟨N1, i1, e1⟩ := run_precOuter_copyA (k := k) (k' := k') a idx rem acc
  obtain ⟨N2, i2, e2⟩ := run_precOuter_copyInner (k := k) (k' := k') a idx rem acc
  obtain ⟨N3, i3, e3⟩ := run_precOuter_pair (k := k) (k' := k') a idx rem acc
  obtain ⟨j23, f23⟩ := join_exit i2 e2 i3 e3
  exact ⟨N1 + (N2 + N3), join_exit i1 e1 j23 f23⟩

/-! ### `B3`, the call, and `B5`

These are simpler: `B3` and `B5` end in ordinary total macros rather than a block call, so they
need no interior states, and the call transition is a `callState` equality. -/

/-- `B3`: the argument reaches the step callee and both pairing blocks come back clean. -/
theorem run_precSeedStep (a idx rem acc : ℕ) :
    ∃ N, (∀ m < N, (run (precSeedStep (k := k) (k' := k'))
          ⟨0, precState3 a idx rem acc⟩ m).pc <
        (precSeedStep (k := k) (k' := k')).length) ∧
      run (precSeedStep (k := k) (k' := k')) ⟨0, precState3 a idx rem acc⟩ N =
        ⟨(precSeedStep (k := k) (k' := k')).length, precState4 a idx rem acc⟩ := by
  rw [precSeedStep]
  obtain ⟨N, hin, hex⟩ :=
    ((realises_copy (r := embedPairB k k' 2) (s := embedStep k k' 0) (t := rTmp k k')
        (by simp) (by simp) (by simp)).seq
      ((realises_clear (embedPairA k k' 0)).seq
        ((realises_clear (embedPairA k k' 1)).seq
          ((realises_clear (embedPairA k k' 2)).seq
            ((realises_clear (embedPairB k k' 0)).seq
              ((realises_clear (embedPairB k k' 1)).seq
                (realises_clear (embedPairB k k' 2))))))))
      (precState3 (k := k) (k' := k') a idx rem acc)
  refine ⟨N, hin, ?_⟩
  rw [hex]
  clear hex hin
  refine congrArg _ (funext fun r => ?_)
  have sset : ∀ i : Fin (k' + 1), i ≠ 0 → precState4 (k := k) (k' := k') a idx rem acc
      (embedStep k k' i) = 0 := by
    intro i hi
    simp [precState4, embedStep_injective.eq_iff, hi]
  rcases precLayout_cases r with rfl | rfl | rfl | rfl | rfl | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ |
    ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · simp [precState3, precState4]
  · simp [precState3, precState4]
  · simp [precState3, precState4]
  · simp [precState3, precState4]
  · simp [precState3, precState4]
  · simp [precState3, precState4]
  · fin_cases i <;>
      simp [precState3, precState4, embedPairA_injective.eq_iff]
  · fin_cases i <;>
      simp [precState3, precState4, embedPairB_injective.eq_iff]
  · simp [precState3, precState4]
  · simp [precState3, precState4]
  · by_cases hi : i = 0
    · subst hi; simp [precState3, precState4, embedPairB_injective.eq_iff]
    · simp [precState3, precState4, embedStep_injective.eq_iff, hi]

/-- The call's exit, as one register file. -/
theorem callState_precState4 (a idx rem acc acc' : ℕ) :
    callState (embedStep k k') (precState4 (k := k) (k' := k') a idx rem acc) acc' =
      precState5 a idx rem acc acc' := by
  classical
  funext r
  by_cases hrng : ∃ j, r = embedStep k k' j
  · obtain ⟨j, rfl⟩ := hrng
    rw [callState_apply embedStep_injective]
    by_cases hj : j = 0
    · subst hj; simp [precState5]
    · rw [unaryConfig_of_ne hj]
      simp [precState5, embedStep_injective.eq_iff, hj]
  · push Not at hrng
    rw [callState_of_not_mem _ _ hrng]
    simp [precState4, precState5, hrng 0]

/-- `B5`: the callee's answer becomes the accumulator, and the loop head is restored. -/
theorem run_precSaveAcc (a idx rem acc acc' : ℕ) :
    ∃ N, (∀ m < N, (run (precSaveAcc (k := k) (k' := k'))
          ⟨0, precState5 a idx rem acc acc'⟩ m).pc <
        (precSaveAcc (k := k) (k' := k')).length) ∧
      run (precSaveAcc (k := k) (k' := k')) ⟨0, precState5 a idx rem acc acc'⟩ N =
        ⟨(precSaveAcc (k := k) (k' := k')).length, precLoopState a idx rem acc'⟩ := by
  rw [precSaveAcc]
  obtain ⟨N, hin, hex⟩ :=
    ((realises_clear (rAcc k k')).seq
      (realises_move (r := embedStep k k' 0) (s := rAcc k k') (by simp)))
      (precState5 (k := k) (k' := k') a idx rem acc acc')
  refine ⟨N, hin, ?_⟩
  rw [hex]
  clear hex hin
  refine congrArg _ (funext fun r => ?_)
  rcases precLayout_cases r with rfl | rfl | rfl | rfl | rfl | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ |
    ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · simp [precState5, precLoopState]
  · simp [precState5, precLoopState]
  · simp [precState5, precLoopState]
  · simp [precState5, precLoopState]
  · simp [precState5, precLoopState]
  · simp [precState5, precLoopState]
  · simp [precState5, precLoopState]
  · simp [precState5, precLoopState]
  · simp [precState5, precLoopState]
  · simp [precState5, precLoopState]
  · by_cases hi : i = 0
    · subst hi; simp [precLoopState]
    · simp [precState5, precLoopState, embedStep_injective.eq_iff, hi]

/-! ## The turn

`run_precBody` packages the five transitions once, so the loop contracts below never mention a
body unit. -/

theorem run_precBody {g : ℕ →. ℕ} (hg : CleanPartComputesUnary Q g)
    (a idx rem acc acc' : ℕ) (hacc' : acc' ∈ g (Nat.pair a (Nat.pair idx acc))) :
    ∃ N, (∀ m < N, (run (precBody (k := k) (k' := k') Q)
          ⟨0, precLoopState a idx rem acc⟩ m).pc < (precBody (k := k) (k' := k') Q).length) ∧
      run (precBody (k := k) (k' := k') Q) ⟨0, precLoopState a idx rem acc⟩ N =
        ⟨(precBody (k := k) (k' := k') Q).length, precLoopState a idx rem acc'⟩ := by
  rw [precBody]
  obtain ⟨N1, i1, e1⟩ := run_precInner (k := k) (k' := k') a idx rem acc
  obtain ⟨N2, i2, e2⟩ := run_precOuter (k := k) (k' := k') a idx rem acc
  obtain ⟨N3, i3, e3⟩ := run_precSeedStep (k := k) (k' := k') a idx rem acc
  obtain ⟨N4, i4, e4⟩ :=
    hg.call_exit embedStep_injective (regs := precState4 (k := k) (k' := k') a idx rem acc)
      (by simp [precState4])
      (fun j hj => by simp [precState4, embedStep_injective.eq_iff, hj]) hacc'
  rw [callState_precState4] at e4
  obtain ⟨N5, i5, e5⟩ := run_precSaveAcc (k := k) (k' := k') a idx rem acc acc'
  obtain ⟨j45, f45⟩ := join_exit i4 e4 i5 e5
  obtain ⟨j345, f345⟩ := join_exit i3 e3 j45 f45
  obtain ⟨j2345, f2345⟩ := join_exit i2 e2 j345 f345
  exact ⟨N1 + (N2 + (N3 + (N4 + N5))), join_exit i1 e1 j2345 f2345⟩

private theorem getElem?_precTest :
    (precLoop (k := k) (k' := k') Q)[0]? =
      some (Instr.dec (rR k k') 1 ((precBody (k := k) (k' := k') Q).length + 2)) := rfl

private theorem getElem?_precInc :
    (precLoop (k := k) (k' := k') Q)[(precBody (k := k) (k' := k') Q).length + 1]? =
      some (Instr.inc (rK k k') 0) := by
  rw [precLoop, List.getElem?_append_right (by simp)]
  simp only [List.length_append, List.length_cons, List.length_nil, length_shiftJumps]
  rw [show (precBody (k := k) (k' := k') Q).length + 1 -
    (0 + 1 + (precBody (k := k) (k' := k') Q).length) = 0 by omega]
  rfl

/-- **Zero exit.** With nothing left to do the branch leaves the loop at once. -/
theorem run_precTurn_zero (a idx acc : ℕ) :
    ∃ N, (∀ m < N, (run (precLoop (k := k) (k' := k') Q)
          ⟨0, precLoopState a idx 0 acc⟩ m).pc < (precLoop (k := k) (k' := k') Q).length) ∧
      run (precLoop (k := k) (k' := k') Q) ⟨0, precLoopState a idx 0 acc⟩ N =
        ⟨(precLoop (k := k) (k' := k') Q).length, precLoopState a idx 0 acc⟩ := by
  refine ⟨1, fun m hm => ?_, ?_⟩
  · rw [show m = 0 by omega, run_zero, length_precLoop]
    exact show 0 < (precBody (k := k) (k' := k') Q).length + 2 by omega
  · rw [run_one, step_dec_zero (getElem?_precTest Q) (by simp [precLoopState]), length_precLoop]

/-- **Positive turn.** Decrement, run the body, count the index, jump back. -/
theorem run_precTurn_succ {g : ℕ →. ℕ} (hg : CleanPartComputesUnary Q g)
    (a idx rem acc acc' : ℕ) (hacc' : acc' ∈ g (Nat.pair a (Nat.pair idx acc))) :
    ∃ N, (∀ m < N, (run (precLoop (k := k) (k' := k') Q)
          ⟨0, precLoopState a idx (rem + 1) acc⟩ m).pc <
        (precLoop (k := k) (k' := k') Q).length) ∧
      run (precLoop (k := k) (k' := k') Q) ⟨0, precLoopState a idx (rem + 1) acc⟩ N =
        ⟨0, precLoopState a (idx + 1) rem acc'⟩ := by
  obtain ⟨N, hin, hex⟩ := run_precBody (k := k) (k' := k') Q hg a idx rem acc acc' hacc'
  have hstep : step (precLoop (k := k) (k' := k') Q) ⟨0, precLoopState a idx (rem + 1) acc⟩ =
      ⟨1, precLoopState a idx rem acc⟩ := by
    rw [step_dec_pos (getElem?_precTest Q) (by simp [precLoopState])]
    refine congrArg _ (funext fun r => ?_)
    rcases precLayout_cases r with rfl | rfl | rfl | rfl | rfl | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ |
      ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ <;>
      simp [precLoopState]
  have hmid : ∀ m ≤ N, run (precLoop (k := k) (k' := k') Q) ⟨1, precLoopState a idx rem acc⟩ m =
      ⟨(run (precBody (k := k) (k' := k') Q) ⟨0, precLoopState a idx rem acc⟩ m).pc + 1,
        (run (precBody (k := k) (k' := k') Q) ⟨0, precLoopState a idx rem acc⟩ m).regs⟩ :=
    fun m hm => run_middle (A := [Instr.dec (rR k k') 1
      ((precBody (k := k) (k' := k') Q).length + 2)])
      (C := [Instr.inc (rK k k') 0]) hin m hm
  have hbody : run (precLoop (k := k) (k' := k') Q) ⟨1, precLoopState a idx rem acc⟩ N =
      ⟨(precBody (k := k) (k' := k') Q).length + 1, precLoopState a idx rem acc'⟩ := by
    rw [hmid N (Nat.le_refl _), hex]
  refine ⟨N + 2, fun m hm => ?_, ?_⟩
  · rcases (show m = 0 ∨ (1 ≤ m ∧ m ≤ N) ∨ m = N + 1 by omega) with rfl | ⟨hm1, hm2⟩ | rfl
    · rw [run_zero, length_precLoop]
      exact show 0 < (precBody (k := k) (k' := k') Q).length + 2 by omega
    · rw [show m = 1 + (m - 1) by omega, run_add, run_one, hstep, hmid (m - 1) (by omega),
        length_precLoop]
      have := hin (m - 1) (by omega)
      exact show (run (precBody (k := k) (k' := k') Q)
        ⟨0, precLoopState a idx rem acc⟩ (m - 1)).pc + 1 <
        (precBody (k := k) (k' := k') Q).length + 2 by omega
    · rw [show N + 1 = 1 + N by omega, run_add, run_one, hstep, hbody, length_precLoop]
      exact show (precBody (k := k) (k' := k') Q).length + 1 <
        (precBody (k := k) (k' := k') Q).length + 2 by omega
  · rw [show N + 2 = 1 + N + 1 by omega, run_add, run_add, run_one, run_one, hstep, hbody,
      step_inc (getElem?_precInc Q)]
    refine congrArg _ (funext fun r => ?_)
    rcases precLayout_cases r with rfl | rfl | rfl | rfl | rfl | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ |
      ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ <;>
      simp [precLoopState]

/-! ## Halting inversion

The direction that makes the operational semantics exact. Stated as an equivalence: the reverse
is cheap from the positive turn, and having it gives the later induction the theorem in its
natural form. -/

/-- A halting run through a relocated middle segment forces that segment to halt. Kept local
until a second controller wants it. -/
private theorem halts_middle {A B C : Program (k + k' + 32)} {regs : Fin (k + k' + 32) → ℕ}
    (h : Halts (A ++ shiftJumps A.length B ++ C) ⟨0 + A.length, regs⟩) : Halts B ⟨0, regs⟩ := by
  by_contra hn
  simp only [Halts, not_exists] at hn
  have hlt : ∀ m, (run B ⟨0, regs⟩ m).pc < B.length := fun m => Nat.lt_of_not_le (hn m)
  obtain ⟨M, hM⟩ := h
  rw [run_middle (n := M) (fun j _ => hlt j) M (Nat.le_refl _)] at hM
  have hle : (A ++ shiftJumps A.length B ++ C).length ≤ (run B ⟨0, regs⟩ M).pc + A.length := hM
  simp only [List.length_append, length_shiftJumps] at hle
  have := hlt M
  omega

/-- **Halting inversion.** A turn halts exactly when the step call converges and the next loop
head halts. -/
theorem precTurn_halts_iff {g : ℕ →. ℕ} (hg : CleanPartComputesUnary Q g)
    (a idx rem acc : ℕ) :
    Halts (precLoop (k := k) (k' := k') Q) ⟨0, precLoopState a idx (rem + 1) acc⟩ ↔
      ∃ acc' ∈ g (Nat.pair a (Nat.pair idx acc)),
        Halts (precLoop (k := k) (k' := k') Q)
          ⟨0, precLoopState a (idx + 1) rem acc'⟩ := by
  constructor
  · intro hh
    -- the branch fires, so the run continues into the body
    have hstep : step (precLoop (k := k) (k' := k') Q)
        ⟨0, precLoopState a idx (rem + 1) acc⟩ = ⟨1, precLoopState a idx rem acc⟩ := by
      rw [step_dec_pos (getElem?_precTest Q) (by simp [precLoopState])]
      refine congrArg _ (funext fun r => ?_)
      rcases precLayout_cases r with rfl | rfl | rfl | rfl | rfl | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ |
        ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ <;>
        simp [precLoopState]
    have hnh : ¬ Halted (precLoop (k := k) (k' := k') Q)
        ⟨0, precLoopState a idx (rem + 1) acc⟩ := by
      intro hc
      have hle : (precLoop (k := k) (k' := k') Q).length ≤ 0 := hc
      rw [length_precLoop] at hle
      omega
    have h1 : Halts (precLoop (k := k) (k' := k') Q) ⟨1, precLoopState a idx rem acc⟩ := by
      rw [← hstep]
      exact (halts_iff_step.mp hh).resolve_left hnh
    -- and the body itself must halt
    have hbody : Halts (precBody (k := k) (k' := k') Q) ⟨0, precLoopState a idx rem acc⟩ :=
      halts_middle (A := [Instr.dec (rR k k') 1 ((precBody (k := k) (k' := k') Q).length + 2)])
        (C := [Instr.inc (rK k k') 0]) h1
    -- peel the three total prefixes, then read off the call
    rw [precBody] at hbody
    obtain ⟨N1, i1, e1⟩ := run_precInner (k := k) (k' := k') a idx rem acc
    have hb1 := (halts_append_of_exits i1 (by rw [e1])).mp hbody
    rw [show (run (precInner (k := k) (k' := k')) ⟨0, precLoopState a idx rem acc⟩ N1).regs =
      precState2 a idx rem acc from by rw [e1]] at hb1
    obtain ⟨N2, i2, e2⟩ := run_precOuter (k := k) (k' := k') a idx rem acc
    have hb2 := (halts_append_of_exits i2 (by rw [e2])).mp hb1
    rw [show (run (precOuter (k := k) (k' := k')) ⟨0, precState2 a idx rem acc⟩ N2).regs =
      precState3 a idx rem acc from by rw [e2]] at hb2
    obtain ⟨N3, i3, e3⟩ := run_precSeedStep (k := k) (k' := k') a idx rem acc
    have hb3 := (halts_append_of_exits i3 (by rw [e3])).mp hb2
    rw [show (run (precSeedStep (k := k) (k' := k')) ⟨0, precState3 a idx rem acc⟩ N3).regs =
      precState4 a idx rem acc from by rw [e3]] at hb3
    have hdom := (hg.call_halts_iff embedStep_injective
      (regs := precState4 (k := k) (k' := k') a idx rem acc)
      (x := Nat.pair a (Nat.pair idx acc)) (by simp [precState4])
      (fun j hj => by simp [precState4, embedStep_injective.eq_iff, hj])).mp
      (halts_prefix_of_halts_append hb3)
    refine ⟨_, Part.get_mem hdom, ?_⟩
    -- replay the exact turn and transfer what is left of the halting run
    obtain ⟨N, hin, hex⟩ := run_precTurn_succ (k := k) (k' := k') Q hg a idx rem acc _
      (Part.get_mem hdom)
    obtain ⟨M, hM⟩ := hh
    have hMN : N ≤ M := by
      by_contra hlt
      exact absurd hM (Nat.not_le.mpr (hin M (Nat.not_le.mp hlt)))
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hMN
    rw [run_add, hex] at hM
    exact ⟨d, hM⟩
  · rintro ⟨acc', hacc', hnext⟩
    obtain ⟨N, hin, hex⟩ := run_precTurn_succ (k := k) (k' := k') Q hg a idx rem acc acc' hacc'
    obtain ⟨M, hM⟩ := hnext
    exact ⟨N + M, by rw [run_add, hex]; exact hM⟩

/-! ## The loop, semantically

From here nothing mentions an instruction or a program counter except through the in-range and
exit data the turn contracts already package. -/

/-- **Segment completeness.** The trailing `tail` is what makes the induction line up: the
inductive step runs the hypothesis at `tail + 1` and then appends one turn. -/
theorem run_precTurns {f g : ℕ →. ℕ} (hg : CleanPartComputesUnary Q g) (a : ℕ) :
    ∀ q idx acc tail out, acc ∈ precSem f g a idx → out ∈ precSem f g a (idx + q) →
      ∃ N, (∀ m < N, (run (precLoop (k := k) (k' := k') Q)
            ⟨0, precLoopState a idx (q + tail) acc⟩ m).pc <
          (precLoop (k := k) (k' := k') Q).length) ∧
        run (precLoop (k := k) (k' := k') Q) ⟨0, precLoopState a idx (q + tail) acc⟩ N =
          ⟨0, precLoopState a (idx + q) tail out⟩ := by
  intro q
  induction q with
  | zero =>
    intro idx acc tail out hacc hout
    rw [Nat.add_zero] at hout
    obtain rfl : out = acc := Part.mem_unique hout hacc
    refine ⟨0, fun m hm => absurd hm (Nat.not_lt_zero m), ?_⟩
    rw [run_zero, show (0 : ℕ) + tail = tail from Nat.zero_add tail,
      show idx + 0 = idx from Nat.add_zero idx]
  | succ q ih =>
    intro idx acc tail out hacc hout
    rw [show idx + (q + 1) = idx + q + 1 by omega] at hout
    obtain ⟨mid, hmid, hstep⟩ := mem_precSem_succ.mp hout
    obtain ⟨N1, i1, e1⟩ := ih idx acc (tail + 1) mid hacc hmid
    obtain ⟨N2, i2, e2⟩ :=
      run_precTurn_succ (k := k) (k' := k') Q hg a (idx + q) tail mid out hstep
    rw [show q + 1 + tail = q + (tail + 1) by omega]
    rw [show idx + (q + 1) = idx + q + 1 by omega]
    exact ⟨N1 + N2, run_segment_trans i1 e1 i2 e2⟩

/-- **The loop's exact exit**, from the initial head to the program's end. -/
theorem run_precLoop {f g : ℕ →. ℕ} (hg : CleanPartComputesUnary Q g) (a acc out rem : ℕ)
    (hacc : acc ∈ precSem f g a 0) (hout : out ∈ precSem f g a rem) :
    ∃ N, (∀ m < N, (run (precLoop (k := k) (k' := k') Q)
          ⟨0, precLoopState a 0 rem acc⟩ m).pc < (precLoop (k := k) (k' := k') Q).length) ∧
      run (precLoop (k := k) (k' := k') Q) ⟨0, precLoopState a 0 rem acc⟩ N =
        ⟨(precLoop (k := k) (k' := k') Q).length, precLoopState a rem 0 out⟩ := by
  obtain ⟨N1, i1, e1⟩ :=
    run_precTurns (k := k) (k' := k') Q hg a rem 0 acc 0 out hacc (by simpa using hout)
  rw [show rem + 0 = rem from Nat.add_zero rem] at e1 i1
  rw [show 0 + rem = rem from Nat.zero_add rem] at e1
  obtain ⟨N2, i2, e2⟩ := run_precTurn_zero (k := k) (k' := k') Q a rem out
  exact ⟨N1 + N2, run_segment_trans i1 e1 i2 e2⟩

/-- **Soundness.** A halting loop delivers a value of the recurrence at the final stage. -/
theorem precLoop_halts_mem {f g : ℕ →. ℕ} (hg : CleanPartComputesUnary Q g) (a : ℕ) :
    ∀ rem idx acc, acc ∈ precSem f g a idx →
      Halts (precLoop (k := k) (k' := k') Q) ⟨0, precLoopState a idx rem acc⟩ →
      ∃ out, out ∈ precSem f g a (idx + rem) := by
  intro rem
  induction rem with
  | zero => intro idx acc hacc _; exact ⟨acc, by simpa using hacc⟩
  | succ rem ih =>
    intro idx acc hacc hh
    obtain ⟨acc', hacc', hnext⟩ := (precTurn_halts_iff (k := k) (k' := k') Q hg a idx rem acc).mp hh
    obtain ⟨out, hout⟩ := ih (idx + 1) acc' (mem_precSem_step hacc hacc') hnext
    exact ⟨out, by rw [show idx + (rem + 1) = idx + 1 + rem by omega]; exact hout⟩

/-- **Halting is convergence at the final stage.** -/
theorem precLoop_halts_iff {f g : ℕ →. ℕ} (hg : CleanPartComputesUnary Q g) (a acc rem : ℕ)
    (hacc : acc ∈ precSem f g a 0) :
    Halts (precLoop (k := k) (k' := k') Q) ⟨0, precLoopState a 0 rem acc⟩ ↔
      (precSem f g a rem).Dom := by
  constructor
  · intro hh
    obtain ⟨out, hout⟩ := precLoop_halts_mem (k := k) (k' := k') Q hg a rem 0 acc hacc hh
    rw [Nat.zero_add] at hout
    exact Part.dom_iff_mem.mpr ⟨out, hout⟩
  · intro hd
    obtain ⟨N, _, hex⟩ :=
      run_precLoop (k := k) (k' := k') Q hg a acc ((precSem f g a rem).get hd) rem hacc
        (Part.get_mem hd)
    exact ⟨N, by rw [hex]; exact Nat.le_refl _⟩

/-! ## The outer controller

Six blocks. The two partiality boundaries are the base call and the loop; no individual step call
appears here, because `precLoop_halts_iff` already packages them all. -/

/-- Put the input where `unpairLoop` will read it, then split it. -/
def precSplit : Program (k + k' + 32) :=
  seq (copy 0 (embedUnpair k k' 0) (rTmp k k'))
    (renameRegs (embedUnpair k k') unpairLoop)

/-- Move the two components into their registers and seed the base callee. -/
def precSeedBase : Program (k + k' + 32) :=
  seq (move (embedUnpair k k' 1) (rA k k'))
    (seq (move (embedUnpair k k' 2) (rR k k'))
      (copy (rA k k') (embedBase k k' 0) (rTmp k k')))

/-- Take the base answer as the initial accumulator and clear the input register. -/
def precSaveBase : Program (k + k' + 32) :=
  seq (move (embedBase k k' 0) (rAcc k k')) (clear 0)

/-- Discard the loop's bookkeeping and return the accumulator. -/
def precFinish : Program (k + k' + 32) :=
  seq (clear (rA k k'))
    (seq (clear (rK k k')) (seq (clear (rR k k')) (move (rAcc k k') 0)))

/-- The whole controller. -/
def precController : Program (k + k' + 32) :=
  seq (precSplit (k := k) (k' := k'))
    (seq (precSeedBase (k := k) (k' := k'))
      (seq (renameRegs (embedBase k k') P)
        (seq (precSaveBase (k := k) (k' := k'))
          (seq (precLoop (k := k) (k' := k') Q) (precFinish (k := k) (k' := k'))))))

/-! ### The controller's interface states -/

/-- After the input has been copied to the unpairing block. -/
def precCtlA (x : ℕ) : Fin (k + k' + 32) → ℕ :=
  fun r => if r = embedUnpair k k' 0 then x else if r = 0 then x else 0

/-- After unpairing: the two components still inside the block. -/
def precCtlB (x : ℕ) : Fin (k + k' + 32) → ℕ :=
  fun r => if r = embedUnpair k k' 1 then x.unpair.1
    else if r = embedUnpair k k' 2 then x.unpair.2
    else if r = 0 then x else 0

/-- After the components are moved out and the base callee is seeded. -/
def precCtlC (x : ℕ) : Fin (k + k' + 32) → ℕ :=
  fun r => if r = embedBase k k' 0 then x.unpair.1
    else if r = rA k k' then x.unpair.1 else if r = rR k k' then x.unpair.2
    else if r = 0 then x else 0

/-- After the base call. -/
def precCtlD (x acc : ℕ) : Fin (k + k' + 32) → ℕ :=
  fun r => if r = embedBase k k' 0 then acc
    else if r = rA k k' then x.unpair.1 else if r = rR k k' then x.unpair.2
    else if r = 0 then x else 0

/-! ### The controller's transitions -/

theorem run_precSplit (x : ℕ) :
    ∃ N, (∀ m < N, (run (precSplit (k := k) (k' := k'))
          ⟨0, unaryConfig (k + k' + 31) x⟩ m).pc < (precSplit (k := k) (k' := k')).length) ∧
      run (precSplit (k := k) (k' := k')) ⟨0, unaryConfig (k + k' + 31) x⟩ N =
        ⟨(precSplit (k := k) (k' := k')).length, precCtlB x⟩ := by
  rw [precSplit]
  obtain ⟨N1, i1, e1⟩ :=
    realises_copy (r := (0 : Fin (k + k' + 32))) (s := embedUnpair k k' 0) (t := rTmp k k')
      (by simp) (by simp) (by simp) (unaryConfig (k + k' + 31) x)
  have e1' : run (copy 0 (embedUnpair k k' 0) (rTmp k k'))
      ⟨0, unaryConfig (k + k' + 31) x⟩ N1 =
      ⟨(copy 0 (embedUnpair k k' 0) (rTmp k k')).length, precCtlA x⟩ := by
    rw [e1]
    refine congrArg _ (funext fun r => ?_)
    rcases precLayout_cases r with rfl | rfl | rfl | rfl | rfl | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ |
      ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ <;>
      simp [unaryConfig, precCtlA, embedUnpair_injective.eq_iff]
  obtain ⟨N2, hu2, hu3⟩ := run_unpairLoop x
  obtain ⟨i2, e2⟩ :=
    run_renameRegs_of_exit embedUnpair_injective hu2 hu3
      (regs := precCtlA (k := k) (k' := k') x)
      (fun i => by
        rcases (show i = 0 ∨ i ≠ 0 by tauto) with rfl | hi
        · simp [precCtlA, unaryConfig]
        · simp [precCtlA, unaryConfig, embedUnpair_injective.eq_iff, hi])
  have e2' : run (renameRegs (embedUnpair k k') unpairLoop) ⟨0, precCtlA x⟩ N2 =
      ⟨(renameRegs (embedUnpair k k') unpairLoop).length, precCtlB x⟩ := by
    rw [e2]
    refine congrArg _ (funext fun r => ?_)
    rcases precLayout_cases r with rfl | rfl | rfl | rfl | rfl | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ |
      ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
    · rw [Function.extend_apply' _ _ _ (by rintro ⟨i, hi⟩; exact (embedUnpair_ne_fixed i).1 hi)]
      simp [precCtlA, precCtlB]
    · rw [Function.extend_apply' _ _ _ (by rintro ⟨i, hi⟩; exact (embedUnpair_ne_fixed i).2.1 hi)]
      simp [precCtlA, precCtlB]
    · rw [Function.extend_apply' _ _ _
        (by rintro ⟨i, hi⟩; exact (embedUnpair_ne_fixed i).2.2.1 hi)]
      simp [precCtlA, precCtlB]
    · rw [Function.extend_apply' _ _ _
        (by rintro ⟨i, hi⟩; exact (embedUnpair_ne_fixed i).2.2.2.1 hi)]
      simp [precCtlA, precCtlB]
    · rw [Function.extend_apply' _ _ _
        (by rintro ⟨i, hi⟩; exact (embedUnpair_ne_fixed i).2.2.2.2.1 hi)]
      simp [precCtlA, precCtlB]
    · rw [Function.extend_apply' _ _ _
        (by rintro ⟨i, hi⟩; exact (embedUnpair_ne_fixed i).2.2.2.2.2 hi)]
      simp [precCtlA, precCtlB]
    · rw [Function.extend_apply' _ _ _
        (by rintro ⟨j, hj⟩; exact (embedPairA_ne_embedUnpair i j).symm hj)]
      simp [precCtlA, precCtlB]
    · rw [Function.extend_apply' _ _ _
        (by rintro ⟨j, hj⟩; exact (embedPairB_ne_embedUnpair i j).symm hj)]
      simp [precCtlA, precCtlB]
    · rw [embedUnpair_injective.extend_apply]
      simp only [precCtlB]
      fin_cases i <;> simp [embedUnpair_injective.eq_iff]
    · rw [Function.extend_apply' _ _ _
        (by rintro ⟨j, hj⟩; exact (embedUnpair_ne_embedBase j i) hj)]
      simp [precCtlA, precCtlB]
    · rw [Function.extend_apply' _ _ _
        (by rintro ⟨j, hj⟩; exact (embedUnpair_ne_embedStep j i) hj)]
      simp [precCtlA, precCtlB]
  exact ⟨N1 + N2, join_exit i1 e1' i2 e2'⟩

theorem run_precSeedBase (x : ℕ) :
    ∃ N, (∀ m < N, (run (precSeedBase (k := k) (k' := k')) ⟨0, precCtlB x⟩ m).pc <
        (precSeedBase (k := k) (k' := k')).length) ∧
      run (precSeedBase (k := k) (k' := k')) ⟨0, precCtlB x⟩ N =
        ⟨(precSeedBase (k := k) (k' := k')).length, precCtlC x⟩ := by
  rw [precSeedBase]
  obtain ⟨N, hin, hex⟩ :=
    ((realises_move (r := embedUnpair k k' 1) (s := rA k k') (by simp)).seq
      ((realises_move (r := embedUnpair k k' 2) (s := rR k k') (by simp)).seq
        (realises_copy (r := rA k k') (s := embedBase k k' 0) (t := rTmp k k')
          (by simp) (by simp) (by simp)))) (precCtlB (k := k) (k' := k') x)
  refine ⟨N, hin, ?_⟩
  rw [hex]
  clear hex hin
  refine congrArg _ (funext fun r => ?_)
  rcases precLayout_cases r with rfl | rfl | rfl | rfl | rfl | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ |
    ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · simp [precCtlB, precCtlC]
  · simp [precCtlB, precCtlC]
  · simp [precCtlB, precCtlC]
  · simp [precCtlB, precCtlC, embedUnpair_injective.eq_iff]
  · simp [precCtlB, precCtlC]
  · simp [precCtlC]
  · simp [precCtlB, precCtlC]
  · simp [precCtlB, precCtlC]
  · fin_cases i <;> simp [precCtlB, precCtlC, embedUnpair_injective.eq_iff]
  · by_cases hi : i = 0
    · subst hi; simp [precCtlB, precCtlC]
    · simp [precCtlB, precCtlC, embedBase_injective.eq_iff, hi]
  · simp [precCtlB, precCtlC]

theorem callState_precCtlC (x acc : ℕ) :
    callState (embedBase k k') (precCtlC (k := k) (k' := k') x) acc = precCtlD x acc := by
  classical
  funext r
  by_cases hrng : ∃ i, r = embedBase k k' i
  · obtain ⟨i, rfl⟩ := hrng
    rw [callState_apply embedBase_injective]
    by_cases hi : i = 0
    · subst hi; simp [precCtlD]
    · rw [unaryConfig_of_ne hi]
      simp [precCtlD, embedBase_injective.eq_iff, hi]
  · push Not at hrng
    rw [callState_of_not_mem _ _ hrng]
    simp [precCtlC, precCtlD, hrng 0]

theorem run_precSaveBase (x acc : ℕ) :
    ∃ N, (∀ m < N, (run (precSaveBase (k := k) (k' := k')) ⟨0, precCtlD x acc⟩ m).pc <
        (precSaveBase (k := k) (k' := k')).length) ∧
      run (precSaveBase (k := k) (k' := k')) ⟨0, precCtlD x acc⟩ N =
        ⟨(precSaveBase (k := k) (k' := k')).length,
          precLoopState x.unpair.1 0 x.unpair.2 acc⟩ := by
  rw [precSaveBase]
  obtain ⟨N, hin, hex⟩ :=
    ((realises_move (r := embedBase k k' 0) (s := rAcc k k') (by simp)).seq
      (realises_clear (0 : Fin (k + k' + 32)))) (precCtlD (k := k) (k' := k') x acc)
  refine ⟨N, hin, ?_⟩
  rw [hex]
  clear hex hin
  refine congrArg _ (funext fun r => ?_)
  rcases precLayout_cases r with rfl | rfl | rfl | rfl | rfl | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ |
    ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · simp [precCtlD, precLoopState]
  · simp [precCtlD, precLoopState]
  · simp [precCtlD, precLoopState]
  · simp [precCtlD, precLoopState]
  · simp [precCtlD, precLoopState]
  · simp [precCtlD, precLoopState]
  · simp [precCtlD, precLoopState]
  · simp [precCtlD, precLoopState]
  · simp [precCtlD, precLoopState]
  · by_cases hi : i = 0
    · subst hi; simp [precCtlD, precLoopState]
    · simp [precCtlD, precLoopState, embedBase_injective.eq_iff, hi]
  · simp [precCtlD, precLoopState]

theorem run_precFinish (a n out : ℕ) :
    ∃ N, (∀ m < N, (run (precFinish (k := k) (k' := k'))
          ⟨0, precLoopState a n 0 out⟩ m).pc < (precFinish (k := k) (k' := k')).length) ∧
      run (precFinish (k := k) (k' := k')) ⟨0, precLoopState a n 0 out⟩ N =
        ⟨(precFinish (k := k) (k' := k')).length, unaryConfig (k + k' + 31) out⟩ := by
  rw [precFinish]
  obtain ⟨N, hin, hex⟩ :=
    ((realises_clear (rA k k')).seq
      ((realises_clear (rK k k')).seq
        ((realises_clear (rR k k')).seq
          (realises_move (r := rAcc k k') (s := (0 : Fin (k + k' + 32))) (by simp)))))
      (precLoopState (k := k) (k' := k') a n 0 out)
  refine ⟨N, hin, ?_⟩
  rw [hex]
  clear hex hin
  refine congrArg _ (funext fun r => ?_)
  rcases precLayout_cases r with rfl | rfl | rfl | rfl | rfl | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ |
    ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ <;>
    simp [precLoopState, unaryConfig]

/-! ## The closure theorem

Two partiality boundaries only: the base call and the loop. `precLoop_halts_iff` has already
absorbed every step call. -/

theorem CleanPartComputesUnary.prec {f g : ℕ →. ℕ} (hf : CleanPartComputesUnary P f)
    (hg : CleanPartComputesUnary Q g) :
    CleanPartComputesUnary (precController (k := k) (k' := k') P Q)
      fun x => precSem f g x.unpair.1 x.unpair.2 := by
  intro x
  have hclean : ∀ i, i ≠ 0 → precCtlC (k := k) (k' := k') x (embedBase k k' i) = 0 :=
    fun i hi => by simp [precCtlC, embedBase_injective.eq_iff, hi]
  have hseed : precCtlC (k := k) (k' := k') x (embedBase k k' 0) = x.unpair.1 := by simp [precCtlC]
  refine ⟨fun y hy => ?_, fun hh => ?_⟩
  · obtain ⟨acc, hacc⟩ := mem_precSem_base hy
    obtain ⟨N1, i1, e1⟩ := run_precSplit (k := k) (k' := k') x
    obtain ⟨N2, i2, e2⟩ := run_precSeedBase (k := k) (k' := k') x
    obtain ⟨N3, i3, e3⟩ := hf.call_exit embedBase_injective hseed hclean hacc
    rw [callState_precCtlC] at e3
    obtain ⟨N4, i4, e4⟩ := run_precSaveBase (k := k) (k' := k') x acc
    obtain ⟨N5, i5, e5⟩ :=
      run_precLoop (k := k) (k' := k') Q hg x.unpair.1 acc y x.unpair.2 hacc hy
    obtain ⟨N6, i6, e6⟩ := run_precFinish (k := k) (k' := k') x.unpair.1 x.unpair.2 y
    obtain ⟨j56, f56⟩ := join_exit i5 e5 i6 e6
    obtain ⟨j456, f456⟩ := join_exit i4 e4 j56 f56
    obtain ⟨j3456, f3456⟩ := join_exit i3 e3 j456 f456
    obtain ⟨j23456, f23456⟩ := join_exit i2 e2 j3456 f3456
    exact ⟨N1 + (N2 + (N3 + (N4 + (N5 + N6)))), join_exit i1 e1 j23456 f23456⟩
  · obtain ⟨N1, i1, e1⟩ := run_precSplit (k := k) (k' := k') x
    have h1 := (halts_append_of_exits i1 (by rw [e1])).mp hh
    rw [show (run (precSplit (k := k) (k' := k'))
      ⟨0, unaryConfig (k + k' + 31) x⟩ N1).regs = precCtlB x from by rw [e1]] at h1
    obtain ⟨N2, i2, e2⟩ := run_precSeedBase (k := k) (k' := k') x
    have h2 := (halts_append_of_exits i2 (by rw [e2])).mp h1
    rw [show (run (precSeedBase (k := k) (k' := k'))
      ⟨0, precCtlB x⟩ N2).regs = precCtlC x from by rw [e2]] at h2
    have hdom := (hf.call_halts_iff embedBase_injective hseed hclean).mp
      (halts_prefix_of_halts_append h2)
    obtain ⟨N3, i3, e3⟩ := hf.call_exit embedBase_injective hseed hclean (Part.get_mem hdom)
    rw [callState_precCtlC] at e3
    have h3 := (halts_append_of_exits i3 (by rw [e3])).mp h2
    rw [show (run (renameRegs (embedBase k k') P) ⟨0, precCtlC x⟩ N3).regs =
      precCtlD x ((f x.unpair.1).get hdom) from by rw [e3]] at h3
    obtain ⟨N4, i4, e4⟩ := run_precSaveBase (k := k) (k' := k') x ((f x.unpair.1).get hdom)
    have h4 := (halts_append_of_exits i4 (by rw [e4])).mp h3
    rw [show (run (precSaveBase (k := k) (k' := k'))
      ⟨0, precCtlD x ((f x.unpair.1).get hdom)⟩ N4).regs =
      precLoopState x.unpair.1 0 x.unpair.2 ((f x.unpair.1).get hdom) from by rw [e4]] at h4
    exact (precLoop_halts_iff (k := k) (k' := k') Q hg x.unpair.1 ((f x.unpair.1).get hdom)
      x.unpair.2 (Part.get_mem hdom)).mp (halts_prefix_of_halts_append h4)

/-- **`Code.prec`.** A `congr` corollary of the closure theorem, through `eval_prec_unpair`. -/
theorem CleanPartComputesUnary.codePrec {cf cg : Code} (hf : CleanPartComputesUnary P cf.eval)
    (hg : CleanPartComputesUnary Q cg.eval) :
    CleanPartComputesUnary (precController (k := k) (k' := k') P Q) (Code.prec cf cg).eval :=
  (CleanPartComputesUnary.prec (k := k) (k' := k') P Q hf hg).congr fun x =>
    (eval_prec_unpair cf cg x).symm

end RegisterMachine

end Hilbert10


/- Source: Hilbert10.Internal.CodeRfind, Hilbert10 v2.3.0, Apache-2.0. -/
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# The source semantics of `Nat.Partrec.Code.rfind'`

Issue #43, before any register is chosen — the same order as #41, #51 and #42.

`rfind'` minimises *from an offset*: on input `Nat.pair a m` it returns the least `y ≥ m` with
`f (Nat.pair a y) = 0`. Mathlib writes that with `Nat.rfind` over a shifted predicate and a
`Part.map`, and `Nat.mem_rfind` is the decisive fact.

## Keeping the offset

`mem_rfindSem` is stated in terms of the number of *unsuccessful turns* `q`, not as an interval
`m ≤ z < y`:

```lean
y ∈ rfindSem f a m ↔ ∃ q, y = q + m ∧ 0 ∈ f (Nat.pair a (q + m)) ∧
  ∀ j < q, ∃ z ∈ f (Nat.pair a (j + m)), z ≠ 0
```

That is what the machine does: after `q` unsuccessful turns its candidate is `q + m`. An interval
form is a corollary if a consumer ever wants one; stating it that way first would put an
arithmetic translation between the machine and its specification, which is exactly the sort of
gap the earlier constructors avoided by naming the recurrence first.
-/

namespace Hilbert10

namespace RegisterMachine

open Nat.Partrec (Code)

/-- Minimisation from an offset, named. -/
def rfindSem (f : ℕ →. ℕ) (a m : ℕ) : Part ℕ :=
  (Nat.rfind fun n => (fun z => z = 0) <$> f (Nat.pair a (n + m))).map (· + m)

/-- The predicate the search minimises, spelled out: `true` means the callee returned zero. -/
private theorem mem_map_decide_true {f : ℕ →. ℕ} {u : ℕ} :
    true ∈ ((fun z => decide (z = 0)) <$> f u) ↔ 0 ∈ f u := by
  rw [Part.map_eq_map, Part.mem_map_iff]
  constructor
  · rintro ⟨z, hz, hz0⟩
    have hz' : z = 0 := by simpa using hz0
    exact hz' ▸ hz
  · intro h
    exact ⟨0, h, by simp⟩

private theorem mem_map_decide_false {f : ℕ →. ℕ} {u : ℕ} :
    false ∈ ((fun z => decide (z = 0)) <$> f u) ↔ ∃ z ∈ f u, z ≠ 0 := by
  rw [Part.map_eq_map, Part.mem_map_iff]
  constructor
  · rintro ⟨z, hz, hz0⟩
    exact ⟨z, hz, by simpa using hz0⟩
  · rintro ⟨z, hz, hz0⟩
    exact ⟨z, hz, by simpa using hz0⟩

/-- **The search characterisation**, counting unsuccessful turns. -/
theorem mem_rfindSem {f : ℕ →. ℕ} {a m y : ℕ} :
    y ∈ rfindSem f a m ↔
      ∃ q, y = q + m ∧ 0 ∈ f (Nat.pair a (q + m)) ∧
        ∀ j < q, ∃ z ∈ f (Nat.pair a (j + m)), z ≠ 0 := by
  rw [rfindSem, Part.mem_map_iff]
  constructor
  · rintro ⟨q, hq, rfl⟩
    have hq' := Nat.mem_rfind.mp hq
    exact ⟨q, rfl, mem_map_decide_true.mp hq'.1,
      fun j hj => mem_map_decide_false.mp (hq'.2 hj)⟩
  · rintro ⟨q, rfl, hq, hmin⟩
    exact ⟨q, Nat.mem_rfind.mpr ⟨mem_map_decide_true.mpr hq,
      fun {j} hj => mem_map_decide_false.mpr (hmin j hj)⟩, rfl⟩

/-- **The bridge.** `Code.rfind'`'s evaluation on a paired input is the named search. -/
theorem eval_rfind_eq (cf : Code) (a m : ℕ) :
    (Code.rfind' cf).eval (Nat.pair a m) = rfindSem cf.eval a m := by
  rw [Code.eval, Nat.unpaired, Nat.unpair_pair]
  rfl

/-- The same for an arbitrary input, which is what the machine receives. -/
theorem eval_rfind_unpair (cf : Code) (x : ℕ) :
    (Code.rfind' cf).eval x = rfindSem cf.eval x.unpair.1 x.unpair.2 := by
  conv_lhs => rw [← Nat.pair_unpair x]
  exact eval_rfind_eq cf _ _

/-! ## The controller's register layout

`Fin (k + 20)`:

| register | role |
|---|---|
| `0` | the input, and at the end the answer |
| `1` | the parameter `a` |
| `2` | the current candidate |
| `3` | the temporary `copy` borrows |
| `4`–`12` | the `pairMachine` block |
| `13`–`18` | the `unpairLoop` block |
| `19 …` | the predicate callee's block |

Simpler than `prec`'s: one callee, one pairing block, no accumulator. -/

variable (k)

/-- The parameter. -/ def sA : Fin (k + 20) := ⟨1, by omega⟩
/-- The current candidate. -/ def sC : Fin (k + 20) := ⟨2, by omega⟩
/-- The temporary. -/ def sT : Fin (k + 20) := ⟨3, by omega⟩

/-- The pairing block. -/
def sPair (i : Fin 9) : Fin (k + 20) := ⟨4 + i.val, by omega⟩

/-- The unpairing block. -/
def sUnpair (i : Fin 6) : Fin (k + 20) := ⟨13 + i.val, by omega⟩

/-- The predicate callee's block. -/
def sCall (i : Fin (k + 1)) : Fin (k + 20) := ⟨19 + i.val, by omega⟩

variable {k}

@[simp] theorem sA_val : (sA k).val = 1 := rfl
@[simp] theorem sC_val : (sC k).val = 2 := rfl
@[simp] theorem sT_val : (sT k).val = 3 := rfl
@[simp] theorem sPair_val (i : Fin 9) : (sPair k i).val = 4 + i.val := rfl
@[simp] theorem sUnpair_val (i : Fin 6) : (sUnpair k i).val = 13 + i.val := rfl
@[simp] theorem sCall_val (i : Fin (k + 1)) : (sCall k i).val = 19 + i.val := rfl

theorem sPair_injective : Function.Injective (sPair k) := fun i j h =>
  Fin.ext (by have := congrArg Fin.val h; simp at this; omega)

theorem sUnpair_injective : Function.Injective (sUnpair k) := fun i j h =>
  Fin.ext (by have := congrArg Fin.val h; simp at this; omega)

theorem sCall_injective : Function.Injective (sCall k) := fun i j h =>
  Fin.ext (by have := congrArg Fin.val h; simp at this; omega)

/-- **The layout is exhaustive**: `4 + 9 + 6 + (k+1) = k + 20`. -/
theorem sLayout_cases (r : Fin (k + 20)) :
    r = 0 ∨ r = sA k ∨ r = sC k ∨ r = sT k ∨ (∃ i, r = sPair k i) ∨
      (∃ i, r = sUnpair k i) ∨ ∃ i, r = sCall k i := by
  have hr := r.isLt
  rcases (show r.val = 0 ∨ r.val = 1 ∨ r.val = 2 ∨ r.val = 3 ∨ (4 ≤ r.val ∧ r.val ≤ 12) ∨
      (13 ≤ r.val ∧ r.val ≤ 18) ∨ 19 ≤ r.val by omega) with h | h | h | h | h | h | h
  · exact Or.inl (Fin.ext (by simpa using h))
  · exact Or.inr (Or.inl (Fin.ext (by simpa using h)))
  · exact Or.inr (Or.inr (Or.inl (Fin.ext (by simpa using h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext (by simpa using h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨⟨r.val - 4, by omega⟩, Fin.ext (by simp; omega)⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨⟨r.val - 13, by omega⟩, Fin.ext (by simp; omega)⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨⟨r.val - 19, by omega⟩, Fin.ext (by simp; omega)⟩)))))

/-! ### Separation -/

theorem sFixed_ne :
    (0 : Fin (k + 20)) ≠ sA k ∧ (0 : Fin (k + 20)) ≠ sC k ∧ (0 : Fin (k + 20)) ≠ sT k ∧
    sA k ≠ sC k ∧ sA k ≠ sT k ∧ sC k ≠ sT k := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (intro h; have := congrArg Fin.val h; simp at this)

theorem sFixed_ne' :
    sA k ≠ (0 : Fin (k + 20)) ∧ sC k ≠ (0 : Fin (k + 20)) ∧ sT k ≠ (0 : Fin (k + 20)) ∧
    sC k ≠ sA k ∧ sT k ≠ sA k ∧ sT k ≠ sC k :=
  ⟨sFixed_ne.1.symm, sFixed_ne.2.1.symm, sFixed_ne.2.2.1.symm, sFixed_ne.2.2.2.1.symm,
    sFixed_ne.2.2.2.2.1.symm, sFixed_ne.2.2.2.2.2.symm⟩

theorem sPair_ne_fixed (i : Fin 9) :
    sPair k i ≠ 0 ∧ sPair k i ≠ sA k ∧ sPair k i ≠ sC k ∧ sPair k i ≠ sT k := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (intro h; have := congrArg Fin.val h; simp at this; all_goals omega)

theorem sUnpair_ne_fixed (i : Fin 6) :
    sUnpair k i ≠ 0 ∧ sUnpair k i ≠ sA k ∧ sUnpair k i ≠ sC k ∧ sUnpair k i ≠ sT k := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (intro h; have := congrArg Fin.val h; simp at this; all_goals omega)

theorem sCall_ne_fixed (i : Fin (k + 1)) :
    sCall k i ≠ 0 ∧ sCall k i ≠ sA k ∧ sCall k i ≠ sC k ∧ sCall k i ≠ sT k := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (intro h; have := congrArg Fin.val h; simp at this; all_goals omega)

theorem sPair_ne_fixed' (i : Fin 9) :
    (0 : Fin (k + 20)) ≠ sPair k i ∧ sA k ≠ sPair k i ∧ sC k ≠ sPair k i ∧ sT k ≠ sPair k i :=
  ⟨(sPair_ne_fixed i).1.symm, (sPair_ne_fixed i).2.1.symm, (sPair_ne_fixed i).2.2.1.symm,
    (sPair_ne_fixed i).2.2.2.symm⟩

theorem sUnpair_ne_fixed' (i : Fin 6) :
    (0 : Fin (k + 20)) ≠ sUnpair k i ∧ sA k ≠ sUnpair k i ∧ sC k ≠ sUnpair k i ∧
      sT k ≠ sUnpair k i :=
  ⟨(sUnpair_ne_fixed i).1.symm, (sUnpair_ne_fixed i).2.1.symm, (sUnpair_ne_fixed i).2.2.1.symm,
    (sUnpair_ne_fixed i).2.2.2.symm⟩

theorem sCall_ne_fixed' (i : Fin (k + 1)) :
    (0 : Fin (k + 20)) ≠ sCall k i ∧ sA k ≠ sCall k i ∧ sC k ≠ sCall k i ∧ sT k ≠ sCall k i :=
  ⟨(sCall_ne_fixed i).1.symm, (sCall_ne_fixed i).2.1.symm, (sCall_ne_fixed i).2.2.1.symm,
    (sCall_ne_fixed i).2.2.2.symm⟩

theorem sPair_ne_sUnpair (i : Fin 9) (j : Fin 6) : sPair k i ≠ sUnpair k j := by
  intro h; have := congrArg Fin.val h; simp at this; omega

theorem sPair_ne_sCall (i : Fin 9) (j : Fin (k + 1)) : sPair k i ≠ sCall k j := by
  intro h; have := congrArg Fin.val h; simp at this; omega

theorem sUnpair_ne_sCall (i : Fin 6) (j : Fin (k + 1)) : sUnpair k i ≠ sCall k j := by
  intro h; have := congrArg Fin.val h; simp at this; omega

theorem sUnpair_ne_sPair (j : Fin 6) (i : Fin 9) : sUnpair k j ≠ sPair k i :=
  (sPair_ne_sUnpair i j).symm

theorem sCall_ne_sPair (j : Fin (k + 1)) (i : Fin 9) : sCall k j ≠ sPair k i :=
  (sPair_ne_sCall i j).symm

theorem sCall_ne_sUnpair (j : Fin (k + 1)) (i : Fin 6) : sCall k j ≠ sUnpair k i :=
  (sUnpair_ne_sCall i j).symm

attribute [local simp] sFixed_ne sFixed_ne' sPair_ne_fixed sPair_ne_fixed'
  sUnpair_ne_fixed sUnpair_ne_fixed' sCall_ne_fixed sCall_ne_fixed'
  sPair_ne_sUnpair sPair_ne_sCall sUnpair_ne_sCall
  sUnpair_ne_sPair sCall_ne_sPair sCall_ne_sUnpair

/-! ## The machine

One callee, one pairing, and a branch on its answer. The loop body is a *prefix* of the loop
rather than a middle segment, so `run_append_of_lt` and `halts_append_of_exits` suffice and
`run_middle` is not needed at all. -/

variable (Cf : Program (k + 1))

/-- Compute `Nat.pair a c` in the pairing block. -/
def rfindPairUp : Program (k + 20) :=
  seq (copy (sA k) (sPair k 0) (sT k))
    (seq (copy (sC k) (sPair k 1) (sT k)) (renameRegs (sPair k) pairMachine))

/-- Hand it to the callee and give the pairing block back clean. -/
def rfindSeedCall : Program (k + 20) :=
  seq (copy (sPair k 2) (sCall k 0) (sT k))
    (seq (clear (sPair k 0)) (seq (clear (sPair k 1)) (clear (sPair k 2))))

/-- One evaluation of the predicate at the current candidate. -/
def rfindBody : Program (k + 20) :=
  seq (rfindPairUp (k := k)) (seq (rfindSeedCall (k := k)) (renameRegs (sCall k) Cf))

/-- The search: evaluate, and on a nonzero answer discard it, step the candidate and repeat.

The `dec` at `rfindBody.length` is the branch — a zero answer leaves the loop, anything else
falls into the drain and then the increment, which also jumps back. -/
def rfindLoop : Program (k + 20) :=
  rfindBody (k := k) Cf ++
    [Instr.dec (sCall k 0) ((rfindBody (k := k) Cf).length + 1)
        ((rfindBody (k := k) Cf).length + 3),
      Instr.dec (sCall k 0) ((rfindBody (k := k) Cf).length + 1)
        ((rfindBody (k := k) Cf).length + 2),
      Instr.inc (sC k) 0]

theorem length_rfindLoop :
    (rfindLoop (k := k) Cf).length = (rfindBody (k := k) Cf).length + 3 := by
  simp [rfindLoop]

/-- Split the input. -/
def rfindSplit : Program (k + 20) :=
  seq (copy 0 (sUnpair k 0) (sT k)) (renameRegs (sUnpair k) unpairLoop)

/-- Move the parameter and the initial candidate into place. -/
def rfindSeed : Program (k + 20) :=
  seq (move (sUnpair k 1) (sA k)) (seq (move (sUnpair k 2) (sC k)) (clear 0))

/-- Return the candidate the search stopped at. -/
def rfindFinish : Program (k + 20) := seq (clear (sA k)) (move (sC k) 0)

/-- The whole controller. -/
def rfindController : Program (k + 20) :=
  seq (rfindSplit (k := k))
    (seq (rfindSeed (k := k)) (seq (rfindLoop (k := k) Cf) (rfindFinish (k := k))))

variable {Cf}

/-! ### The loop head

The only state the search carries: the parameter and the current candidate. There is no counter,
which is what makes soundness an induction on halting time rather than on a register. -/

/-- The register file at a loop head. -/
def searchState (a c : ℕ) : Fin (k + 20) → ℕ :=
  fun r => if r = sA k then a else if r = sC k then c else 0

/-- After the pairing: the candidate's argument built. -/
def searchPaired (a c : ℕ) : Fin (k + 20) → ℕ :=
  fun r => if r = sA k then a else if r = sC k then c
    else if r = sPair k 0 then a else if r = sPair k 1 then c
    else if r = sPair k 2 then Nat.pair a c else 0

/-- After the callee is seeded and the pairing block cleaned. -/
def searchSeeded (a c : ℕ) : Fin (k + 20) → ℕ :=
  fun r => if r = sA k then a else if r = sC k then c
    else if r = sCall k 0 then Nat.pair a c else 0

/-- After the call. -/
def searchAnswered (a c z : ℕ) : Fin (k + 20) → ℕ :=
  fun r => if r = sA k then a else if r = sC k then c
    else if r = sCall k 0 then z else 0

/-! ### The body's transitions -/

/-- After the parameter reaches the pairing block. -/
def searchPairA (a c : ℕ) : Fin (k + 20) → ℕ :=
  fun r => if r = sPair k 0 then a
    else if r = sA k then a else if r = sC k then c else 0

/-- After the candidate reaches it. -/
def searchPairB (a c : ℕ) : Fin (k + 20) → ℕ :=
  fun r => if r = sPair k 1 then c else if r = sPair k 0 then a
    else if r = sA k then a else if r = sC k then c else 0

theorem searchPairB_comp_sPair (a c : ℕ) :
    searchPairB (k := k) a c ∘ sPair k = fun i => if i = 0 then a else if i = 1 then c else 0 := by
  funext i
  fin_cases i <;> simp [searchPairB, sPair_injective.eq_iff]

theorem run_rfindPairUp_copyA (a c : ℕ) :
    ∃ N, (∀ m < N, (run (copy (sA k) (sPair k 0) (sT k)) ⟨0, searchState a c⟩ m).pc <
        (copy (sA k) (sPair k 0) (sT k)).length) ∧
      run (copy (sA k) (sPair k 0) (sT k)) ⟨0, searchState a c⟩ N =
        ⟨(copy (sA k) (sPair k 0) (sT k)).length, searchPairA a c⟩ := by
  obtain ⟨N, hin, hex⟩ :=
    realises_copy (r := sA k) (s := sPair k 0) (t := sT k) (by simp) (by simp) (by simp)
      (searchState (k := k) a c)
  refine ⟨N, hin, ?_⟩
  rw [hex]
  clear hex hin
  refine congrArg _ (funext fun r => ?_)
  rcases sLayout_cases r with rfl | rfl | rfl | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ <;>
    simp [searchState, searchPairA, sPair_injective.eq_iff]

theorem run_rfindPairUp_copyC (a c : ℕ) :
    ∃ N, (∀ m < N, (run (copy (sC k) (sPair k 1) (sT k)) ⟨0, searchPairA a c⟩ m).pc <
        (copy (sC k) (sPair k 1) (sT k)).length) ∧
      run (copy (sC k) (sPair k 1) (sT k)) ⟨0, searchPairA a c⟩ N =
        ⟨(copy (sC k) (sPair k 1) (sT k)).length, searchPairB a c⟩ := by
  obtain ⟨N, hin, hex⟩ :=
    realises_copy (r := sC k) (s := sPair k 1) (t := sT k) (by simp) (by simp) (by simp)
      (searchPairA (k := k) a c)
  refine ⟨N, hin, ?_⟩
  rw [hex]
  clear hex hin
  refine congrArg _ (funext fun r => ?_)
  rcases sLayout_cases r with rfl | rfl | rfl | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ <;>
    simp [searchPairA, searchPairB, sPair_injective.eq_iff]

theorem run_rfindPairUp_pair (a c : ℕ) :
    ∃ N, (∀ m < N, (run (renameRegs (sPair k) pairMachine) ⟨0, searchPairB a c⟩ m).pc <
        (renameRegs (sPair k) pairMachine).length) ∧
      run (renameRegs (sPair k) pairMachine) ⟨0, searchPairB a c⟩ N =
        ⟨(renameRegs (sPair k) pairMachine).length, searchPaired a c⟩ := by
  obtain ⟨N, hin, hex⟩ :=
    (realises_pairMachine.renameRegs_blockState sPair_injective) (searchPairB (k := k) a c)
  refine ⟨N, hin, ?_⟩
  rw [hex]
  clear hex hin
  refine congrArg _ (funext fun r => ?_)
  rcases sLayout_cases r with rfl | rfl | rfl | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rw [blockState_of_not_mem _ _ (fun i => by simp)]; simp [searchPairB, searchPaired]
  · rw [blockState_of_not_mem _ _ (fun i => by simp)]; simp [searchPairB, searchPaired]
  · rw [blockState_of_not_mem _ _ (fun i => by simp)]; simp [searchPairB, searchPaired]
  · rw [blockState_of_not_mem _ _ (fun i => by simp)]; simp [searchPairB, searchPaired]
  · rw [blockState_apply sPair_injective, searchPairB_comp_sPair]
    simp only [searchPaired]
    fin_cases i <;> simp [sPair_injective.eq_iff]
  · rw [blockState_of_not_mem _ _ (fun j => by simp)]; simp [searchPairB, searchPaired]
  · rw [blockState_of_not_mem _ _ (fun j => by simp)]; simp [searchPairB, searchPaired]

theorem run_rfindPairUp (a c : ℕ) :
    ∃ N, (∀ m < N, (run (rfindPairUp (k := k)) ⟨0, searchState a c⟩ m).pc <
        (rfindPairUp (k := k)).length) ∧
      run (rfindPairUp (k := k)) ⟨0, searchState a c⟩ N =
        ⟨(rfindPairUp (k := k)).length, searchPaired a c⟩ := by
  rw [rfindPairUp]
  obtain ⟨N1, i1, e1⟩ := run_rfindPairUp_copyA (k := k) a c
  obtain ⟨N2, i2, e2⟩ := run_rfindPairUp_copyC (k := k) a c
  obtain ⟨N3, i3, e3⟩ := run_rfindPairUp_pair (k := k) a c
  obtain ⟨j23, f23⟩ := join_exit i2 e2 i3 e3
  exact ⟨N1 + (N2 + N3), join_exit i1 e1 j23 f23⟩

theorem run_rfindSeedCall (a c : ℕ) :
    ∃ N, (∀ m < N, (run (rfindSeedCall (k := k)) ⟨0, searchPaired a c⟩ m).pc <
        (rfindSeedCall (k := k)).length) ∧
      run (rfindSeedCall (k := k)) ⟨0, searchPaired a c⟩ N =
        ⟨(rfindSeedCall (k := k)).length, searchSeeded a c⟩ := by
  rw [rfindSeedCall]
  obtain ⟨N, hin, hex⟩ :=
    ((realises_copy (r := sPair k 2) (s := sCall k 0) (t := sT k)
        (by simp) (by simp) (by simp)).seq
      ((realises_clear (sPair k 0)).seq
        ((realises_clear (sPair k 1)).seq (realises_clear (sPair k 2)))))
      (searchPaired (k := k) a c)
  refine ⟨N, hin, ?_⟩
  rw [hex]
  clear hex hin
  refine congrArg _ (funext fun r => ?_)
  rcases sLayout_cases r with rfl | rfl | rfl | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · simp [searchPaired, searchSeeded, sPair_injective.eq_iff]
  · simp [searchPaired, searchSeeded, sPair_injective.eq_iff]
  · simp [searchPaired, searchSeeded, sPair_injective.eq_iff]
  · simp [searchPaired, searchSeeded, sPair_injective.eq_iff]
  · fin_cases i <;> simp [searchPaired, searchSeeded, sPair_injective.eq_iff]
  · simp [searchPaired, searchSeeded, sPair_injective.eq_iff]
  · by_cases hi : i = 0
    · subst hi; simp [searchPaired, searchSeeded, sPair_injective.eq_iff]
    · simp [searchPaired, searchSeeded, sCall_injective.eq_iff, hi]

theorem callState_searchSeeded (a c z : ℕ) :
    callState (sCall k) (searchSeeded (k := k) a c) z = searchAnswered a c z := by
  classical
  funext r
  by_cases hrng : ∃ i, r = sCall k i
  · obtain ⟨i, rfl⟩ := hrng
    rw [callState_apply sCall_injective]
    by_cases hi : i = 0
    · subst hi; simp [searchAnswered]
    · rw [unaryConfig_of_ne hi]
      simp [searchAnswered, sCall_injective.eq_iff, hi]
  · push Not at hrng
    rw [callState_of_not_mem _ _ hrng]
    simp [searchSeeded, searchAnswered, hrng 0]

/-- **One evaluation of the predicate.** -/
theorem run_rfindBody {f : ℕ →. ℕ} (hf : CleanPartComputesUnary Cf f) (a c z : ℕ)
    (hz : z ∈ f (Nat.pair a c)) :
    ∃ N, (∀ m < N, (run (rfindBody (k := k) Cf) ⟨0, searchState a c⟩ m).pc <
        (rfindBody (k := k) Cf).length) ∧
      run (rfindBody (k := k) Cf) ⟨0, searchState a c⟩ N =
        ⟨(rfindBody (k := k) Cf).length, searchAnswered a c z⟩ := by
  rw [rfindBody]
  obtain ⟨N1, i1, e1⟩ := run_rfindPairUp (k := k) a c
  obtain ⟨N2, i2, e2⟩ := run_rfindSeedCall (k := k) a c
  obtain ⟨N3, i3, e3⟩ :=
    hf.call_exit sCall_injective (regs := searchSeeded (k := k) a c)
      (x := Nat.pair a c) (by simp [searchSeeded])
      (fun i hi => by simp [searchSeeded, sCall_injective.eq_iff, hi]) hz
  rw [callState_searchSeeded] at e3
  obtain ⟨j23, f23⟩ := join_exit i2 e2 i3 e3
  exact ⟨N1 + (N2 + N3), join_exit i1 e1 j23 f23⟩

/-! ### The two turns

`rfindBody` is a *prefix* of `rfindLoop`, so peeling it needs only `run_append_of_lt` and
`halts_prefix_of_halts_append`; the absolute jump back in the suffix does not interfere with
either. -/

private theorem getElem?_sBranch :
    (rfindLoop (k := k) Cf)[(rfindBody (k := k) Cf).length]? =
      some (Instr.dec (sCall k 0) ((rfindBody (k := k) Cf).length + 1)
        ((rfindBody (k := k) Cf).length + 3)) := by
  rw [rfindLoop, List.getElem?_append_right (Nat.le_refl _)]
  simp

private theorem getElem?_sDrain :
    (rfindLoop (k := k) Cf)[(rfindBody (k := k) Cf).length + 1]? =
      some (Instr.dec (sCall k 0) ((rfindBody (k := k) Cf).length + 1)
        ((rfindBody (k := k) Cf).length + 2)) := by
  rw [rfindLoop, List.getElem?_append_right (by omega)]
  simp

private theorem getElem?_sInc :
    (rfindLoop (k := k) Cf)[(rfindBody (k := k) Cf).length + 2]? =
      some (Instr.inc (sC k) 0) := by
  rw [rfindLoop, List.getElem?_append_right (by omega)]
  simp

private theorem run_body_in_loop {S : Fin (k + 20) → ℕ} {N : ℕ}
    (hin : ∀ m < N, (run (rfindBody (k := k) Cf) ⟨0, S⟩ m).pc <
      (rfindBody (k := k) Cf).length) (m : ℕ) (hm : m ≤ N) :
    run (rfindLoop (k := k) Cf) ⟨0, S⟩ m = run (rfindBody (k := k) Cf) ⟨0, S⟩ m := by
  rw [rfindLoop, run_append_of_lt (fun j hj => hin j (by omega))]

/-- **Zero turn.** The predicate answered zero, so the branch leaves the loop at the current
candidate. -/
theorem run_rfindTurn_zero {f : ℕ →. ℕ} (hf : CleanPartComputesUnary Cf f) (a c : ℕ)
    (hz : 0 ∈ f (Nat.pair a c)) :
    ∃ N, (∀ m < N, (run (rfindLoop (k := k) Cf) ⟨0, searchState a c⟩ m).pc <
        (rfindLoop (k := k) Cf).length) ∧
      run (rfindLoop (k := k) Cf) ⟨0, searchState a c⟩ N =
        ⟨(rfindLoop (k := k) Cf).length, searchState a c⟩ := by
  obtain ⟨N, hin, hex⟩ := run_rfindBody (k := k) hf a c 0 hz
  have hb : run (rfindLoop (k := k) Cf) ⟨0, searchState a c⟩ N =
      ⟨(rfindBody (k := k) Cf).length, searchAnswered a c 0⟩ := by
    rw [run_body_in_loop hin N (Nat.le_refl _), hex]
  refine ⟨N + 1, fun j hj => ?_, ?_⟩
  · rcases (show j ≤ N by omega).lt_or_eq with hlt | rfl
    · rw [run_body_in_loop hin j (by omega), length_rfindLoop]
      have := hin j hlt
      omega
    · rw [hb, length_rfindLoop]
      exact show (rfindBody (k := k) Cf).length < (rfindBody (k := k) Cf).length + 3 by omega
  · rw [show N + 1 = N + 1 from rfl, run_add, hb, run_one,
      step_dec_zero (getElem?_sBranch (Cf := Cf)) (by simp [searchAnswered]), length_rfindLoop]
    refine congrArg _ (funext fun r => ?_)
    rcases sLayout_cases r with rfl | rfl | rfl | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ <;>
      simp [searchAnswered, searchState]

/-- **Nonzero turn.** The predicate answered something else, so the loop discards it, steps the
candidate and returns to the head. The step count is positive, which is what the halting-time
induction needs. -/
theorem run_rfindTurn_ne {f : ℕ →. ℕ} (hf : CleanPartComputesUnary Cf f) (a c z : ℕ)
    (hzm : z ∈ f (Nat.pair a c)) (hz : z ≠ 0) :
    ∃ N, 0 < N ∧ (∀ m < N, (run (rfindLoop (k := k) Cf) ⟨0, searchState a c⟩ m).pc <
        (rfindLoop (k := k) Cf).length) ∧
      run (rfindLoop (k := k) Cf) ⟨0, searchState a c⟩ N = ⟨0, searchState a (c + 1)⟩ := by
  obtain ⟨N, hin, hex⟩ := run_rfindBody (k := k) hf a c z hzm
  have hval : searchAnswered (k := k) a c z (sCall k 0) = z := by simp [searchAnswered]
  have hb : run (rfindLoop (k := k) Cf) ⟨0, searchState a c⟩ N =
      ⟨(rfindBody (k := k) Cf).length, searchAnswered a c z⟩ := by
    rw [run_body_in_loop hin N (Nat.le_refl _), hex]
  have hstep : step (rfindLoop (k := k) Cf)
      ⟨(rfindBody (k := k) Cf).length, searchAnswered a c z⟩ =
      ⟨(rfindBody (k := k) Cf).length + 1,
        Function.update (searchAnswered (k := k) a c z) (sCall k 0) (z - 1)⟩ := by
    rw [step_dec_pos (getElem?_sBranch (Cf := Cf)) (by rw [hval]; exact hz), hval]
  have hdrain : run (rfindLoop (k := k) Cf)
      ⟨(rfindBody (k := k) Cf).length + 1,
        Function.update (searchAnswered (k := k) a c z) (sCall k 0) (z - 1)⟩ z =
      ⟨(rfindBody (k := k) Cf).length + 2,
        Function.update (searchAnswered (k := k) a c z) (sCall k 0) 0⟩ := by
    have h := run_drain (getElem?_sDrain (Cf := Cf))
      (Function.update (searchAnswered (k := k) a c z) (sCall k 0) (z - 1))
    rw [Function.update_self, Function.update_idem,
      show z - 1 + 1 = z from by omega] at h
    exact h
  refine ⟨N + (1 + (z + 1)), by omega, fun j hj => ?_, ?_⟩
  · rcases (show j ≤ N ∨ (N + 1 ≤ j ∧ j ≤ N + z) ∨ j = N + 1 + z by omega)
      with hle | ⟨h1, h2⟩ | rfl
    · rcases hle.lt_or_eq with hlt | rfl
      · rw [run_body_in_loop hin j (by omega), length_rfindLoop]
        have := hin j hlt
        omega
      · rw [hb, length_rfindLoop]
        exact show (rfindBody (k := k) Cf).length < (rfindBody (k := k) Cf).length + 3 by omega
    · rw [show j = N + 1 + (j - N - 1) by omega, run_add, run_add, run_one, hb, hstep,
        run_drain_partial (getElem?_sDrain (Cf := Cf)) _ (j - N - 1)
          (by rw [Function.update_self]; omega), length_rfindLoop]
      exact show (rfindBody (k := k) Cf).length + 1 <
        (rfindBody (k := k) Cf).length + 3 by omega
    · rw [show N + 1 + z = N + 1 + z from rfl, run_add, run_add, run_one, hb, hstep, hdrain,
        length_rfindLoop]
      exact show (rfindBody (k := k) Cf).length + 2 <
        (rfindBody (k := k) Cf).length + 3 by omega
  · rw [show N + (1 + (z + 1)) = N + 1 + z + 1 by omega, run_add, run_add, run_add,
      run_one, run_one, hb, hstep, hdrain, step_inc (getElem?_sInc (Cf := Cf))]
    refine congrArg _ (funext fun r => ?_)
    rcases sLayout_cases r with rfl | rfl | rfl | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
    · simp [searchAnswered, searchState]
    · simp [searchAnswered, searchState]
    · simp [searchAnswered, searchState]
    · simp [searchAnswered, searchState]
    · simp [searchAnswered, searchState]
    · simp [searchAnswered, searchState]
    · by_cases hi : i = 0
      · subst hi; simp [searchAnswered, searchState]
      · simp [searchAnswered, searchState, sCall_injective.eq_iff, hi]

/-! ### Soundness

There is no counter to induct on, so the induction is on the halting time. The nonzero turn's
`0 < steps` and its in-range clause together give `N - steps < N`. -/

/-- A halting loop forces the predicate to converge at the current candidate. -/
theorem rfindLoop_call_dom {f : ℕ →. ℕ} (hf : CleanPartComputesUnary Cf f) (a c : ℕ)
    (hh : Halts (rfindLoop (k := k) Cf) ⟨0, searchState a c⟩) : (f (Nat.pair a c)).Dom := by
  have hbody : Halts (rfindBody (k := k) Cf) ⟨0, searchState a c⟩ := by
    rw [rfindLoop] at hh
    exact halts_prefix_of_halts_append hh
  rw [rfindBody] at hbody
  obtain ⟨N1, i1, e1⟩ := run_rfindPairUp (k := k) a c
  have h1 := (halts_append_of_exits i1 (by rw [e1])).mp hbody
  rw [show (run (rfindPairUp (k := k)) ⟨0, searchState a c⟩ N1).regs =
    searchPaired a c from by rw [e1]] at h1
  obtain ⟨N2, i2, e2⟩ := run_rfindSeedCall (k := k) a c
  have h2 := (halts_append_of_exits i2 (by rw [e2])).mp h1
  rw [show (run (rfindSeedCall (k := k)) ⟨0, searchPaired a c⟩ N2).regs =
    searchSeeded a c from by rw [e2]] at h2
  exact (hf.call_halts_iff sCall_injective (regs := searchSeeded (k := k) a c)
    (x := Nat.pair a c) (by simp [searchSeeded])
    (fun i hi => by simp [searchSeeded, sCall_injective.eq_iff, hi])).mp h2

/-- **Soundness, with an explicit halting time.** A loop that halts at time `N` from candidate
`q + m` exhibits a stopping point `d ≥ q`, together with the failures in between. -/
theorem rfindLoop_sound_at {f : ℕ →. ℕ} (hf : CleanPartComputesUnary Cf f) (a m : ℕ) :
    ∀ N q, Halted (rfindLoop (k := k) Cf)
        (run (rfindLoop (k := k) Cf) ⟨0, searchState a (q + m)⟩ N) →
      ∃ d, 0 ∈ f (Nat.pair a (d + m)) ∧ q ≤ d ∧
        ∀ j, q ≤ j → j < d → ∃ z ∈ f (Nat.pair a (j + m)), z ≠ 0 := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro q hN
    have hdom := rfindLoop_call_dom (k := k) hf a (q + m) ⟨N, hN⟩
    by_cases hz : (f (Nat.pair a (q + m))).get hdom = 0
    · exact ⟨q, hz ▸ Part.get_mem hdom, Nat.le_refl q,
        fun j h1 h2 => absurd h2 (Nat.not_lt.mpr h1)⟩
    · obtain ⟨steps, hpos, hin, hex⟩ :=
        run_rfindTurn_ne (k := k) hf a (q + m) _ (Part.get_mem hdom) hz
      have hle : steps ≤ N := by
        by_contra hlt
        exact absurd hN (Nat.not_le.mpr (hin N (Nat.not_le.mp hlt)))
      obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hle
      rw [run_add, hex] at hN
      have hnext : Halted (rfindLoop (k := k) Cf)
          (run (rfindLoop (k := k) Cf) ⟨0, searchState a (q + 1 + m)⟩ t) := by
        rw [show q + 1 + m = q + m + 1 from by omega]
        exact hN
      obtain ⟨d, hd0, hdq, hdj⟩ := ih t (by omega) (q + 1) hnext
      refine ⟨d, hd0, by omega, fun j h1 h2 => ?_⟩
      rcases (show j = q ∨ q + 1 ≤ j by omega) with rfl | h3
      · exact ⟨_, Part.get_mem hdom, hz⟩
      · exact hdj j h3 h2

/-! ### Completeness, and the semantic endpoint -/

/-- **Segment completeness.** Given `q` failures, the loop walks from candidate `m` to `q + m`. -/
theorem run_rfindFailures {f : ℕ →. ℕ} (hf : CleanPartComputesUnary Cf f) (a m : ℕ) :
    ∀ q, (∀ j < q, ∃ z ∈ f (Nat.pair a (j + m)), z ≠ 0) →
      ∃ steps, (∀ s < steps, (run (rfindLoop (k := k) Cf) ⟨0, searchState a m⟩ s).pc <
          (rfindLoop (k := k) Cf).length) ∧
        run (rfindLoop (k := k) Cf) ⟨0, searchState a m⟩ steps =
          ⟨0, searchState a (q + m)⟩ := by
  intro q
  induction q with
  | zero =>
    intro _
    refine ⟨0, fun s hs => absurd hs (Nat.not_lt_zero s), ?_⟩
    rw [run_zero, show (0 : ℕ) + m = m from Nat.zero_add m]
  | succ q ih =>
    intro hfail
    obtain ⟨s1, i1, e1⟩ := ih (fun j hj => hfail j (by omega))
    obtain ⟨z, hz, hz0⟩ := hfail q (by omega)
    obtain ⟨s2, _, i2, e2⟩ := run_rfindTurn_ne (k := k) hf a (q + m) z hz hz0
    rw [show q + m + 1 = q + 1 + m from by omega] at e2
    exact ⟨s1 + s2, run_segment_trans i1 e1 i2 e2⟩

/-- **The loop's exact exit.** -/
theorem run_rfindLoop {f : ℕ →. ℕ} (hf : CleanPartComputesUnary Cf f) (a m y : ℕ)
    (hy : y ∈ rfindSem f a m) :
    ∃ N, (∀ s < N, (run (rfindLoop (k := k) Cf) ⟨0, searchState a m⟩ s).pc <
        (rfindLoop (k := k) Cf).length) ∧
      run (rfindLoop (k := k) Cf) ⟨0, searchState a m⟩ N =
        ⟨(rfindLoop (k := k) Cf).length, searchState a y⟩ := by
  obtain ⟨q, rfl, hq, hmin⟩ := mem_rfindSem.mp hy
  obtain ⟨s1, i1, e1⟩ := run_rfindFailures (k := k) hf a m q hmin
  obtain ⟨s2, i2, e2⟩ := run_rfindTurn_zero (k := k) hf a (q + m) hq
  exact ⟨s1 + s2, run_segment_trans i1 e1 i2 e2⟩

/-- **The semantic endpoint of the loop.** -/
theorem rfindLoop_halts_iff {f : ℕ →. ℕ} (hf : CleanPartComputesUnary Cf f) (a m : ℕ) :
    Halts (rfindLoop (k := k) Cf) ⟨0, searchState a m⟩ ↔ (rfindSem f a m).Dom := by
  constructor
  · rintro ⟨N, hN⟩
    have hN' : Halted (rfindLoop (k := k) Cf)
        (run (rfindLoop (k := k) Cf) ⟨0, searchState a (0 + m)⟩ N) := by
      rw [show (0 : ℕ) + m = m from Nat.zero_add m]
      exact hN
    obtain ⟨d, hd0, _, hdj⟩ := rfindLoop_sound_at (k := k) hf a m N 0 hN'
    exact Part.dom_iff_mem.mpr ⟨d + m,
      mem_rfindSem.mpr ⟨d, rfl, hd0, fun j hj => hdj j (Nat.zero_le j) hj⟩⟩
  · intro hd
    obtain ⟨N, _, hex⟩ :=
      run_rfindLoop (k := k) hf a m ((rfindSem f a m).get hd) (Part.get_mem hd)
    exact ⟨N, by rw [hex]; exact Nat.le_refl _⟩

/-! ## The controller

One partial boundary: the packaged search loop. -/

/-- After the input has been copied to the unpairing block. -/
def rfindCtlA (x : ℕ) : Fin (k + 20) → ℕ :=
  fun r => if r = sUnpair k 0 then x else if r = 0 then x else 0

/-- After unpairing. -/
def rfindCtlB (x : ℕ) : Fin (k + 20) → ℕ :=
  fun r => if r = sUnpair k 1 then x.unpair.1 else if r = sUnpair k 2 then x.unpair.2
    else if r = 0 then x else 0

theorem run_rfindSplit (x : ℕ) :
    ∃ N, (∀ m < N, (run (rfindSplit (k := k)) ⟨0, unaryConfig (k + 19) x⟩ m).pc <
        (rfindSplit (k := k)).length) ∧
      run (rfindSplit (k := k)) ⟨0, unaryConfig (k + 19) x⟩ N =
        ⟨(rfindSplit (k := k)).length, rfindCtlB x⟩ := by
  rw [rfindSplit]
  obtain ⟨N1, i1, e1⟩ :=
    realises_copy (r := (0 : Fin (k + 20))) (s := sUnpair k 0) (t := sT k)
      (by simp) (by simp) (by simp) (unaryConfig (k + 19) x)
  have e1' : run (copy 0 (sUnpair k 0) (sT k)) ⟨0, unaryConfig (k + 19) x⟩ N1 =
      ⟨(copy 0 (sUnpair k 0) (sT k)).length, rfindCtlA x⟩ := by
    rw [e1]
    refine congrArg _ (funext fun r => ?_)
    rcases sLayout_cases r with rfl | rfl | rfl | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ <;>
      simp [unaryConfig, rfindCtlA, sUnpair_injective.eq_iff]
  obtain ⟨N2, hu2, hu3⟩ := run_unpairLoop x
  obtain ⟨i2, e2⟩ :=
    run_renameRegs_of_exit sUnpair_injective hu2 hu3 (regs := rfindCtlA (k := k) x)
      (fun i => by
        rcases (show i = 0 ∨ i ≠ 0 by tauto) with rfl | hi
        · simp [rfindCtlA, unaryConfig]
        · simp [rfindCtlA, unaryConfig, sUnpair_injective.eq_iff, hi])
  have e2' : run (renameRegs (sUnpair k) unpairLoop) ⟨0, rfindCtlA x⟩ N2 =
      ⟨(renameRegs (sUnpair k) unpairLoop).length, rfindCtlB x⟩ := by
    rw [e2]
    refine congrArg _ (funext fun r => ?_)
    rcases sLayout_cases r with rfl | rfl | rfl | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
    · rw [Function.extend_apply' _ _ _ (by rintro ⟨i, hi⟩; exact (sUnpair_ne_fixed i).1 hi)]
      simp [rfindCtlA, rfindCtlB]
    · rw [Function.extend_apply' _ _ _ (by rintro ⟨i, hi⟩; exact (sUnpair_ne_fixed i).2.1 hi)]
      simp [rfindCtlA, rfindCtlB]
    · rw [Function.extend_apply' _ _ _ (by rintro ⟨i, hi⟩; exact (sUnpair_ne_fixed i).2.2.1 hi)]
      simp [rfindCtlA, rfindCtlB]
    · rw [Function.extend_apply' _ _ _ (by rintro ⟨i, hi⟩; exact (sUnpair_ne_fixed i).2.2.2 hi)]
      simp [rfindCtlA, rfindCtlB]
    · rw [Function.extend_apply' _ _ _ (by rintro ⟨j, hj⟩; exact (sUnpair_ne_sPair j i) hj)]
      simp [rfindCtlA, rfindCtlB]
    · rw [sUnpair_injective.extend_apply]
      simp only [rfindCtlB]
      fin_cases i <;> simp [sUnpair_injective.eq_iff]
    · rw [Function.extend_apply' _ _ _ (by rintro ⟨j, hj⟩; exact (sUnpair_ne_sCall j i) hj)]
      simp [rfindCtlA, rfindCtlB]
  exact ⟨N1 + N2, join_exit i1 e1' i2 e2'⟩

theorem run_rfindSeed (x : ℕ) :
    ∃ N, (∀ m < N, (run (rfindSeed (k := k)) ⟨0, rfindCtlB x⟩ m).pc <
        (rfindSeed (k := k)).length) ∧
      run (rfindSeed (k := k)) ⟨0, rfindCtlB x⟩ N =
        ⟨(rfindSeed (k := k)).length, searchState x.unpair.1 x.unpair.2⟩ := by
  rw [rfindSeed]
  obtain ⟨N, hin, hex⟩ :=
    ((realises_move (r := sUnpair k 1) (s := sA k) (by simp)).seq
      ((realises_move (r := sUnpair k 2) (s := sC k) (by simp)).seq
        (realises_clear (0 : Fin (k + 20))))) (rfindCtlB (k := k) x)
  refine ⟨N, hin, ?_⟩
  rw [hex]
  clear hex hin
  refine congrArg _ (funext fun r => ?_)
  rcases sLayout_cases r with rfl | rfl | rfl | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · simp [rfindCtlB, searchState, sUnpair_injective.eq_iff]
  · simp [rfindCtlB, searchState, sUnpair_injective.eq_iff]
  · simp [rfindCtlB, searchState, sUnpair_injective.eq_iff]
  · simp [rfindCtlB, searchState, sUnpair_injective.eq_iff]
  · simp [rfindCtlB, searchState, sUnpair_injective.eq_iff]
  · fin_cases i <;> simp [rfindCtlB, searchState, sUnpair_injective.eq_iff]
  · simp [rfindCtlB, searchState, sUnpair_injective.eq_iff]

theorem run_rfindFinish (a y : ℕ) :
    ∃ N, (∀ m < N, (run (rfindFinish (k := k)) ⟨0, searchState a y⟩ m).pc <
        (rfindFinish (k := k)).length) ∧
      run (rfindFinish (k := k)) ⟨0, searchState a y⟩ N =
        ⟨(rfindFinish (k := k)).length, unaryConfig (k + 19) y⟩ := by
  rw [rfindFinish]
  obtain ⟨N, hin, hex⟩ :=
    ((realises_clear (sA k)).seq
      (realises_move (r := sC k) (s := (0 : Fin (k + 20))) (by simp)))
      (searchState (k := k) a y)
  refine ⟨N, hin, ?_⟩
  rw [hex]
  clear hex hin
  refine congrArg _ (funext fun r => ?_)
  rcases sLayout_cases r with rfl | rfl | rfl | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ <;>
    simp [searchState, unaryConfig]

/-- **`Code.rfind'`'s closure theorem.** -/
theorem CleanPartComputesUnary.rfind' {f : ℕ →. ℕ} (hf : CleanPartComputesUnary Cf f) :
    CleanPartComputesUnary (rfindController (k := k) Cf)
      fun x => rfindSem f x.unpair.1 x.unpair.2 := by
  intro x
  refine ⟨fun y hy => ?_, fun hh => ?_⟩
  · obtain ⟨N1, i1, e1⟩ := run_rfindSplit (k := k) x
    obtain ⟨N2, i2, e2⟩ := run_rfindSeed (k := k) x
    obtain ⟨N3, i3, e3⟩ := run_rfindLoop (k := k) hf x.unpair.1 x.unpair.2 y hy
    obtain ⟨N4, i4, e4⟩ := run_rfindFinish (k := k) x.unpair.1 y
    obtain ⟨j34, f34⟩ := join_exit i3 e3 i4 e4
    obtain ⟨j234, f234⟩ := join_exit i2 e2 j34 f34
    exact ⟨N1 + (N2 + (N3 + N4)), join_exit i1 e1 j234 f234⟩
  · obtain ⟨N1, i1, e1⟩ := run_rfindSplit (k := k) x
    have h1 := (halts_append_of_exits i1 (by rw [e1])).mp hh
    rw [show (run (rfindSplit (k := k)) ⟨0, unaryConfig (k + 19) x⟩ N1).regs =
      rfindCtlB x from by rw [e1]] at h1
    obtain ⟨N2, i2, e2⟩ := run_rfindSeed (k := k) x
    have h2 := (halts_append_of_exits i2 (by rw [e2])).mp h1
    rw [show (run (rfindSeed (k := k)) ⟨0, rfindCtlB x⟩ N2).regs =
      searchState x.unpair.1 x.unpair.2 from by rw [e2]] at h2
    exact (rfindLoop_halts_iff (k := k) hf x.unpair.1 x.unpair.2).mp
      (halts_prefix_of_halts_append h2)

/-- **`Code.rfind'`.** `congr` through the source-semantics bridge, and nothing else. -/
theorem CleanPartComputesUnary.codeRfind {cf : Code} (hf : CleanPartComputesUnary Cf cf.eval) :
    CleanPartComputesUnary (rfindController (k := k) Cf) (Code.rfind' cf).eval :=
  (CleanPartComputesUnary.rfind' (k := k) hf).congr fun x => (eval_rfind_unpair cf x).symm

end RegisterMachine

end Hilbert10


/- Source: Hilbert10.Internal.CodeMachine, Hilbert10 v2.3.0, Apache-2.0. -/
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# Every code has a machine

Issue #44. The constructor library is complete, so this is a structural induction that selects
the right closure theorem in each case.

## Proposition-valued on purpose

`exists_cleanMachine` is an existential, not a `Code → Program` compiler with a correctness
certificate. Nothing downstream needs the machine as *data*: #21 arithmetises a fixed machine's
trace relation, and fixing it is existential elimination in a `Prop`. Producing a dependent
compiler object would be the verified-DSL project (#29) arriving through the side door — the same
argument that made DPRM a semantic theorem in the first place.

## The graph relation

`Accepts` (in `CleanScratch`) is trace-level: it says the machine takes the clean configuration
for `x` to the clean configuration for `y`, with no mention of the function computed.
`accepts_iff` is the only place the two meet, and `exists_machine_graph` is what #21 consumes.
-/

namespace Hilbert10

namespace RegisterMachine

open Nat.Partrec (Code)

/-- **Every code is computed by a clean machine.** -/
theorem exists_cleanMachine (c : Code) :
    ∃ (k : ℕ) (P : Program (k + 1)), CleanPartComputesUnary P c.eval := by
  induction c with
  | zero =>
    exact ⟨0, zeroMachine 0, computesUnary_zeroMachine.toPart.toClean.congr fun x => rfl⟩
  | succ =>
    exact ⟨0, succMachine 0, computesUnary_succMachine.toPart.toClean.congr fun x => rfl⟩
  | left => exact ⟨5, leftMachine, cleanPartComputesUnary_leftMachine.congr fun x => rfl⟩
  | right => exact ⟨5, rightMachine, cleanPartComputesUnary_rightMachine.congr fun x => rfl⟩
  | pair cf cg ihf ihg =>
    obtain ⟨kf, Pf, hf⟩ := ihf
    obtain ⟨kg, Pg, hg⟩ := ihg
    exact ⟨kf + kg + 12, _, hf.codePair hg⟩
  | comp cf cg ihf ihg =>
    obtain ⟨kf, Pf, hf⟩ := ihf
    obtain ⟨kg, Pg, hg⟩ := ihg
    have hf' := hf.widen (k' := max kf kg)
      (σ := Fin.castLE (by omega)) (Fin.castLE_injective _) (by simp)
    have hg' := hg.widen (k' := max kf kg)
      (σ := Fin.castLE (by omega)) (Fin.castLE_injective _) (by simp)
    exact ⟨max kf kg, _, (hg'.comp hf').congr fun x => rfl⟩
  | prec cf cg ihf ihg =>
    obtain ⟨kf, Pf, hf⟩ := ihf
    obtain ⟨kg, Pg, hg⟩ := ihg
    exact ⟨kf + kg + 31, _, CleanPartComputesUnary.codePrec (k := kf) (k' := kg) Pf Pg hf hg⟩
  | rfind' cf ihf =>
    obtain ⟨kf, Pf, hf⟩ := ihf
    exact ⟨kf + 19, _, CleanPartComputesUnary.codeRfind hf⟩

/-- **The graph endpoint.** A fixed machine whose trace relation is exactly the code's graph —
which is what #21 arithmetises. -/
theorem exists_machine_graph (c : Code) :
    ∃ (k : ℕ) (P : Program (k + 1)), ∀ x y, Accepts P x y ↔ y ∈ c.eval x := by
  obtain ⟨k, P, h⟩ := exists_cleanMachine c
  exact ⟨k, P, fun x y => h.accepts_iff x y⟩

end RegisterMachine

end Hilbert10


/- Source: Hilbert10.PolyBridge, Hilbert10 v2.3.0, Apache-2.0. -/
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# The `Poly` / `MvPolynomial` bridge

Issues #3, #4 and #5. `Mathlib.NumberTheory.Dioph` carries the TODO "Connect `Poly` to
`MvPolynomial`"; this is that connection, in the form the Diophantine normal form (#6)
needs.

## Main declarations

* `MvPolynomial.toDiophPoly`: the ring homomorphism `MvPolynomial α ℤ →+* Poly α`.
* `exists_mvPolynomial`: conversely, every `Poly` agrees with some `MvPolynomial` at
  natural-number valuations. This is an *existence* statement, not a function: `Poly` is an
  extensional subtype whose induction principle eliminates into `Prop` only, so no
  computable extraction is available or attempted.
* `MvPolynomial.RepresentsNat`: the specification relation saying that a polynomial in
  input variables `α` and witness variables `β` represents a relation on `α`-tuples.

## Implementation notes

`Poly α` is a `CommRing` (`Mathlib/NumberTheory/Dioph.lean`), so the forward direction is
`eval₂Hom` rather than a bare function. Everything downstream then commutes with `+`, `*`
and `C` by `map_add` / `map_mul` / `map_intCast` instead of bespoke induction.
-/

namespace Hilbert10

open MvPolynomial

variable {α β : Type*}

/-! ### From `MvPolynomial` to `Poly` -/

/-- The ring homomorphism sending a multivariate integer polynomial to the corresponding
`Poly`, i.e. to its evaluation function on natural-number valuations. -/
def toDiophPoly : MvPolynomial α ℤ →+* Poly α :=
  eval₂Hom (Int.castRingHom (Poly α)) Poly.proj

@[simp]
theorem toDiophPoly_X (i : α) : toDiophPoly (X i : MvPolynomial α ℤ) = Poly.proj i := by
  simp [toDiophPoly]

/-- The integer cast into `Poly α` is the constant function. -/
@[simp]
theorem Poly.intCast_apply (n : ℤ) (x : α → ℕ) : ((n : Poly α)) x = n := by
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih => push_cast at ih ⊢; simp [ih]
  | pred k ih => push_cast at ih ⊢; simp [ih]

@[simp]
theorem toDiophPoly_C (n : ℤ) : toDiophPoly (C n : MvPolynomial α ℤ) = Poly.const n := by
  ext x
  simp [toDiophPoly]

/-- Evaluating the `Poly` produced by `toDiophPoly` at a natural-number valuation agrees
with evaluating the original polynomial at the corresponding integer valuation. -/
@[simp]
theorem toDiophPoly_apply (p : MvPolynomial α ℤ) (x : α → ℕ) :
    toDiophPoly p x = eval (fun i => (x i : ℤ)) p := by
  induction p using MvPolynomial.induction_on with
  | C n => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

/-! ### From `Poly` to `MvPolynomial` -/

/-- Every `Poly` agrees, at natural-number valuations, with some multivariate integer
polynomial.

This is an existence statement rather than a function: `Poly.induction` eliminates into
`Prop` only, so nothing here extracts syntax from a `Poly`. Note also where finiteness
enters — the `MvPolynomial` produced has finite support by construction, whereas the
variable type of the `Poly` may be arbitrary. -/
theorem exists_mvPolynomial (p : Poly α) :
    ∃ q : MvPolynomial α ℤ, ∀ x : α → ℕ, eval (fun i => (x i : ℤ)) q = p x := by
  induction p using Poly.induction with
  | H1 i => exact ⟨X i, fun x => by simp⟩
  | H2 n => exact ⟨C n, fun x => by simp⟩
  | H3 f g hf hg =>
    obtain ⟨qf, hqf⟩ := hf
    obtain ⟨qg, hqg⟩ := hg
    exact ⟨qf - qg, fun x => by simp [hqf, hqg]⟩
  | H4 f g hf hg =>
    obtain ⟨qf, hqf⟩ := hf
    obtain ⟨qg, hqg⟩ := hg
    exact ⟨qf * qg, fun x => by simp [hqf, hqg]⟩

/-! ### The specification relation -/

/-- `p.RepresentsNat R` says that the polynomial `p`, in input variables `α` and witness
variables `β`, represents the relation `R` on `α`-tuples of naturals: `R x` holds exactly
when `p` has a natural-number root extending `x`.

The variable types are deliberately left general; the finite `Fin n ⊕ Fin m` shape belongs
to the normal-form theorem (#6), not to this definition.

Note this lives in the `Hilbert10` namespace rather than `MvPolynomial`: dot
notation on `MvPolynomial` is unreliable anyway, since the type unfolds to
`AddMonoidAlgebra`. It moves to the `MvPolynomial` namespace when upstreamed. -/
def RepresentsNat (p : MvPolynomial (α ⊕ β) ℤ) (R : (α → ℕ) → Prop) : Prop :=
  ∀ x : α → ℕ, R x ↔ ∃ y : β → ℕ,
    eval (Sum.elim (fun i => (x i : ℤ)) (fun j => (y j : ℤ))) p = 0

theorem RepresentsNat.congr {p : MvPolynomial (α ⊕ β) ℤ} {R S : (α → ℕ) → Prop}
    (h : RepresentsNat p R) (hRS : ∀ x, R x ↔ S x) : RepresentsNat p S :=
  fun x => (hRS x).symm.trans (h x)

end Hilbert10


/- Source: Hilbert10.Internal.ForMathlib.RightRename, Hilbert10 v2.3.0, Apache-2.0. -/
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# Compacting only the witness variables

Issue #2, staged here for upstreaming to mathlib.

`MvPolynomial.exists_fin_rename` reindexes the *entire* variable type along an injection
`Fin n → σ`. Applied at `σ = Fin n ⊕ β` it renumbers the input variables together with the
witnesses, which destroys the input/witness partition that the whole Hilbert-tenth
development is built on (issue #6 fixes inputs as the left summand and existential
witnesses as the right one).

What is needed instead is a *right-only* compaction: the `Fin n` block is fixed pointwise
and only `β` is compacted to its finite support.
-/

namespace Hilbert10

open MvPolynomial

variable {β R : Type*} [CommSemiring R]

/-- Every polynomial in `σ ⊕ τ` is a polynomial in all of the variables from `σ` and finitely
many of the variables from `τ`. Mirrors `MvPolynomial.exists_finset_rename`. -/
theorem exists_finset_right_rename {σ : Type*} (p : MvPolynomial (σ ⊕ β) R) :
    ∃ (t : Finset β) (q : MvPolynomial (σ ⊕ { x // x ∈ t }) R),
      p = rename (Sum.map id (↑)) q := by
  classical
  obtain ⟨s, q, rfl⟩ := exists_finset_rename p
  let f : { x // x ∈ s } → σ ⊕ { x // x ∈ s.toRight } := fun x =>
    match h : x.1 with
    | .inl a => .inl a
    | .inr b => .inr ⟨b, Finset.mem_toRight.mpr (h ▸ x.2)⟩
  refine ⟨s.toRight, rename f q, ?_⟩
  rw [rename_rename]
  congr 2
  funext x
  rcases x with ⟨a | b, h⟩
  · rfl
  · simp [f]

/-- Compact only the right summand of the variable type: the variables from `σ` are preserved
pointwise, and the witnesses are reindexed by a finite injection.

Unlike `MvPolynomial.exists_fin_rename`, which reindexes the whole variable type along an
injection `Fin n → σ ⊕ β`, the left summand is left untouched. This is what the Diophantine
normal form needs: renumbering the *input* variables would change the relation represented.

Upstreamed as leanprover-community/mathlib4#42203; delete this file once that merges. -/
theorem exists_fin_right_rename {σ : Type*} (p : MvPolynomial (σ ⊕ β) R) :
    ∃ (m : ℕ) (f : Fin m → β) (_ : Function.Injective f) (q : MvPolynomial (σ ⊕ Fin m) R),
      p = rename (Sum.map id f) q := by
  obtain ⟨t, q, rfl⟩ := exists_finset_right_rename p
  let m := Fintype.card { x // x ∈ t }
  let e := Fintype.equivFin { x // x ∈ t }
  refine ⟨m, (↑) ∘ e.symm, Subtype.val_injective.comp e.symm.injective,
    rename (Sum.map id e) q, ?_⟩
  rw [rename_rename]
  congr 1
  ext x
  obtain a | b := x <;> simp

/-- The evaluation corollary that downstream actually consumes. Stated with assignments in
the coefficient ring; for a different target ring use `eval₂` with a `RingHom R →+* S`
rather than an `S`-valued `eval`, which would not typecheck against `R` coefficients. -/
theorem eval_of_exists_fin_right_rename {σ : Type*} (p : MvPolynomial (σ ⊕ β) R)
    {m : ℕ} {f : Fin m → β} {q : MvPolynomial (σ ⊕ Fin m) R}
    (hq : p = rename (Sum.map id f) q) (x : σ → R) (y : β → R) :
    eval (Sum.elim x y) p = eval (Sum.elim x (y ∘ f)) q := by
  subst hq
  have hassign : Sum.elim x y ∘ Sum.map id f = Sum.elim x (y ∘ f) := by
    funext i
    cases i <;> rfl
  rw [eval_rename, hassign]

end Hilbert10


/- Source: Hilbert10.NormalForm, Hilbert10 v2.3.0, Apache-2.0. -/
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# The finite Diophantine normal form

Issue #6, the headline result of M1. Mathlib's `Dioph` existentially quantifies an
arbitrary witness type `β : Type u` and a bespoke `Poly`. Here we show that for relations
on finite tuples one may always take the witnesses to be `Fin m` and the polynomial to be
an honest `MvPolynomial`.

This fixes the convention every later milestone depends on: **inputs are the left summand
`Fin n`, existentially quantified witnesses are the right summand `Fin m`**.

## Implementation notes

The order of the two steps matters. Finiteness of the witness block is *created* by
`Hilbert10.exists_mvPolynomial` (in `PolyBridge`), whose output has finite support by
construction; the arbitrary `β` in `Dioph` gives no finiteness on its own. Only then can
`exists_fin_right_rename` compact that support to `Fin m`.

Witnesses outside the range of the compacting injection are unused, so the reverse
inclusion extends a `Fin m`-tuple back to a `β`-tuple with `Function.extend`.

## An arbitrary finite input type

`dioph_iff_exists_finite_mvPolynomial` is the same statement for any `Finite` input type,
transported along an equivalence with `Fin n`. Two conventions are forced rather than chosen:

* the hypothesis is `Finite`, not `Fintype` — the proof needs only an equivalence, the conclusion
  is a `Prop`, and mathlib's `unusedFintypeInType` linter rejects a `Fintype` restatement;
* the input type is `Type`, not `Type*` — mathlib's `Dioph.reindex_dioph` keeps source and target
  in one universe, so transporting an arbitrary input type to `Fin n` forces `Type 0`. `Dioph`
  itself is universe-polymorphic; its closure API is not.
-/

namespace Hilbert10

open MvPolynomial

variable {α β : Type*} {n : ℕ}

/-- Casting a `Sum.elim` of natural-valued tuples agrees with `Sum.elim` of the casts. -/
theorem sum_elim_cast (x : α → ℕ) (y : β → ℕ) :
    (Sum.elim (fun i => (x i : ℤ)) fun j => (y j : ℤ)) = fun i => ((Sum.elim x y i : ℕ) : ℤ) := by
  funext i
  cases i <;> rfl

/-- **The finite Diophantine normal form.** A relation on `Fin n`-tuples of naturals is
Diophantine exactly when it is represented by a multivariate integer polynomial in `n`
input variables and finitely many witness variables.

This discharges the "Connect `Poly` to `MvPolynomial`" TODO of `Mathlib.NumberTheory.Dioph`
in the form the rest of the project needs. -/
theorem dioph_iff_exists_fin_mvPolynomial (R : (Fin n → ℕ) → Prop) :
    Dioph {x : Fin n → ℕ | R x} ↔
      ∃ (m : ℕ) (p : MvPolynomial (Fin n ⊕ Fin m) ℤ), RepresentsNat p R := by
  constructor
  · rintro ⟨β, p, hp⟩
    have hp' : ∀ v : Fin n → ℕ, R v ↔ ∃ t : β → ℕ, p (Sum.elim v t) = 0 := hp
    -- Replace the bespoke `Poly` by an `MvPolynomial`: this is where finiteness appears.
    obtain ⟨q, hq⟩ := exists_mvPolynomial p
    -- Compact the witness variables, leaving the inputs alone.
    obtain ⟨m, f, hf, q', rfl⟩ := exists_fin_right_rename (σ := Fin n) q
    -- Evaluating the compacted polynomial at a witness tuple pulled back along `f`.
    have key : ∀ (x : Fin n → ℕ) (t : β → ℕ),
        eval (Sum.elim (fun i => (x i : ℤ)) fun j => ((t (f j) : ℕ) : ℤ)) q' =
          p (Sum.elim x t) := by
      intro x t
      rw [← hq (Sum.elim x t), ← sum_elim_cast]
      exact (eval_of_exists_fin_right_rename _ rfl (fun i => (x i : ℤ)) fun b => (t b : ℤ)).symm
    refine ⟨m, q', fun x => ?_⟩
    rw [hp' x]
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨fun j => t (f j), (key x t).trans ht⟩
    · rintro ⟨y, hy⟩
      classical
      refine ⟨Function.extend f y (fun _ => 0), ?_⟩
      rw [← key x (Function.extend f y fun _ => 0)]
      simpa only [hf.extend_apply] using hy
  · rintro ⟨m, p, hp⟩
    refine ⟨Fin m, toDiophPoly p, fun x => ?_⟩
    change R x ↔ _
    rw [hp x]
    exact exists_congr fun y => by rw [toDiophPoly_apply, ← sum_elim_cast]

/-- **The normal form at any finite input type.** Transport of `dioph_iff_exists_fin_mvPolynomial`
along an equivalence `α ≃ Fin n`, on both the `Dioph` side (by reindexing) and the polynomial side
(by renaming). -/
theorem dioph_iff_exists_finite_mvPolynomial {α : Type} [Finite α] (R : (α → ℕ) → Prop) :
    Dioph {x : α → ℕ | R x} ↔
      ∃ (m : ℕ) (p : MvPolynomial (α ⊕ Fin m) ℤ), RepresentsNat p R := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin α
  have hcomp : ∀ x : α → ℕ, (x ∘ e.symm) ∘ e = x := fun x => funext fun a => by simp
  constructor
  · intro hD
    -- reindex the Diophantine set to `Fin n`, apply the frozen normal form, rename back
    have hFin : Dioph {v : Fin n → ℕ | R (v ∘ e)} :=
      Dioph.reindex_dioph (S := {x : α → ℕ | R x}) (Fin n) e hD
    obtain ⟨m, q, hq⟩ := (dioph_iff_exists_fin_mvPolynomial _).mp hFin
    refine ⟨m, rename (Sum.map e.symm id) q, fun x => ?_⟩
    have hx := hq (x ∘ e.symm)
    dsimp only at hx
    rw [hcomp] at hx
    refine hx.trans (exists_congr fun y => ?_)
    rw [eval_rename]
    have hfun : (Sum.elim (fun i : α => ((x i : ℕ) : ℤ)) fun j : Fin m => ((y j : ℕ) : ℤ))
        ∘ Sum.map e.symm id
        = Sum.elim (fun i : Fin n => (((x ∘ e.symm) i : ℕ) : ℤ))
            fun j : Fin m => ((y j : ℕ) : ℤ) := by
      funext i
      cases i <;> rfl
    rw [hfun]
  · rintro ⟨m, p, hp⟩
    -- rename the polynomial to `Fin n` inputs, apply the frozen normal form, reindex back
    have hFin : Dioph {v : Fin n → ℕ | R (v ∘ e)} := by
      refine (dioph_iff_exists_fin_mvPolynomial _).mpr ⟨m, rename (Sum.map e id) p, fun v => ?_⟩
      refine (hp (v ∘ e)).trans (exists_congr fun y => ?_)
      rw [eval_rename]
      have hfun : (Sum.elim (fun i : Fin n => ((v i : ℕ) : ℤ)) fun j : Fin m => ((y j : ℕ) : ℤ))
          ∘ Sum.map e id
          = Sum.elim (fun i : α => (((v ∘ e) i : ℕ) : ℤ)) fun j : Fin m => ((y j : ℕ) : ℤ) := by
        funext i
        cases i <;> rfl
      rw [hfun]
    have hback := Dioph.reindex_dioph (S := {v : Fin n → ℕ | R (v ∘ e)}) α e.symm hFin
    refine Dioph.ext hback fun x => ?_
    simp only [Set.mem_setOf_eq]
    rw [hcomp]

end Hilbert10


/- Source: Hilbert10.PolynomialCode, Hilbert10 v2.3.0, Apache-2.0. -/
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# A wire format for Hilbert's tenth problem

Issue #8. To state H10 as a decision problem the input must be a finitely encoded object;
this is that encoding, and deliberately nothing more.

## Design

* **Permissive, not canonical.** Duplicate monomials, zero coefficients, trailing zero
  exponents and arbitrary term order are all legal. H10's undecidability must not depend
  on canonicalisation, so there is no quotient, no normal form and no `DecidableEq`
  obligation.
* **Missing variables evaluate to zero.** Evaluation recurses structurally over the
  exponent and assignment lists in parallel; an exhausted assignment is treated as zeros.
  This is what makes zero-extension hold *unconditionally* and keeps the computability
  proof of #9 free of index arithmetic.
* **`arity` is a presentation upper bound**, the maximum exponent-vector length — not the
  minimal semantic arity, which would be false for a permissive format. Every use of it in
  this project is an upper bound. Do not state or rely on any minimality lemma.

Deliberately absent: any `MvPolynomial` connection (that is #10), any `+`/`*` API,
substitution beyond #12, systems of equations, or fresh-variable allocation.
-/

namespace Hilbert10

/-- The exponent vector of a monomial: the `i`-th entry is the exponent of variable `i`. -/
abbrev MonomialCode := List ℕ

/-- A permissive sparse encoding of a multivariate integer polynomial as a list of
`(coefficient, exponent vector)` pairs. -/
structure PolynomialCode where
  /-- The terms of the polynomial, as `(coefficient, exponent vector)` pairs. -/
  terms : List (ℤ × MonomialCode)

namespace PolynomialCode

/-- The value of a monomial at an assignment, by structural recursion on the exponent
vector and the assignment in parallel. Variables past the end of the assignment are taken
to be `0`; note `(0 : ℤ) ^ 0 = 1`, so a zero exponent is harmless there. -/
def evalMonomial : MonomialCode → List ℕ → ℤ
  | [], _ => 1
  | e :: es, [] => (0 : ℤ) ^ e * evalMonomial es []
  | e :: es, v :: vs => (v : ℤ) ^ e * evalMonomial es vs

/-- The value of an encoded polynomial at an assignment. -/
def eval (p : PolynomialCode) (x : List ℕ) : ℤ :=
  (p.terms.map fun t => t.1 * evalMonomial t.2 x).sum

/-- A presentation upper bound on the number of variables: the maximum exponent-vector
length. Trailing zero exponents inflate it, which is harmless — see the module docstring. -/
def arity (p : PolynomialCode) : ℕ :=
  (p.terms.map fun t => t.2.length).foldr max 0

@[simp] theorem evalMonomial_nil (x : List ℕ) : evalMonomial [] x = 1 := rfl

@[simp] theorem eval_mk_nil (x : List ℕ) : eval ⟨[]⟩ x = 0 := rfl

/-! ### Zero-extension

Padding an assignment with zeros never changes a value, with no hypothesis at all: the
variables being supplied were already being read as zero.
-/

theorem evalMonomial_append_zeros (e : MonomialCode) (x z : List ℕ) (hz : ∀ v ∈ z, v = 0) :
    evalMonomial e (x ++ z) = evalMonomial e x := by
  induction e generalizing x z with
  | nil => rfl
  | cons a es ih =>
    cases x with
    | nil =>
      cases z with
      | nil => rfl
      | cons c cs =>
        obtain rfl : c = 0 := hz c (by simp)
        have hrec : evalMonomial es cs = evalMonomial es [] := by
          simpa using ih [] cs fun v hv => hz v (by simp [hv])
        simp [evalMonomial, hrec]
    | cons v vs =>
      simp only [List.cons_append, evalMonomial]
      rw [ih vs z hz]

theorem eval_append_zeros (p : PolynomialCode) (x z : List ℕ) (hz : ∀ v ∈ z, v = 0) :
    p.eval (x ++ z) = p.eval x := by
  simp only [eval]
  congr 1
  exact List.map_congr_left fun t _ => by rw [evalMonomial_append_zeros t.2 x z hz]

/-- Zero-extension: padding an assignment with zeros is invisible. -/
theorem eval_append_replicate_zero (p : PolynomialCode) (x : List ℕ) (k : ℕ) :
    p.eval (x ++ List.replicate k 0) = p.eval x :=
  p.eval_append_zeros x _ fun _ hv => List.eq_of_mem_replicate hv

/-! ### Append-invariance under the arity bound

Once an assignment is at least as long as the arity, appending anything is invisible: the
extra values are never read.
-/

theorem evalMonomial_append_of_length_le {e : MonomialCode} {x : List ℕ} (h : e.length ≤ x.length)
    (y : List ℕ) : evalMonomial e (x ++ y) = evalMonomial e x := by
  induction e generalizing x with
  | nil => rfl
  | cons a es ih =>
    cases x with
    | nil => simp at h
    | cons v vs =>
      simp only [List.cons_append, evalMonomial]
      rw [ih (by simpa using h)]

theorem length_le_foldr_max {l : List (ℤ × MonomialCode)} {t : ℤ × MonomialCode} (ht : t ∈ l) :
    t.2.length ≤ (l.map fun s => s.2.length).foldr max 0 := by
  induction l with
  | nil => cases ht
  | cons s ss ih =>
    rcases List.mem_cons.mp ht with rfl | hts
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih hts) (Nat.le_max_right _ _)

theorem length_le_arity {p : PolynomialCode} {t : ℤ × MonomialCode} (ht : t ∈ p.terms) :
    t.2.length ≤ p.arity :=
  length_le_foldr_max ht

theorem eval_append_of_arity_le {p : PolynomialCode} {x : List ℕ} (h : p.arity ≤ x.length)
    (y : List ℕ) : p.eval (x ++ y) = p.eval x := by
  simp only [eval]
  congr 1
  exact List.map_congr_left fun t ht => by
    rw [evalMonomial_append_of_length_le (Nat.le_trans (length_le_arity ht) h)]

/-! ### Sanity checks

Concrete instances of the three conventions, kept as regression tests: the encoding of
`x₀ ^ 2 + x₁ ^ 2 - 25`, a variable read past the end of an assignment, and a trailing zero
exponent inflating `arity` without changing any value.
-/

example : (⟨[(1, [2]), (1, [0, 2]), (-25, [])]⟩ : PolynomialCode).eval [3, 4] = 0 := by decide

example : (⟨[(1, [2]), (1, [0, 2]), (-25, [])]⟩ : PolynomialCode).arity = 2 := by decide

example : (⟨[(1, [0, 1])]⟩ : PolynomialCode).eval [5] = 0 := by decide

example : (⟨[(1, [1, 0, 0])]⟩ : PolynomialCode).arity = 3 := by decide

example : (⟨[(1, [1, 0, 0])]⟩ : PolynomialCode).eval [4] = 4 := by decide

end PolynomialCode

end Hilbert10


/- Source: Hilbert10.PolynomialCodeInt, Hilbert10 v2.3.0, Apache-2.0. -/
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# Evaluating an encoded polynomial at an integer assignment

Issue #28, first piece. The wire format's `eval` takes a *natural* assignment, because that is
what the natural-root problem needs. Hilbert asked about integer solutions, so the same code has
to be readable at an integer assignment too.

## The same recursion, one type up

`evalMonomialInt` and `evalInt` mirror `evalMonomial` and `eval` exactly: same shape, same
out-of-range convention (variables past the end of the assignment are `0`), same permissiveness.
Only the assignment's type changes. That is deliberate — the two evaluations agree on natural
assignments, `evalInt_map_natCast`, which is what lets the two solvability predicates be compared
rather than merely coexist.

## Computability is not proved here

`primrec₂_eval` exists because `NatSolvable`'s recursive enumerability needs it. The integer
analogue has no consumer: `rePred_intSolvable` is proved from `IntSolvable ≤₀ NatSolvable` and
recursive enumerability of the natural version, since recursive enumerability transfers along
many-one reductions (`REPred.of_manyOneReducible`). If some later step does need
`Primrec₂ evalInt`, it should be added then — the sign handling it requires is real work, and
speculative work here is exactly what #28 says to avoid.

## Main results

* `Hilbert10.PolynomialCode.evalInt`
* `Hilbert10.PolynomialCode.evalInt_map_natCast` — the two evaluations agree under the cast
-/

namespace Hilbert10

namespace PolynomialCode

/-- The value of a monomial at an integer assignment, by structural recursion on the exponent
vector and the assignment in parallel. Variables past the end of the assignment are taken to be
`0`, exactly as in `evalMonomial`. -/
def evalMonomialInt : MonomialCode → List ℤ → ℤ
  | [], _ => 1
  | e :: es, [] => (0 : ℤ) ^ e * evalMonomialInt es []
  | e :: es, v :: vs => v ^ e * evalMonomialInt es vs

/-- The value of an encoded polynomial at an integer assignment. -/
def evalInt (p : PolynomialCode) (x : List ℤ) : ℤ :=
  (p.terms.map fun t => t.1 * evalMonomialInt t.2 x).sum

@[simp] theorem evalMonomialInt_nil (x : List ℤ) : evalMonomialInt [] x = 1 := rfl

@[simp] theorem evalInt_mk_nil (x : List ℤ) : evalInt ⟨[]⟩ x = 0 := rfl

@[simp] theorem evalInt_mk_cons (t : ℤ × MonomialCode) (ts : List (ℤ × MonomialCode))
    (x : List ℤ) :
    evalInt ⟨t :: ts⟩ x = t.1 * evalMonomialInt t.2 x + evalInt ⟨ts⟩ x := by
  simp [evalInt]

/-! ### Agreement with the natural evaluation -/

theorem evalMonomialInt_map_natCast :
    ∀ (m : MonomialCode) (x : List ℕ),
      evalMonomialInt m (x.map (Nat.cast : ℕ → ℤ)) = evalMonomial m x
  | [], _ => rfl
  | _ :: es, [] => by
    have ih : evalMonomialInt es [] = evalMonomial es [] := by
      simpa using evalMonomialInt_map_natCast es []
    simp only [List.map_nil, evalMonomialInt, evalMonomial, ih]
  | _ :: es, v :: vs => by
    simp only [List.map_cons, evalMonomialInt, evalMonomial,
      evalMonomialInt_map_natCast es vs]

/-- **The two evaluations agree on natural assignments.** This is what makes the natural and
integer formulations comparable: a natural root is an integer root of the same code. -/
theorem evalInt_map_natCast (p : PolynomialCode) (x : List ℕ) :
    evalInt p (x.map (Nat.cast : ℕ → ℤ)) = eval p x := by
  simp only [evalInt, eval, evalMonomialInt_map_natCast]


/-! ### Normalising an integer assignment

The two solvability predicates quantify over arbitrary-length lists, while a block layout needs a
fixed length. These are the integer analogues of the natural-root padding lemmas, added because
the difference substitution consumes them — nothing more general. -/

theorem evalMonomialInt_append_zeros (e : MonomialCode) (x z : List ℤ) (hz : ∀ v ∈ z, v = 0) :
    evalMonomialInt e (x ++ z) = evalMonomialInt e x := by
  induction e generalizing x z with
  | nil => rfl
  | cons a es ih =>
    cases x with
    | nil =>
      cases z with
      | nil => rfl
      | cons c cs =>
        obtain rfl : c = 0 := hz c (by simp)
        have hrec : evalMonomialInt es cs = evalMonomialInt es [] := by
          simpa using ih [] cs fun v hv => hz v (by simp [hv])
        simp [evalMonomialInt, hrec]
    | cons v vs =>
      simp only [List.cons_append, evalMonomialInt]
      rw [ih vs z hz]

theorem evalInt_append_zeros (p : PolynomialCode) (x z : List ℤ) (hz : ∀ v ∈ z, v = 0) :
    p.evalInt (x ++ z) = p.evalInt x := by
  simp only [evalInt]
  congr 1
  exact List.map_congr_left fun t _ => by rw [evalMonomialInt_append_zeros t.2 x z hz]

theorem evalInt_append_replicate_zero (p : PolynomialCode) (x : List ℤ) (k : ℕ) :
    p.evalInt (x ++ List.replicate k 0) = p.evalInt x :=
  p.evalInt_append_zeros x _ fun _ hv => List.eq_of_mem_replicate hv

theorem evalMonomialInt_append_of_length_le {e : MonomialCode} {x : List ℤ}
    (h : e.length ≤ x.length) (y : List ℤ) :
    evalMonomialInt e (x ++ y) = evalMonomialInt e x := by
  induction e generalizing x with
  | nil => rfl
  | cons a es ih =>
    cases x with
    | nil => simp at h
    | cons v vs =>
      simp only [List.cons_append, evalMonomialInt]
      rw [ih (by simpa using h)]

theorem evalInt_append_of_arity_le {p : PolynomialCode} {x : List ℤ} (h : p.arity ≤ x.length)
    (y : List ℤ) : p.evalInt (x ++ y) = p.evalInt x := by
  simp only [evalInt]
  congr 1
  exact List.map_congr_left fun t ht => by
    rw [evalMonomialInt_append_of_length_le (Nat.le_trans (length_le_arity ht) h)]

/-- **Every integer assignment normalises to any length at least the arity.** Pad with zeros,
then truncate; both steps are invisible to the value. -/
theorem exists_length_eq_evalInt_eq (p : PolynomialCode) (x : List ℤ) {m : ℕ}
    (hm : p.arity ≤ m) : ∃ y : List ℤ, y.length = m ∧ p.evalInt y = p.evalInt x := by
  refine ⟨(x ++ List.replicate m 0).take m, ?_, ?_⟩
  · simp only [List.length_take, List.length_append, List.length_replicate]
    omega
  · have hsplit : (x ++ List.replicate m 0)
        = (x ++ List.replicate m 0).take m ++ (x ++ List.replicate m 0).drop m := by
      simp
    have hlen : p.arity ≤ ((x ++ List.replicate m 0).take m).length := by
      simp only [List.length_take, List.length_append, List.length_replicate]
      omega
    calc p.evalInt ((x ++ List.replicate m 0).take m)
        = p.evalInt ((x ++ List.replicate m 0).take m ++ (x ++ List.replicate m 0).drop m) :=
          (evalInt_append_of_arity_le hlen _).symm
      _ = p.evalInt (x ++ List.replicate m 0) := by rw [← hsplit]
      _ = p.evalInt x := evalInt_append_replicate_zero p x _

/-- The special case used by the difference substitution. -/
theorem exists_length_eq_arity_evalInt_eq (p : PolynomialCode) (x : List ℤ) :
    ∃ y : List ℤ, y.length = p.arity ∧ p.evalInt y = p.evalInt x :=
  exists_length_eq_evalInt_eq p x (Nat.le_refl _)

end PolynomialCode

end Hilbert10


/- Source: Hilbert10.PolynomialCodeDenote, Hilbert10 v2.3.0, Apache-2.0. -/
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# The wire format denotes a multivariate polynomial

Issue #10. This is the semantic anchor for `PolynomialCode`: it is what makes the encoding
a *representation of a polynomial* rather than an arbitrary evaluator, and it is what #11
states its contract against.

## Main results

* `denote`: the `MvPolynomial ℕ ℤ` denoted by a code.
* `evalInt_denote`, `eval_denote`: evaluating the denotation agrees with `evalInt` and with
  `eval`, for **every** assignment list, under the same zero-default convention both use. The
  integer statement is the primary one, since the denotation has integer coefficients; the
  natural one is its restriction along the cast.
* `evalInt_eq_of_denote_eq`, `eval_eq_of_denote_eq`: codes with the same denotation evaluate
  alike, which is what makes the permissive format harmless — duplicate terms and trailing
  zero exponents change the code but not the denotation.
* `denote_singleton`, `denote_append`: #11 needs algebraic equality of denotations, not
  merely agreement of evaluations, so the compositional structure is exposed.
* `vars_denote_subset`: `p.denote.vars ⊆ Finset.range p.arity`, an **upper bound only** —
  `arity` is a presentation bound and no minimality holds for a permissive format.

## Implementation notes

Monomial denotation mirrors `evalMonomial` structurally, threading the variable index
through the recursion. That keeps the evaluation proof a straightforward induction and
makes the treatment of trailing zero exponents visible: a trailing `0` contributes
`X i ^ 0 = 1`, so it changes the denotation not at all while still counting towards
`arity`.

Nothing here normalizes. Duplicate monomials denote as a genuine repeated sum, which is
equal — not merely equivalent — to the combined term, because addition in `MvPolynomial`
does the combining.

No computability results: that is #9, and it deliberately does not depend on this file.
-/

namespace Hilbert10

namespace PolynomialCode

open MvPolynomial

-- `MvPolynomial` is noncomputable, and `PolynomialCode.eval` shadows `MvPolynomial.eval`
-- inside this namespace, so the latter is always written out in full below.
noncomputable section

/-- Denotation of an exponent vector whose first entry refers to variable `i`. -/
private def denoteMonomialFrom : ℕ → MonomialCode → MvPolynomial ℕ ℤ
  | _, [] => 1
  | i, e :: es => X i ^ e * denoteMonomialFrom (i + 1) es

/-- The monomial denoted by an exponent vector: the `i`-th entry is the exponent of
variable `i`. -/
def denoteMonomial (e : MonomialCode) : MvPolynomial ℕ ℤ := denoteMonomialFrom 0 e

/-- The multivariate integer polynomial denoted by a code. -/
def denote (p : PolynomialCode) : MvPolynomial ℕ ℤ :=
  (p.terms.map fun t => C t.1 * denoteMonomial t.2).sum

/-! ### Compositional structure

Exposed because #11 needs to prove an equality of denotations, which is done by induction
over the term list rather than by comparing evaluations.
-/

@[simp] theorem denote_nil : (⟨[]⟩ : PolynomialCode).denote = 0 := rfl

theorem denote_singleton (c : ℤ) (e : MonomialCode) :
    (⟨[(c, e)]⟩ : PolynomialCode).denote = C c * denoteMonomial e := by
  simp [denote]

theorem denote_cons (t : ℤ × MonomialCode) (ts : List (ℤ × MonomialCode)) :
    (⟨t :: ts⟩ : PolynomialCode).denote =
      C t.1 * denoteMonomial t.2 + (⟨ts⟩ : PolynomialCode).denote := by
  simp [denote]

theorem denote_append (s t : List (ℤ × MonomialCode)) :
    (⟨s ++ t⟩ : PolynomialCode).denote =
      (⟨s⟩ : PolynomialCode).denote + (⟨t⟩ : PolynomialCode).denote := by
  simp [denote, List.map_append, List.sum_append]

/-! ### No normalization

Two consequences of denoting structurally, stated rather than left implicit: trailing zero
exponents contribute nothing, and duplicate terms denote as a genuine repeated sum whose
value is *equal* to the combined term — addition in `MvPolynomial` does the combining, so
no normalization step is needed anywhere.
-/

private theorem denoteMonomialFrom_replicate_zero (i k : ℕ) :
    denoteMonomialFrom i (List.replicate k 0) = 1 := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, denoteMonomialFrom, ih]

private theorem denoteMonomialFrom_append_replicate_zero (e : MonomialCode) (i k : ℕ) :
    denoteMonomialFrom i (e ++ List.replicate k 0) = denoteMonomialFrom i e := by
  induction e generalizing i with
  | nil =>
    rw [List.nil_append]
    exact (denoteMonomialFrom_replicate_zero i k).trans rfl
  | cons a es ih => simp [denoteMonomialFrom, ih]

/-- An all-zero exponent vector denotes `1`. -/
@[simp] theorem denoteMonomial_replicate_zero (k : ℕ) :
    denoteMonomial (List.replicate k 0) = 1 :=
  denoteMonomialFrom_replicate_zero 0 k

/-- Trailing zero exponents do not change a denotation, though they do inflate `arity`. -/
theorem denoteMonomial_append_replicate_zero (e : MonomialCode) (k : ℕ) :
    denoteMonomial (e ++ List.replicate k 0) = denoteMonomial e :=
  denoteMonomialFrom_append_replicate_zero e 0 k

/-- Duplicate terms need no normalization: two copies of a term denote the same polynomial
as the single term with the coefficients added. -/
theorem denote_duplicate (c d : ℤ) (e : MonomialCode) :
    (⟨[(c, e), (d, e)]⟩ : PolynomialCode).denote = (⟨[(c + d, e)]⟩ : PolynomialCode).denote := by
  simp only [denote, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, map_add]
  ring

-- Regression tests for the two claims above. Note the trailing-zero lemma applies in the
-- `e ++ List.replicate k 0` form, which is how padding arises; a *literal* exponent list
-- like `[1, 0, 0]` is normalized by the elaborator before any rewrite can match it, so
-- state it as an append.
example : denoteMonomial ([1] ++ List.replicate 2 0) = denoteMonomial [1] :=
  denoteMonomial_append_replicate_zero [1] 2

example (e : MonomialCode) :
    (⟨[(1, e), (1, e)]⟩ : PolynomialCode).denote = (⟨[(2, e)]⟩ : PolynomialCode).denote := by
  simpa using denote_duplicate 1 1 e

/-- Incrementing the exponent at index `k` multiplies the monomial by `X k`. Sound only
when the exponent vector is long enough to reach `k`: `List.set` past the end is silently a
no-op. Used by #11, where every exponent vector is padded to a fixed length. -/
theorem denoteMonomial_set :
    ∀ (e : MonomialCode) (k : ℕ), k < e.length →
      denoteMonomial (e.set k (e.getD k 0 + 1)) = denoteMonomial e * X k := by
  have aux : ∀ (e : MonomialCode) (i k : ℕ), k < e.length →
      denoteMonomialFrom i (e.set k (e.getD k 0 + 1)) =
        denoteMonomialFrom i e * X (i + k) := by
    intro e
    induction e with
    | nil => intro i k hk; simp at hk
    | cons a es ih =>
      intro i k hk
      cases k with
      | zero =>
        simp only [List.set_cons_zero, List.getD_cons_zero, denoteMonomialFrom, Nat.add_zero,
          pow_succ]
        ring
      | succ k =>
        have hk' : k < es.length := by simpa using hk
        simp only [List.set_cons_succ, List.getD_cons_succ, denoteMonomialFrom, ih (i + 1) k hk']
        have hi : i + 1 + k = i + (k + 1) := by omega
        rw [hi]
        ring
  intro e k hk
  simpa [denoteMonomial] using aux e 0 k hk

/-! ### Evaluation

The integer evaluation is the one proved by induction: the denotation has integer coefficients,
so an integer assignment is its natural argument. The natural evaluation then agrees because it
is the integer one restricted along the cast (`evalInt_map_natCast`). -/

private theorem evalInt_denoteMonomialFrom (x : List ℤ) :
    ∀ (e : MonomialCode) (i : ℕ),
      MvPolynomial.eval (fun j => x.getD j 0) (denoteMonomialFrom i e) =
        evalMonomialInt e (x.drop i) := by
  intro e
  induction e with
  | nil => intro i; simp [denoteMonomialFrom]
  | cons a es ih =>
    intro i
    simp only [denoteMonomialFrom, map_mul, map_pow, eval_X, ih]
    by_cases hi : i < x.length
    · rw [List.drop_eq_getElem_cons hi]
      simp only [evalMonomialInt, List.getD_eq_getElem _ _ hi]
    · have hnil : x.drop i = [] := List.drop_eq_nil_of_le (le_of_not_gt hi)
      have hnil' : x.drop (i + 1) = [] := List.drop_eq_nil_of_le (by omega)
      rw [hnil, hnil', List.getD_eq_default _ _ (le_of_not_gt hi)]
      simp only [evalMonomialInt]

/-- **Evaluating the denotation agrees with `evalInt`**, for every integer assignment list.
Variables past the end of the list are read as `0` on both sides. -/
theorem evalInt_denote (p : PolynomialCode) (x : List ℤ) :
    MvPolynomial.eval (fun i => x.getD i 0) p.denote = p.evalInt x := by
  simp only [denote, evalInt]
  induction p.terms with
  | nil => simp
  | cons t ts ih =>
    simp only [List.map_cons, List.sum_cons, map_add, map_mul, eval_C, ih]
    rw [denoteMonomial, evalInt_denoteMonomialFrom x t.2 0, List.drop_zero]

/-- **Evaluating the denotation agrees with `eval`**, for every natural assignment list: the
integer statement, restricted along the cast. -/
theorem eval_denote (p : PolynomialCode) (x : List ℕ) :
    MvPolynomial.eval (fun i => ((x.getD i 0 : ℕ) : ℤ)) p.denote = p.eval x := by
  have hx : (fun i => ((x.getD i 0 : ℕ) : ℤ)) = fun i => (x.map (Nat.cast : ℕ → ℤ)).getD i 0 := by
    funext i
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases x[i]? <;> simp
  rw [← evalInt_map_natCast, ← evalInt_denote, hx]

/-! ### Only the denotation matters

The consequence the permissive format is entitled to: two codes that denote the same polynomial
evaluate alike, at every assignment. Duplicate terms (`denote_duplicate`) and trailing zero
exponents (`denoteMonomial_append_replicate_zero`) are the two ways the format lets codes
differ without their denotations differing. -/

/-- Codes with the same denotation take the same integer values. -/
theorem evalInt_eq_of_denote_eq {p q : PolynomialCode} (h : p.denote = q.denote) (x : List ℤ) :
    p.evalInt x = q.evalInt x := by
  rw [← evalInt_denote, ← evalInt_denote, h]

/-- Codes with the same denotation take the same natural values. -/
theorem eval_eq_of_denote_eq {p q : PolynomialCode} (h : p.denote = q.denote) (x : List ℕ) :
    p.eval x = q.eval x := by
  rw [← eval_denote, ← eval_denote, h]

/-! ### Total degree

The sum of a monomial's exponents bounds the total degree of its denotation (with equality, but
the bound is what the degree accounting in `Degree.lean` consumes). -/

private theorem totalDegree_denoteMonomialFrom_le (e : MonomialCode) (i : ℕ) :
    (denoteMonomialFrom i e).totalDegree ≤ e.sum := by
  induction e generalizing i with
  | nil => simp [denoteMonomialFrom]
  | cons a es ih =>
    simp only [denoteMonomialFrom, List.sum_cons]
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_X_pow]
    exact Nat.add_le_add_left (ih (i + 1)) a

/-- The total degree of a monomial's denotation is at most the sum of its exponents. -/
theorem totalDegree_denoteMonomial_le (e : MonomialCode) :
    (denoteMonomial e).totalDegree ≤ e.sum :=
  totalDegree_denoteMonomialFrom_le e 0

/-! ### Variables

An upper bound only. `arity` is the maximum exponent-vector length, so trailing zero
exponents inflate it; no minimal-arity statement is true for a permissive encoding.
-/

private theorem vars_denoteMonomialFrom (e : MonomialCode) (i : ℕ) :
    (denoteMonomialFrom i e).vars ⊆ Finset.range (i + e.length) := by
  induction e generalizing i with
  | nil => simp [denoteMonomialFrom]
  | cons a es ih =>
    classical
    refine (vars_mul _ _).trans ?_
    refine Finset.union_subset ?_ ?_
    · refine (vars_pow _ _).trans ?_
      rw [vars_X]
      intro j hj
      simp only [Finset.mem_singleton] at hj
      simp [hj]
    · refine (ih (i + 1)).trans ?_
      simp only [List.length_cons]
      intro j hj
      simp only [Finset.mem_range] at hj ⊢
      omega

theorem vars_denoteMonomial (e : MonomialCode) :
    (denoteMonomial e).vars ⊆ Finset.range e.length := by
  have h := vars_denoteMonomialFrom e 0
  simpa [denoteMonomial] using h

private theorem vars_sum_subset_of_le (n : ℕ) :
    ∀ ts : List (ℤ × MonomialCode), (∀ t ∈ ts, t.2.length ≤ n) →
      (ts.map fun t : ℤ × MonomialCode => C t.1 * denoteMonomial t.2).sum.vars ⊆
        Finset.range n := by
  classical
  intro ts
  induction ts with
  | nil => intro _; simp
  | cons t ts ih =>
    intro hts
    simp only [List.map_cons, List.sum_cons]
    refine (vars_add_subset _ _).trans (Finset.union_subset ?_ ?_)
    · refine (vars_mul _ _).trans (Finset.union_subset ?_ ?_)
      · simp only [vars_C]
        exact Finset.empty_subset _
      · exact (vars_denoteMonomial t.2).trans
          (Finset.range_mono (hts t (List.mem_cons_self ..)))
    · exact ih fun s hs => hts s (List.mem_cons_of_mem _ hs)

/-- The variables of a denotation are bounded by the arity. This is an **upper bound only**:
`arity` counts trailing zero exponents, which contribute no variables. -/
theorem vars_denote_subset (p : PolynomialCode) :
    p.denote.vars ⊆ Finset.range p.arity :=
  vars_sum_subset_of_le p.arity p.terms fun _ ht => length_le_arity ht

end

end PolynomialCode

end Hilbert10


/- Source: Hilbert10.ExistsCode, Hilbert10 v2.3.0, Apache-2.0. -/
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# Every finite-arity polynomial has a code

Issue #11, core half. This module imports only #10, so its independence from the
`Poly`/`MvPolynomial` bridge is a fact about the Lean module graph and not merely a claim
in prose. The `RepresentsNat` corollary, which does need #5, lives in
`Hilbert10/ExistsCodeRepresents.lean`.

## The variable contract

Inputs are variables `0, …, n-1` and witnesses are variables `n, …, n+m-1`, contiguously
and in that order. That is exactly

```lean
Sum.elim (fun i : Fin n => i.val) (fun j : Fin m => n + j.val)
```

which is `varIndex` below. Every later milestone assumes this ordering, so it is stated
once, as a definition, and never re-derived.

## Implementation notes

The contract is an equality of *denotations*, not agreement of evaluations; the evaluation
corollary is derived from it via `eval_denote` and `MvPolynomial.eval_rename`.

Codes are built by induction on the polynomial with every exponent vector of length exactly
`n + m`. The fixed length is what makes multiplication by a variable well defined as
`List.set` at the variable's index: with ragged vectors `List.set` past the end is silently
a no-op, which would be a soundness bug rather than an inconvenience.
-/

namespace Hilbert10

namespace PolynomialCode

open MvPolynomial

variable {n m : ℕ}

/-- The variable-index contract: inputs first, then witnesses, contiguously. -/
def varIndex (n m : ℕ) : Fin n ⊕ Fin m → ℕ :=
  Sum.elim (fun i : Fin n => i.val) (fun j : Fin m => n + j.val)

/-- The contract, expressed through `finSumFinEquiv`. Injectivity and the bound are read
off from the equivalence, but every downstream statement is phrased in terms of `varIndex`
itself. -/
theorem varIndex_eq (n m : ℕ) : varIndex n m = fun v => ((finSumFinEquiv v : Fin (n + m)) : ℕ) := by
  funext v
  cases v <;> simp [varIndex]

theorem varIndex_lt (v : Fin n ⊕ Fin m) : varIndex n m v < n + m := by
  rw [varIndex_eq]
  exact (finSumFinEquiv v).isLt

theorem varIndex_injective : Function.Injective (varIndex n m) := by
  rw [varIndex_eq]
  exact Fin.val_injective.comp finSumFinEquiv.injective

/-! ### Multiplying a code by a variable -/

/-- Multiply a code by the variable `k`, by incrementing the exponent at index `k` in every
term. Sound only when every exponent vector is long enough to reach `k`; see
`denote_mulX`. -/
private def mulX (k : ℕ) (q : PolynomialCode) : PolynomialCode :=
  ⟨q.terms.map fun t => (t.1, t.2.set k (t.2.getD k 0 + 1))⟩

private theorem denote_mulX_aux (k : ℕ) :
    ∀ ts : List (ℤ × MonomialCode), (∀ t ∈ ts, k < t.2.length) →
      (ts.map fun t : ℤ × MonomialCode =>
          C t.1 * denoteMonomial (t.2.set k (t.2.getD k 0 + 1))).sum =
        (ts.map fun t : ℤ × MonomialCode => C t.1 * denoteMonomial t.2).sum * X k := by
  intro ts
  induction ts with
  | nil => intro _; simp
  | cons t ts ih =>
    intro hts
    simp only [List.map_cons, List.sum_cons]
    rw [ih fun s hs => hts s (List.mem_cons_of_mem _ hs),
      denoteMonomial_set t.2 k (hts t (List.mem_cons_self ..))]
    ring

private theorem denote_mulX {k : ℕ} {q : PolynomialCode}
    (hq : ∀ t ∈ q.terms, k < t.2.length) : (mulX k q).denote = q.denote * X k := by
  simp only [mulX, denote, List.map_map]
  exact denote_mulX_aux k q.terms hq

private theorem length_mem_mulX {k : ℕ} {q : PolynomialCode} {N : ℕ}
    (hq : ∀ t ∈ q.terms, t.2.length = N) :
    ∀ t ∈ (mulX k q).terms, t.2.length = N := by
  simp only [mulX]
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  simpa using hq s hs

/-! ### The coding theorem -/

/-- Every polynomial in `n` input and `m` witness variables has a code, whose denotation is
literally the renaming of that polynomial along the variable contract.

The auxiliary conclusion — that every exponent vector has length exactly `n + m` — is what
makes the induction go through; `arity ≤ n + m` follows. -/
private theorem exists_code_aux (p : MvPolynomial (Fin n ⊕ Fin m) ℤ) :
    ∃ q : PolynomialCode, (∀ t ∈ q.terms, t.2.length = n + m) ∧
      q.denote = rename (varIndex n m) p := by
  induction p using MvPolynomial.induction_on with
  | C r =>
    refine ⟨⟨[(r, List.replicate (n + m) 0)]⟩, ?_, ?_⟩
    · intro t ht
      simp only [List.mem_singleton] at ht
      simp [ht]
    · rw [denote_singleton, denoteMonomial_replicate_zero, mul_one, rename_C]
  | add p₁ p₂ h₁ h₂ =>
    obtain ⟨q₁, hlen₁, hden₁⟩ := h₁
    obtain ⟨q₂, hlen₂, hden₂⟩ := h₂
    refine ⟨⟨q₁.terms ++ q₂.terms⟩, ?_, ?_⟩
    · intro t ht
      rcases List.mem_append.mp ht with h | h
      · exact hlen₁ t h
      · exact hlen₂ t h
    · rw [denote_append, map_add, hden₁, hden₂]
  | mul_X p v h =>
    obtain ⟨q, hlen, hden⟩ := h
    refine ⟨mulX (varIndex n m v) q, length_mem_mulX hlen, ?_⟩
    rw [denote_mulX fun t ht => by rw [hlen t ht]; exact varIndex_lt v, hden, map_mul, rename_X]

/-- **Every finite-arity polynomial has a code.** The contract is denotation equality, not
evaluation agreement. -/
theorem exists_code (p : MvPolynomial (Fin n ⊕ Fin m) ℤ) :
    ∃ q : PolynomialCode, q.arity ≤ n + m ∧ q.denote = rename (varIndex n m) p := by
  obtain ⟨q, hlen, hden⟩ := exists_code_aux p
  refine ⟨q, ?_, hden⟩
  simp only [arity]
  have aux : ∀ ts : List (ℤ × MonomialCode), (∀ t ∈ ts, t.2.length = n + m) →
      (ts.map fun t : ℤ × MonomialCode => t.2.length).foldr max 0 ≤ n + m := by
    intro ts
    induction ts with
    | nil => intro _; simp
    | cons t ts ih =>
      intro hts
      simp only [List.map_cons, List.foldr_cons]
      exact max_le (le_of_eq (hts t (List.mem_cons_self ..)))
        (ih fun s hs => hts s (List.mem_cons_of_mem _ hs))
  exact aux q.terms hlen

/-! ### Evaluation

Derived from the denotation contract, rather than proved separately by pointwise reasoning.
-/

private theorem getD_ofFn_append (x : Fin n → ℕ) (y : Fin m → ℕ) (v : Fin n ⊕ Fin m) :
    (List.ofFn x ++ List.ofFn y).getD (varIndex n m v) 0 = Sum.elim x y v := by
  cases v with
  | inl i =>
    have hi : varIndex n m (Sum.inl i) = (i : ℕ) := rfl
    rw [hi, List.getD_append _ _ _ _ (by simp)]
    rw [List.getD_eq_getElem _ _ (by simp)]
    simp
  | inr j =>
    have hj : varIndex n m (Sum.inr j) = n + (j : ℕ) := rfl
    rw [hj, List.getD_append_right _ _ _ _ (by simp)]
    rw [List.getD_eq_getElem _ _ (by simp)]
    simp

/-- Evaluating a code at inputs followed by witnesses agrees with evaluating the polynomial
it codes. Derived from the denotation contract via `eval_denote` and `eval_rename`, not by
pointwise reasoning about the code. -/
theorem eval_exists_code {p : MvPolynomial (Fin n ⊕ Fin m) ℤ} {q : PolynomialCode}
    (hq : q.denote = rename (varIndex n m) p) (x : Fin n → ℕ) (y : Fin m → ℕ) :
    q.eval (List.ofFn x ++ List.ofFn y) =
      MvPolynomial.eval (Sum.elim (fun i => (x i : ℤ)) fun j => (y j : ℤ)) p := by
  have hassign :
      (fun i => (((List.ofFn x ++ List.ofFn y).getD i 0 : ℕ) : ℤ)) ∘ varIndex n m =
        Sum.elim (fun i => (x i : ℤ)) fun j => (y j : ℤ) := by
    funext v
    simp only [Function.comp_apply, getD_ofFn_append x y v]
    cases v <;> rfl
  rw [← eval_denote q (List.ofFn x ++ List.ofFn y), hq, eval_rename, hassign]

end PolynomialCode

end Hilbert10


/- Source: Hilbert10.ExistsCodeRepresents, Hilbert10 v2.3.0, Apache-2.0. -/
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# Coding a polynomial that represents a relation

Issue #11, compatibility half: the one statement that needs `RepresentsNat` from #5, kept
in its own module so that `Hilbert10.ExistsCode` genuinely does not depend on the
`Poly`/`MvPolynomial` bridge — a fact about the import graph, not a claim in prose. That
separation is why `ExistsCode` could be promoted (#50) while this module, which needs the
staged `PolyBridge`, could not.
-/

namespace Hilbert10

namespace PolynomialCode

open MvPolynomial

variable {n m : ℕ}

/-- If a polynomial represents a relation, some code has that relation as its natural-root
condition, with inputs in the first `n` slots and witnesses in the next `m`. -/
theorem exists_code_representsNat {R : (Fin n → ℕ) → Prop}
    {p : MvPolynomial (Fin n ⊕ Fin m) ℤ} (hp : RepresentsNat p R) :
    ∃ q : PolynomialCode, q.arity ≤ n + m ∧
      ∀ x : Fin n → ℕ, R x ↔ ∃ y : Fin m → ℕ, q.eval (List.ofFn x ++ List.ofFn y) = 0 := by
  obtain ⟨q, harity, hden⟩ := exists_code p
  refine ⟨q, harity, fun x => ?_⟩
  rw [hp x]
  exact exists_congr fun y => by rw [eval_exists_code hden x y]

end PolynomialCode

end Hilbert10


/- Source: Hilbert10.PolynomialCodePrimcodable, Hilbert10 v2.3.0, Apache-2.0. -/
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# The encoding contract of the wire format

Issue #9, first half. `PolynomialCode` is a one-field structure over `List (ℤ × List ℕ)`, so
its `Primcodable` instance is transported along an explicit equivalence rather than built by
hand. Computability of the constructor, of the `terms` projection and of `arity` follows
immediately, so no later proof ever has to unfold the encoding.

Split out from `PolynomialCodeComp` for a boundary reason. Computability of `eval` needs
`Primrec` lemmas about `ℤ` that the pinned mathlib does not have (#36); the *encoding* needs
none of them, because `Primcodable ℤ` itself is already in mathlib and only the lemmas are
missing. Keeping the two apart means the input type of Hilbert's tenth problem carries its
`Primcodable` contract without depending on a local mathlib shim.
-/

namespace Hilbert10

namespace PolynomialCode

/-- A `PolynomialCode` is exactly its list of terms. -/
def equivTerms : PolynomialCode ≃ List (ℤ × MonomialCode) where
  toFun := terms
  invFun := mk
  left_inv := fun ⟨_⟩ => rfl
  right_inv := fun _ => rfl

instance : Primcodable PolynomialCode := Primcodable.ofEquiv _ equivTerms

/-- The `terms` projection is primitive recursive. Downstream proofs use this rather than
unfolding the encoding. -/
theorem primrec_terms : Primrec terms :=
  Primrec.of_equiv (e := equivTerms)

/-- The constructor is primitive recursive. -/
theorem primrec_mk : Primrec mk :=
  Primrec.of_equiv_symm (e := equivTerms)

/-! ### Arity -/

theorem arity_eq_foldr (p : PolynomialCode) :
    p.arity = p.terms.foldr (fun t acc => max t.2.length acc) 0 := by
  simp only [arity]
  induction p.terms with
  | nil => rfl
  | cons s ss ih => simp [ih]

theorem primrec_arity : Primrec arity := by
  have hstep : Primrec₂ fun (_ : PolynomialCode) (q : (ℤ × MonomialCode) × ℕ) =>
      max q.1.2.length q.2 :=
    Primrec.nat_max.comp
      (Primrec.list_length.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp Primrec.snd)
  have h := Primrec.list_foldr (f := fun p : PolynomialCode => p.terms)
    (g := fun _ : PolynomialCode => (0 : ℕ))
    (h := fun _ q => max q.1.2.length q.2) primrec_terms (Primrec.const 0) hstep
  exact h.of_eq fun p => (arity_eq_foldr p).symm

end PolynomialCode

end Hilbert10


/- Source: Hilbert10.Internal.ForMathlib.PrimrecInt, Hilbert10 v2.3.0, Apache-2.0. -/
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# Integers are primitive recursive

Issue #36, destined for `Mathlib/Computability/Primrec/Int.lean`. At the pinned mathlib
revision the computability library exposes no lemmas about `ℤ` at all — no `Primrec`, no
`Computable`, for any integer operation. `Primcodable ℤ` exists only because
`Denumerable ℤ` does.

## Main results

* `Primrec.intEquivNatSumNat` / `Primrec.intEquivNatSumNat_symm`: the sign-case view
  `ℤ ≃ ℕ ⊕ ℕ` is primitive recursive in both directions.
* `Primrec.int_natAbs`, `Primrec.int_toNat`, `Primrec.int_nonneg`, `Primrec.int_natCast`,
  `Primrec.int_subNat`.

## Implementation notes

`Primcodable ℤ` encodes through `Equiv.intEquivNat = intEquivNatSumNat.trans
natSumNatEquivNat`, and `Equiv.natSumNatEquivNat_apply` is `Sum.elim (2 * ·) (2 * · + 1)`.
`Encodable.encodeSum` is `2 * encode ·` / `2 * encode · + 1`. These are the same function,
so the two encodings agree definitionally and the sign-case view is primitive recursive by
`cases z <;> rfl`. Everything else is a `Primrec.sumCasesOn` over that.

Only what is needed downstream is proved. The full integer ring API — `Int.add`, `Int.mul`
and friends — is each a further sign case analysis, and should be added when something
requires it.
-/

namespace Primrec

/-- Viewing an integer by its sign case is primitive recursive. -/
theorem intEquivNatSumNat : Primrec (Equiv.intEquivNatSumNat) := by
  have h : ∀ z : ℤ, Encodable.encode (Equiv.intEquivNatSumNat z) = Encodable.encode z := by
    intro z
    cases z <;> rfl
  exact Primrec.encode_iff.mp (Primrec.encode.of_eq fun z => (h z).symm)

/-- Rebuilding an integer from its sign case is primitive recursive. -/
theorem intEquivNatSumNat_symm : Primrec (Equiv.intEquivNatSumNat.symm) := by
  have h : ∀ s : ℕ ⊕ ℕ,
      Encodable.encode (Equiv.intEquivNatSumNat.symm s) = Encodable.encode s := by
    rintro (m | n) <;> rfl
  exact Primrec.encode_iff.mp (Primrec.encode.of_eq fun s => (h s).symm)

/-- `Int.natAbs` is primitive recursive. -/
theorem int_natAbs : Primrec Int.natAbs := by
  have h := Primrec.sumCasesOn intEquivNatSumNat
    (g := fun _ (m : ℕ) => m) (h := fun _ (n : ℕ) => n + 1)
    Primrec.snd (Primrec.succ.comp Primrec.snd)
  exact h.of_eq fun z => by cases z <;> rfl

/-- `Int.toNat` is primitive recursive. -/
theorem int_toNat : Primrec Int.toNat := by
  have h := Primrec.sumCasesOn intEquivNatSumNat
    (g := fun _ (m : ℕ) => m) (h := fun _ (_ : ℕ) => 0)
    Primrec.snd (Primrec.const 0)
  exact h.of_eq fun z => by cases z <;> rfl

/-- Nonnegativity of an integer is a primitive recursive predicate. -/
theorem int_nonneg : PrimrecPred fun z : ℤ => 0 ≤ z := by
  refine primrecPred_iff_primrec_decide.mpr ?_
  have h := Primrec.sumCasesOn intEquivNatSumNat
    (g := fun _ (_ : ℕ) => true) (h := fun _ (_ : ℕ) => false)
    (Primrec.const true) (Primrec.const false)
  exact h.of_eq fun z => by cases z <;> rfl

/-- The cast `ℕ → ℤ` is primitive recursive. -/
theorem int_natCast : Primrec ((↑) : ℕ → ℤ) := by
  have h := intEquivNatSumNat_symm.comp (Primrec.sumInl (β := ℕ) (α := ℕ))
  exact h.of_eq fun n => rfl

/-- The difference of two natural numbers, valued in `ℤ`, is primitive recursive. Note the
result is a genuine integer difference, not truncated subtraction. -/
theorem int_subNat : Primrec₂ fun a b : ℕ => ((a : ℤ) - b) := by
  have h : Primrec fun q : ℕ × ℕ =>
      if q.2 ≤ q.1 then Equiv.intEquivNatSumNat.symm (Sum.inl (q.1 - q.2))
      else Equiv.intEquivNatSumNat.symm (Sum.inr (q.2 - q.1 - 1)) := by
    refine Primrec.ite (Primrec.nat_le.comp Primrec.snd Primrec.fst) ?_ ?_
    · exact intEquivNatSumNat_symm.comp
        (Primrec.sumInl.comp (Primrec.nat_sub.comp Primrec.fst Primrec.snd))
    · exact intEquivNatSumNat_symm.comp
        (Primrec.sumInr.comp
          (Primrec.nat_sub.comp (Primrec.nat_sub.comp Primrec.snd Primrec.fst)
            (Primrec.const 1)))
  refine h.of_eq fun q => ?_
  obtain ⟨a, b⟩ := q
  by_cases hba : b ≤ a
  · simp only [hba, if_true]
    change (((a - b : ℕ) : ℤ)) = ((a : ℤ) - b)
    omega
  · simp only [hba, if_false]
    change Int.negSucc (b - a - 1) = ((a : ℤ) - b)
    rw [Int.negSucc_eq]
    omega

/-- Integer negation is primitive recursive. Written through the positive/negative parts, since
the shim's only integer primitive is `int_subNat`. -/
theorem int_neg : Primrec (fun z : ℤ => -z) := by
  have h : Primrec fun z : ℤ => ((z.natAbs - z.toNat : ℕ) : ℤ) - ((z.toNat : ℕ) : ℤ) :=
    Primrec₂.comp (f := fun a b : ℕ => ((a : ℤ) - b)) int_subNat
      (Primrec.nat_sub.comp int_natAbs int_toNat) int_toNat
  exact h.of_eq fun z => by omega

/-- Integer multiplication is primitive recursive. Every integer is `toNat - (natAbs - toNat)`,
so the product expands into four natural products. -/
theorem int_mul : Primrec₂ ((· * ·) : ℤ → ℤ → ℤ) := by
  have key : ∀ z w : ℤ, z * w
      = ((z.toNat * w.toNat + (z.natAbs - z.toNat) * (w.natAbs - w.toNat) : ℕ) : ℤ)
        - ((z.toNat * (w.natAbs - w.toNat) + (z.natAbs - z.toNat) * w.toNat : ℕ) : ℤ) := by
    intro z w
    set a := z.toNat with ha
    set b := z.natAbs - z.toNat with hb
    set c := w.toNat with hc
    set d := w.natAbs - w.toNat with hd
    have hz : z = (a : ℤ) - (b : ℤ) := by omega
    have hw : w = (c : ℤ) - (d : ℤ) := by omega
    rw [hz, hw]
    push_cast
    ring
  have h : Primrec fun q : ℤ × ℤ =>
      ((q.1.toNat * q.2.toNat + (q.1.natAbs - q.1.toNat) * (q.2.natAbs - q.2.toNat) : ℕ) : ℤ)
        - ((q.1.toNat * (q.2.natAbs - q.2.toNat)
            + (q.1.natAbs - q.1.toNat) * q.2.toNat : ℕ) : ℤ) := by
    have hpz : Primrec fun q : ℤ × ℤ => q.1.toNat := int_toNat.comp Primrec.fst
    have hmz : Primrec fun q : ℤ × ℤ => q.1.natAbs - q.1.toNat :=
      Primrec.nat_sub.comp (int_natAbs.comp Primrec.fst) (int_toNat.comp Primrec.fst)
    have hpw : Primrec fun q : ℤ × ℤ => q.2.toNat := int_toNat.comp Primrec.snd
    have hmw : Primrec fun q : ℤ × ℤ => q.2.natAbs - q.2.toNat :=
      Primrec.nat_sub.comp (int_natAbs.comp Primrec.snd) (int_toNat.comp Primrec.snd)
    exact Primrec₂.comp (f := fun a b : ℕ => ((a : ℤ) - b)) int_subNat
      (Primrec.nat_add.comp (Primrec.nat_mul.comp hpz hpw) (Primrec.nat_mul.comp hmz hmw))
      (Primrec.nat_add.comp (Primrec.nat_mul.comp hpz hmw) (Primrec.nat_mul.comp hmz hpw))
  exact h.of_eq fun q => (key q.1 q.2).symm

/-- Building a list of zeros is primitive recursive. -/
theorem list_replicate_zero : Primrec fun i : ℕ => List.replicate i (0 : ℕ) := by
  have h := Primrec.nat_rec' (f := fun i : ℕ => i) (g := fun _ : ℕ => ([] : List ℕ))
    (h := fun _ (q : ℕ × List ℕ) => 0 :: q.2) Primrec.id (Primrec.const ([] : List ℕ))
    (Primrec₂.comp Primrec.list_cons (Primrec.const 0) (Primrec.snd.comp Primrec.snd))
  refine h.of_eq fun i => ?_
  induction i with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, ← ih]

end Primrec




/- Source: Hilbert10.Internal.ForMathlib.PrimrecNat, Hilbert10 v2.3.0, Apache-2.0. -/
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# Natural-number exponentiation is primitive recursive

A companion one-liner to issue #36, kept in a separate file so the integer layer stays
exactly what it says it is.

`Mathlib/Computability/Primrec/Basic.lean` lifts `Nat.Primrec.add`, `.sub` and `.mul` to
`Primrec₂` as `Primrec.nat_add`, `Primrec.nat_sub`, `Primrec.nat_mul`, but never lifts
`Nat.Primrec.pow`, which is proved right beside them. This is that missing lemma.
-/

namespace Primrec

/-- Exponentiation of naturals is primitive recursive. -/
theorem nat_pow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) :=
  Primrec₂.unpaired'.1 Nat.Primrec.pow

end Primrec


/- Source: Hilbert10.PolynomialCodeComp, Hilbert10 v2.3.0, Apache-2.0. -/
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# Computability of evaluation

Issue #9, second half. The `Primcodable` contract and the primitive recursiveness of the
projections live in `PolynomialCodePrimcodable`; what remains here is `eval`, which is the
only part that needs anything about `ℤ`.

## Note on integers

`eval` is `ℤ`-valued, and at the pinned mathlib revision the computability library exposes
no lemmas about `ℤ` at all. That layer lives in
`Hilbert10/Internal/ForMathlib/PrimrecInt.lean` (issue #36), deliberately separate: it
is a mathlib gap rather than anything about this wire format, and it must not be allowed to
reshape `PolynomialCode` or `evalMonomial`.
-/

namespace Hilbert10

namespace PolynomialCode

/-! ### Evaluation

`eval` is `ℤ`-valued, but its integer content is thin: each coefficient splits as
`c = c.toNat - negPart c` with both parts natural, so `eval` is a difference of two
natural-valued sums. Computability then needs exactly one integer lemma,
`Primrec.int_subNat`, with the rest of the work over `ℕ`.

`natEvalMonomial`, `evalPos`, `evalNeg` and the decomposition are private: they are proof
scaffolding for `primrec₂_eval`, not API.
-/

/-- `evalMonomial`, valued in `ℕ`. Every monomial value is a product of natural powers, so
nothing is lost. -/
private def natEvalMonomial : MonomialCode → List ℕ → ℕ
  | [], _ => 1
  | e :: es, [] => 0 ^ e * natEvalMonomial es []
  | e :: es, v :: vs => v ^ e * natEvalMonomial es vs

private theorem evalMonomial_eq_cast (e : MonomialCode) (x : List ℕ) :
    evalMonomial e x = (natEvalMonomial e x : ℤ) := by
  induction e generalizing x with
  | nil => rfl
  | cons a es ih =>
    cases x with
    | nil => simp only [evalMonomial, natEvalMonomial, ih]; push_cast; ring
    | cons v vs => simp only [evalMonomial, natEvalMonomial, ih]; push_cast; ring

/-- The negative part of a coefficient, as a natural number. Written with `natAbs` and
`toNat` rather than `(-c).toNat` so that only lemmas already in `Internal/ForMathlib/PrimrecInt`
are needed. -/
private def negPart (c : ℤ) : ℕ := c.natAbs - c.toNat

private theorem int_eq_toNat_sub_negPart (c : ℤ) : c = (c.toNat : ℤ) - (negPart c : ℤ) := by
  unfold negPart
  omega

private def evalPos (p : PolynomialCode) (x : List ℕ) : ℕ :=
  (p.terms.map fun t => t.1.toNat * natEvalMonomial t.2 x).sum

private def evalNeg (p : PolynomialCode) (x : List ℕ) : ℕ :=
  (p.terms.map fun t => negPart t.1 * natEvalMonomial t.2 x).sum

private theorem term_eq (c : ℤ) (m : ℕ) :
    c * (m : ℤ) = ((c.toNat * m : ℕ) : ℤ) - ((negPart c * m : ℕ) : ℤ) := by
  push_cast
  conv_lhs => rw [int_eq_toNat_sub_negPart c]
  ring

private theorem sum_eq_sub (x : List ℕ) (ts : List (ℤ × MonomialCode)) :
    (ts.map fun t => t.1 * evalMonomial t.2 x).sum =
      ((ts.map fun t => t.1.toNat * natEvalMonomial t.2 x).sum : ℤ) -
        ((ts.map fun t => negPart t.1 * natEvalMonomial t.2 x).sum : ℤ) := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih, evalMonomial_eq_cast, term_eq]
    push_cast
    ring

private theorem eval_eq_sub (p : PolynomialCode) (x : List ℕ) :
    p.eval x = (evalPos p x : ℤ) - (evalNeg p x : ℤ) :=
  sum_eq_sub x p.terms

/-! #### Computability of the natural-valued pieces -/

private theorem primrec₂_natEvalMonomial : Primrec₂ natEvalMonomial := by
  -- Parallel recursion on the exponent vector and the assignment, as a left fold that
  -- carries the unconsumed assignment in the accumulator.
  have key : ∀ (e : MonomialCode) (x : List ℕ) (a : ℕ),
      (e.foldl (fun q ei => (q.1 * q.2.headI ^ ei, q.2.tail)) (a, x)).1 =
        a * natEvalMonomial e x := by
    intro e
    induction e with
    | nil => intro x a; simp [natEvalMonomial]
    | cons ei es ih =>
      intro x a
      cases x with
      | nil =>
        have hdef : (default : ℕ) = 0 := rfl
        simp only [List.foldl_cons, ih, natEvalMonomial, List.headI_nil, List.tail_nil, hdef]
        ring
      | cons v vs =>
        simp only [List.foldl_cons, ih, natEvalMonomial, List.headI_cons, List.tail_cons]
        ring
  have hstep : Primrec₂ fun (_ : MonomialCode × List ℕ) (q : (ℕ × List ℕ) × ℕ) =>
      (q.1.1 * q.1.2.headI ^ q.2, q.1.2.tail) :=
    Primrec.pair
      (Primrec.nat_mul.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.nat_pow.comp
          (Primrec.list_headI.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
          (Primrec.snd.comp Primrec.snd)))
      (Primrec.list_tail.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
  have h := Primrec.list_foldl (f := fun a : MonomialCode × List ℕ => a.1)
    (g := fun a : MonomialCode × List ℕ => ((1 : ℕ), a.2))
    (h := fun _ q => (q.1.1 * q.1.2.headI ^ q.2, q.1.2.tail))
    Primrec.fst (Primrec.pair (Primrec.const 1) Primrec.snd) hstep
  exact (Primrec.fst.comp h).of_eq fun a => by rw [key a.1 a.2 1, one_mul]

private theorem primrec₂_evalPos : Primrec₂ evalPos := by
  have hstep : Primrec₂ fun (a : PolynomialCode × List ℕ) (q : (ℤ × MonomialCode) × ℕ) =>
      q.1.1.toNat * natEvalMonomial q.1.2 a.2 + q.2 :=
    Primrec.nat_add.comp
      (Primrec.nat_mul.comp
        (Primrec.int_toNat.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))
        (primrec₂_natEvalMonomial.comp
          (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
          (Primrec.snd.comp Primrec.fst)))
      (Primrec.snd.comp Primrec.snd)
  have h := Primrec.list_foldr (f := fun a : PolynomialCode × List ℕ => a.1.terms)
    (g := fun _ : PolynomialCode × List ℕ => (0 : ℕ))
    (h := fun a q => q.1.1.toNat * natEvalMonomial q.1.2 a.2 + q.2)
    (primrec_terms.comp Primrec.fst) (Primrec.const 0) hstep
  refine h.of_eq fun a => ?_
  simp only [evalPos]
  induction a.1.terms with
  | nil => rfl
  | cons t ts ih => simp only [List.foldr_cons, List.map_cons, List.sum_cons, ih]

private theorem primrec₂_evalNeg : Primrec₂ evalNeg := by
  have hnegPart : Primrec negPart :=
    Primrec.nat_sub.comp Primrec.int_natAbs Primrec.int_toNat
  have hstep : Primrec₂ fun (a : PolynomialCode × List ℕ) (q : (ℤ × MonomialCode) × ℕ) =>
      negPart q.1.1 * natEvalMonomial q.1.2 a.2 + q.2 :=
    Primrec.nat_add.comp
      (Primrec.nat_mul.comp
        (hnegPart.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))
        (primrec₂_natEvalMonomial.comp
          (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
          (Primrec.snd.comp Primrec.fst)))
      (Primrec.snd.comp Primrec.snd)
  have h := Primrec.list_foldr (f := fun a : PolynomialCode × List ℕ => a.1.terms)
    (g := fun _ : PolynomialCode × List ℕ => (0 : ℕ))
    (h := fun a q => negPart q.1.1 * natEvalMonomial q.1.2 a.2 + q.2)
    (primrec_terms.comp Primrec.fst) (Primrec.const 0) hstep
  refine h.of_eq fun a => ?_
  simp only [evalNeg]
  induction a.1.terms with
  | nil => rfl
  | cons t ts ih => simp only [List.foldr_cons, List.map_cons, List.sum_cons, ih]

/-- Evaluation of an encoded polynomial is primitive recursive in the code and the
assignment jointly. -/
theorem primrec₂_eval : Primrec₂ eval := by
  have h := Primrec.int_subNat.comp primrec₂_evalPos primrec₂_evalNeg
  exact h.of_eq fun a => (eval_eq_sub a.1 a.2).symm

/-- Evaluation of an encoded polynomial is computable in the code and the assignment
jointly. -/
theorem computable₂_eval : Computable₂ eval := primrec₂_eval.to_comp

end PolynomialCode

end Hilbert10


/- Source: Hilbert10.Instantiate, Hilbert10 v2.3.0, Apache-2.0. -/
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# Specializing the initial variables of a code

Issue #12. This is the only substitution-like operation the project ships, and it is
simultaneously the computable step in the nonuniform-specialisation reduction (#35) and the
partial-evaluation primitive a future compiler would want.

## Design

A term is specialized by *evaluating its own initial segment*:

```lean
specializeTerm params t =
  (eval ⟨[(t.1, t.2.take params.length)]⟩ params, t.2.drop params.length)
```

The new coefficient is the old one with the parameter powers folded in, computed by reusing
`eval` itself, so no integer multiplication lemma is needed beyond what #9 already proved.
The variable shift is exactly `List.drop params.length`, term count and order are preserved,
and the encoding stays permissive.

`eval_instantiate` holds unconditionally — in particular for parameter lists longer than a
term's exponent vector, where the vector is entirely consumed and `drop` leaves nothing.
That is a consequence of the zero-extension convention from #8, not an extra hypothesis.
-/

namespace Hilbert10

namespace PolynomialCode

/-- Specialize one term: fold the parameter powers into the coefficient, and drop the
exponents that have been consumed. -/
def specializeTerm (params : List ℕ) (t : ℤ × MonomialCode) : ℤ × MonomialCode :=
  (eval ⟨[(t.1, t.2.take params.length)]⟩ params, t.2.drop params.length)

/-- Substitute `params` for the initial variables, shifting the remaining ones down. -/
def instantiate (p : PolynomialCode) (params : List ℕ) : PolynomialCode :=
  ⟨p.terms.map (specializeTerm params)⟩

@[simp] theorem eval_singleton (c : ℤ) (e : MonomialCode) (x : List ℕ) :
    eval ⟨[(c, e)]⟩ x = c * evalMonomial e x := by
  simp [eval]

/-! ### Evaluation -/

/-- Splitting an assignment splits a monomial's value: the exponents consumed by `params`
contribute a factor computed from `params` alone. Holds for every `e` and `params`, with no
length hypothesis — if `e` is shorter than `params` the second factor is `1`. -/
theorem evalMonomial_append_split (e : MonomialCode) (params w : List ℕ) :
    evalMonomial e (params ++ w) =
      evalMonomial (e.take params.length) params * evalMonomial (e.drop params.length) w := by
  induction params generalizing e with
  | nil => simp
  | cons a rest ih =>
    cases e with
    | nil => simp [evalMonomial]
    | cons ei es =>
      simp only [List.cons_append, List.length_cons, List.take_succ_cons, List.drop_succ_cons,
        evalMonomial, ih es]
      ring

/-- Instantiating and then evaluating is evaluating at the concatenated assignment. No
length hypotheses: the zero-extension convention of #8 makes this hold for every list. -/
theorem eval_instantiate (p : PolynomialCode) (params witnesses : List ℕ) :
    (p.instantiate params).eval witnesses = p.eval (params ++ witnesses) := by
  simp only [instantiate, eval, List.map_map]
  induction p.terms with
  | nil => simp
  | cons t ts ih =>
    simp only [List.map_cons, List.sum_cons, Function.comp_apply, ih, specializeTerm,
      eval_singleton, evalMonomial_append_split t.2 params witnesses]
    ring

/-! ### Arity -/

private theorem foldr_max_drop_le (k : ℕ) :
    ∀ (ts : List (ℤ × MonomialCode)) (N : ℕ), (∀ t ∈ ts, t.2.length ≤ N) →
      (ts.map fun t => ((t.2.drop k).length)).foldr max 0 ≤ N - k := by
  intro ts
  induction ts with
  | nil => intro _ _; simp
  | cons t ts ih =>
    intro N hts
    simp only [List.map_cons, List.foldr_cons]
    refine max_le ?_ (ih N fun s hs => hts s (List.mem_cons_of_mem _ hs))
    have := hts t (List.mem_cons_self ..)
    simp only [List.length_drop]
    omega

/-- Instantiating decreases the arity by the number of parameters supplied. An upper bound,
like every `arity` statement. -/
theorem arity_instantiate (p : PolynomialCode) (params : List ℕ) :
    (p.instantiate params).arity ≤ p.arity - params.length := by
  have h := foldr_max_drop_le params.length p.terms p.arity fun t ht => length_le_arity ht
  calc (p.instantiate params).arity
      = (p.terms.map fun t => (t.2.drop params.length).length).foldr max 0 := by
        simp [instantiate, arity, Function.comp_def, specializeTerm]
    _ ≤ p.arity - params.length := h

/-! ### Computability -/

theorem primrec₂_specializeTerm :
    Primrec₂ fun (params : List ℕ) (t : ℤ × MonomialCode) => specializeTerm params t := by
  have hparams : Primrec fun a : List ℕ × (ℤ × MonomialCode) => a.1 := Primrec.fst
  have hlen : Primrec fun a : List ℕ × (ℤ × MonomialCode) => a.1.length :=
    Primrec.list_length.comp hparams
  have hcoeff : Primrec fun a : List ℕ × (ℤ × MonomialCode) => a.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hexp : Primrec fun a : List ℕ × (ℤ × MonomialCode) => a.2.2 :=
    Primrec.snd.comp Primrec.snd
  have htake : Primrec fun a : List ℕ × (ℤ × MonomialCode) => a.2.2.take a.1.length :=
    Primrec.list_take.comp hlen hexp
  have hcode : Primrec fun a : List ℕ × (ℤ × MonomialCode) =>
      (⟨[(a.2.1, a.2.2.take a.1.length)]⟩ : PolynomialCode) :=
    primrec_mk.comp (Primrec.list_cons.comp (Primrec.pair hcoeff htake) (Primrec.const []))
  exact Primrec.pair (primrec₂_eval.comp hcode hparams)
    (Primrec.list_drop.comp hlen hexp)

theorem primrec₂_instantiate : Primrec₂ instantiate := by
  have hg : Primrec₂ fun (a : PolynomialCode × List ℕ) (t : ℤ × MonomialCode) =>
      specializeTerm a.2 t :=
    primrec₂_specializeTerm.comp (Primrec.snd.comp Primrec.fst) Primrec.snd
  have h := Primrec.list_map (primrec_terms.comp Primrec.fst) hg
  exact (primrec_mk.comp h).of_eq fun _ => rfl

theorem computable₂_instantiate : Computable₂ instantiate := primrec₂_instantiate.to_comp

/-! ### Sanity checks

`x₀ ^ 2 + x₁ ^ 2 - 25` specialized at `x₀ := 3` becomes `9 + x₀ ^ 2 - 25`: the term count
and order are preserved, the first term collapses to a constant, and the surviving variable
has shifted down by one. The second example supplies more parameters than the polynomial has
variables, which is legal and leaves nothing.
-/

example :
    ((⟨[(1, [2]), (1, [0, 2]), (-25, [])]⟩ : PolynomialCode).instantiate [3]).terms =
      [(9, []), (1, [2]), (-25, [])] := by decide

example :
    ((⟨[(1, [2]), (1, [0, 2]), (-25, [])]⟩ : PolynomialCode).instantiate [3]).eval [4] = 0 := by
  decide

example :
    ((⟨[(1, [2]), (1, [0, 2]), (-25, [])]⟩ : PolynomialCode).instantiate
      [3, 4, 7, 9]).arity = 0 := by
  decide

end PolynomialCode

end Hilbert10


/- Source: Hilbert10.NatSolvable, Hilbert10 v2.3.0, Apache-2.0. -/
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# Hilbert's tenth problem as a decision problem

Issue #13, the last piece of M2. This is the predicate whose undecidability is the
project's headline (#27), and whose RE-completeness is #35 and #26.

## The missing side condition

`HasNatRoot` places **no** constraint relating the length of the root to the arity:

```lean
def HasNatRoot (p : PolynomialCode) : Prop := ∃ x : List ℕ, p.eval x = 0
```

That is equivalent to demanding a root of length exactly `arity` (`hasNatRoot_iff`), because
zero-extension (#8) lets a short root be padded and the arity bound lets a long one be
truncated. The unconstrained form is what every later proof wants, since it never has to
produce or preserve a length invariant.

The name says `Nat` because the development is over natural-number assignments, matching
`Dioph`. Hilbert's original integer formulation is #28 and gets `IntSolvable`; nothing here
is called `H10` unqualified.

## What this module does not yet claim

`NatSolvable` is a predicate on `PolynomialCode`, which carries a `Primcodable` instance, so
it is a decision problem in the sense the computability library expects. That instance is
imported here rather than merely referenced, so this module alone supplies what it advertises
instead of relying on the root bundle to pull it in.

But `REPred NatSolvable` is *not* provable from this module's imports: it needs computability
of `eval`, which needs `Primrec` lemmas about `ℤ` that the pinned mathlib lacks (#36).

So the definition and its semantics are settled here, and the statement that it is
recursively enumerable is a separate theorem with a separate dependency. Do not read the
public `NatSolvable` as already carrying that content.
-/

namespace Hilbert10

namespace PolynomialCode

/-- An encoded polynomial has a natural root. No length side condition — see
`hasNatRoot_iff`. -/
def HasNatRoot (p : PolynomialCode) : Prop := ∃ x : List ℕ, p.eval x = 0

/-- A root may always be taken to have length exactly `arity`.

The witness is uniform in both directions: pad with zeros and truncate to `arity`, which is
correct whether the original root was short or long, so no case split on lengths is
needed. -/
theorem hasNatRoot_iff (p : PolynomialCode) :
    p.HasNatRoot ↔ ∃ x : List ℕ, x.length = p.arity ∧ p.eval x = 0 := by
  constructor
  · rintro ⟨x, hx⟩
    set L := x ++ List.replicate p.arity 0 with hL
    refine ⟨L.take p.arity, ?_, ?_⟩
    · simp [hL]
    · have hlen : (L.take p.arity).length = p.arity := by simp [hL]
      have hsplit : p.eval L = p.eval (L.take p.arity) := by
        conv_lhs => rw [← List.take_append_drop p.arity L]
        exact eval_append_of_arity_le (Nat.le_of_eq hlen.symm) _
      rw [← hsplit, hL, eval_append_replicate_zero]
      exact hx
  · rintro ⟨x, _, hx⟩
    exact ⟨x, hx⟩

end PolynomialCode

/-- **Hilbert's tenth problem over the naturals**: does an encoded polynomial have a natural
root? Definitionally `PolynomialCode.HasNatRoot`, so no second semantics exists to drift. -/
def NatSolvable : PolynomialCode → Prop := PolynomialCode.HasNatRoot

theorem natSolvable_iff (p : PolynomialCode) :
    NatSolvable p ↔ ∃ x : List ℕ, p.eval x = 0 := Iff.rfl

theorem natSolvable_iff_arity (p : PolynomialCode) :
    NatSolvable p ↔ ∃ x : List ℕ, x.length = p.arity ∧ p.eval x = 0 :=
  PolynomialCode.hasNatRoot_iff p

/-- **Solvability depends only on the denoted polynomial.** This is the promise the permissive
wire format makes: duplicate terms, trailing zero exponents and any other presentation choice
that leaves `denote` unchanged cannot change whether a root exists. -/
theorem natSolvable_iff_of_denote_eq {p q : PolynomialCode} (h : p.denote = q.denote) :
    NatSolvable p ↔ NatSolvable q :=
  exists_congr fun x => by rw [PolynomialCode.eval_eq_of_denote_eq h]

/-! ### Sanity checks -/

/-- The tie to `HasNatRoot` is definitional, not an equivalence to be maintained. -/
example (p : PolynomialCode) : NatSolvable p ↔ p.HasNatRoot := Iff.rfl

/-- A solvable instance: `x₀ ^ 2 + x₁ ^ 2 - 25` has the root `[3, 4]`. -/
example : NatSolvable ⟨[(1, [2]), (1, [0, 2]), (-25, [])]⟩ := ⟨[3, 4], by decide⟩

/-- Duplicate terms do not affect solvability: they denote the combined term. -/
example (c d : ℤ) (e : MonomialCode) :
    NatSolvable ⟨[(c, e), (d, e)]⟩ ↔ NatSolvable ⟨[(c + d, e)]⟩ :=
  natSolvable_iff_of_denote_eq (PolynomialCode.denote_duplicate c d e)

/-- Trailing zero exponents do not affect solvability, though they inflate `arity`. -/
example (c : ℤ) (e : MonomialCode) (k : ℕ) :
    NatSolvable ⟨[(c, e ++ List.replicate k 0)]⟩ ↔ NatSolvable ⟨[(c, e)]⟩ :=
  natSolvable_iff_of_denote_eq (by
    simp [PolynomialCode.denote, PolynomialCode.denoteMonomial_append_replicate_zero])

end Hilbert10


/- Source: Hilbert10.Specialization, Hilbert10 v2.3.0, Apache-2.0. -/
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# From a representation to a reduction

Issue #35, the computational centrepiece — and the whole scope argument of the project in
one theorem. A relation with *any* polynomial representation many-one reduces to
`NatSolvable`, with **no DPRM content whatsoever**.

## Why the nonuniformity is fine

The target `R ≤₀ NatSolvable` is a proposition, so existential elimination may fix the
representing polynomial locally. **No uniform data-valued extractor is produced**: there is
deliberately no function from representations to codes here, and in particular nothing of
the shape `Nat.Partrec.Code → PolynomialCode` (see #29).

The reduction is `fun x => q.instantiate (List.ofFn x)`. It is computable in `x` because `q`
is a *constant* — chosen once, outside the reduction — and only `instantiate` has to be
computable. Note that fixing `q` needs no choice principle at all: eliminating an
existential into a `Prop` is constructive.

## Test rather than argument

The final example compiles a hand-written representation of "is a sum of two squares" all
the way to a many-one reduction, exercising #5, #10, #11, #12 and #13 end to end before any
of M4's cost is incurred.
-/

namespace Hilbert10

namespace PolynomialCode

/-- A list of known length is `List.ofFn` of the corresponding function. -/
private theorem ofFn_getD_of_length_eq {l : List ℕ} {m : ℕ} (hl : l.length = m) :
    List.ofFn (fun i : Fin m => l.getD i 0) = l := by
  subst hl
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp

/-- Roots may be taken in `List.ofFn` form at any length at least the arity. This is the one
place the conversion between root lists and `Fin`-indexed witnesses happens. -/
theorem hasNatRoot_iff_fin_of_arity_le {p : PolynomialCode} {m : ℕ} (h : p.arity ≤ m) :
    p.HasNatRoot ↔ ∃ y : Fin m → ℕ, p.eval (List.ofFn y) = 0 := by
  constructor
  · intro hp
    obtain ⟨x, hlen, hx⟩ := (hasNatRoot_iff p).mp hp
    have hll : (x ++ List.replicate (m - p.arity) 0).length = m := by
      simp only [List.length_append, List.length_replicate, hlen]
      omega
    refine ⟨fun i => (x ++ List.replicate (m - p.arity) 0).getD i 0, ?_⟩
    rw [ofFn_getD_of_length_eq hll, eval_append_replicate_zero]
    exact hx
  · rintro ⟨y, hy⟩
    exact ⟨List.ofFn y, hy⟩

/-- Assembling a `List.ofFn` from a `Fin`-indexed tuple is primitive recursive. -/
theorem primrec_ofFn {n : ℕ} : Primrec fun x : Fin n → ℕ => List.ofFn x :=
  Primrec.list_ofFn fun i => Primrec.fin_app.comp Primrec.id (Primrec.const i)

end PolynomialCode

open PolynomialCode MvPolynomial

/-- **Representation to reduction, general arity.** A relation on `Fin n`-tuples that is
represented by *some* polynomial many-one reduces to `NatSolvable`.

The representation is an existential and stays one; nothing is extracted from it. -/
theorem representsNat_manyOneReducible_natSolvable' {n : ℕ} {R : (Fin n → ℕ) → Prop}
    (h : ∃ (m : ℕ) (p : MvPolynomial (Fin n ⊕ Fin m) ℤ), RepresentsNat p R) :
    R ≤₀ NatSolvable := by
  obtain ⟨m, p, hp⟩ := h
  obtain ⟨q, harity, hq⟩ := exists_code_representsNat hp
  refine ⟨fun x => q.instantiate (List.ofFn x),
    computable₂_instantiate.comp (Computable.const q) primrec_ofFn.to_comp, fun x => ?_⟩
  have harity' : (q.instantiate (List.ofFn x)).arity ≤ m := by
    refine le_trans (arity_instantiate q (List.ofFn x)) ?_
    simp only [List.length_ofFn]
    omega
  rw [hq x]
  rw [show NatSolvable (q.instantiate (List.ofFn x)) =
      (q.instantiate (List.ofFn x)).HasNatRoot from rfl,
    hasNatRoot_iff_fin_of_arity_le harity']
  exact exists_congr fun y => by rw [eval_instantiate]

/-- **Representation to reduction, unary.** Derived from the general form by supplying the
constant tuple; no auxiliary predicate on lists is introduced. -/
theorem representsNat_manyOneReducible_natSolvable {R : ℕ → Prop}
    (h : ∃ (m : ℕ) (p : MvPolynomial (Fin 1 ⊕ Fin m) ℤ),
      RepresentsNat p fun v : Fin 1 → ℕ => R (v 0)) :
    R ≤₀ NatSolvable := by
  obtain ⟨f, hf, hfR⟩ := representsNat_manyOneReducible_natSolvable' h
  have hconst : Primrec fun a : ℕ => (fun _ : Fin 1 => a) :=
    Primrec.fin_curry.mpr (show Primrec₂ fun (a : ℕ) (_ : Fin 1) => a from Primrec.fst)
  exact ⟨fun a => f fun _ => a, hf.comp hconst.to_comp, fun a => hfR fun _ => a⟩

/-! ### End-to-end test

A hand-written representation, compiled to a reduction. This exercises the whole M1–M2
pipeline — `RepresentsNat`, `exists_code`, `denote`, `instantiate`, `NatSolvable` — with no
DPRM content, which is the point of doing it now rather than after M4.
-/

/-- Being a sum of two squares is represented by `x₀ - y₀² - y₁²`. -/
theorem representsNat_sumTwoSquares :
    RepresentsNat (X (Sum.inl 0) - X (Sum.inr 0) ^ 2 - X (Sum.inr 1) ^ 2 :
        MvPolynomial (Fin 1 ⊕ Fin 2) ℤ)
      (fun v : Fin 1 → ℕ => ∃ a b : ℕ, v 0 = a ^ 2 + b ^ 2) := by
  intro v
  simp only [map_sub, map_pow, eval_X]
  constructor
  · rintro ⟨a, b, hab⟩
    refine ⟨![a, b], ?_⟩
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Sum.elim_inl,
      Sum.elim_inr, hab]
    push_cast
    ring
  · rintro ⟨y, hy⟩
    refine ⟨y 0, y 1, ?_⟩
    simp only [Sum.elim_inl, Sum.elim_inr] at hy
    have : ((v 0 : ℕ) : ℤ) = ((y 0 ^ 2 + y 1 ^ 2 : ℕ) : ℤ) := by push_cast; linarith
    exact_mod_cast this

/-- The compiled reduction: "is a sum of two squares" many-one reduces to Hilbert's tenth
problem over the naturals. -/
theorem sumTwoSquares_manyOneReducible_natSolvable :
    (fun n : ℕ => ∃ a b : ℕ, n = a ^ 2 + b ^ 2) ≤₀ NatSolvable :=
  representsNat_manyOneReducible_natSolvable ⟨2, _, representsNat_sumTwoSquares⟩

end Hilbert10


/- Source: Hilbert10.DiophToRE, Hilbert10 v2.3.0, Apache-2.0. -/
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# Diophantine implies recursively enumerable

Issue #14, the cheap half of the eventual `Dioph ↔ REPred` characterisation, and the
integration test for M1 and M2 together: it is the first result that needs the finite
normal form (#6), the wire format (#8), its computability (#9) and the coding theorem (#11)
to fit together.

## Architecture

Both endpoints are specializations of one closure lemma,

```lean
ComputablePred.rePred_exists : ComputablePred P → REPred fun a => ∃ b, P (a, b)
```

which is independently useful and has nothing to do with polynomials: projecting a
decidable predicate along an existential over any `Primcodable` type gives an RE predicate.
It is proved by searching the *encodings* of witnesses with `Nat.rfindOpt`, so the search
enumerates encoded witness tuples directly rather than boxes of naturals, and invalid codes
map to `none` rather than to some default.

## Why `decode` and not `decode₂`

The search needs a computable surjection onto candidate witnesses, and rechecks `P` on every
one, so canonicality of codes is irrelevant. `decode₂` additionally rejects non-canonical
codes — what an *injective* enumeration needs — which would add machinery without
strengthening soundness or completeness. Completeness here is exactly
`Encodable.encodek : decode (encode b) = some b`.
-/

namespace Hilbert10

open MvPolynomial PolynomialCode

/-- Projecting a decidable predicate along an existential over a `Primcodable` type yields a
recursively enumerable predicate.

The search runs over encodings of witnesses: at stage `n` it decodes `n`, and succeeds if it
decodes to a witness satisfying `P`. Completeness comes from `Encodable.encodek`, since the
witness `b` is found at stage `encode b`. -/
theorem ComputablePred.rePred_exists {α β : Type*} [Primcodable α] [Primcodable β]
    {P : α × β → Prop} (hP : ComputablePred P) : REPred fun a => ∃ b, P (a, b) := by
  obtain ⟨_inst, hPc⟩ := hP
  classical
  have hg : Computable₂ fun (a : α) (n : ℕ) =>
      (Encodable.decode (α := β) n).bind fun b => if P (a, b) then some b else none := by
    refine Computable.option_bind (Computable.decode.comp Computable.snd) ?_
    have hdec : Computable fun z : (α × ℕ) × β => decide (P (z.1.1, z.2)) :=
      hPc.comp ((Computable.fst.comp Computable.fst).pair Computable.snd)
    exact (Computable.cond hdec (Computable.option_some.comp Computable.snd)
      (Computable.const none)).of_eq fun z => by by_cases h : P (z.1.1, z.2) <;> simp [h]
  refine ((Partrec.rfindOpt hg).dom_re).of_eq fun a => ?_
  simp only [Nat.rfindOpt_dom]
  constructor
  · rintro ⟨n, b, hb⟩
    cases hd : Encodable.decode (α := β) n with
    | none =>
      rw [hd] at hb
      simp at hb
    | some c =>
      rw [hd] at hb
      by_cases hP : P (a, c)
      · exact ⟨c, hP⟩
      · simp only [Option.bind, if_neg hP] at hb
        simp at hb
  · rintro ⟨b, hb⟩
    exact ⟨Encodable.encode b, b, by simp [Encodable.encodek, hb]⟩

/-- Evaluating a fixed code at a pair of `Fin`-indexed tuples is a computable predicate. -/
private theorem computablePred_eval_ofFn (q : PolynomialCode) (n m : ℕ) :
    ComputablePred fun z : (Fin n → ℕ) × (Fin m → ℕ) =>
      q.eval (List.ofFn z.1 ++ List.ofFn z.2) = 0 := by
  have hlist : Primrec fun z : (Fin n → ℕ) × (Fin m → ℕ) => List.ofFn z.1 ++ List.ofFn z.2 :=
    Primrec.list_append.comp (primrec_ofFn.comp Primrec.fst) (primrec_ofFn.comp Primrec.snd)
  exact PrimrecPred.computablePred
    (PrimrecRel.comp Primrec.eq (primrec₂_eval.comp (Primrec.const q) hlist) (Primrec.const 0))

/-- **Diophantine implies recursively enumerable.** -/
theorem Dioph.rePred {n : ℕ} {R : (Fin n → ℕ) → Prop} (h : Dioph {x : Fin n → ℕ | R x}) :
    REPred R := by
  obtain ⟨m, p, hp⟩ := (dioph_iff_exists_fin_mvPolynomial R).mp h
  obtain ⟨q, _, hq⟩ := exists_code_representsNat hp
  refine (ComputablePred.rePred_exists (computablePred_eval_ofFn q n m)).of_eq fun x => ?_
  exact (hq x).symm

/-- Evaluating a code at an assignment is a computable predicate, jointly in both. -/
private theorem computablePred_eval : ComputablePred fun z : PolynomialCode × List ℕ =>
    z.1.eval z.2 = 0 :=
  PrimrecPred.computablePred
    (PrimrecRel.comp Primrec.eq (primrec₂_eval.comp Primrec.fst Primrec.snd) (Primrec.const 0))

/-- **Hilbert's tenth problem over the naturals is recursively enumerable.** -/
theorem rePred_natSolvable : REPred NatSolvable :=
  (ComputablePred.rePred_exists computablePred_eval).of_eq fun _ => Iff.rfl

end Hilbert10


/- Source: Hilbert10.Internal.ExpDioph, Hilbert10 v2.3.0, Apache-2.0. -/
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# Exponential Diophantine relations

Issue #16, and the first piece of M4. This layer is **route-independent**: both the machine
route and the direct route arithmetise into exponential Diophantine relations, and #15's
spike must produce one, so it is a prerequisite for the route decision rather than a
consequence of it.

## Why ℕ-valued

`ExpTerm` is valued in `ℕ`, and `ExpDioph` is *equality of two ℕ-valued terms* under ℕ
witnesses. An `ℤ`-valued exponential term would leave `s ^ t` ill-specified when the
exponent evaluates negatively, and `Dioph.pow_dioph` supplies only the graph of **natural**
exponentiation. So there is no negation, and equations are `s = t` rather than `p = 0`.

The payoff is that the bridge to `Dioph` is a structural induction over combinators mathlib
already has. `DiophFn` is itself ℕ-valued, and every term constructor here is backed by a
`DiophFn`-valued lemma:

| constructor | mathlib |
|---|---|
| `var`, `const` | `Dioph.proj_dioph`, `Dioph.const_dioph` |
| `add`, `mul`, `pow` | `Dioph.add_dioph`, `Dioph.mul_dioph`, `Dioph.pow_dioph` |
| `div`, `mod` | `Dioph.div_dioph`, `Dioph.mod_dioph` |
| `sub` (truncated) | `Dioph.sub_dioph` |

`div` and `mod` are constructors for a concrete reason: base-`u` digit extraction (#33) needs
them at the `ExpDioph` level, and `ExpDioph.dioph` is one-directional, so a `Dioph`-level
lemma could not be pulled back. Relations that are *not* `DiophFn`-valued in mathlib —
`≤`, `<`, `∣` — appear instead as closure lemmas below.

`sub` is truncated subtraction, and it earns its place by making **conjunction** available.
Over `ℤ` a system of equations is combined by sum of squares (`Poly.sumsq`); over `ℕ` that is
unavailable, but

```
s₁ = t₁ ∧ s₂ = t₂  ↔  (s₁ ∸ t₁) + (t₁ ∸ s₁) + (s₂ ∸ t₂) + (t₂ ∸ s₂) = 0
```

does the same job, since a sum of naturals vanishes iff every summand does. Without it
`ExpDioph` could express only single equations, which is not enough for any real
arithmetisation — a packed machine run is a *system* whose constraints share witnesses.

## Universes

Everything here lives at `Type 0`. That is forced: `Dioph` itself is universe-polymorphic,
but mathlib states the entire `DiophFn` combinator API — `add_dioph`, `mul_dioph`,
`pow_dioph`, `div_dioph`, `mod_dioph`, `eq_dioph` — inside a section fixing
`variable {α : Type}`. No loss here, since every variable type in this project is `Fin n`,
but it is a real restriction on the API and worth generalising upstream some day.

This syntax stays internal to the DPRM core; it is not the DSL of #29, having no
fresh-variable discipline, no gadget calls and no extraction.
-/

namespace Hilbert10

variable {α β : Type}

/-- Syntax of exponential polynomials over `ℕ`. -/
inductive ExpTerm (α : Type) : Type
  | var : α → ExpTerm α
  | const : ℕ → ExpTerm α
  | add : ExpTerm α → ExpTerm α → ExpTerm α
  | mul : ExpTerm α → ExpTerm α → ExpTerm α
  | pow : ExpTerm α → ExpTerm α → ExpTerm α
  | div : ExpTerm α → ExpTerm α → ExpTerm α
  | mod : ExpTerm α → ExpTerm α → ExpTerm α
  | sub : ExpTerm α → ExpTerm α → ExpTerm α

namespace ExpTerm

/-- Value of an exponential term at an assignment. -/
def eval : ExpTerm α → (α → ℕ) → ℕ
  | var i, x => x i
  | const n, _ => n
  | add s t, x => s.eval x + t.eval x
  | mul s t, x => s.eval x * t.eval x
  | pow s t, x => s.eval x ^ t.eval x
  | div s t, x => s.eval x / t.eval x
  | mod s t, x => s.eval x % t.eval x
  | sub s t, x => s.eval x - t.eval x

/-- **The bridge.** Every exponential term denotes a Diophantine function.

One structural induction, each case a mathlib combinator; `pow` is where
`Pell.eq_pow_of_pell` enters, through `Dioph.pow_dioph`. -/
theorem diophFn (t : ExpTerm α) : Dioph.DiophFn fun x => t.eval x := by
  induction t with
  | var i => exact Dioph.proj_dioph i
  | const n => exact Dioph.const_dioph n
  | add s t hs ht => exact Dioph.add_dioph hs ht
  | mul s t hs ht => exact Dioph.mul_dioph hs ht
  | pow s t hs ht => exact Dioph.pow_dioph hs ht
  | div s t hs ht => exact Dioph.div_dioph hs ht
  | mod s t hs ht => exact Dioph.mod_dioph hs ht
  | sub s t hs ht => exact Dioph.sub_dioph hs ht

/-- Reindex the variables of a term. -/
def map (f : α → β) : ExpTerm α → ExpTerm β
  | var i => var (f i)
  | const n => const n
  | add s t => add (s.map f) (t.map f)
  | mul s t => mul (s.map f) (t.map f)
  | pow s t => pow (s.map f) (t.map f)
  | div s t => div (s.map f) (t.map f)
  | mod s t => mod (s.map f) (t.map f)
  | sub s t => sub (s.map f) (t.map f)

@[simp] theorem eval_map (f : α → β) (t : ExpTerm α) (x : β → ℕ) :
    (t.map f).eval x = t.eval (x ∘ f) := by
  induction t <;> simp_all [map, eval]

/-- Substitute a term for each variable. Unlike `map`, which only renames variables, this
replaces them by arbitrary terms — which is what an arithmetisation needs when a local
witness variable has to become a lookup into a coded sequence. -/
def subst (f : α → ExpTerm β) : ExpTerm α → ExpTerm β
  | var i => f i
  | const n => const n
  | add s t => add (s.subst f) (t.subst f)
  | mul s t => mul (s.subst f) (t.subst f)
  | pow s t => pow (s.subst f) (t.subst f)
  | div s t => div (s.subst f) (t.subst f)
  | mod s t => mod (s.subst f) (t.subst f)
  | sub s t => sub (s.subst f) (t.subst f)

@[simp] theorem eval_subst (f : α → ExpTerm β) (t : ExpTerm α) (v : β → ℕ) :
    (t.subst f).eval v = t.eval fun i => (f i).eval v := by
  induction t <;> simp_all [subst, eval]

end ExpTerm

/-- A set is exponential Diophantine when it is the projection of an equality between two
exponential terms. -/
def ExpDioph (S : Set (α → ℕ)) : Prop :=
  ∃ (β : Type) (s t : ExpTerm (α ⊕ β)),
    ∀ v, v ∈ S ↔ ∃ w : β → ℕ, s.eval (Sum.elim v w) = t.eval (Sum.elim v w)

namespace ExpDioph

/-- **Exponential Diophantine implies Diophantine.** The witnesses are projected away by
`Dioph.ex_dioph`, and the equation is `Dioph` by `Dioph.eq_dioph` applied to the two
`DiophFn`s from `ExpTerm.diophFn`. -/
theorem dioph {S : Set (α → ℕ)} (h : ExpDioph S) : Dioph S := by
  obtain ⟨β, s, t, hst⟩ := h
  have heq : Dioph {z : α ⊕ β → ℕ | s.eval z = t.eval z} :=
    Dioph.eq_dioph s.diophFn t.diophFn
  exact (Dioph.ex_dioph heq).ext fun v => (hst v).symm

/-- Two natural numbers are equal iff their two truncated differences both vanish. This is
the ℕ substitute for the sum-of-squares trick that combines a system of equations over `ℤ`. -/
theorem eq_iff_sub_add_sub {a b : ℕ} : a = b ↔ (a - b) + (b - a) = 0 := by omega

/-- `ExpDioph` is closed under conjunction, with the two witness blocks combined. This is
what makes a *system* of constraints expressible, which every arithmetisation needs. -/
theorem and {S T : Set (α → ℕ)} (hS : ExpDioph S) (hT : ExpDioph T) : ExpDioph (S ∩ T) := by
  obtain ⟨β, s₁, t₁, h₁⟩ := hS
  obtain ⟨γ, s₂, t₂, h₂⟩ := hT
  -- Reindex each equation into the combined witness block `β ⊕ γ`.
  let f₁ : α ⊕ β → α ⊕ (β ⊕ γ) := Sum.elim Sum.inl (fun b => Sum.inr (Sum.inl b))
  let f₂ : α ⊕ γ → α ⊕ (β ⊕ γ) := Sum.elim Sum.inl (fun c => Sum.inr (Sum.inr c))
  refine ⟨β ⊕ γ,
    .add (.add (.sub (s₁.map f₁) (t₁.map f₁)) (.sub (t₁.map f₁) (s₁.map f₁)))
      (.add (.sub (s₂.map f₂) (t₂.map f₂)) (.sub (t₂.map f₂) (s₂.map f₂))),
    .const 0, fun v => ?_⟩
  have key : ∀ (w : (β ⊕ γ) → ℕ),
      (Sum.elim v w ∘ f₁ = Sum.elim v (w ∘ Sum.inl)) ∧
        (Sum.elim v w ∘ f₂ = Sum.elim v (w ∘ Sum.inr)) := by
    intro w
    constructor <;> (funext z; cases z <;> rfl)
  constructor
  · rintro ⟨hv₁, hv₂⟩
    obtain ⟨w₁, hw₁⟩ := (h₁ v).mp hv₁
    obtain ⟨w₂, hw₂⟩ := (h₂ v).mp hv₂
    refine ⟨Sum.elim w₁ w₂, ?_⟩
    have e := key (Sum.elim w₁ w₂)
    simp only [ExpTerm.eval, ExpTerm.eval_map, e.1, e.2, Sum.elim_comp_inl, Sum.elim_comp_inr]
    omega
  · rintro ⟨w, hw⟩
    have e := key w
    simp only [ExpTerm.eval, ExpTerm.eval_map, e.1, e.2] at hw
    refine ⟨(h₁ v).mpr ⟨w ∘ Sum.inl, by omega⟩, (h₂ v).mpr ⟨w ∘ Sum.inr, by omega⟩⟩

/-- `ExpDioph` is closed under disjunction, via the *product* of the two symmetric equality
gaps: a product of naturals vanishes exactly when one factor does. Finite dispatch over a fixed
program's instruction list (#45) is repeated use of this, which is why it is worth having
alongside `and` rather than routing through complements. -/
theorem or {S T : Set (α → ℕ)} (hS : ExpDioph S) (hT : ExpDioph T) : ExpDioph (S ∪ T) := by
  obtain ⟨β, s₁, t₁, h₁⟩ := hS
  obtain ⟨γ, s₂, t₂, h₂⟩ := hT
  let f₁ : α ⊕ β → α ⊕ (β ⊕ γ) := Sum.elim Sum.inl (fun b => Sum.inr (Sum.inl b))
  let f₂ : α ⊕ γ → α ⊕ (β ⊕ γ) := Sum.elim Sum.inl (fun c => Sum.inr (Sum.inr c))
  refine ⟨β ⊕ γ,
    .mul (.add (.sub (s₁.map f₁) (t₁.map f₁)) (.sub (t₁.map f₁) (s₁.map f₁)))
      (.add (.sub (s₂.map f₂) (t₂.map f₂)) (.sub (t₂.map f₂) (s₂.map f₂))),
    .const 0, fun v => ?_⟩
  have key : ∀ (w : (β ⊕ γ) → ℕ),
      (Sum.elim v w ∘ f₁ = Sum.elim v (w ∘ Sum.inl)) ∧
        (Sum.elim v w ∘ f₂ = Sum.elim v (w ∘ Sum.inr)) := by
    intro w
    constructor <;> (funext z; cases z <;> rfl)
  constructor
  · rintro (hv | hv)
    · obtain ⟨w₁, hw₁⟩ := (h₁ v).mp hv
      refine ⟨Sum.elim w₁ (fun _ => 0), ?_⟩
      have e := key (Sum.elim w₁ (fun _ => 0))
      simp only [ExpTerm.eval, ExpTerm.eval_map, e.1, e.2, Sum.elim_comp_inl, Sum.elim_comp_inr]
      exact Nat.mul_eq_zero.mpr (Or.inl (by omega))
    · obtain ⟨w₂, hw₂⟩ := (h₂ v).mp hv
      refine ⟨Sum.elim (fun _ => 0) w₂, ?_⟩
      have e := key (Sum.elim (fun _ => 0) w₂)
      simp only [ExpTerm.eval, ExpTerm.eval_map, e.1, e.2, Sum.elim_comp_inl, Sum.elim_comp_inr]
      exact Nat.mul_eq_zero.mpr (Or.inr (by omega))
  · rintro ⟨w, hw⟩
    have e := key w
    simp only [ExpTerm.eval, ExpTerm.eval_map, e.1, e.2] at hw
    rcases Nat.mul_eq_zero.mp hw with h | h
    · exact Or.inl ((h₁ v).mpr ⟨w ∘ Sum.inl, by omega⟩)
    · exact Or.inr ((h₂ v).mpr ⟨w ∘ Sum.inr, by omega⟩)

/-- The empty relation. The base case of a finite disjunction. -/
theorem of_false : ExpDioph (∅ : Set (α → ℕ)) :=
  ⟨Empty, .const 0, .const 1, fun v => by simp [ExpTerm.eval]⟩

/-- `ExpDioph` respects extensional equality of relations. -/
theorem congr {S T : Set (α → ℕ)} (h : ExpDioph S) (hST : ∀ v, v ∈ S ↔ v ∈ T) :
    ExpDioph T := by
  obtain ⟨β, s, t, hst⟩ := h
  exact ⟨β, s, t, fun v => (hST v).symm.trans (hst v)⟩

/-- Reindexing the variables of an exponential Diophantine set. -/
theorem reindex {S : Set (α → ℕ)} (h : ExpDioph S) (f : α → β) :
    ExpDioph {v : β → ℕ | (v ∘ f) ∈ S} := by
  obtain ⟨γ, s, t, hst⟩ := h
  refine ⟨γ, s.map (Sum.map f id), t.map (Sum.map f id), fun v => ?_⟩
  have e : ∀ w : γ → ℕ,
      Sum.elim v w ∘ Sum.map f id = Sum.elim (v ∘ f) w := by
    intro w
    funext z
    cases z <;> rfl
  simp only [Set.mem_setOf_eq, ExpTerm.eval_map, e]
  exact hst (v ∘ f)

/-- Projecting away the last block of variables. Mirrors `Dioph.ex_dioph`; this is the
primary projection operation, not a variant of another lemma. -/
theorem ex {S : Set (α ⊕ β → ℕ)} (h : ExpDioph S) :
    ExpDioph {v : α → ℕ | ∃ w : β → ℕ, Sum.elim v w ∈ S} := by
  obtain ⟨γ, s, t, hst⟩ := h
  -- Combine the projected block with the existing witnesses.
  let f : (α ⊕ β) ⊕ γ → α ⊕ (β ⊕ γ) :=
    Sum.elim (Sum.elim Sum.inl (fun b => Sum.inr (Sum.inl b))) (fun c => Sum.inr (Sum.inr c))
  refine ⟨β ⊕ γ, s.map f, t.map f, fun v => ?_⟩
  have e : ∀ (w : β → ℕ) (u : γ → ℕ),
      Sum.elim v (Sum.elim w u) ∘ f = Sum.elim (Sum.elim v w) u := by
    intro w u
    funext z
    rcases z with (a | b) | c <;> rfl
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨u, hu⟩ := (hst (Sum.elim v w)).mp hw
    exact ⟨Sum.elim w u, by simpa only [ExpTerm.eval_map, e w u] using hu⟩
  · rintro ⟨wu, hwu⟩
    refine ⟨wu ∘ Sum.inl, (hst _).mpr ⟨wu ∘ Sum.inr, ?_⟩⟩
    have := hwu
    simp only [ExpTerm.eval_map] at this
    rwa [show Sum.elim v wu ∘ f
        = Sum.elim (Sum.elim v (wu ∘ Sum.inl)) (wu ∘ Sum.inr) by
      funext z; rcases z with (a | b) | c <;> rfl] at this

/-- `≤` between exponential terms, via a slack witness. -/
theorem of_le {s t : ExpTerm α} : ExpDioph {v | s.eval v ≤ t.eval v} := by
  refine ⟨Unit, .add (s.map Sum.inl) (.var (Sum.inr ())), t.map Sum.inl, fun v => ?_⟩
  simp only [Set.mem_setOf_eq, ExpTerm.eval, ExpTerm.eval_map, Sum.elim_comp_inl]
  constructor
  · intro h
    exact ⟨fun _ => t.eval v - s.eval v, by simp [Sum.elim_inr]; omega⟩
  · rintro ⟨w, hw⟩
    simp only [Sum.elim_inr] at hw
    omega

/-- `<` between exponential terms, via a slack witness. -/
theorem of_lt {s t : ExpTerm α} : ExpDioph {v | s.eval v < t.eval v} := by
  refine ⟨Unit, .add (.add (s.map Sum.inl) (.var (Sum.inr ()))) (.const 1),
    t.map Sum.inl, fun v => ?_⟩
  simp only [Set.mem_setOf_eq, ExpTerm.eval, ExpTerm.eval_map, Sum.elim_comp_inl]
  constructor
  · intro h
    exact ⟨fun _ => t.eval v - s.eval v - 1, by simp [Sum.elim_inr]; omega⟩
  · rintro ⟨w, hw⟩
    simp only [Sum.elim_inr] at hw
    omega

/-- Divisibility between exponential terms, via a cofactor witness. -/
theorem of_dvd {s t : ExpTerm α} : ExpDioph {v | s.eval v ∣ t.eval v} := by
  refine ⟨Unit, .mul (s.map Sum.inl) (.var (Sum.inr ())), t.map Sum.inl, fun v => ?_⟩
  simp only [Set.mem_setOf_eq, ExpTerm.eval, ExpTerm.eval_map, Sum.elim_comp_inl]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨fun _ => c, by simp [Sum.elim_inr, hc]⟩
  · rintro ⟨w, hw⟩
    simp only [Sum.elim_inr] at hw
    exact ⟨w (), hw.symm⟩

/-- Any equation between exponential terms with no witnesses is exponential Diophantine. -/
theorem of_eq {s t : ExpTerm α} : ExpDioph {v | s.eval v = t.eval v} := by
  refine ⟨PEmpty, s.map Sum.inl, t.map Sum.inl, fun v => ?_⟩
  simp only [Set.mem_setOf_eq, ExpTerm.eval_map]
  exact ⟨fun h => ⟨PEmpty.elim, by simpa using h⟩, fun ⟨_, hw⟩ => by simpa using hw⟩

/-- The trivial condition. Needed as the base case of a finite conjunction, and as the branch
a statically false side condition collapses to. -/
theorem of_true : ExpDioph (Set.univ : Set (α → ℕ)) :=
  (of_eq (s := (.const 0 : ExpTerm α)) (t := .const 0)).congr fun _ => by simp

/-- A conjunction indexed by a list. Distinct from `ex`, whose quantifier ranges over an input
of the problem: the length here is fixed when the condition is written down. -/
theorem list_and {ι : Type} {S : ι → Set (α → ℕ)} (h : ∀ i, ExpDioph (S i)) :
    ∀ l : List ι, ExpDioph {v | ∀ i ∈ l, v ∈ S i}
  | [] => of_true.congr fun _ => by simp
  | i :: l => (((h i).and (list_and h l)).congr fun v => by
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, List.mem_cons]
      constructor
      · rintro ⟨hi, hl⟩ j (rfl | hj)
        · exact hi
        · exact hl j hj
      · intro hall
        exact ⟨hall i (Or.inl rfl), fun j hj => hall j (Or.inr hj)⟩)

/-- **A finite conjunction over a fixed index type.** The number of conjuncts is determined by
the problem, not by its input, so this adds no quantifier: it unfolds to nested `and`. -/
theorem fin_and {ι : Type} [Finite ι] {S : ι → Set (α → ℕ)} (h : ∀ i, ExpDioph (S i)) :
    ExpDioph {v | ∀ i, v ∈ S i} := by
  have : Fintype ι := Fintype.ofFinite ι
  exact (list_and h (Finset.univ : Finset ι).toList).congr fun v => by
    simp [Finset.mem_toList]

end ExpDioph

/-! ### Finite sums of terms

A coefficient-weighted sum over a fixed index type is a term, built by folding: again the
length is fixed when the term is written down. -/

namespace ExpTerm

/-- The sum of a finite family of terms. -/
noncomputable def sumTerm {ι : Type} [Fintype ι] (t : ι → ExpTerm α) : ExpTerm α :=
  (((Finset.univ : Finset ι).toList).map t).foldr ExpTerm.add (ExpTerm.const 0)

theorem eval_foldr_add (v : α → ℕ) :
    ∀ l : List (ExpTerm α),
      (l.foldr ExpTerm.add (ExpTerm.const 0)).eval v = (l.map (fun t => t.eval v)).sum
  | [] => rfl
  | t :: l => by
    simp only [List.foldr_cons, List.map_cons, List.sum_cons, eval]
    rw [eval_foldr_add v l]

@[simp] theorem eval_sumTerm {ι : Type} [Fintype ι] (t : ι → ExpTerm α) (v : α → ℕ) :
    (sumTerm t).eval v = ∑ i, (t i).eval v := by
  rw [sumTerm, eval_foldr_add, List.map_map]
  exact Finset.sum_map_toList Finset.univ fun i => (t i).eval v

end ExpTerm

/-! ### Acceptance tests

Nested powers are the case a representation that does not really compose fails on, so the
layer is exercised on one before anything is built above it.
-/

/-- A nested power: `2 ^ (2 ^ x₀) = x₁` is exponential Diophantine, and hence Diophantine. -/
theorem expDioph_two_pow_two_pow {α : Type} (i j : α) :
    ExpDioph {v : α → ℕ | 2 ^ (2 ^ v i) = v j} :=
  ExpDioph.of_eq (s := .pow (.const 2) (.pow (.const 2) (.var i))) (t := .var j)

theorem dioph_two_pow_two_pow {α : Type} (i j : α) :
    Dioph {v : α → ℕ | 2 ^ (2 ^ v i) = v j} :=
  (expDioph_two_pow_two_pow i j).dioph

/-- A term mixing every constructor, to check the induction covers them together. -/
theorem dioph_mixed {α : Type} (i j : α) :
    Dioph {v : α → ℕ | (v i ^ v j + v i * v j) / (v j % 3 + 1) = v i} :=
  (ExpDioph.of_eq
    (s := .div (.add (.pow (.var i) (.var j)) (.mul (.var i) (.var j)))
      (.add (.mod (.var j) (.const 3)) (.const 1)))
    (t := .var i)).dioph

end Hilbert10


/- Source: Hilbert10.Internal.TupleCoding, Hilbert10 v2.3.0, Apache-2.0. -/
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# Coding a finite tuple as one natural number

Issue #23, second part, and nothing more: a machine consumes one natural number, while an
`n`-ary predicate receives a `Fin n → ℕ`. Bridging that needs an encoding which is at once
computable to invert and Diophantine to impose.

## Why it is written out rather than imported

`Primcodable (Fin n → ℕ)` already provides an encoding, but an opaque one: its graph is not
known to be Diophantine, and assuming it were would beg the question. The temptation to reach
for "`Dioph` is closed under computable preimages" is worse — that statement *is* DPRM, so using
it here would be circular. So the encoding is an explicit right-associated `Nat.pair`, whose
graph is Diophantine because `Nat.pair` is piecewise polynomial.

Only two properties are needed, and they point in opposite directions:

* `tupleDecode_tupleCode` with `computable_tupleDecode` — the decoder is computable, which is
  what transports a recursively enumerable predicate on tuples to one on `ℕ`;
* `expDioph_tupleCode_graph` — the encoder's graph is exponential Diophantine, which is what
  transports the resulting Diophantine condition back to tuples.

This is deliberately not a coded-sequence library: there is no lookup, no length, no
concatenation, and `n` is fixed in every statement.

## Main results

* `Hilbert10.tupleDecode_tupleCode`, `Hilbert10.computable_tupleDecode`
* `Hilbert10.expDioph_tupleCode_graph`
-/

namespace Hilbert10

variable {α : Type}

/-! ### The encoding -/

/-- A tuple as one number, pairing to the right. -/
def tupleCode : {n : ℕ} → (Fin n → ℕ) → ℕ
  | 0, _ => 0
  | _ + 1, v => Nat.pair (v 0) (tupleCode fun i => v i.succ)

/-- Drop the first `i` components of a code. -/
def tupleDrop : ℕ → ℕ → ℕ
  | 0, z => z
  | i + 1, z => tupleDrop i z.unpair.2

/-- The decoder: component `i` is the first half of what is left after dropping `i`. -/
def tupleDecode (n : ℕ) (z : ℕ) : Fin n → ℕ := fun i => (tupleDrop i z).unpair.1

@[simp] theorem tupleCode_zero (v : Fin 0 → ℕ) : tupleCode v = 0 := rfl

theorem tupleCode_succ {n : ℕ} (v : Fin (n + 1) → ℕ) :
    tupleCode v = Nat.pair (v 0) (tupleCode fun i => v i.succ) := rfl

/-- **The round trip.** -/
theorem tupleDecode_tupleCode : ∀ {n : ℕ} (v : Fin n → ℕ), tupleDecode n (tupleCode v) = v
  | 0, v => funext fun i => i.elim0
  | n + 1, v => by
    funext i
    refine Fin.cases ?_ ?_ i
    · change (tupleDrop 0 (tupleCode v)).unpair.1 = v 0
      rw [tupleCode_succ]
      simp [tupleDrop]
    · intro j
      change (tupleDrop ((j : ℕ) + 1) (tupleCode v)).unpair.1 = v j.succ
      rw [tupleCode_succ]
      have : tupleDrop ((j : ℕ) + 1) (Nat.pair (v 0) (tupleCode fun i => v i.succ))
          = tupleDrop (j : ℕ) (tupleCode fun i => v i.succ) := by
        simp [tupleDrop]
      rw [this]
      exact congrFun (tupleDecode_tupleCode (fun i => v i.succ)) j

/-! ### The decoder is computable -/

private theorem computable_tupleDrop (i : ℕ) : Computable (tupleDrop i) := by
  induction i with
  | zero => exact Computable.id
  | succ i ih =>
    have h : Computable fun z : ℕ => z.unpair.2 :=
      Computable.snd.comp (Primrec.unpair.to_comp)
    exact (ih.comp h).of_eq fun z => rfl

/-- The decoder at a fixed arity is computable. Transferred through the `List.Vector`
equivalence that `Primcodable (Fin n → ℕ)` is built from. -/
theorem computable_tupleDecode (n : ℕ) : Computable (tupleDecode n) := by
  have h1 : Computable fun z : ℕ =>
      List.Vector.ofFn (fun i : Fin n => (tupleDrop i z).unpair.1) :=
    Computable.vector_ofFn fun i => Computable.fst.comp
      (Primrec.unpair.to_comp.comp (computable_tupleDrop i))
  have h2 := (Primrec.of_equiv_symm (e := (Equiv.vectorEquivFin ℕ n).symm)).to_comp.comp h1
  refine h2.of_eq fun z => ?_
  funext i
  simp [Equiv.vectorEquivFin, tupleDecode]

/-! ### The encoder's graph is exponential Diophantine -/

/-- `Nat.pair` is piecewise polynomial, so its graph is a union of two polynomial conditions. -/
theorem expDioph_pair (a b c : ExpTerm α) :
    ExpDioph {v : α → ℕ | Nat.pair (a.eval v) (b.eval v) = c.eval v} := by
  refine (ExpDioph.or
    (ExpDioph.and (ExpDioph.of_lt (s := a) (t := b))
      (ExpDioph.of_eq (s := c) (t := .add (.mul b b) a)))
    (ExpDioph.and (ExpDioph.of_le (s := b) (t := a))
      (ExpDioph.of_eq (s := c) (t := .add (.add (.mul a a) a) b)))).congr fun v => ?_
  simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq, ExpTerm.eval, Nat.pair]
  by_cases h : a.eval v < b.eval v
  · rw [if_pos h]
    constructor
    · rintro (⟨-, hc⟩ | ⟨hle, -⟩)
      · exact hc.symm
      · omega
    · intro hc
      exact Or.inl ⟨h, hc.symm⟩
  · rw [if_neg h]
    constructor
    · rintro (⟨hlt, -⟩ | ⟨-, hc⟩)
      · omega
      · exact hc.symm
    · intro hc
      exact Or.inr ⟨by omega, hc.symm⟩

/-- **The encoder's graph.** The tuple sits on `Fin n` variables and its code on the extra one;
the induction adds one existential per component, which is `finite existential composition` and
not a quantifier over anything the problem supplies. -/
theorem expDioph_tupleCode_graph :
    ∀ n : ℕ, ExpDioph {u : (Fin n ⊕ Unit) → ℕ |
      tupleCode (fun i => u (.inl i)) = u (.inr ())}
  | 0 => by
    refine (ExpDioph.of_eq (s := .const 0) (t := .var (.inr ()))).congr fun u => ?_
    simp [Set.mem_setOf_eq, ExpTerm.eval]
  | n + 1 => by
    -- `f` places the induction hypothesis' variables inside the larger block
    let f : Fin n ⊕ Unit → (Fin (n + 1) ⊕ Unit) ⊕ Unit :=
      Sum.elim (fun i => .inl (.inl i.succ)) (fun _ => .inr ())
    refine (ExpDioph.congr (ExpDioph.ex (ExpDioph.and
      (ExpDioph.reindex (expDioph_tupleCode_graph n) f)
      (expDioph_pair (.var (.inl (.inl 0))) (.var (.inr ())) (.var (.inl (.inr ()))))))
      fun u => ?_)
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Function.comp, ExpTerm.eval, f,
      Sum.elim_inl, Sum.elim_inr, tupleCode_succ]
    constructor
    · rintro ⟨w, h1, h2⟩
      rw [← h2, h1]
    · intro h
      exact ⟨fun _ => tupleCode (fun i : Fin n => u (.inl i.succ)), rfl, by rw [← h]⟩

end Hilbert10


/- Source: Hilbert10.Internal.ConfigCoding, Hilbert10 v2.3.0, Apache-2.0. -/
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# Configurations as numbers, and one step as arithmetic

Issue #45, the first child of #21. A configuration of a `k`-register machine becomes a single
natural number written in base `2 ^ w`:

```
digit 0     = pc
digit i + 1 = register i
```

and one step of a *fixed* program becomes a relation between two such numbers.

## What is deliberately absent

There is no encoding of `Instr` or of `Program`, no universal interpreter, and no computable
lookup into an encoded program. #20's endpoint is `exists_machine_graph`, so the program is
obtained by existential elimination and is fixed from then on; its instruction list is finite,
and `EncodedStep` is a finite disjunction over it, built nonuniformly by recursion on the list.
An encoding of the program itself would be a universal machine, which nothing here needs.

## Total, permissive semantics

`configField` and `setField` are total: every natural number has fields, and every field can be
overwritten. Bounds are not part of the definitions but hypotheses on the theorems, saying when
a number *represents* the configuration one has in mind. This is the same discipline as
`Function.extend` in `CleanScratch`: no partiality, no well-formedness predicate threaded
through every statement.

## Composition with `BlockPacking`

`FitsConfig` gives `configCode w c < (2 ^ w) ^ (k + 1) = 2 ^ (w * (k + 1))`, so a run of these
configurations packs into `BlockPacking`'s already-proved one-guard-bit layout at data width
`w * (k + 1)`. That is what #47 and #48 consume; choosing `w` large enough is #46's job.

## Main definitions

* `RegisterMachine.configField`, `setField` — reading and writing one base-`2 ^ w` field
* `RegisterMachine.configCode`, `FitsConfig` — a configuration as a number, and when it fits
* `RegisterMachine.decodeConfig` — and back, totally
* `RegisterMachine.EncodedStep` — one step of a fixed program, as a relation on codes

## Main results

* `RegisterMachine.field_configCode_zero`, `field_configCode_succ` — the fields of a code
* `RegisterMachine.configCode_lt`, `configCode_injective`
* `RegisterMachine.encodedStep_iff` — the headline: for an in-range fitting configuration,
  `EncodedStep` holds of exactly one successor, and it is the code of `step P c`
* `RegisterMachine.configCode_decodeConfig`, `decodeConfig_configCode` — the inverse pair
* `RegisterMachine.decodeConfig_step_of_encodedStep` — the decoded step relation, needing only
  a bound on the *predecessor*; this is why #48 does no carry reasoning
-/

namespace Hilbert10

namespace RegisterMachine

variable {k : ℕ}

/-! ### Reading a field

`configField w code i` is digit `i` of `code` in base `2 ^ w`. Total: no bounds are assumed. -/

/-- Digit `i` of `code`, reading `code` in base `2 ^ w`. -/
def configField (w code i : ℕ) : ℕ := code / (2 ^ w) ^ i % 2 ^ w

theorem configField_zero (w x : ℕ) : configField w x 0 = x % 2 ^ w := by
  simp [configField]

theorem configField_succ (w x i : ℕ) : configField w x (i + 1) = configField w (x / 2 ^ w) i := by
  rw [configField, configField, Nat.div_div_eq_div_mul,
    show (2 ^ w) ^ (i + 1) = 2 ^ w * (2 ^ w) ^ i by ring]

theorem configField_lt (w x i : ℕ) : configField w x i < 2 ^ w :=
  Nat.mod_lt _ (Nat.two_pow_pos w)

/-- Fields below `i` depend only on `code % (2 ^ w) ^ i`. -/
theorem configField_of_mod {w x i j : ℕ} (hj : j < i) :
    configField w (x % (2 ^ w) ^ i) j = configField w x j := by
  have key : ∀ y : ℕ, configField w y j = y % (2 ^ w) ^ (j + 1) / (2 ^ w) ^ j := by
    intro y
    rw [configField, show (2 ^ w) ^ (j + 1) = (2 ^ w) ^ j * 2 ^ w by ring,
      Nat.mod_mul_right_div_self]
  rw [key, key, Nat.mod_mod_of_dvd _ (pow_dvd_pow _ hj)]

/-- Fields above `i` depend only on `code / (2 ^ w) ^ (i + 1)`. -/
theorem configField_div {w x i j : ℕ} (h : i < j) :
    configField w (x / (2 ^ w) ^ (i + 1)) (j - (i + 1)) = configField w x j := by
  rw [configField, configField, Nat.div_div_eq_div_mul, ← pow_add,
    show i + 1 + (j - (i + 1)) = j by omega]

/-! ### Writing a field -/

/-- Overwrite digit `i` of `code` with `value`, in base `2 ^ w`. Total: the low part is kept,
the old digit dropped, and the high part shifted back into place. -/
def setField (w code i value : ℕ) : ℕ :=
  code % (2 ^ w) ^ i + value * (2 ^ w) ^ i + code / (2 ^ w) ^ (i + 1) * (2 ^ w) ^ (i + 1)

/-- `setField` regrouped so that everything above digit `i` is a single multiple of
`(2 ^ w) ^ i`. Every lemma below is a division or a modulus applied to this form. -/
theorem setField_eq (w code i value : ℕ) :
    setField w code i value
      = code % (2 ^ w) ^ i + (value + code / (2 ^ w) ^ (i + 1) * 2 ^ w) * (2 ^ w) ^ i := by
  rw [setField, show (2 ^ w) ^ (i + 1) = (2 ^ w) ^ i * 2 ^ w by ring]
  ring

theorem setField_mod (w code i value : ℕ) :
    setField w code i value % (2 ^ w) ^ i = code % (2 ^ w) ^ i := by
  rw [setField_eq, Nat.add_mul_mod_self_right, Nat.mod_mod_of_dvd _ dvd_rfl]

/-- The written value is bounded, so the high part is untouched. -/
theorem setField_div {w code i value : ℕ} (hv : value < 2 ^ w) :
    setField w code i value / (2 ^ w) ^ (i + 1) = code / (2 ^ w) ^ (i + 1) := by
  have hlow : code % (2 ^ w) ^ i + value * (2 ^ w) ^ i < (2 ^ w) ^ (i + 1) := by
    calc code % (2 ^ w) ^ i + value * (2 ^ w) ^ i
        < (2 ^ w) ^ i + value * (2 ^ w) ^ i :=
          by have := Nat.mod_lt code (y := (2 ^ w) ^ i) (pow_pos (Nat.two_pow_pos w) i); omega
      _ = (value + 1) * (2 ^ w) ^ i := by ring
      _ ≤ 2 ^ w * (2 ^ w) ^ i := Nat.mul_le_mul_right _ hv
      _ = (2 ^ w) ^ (i + 1) := by ring
  rw [show setField w code i value
      = code % (2 ^ w) ^ i + value * (2 ^ w) ^ i
        + code / (2 ^ w) ^ (i + 1) * (2 ^ w) ^ (i + 1) from rfl,
    Nat.add_mul_div_right _ _ (pow_pos (Nat.two_pow_pos w) (i + 1)), Nat.div_eq_of_lt hlow,
    Nat.zero_add]

/-- **Read after write.** -/
theorem configField_setField_self {w code i value : ℕ} (hv : value < 2 ^ w) :
    configField w (setField w code i value) i = value := by
  rw [configField, setField_eq,
    Nat.add_mul_div_right _ _ (pow_pos (Nat.two_pow_pos w) i),
    Nat.div_eq_of_lt (Nat.mod_lt code (y := (2 ^ w) ^ i) (pow_pos (Nat.two_pow_pos w) i)),
    Nat.zero_add,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hv]

/-- **Read another field.** -/
theorem configField_setField_of_ne {w code i value j : ℕ} (hv : value < 2 ^ w) (hj : j ≠ i) :
    configField w (setField w code i value) j = configField w code j := by
  rcases Nat.lt_or_ge j i with h | h
  · rw [← configField_of_mod h, setField_mod, configField_of_mod h]
  · have h : i < j := by omega
    rw [← configField_div h, setField_div hv, configField_div h]

/-- Writing a field inside range keeps the number inside range. -/
theorem setField_lt {w n code i value : ℕ} (hc : code < (2 ^ w) ^ n) (hi : i < n)
    (hv : value < 2 ^ w) : setField w code i value < (2 ^ w) ^ n := by
  have hlow : code % (2 ^ w) ^ i + value * (2 ^ w) ^ i < (2 ^ w) ^ (i + 1) := by
    calc code % (2 ^ w) ^ i + value * (2 ^ w) ^ i
        < (2 ^ w) ^ i + value * (2 ^ w) ^ i :=
          by have := Nat.mod_lt code (y := (2 ^ w) ^ i) (pow_pos (Nat.two_pow_pos w) i); omega
      _ = (value + 1) * (2 ^ w) ^ i := by ring
      _ ≤ 2 ^ w * (2 ^ w) ^ i := Nat.mul_le_mul_right _ hv
      _ = (2 ^ w) ^ (i + 1) := by ring
  have hhigh : code / (2 ^ w) ^ (i + 1) < (2 ^ w) ^ (n - (i + 1)) := by
    refine Nat.div_lt_of_lt_mul ?_
    calc code < (2 ^ w) ^ n := hc
      _ = (2 ^ w) ^ (i + 1) * (2 ^ w) ^ (n - (i + 1)) := by
          rw [← pow_add]; congr 1; omega
  calc setField w code i value
      = code % (2 ^ w) ^ i + value * (2 ^ w) ^ i
        + code / (2 ^ w) ^ (i + 1) * (2 ^ w) ^ (i + 1) := rfl
    _ < (2 ^ w) ^ (i + 1) + code / (2 ^ w) ^ (i + 1) * (2 ^ w) ^ (i + 1) := by omega
    _ = (code / (2 ^ w) ^ (i + 1) + 1) * (2 ^ w) ^ (i + 1) := by ring
    _ ≤ (2 ^ w) ^ (n - (i + 1)) * (2 ^ w) ^ (i + 1) := Nat.mul_le_mul_right _ hhigh
    _ = (2 ^ w) ^ n := by rw [← pow_add]; congr 1; omega

/-! ### Codes of field vectors -/

/-- The base-`2 ^ w` code of a field vector: `f i` in place `i`. -/
def fieldsCode (w : ℕ) : {n : ℕ} → (Fin n → ℕ) → ℕ
  | 0, _ => 0
  | _ + 1, f => f 0 + 2 ^ w * fieldsCode w (f ∘ Fin.succ)

theorem fieldsCode_succ (w n : ℕ) (f : Fin (n + 1) → ℕ) :
    fieldsCode w f = f 0 + 2 ^ w * fieldsCode w (f ∘ Fin.succ) := rfl

theorem fieldsCode_lt {w : ℕ} : ∀ {n : ℕ} {f : Fin n → ℕ}, (∀ i, f i < 2 ^ w) →
    fieldsCode w f < (2 ^ w) ^ n := by
  intro n
  induction n with
  | zero => intro f _; simp [fieldsCode]
  | succ n ih =>
    intro f hf
    have hrest : fieldsCode w (f ∘ Fin.succ) < (2 ^ w) ^ n := ih fun i => hf i.succ
    calc fieldsCode w f = f 0 + 2 ^ w * fieldsCode w (f ∘ Fin.succ) := rfl
      _ < 2 ^ w + 2 ^ w * fieldsCode w (f ∘ Fin.succ) := by have := hf 0; omega
      _ = 2 ^ w * (fieldsCode w (f ∘ Fin.succ) + 1) := by ring
      _ ≤ 2 ^ w * (2 ^ w) ^ n := Nat.mul_le_mul_left _ hrest
      _ = (2 ^ w) ^ (n + 1) := by ring

@[simp] theorem fieldsCode_const_zero (w : ℕ) : ∀ {n : ℕ}, fieldsCode w (fun _ : Fin n => 0) = 0
  | 0 => rfl
  | n + 1 => by
    rw [fieldsCode_succ, show ((fun _ : Fin (n + 1) => 0) ∘ Fin.succ) = fun _ : Fin n => 0 from rfl,
      fieldsCode_const_zero w]
    simp

theorem field_fieldsCode {w : ℕ} : ∀ {n : ℕ} {f : Fin n → ℕ}, (∀ i, f i < 2 ^ w) →
    ∀ i : Fin n, configField w (fieldsCode w f) i = f i := by
  intro n
  induction n with
  | zero => intro f _ i; exact i.elim0
  | succ n ih =>
    intro f hf i
    refine Fin.cases ?_ ?_ i
    · rw [show ((0 : Fin (n + 1)) : ℕ) = 0 from rfl, fieldsCode_succ, configField_zero,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hf 0)]
    · intro j
      rw [Fin.val_succ, configField_succ, fieldsCode_succ,
        Nat.add_mul_div_left _ _ (Nat.two_pow_pos w), Nat.div_eq_of_lt (hf 0), Nat.zero_add]
      exact ih (fun i => hf i.succ) j

/-- Every number below `(2 ^ w) ^ n` is the code of its own first `n` fields. -/
theorem fieldsCode_configField {w : ℕ} : ∀ {n z : ℕ}, z < (2 ^ w) ^ n →
    fieldsCode w (fun i : Fin n => configField w z i) = z := by
  intro n
  induction n with
  | zero => intro z hz; simp only [pow_zero] at hz; simpa [fieldsCode] using (by omega : 0 = z)
  | succ n ih =>
    intro z hz
    have hz' : z / 2 ^ w < (2 ^ w) ^ n := by
      refine Nat.div_lt_of_lt_mul ?_
      calc z < (2 ^ w) ^ (n + 1) := hz
        _ = 2 ^ w * (2 ^ w) ^ n := by ring
    rw [fieldsCode_succ,
      show ((fun i : Fin (n + 1) => configField w z i) ∘ Fin.succ)
          = fun i : Fin n => configField w (z / 2 ^ w) i from by
        funext i; simp only [Function.comp_apply, Fin.val_succ]; exact configField_succ w z i,
      ih hz', show ((0 : Fin (n + 1)) : ℕ) = 0 from rfl, configField_zero]
    exact Nat.mod_add_div z (2 ^ w)

/-- Two numbers below `(2 ^ w) ^ n` with the same first `n` fields are equal. This is the
extensionality principle every `configCode` computation below goes through. -/
theorem eq_of_configField_eq {w n x y : ℕ} (hx : x < (2 ^ w) ^ n) (hy : y < (2 ^ w) ^ n)
    (h : ∀ i < n, configField w x i = configField w y i) : x = y := by
  rw [← fieldsCode_configField hx, ← fieldsCode_configField hy]
  exact congrArg _ (funext fun i => h i i.isLt)

/-! ### Configurations -/

/-- A configuration as a number: the program counter in digit `0`, register `i` in digit
`i + 1`, base `2 ^ w`. -/
def configCode (w : ℕ) (c : Config k) : ℕ := fieldsCode w (@Fin.cons k (fun _ => ℕ) c.pc c.regs)

/-- `c` fits in width `w` when its program counter and every register are below `2 ^ w`. -/
def FitsConfig (w : ℕ) (c : Config k) : Prop := c.pc < 2 ^ w ∧ ∀ r, c.regs r < 2 ^ w

theorem configFields_lt {w : ℕ} {c : Config k} (h : FitsConfig w c) :
    ∀ i : Fin (k + 1), @Fin.cons k (fun _ => ℕ) c.pc c.regs i < 2 ^ w := by
  intro i
  refine Fin.cases ?_ ?_ i
  · simpa using h.1
  · intro r; simpa using h.2 r

theorem field_configCode_zero {w : ℕ} {c : Config k} (h : FitsConfig w c) :
    configField w (configCode w c) 0 = c.pc := by
  have := field_fieldsCode (configFields_lt h) 0
  simpa [configCode] using this

theorem field_configCode_succ {w : ℕ} {c : Config k} (h : FitsConfig w c) (r : Fin k) :
    configField w (configCode w c) ((r : ℕ) + 1) = c.regs r := by
  have := field_fieldsCode (configFields_lt h) r.succ
  simpa [configCode] using this

theorem configCode_lt {w : ℕ} {c : Config k} (h : FitsConfig w c) :
    configCode w c < (2 ^ w) ^ (k + 1) :=
  fieldsCode_lt (configFields_lt h)

/-- The bound in the shape `BlockPacking` wants: a configuration is a datum of width
`w * (k + 1)`. -/
theorem configCode_lt_two_pow {w : ℕ} {c : Config k} (h : FitsConfig w c) :
    configCode w c < 2 ^ (w * (k + 1)) := by
  rw [pow_mul]; exact configCode_lt h

theorem configCode_injective {w : ℕ} {c₁ c₂ : Config k} (h₁ : FitsConfig w c₁)
    (h₂ : FitsConfig w c₂) (h : configCode w c₁ = configCode w c₂) : c₁ = c₂ := by
  have hpc : c₁.pc = c₂.pc := by
    rw [← field_configCode_zero h₁, ← field_configCode_zero h₂, h]
  have hregs : c₁.regs = c₂.regs := by
    funext r
    rw [← field_configCode_succ h₁ r, ← field_configCode_succ h₂ r, h]
  obtain ⟨p₁, r₁⟩ := c₁
  obtain ⟨p₂, r₂⟩ := c₂
  simp only [Config.mk.injEq]
  exact ⟨hpc, hregs⟩

/-- The exhaustive partition of a field index: the program counter, or one register. -/
theorem index_cases {i : ℕ} (hi : i < k + 1) : i = 0 ∨ ∃ r : Fin k, (r : ℕ) + 1 = i := by
  cases i with
  | zero => exact Or.inl rfl
  | succ n => exact Or.inr ⟨⟨n, by omega⟩, rfl⟩

/-- Jumping: writing the program counter field is exactly the code of the jumped-to
configuration. -/
theorem configCode_setPc {w : ℕ} {c : Config k} (h : FitsConfig w c) {j : ℕ} (hj : j < 2 ^ w) :
    configCode w (⟨j, c.regs⟩ : Config k) = setField w (configCode w c) 0 j := by
  have hfit : FitsConfig w (⟨j, c.regs⟩ : Config k) := ⟨hj, h.2⟩
  refine eq_of_configField_eq (configCode_lt hfit)
    (setField_lt (configCode_lt h) (Nat.succ_pos k) hj) ?_
  intro i hi
  rcases index_cases hi with rfl | ⟨r, rfl⟩
  · rw [field_configCode_zero hfit, configField_setField_self hj]
  · rw [field_configCode_succ hfit r, configField_setField_of_ne hj (by omega),
      field_configCode_succ h r]

/-- Jumping and updating one register at once. Both machine instructions have this shape, and
this is the only place `configCode` is computed field by field. -/
theorem configCode_update {w : ℕ} {c : Config k} (h : FitsConfig w c) {j : ℕ} (hj : j < 2 ^ w)
    (r : Fin k) {v : ℕ} (hv : v < 2 ^ w) :
    configCode w (⟨j, Function.update c.regs r v⟩ : Config k)
      = setField w (setField w (configCode w c) 0 j) ((r : ℕ) + 1) v := by
  have hfit : FitsConfig w (⟨j, Function.update c.regs r v⟩ : Config k) := by
    refine ⟨hj, fun s => ?_⟩
    rcases eq_or_ne s r with rfl | hs
    · simpa using hv
    · simpa [Function.update_of_ne hs] using h.2 s
  have hr : (r : ℕ) + 1 < k + 1 := by have := r.isLt; omega
  refine eq_of_configField_eq (configCode_lt hfit)
    (setField_lt (setField_lt (configCode_lt h) (Nat.succ_pos k) hj) hr hv) ?_
  intro i hi
  rcases index_cases hi with rfl | ⟨s, rfl⟩
  · rw [field_configCode_zero hfit, configField_setField_of_ne hv (by omega),
      configField_setField_self hj]
  · rw [field_configCode_succ hfit s]
    rcases eq_or_ne s r with rfl | hs
    · rw [configField_setField_self hv]
      simp
    · have hsr : (s : ℕ) ≠ (r : ℕ) := fun hh => hs (Fin.ext hh)
      rw [configField_setField_of_ne hv (by omega), configField_setField_of_ne hj (by omega),
        field_configCode_succ h s]
      simp [Function.update_of_ne hs]

/-! ### Decoding

The inverse of `configCode`, total like everything else here. #48 runs it on every block of a
packed run, so it must not carry a fitting hypothesis. -/

/-- The configuration a number codes, read field by field. -/
def decodeConfig (w z : ℕ) : Config k :=
  ⟨configField w z 0, fun r => configField w z ((r : ℕ) + 1)⟩

/-- Unconditional: every extracted field is a remainder modulo `2 ^ w`. -/
theorem fits_decodeConfig {w z : ℕ} : FitsConfig w (decodeConfig (k := k) w z) :=
  ⟨configField_lt w z 0, fun r => configField_lt w z ((r : ℕ) + 1)⟩

theorem configCode_decodeConfig {w z : ℕ} (hz : z < 2 ^ (w * (k + 1))) :
    configCode w (decodeConfig (k := k) w z) = z := by
  rw [pow_mul] at hz
  rw [configCode,
    show @Fin.cons k (fun _ => ℕ) (decodeConfig (k := k) w z).pc (decodeConfig (k := k) w z).regs
        = fun i : Fin (k + 1) => configField w z i from by
      funext i
      refine Fin.cases ?_ ?_ i
      · rfl
      · intro r; rw [Fin.cons_succ, Fin.val_succ]; rfl]
  exact fieldsCode_configField hz

theorem decodeConfig_configCode {w : ℕ} {c : Config k} (hc : FitsConfig w c) :
    decodeConfig w (configCode w c) = c := by
  obtain ⟨p, r⟩ := c
  simp only [decodeConfig, Config.mk.injEq]
  exact ⟨field_configCode_zero hc, funext fun s => field_configCode_succ hc s⟩

/-! ### One step, as a relation on codes

The program is *fixed*. `EncodedStep` is a finite disjunction over its instruction list, built by
recursion on that list: nothing here encodes a program or looks an instruction up. -/

/-- The encoded effect of the single instruction `I` sitting at index `p`. The first conjunct
pins the program counter, which is what makes the disjunction below exclusive. -/
def Instr.EncodedStep (w p : ℕ) : Instr k → ℕ → ℕ → Prop
  | .inc r j => fun b a =>
      configField w b 0 = p ∧ j < 2 ^ w ∧ configField w b ((r : ℕ) + 1) + 1 < 2 ^ w ∧
        a = setField w (setField w b 0 j) ((r : ℕ) + 1) (configField w b ((r : ℕ) + 1) + 1)
  | .dec r jpos jzero => fun b a =>
      configField w b 0 = p ∧
        ((configField w b ((r : ℕ) + 1) = 0 ∧ jzero < 2 ^ w ∧ a = setField w b 0 jzero) ∨
          (0 < configField w b ((r : ℕ) + 1) ∧ jpos < 2 ^ w ∧
            a = setField w (setField w b 0 jpos) ((r : ℕ) + 1)
              (configField w b ((r : ℕ) + 1) - 1)))

/-- The disjunction over a suffix of the program whose first instruction sits at index `p`. -/
def encodedStepFrom (w : ℕ) : ℕ → Program k → ℕ → ℕ → Prop
  | _, [], _, _ => False
  | p, I :: rest, b, a => I.EncodedStep w p b a ∨ encodedStepFrom w (p + 1) rest b a

/-- **One step of a fixed program, as a relation between two codes.** -/
def EncodedStep (P : Program k) (w b a : ℕ) : Prop := encodedStepFrom w 0 P b a

/-- The disjunction, read as a bounded existential over instruction indices. -/
theorem encodedStepFrom_iff (w : ℕ) : ∀ (L : Program k) (p b a : ℕ),
    encodedStepFrom w p L b a ↔ ∃ q, ∃ _ : q < L.length, (L[q]).EncodedStep w (p + q) b a := by
  intro L
  induction L with
  | nil => intro p b a; simp [encodedStepFrom]
  | cons I rest ih =>
    intro p b a
    rw [show encodedStepFrom w p (I :: rest) b a
        = (I.EncodedStep w p b a ∨ encodedStepFrom w (p + 1) rest b a) from rfl, ih]
    constructor
    · rintro (hI | ⟨q, hq, hstep⟩)
      · exact ⟨0, by simp, by simpa using hI⟩
      · exact ⟨q + 1, by simpa using hq, by simpa [Nat.add_assoc, Nat.add_comm 1 q] using hstep⟩
    · rintro ⟨q, hq, hstep⟩
      cases q with
      | zero => exact Or.inl (by simpa using hstep)
      | succ q =>
        refine Or.inr ⟨q, by simpa using hq, ?_⟩
        simpa [Nat.add_assoc, Nat.add_comm 1 q] using hstep

theorem encodedStep_iff_exists {P : Program k} {w b a : ℕ} :
    EncodedStep P w b a ↔ ∃ q, ∃ _ : q < P.length, (P[q]).EncodedStep w q b a := by
  rw [EncodedStep]
  simpa using encodedStepFrom_iff w P 0 b a

/-- The instruction at the current program counter, encoded, is satisfied by exactly the code of
the successor configuration — and only when that successor fits. -/
theorem instr_encodedStep_iff {P : Program k} {w : ℕ} {c : Config k} {z : ℕ}
    (hc : FitsConfig w c) (hpc : c.pc < P.length) :
    (P[c.pc]'hpc).EncodedStep w c.pc (configCode w c) z ↔
      FitsConfig w (step P c) ∧ z = configCode w (step P c) := by
  have hstep : step P c = (P[c.pc]'hpc).exec c.regs :=
    step_of_getElem? (List.getElem?_eq_getElem hpc)
  have hpc0 : configField w (configCode w c) 0 = c.pc := field_configCode_zero hc
  rcases hI : (P[c.pc]'hpc) with ⟨r, j⟩ | ⟨r, jpos, jzero⟩
  · -- `inc r j`
    have hexec : step P c = ⟨j, Function.update c.regs r (c.regs r + 1)⟩ := by
      rw [hstep, hI]; rfl
    have hreg : configField w (configCode w c) ((r : ℕ) + 1) = c.regs r :=
      field_configCode_succ hc r
    have hE : Instr.EncodedStep w c.pc (Instr.inc r j) (configCode w c) z ↔
        (j < 2 ^ w ∧ c.regs r + 1 < 2 ^ w ∧
          z = setField w (setField w (configCode w c) 0 j) ((r : ℕ) + 1) (c.regs r + 1)) := by
      rw [show Instr.EncodedStep w c.pc (Instr.inc r j) (configCode w c) z
          = (configField w (configCode w c) 0 = c.pc ∧ j < 2 ^ w ∧
              configField w (configCode w c) ((r : ℕ) + 1) + 1 < 2 ^ w ∧
              z = setField w (setField w (configCode w c) 0 j) ((r : ℕ) + 1)
                (configField w (configCode w c) ((r : ℕ) + 1) + 1)) from rfl, hreg]
      exact and_iff_right hpc0
    rw [hE, hexec]
    constructor
    · rintro ⟨hj, hv, hz⟩
      refine ⟨⟨hj, fun s => ?_⟩, by rw [hz, configCode_update hc hj r hv]⟩
      rcases eq_or_ne s r with rfl | hs
      · simpa using hv
      · simpa [Function.update_of_ne hs] using hc.2 s
    · rintro ⟨hfit, hz⟩
      have hj : j < 2 ^ w := hfit.1
      have hv : c.regs r + 1 < 2 ^ w := by simpa using hfit.2 r
      exact ⟨hj, hv, by rw [hz, configCode_update hc hj r hv]⟩
  · -- `dec r jpos jzero`
    have hreg : configField w (configCode w c) ((r : ℕ) + 1) = c.regs r :=
      field_configCode_succ hc r
    have hE : Instr.EncodedStep w c.pc (Instr.dec r jpos jzero) (configCode w c) z ↔
        ((c.regs r = 0 ∧ jzero < 2 ^ w ∧ z = setField w (configCode w c) 0 jzero) ∨
          (0 < c.regs r ∧ jpos < 2 ^ w ∧
            z = setField w (setField w (configCode w c) 0 jpos) ((r : ℕ) + 1)
              (c.regs r - 1))) := by
      rw [show Instr.EncodedStep w c.pc (Instr.dec r jpos jzero) (configCode w c) z
          = (configField w (configCode w c) 0 = c.pc ∧
              ((configField w (configCode w c) ((r : ℕ) + 1) = 0 ∧ jzero < 2 ^ w ∧
                  z = setField w (configCode w c) 0 jzero) ∨
                (0 < configField w (configCode w c) ((r : ℕ) + 1) ∧ jpos < 2 ^ w ∧
                  z = setField w (setField w (configCode w c) 0 jpos) ((r : ℕ) + 1)
                    (configField w (configCode w c) ((r : ℕ) + 1) - 1)))) from rfl,
        hreg]
      exact and_iff_right hpc0
    rw [hE]
    rcases Nat.eq_zero_or_pos (c.regs r) with hz | hz
    · have hexec : step P c = ⟨jzero, c.regs⟩ := by rw [hstep, hI]; simp [Instr.exec, hz]
      rw [hexec]
      constructor
      · rintro (⟨-, hj, h⟩ | ⟨h, -, -⟩)
        · exact ⟨⟨hj, hc.2⟩, by rw [h, configCode_setPc hc hj]⟩
        · omega
      · rintro ⟨hfit, h⟩
        exact Or.inl ⟨hz, hfit.1, by rw [h, configCode_setPc hc hfit.1]⟩
    · have hexec : step P c = ⟨jpos, Function.update c.regs r (c.regs r - 1)⟩ := by
        rw [hstep, hI]; simp [Instr.exec, Nat.ne_of_gt hz]
      have hv : c.regs r - 1 < 2 ^ w := by have := hc.2 r; omega
      rw [hexec]
      constructor
      · rintro (⟨h, -, -⟩ | ⟨-, hj, h⟩)
        · omega
        · refine ⟨⟨hj, fun s => ?_⟩, by rw [h, configCode_update hc hj r hv]⟩
          rcases eq_or_ne s r with rfl | hs
          · simpa using hv
          · simpa [Function.update_of_ne hs] using hc.2 s
      · rintro ⟨hfit, h⟩
        exact Or.inr ⟨hz, hfit.1, by rw [h, configCode_update hc hfit.1 r hv]⟩

/-- **The headline theorem.** For an in-range configuration that fits, the encoded step relation
holds of exactly one number, and only when the real successor fits too.

The successor-fit conjunct is not decoration. `setField` is permissive, so an out-of-range
written value carries into the next field and the resulting code is still bounded: with `w = 2`,
`[inc 0 1, dec 1 2 2]` from `⟨0, ![3, 0]⟩` would encode `⟨1, ![4, 0]⟩` as `17`, whose digits are
`(1, 0, 1)`, and the encoded run would then decrement the carried `1` and terminate at `0` where
the machine terminates at `4`. Every code stays below the bound throughout, so no outer block
constraint catches it. The per-instruction bound conjuncts are what rule it out, and #48 needs
them because the successor-fit hypothesis is not available during soundness.

Only in-range configurations get a case. `Accepts` never steps its terminal configuration, so
there is no out-of-range branch to add — and adding one would cost a disequality guard in every
disjunct downstream. -/
theorem encodedStep_iff {P : Program k} {w : ℕ} {c : Config k} {z : ℕ}
    (hc : FitsConfig w c) (hpc : c.pc < P.length) :
    EncodedStep P w (configCode w c) z ↔
      FitsConfig w (step P c) ∧ z = configCode w (step P c) := by
  rw [encodedStep_iff_exists]
  constructor
  · rintro ⟨q, hq, hstep⟩
    have hqc : q = c.pc := by
      rcases hI : (P[q]'hq) with ⟨r, j⟩ | ⟨r, jpos, jzero⟩ <;>
        · rw [hI] at hstep
          have := hstep.1
          rw [field_configCode_zero hc] at this
          omega
    subst hqc
    exact (instr_encodedStep_iff hc hpc).mp hstep
  · intro h
    exact ⟨c.pc, hpc, (instr_encodedStep_iff hc hpc).mpr h⟩

/-- Widening the field width preserves fitting. #46 chooses one width large enough for every
configuration of a run; this is what lets a per-configuration bound be promoted to it. -/
theorem FitsConfig.mono {w w' : ℕ} {c : Config k} (h : FitsConfig w c) (hw : w ≤ w') :
    FitsConfig w' c :=
  ⟨lt_of_lt_of_le h.1 (Nat.pow_le_pow_right (by norm_num) hw),
    fun r => lt_of_lt_of_le (h.2 r) (Nat.pow_le_pow_right (by norm_num) hw)⟩

/-- Soundness, in the form #48 uses: a related successor code *is* the code of the real
successor, and the real successor fits. No fit hypothesis about the successor is needed. -/
theorem eq_configCode_step_of_encodedStep {P : Program k} {w : ℕ} {c : Config k} {z : ℕ}
    (hc : FitsConfig w c) (hpc : c.pc < P.length) (h : EncodedStep P w (configCode w c) z) :
    FitsConfig w (step P c) ∧ z = configCode w (step P c) :=
  (encodedStep_iff hc hpc).mp h

/-- Completeness, in the form #47 uses: the intended successor is related. -/
theorem encodedStep_configCode {P : Program k} {w : ℕ} {c : Config k} (hc : FitsConfig w c)
    (hs : FitsConfig w (step P c)) (hpc : c.pc < P.length) :
    EncodedStep P w (configCode w c) (configCode w (step P c)) :=
  (encodedStep_iff hc hpc).mpr ⟨hs, rfl⟩

/-- Determinism. -/
theorem encodedStep_unique {P : Program k} {w : ℕ} {c : Config k} {z₁ z₂ : ℕ}
    (hc : FitsConfig w c) (hpc : c.pc < P.length)
    (h₁ : EncodedStep P w (configCode w c) z₁) (h₂ : EncodedStep P w (configCode w c) z₂) :
    z₁ = z₂ :=
  ((encodedStep_iff hc hpc).mp h₁).2.trans ((encodedStep_iff hc hpc).mp h₂).2.symm

/-- Nothing at all is related when the real successor overflows the width. This is the whole
content of the correction: an overflowing step is *unrepresentable* at that width rather than
represented wrongly, and #46's job is to choose a width where it never happens. -/
theorem not_encodedStep_of_not_fits {P : Program k} {w : ℕ} {c : Config k}
    (hc : FitsConfig w c) (hpc : c.pc < P.length) (hs : ¬ FitsConfig w (step P c)) (z : ℕ) :
    ¬ EncodedStep P w (configCode w c) z :=
  fun h => hs ((encodedStep_iff hc hpc).mp h).1

/-- The counterexample above, kept as a regression: at width `2` the machine's first step
overflows register `0`, and the strengthened relation has no successor for it. -/
example (z : ℕ) :
    ¬ EncodedStep ([.inc 0 1, .dec 1 2 2] : Program 2) 2
      (configCode 2 ⟨0, fun i : Fin 2 => if i = 0 then 3 else 0⟩) z := by
  refine not_encodedStep_of_not_fits ⟨by norm_num, fun r => ?_⟩ (by norm_num) (fun h => ?_) z
  · dsimp only; split <;> norm_num
  · have := h.2 0
    rw [show step ([.inc 0 1, .dec 1 2 2] : Program 2) ⟨0, fun i : Fin 2 => if i = 0 then 3 else 0⟩
        = ⟨1, Function.update (fun i : Fin 2 => if i = 0 then 3 else 0) 0 4⟩ from rfl] at this
    norm_num at this

/-! ### The seams #48 consumes

Both directions of the step relation, packaged so that all carry reasoning stays here. -/

/-- The program counter of a related code is in range. #48 needs this before it can apply
`encodedStep_iff`, and the relation already contains it: every disjunct pins the field. -/
theorem configField_zero_lt_of_encodedStep {P : Program k} {w b a : ℕ}
    (h : EncodedStep P w b a) : configField w b 0 < P.length := by
  obtain ⟨q, hq, hstep⟩ := encodedStep_iff_exists.mp h
  rcases hI : (P[q]'hq) with ⟨r, j⟩ | ⟨r, jpos, jzero⟩ <;>
    · rw [hI] at hstep
      rw [hstep.1]
      exact hq

/-- **Soundness of one step, decoded.** Only the bound on `b` is needed: the strengthened
`encodedStep_iff` already proves that the real successor fits and that `a` is its exact code. -/
theorem decodeConfig_step_of_encodedStep {P : Program k} {w b a : ℕ}
    (hb : b < 2 ^ (w * (k + 1))) (h : EncodedStep P w b a) :
    decodeConfig w a = step P (decodeConfig (k := k) w b) := by
  have hc : FitsConfig w (decodeConfig (k := k) w b) := fits_decodeConfig
  have hcode : configCode w (decodeConfig (k := k) w b) = b := configCode_decodeConfig hb
  have hpc : (decodeConfig (k := k) w b).pc < P.length :=
    configField_zero_lt_of_encodedStep h
  rw [← hcode] at h
  obtain ⟨hfit, ha⟩ := (encodedStep_iff hc hpc).mp h
  rw [ha, decodeConfig_configCode hfit]

end RegisterMachine

end Hilbert10


/- Source: Hilbert10.Internal.ConfigCodingDioph, Hilbert10 v2.3.0, Apache-2.0. -/
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# The encoded step relation is exponential Diophantine

The second half of #45. `ConfigCoding` proves that `EncodedStep` says exactly the right thing;
this file proves it is expressible.

The width is a *term*, not a numeral. Register values and run lengths grow with the input, so
`w` cannot be fixed in advance — choosing it is #46's job, and by then it has to be a variable of
the formula being built. Likewise `before` and `after` are arbitrary terms, because #49 instantiates
them with two block lookups into a single packed run.

Field indices, by contrast, *are* numerals: the program is fixed by the time this is used, so
each register index appearing in it is a concrete number.

## Main results

* `RegisterMachine.expDioph_encodedStep`
-/

namespace Hilbert10

namespace RegisterMachine

variable {α : Type} {k : ℕ}

/-! ### Terms for the field operations -/

/-- The base, `2 ^ w`, given a term for `w`. -/
def widthTerm (W : ExpTerm α) : ExpTerm α := .pow (.const 2) W

/-- Reading field `i`. -/
def fieldTerm (W t : ExpTerm α) (i : ℕ) : ExpTerm α :=
  .mod (.div t (.pow (widthTerm W) (.const i))) (widthTerm W)

@[simp] theorem eval_fieldTerm (W t : ExpTerm α) (i : ℕ) (v : α → ℕ) :
    (fieldTerm W t i).eval v = configField (W.eval v) (t.eval v) i := rfl

/-- Writing `u` into field `i`. -/
def setFieldTerm (W t : ExpTerm α) (i : ℕ) (u : ExpTerm α) : ExpTerm α :=
  .add (.add (.mod t (.pow (widthTerm W) (.const i))) (.mul u (.pow (widthTerm W) (.const i))))
    (.mul (.div t (.pow (widthTerm W) (.const (i + 1)))) (.pow (widthTerm W) (.const (i + 1))))

@[simp] theorem eval_setFieldTerm (W t : ExpTerm α) (i : ℕ) (u : ExpTerm α) (v : α → ℕ) :
    (setFieldTerm W t i u).eval v = setField (W.eval v) (t.eval v) i (u.eval v) := rfl

/-! ### Representability -/

/-- A single instruction's encoded effect is exponential Diophantine. -/
theorem expDioph_instrEncodedStep (W b a : ExpTerm α) (p : ℕ) (I : Instr k) :
    ExpDioph {v : α → ℕ | I.EncodedStep (W.eval v) p (b.eval v) (a.eval v)} := by
  cases I with
  | inc r j =>
    refine ExpDioph.congr
      (ExpDioph.and (ExpDioph.of_eq (s := fieldTerm W b 0) (t := .const p))
        (ExpDioph.and (ExpDioph.of_lt (s := .const j) (t := widthTerm W))
          (ExpDioph.and
            (ExpDioph.of_lt (s := .add (fieldTerm W b ((r : ℕ) + 1)) (.const 1))
              (t := widthTerm W))
            (ExpDioph.of_eq (s := a)
              (t := setFieldTerm W (setFieldTerm W b 0 (.const j)) ((r : ℕ) + 1)
                (.add (fieldTerm W b ((r : ℕ) + 1)) (.const 1))))))) ?_
    intro v
    simp [Instr.EncodedStep, ExpTerm.eval, widthTerm]
  | dec r jpos jzero =>
    refine ExpDioph.congr
      (ExpDioph.and (ExpDioph.of_eq (s := fieldTerm W b 0) (t := .const p))
        (ExpDioph.or
          (ExpDioph.and (ExpDioph.of_eq (s := fieldTerm W b ((r : ℕ) + 1)) (t := .const 0))
            (ExpDioph.and (ExpDioph.of_lt (s := .const jzero) (t := widthTerm W))
              (ExpDioph.of_eq (s := a) (t := setFieldTerm W b 0 (.const jzero)))))
          (ExpDioph.and (ExpDioph.of_lt (s := .const 0) (t := fieldTerm W b ((r : ℕ) + 1)))
            (ExpDioph.and (ExpDioph.of_lt (s := .const jpos) (t := widthTerm W))
              (ExpDioph.of_eq (s := a)
                (t := setFieldTerm W (setFieldTerm W b 0 (.const jpos)) ((r : ℕ) + 1)
                  (.sub (fieldTerm W b ((r : ℕ) + 1)) (.const 1)))))))) ?_
    intro v
    simp [Instr.EncodedStep, ExpTerm.eval, widthTerm]

/-- The disjunction over a suffix of the program. Recursion on the instruction list; each `::`
is one use of `ExpDioph.or`. -/
theorem expDioph_encodedStepFrom (W b a : ExpTerm α) : ∀ (L : Program k) (p : ℕ),
    ExpDioph {v : α → ℕ | encodedStepFrom (W.eval v) p L (b.eval v) (a.eval v)} := by
  intro L
  induction L with
  | nil =>
    intro p
    exact ExpDioph.congr ExpDioph.of_false fun v => by simp [encodedStepFrom]
  | cons I rest ih =>
    intro p
    refine ExpDioph.congr (ExpDioph.or (expDioph_instrEncodedStep W b a p I) (ih (p + 1))) ?_
    intro v
    simp [encodedStepFrom]

/-- **The step relation is exponential Diophantine**, hence Diophantine by `ExpDioph.dioph`.

The program is a fixed finite list, so this is a finite disjunction assembled nonuniformly —
no instruction is ever encoded, and no lookup is ever computed. -/
theorem expDioph_encodedStep (P : Program k) (W b a : ExpTerm α) :
    ExpDioph {v : α → ℕ | EncodedStep P (W.eval v) (b.eval v) (a.eval v)} :=
  expDioph_encodedStepFrom W b a P 0

theorem dioph_encodedStep (P : Program k) (W b a : ExpTerm α) :
    Dioph {v : α → ℕ | EncodedStep P (W.eval v) (b.eval v) (a.eval v)} :=
  (expDioph_encodedStep P W b a).dioph

end RegisterMachine

end Hilbert10


/- Source: Hilbert10.Internal.ForMathlib.ChooseDigit, Hilbert10 v2.3.0, Apache-2.0. -/
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# Binomial coefficients are base-`u` digits

The coefficient-extraction identity underlying #33: for a base large enough to hold every
coefficient, the binomial coefficients of `n` are literally the base-`u` digits of
`(u + 1) ^ n`.

```lean
n.choose k = ((2 ^ (n + 1) + 1) ^ n / (2 ^ (n + 1)) ^ k) % 2 ^ (n + 1)
```

Unconditional: for `k > n` the digit and the coefficient are both zero.

## Route

Mathlib's digits API does nearly all of it. The little-endian list `[n.choose 0, …, n.choose n]`
has base-`u` value `(u + 1) ^ n` by the binomial theorem; every entry is below `u` because
`n.choose k ≤ 2 ^ n < 2 ^ (n + 1)`; its last entry is `n.choose n = 1`, so `Nat.digits_ofDigits`
recovers the list on the nose; and `Nat.getD_digits` turns a list lookup into division and
modulus.

So no bespoke coefficient extraction is needed — the obstacle was already in mathlib.
-/

namespace Nat

/-- The base-`u` value of a list of the form `(range m).map f`. -/
private theorem ofDigits_range_map (u : ℕ) :
    ∀ (m : ℕ) (f : ℕ → ℕ),
      Nat.ofDigits u ((List.range m).map f) = ∑ i ∈ Finset.range m, f i * u ^ i := by
  intro m
  induction m with
  | zero => intro f; simp
  | succ m ih =>
    intro f
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, Nat.ofDigits_cons]
    simp only [Function.comp_def]
    rw [ih (fun i => f (i + 1)), Finset.sum_range_succ' (fun i => f i * u ^ i) m]
    simp only [pow_zero, mul_one, pow_succ, Finset.mul_sum]
    rw [add_comm]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring

/-- The digit list of `(u + 1) ^ n` in base `u`, when `u` is large enough. -/
private theorem digits_add_one_pow {u n : ℕ} (hu : 2 ^ n < u) :
    Nat.digits u ((u + 1) ^ n) = (List.range (n + 1)).map (n.choose ·) := by
  have hu1 : 1 < u := lt_of_le_of_lt (Nat.one_le_two_pow) hu
  have hval : Nat.ofDigits u ((List.range (n + 1)).map (n.choose ·)) = (u + 1) ^ n := by
    rw [ofDigits_range_map]
    rw [add_pow u 1 n]
    exact (Finset.sum_congr rfl fun i _ => by push_cast; ring).symm
  rw [← hval]
  refine Nat.digits_ofDigits u hu1 _ (fun l hl => ?_) (fun h => ?_)
  · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hl
    exact lt_of_le_of_lt (Nat.choose_le_two_pow n i) hu
  · rw [List.getLast_map, List.getLast_range]
    simp

/-- **Binomial coefficients are base-`u` digits.** Unconditional in `k`. -/
theorem choose_eq_baseDigit (n k : ℕ) :
    n.choose k = ((2 ^ (n + 1) + 1) ^ n / (2 ^ (n + 1)) ^ k) % 2 ^ (n + 1) := by
  set u := 2 ^ (n + 1) with hu
  have hun : 2 ^ n < u := by
    rw [hu]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hu2 : 2 ≤ u := by
    have : (2 : ℕ) ^ 1 ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    simpa using this
  have hgetD := Nat.getD_digits ((u + 1) ^ n) k hu2
  rw [digits_add_one_pow hun] at hgetD
  rw [← hgetD]
  -- the list lookup is the coefficient, on both sides of `k ≤ n`
  by_cases hk : k < n + 1
  · rw [List.getD_eq_getElem _ _ (by simpa using hk)]
    simp
  · rw [List.getD_eq_default _ _ (by simpa using Nat.not_lt.mp hk)]
    exact Nat.choose_eq_zero_of_lt (show n < k by omega)

end Nat


/- Source: Hilbert10.Internal.ForMathlib.BinarySubmask, Hilbert10 v2.3.0, Apache-2.0. -/
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# Binary submasks

Generic bit-level material, extracted from the route spike (#15) once it became clear the
proofs are about an arbitrary power-of-two boundary rather than anything in the machine
encoding. Nothing here mentions a machine, a block layout, or a guard bit.

`Nat.IsBinarySubmask` is stated on `Nat.testBit`, which is the canonical form for this
project: #18 consumes it directly, and #34's contract is phrased in terms of it.

## Main results

* `Nat.isBinarySubmask_two_pow_sub_one_iff`: being a submask of `2 ^ k - 1` is fitting in
  `k` bits.
* `Nat.isBinarySubmask_add_mul_two_pow_iff`: a submask condition splits at a power-of-two
  boundary, provided the low part fits below it.
-/

namespace Nat

/-- Every binary digit of `a` is at most the corresponding digit of `b`. -/
def IsBinarySubmask (a b : ℕ) : Prop := ∀ i, a.testBit i = true → b.testBit i = true

@[simp] theorem isBinarySubmask_zero_iff {x : ℕ} : IsBinarySubmask x 0 ↔ x = 0 := by
  constructor
  · intro h
    refine Nat.zero_of_testBit_eq_false fun i => ?_
    by_contra hc
    simpa using h i (by simpa using hc)
  · rintro rfl i hi
    simp at hi

theorem isBinarySubmask_refl (a : ℕ) : IsBinarySubmask a a := fun _ h => h

theorem IsBinarySubmask.trans {a b c : ℕ} (hab : IsBinarySubmask a b)
    (hbc : IsBinarySubmask b c) : IsBinarySubmask a c := fun i h => hbc i (hab i h)

/-- A number is a submask of `2 ^ k - 1` exactly when it fits in `k` bits, since `2 ^ k - 1`
is precisely the low `k` bits. -/
theorem isBinarySubmask_two_pow_sub_one_iff {k x : ℕ} :
    IsBinarySubmask x (2 ^ k - 1) ↔ x < 2 ^ k := by
  simp only [IsBinarySubmask, Nat.testBit_two_pow_sub_one, decide_eq_true_eq]
  constructor
  · intro h
    refine Nat.lt_pow_two_of_testBit x fun i hi => ?_
    by_contra hc
    exact absurd (h i (by simpa using hc)) (by omega)
  · intro hx i hi
    by_contra hik
    have hle : (2 : ℕ) ^ k ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hx hle)] at hi
    simp at hi

/-- A submask condition splits at a power-of-two boundary: below the boundary and above it
are independent bit ranges. The hypothesis is what makes `a` the low part. -/
theorem isBinarySubmask_add_mul_two_pow_iff {width x a b : ℕ} (ha : a < 2 ^ width) :
    IsBinarySubmask x (a + 2 ^ width * b) ↔
      IsBinarySubmask (x % 2 ^ width) a ∧ IsBinarySubmask (x / 2 ^ width) b := by
  have hmask : ∀ j, (a + 2 ^ width * b).testBit j =
      if j < width then a.testBit j else b.testBit (j - width) := by
    intro j
    have h : a + 2 ^ width * b = 2 ^ width * b + a := by omega
    rw [h, Nat.testBit_two_pow_mul_add b ha j]
  simp only [IsBinarySubmask, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow,
    Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro h
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · have := h i hi.2
      rw [hmask i, if_pos hi.1] at this
      exact this
    · have := h (i + width) hi
      rw [hmask _, if_neg (by omega)] at this
      simpa using this
  · rintro ⟨hlo, hhi⟩ i hi
    rw [hmask i]
    by_cases hiw : i < width
    · rw [if_pos hiw]
      exact hlo i ⟨hiw, hi⟩
    · rw [if_neg hiw]
      exact hhi (i - width) (by rwa [Nat.sub_add_cancel (by omega)])

end Nat


/- Source: Hilbert10.Internal.ForMathlib.SubmaskChoose, Hilbert10 v2.3.0, Apache-2.0. -/
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# Binary submasks and binomial parity

Issue #18: the bridge between the bit-level definition and the arithmetic one,

```lean
Nat.IsBinarySubmask k n ↔ Odd (n.choose k)
```

## Route

An adapter around mathlib's Lucas's theorem (`Choose.lucas_theorem_nat`) rather than a
development from Kummer. At `p = 2` Lucas gives

```
n.choose k ≡ ∏ i ∈ range a, (n / 2 ^ i % 2).choose (k / 2 ^ i % 2)   [MOD 2]
```

for any `a` with `n, k < 2 ^ a`. Each local factor is `(n.testBit i).toNat.choose
(k.testBit i).toNat`, and a four-way bit split shows it is `1` exactly when
`k.testBit i → n.testBit i`, and `0` otherwise. The product is odd exactly when every factor
is `1`, and bits at or above the bound vanish on both sides, so no condition on `a` survives
into the statement.

Taking `a := max n k + 1` therefore yields the theorem **unconditionally** — no `k ≤ n`
hypothesis and no separate `IsBinarySubmask k n → k ≤ n` lemma first. Kummer and the
`padicValNat` lemmas stay unused unless #33 turns out to need them.

Kept in a separate file so `BinarySubmask` remains importable by consumers that need only the
bit lemmas, without dragging in the `Choose` hierarchy.
-/

namespace Nat

/-- The local Lucas factor at bit `i`: `1` unless `k` has a bit that `n` lacks. -/
private theorem choose_bit_eq_one_iff (n k i : ℕ) :
    (n / 2 ^ i % 2).choose (k / 2 ^ i % 2) = 1 ↔ (k.testBit i = true → n.testBit i = true) := by
  rw [← toNat_testBit, ← toNat_testBit]
  cases hn : n.testBit i <;> cases hk : k.testBit i <;> simp

/-- Bits at or above a bound where both numbers vanish impose no constraint. -/
private theorem submask_iff_forall_lt {k n a : ℕ} (hk : k < 2 ^ a) :
    IsBinarySubmask k n ↔ ∀ i < a, k.testBit i = true → n.testBit i = true := by
  constructor
  · intro h i _ hi
    exact h i hi
  · intro h i hi
    by_cases hia : i < a
    · exact h i hia hi
    · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hk
        (Nat.pow_le_pow_right (by omega) (by omega)))] at hi
      simp at hi

/-- **Binary submask is binomial parity.** Unconditional: no `k ≤ n` hypothesis. -/
theorem isBinarySubmask_iff_odd_choose (k n : ℕ) :
    IsBinarySubmask k n ↔ Odd (n.choose k) := by
  classical
  set a := max n k + 1 with ha
  have hn : n < 2 ^ a := lt_of_le_of_lt (le_max_left n k) (by
    have := Nat.lt_two_pow_self (n := max n k)
    calc max n k < 2 ^ max n k := this
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by omega) (by omega))
  have hk : k < 2 ^ a := lt_of_le_of_lt (le_max_right n k) (by
    have := Nat.lt_two_pow_self (n := max n k)
    calc max n k < 2 ^ max n k := this
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by omega) (by omega))
  -- Lucas at `p = 2`
  have hluc : n.choose k ≡ ∏ i ∈ Finset.range a,
      (n / 2 ^ i % 2).choose (k / 2 ^ i % 2) [MOD 2] :=
    Choose.lucas_theorem_nat hn hk
  have hodd : Odd (n.choose k) ↔
      (∏ i ∈ Finset.range a, (n / 2 ^ i % 2).choose (k / 2 ^ i % 2)) % 2 = 1 := by
    rw [Nat.odd_iff]
    exact ⟨fun h => by rwa [← hluc], fun h => by rwa [hluc]⟩
  -- the product is odd exactly when every factor is one
  have hfac : ∀ i, (n / 2 ^ i % 2).choose (k / 2 ^ i % 2) ≤ 1 := by
    intro i
    rw [← toNat_testBit, ← toNat_testBit]
    cases n.testBit i <;> cases k.testBit i <;> simp
  have hprod : (∏ i ∈ Finset.range a, (n / 2 ^ i % 2).choose (k / 2 ^ i % 2)) % 2 = 1 ↔
      ∀ i ∈ Finset.range a, (n / 2 ^ i % 2).choose (k / 2 ^ i % 2) = 1 := by
    constructor
    · intro h i hi
      by_contra hne
      have hzero : (n / 2 ^ i % 2).choose (k / 2 ^ i % 2) = 0 := by
        have := hfac i; omega
      rw [Finset.prod_eq_zero hi hzero] at h
      simp at h
    · intro h
      have hone : (∏ i ∈ Finset.range a, (n / 2 ^ i % 2).choose (k / 2 ^ i % 2)) = 1 := by
        rw [Finset.prod_congr rfl h]
        simp
      rw [hone]
  rw [hodd, hprod, submask_iff_forall_lt hk]
  exact ⟨fun h i hi => (choose_bit_eq_one_iff n k i).mpr (h i (Finset.mem_range.mp hi)),
    fun h i hi => (choose_bit_eq_one_iff n k i).mp (h i (Finset.mem_range.mpr hi))⟩

end Nat


/- Source: Hilbert10.Internal.ExpDiophChoose, Hilbert10 v2.3.0, Apache-2.0. -/
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# Binomial coefficients and binary submasks are exponential Diophantine

Issues #33 and #34. Both reduce to packaging, now that `Nat.choose_eq_baseDigit` supplies the
coefficient extraction and `Nat.isBinarySubmask_iff_odd_choose` (#18) supplies the parity
bridge.

`chooseTerm` is **compositional over terms**, not over variable names, so it can be applied to
whatever expressions a machine encoding produces rather than only to atoms. It introduces no
new `ExpTerm` constructor: `pow`, `div` and `mod` already exist, which is precisely the reason
#16 made `div` and `mod` constructors rather than closure lemmas.

Kept in its own file so `ExpDioph` stays importable without the `Choose` hierarchy.
-/

namespace Hilbert10

variable {α : Type}

namespace ExpTerm

/-- The base used to read binomial coefficients off as digits: `2 ^ (n + 1)`. -/
private def chooseBase (n : ExpTerm α) : ExpTerm α := .pow (.const 2) (.add n (.const 1))

/-- `n.choose k`, as an exponential term in `n` and `k`. -/
def chooseTerm (n k : ExpTerm α) : ExpTerm α :=
  .mod (.div (.pow (.add (chooseBase n) (.const 1)) n) (.pow (chooseBase n) k)) (chooseBase n)

@[simp] theorem eval_chooseTerm (n k : ExpTerm α) (v : α → ℕ) :
    (chooseTerm n k).eval v = (n.eval v).choose (k.eval v) := by
  simp only [chooseTerm, chooseBase, eval]
  exact (Nat.choose_eq_baseDigit (n.eval v) (k.eval v)).symm

end ExpTerm

namespace ExpDioph

/-- **#33.** The graph of `Nat.choose` is exponential Diophantine, with no witnesses. -/
theorem of_choose (n k r : ExpTerm α) :
    ExpDioph {v : α → ℕ | (n.eval v).choose (k.eval v) = r.eval v} := by
  refine (of_eq (s := ExpTerm.chooseTerm n k) (t := r)).congr fun v => ?_
  simp [Set.mem_setOf_eq]

/-- **#34.** The binary submask relation is exponential Diophantine — the consumer lemma the
route spike's `Guarded.mask` needs, in exactly the shape it was stated in. -/
theorem of_isBinarySubmask (a b : ExpTerm α) :
    ExpDioph {v : α → ℕ | Nat.IsBinarySubmask (a.eval v) (b.eval v)} := by
  refine (of_eq (s := .mod (ExpTerm.chooseTerm b a) (.const 2)) (t := .const 1)).congr fun v => ?_
  simp only [Set.mem_setOf_eq, ExpTerm.eval, ExpTerm.eval_chooseTerm]
  rw [Nat.isBinarySubmask_iff_odd_choose, Nat.odd_iff]

end ExpDioph

end Hilbert10


/- Source: Hilbert10.Internal.BlockPacking, Hilbert10 v2.3.0, Apache-2.0. -/
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# Guarded block packing

The reusable layer extracted from the route spike (#15): a block layout with one guard bit
per block, and the two APIs its two consumers actually need.

## Two APIs, deliberately

The spike proved both directions of a machine encoding against this layer, and they consume
it differently:

* **soundness** uses the global characterisation `isBinarySubmask_guardMask_iff`, which turns
  a mask hypothesis into every block bound plus `R < blockBase k ^ t`;
* **completeness** uses the recursive split `isBinarySubmask_split` together with
  `guardMask_succ`, peeling one block from each side in step.

Both are exported. Factoring against only one consumer would have picked the wrong API.

The layout is fixed at **one guard bit**: data values below `2 ^ k`, blocks of width `k + 1`.
That is the construction the spike validated, and it is the right reusable unit; block layouts
with more guard bits or non-uniform fields are not generalised over here.

`geom` is not new API — it is `∑ i ∈ Finset.range t, b ^ i`, mathlib's geometric sum, given a
local name for readability. What is worth keeping is `geom_unique`, the subtraction-free
uniqueness statement, which is stated against that sum.
-/

namespace Hilbert10

open Finset

/-- `∑ i < t, b ^ i`, the geometric sum that counts one decrement per step. -/
def geom (b t : ℕ) : ℕ := ∑ i ∈ range t, b ^ i

/-- Peeling the first digit: one more step multiplies the geometric sum by the base. -/
theorem geom_succ (b n : ℕ) : geom b (n + 1) = 1 + b * geom b n := by
  simp only [geom, Finset.sum_range_succ']
  rw [Finset.mul_sum]
  simp [pow_succ, mul_comm, add_comm]

/-- The geometric identity, in the subtraction-free form the arithmetisation needs. Holds
for every base, including degenerate ones. -/
theorem geom_spec (b t : ℕ) : geom b t * b + 1 = geom b t + b ^ t := by
  induction t with
  | zero => simp [geom]
  | succ t ih =>
    rw [geom_succ, pow_succ]
    nlinarith [ih]

/-- The geometric identity determines its solution, for any base at least `2`. This is what
lets an encoding carry the geometric sum as a *variable* rather than a computed value. -/
theorem geom_unique {b t G : ℕ} (hb : 2 ≤ b) (h : G * b + 1 = G + b ^ t) :
    G = geom b t := by
  obtain ⟨C, hC⟩ : ∃ C, b = C + 1 := ⟨b - 1, by omega⟩
  have hC0 : 0 < C := by omega
  have h1 : G * C + 1 = b ^ t := by
    have h' : G * C + G + 1 = G + b ^ t := by
      calc G * C + G + 1 = G * (C + 1) + 1 := by ring
        _ = G + b ^ t := by rw [← hC]; exact h
    omega
  have h2 : geom b t * C + 1 = b ^ t := by
    have hg := geom_spec b t
    have h' : geom b t * C + geom b t + 1 = geom b t + b ^ t := by
      calc geom b t * C + geom b t + 1 = geom b t * (C + 1) + 1 := by ring
        _ = geom b t + b ^ t := by rw [← hC]; exact hg
    omega
  exact Nat.eq_of_mul_eq_mul_right hC0 (Nat.add_right_cancel (h1.trans h2.symm))

/-- Permitted register values are `< 2 ^ k`. -/
def dataBound (k : ℕ) : ℕ := 2 ^ k

/-- The packing base: one guard bit above the data field. -/
def blockBase (k : ℕ) : ℕ := 2 ^ (k + 1)

theorem blockBase_eq (k : ℕ) : blockBase k = 2 * dataBound k := by
  simp [blockBase, dataBound, pow_succ, mul_comm]

theorem two_le_blockBase (k : ℕ) : 2 ≤ blockBase k := by
  simpa [blockBase] using Nat.pow_le_pow_right (by norm_num) (Nat.succ_le_succ (Nat.zero_le k))

/-- `guardMask k t` is the number whose set bits are the low `k` bits of each of the first
`t` blocks of width `k + 1`. -/
def guardMask (k t : ℕ) : ℕ := (dataBound k - 1) * geom (blockBase k) t

theorem guardMask_zero (k : ℕ) : guardMask k 0 = 0 := by simp [guardMask, geom]

/-- One more block, prepended below the rest. -/
theorem guardMask_succ (k t : ℕ) :
    guardMask k (t + 1) = (dataBound k - 1) + blockBase k * guardMask k t := by
  simp only [guardMask, geom_succ, Nat.mul_add, mul_one]
  ring

/-- The split, specialised to the block layout. The content is generic — see
`Nat.isBinarySubmask_add_mul_two_pow_iff` — since `blockBase k` is a power of two. -/
theorem isBinarySubmask_split {k x a b : ℕ} (ha : a < blockBase k) :
    Nat.IsBinarySubmask x (a + blockBase k * b) ↔
      Nat.IsBinarySubmask (x % blockBase k) a ∧ Nat.IsBinarySubmask (x / blockBase k) b :=
  Nat.isBinarySubmask_add_mul_two_pow_iff ha

/-- The API bridge: `Guarded.mask` is stated with the closed form `(dataBound k - 1) * G`, and
after `geo_unique` that *is* `guardMask k t`. Definitional, but named so the rewrite step is
explicit. -/
theorem guardMask_eq (k t : ℕ) :
    guardMask k t = (dataBound k - 1) * geom (blockBase k) t := rfl

/-- Fitting in the data field, specialised from
`Nat.isBinarySubmask_two_pow_sub_one_iff`. This is where the guard bit does its work:
`dataBound k - 1` permits precisely the low `k` bits. -/
theorem isBinarySubmask_dataBound_sub_one_iff {k x : ℕ} :
    Nat.IsBinarySubmask x (dataBound k - 1) ↔ x < dataBound k :=
  Nat.isBinarySubmask_two_pow_sub_one_iff

/-- **The mask characterisation.** Stated as an equivalence, so that it serves soundness
(every block bound, plus the global bound), completeness (the mask reduced to ordinary bounds
on packed values), and fixes #34's exact semantic contract. -/
theorem isBinarySubmask_guardMask_iff {k t R : ℕ} :
    Nat.IsBinarySubmask R (guardMask k t) ↔
      R < blockBase k ^ t ∧ ∀ i < t, (R / blockBase k ^ i) % blockBase k < dataBound k := by
  induction t generalizing R with
  | zero =>
    simp only [guardMask_zero, pow_zero, Nat.lt_one_iff, Nat.isBinarySubmask_zero_iff]
    constructor
    · intro h
      exact ⟨h, by omega⟩
    · rintro ⟨h, -⟩
      exact h
  | succ t ih =>
    have hlow : dataBound k - 1 < blockBase k := by
      simp only [dataBound, blockBase]
      have h1 : 0 < 2 ^ k := Nat.two_pow_pos k
      have h2 : (2 : ℕ) ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    rw [guardMask_succ, isBinarySubmask_split hlow, isBinarySubmask_dataBound_sub_one_iff, ih]
    have hB : 0 < blockBase k := by simp [blockBase]
    constructor
    · rintro ⟨hmod, hdiv, hblk⟩
      refine ⟨?_, fun i hi => ?_⟩
      · rw [pow_succ]
        exact (Nat.div_lt_iff_lt_mul hB).mp hdiv
      · cases i with
        | zero => simpa using hmod
        | succ i =>
          have := hblk i (by omega)
          rwa [Nat.div_div_eq_div_mul, ← pow_succ'] at this
    · rintro ⟨hlt, hblk⟩
      refine ⟨by simpa using hblk 0 (by omega), ?_, fun i hi => ?_⟩
      · refine (Nat.div_lt_iff_lt_mul hB).mpr ?_
        rwa [← pow_succ]
      · have := hblk (i + 1) (by omega)
        rwa [Nat.div_div_eq_div_mul, ← pow_succ']


end Hilbert10


/- Source: Hilbert10.Internal.RunWidth, Hilbert10 v2.3.0, Apache-2.0. -/
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# A width that is big enough

Issue #46. #45 leaves every statement conditional on `FitsConfig w`, so something has to produce
a `w`. This file produces one, for a bounded prefix of a run.

## Deliberately not minimal

The width is a *sum*, not a maximum and not a logarithm:

```
configWeight c = c.pc + ∑ r, c.regs r
programWeight P = P.length + ∑ I ∈ P, I.jumpWeight
runWidth P c n = programWeight P + ∑ i ≤ n, configWeight (run P c i)
```

Every quantity that has to fit is one summand of `runWidth`, so every bound is
`Finset.single_le_sum` followed by `Nat.lt_two_pow_self : m < 2 ^ m`. There is no `Nat.log`, no
`Finset.max'`, no case split on emptiness, and no arithmetic to verify: the width is grotesquely
larger than necessary, which costs nothing because it is representation data inside an
existential that #47 and #48 immediately eliminate.

Using the weight as an exponent is the whole trick. `runWidth` bounds the *values*, and
`2 ^ runWidth` then dominates them with room to spare, so the two roles a width plays — being
large enough to hold a value, and being a field width — never have to be reconciled.

## Main results

* `RegisterMachine.fits_runWidth` — every configuration of the prefix fits
* `RegisterMachine.exists_width` — the packaged form: one width for the configurations, the
  program length, and every jump target in the program
* `RegisterMachine.encodedStep_run` — the handoff: at this width, consecutive configurations of
  a run are related by #45's step relation
-/

namespace Hilbert10

namespace RegisterMachine

variable {k : ℕ}

/-- Everything a single configuration needs to fit, added up. -/
def configWeight (c : Config k) : ℕ := c.pc + ∑ r, c.regs r

/-- The jump targets of one instruction, added up. -/
def Instr.jumpWeight : Instr k → ℕ
  | .inc _ j => j
  | .dec _ jpos jzero => jpos + jzero

/-- Everything the program's own constants need to fit, added up. -/
def programWeight (P : Program k) : ℕ := P.length + (P.map Instr.jumpWeight).sum

/-- A width large enough for the first `n + 1` configurations of the run from `c`, and for the
program's constants. -/
def runWidth (P : Program k) (c : Config k) (n : ℕ) : ℕ :=
  programWeight P + ∑ i ∈ Finset.range (n + 1), configWeight (run P c i)

theorem pc_le_configWeight (c : Config k) : c.pc ≤ configWeight c := Nat.le_add_right _ _

theorem regs_le_configWeight (c : Config k) (r : Fin k) : c.regs r ≤ configWeight c :=
  le_trans (Finset.single_le_sum (f := c.regs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ r))
    (Nat.le_add_left _ _)

theorem length_le_programWeight (P : Program k) : P.length ≤ programWeight P :=
  Nat.le_add_right _ _

theorem jumpWeight_le_programWeight {P : Program k} {I : Instr k} (hI : I ∈ P) :
    I.jumpWeight ≤ programWeight P :=
  le_trans (List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map_of_mem hI))
    (Nat.le_add_left _ _)

theorem programWeight_le_runWidth (P : Program k) (c : Config k) (n : ℕ) :
    programWeight P ≤ runWidth P c n := Nat.le_add_right _ _

theorem configWeight_le_runWidth {P : Program k} {c : Config k} {i n : ℕ} (hi : i ≤ n) :
    configWeight (run P c i) ≤ runWidth P c n :=
  le_trans (Finset.single_le_sum (f := fun j => configWeight (run P c j))
    (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))) (Nat.le_add_left _ _)

/-- The one arithmetic fact this file uses: a weight is dwarfed by two to that weight. -/
theorem lt_two_pow_runWidth {P : Program k} {c : Config k} {n m : ℕ} (h : m ≤ runWidth P c n) :
    m < 2 ^ runWidth P c n :=
  lt_of_le_of_lt h Nat.lt_two_pow_self

theorem runWidth_mono {P : Program k} {c : Config k} {m n : ℕ} (h : m ≤ n) :
    runWidth P c m ≤ runWidth P c n := by
  refine Nat.add_le_add_left (Finset.sum_le_sum_of_subset ?_) _
  intro x hx
  simp only [Finset.mem_range] at hx ⊢
  omega

/-- **Every configuration of the prefix fits.** -/
theorem fits_runWidth {P : Program k} {c : Config k} {i n : ℕ} (hi : i ≤ n) :
    FitsConfig (runWidth P c n) (run P c i) :=
  ⟨lt_two_pow_runWidth (le_trans (pc_le_configWeight _) (configWeight_le_runWidth hi)),
    fun r => lt_two_pow_runWidth
      (le_trans (regs_le_configWeight _ r) (configWeight_le_runWidth hi))⟩

theorem length_lt_two_pow_runWidth (P : Program k) (c : Config k) (n : ℕ) :
    P.length < 2 ^ runWidth P c n :=
  lt_two_pow_runWidth (le_trans (length_le_programWeight P) (programWeight_le_runWidth P c n))

theorem jumpWeight_lt_two_pow_runWidth {P : Program k} {I : Instr k} (hI : I ∈ P) (c : Config k)
    (n : ℕ) : I.jumpWeight < 2 ^ runWidth P c n :=
  lt_two_pow_runWidth (le_trans (jumpWeight_le_programWeight hI) (programWeight_le_runWidth P c n))

/-- **The packaged form.** One width under which the whole prefix of the run is representable and
every constant of the program fits.

The jump targets are listed separately because that is the shape #45's `EncodedStep` asks for:
each disjunct bounds the target it selects. -/
theorem exists_width (P : Program k) (c : Config k) (n : ℕ) :
    ∃ w, P.length < 2 ^ w
      ∧ (∀ (r : Fin k) (j : ℕ), Instr.inc r j ∈ P → j < 2 ^ w)
      ∧ (∀ (r : Fin k) (jpos jzero : ℕ), Instr.dec r jpos jzero ∈ P →
          jpos < 2 ^ w ∧ jzero < 2 ^ w)
      ∧ ∀ i ≤ n, FitsConfig w (run P c i) := by
  refine ⟨runWidth P c n, length_lt_two_pow_runWidth P c n, ?_, ?_, fun i hi => fits_runWidth hi⟩
  · intro r j hI
    have := jumpWeight_lt_two_pow_runWidth hI c n
    simpa [Instr.jumpWeight] using this
  · intro r jpos jzero hI
    have := jumpWeight_lt_two_pow_runWidth hI c n
    simp only [Instr.jumpWeight] at this
    omega

/-- The handoff to #47: at `runWidth`, consecutive configurations of the run are related by the
encoded step. This is where #45's local statement and #46's width meet, and it is the only place
the two files need to be read together. -/
theorem encodedStep_run {P : Program k} {c : Config k} {i n : ℕ} (hi : i < n)
    (hpc : (run P c i).pc < P.length) :
    EncodedStep P (runWidth P c n) (configCode (runWidth P c n) (run P c i))
      (configCode (runWidth P c n) (run P c (i + 1))) := by
  have hstep : step P (run P c i) = run P c (i + 1) := (run_succ P c i).symm
  rw [← hstep]
  exact encodedStep_configCode (fits_runWidth (by omega))
    (hstep ▸ fits_runWidth (P := P) (c := c) (i := i + 1) (n := n) (by omega)) hpc

end RegisterMachine

end Hilbert10


/- Source: Hilbert10.Internal.PackedRun, Hilbert10 v2.3.0, Apache-2.0. -/
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# A whole run as one number

Issue #47: packed-run completeness, semantically. An accepting run becomes a single natural
number whose blocks are the configuration codes of its successive configurations.

## Two nestings of the same construction

`fieldsCode` is used twice, at two widths, and that is the whole design.

*Inner*: a configuration of an `r`-register machine is `r + 1` fields of width `w`, so it
occupies `w * (r + 1)` bits (#45).

*Outer*: a run of `n + 1` configurations is `n + 1` blocks of width `w * (r + 1) + 1` — the
configuration, plus `BlockPacking`'s single guard bit. `Nat.IsBinarySubmask R (guardMask …)`
says exactly that every block's guard bit is clear, which by
`isBinarySubmask_guardMask_iff` is exactly that every block holds a configuration.

So extraction is `field_fieldsCode` at the outer width, and the mask obligation is the existing
`BlockPacking` characterisation. No new packing arithmetic appears here.

## Indexing

The width is written `w * (k + 1)` where `k` is the *program's* register count, so a
`Program (k + 1)` — which is what `CleanScratch` deals in — gets `w * (k + 2)` automatically.
The specialisation happens only at the `Accepts` endpoint.

## Scope

The bounded conjunction `∀ i < n, EncodedStep …` is left visible. Turning it into an exponential
Diophantine condition is #49; this file is semantics only.

## Main results

* `RegisterMachine.EncodedRun` — the packed-run predicate
* `RegisterMachine.encodedRun_packRun` — every prefix of a run packs
* `RegisterMachine.encodedRun_sound` — and every packed run is a run
* `RegisterMachine.accepts_iff_exists_encodedRun` — the two directions combined, and the exact
  statement #49 represents
-/

namespace Hilbert10

namespace RegisterMachine

variable {k : ℕ}

/-- **A packed run.** `R` codes `n + 1` configurations in blocks of width `w * (k + 1) + 1`,
consecutive blocks are related by one step of `P`, and the first and last are `start` and
`finish`. -/
def EncodedRun (P : Program k) (w n R start finish : ℕ) : Prop :=
  Nat.IsBinarySubmask R (guardMask (w * (k + 1)) (n + 1)) ∧
    configField (w * (k + 1) + 1) R 0 = start ∧
      configField (w * (k + 1) + 1) R n = finish ∧
        ∀ i < n, EncodedStep P w (configField (w * (k + 1) + 1) R i)
          (configField (w * (k + 1) + 1) R (i + 1))

/-- The packing: block `i` is the code of the `i`-th configuration. -/
def packRun (P : Program k) (c : Config k) (w n : ℕ) : ℕ :=
  fieldsCode (w * (k + 1) + 1) fun i : Fin (n + 1) => configCode w (run P c i)

/-- Each block of a configuration code sits strictly inside its data field, leaving the guard
bit clear. This is the one numeric fact the outer layer needs about the inner one. -/
theorem configCode_lt_dataBound {w : ℕ} {c : Config k} (h : FitsConfig w c) :
    configCode w c < dataBound (w * (k + 1)) :=
  configCode_lt_two_pow h

theorem configCode_lt_blockBase {w : ℕ} {c : Config k} (h : FitsConfig w c) :
    configCode w c < 2 ^ (w * (k + 1) + 1) :=
  lt_trans (configCode_lt_two_pow h) (Nat.pow_lt_pow_right (by norm_num) (by omega))

/-- Extraction: the blocks of `packRun` are the configuration codes. -/
theorem field_packRun {P : Program k} {c : Config k} {w n : ℕ}
    (hfit : ∀ i ≤ n, FitsConfig w (run P c i)) {i : ℕ} (hi : i ≤ n) :
    configField (w * (k + 1) + 1) (packRun P c w n) i = configCode w (run P c i) := by
  have := field_fieldsCode
    (w := w * (k + 1) + 1) (f := fun j : Fin (n + 1) => configCode w (run P c j))
    (fun j => configCode_lt_blockBase (hfit j (by omega))) ⟨i, by omega⟩
  simpa [packRun] using this

theorem packRun_lt {P : Program k} {c : Config k} {w n : ℕ}
    (hfit : ∀ i ≤ n, FitsConfig w (run P c i)) :
    packRun P c w n < blockBase (w * (k + 1)) ^ (n + 1) :=
  fieldsCode_lt fun j => configCode_lt_blockBase (hfit j (by omega))

/-- The guard bits are clear. Immediately from `BlockPacking`'s characterisation, since each
block is a configuration code and so below `dataBound`. -/
theorem isBinarySubmask_packRun {P : Program k} {c : Config k} {w n : ℕ}
    (hfit : ∀ i ≤ n, FitsConfig w (run P c i)) :
    Nat.IsBinarySubmask (packRun P c w n) (guardMask (w * (k + 1)) (n + 1)) := by
  refine isBinarySubmask_guardMask_iff.mpr ⟨packRun_lt hfit, fun i hi => ?_⟩
  rw [show packRun P c w n / blockBase (w * (k + 1)) ^ i % blockBase (w * (k + 1))
      = configField (w * (k + 1) + 1) (packRun P c w n) i from rfl,
    field_packRun hfit (by omega)]
  exact configCode_lt_dataBound (hfit i (by omega))

/-- **Every prefix of a run packs.** The width is #46's, so no fitting hypothesis is needed. -/
theorem encodedRun_packRun {P : Program k} {c : Config k} {n : ℕ}
    (hin : ∀ i < n, (run P c i).pc < P.length) :
    EncodedRun P (runWidth P c n) n (packRun P c (runWidth P c n) n)
      (configCode (runWidth P c n) c) (configCode (runWidth P c n) (run P c n)) := by
  set w := runWidth P c n with hw
  have hfit : ∀ i ≤ n, FitsConfig w (run P c i) := fun i hi => fits_runWidth hi
  refine ⟨isBinarySubmask_packRun hfit, ?_, field_packRun hfit le_rfl, fun i hi => ?_⟩
  · rw [field_packRun hfit (Nat.zero_le n), run_zero]
  · rw [field_packRun hfit (by omega), field_packRun hfit (by omega)]
    exact encodedStep_run hi (hin i hi)

/-- **The endpoint #49 consumes.** An accepting run of `P` is a packed run from the clean input
configuration to the clean output configuration, *with the boundary constants bounded*.

The three bounds are not redundant with the mask. `EncodedRun` bounds its blocks, but an
oversized `x`, `y` or `P.length` carries inside `configCode` exactly as an oversized register
value carried inside `setField` before #45 was corrected, and the packed run would still satisfy
every block constraint. Stating them is what lets #48 recover the *exact* clean boundary
configurations rather than merely bounded ones. They are free at #46's width and cheap for
`ExpDioph`, being three `of_lt` conjuncts.

`Accepts` supplies exactly what `encodedRun_packRun` needs: the run length, the in-range program
counter at every transition, and the exit equation. Fitting comes from #46 internally and is
never an obligation on the caller. -/
theorem exists_encodedRun_of_accepts {P : Program (k + 1)} {x y : ℕ} (h : Accepts P x y) :
    ∃ n w R, x < 2 ^ w ∧ y < 2 ^ w ∧ P.length < 2 ^ w ∧
      EncodedRun P w n R
        (configCode w (⟨0, unaryConfig k x⟩ : Config (k + 1)))
        (configCode w (⟨P.length, unaryConfig k y⟩ : Config (k + 1))) := by
  obtain ⟨n, hin, hex⟩ := h
  refine ⟨n, runWidth P ⟨0, unaryConfig k x⟩ n,
    packRun P ⟨0, unaryConfig k x⟩ (runWidth P ⟨0, unaryConfig k x⟩ n) n, ?_, ?_,
    length_lt_two_pow_runWidth P ⟨0, unaryConfig k x⟩ n, ?_⟩
  · have := (fits_runWidth (P := P) (c := ⟨0, unaryConfig k x⟩) (i := 0) (n := n)
      (Nat.zero_le n)).2 0
    rw [run_zero] at this
    simpa using this
  · have := (fits_runWidth (P := P) (c := ⟨0, unaryConfig k x⟩) (i := n) (n := n) le_rfl).2 0
    rw [hex] at this
    simpa using this
  · have := encodedRun_packRun (P := P) (c := ⟨0, unaryConfig k x⟩) (n := n) hin
    rwa [hex] at this

/-- The code of a clean configuration, in closed form. The register file is zero above
register `0`, so the whole code is two terms — which is what makes the endpoint equalities of
#49 ordinary exponential terms rather than nested sums. -/
theorem configCode_unaryConfig (w p x : ℕ) :
    configCode w (⟨p, unaryConfig k x⟩ : Config (k + 1)) = p + 2 ^ w * x := by
  have h1 : (@Fin.cons (k + 1) (fun _ => ℕ) p (unaryConfig k x)) ∘ Fin.succ = unaryConfig k x := by
    funext i; simp
  have h2 : (unaryConfig k x) ∘ Fin.succ = fun _ : Fin k => 0 := by
    funext i; exact unaryConfig_of_ne (Fin.succ_ne_zero i)
  rw [configCode, fieldsCode_succ, h1, fieldsCode_succ, h2, fieldsCode_const_zero]
  simp

/-! ### Soundness

The inverse of `encodedRun_packRun`. Every carry argument was discharged in #45, so this is an
induction over block indices and nothing else. -/

/-- **A packed run really is a run.** Generic in the boundary configurations; the clean
specialisation comes after.

The invariant is that block `i`, decoded, is the `i`-th configuration of the run. It is
maintained by `decodeConfig_step_of_encodedStep`, which needs only the block bound the mask
already supplies, and `n = 0` needs no separate case because the base case is the identification
of block `0`. -/
theorem encodedRun_sound {P : Program k} {w n R : ℕ} {start finish : Config k}
    (hs : FitsConfig w start) (hf : FitsConfig w finish)
    (h : EncodedRun P w n R (configCode w start) (configCode w finish)) :
    (∀ i < n, (run P start i).pc < P.length) ∧ run P start n = finish := by
  obtain ⟨hmask, h0, hn, hstep⟩ := h
  have hblk : ∀ i < n + 1, configField (w * (k + 1) + 1) R i < 2 ^ (w * (k + 1)) := fun i hi =>
    (isBinarySubmask_guardMask_iff.mp hmask).2 i hi
  have key : ∀ i, i ≤ n → decodeConfig w (configField (w * (k + 1) + 1) R i) = run P start i := by
    intro i
    induction i with
    | zero => intro _; rw [h0, decodeConfig_configCode hs, run_zero]
    | succ i ih =>
      intro hi
      rw [decodeConfig_step_of_encodedStep (hblk i (by omega)) (hstep i (by omega)),
        ih (by omega), run_succ]
  refine ⟨fun i hi => ?_, ?_⟩
  · rw [← key i (by omega)]
    exact configField_zero_lt_of_encodedStep (hstep i hi)
  · rw [← key n le_rfl, hn, decodeConfig_configCode hf]

/-- The clean boundary configurations fit as soon as their two constants do. -/
theorem fitsConfig_unaryConfig {w p x : ℕ} (hp : p < 2 ^ w) (hx : x < 2 ^ w) :
    FitsConfig w (⟨p, unaryConfig k x⟩ : Config (k + 1)) := by
  refine ⟨hp, fun i => ?_⟩
  rcases eq_or_ne i 0 with rfl | hi
  · simpa using hx
  · simp [unaryConfig_of_ne hi]

/-- **The exact endpoint.** `Accepts` — the trace relation #20 hands over — is *equivalent* to
the existence of a packed run with bounded boundary constants.

`EncodedRun` itself stays generic; the boundary bounds live only here, where they are needed to
pin the endpoints down to the clean configurations. #49 targets this right-hand side verbatim. -/
theorem accepts_iff_exists_encodedRun {P : Program (k + 1)} {x y : ℕ} :
    Accepts P x y ↔
      ∃ n w R, x < 2 ^ w ∧ y < 2 ^ w ∧ P.length < 2 ^ w ∧
        EncodedRun P w n R
          (configCode w (⟨0, unaryConfig k x⟩ : Config (k + 1)))
          (configCode w (⟨P.length, unaryConfig k y⟩ : Config (k + 1))) := by
  refine ⟨exists_encodedRun_of_accepts, ?_⟩
  rintro ⟨n, w, R, hx, hy, hlen, hrun⟩
  exact ⟨n, encodedRun_sound (fitsConfig_unaryConfig (Nat.two_pow_pos w) hx)
    (fitsConfig_unaryConfig hlen hy) hrun⟩

end RegisterMachine

end Hilbert10


/- Source: Hilbert10.Internal.AcceptsDioph, Hilbert10 v2.3.0, Apache-2.0. -/
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# The machine route, reduced to one obligation

Issue #49, first phase. #48 closed the semantic chain: `Accepts` is *equivalent* to the
existence of a packed run. This file represents every part of that statement except one, and
gives the remainder a name.

## What is discharged here

The endpoint of `accepts_iff_exists_encodedRun` has eight conjuncts under four existentials.
Seven of them are ordinary exponential Diophantine atoms:

* the two input and output bounds, `of_lt`;
* two endpoint equalities, `of_eq`, using the closed form `configCode w ⟨p, unaryConfig k x⟩
  = p + 2 ^ w * x`.

The rest — the program-length bound, the guard mask, and the bounded conjunction over indices —
is bundled into `Aggregation` and taken as a hypothesis, so that the accounting cannot drift:
`expDioph_accepts` is *conditional*, and the condition is a single `def` one can read.

## Why the bundle, and not the conjunct alone

The mask is not hard to represent. It is `ExpDioph.of_isBinarySubmask` (#34) applied to
`guardMask` with `geom` carried as a *variable* pinned by `geom_unique` — which is exactly what
that subtraction-free identity was proved for — and the program-length bound is one `of_lt`.
They are bundled anyway, because any construction that discharges the bounded conjunction needs
them as *hypotheses*: without the mask it must reason about arbitrary, possibly overflowing
block values, and without `P.length < 2 ^ w` it cannot bound instruction indices inside a block.
Stating the obligation as the weakest thing the endpoint actually needs is the same "prove only
the endpoint" rule the rest of the development follows. The geometric-sum witness therefore
stays internal to whatever proof discharges `Aggregation`.

## How it is discharged, and what did not count as progress

`Aggregation` is the same bounded-universal theorem the direct-route spike isolated in
`Spike/Sequences.lean`. `SelectorRegsDioph.aggregation_succ` discharges it at every register
count, by the selector encoding rather than by any bounded-universal representation: finitely
many identities over one-hot selector lanes replace the quantifier outright. Two things would
not have counted as progress, and did not happen:

* adding a bounded-product or bounded-forall constructor to `ExpTerm` — that relocates the
  missing proof into new syntax;
* `boundedForall_eq_iff_prod`. Product-equals-one is *equivalent* to the bounded universal for
  those gap factors, so the reduction is free and the representation of the variable product is
  the whole of the difficulty.

A discharge has to come from an independently proved representation theorem, and attribution
belongs at the deepest non-circular one — here, the selector construction.

## Main definitions

* `RegisterMachine.blockTerm` — outer block lookup at a **variable** index
* `RegisterMachine.Aggregation` — the obligation, discharged in `SelectorRegsDioph`

## Main results

* `RegisterMachine.expDioph_accepts` — conditional on `Aggregation`; the unconditional form
  is `RegisterMachine.dioph_accepts_regs`
-/

namespace Hilbert10

namespace RegisterMachine

variable {α : Type} {k : ℕ}

/-! ### Terms for the outer layer

`ConfigCodingDioph`'s `fieldTerm` reads a field at a numeral index, which is right for the
inner layer: the program is fixed, so its register indices are numerals. The outer index runs
over blocks and is a variable, so it needs its own term. -/

/-- The data width of one block: `w * (k + 1)` for a `k`-register machine. -/
def dataBaseTerm (k : ℕ) (W : ExpTerm α) : ExpTerm α :=
  .pow (.const 2) (.mul W (.const (k + 1)))

@[simp] theorem eval_dataBaseTerm (k : ℕ) (W : ExpTerm α) (v : α → ℕ) :
    (dataBaseTerm k W).eval v = 2 ^ (W.eval v * (k + 1)) := rfl

/-- The outer packing base: one block is the data plus one guard bit. -/
def outerBaseTerm (k : ℕ) (W : ExpTerm α) : ExpTerm α :=
  .pow (.const 2) (.add (.mul W (.const (k + 1))) (.const 1))

@[simp] theorem eval_outerBaseTerm (k : ℕ) (W : ExpTerm α) (v : α → ℕ) :
    (outerBaseTerm k W).eval v = 2 ^ (W.eval v * (k + 1) + 1) := rfl

/-- **Outer block lookup at a variable index.** -/
def blockTerm (k : ℕ) (W R I : ExpTerm α) : ExpTerm α :=
  .mod (.div R (.pow (outerBaseTerm k W) I)) (outerBaseTerm k W)

@[simp] theorem eval_blockTerm (k : ℕ) (W R I : ExpTerm α) (v : α → ℕ) :
    (blockTerm k W R I).eval v
      = configField (W.eval v * (k + 1) + 1) (R.eval v) (I.eval v) := rfl

/-! ### The obligation -/

/-- **The obligation for one program**: a bounded conjunction of step relations over a variable
number of block indices, bundled with the two facts any proof of it would have to assume anyway.

Stated with `N`, `W`, `R` as terms and the index quantified semantically, so that it cannot be
satisfied by making the index a numeral or by assuming a representable lookup function.

Separated from `Aggregation` because it is provable for particular programs — see
`Spike/SelectorSliceDioph` — long before it is provable for all of them, and the endpoint below
only ever needs it at the one program it is applied to. -/
def StepBundle (P : Program k) (N W R : ExpTerm α) : Set (α → ℕ) :=
  {v : α → ℕ |
    P.length < 2 ^ W.eval v ∧
    Nat.IsBinarySubmask (R.eval v) (guardMask (W.eval v * (k + 1)) (N.eval v + 1)) ∧
    ∀ i < N.eval v,
      EncodedStep P (W.eval v)
        (configField (W.eval v * (k + 1) + 1) (R.eval v) i)
        (configField (W.eval v * (k + 1) + 1) (R.eval v) (i + 1))}

/-- **The sole remaining representability obligation of #21**: `StepBundle`, uniformly in the
program. -/
def Aggregation (k : ℕ) : Prop :=
  ∀ {α : Type} (P : Program k) (N W R : ExpTerm α), ExpDioph (StepBundle P N W R)

/-! ### Everything else -/

/-- The witness block of `expDioph_accepts`: `0` is the run length, `1` the width, `2` the
packed run. There is no fourth witness — the geometric sum moved inside `Aggregation`. -/
def runBody (P : Program (k + 1)) (X Y : ExpTerm α) : Set ((α ⊕ Fin 3) → ℕ) :=
  {u | (X.map Sum.inl).eval u < 2 ^ u (Sum.inr 1) ∧
    (Y.map Sum.inl).eval u < 2 ^ u (Sum.inr 1) ∧
    configField (u (Sum.inr 1) * (k + 1 + 1) + 1) (u (Sum.inr 2)) 0
      = 2 ^ u (Sum.inr 1) * (X.map Sum.inl).eval u ∧
    configField (u (Sum.inr 1) * (k + 1 + 1) + 1) (u (Sum.inr 2)) (u (Sum.inr 0))
      = P.length + 2 ^ u (Sum.inr 1) * (Y.map Sum.inl).eval u ∧
    (P.length < 2 ^ u (Sum.inr 1) ∧
      Nat.IsBinarySubmask (u (Sum.inr 2))
        (guardMask (u (Sum.inr 1) * (k + 1 + 1)) (u (Sum.inr 0) + 1)) ∧
      ∀ i < u (Sum.inr 0),
        EncodedStep P (u (Sum.inr 1))
          (configField (u (Sum.inr 1) * (k + 1 + 1) + 1) (u (Sum.inr 2)) i)
          (configField (u (Sum.inr 1) * (k + 1 + 1) + 1) (u (Sum.inr 2)) (i + 1)))}

theorem expDioph_runBody_of_bundle {P : Program (k + 1)}
    (hP : ∀ {β : Type} (N W R : ExpTerm β), ExpDioph (StepBundle P N W R)) (X Y : ExpTerm α) :
    ExpDioph (runBody P X Y) := by
  refine ExpDioph.congr (ExpDioph.and
    (ExpDioph.of_lt (s := X.map Sum.inl) (t := widthTerm (.var (Sum.inr 1)))) (ExpDioph.and
    (ExpDioph.of_lt (s := Y.map Sum.inl) (t := widthTerm (.var (Sum.inr 1)))) (ExpDioph.and
    (ExpDioph.of_eq
      (s := blockTerm (k + 1) (.var (Sum.inr 1)) (.var (Sum.inr 2)) (.const 0))
      (t := .mul (widthTerm (.var (Sum.inr 1))) (X.map Sum.inl))) (ExpDioph.and
    (ExpDioph.of_eq
      (s := blockTerm (k + 1) (.var (Sum.inr 1)) (.var (Sum.inr 2)) (.var (Sum.inr 0)))
      (t := .add (.const P.length) (.mul (widthTerm (.var (Sum.inr 1))) (Y.map Sum.inl))))
    (hP (.var (Sum.inr 0)) (.var (Sum.inr 1)) (.var (Sum.inr 2))))))) ?_
  intro u
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, runBody, StepBundle, widthTerm, ExpTerm.eval,
    eval_blockTerm]

theorem expDioph_runBody (hagg : Aggregation (k + 1)) (P : Program (k + 1)) (X Y : ExpTerm α) :
    ExpDioph (runBody P X Y) :=
  expDioph_runBody_of_bundle (fun {β} N W R => hagg (α := β) P N W R) X Y

/-- **The endpoint, for a single program.**

Every conjunct of `accepts_iff_exists_encodedRun` other than the bundle is discharged here:
the input and output bounds, and the two endpoint equalities. Only `StepBundle` for the one
program in hand is assumed, so a program whose aggregation is provable is representable
outright, without waiting for `Aggregation`. -/
theorem expDioph_accepts_of_bundle {P : Program (k + 1)}
    (hP : ∀ {β : Type} (N W R : ExpTerm β), ExpDioph (StepBundle P N W R)) (X Y : ExpTerm α) :
    ExpDioph {v : α → ℕ | Accepts P (X.eval v) (Y.eval v)} := by
  refine ExpDioph.congr (ExpDioph.ex (expDioph_runBody_of_bundle hP X Y)) fun v => ?_
  simp only [runBody, Set.mem_setOf_eq, ExpTerm.eval_map, Sum.elim_comp_inl, Sum.elim_inr]
  rw [accepts_iff_exists_encodedRun]
  simp only [EncodedRun, configCode_unaryConfig, Nat.zero_add]
  constructor
  · rintro ⟨u, hx, hy, h0, hn, hlen, hmask, hstep⟩
    exact ⟨u 0, u 1, u 2, hx, hy, hlen, hmask, h0, hn, hstep⟩
  · rintro ⟨n, w, R, hx, hy, hlen, hmask, h0, hn, hstep⟩
    exact ⟨![n, w, R], hx, hy, h0, hn, hlen, hmask, hstep⟩

/-- **The endpoint, conditional on aggregation.** -/
theorem expDioph_accepts (hagg : Aggregation (k + 1)) (P : Program (k + 1)) (X Y : ExpTerm α) :
    ExpDioph {v : α → ℕ | Accepts P (X.eval v) (Y.eval v)} :=
  expDioph_accepts_of_bundle (fun {β} N W R => hagg (α := β) P N W R) X Y

end RegisterMachine

end Hilbert10


/- Source: Hilbert10.Internal.SelectorMask, Hilbert10 v2.3.0, Apache-2.0. -/
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# Selector packing: global identities read blockwise

The packing algebra the selector encoding is built on, and the answer to the question #49 was
opened to decide. `Aggregation` is a bounded conjunction over block indices, bundled with a guard
mask and a program-length bound; the question was whether it can instead be expressed by finitely
many global identities. It can, and the lemmas here are why.

Originally a time-boxed probe under `Spike/`. It moved out when the general theorem came to
depend on it: `SelectorRegs`, `SelectorRegsGlobal` and `SelectorRegsDioph` are the load-bearing
chain, while the fixed-program and one-register developments stay under `Spike/` as the evidence
that decided the route.

## The distinction that decides it

A condition on a packed number is acceptable if the equivalence

> global identity between numbers  ⟺  the same identity in every block

is a **theorem proved by induction on the block index**, and unacceptable if it is a
*Diophantine condition* that itself needs representing. The circularity trap in
`Spike/Sequences.lean` is the second kind: coding partial products and requiring
`p (i + 1) = p i * h i` reproduces the bounded conjunction one level down.

Every primitive below is of the first kind. That is the content of the probe: `fieldsCode` is
linear, so sums, scalar multiples and pointwise-bounded differences of packed numbers are
blockwise for free; equality of two in-range packings is blockwise by base uniqueness; and a
submask condition is blockwise by peeling one block at a time.

## The intended encoding

Per *register lane*, not per configuration: `Xpc, X₀, …, X_k`, each packing `n + 1` values.

**All lanes use the same outer base as the packed run**, `B = 2 ^ (w * (k + 1) + 1)`. This is
deliberately wasteful — a lane block spends `w * (k + 1) + 1` bits carrying a `w`-bit value —
and it is what keeps the connection to #47's `R` a single global identity,

```
R = Xpc + 2 ^ w * X₀ + 2 ^ (2 * w) * X₁ + ⋯
```

blockwise, since a configuration code is below `2 ^ (w * (k + 1))` and so below `B`. Lanes at
their own tight base `2 ^ (w + 1)` would have forced a second packed-run development alongside
#47 and #48; at base `B` those two are reused unchanged.

The data mask for a lane is `M = (2 ^ w - 1) * geom B (n + 1)`: one `w`-bit field per block,
guard bits clear.

For a fixed program of `m` instructions, selectors `S₀, …, S_{m-1}` pack `n` bits, and each
`dec` selector splits as `S⁺ₚ + S⁰ₚ`. The conditions are then, all global:

* `IsBinarySubmask Sₚ (geom B n)` — each selector is one bit per block;
* `∑ₚ Sₚ = geom B n` — exactly one instruction runs per step, carry-free because
  `P.length < 2 ^ w` is part of `Aggregation`'s bundle;
* `Xpc % Bⁿ = ∑ₚ p · Sₚ` — the selector agrees with the program counter;
* `Xpc / B = ∑ₚ targetₚ · Sₚ^branch` — the jump;
* `X_r / B + ∑_{dec r} S⁺ₚ = X_r % Bⁿ + ∑_{inc r} Sₚ` — the register update, subtraction-free;
* for each instruction, the bound on the target it *selects*:
  `Sₚ = 0 ∨ jₚ < 2 ^ w` for an `inc`, and `S⁺ₚ = 0 ∨ jposₚ < 2 ^ w`,
  `S⁰ₚ = 0 ∨ jzeroₚ < 2 ^ w` for a `dec`;
* for each `dec` instruction `p` reading register `r`:
  `S⁰ₚ + S⁺ₚ = Sₚ`, both submasked by `geom B n`;
  `IsBinarySubmask (S⁰ₚ · (2 ^ w - 1)) (M % Bⁿ - X_r % Bⁿ)` — the zero branch;
  `X_r % Bⁿ = X''ₚ + S⁺ₚ` **together with** `IsBinarySubmask X''ₚ (M % Bⁿ)` — the positive
  branch.

That last mask is load-bearing, not decoration. Without it the equation is unsound blockwise,
because the addition may carry: at `B = 8`, `X = 8`, `S⁺ = 1`, `X'' = 7` satisfies `X = X'' + S⁺`
while block `0` of `X` is zero and block `0` of `S⁺` is one. Bounding each block of `X''` below
`2 ^ w` rules the carry out.

The selected-target bounds are load-bearing for the same reason, one level up.
`P.length < 2 ^ w` bounds instruction *indices*, but a `Program` may carry jump targets far
larger than either `P.length` or `2 ^ w`, and `targetₚ · Sₚ` is blockwise only while
`targetₚ < B`. Without them a large target carries between selector blocks and the jump equation
can be satisfied spuriously. They are stated per branch, and as disjunctions, because
`EncodedStep` bounds only the target it selects: requiring every target in the program to fit
would be strictly stronger, and wrong, since an unreachable branch need not fit. Because a
target is a *constant*, the bounded universal `∀ i < n, sₚ,ᵢ = 1 → jₚ < 2 ^ w` collapses to the
disjunction `Sₚ = 0 ∨ jₚ < 2 ^ w`, which is one `ExpDioph.or`.

Several instructions may read the same register: give each `dec` its own `S⁰ₚ` and `S⁺ₚ`, and the
global selector partition puts their conditions on disjoint blocks.

## Status

The primitives are proved. The **acceptance slice** is **not built**, and until it is, the
encoding above is an argument rather than a theorem. This file discharges nothing of
`Aggregation`.

The slice must exercise four cases: `n = 0`; an increment; both branches of a decrement; and an
*unselected* branch whose target exceeds `2 ^ w`, confirming that the encoding does not
accidentally demand that every target fit. A second decrement reading the same register belongs
in a separate regression rather than the minimal slice.
-/

namespace Hilbert10

namespace RegisterMachine

variable {W : ℕ}

/-! ### Blockwise arithmetic

`fieldsCode` is a `∑ᵢ fᵢ · Bⁱ`, so it is linear. That is why sums and scalar multiples of
packed numbers need no hypotheses at all: the bounds enter only when *recovering* the blocks. -/

theorem fieldsCode_add (W : ℕ) : ∀ {n : ℕ} (a c : Fin n → ℕ),
    fieldsCode W a + fieldsCode W c = fieldsCode W fun i => a i + c i
  | 0, _, _ => rfl
  | n + 1, a, c => by
    rw [fieldsCode_succ, fieldsCode_succ, fieldsCode_succ,
      show ((fun i => a i + c i) ∘ Fin.succ) = (fun i => (a ∘ Fin.succ) i + (c ∘ Fin.succ) i) from
        rfl,
      ← fieldsCode_add W (a ∘ Fin.succ) (c ∘ Fin.succ)]
    ring

theorem fieldsCode_smul (W m : ℕ) : ∀ {n : ℕ} (a : Fin n → ℕ),
    m * fieldsCode W a = fieldsCode W fun i => m * a i
  | 0, _ => by simp [fieldsCode]
  | n + 1, a => by
    rw [fieldsCode_succ, fieldsCode_succ,
      show ((fun i => m * a i) ∘ Fin.succ) = (fun i => m * (a ∘ Fin.succ) i) from rfl,
      ← fieldsCode_smul W m (a ∘ Fin.succ)]
    ring

/-- Base-`2 ^ W` uniqueness, in packing form. -/
theorem fieldsCode_injective {n : ℕ} {a c : Fin n → ℕ} (ha : ∀ i, a i < 2 ^ W)
    (hc : ∀ i, c i < 2 ^ W) (h : fieldsCode W a = fieldsCode W c) : a = c := by
  funext i
  rw [← field_fieldsCode ha i, ← field_fieldsCode hc i, h]

/-- **The primitive the probe turns on.** A single equation between packed numbers *is* the
family of equations between their blocks, provided nothing overflows a block. Proved by
induction; nothing here is a Diophantine condition. -/
theorem fieldsCode_add_eq_iff {n : ℕ} {a c d : Fin n → ℕ} (h : ∀ i, a i + c i < 2 ^ W)
    (hd : ∀ i, d i < 2 ^ W) :
    fieldsCode W a + fieldsCode W c = fieldsCode W d ↔ ∀ i, a i + c i = d i := by
  rw [fieldsCode_add]
  constructor
  · intro heq i
    exact congrFun (fieldsCode_injective h hd heq) i
  · intro heq
    exact congrArg _ (funext heq)

/-- The same for a sum of scalar multiples, which is the shape of the selector conditions
`Xpc % Bⁿ = ∑ₚ p · Sₚ` and the jump equation. -/
theorem fieldsCode_smul_add_eq_iff {n m₁ m₂ : ℕ} {a c d : Fin n → ℕ}
    (h : ∀ i, m₁ * a i + m₂ * c i < 2 ^ W) (hd : ∀ i, d i < 2 ^ W) :
    m₁ * fieldsCode W a + m₂ * fieldsCode W c = fieldsCode W d ↔
      ∀ i, m₁ * a i + m₂ * c i = d i := by
  rw [fieldsCode_smul, fieldsCode_smul]
  exact fieldsCode_add_eq_iff h hd

/-! ### Finite sums of lanes

Every selector condition is a sum over the program's instructions, so the two-term lemmas are
not enough. `Finset` induction lifts them. -/

theorem fieldsCode_sum {ι : Type} (W : ℕ) {n : ℕ} (s : Finset ι) (g : ι → Fin n → ℕ) :
    ∑ p ∈ s, fieldsCode W (g p) = fieldsCode W fun i => ∑ p ∈ s, g p i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert p s hp ih =>
    rw [Finset.sum_insert hp, ih, fieldsCode_add]
    exact congrArg _ (funext fun i => (Finset.sum_insert (f := fun q => g q i) hp).symm)

/-- Three scaled packings added, which is the shape every selector equation takes. -/
theorem fieldsCode_three (W : ℕ) {n : ℕ} (a b c : ℕ) (f g h : Fin n → ℕ) :
    a * fieldsCode W f + b * fieldsCode W g + c * fieldsCode W h
      = fieldsCode W fun i => a * f i + b * g i + c * h i := by
  rw [fieldsCode_smul, fieldsCode_smul, fieldsCode_smul, fieldsCode_add, fieldsCode_add]

theorem fieldsCode_sum_smul {ι : Type} (W : ℕ) {n : ℕ} (s : Finset ι)
    (m : ι → ℕ) (g : ι → Fin n → ℕ) :
    ∑ p ∈ s, m p * fieldsCode W (g p) = fieldsCode W fun i => ∑ p ∈ s, m p * g p i := by
  rw [← fieldsCode_sum]
  exact Finset.sum_congr rfl fun p _ => fieldsCode_smul W (m p) (g p)

/-- The selector-condition shape: one global equation between a scaled sum of lanes and a lane
is the family of its block equations. -/
theorem fieldsCode_sum_smul_eq_iff {ι : Type} {W n : ℕ} {s : Finset ι}
    {m : ι → ℕ} {g : ι → Fin n → ℕ} {d : Fin n → ℕ}
    (h : ∀ i, ∑ p ∈ s, m p * g p i < 2 ^ W) (hd : ∀ i, d i < 2 ^ W) :
    ∑ p ∈ s, m p * fieldsCode W (g p) = fieldsCode W d ↔ ∀ i, ∑ p ∈ s, m p * g p i = d i := by
  rw [fieldsCode_sum_smul]
  constructor
  · intro heq i
    exact congrFun (fieldsCode_injective h hd heq) i
  · intro heq
    exact congrArg _ (funext heq)

/-- **Only selected scalars have to fit.** A scaled sum of selectors is blockwise exactly when
every selector that is used *somewhere* carries a scalar below the block bound; a selector that
is identically zero imposes nothing at all.

This is the mechanism behind the disjunctions `Sₚ = 0 ∨ targetₚ < 2 ^ w` in the condition list.
It is what stops an oversized target on an unreachable branch from being required to fit, and it
is why the bound must be stated per branch rather than over the whole program. -/
theorem fieldsCode_selected_smul_eq_iff {ι : Type} {W n : ℕ} {s : Finset ι} {m : ι → ℕ}
    {sel : ι → Fin n → ℕ} {d : Fin n → ℕ}
    (hone : ∀ i, ∑ p ∈ s, sel p i = 1)
    (hfit : ∀ p ∈ s, (∀ i, sel p i = 0) ∨ m p < 2 ^ W)
    (hd : ∀ i, d i < 2 ^ W) :
    ∑ p ∈ s, m p * fieldsCode W (sel p) = fieldsCode W d ↔
      ∀ i, ∑ p ∈ s, m p * sel p i = d i := by
  classical
  refine fieldsCode_sum_smul_eq_iff (fun i => ?_) hd
  -- exactly one selector is `1` at block `i`, so the block value is that selector's scalar
  obtain ⟨p₀, hp₀s, hp₀⟩ : ∃ p ∈ s, sel p i ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_and, ne_eq, not_not] at hcon
    have h1 := hone i
    rw [Finset.sum_congr rfl fun p hp => hcon p hp] at h1
    simp at h1
  have hle : sel p₀ i ≤ ∑ p ∈ s, sel p i :=
    Finset.single_le_sum (f := fun p => sel p i) (fun _ _ => Nat.zero_le _) hp₀s
  rw [hone i] at hle
  have hp₀one : sel p₀ i = 1 := by omega
  have hsplit : sel p₀ i + ∑ p ∈ s.erase p₀, sel p i = 1 :=
    (Finset.add_sum_erase s (fun p => sel p i) hp₀s).trans (hone i)
  have hzero : ∑ p ∈ s.erase p₀, sel p i = 0 := by omega
  have herase : ∑ p ∈ s.erase p₀, m p * sel p i = 0 :=
    Finset.sum_eq_zero fun p hp => by rw [Finset.sum_eq_zero_iff.mp hzero p hp, mul_zero]
  have hval : ∑ p ∈ s, m p * sel p i = m p₀ := by
    rw [← Finset.add_sum_erase s (fun p => m p * sel p i) hp₀s, herase, hp₀one, mul_one]
    omega
  rw [hval]
  rcases hfit p₀ hp₀s with h | h
  · exact absurd (h i) hp₀
  · exact h

/-! ### Lane masks

A lane's blocks hold `w`-bit values inside `w * (k + 1) + 1`-bit blocks, so the lane data mask is
*narrower* than `BlockPacking`'s `guardMask` and is not an instance of it. These two lemmas are
the ones the globalisation step demands: the mask is a constant packing, and it characterises
both the range and the per-block bound. -/

theorem fieldsCode_const (W v : ℕ) : ∀ {t : ℕ},
    fieldsCode W (fun _ : Fin t => v) = v * geom (2 ^ W) t
  | 0 => by simp [fieldsCode, geom]
  | t + 1 => by
    rw [fieldsCode_succ,
      show ((fun _ : Fin (t + 1) => v) ∘ Fin.succ) = fun _ : Fin t => v from rfl,
      fieldsCode_const W v, geom_succ]
    ring

/-- **The lane mask says exactly what it should.** Being a submask of `(2 ^ v - 1)` repeated in
every block is being below `(2 ^ W) ^ t` with every block below `2 ^ v`. Mirrors
`isBinarySubmask_guardMask_iff`, which is the same statement at `v = W - 1`. -/
theorem isBinarySubmask_constMask_iff {W v : ℕ} (hv : v ≤ W) : ∀ {t X : ℕ},
    Nat.IsBinarySubmask X ((2 ^ v - 1) * geom (2 ^ W) t) ↔
      X < (2 ^ W) ^ t ∧ ∀ i < t, configField W X i < 2 ^ v := by
  intro t
  induction t with
  | zero =>
    intro X
    simp only [geom, Finset.range_zero, Finset.sum_empty, mul_zero, pow_zero, Nat.lt_one_iff,
      Nat.isBinarySubmask_zero_iff]
    exact ⟨fun h => ⟨h, by omega⟩, fun h => h.1⟩
  | succ t ih =>
    intro X
    have hlow : 2 ^ v - 1 < 2 ^ W := by
      have h1 : (2 : ℕ) ^ v ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) hv
      have h2 : 0 < (2 : ℕ) ^ v := Nat.two_pow_pos v
      omega
    have hB : 0 < (2 : ℕ) ^ W := Nat.two_pow_pos W
    rw [geom_succ, Nat.mul_add, mul_one,
      show (2 ^ v - 1) * (2 ^ W * geom (2 ^ W) t) = 2 ^ W * ((2 ^ v - 1) * geom (2 ^ W) t) by ring,
      Nat.isBinarySubmask_add_mul_two_pow_iff hlow,
      Nat.isBinarySubmask_two_pow_sub_one_iff, ih]
    constructor
    · rintro ⟨hmod, hlt, hblk⟩
      refine ⟨?_, fun i hi => ?_⟩
      · rw [pow_succ]
        exact (Nat.div_lt_iff_lt_mul hB).mp hlt
      · cases i with
        | zero => rwa [configField_zero]
        | succ i => rw [configField_succ]; exact hblk i (by omega)
    · rintro ⟨hlt, hblk⟩
      refine ⟨by have := hblk 0 (by omega); rwa [configField_zero] at this, ?_,
        fun i hi => ?_⟩
      · refine (Nat.div_lt_iff_lt_mul hB).mpr ?_
        rwa [← pow_succ]
      · have := hblk (i + 1) (by omega)
        rwa [configField_succ] at this

/-- **Normalising a packed witness.** Every masked number is the packing of its own fields, with
each field bounded. This is the first move in every soundness argument: apply it once per
witness, and afterwards work only with `Fin t` functions. -/
theorem packed_eq_fieldsCode {W v t X : ℕ} (hv : v ≤ W)
    (h : Nat.IsBinarySubmask X ((2 ^ v - 1) * geom (2 ^ W) t)) :
    X = fieldsCode W (fun i : Fin t => configField W X i) ∧
      ∀ i : Fin t, configField W X i < 2 ^ v := by
  obtain ⟨hlt, hblk⟩ := (isBinarySubmask_constMask_iff hv).mp h
  exact ⟨(fieldsCode_configField hlt).symm, fun i => hblk i i.isLt⟩

/-! ### The lane decomposition

Why lanes are packed at the *outer* base `B` rather than at their own tight base: the packed run
of #47 is then a scaled sum of the lanes, one global identity, and #47 and #48 are reused
unchanged. -/

theorem fieldsCode_eq_sum (W : ℕ) : ∀ {n : ℕ} (f : Fin n → ℕ),
    fieldsCode W f = ∑ i : Fin n, (2 ^ W) ^ (i : ℕ) * f i := by
  intro n
  induction n with
  | zero => simp [fieldsCode]
  | succ n ih =>
    intro f
    rw [fieldsCode_succ, ih (f ∘ Fin.succ), Fin.sum_univ_succ, Finset.mul_sum]
    simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_succ, Function.comp_apply]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring

/-- **`R` is the scaled sum of its lanes.** The identity that lets the selector encoding talk
about registers separately while #47's packed run stays exactly as it is. -/
theorem fieldsCode_configCode_eq_lanes {k : ℕ} (w : ℕ) {n : ℕ} (cs : Fin n → Config k) :
    fieldsCode (w * (k + 1) + 1) (fun i => configCode w (cs i))
      = ∑ j : Fin (k + 1), (2 ^ w) ^ (j : ℕ) *
          fieldsCode (w * (k + 1) + 1)
            (fun i => (@Fin.cons k (fun _ => ℕ) (cs i).pc (cs i).regs) j) := by
  rw [fieldsCode_sum_smul]
  exact congrArg _ (funext fun i => fieldsCode_eq_sum w _)

/-! ### Truncation

`X % Bⁿ` drops the last block: it is what restricts a lane of `n + 1` values to the `n` steps
that have a successor. -/

theorem fieldsCode_snoc (W : ℕ) : ∀ {n : ℕ} (f : Fin (n + 1) → ℕ),
    fieldsCode W f = fieldsCode W (Fin.init f) + (2 ^ W) ^ n * f (Fin.last n) := by
  intro n
  induction n with
  | zero =>
    intro f
    rw [fieldsCode_succ]
    simp [fieldsCode]
  | succ n ih =>
    intro f
    have h2 : ((Fin.init f) ∘ Fin.succ) = Fin.init (f ∘ Fin.succ) := by
      funext i
      exact congrArg f (Fin.ext (by simp))
    have h3 : (f ∘ Fin.succ) (Fin.last n) = f (Fin.last (n + 1)) :=
      congrArg f (Fin.ext (by simp))
    rw [fieldsCode_succ, fieldsCode_succ W n (Fin.init f), h2, ih (f ∘ Fin.succ), h3,
      show (Fin.init f) 0 = f 0 from congrArg f (Fin.ext (by simp))]
    ring

theorem fieldsCode_mod_pow {W n : ℕ} {f : Fin (n + 1) → ℕ} (hf : ∀ i, f i < 2 ^ W) :
    fieldsCode W f % (2 ^ W) ^ n = fieldsCode W (Fin.init f) := by
  rw [fieldsCode_snoc, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (fieldsCode_lt fun i => hf _)

/-! ### Blockwise masking

The other half: a submask condition between packed numbers is the family of submask conditions
between their blocks. This is the one that decides whether *selector validity* is cheap, since
every selector is constrained by a mask rather than an equation. -/

theorem fieldsCode_mod_base (W : ℕ) {n : ℕ} (f : Fin (n + 1) → ℕ) (h0 : f 0 < 2 ^ W) :
    fieldsCode W f % 2 ^ W = f 0 := by
  rw [fieldsCode_succ, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h0]

theorem fieldsCode_div (W : ℕ) {n : ℕ} (f : Fin (n + 1) → ℕ) (h0 : f 0 < 2 ^ W) :
    fieldsCode W f / 2 ^ W = fieldsCode W (f ∘ Fin.succ) := by
  rw [fieldsCode_succ, Nat.add_mul_div_left _ _ (Nat.two_pow_pos W), Nat.div_eq_of_lt h0,
    Nat.zero_add]

/-- **A submask condition is blockwise too.** This is the lemma that decides the probe: every
selector is constrained by a mask rather than an equation, so if selector validity were to
recreate a bounded universal, it would have to happen here. It does not — the peeling step is
`Nat.isBinarySubmask_add_mul_two_pow_iff`, and the recursion is on the number of blocks. -/
theorem isBinarySubmask_fieldsCode_iff : ∀ {n : ℕ} {a c : Fin n → ℕ}, (∀ i, a i < 2 ^ W) →
    (∀ i, c i < 2 ^ W) →
      (Nat.IsBinarySubmask (fieldsCode W a) (fieldsCode W c) ↔
        ∀ i, Nat.IsBinarySubmask (a i) (c i)) := by
  intro n
  induction n with
  | zero =>
    intro a c _ _
    exact ⟨fun _ i => i.elim0, fun _ => Nat.isBinarySubmask_refl 0⟩
  | succ n ih =>
    intro a c ha hc
    rw [show fieldsCode W c = c 0 + 2 ^ W * fieldsCode W (c ∘ Fin.succ) from fieldsCode_succ W n c,
      Nat.isBinarySubmask_add_mul_two_pow_iff (hc 0), fieldsCode_mod_base W a (ha 0),
      fieldsCode_div W a (ha 0),
      ih (a := a ∘ Fin.succ) (c := c ∘ Fin.succ) (fun i => ha i.succ) (fun i => hc i.succ)]
    constructor
    · rintro ⟨h0, hs⟩ i
      exact Fin.cases h0 (fun j => hs j) i
    · intro h
      exact ⟨h 0, fun j => h j.succ⟩

/-! ### Sums against a one-hot family -/

/-- A sum against an index indicator collapses to one term. -/
theorem sum_indicator {L m : ℕ} (h : m < L) (f : Fin L → ℕ) :
    ∑ p : Fin L, (if (p : ℕ) = m then f p else 0) = f ⟨m, h⟩ := by
  rw [Finset.sum_congr rfl (g := fun p : Fin L => if p = ⟨m, h⟩ then f p else 0) fun p _ => ?_]
  · simp
  · by_cases hp : (p : ℕ) = m
    · rw [if_pos hp, if_pos (Fin.ext hp)]
    · rw [if_neg hp, if_neg (fun he : p = ⟨m, h⟩ => hp (by rw [he]))]

/-- A sum whose family vanishes off one index collapses to that index. -/
theorem sum_eq_of_vanishing {L : ℕ} {g : Fin L → ℕ} {q : Fin L} (h : ∀ p, p ≠ q → g p = 0) :
    ∑ p : Fin L, g p = g q :=
  Finset.sum_eq_single q (fun p _ hp => h p hp) (fun hq => absurd (Finset.mem_univ q) hq)

/-- A family of naturals summing to `1` is `1` at one index and `0` everywhere else. -/
theorem exists_unique_of_sum_eq_one {L : ℕ} {g : Fin L → ℕ} (h : ∑ p : Fin L, g p = 1) :
    ∃ q, g q = 1 ∧ ∀ p, p ≠ q → g p = 0 := by
  obtain ⟨q, -, hq⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by omega : ∑ p : Fin L, g p ≠ 0)
  have hsplit : g q + ∑ p ∈ Finset.univ.erase q, g p = 1 := by
    rw [Finset.add_sum_erase _ _ (Finset.mem_univ q)]; exact h
  refine ⟨q, by omega, fun p hp => ?_⟩
  have hz : ∑ p ∈ Finset.univ.erase q, g p = 0 := by omega
  exact (Finset.sum_eq_zero_iff.mp hz) p (Finset.mem_erase.mpr ⟨hp, Finset.mem_univ p⟩)

end RegisterMachine

end Hilbert10


/- Source: Hilbert10.Internal.SelectorRegs, Hilbert10 v2.3.0, Apache-2.0. -/
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# The selector encoding for many registers: the blockwise layer

#49, phase 4. `Spike/SelectorProgram` and its two successors proved `Aggregation 1`. The
remaining scaling question is the register count, and this file is its blockwise layer: the same
selector vocabulary for an arbitrary `P : Program (k + 1)`.

## What becomes register-indexed

The selectors do not. There is still one ordinary and one zero selector per instruction, and
they are still one-hot across the whole program. What becomes indexed by `Fin (k + 1)` is the
*coefficients* and the *residuals*:

* `gainAt r` and `lossAt r` pick out the instructions that increment or decrement register `r`,
  so each register gets its own subtraction-free update equation;
* the positive residual becomes one per register;
* the zero branch is tested at the decremented register, so its selector sub-sum is
  `∑ p, lossAt r (P.get p) * Z p` — the decrements *on `r`* that took their zero branch.

## Why the sub-sums do not carry

Every one of those sums is bounded by `1`, even when many instructions mention the same
register, because each is a sub-sum of the global one-hot family: `lossAt r I ≤ 1` and
`A p ≤ A p + Z p`. `subSum_le_one` is that fact, proved once and used by every register
equation. It is what keeps the register equations carry-free at the layer above, and it is the
only place the register count could have introduced a new bound.

## Scope

`blockStepK_iff` only. Globalising the lanes is `SelectorRegsGlobal`, and packaging them into
`Aggregation (k + 1)` is `SelectorRegsDioph`. The one-register development is left untouched, as
regression evidence for the route.
-/

namespace Hilbert10

namespace RegisterMachine

variable {k : ℕ}

/-! ### Per-instruction coefficients, register-indexed where they must be -/

namespace Instr

/-- The target of the ordinary branch. -/
def jumpPos : Instr k → ℕ
  | .inc _ j => j
  | .dec _ jpos _ => jpos

/-- The target of the zero branch; an increment has none. -/
def jumpZero : Instr k → ℕ
  | .inc _ _ => 0
  | .dec _ _ jzero => jzero

/-- Whether a zero branch exists at all. -/
def branches : Instr k → ℕ
  | .inc _ _ => 0
  | .dec _ _ _ => 1

/-- The register the instruction acts on, and whose value its branch tests. -/
def testReg : Instr k → Fin k
  | .inc r _ => r
  | .dec r _ _ => r

/-- What the ordinary branch adds to register `r`. -/
def gainAt [DecidableEq (Fin k)] (r : Fin k) : Instr k → ℕ
  | .inc r' _ => if r' = r then 1 else 0
  | .dec _ _ _ => 0

/-- What the ordinary branch removes from register `r`; also which decrements test `r`. -/
def lossAt [DecidableEq (Fin k)] (r : Fin k) : Instr k → ℕ
  | .inc _ _ => 0
  | .dec r' _ _ => if r' = r then 1 else 0

theorem gainAt_le_one (r : Fin k) (I : Instr k) : gainAt r I ≤ 1 := by
  unfold gainAt; split <;> [split; skip] <;> omega

theorem lossAt_le_one (r : Fin k) (I : Instr k) : lossAt r I ≤ 1 := by
  unfold lossAt; split <;> [skip; split] <;> omega

end Instr

/-- Two configurations agreeing on the program counter and every register are equal. -/
theorem config_ext {c₁ c₂ : Config k} (hpc : c₁.pc = c₂.pc) (hr : ∀ r, c₁.regs r = c₂.regs r) :
    c₁ = c₂ := by
  obtain ⟨p₁, r₁⟩ := c₁
  obtain ⟨p₂, r₂⟩ := c₂
  simp only [Config.mk.injEq]
  exact ⟨hpc, funext hr⟩

/-- **The sub-sums stay one-hot.** A coefficient family bounded by `1`, summed against either
selector of a one-hot pair, is itself at most `1`. Every register equation below is an instance,
which is why no register equation can carry. -/
theorem subSum_le_one {L : ℕ} {A Z g : Fin L → ℕ} (hg : ∀ p, g p ≤ 1)
    (hone : (∑ p : Fin L, (A p + Z p)) = 1) :
    (∑ p : Fin L, g p * A p) ≤ 1 ∧ (∑ p : Fin L, g p * Z p) ≤ 1 := by
  constructor
  · calc (∑ p : Fin L, g p * A p) ≤ ∑ p : Fin L, (A p + Z p) :=
          Finset.sum_le_sum fun p _ => by
            calc g p * A p ≤ 1 * A p := Nat.mul_le_mul_right _ (hg p)
              _ = A p := one_mul _
              _ ≤ A p + Z p := Nat.le_add_right _ _
      _ = 1 := hone
  · calc (∑ p : Fin L, g p * Z p) ≤ ∑ p : Fin L, (A p + Z p) :=
          Finset.sum_le_sum fun p _ => by
            calc g p * Z p ≤ 1 * Z p := Nat.mul_le_mul_right _ (hg p)
              _ = Z p := one_mul _
              _ ≤ A p + Z p := Nat.le_add_left _ _
      _ = 1 := hone

/-! ### The blockwise conditions -/

/-- **The selector conditions at one step, for an arbitrary program on `k + 1` registers.**

Read in order: the selectors are one-hot; the program counter names the selected instruction and
jumps to its target; every register has its own subtraction-free update equation; only a
decrement may take a zero branch, and a zero branch on `r` forces `r` to vanish; every register
has a positive residual; and each selected target fits. -/
def BlockStepK (P : Program (k + 1)) (w pcHere pcNext : ℕ)
    (regsHere regsNext res : Fin (k + 1) → ℕ) (A Z : Fin P.length → ℕ) : Prop :=
  (∑ p : Fin P.length, (A p + Z p)) = 1 ∧
  pcHere = ∑ p : Fin P.length, (p : ℕ) * (A p + Z p) ∧
  pcNext = ∑ p : Fin P.length, ((P.get p).jumpPos * A p + (P.get p).jumpZero * Z p) ∧
  (∀ r, regsNext r + ∑ p : Fin P.length, (P.get p).lossAt r * A p
    = regsHere r + ∑ p : Fin P.length, (P.get p).gainAt r * A p) ∧
  (∀ p, Z p ≤ (P.get p).branches) ∧
  (∀ r, (∑ p : Fin P.length, (P.get p).lossAt r * Z p) = 1 → regsHere r = 0) ∧
  (∀ r, regsHere r = res r + ∑ p : Fin P.length, (P.get p).lossAt r * A p) ∧
  (∀ r, res r < 2 ^ w) ∧
  (∀ p, A p = 1 → (P.get p).jumpPos < 2 ^ w) ∧
  (∀ p, Z p = 1 → (P.get p).jumpZero < 2 ^ w) ∧
  pcNext < 2 ^ w ∧ (∀ r, regsNext r < 2 ^ w)

/-- The ordinary selector of a configuration: the instruction at the program counter is selected
unless it is a decrement whose tested register has run out. -/
private def ordFlagK (P : Program (k + 1)) (c : Config (k + 1)) (p : Fin P.length) : ℕ :=
  if (P.get p).branches = 1 ∧ c.regs ((P.get p).testReg) = 0 then 0 else 1

theorem ordFlagK_le_one (P : Program (k + 1)) (c : Config (k + 1)) (p : Fin P.length) :
    ordFlagK P c p ≤ 1 := by
  unfold ordFlagK; split <;> omega

/-- **The blockwise equivalence, for an arbitrary program on `k + 1` registers.** -/
theorem blockStepK_iff (P : Program (k + 1)) (w n : ℕ) (cs : ℕ → Config (k + 1))
    (hfit : ∀ i, FitsConfig w (cs i)) :
    (∀ i < n, EncodedStep P w (configCode w (cs i)) (configCode w (cs (i + 1)))) ↔
      ∃ A Z : ℕ → Fin P.length → ℕ, ∃ res : ℕ → Fin (k + 1) → ℕ, ∀ i < n,
        BlockStepK P w (cs i).pc (cs (i + 1)).pc (cs i).regs (cs (i + 1)).regs (res i)
          (A i) (Z i) := by
  constructor
  · intro h
    refine ⟨fun i p => if (p : ℕ) = (cs i).pc then ordFlagK P (cs i) p else 0,
      fun i p => if (p : ℕ) = (cs i).pc then 1 - ordFlagK P (cs i) p else 0,
      fun i r => (cs i).regs r - ∑ p : Fin P.length, (P.get p).lossAt r *
        (if (p : ℕ) = (cs i).pc then ordFlagK P (cs i) p else 0), ?_⟩
    intro i hi
    dsimp only
    have hstep := h i hi
    have hpc : (cs i).pc < P.length := by
      have := configField_zero_lt_of_encodedStep hstep
      rwa [field_configCode_zero (hfit i)] at this
    obtain ⟨hfits, hz⟩ := (encodedStep_iff (hfit i) hpc).mp hstep
    have hnext : cs (i + 1) = step P (cs i) :=
      configCode_injective (hfit (i + 1)) hfits hz
    set q : Fin P.length := ⟨(cs i).pc, hpc⟩ with hq
    have hget : step P (cs i) = (P.get q).exec (cs i).regs :=
      step_of_getElem? (by simp [hq])
    -- every sum collapses to the selected instruction
    have hsumA : ∀ f : Fin P.length → ℕ,
        (∑ p : Fin P.length, f p * (if (p : ℕ) = (cs i).pc then ordFlagK P (cs i) p else 0))
          = f q * ordFlagK P (cs i) q := by
      intro f
      have e : (fun p : Fin P.length =>
          f p * (if (p : ℕ) = (cs i).pc then ordFlagK P (cs i) p else 0))
          = fun p : Fin P.length =>
            if (p : ℕ) = (cs i).pc then f p * ordFlagK P (cs i) p else 0 := by
        funext p
        by_cases hp : (p : ℕ) = (cs i).pc
        · rw [if_pos hp, if_pos hp]
        · rw [if_neg hp, if_neg hp, Nat.mul_zero]
      rw [show (∑ p : Fin P.length,
          f p * (if (p : ℕ) = (cs i).pc then ordFlagK P (cs i) p else 0))
          = ∑ p : Fin P.length,
            (if (p : ℕ) = (cs i).pc then f p * ordFlagK P (cs i) p else 0) from by rw [e],
        sum_indicator hpc]
    have hsumZ : ∀ f : Fin P.length → ℕ,
        (∑ p : Fin P.length, f p * (if (p : ℕ) = (cs i).pc then 1 - ordFlagK P (cs i) p else 0))
          = f q * (1 - ordFlagK P (cs i) q) := by
      intro f
      have e : (fun p : Fin P.length =>
          f p * (if (p : ℕ) = (cs i).pc then 1 - ordFlagK P (cs i) p else 0))
          = fun p : Fin P.length =>
            if (p : ℕ) = (cs i).pc then f p * (1 - ordFlagK P (cs i) p) else 0 := by
        funext p
        by_cases hp : (p : ℕ) = (cs i).pc
        · rw [if_pos hp, if_pos hp]
        · rw [if_neg hp, if_neg hp, Nat.mul_zero]
      rw [show (∑ p : Fin P.length,
          f p * (if (p : ℕ) = (cs i).pc then 1 - ordFlagK P (cs i) p else 0))
          = ∑ p : Fin P.length,
            (if (p : ℕ) = (cs i).pc then f p * (1 - ordFlagK P (cs i) p) else 0) from by rw [e],
        sum_indicator hpc]
    have hsum1 : (∑ p : Fin P.length,
        ((if (p : ℕ) = (cs i).pc then ordFlagK P (cs i) p else 0)
          + (if (p : ℕ) = (cs i).pc then 1 - ordFlagK P (cs i) p else 0))) = 1 := by
      have e : (fun p : Fin P.length =>
          (if (p : ℕ) = (cs i).pc then ordFlagK P (cs i) p else 0)
            + (if (p : ℕ) = (cs i).pc then 1 - ordFlagK P (cs i) p else 0))
          = fun p : Fin P.length => if (p : ℕ) = (cs i).pc then 1 else 0 := by
        funext p
        by_cases hp : (p : ℕ) = (cs i).pc
        · have hle := ordFlagK_le_one P (cs i) p
          rw [if_pos hp, if_pos hp, if_pos hp]
          omega
        · rw [if_neg hp, if_neg hp, if_neg hp]
      rw [show (∑ p : Fin P.length,
          ((if (p : ℕ) = (cs i).pc then ordFlagK P (cs i) p else 0)
            + (if (p : ℕ) = (cs i).pc then 1 - ordFlagK P (cs i) p else 0)))
          = ∑ p : Fin P.length, (if (p : ℕ) = (cs i).pc then 1 else 0) from by rw [e]]
      simpa using sum_indicator hpc (fun _ => 1)
    have hsumPc : (∑ p : Fin P.length, (p : ℕ) *
        ((if (p : ℕ) = (cs i).pc then ordFlagK P (cs i) p else 0)
          + (if (p : ℕ) = (cs i).pc then 1 - ordFlagK P (cs i) p else 0))) = (cs i).pc := by
      have e : (fun p : Fin P.length => (p : ℕ) *
          ((if (p : ℕ) = (cs i).pc then ordFlagK P (cs i) p else 0)
            + (if (p : ℕ) = (cs i).pc then 1 - ordFlagK P (cs i) p else 0)))
          = fun p : Fin P.length => if (p : ℕ) = (cs i).pc then (p : ℕ) else 0 := by
        funext p
        by_cases hp : (p : ℕ) = (cs i).pc
        · have hle := ordFlagK_le_one P (cs i) p
          rw [if_pos hp, if_pos hp, if_pos hp,
            show ordFlagK P (cs i) p + (1 - ordFlagK P (cs i) p) = 1 from by omega, Nat.mul_one]
        · rw [if_neg hp, if_neg hp, if_neg hp]
          simp
      rw [show (∑ p : Fin P.length, (p : ℕ) *
          ((if (p : ℕ) = (cs i).pc then ordFlagK P (cs i) p else 0)
            + (if (p : ℕ) = (cs i).pc then 1 - ordFlagK P (cs i) p else 0)))
          = ∑ p : Fin P.length, (if (p : ℕ) = (cs i).pc then (p : ℕ) else 0) from by rw [e],
        sum_indicator hpc (fun p => (p : ℕ))]
    have hbr : ∀ r, (cs i).regs r < 2 ^ w := (hfit i).2
    have hb0 : (cs (i + 1)).pc < 2 ^ w := (hfit (i + 1)).1
    have hb1 : ∀ r, (cs (i + 1)).regs r < 2 ^ w := (hfit (i + 1)).2
    rcases hinstr : (P.get q) with ⟨r, j⟩ | ⟨r, jpos, jzero⟩
    · -- an increment
      have hord : ordFlagK P (cs i) q = 1 := by
        unfold ordFlagK
        rw [hinstr]
        simp [Instr.branches]
      have hexec : cs (i + 1) = ⟨j, Function.update (cs i).regs r ((cs i).regs r + 1)⟩ := by
        rw [hnext, hget, hinstr]
        rfl
      have hpcn : (cs (i + 1)).pc = j := by rw [hexec]
      have hrn : ∀ s, (cs (i + 1)).regs s
          = (cs i).regs s + (if r = s then 1 else 0) := by
        intro s
        rw [hexec]
        by_cases hs : s = r
        · subst hs; simp
        · simp [Function.update_of_ne hs, Ne.symm hs]
      refine ⟨hsum1, hsumPc.symm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega, ?_⟩ <;>
        (try dsimp only)
      · rw [Finset.sum_add_distrib, hsumA (fun p => (P.get p).jumpPos),
          hsumZ (fun p => (P.get p).jumpZero), hord, hinstr]
        simp [Instr.jumpPos, hpcn]
      · intro s
        rw [hsumA (fun p => (P.get p).lossAt s), hsumA (fun p => (P.get p).gainAt s), hord,
          hinstr, hrn s]
        simp only [Instr.lossAt, Instr.gainAt, Nat.mul_one]
        split <;> omega
      · intro p
        by_cases hp : (p : ℕ) = (cs i).pc
        · have hpq : p = q := Fin.ext hp
          rw [if_pos hp, hpq, hord]
          simp
        · simp [hp]
      · intro s hzs
        exfalso
        rw [hsumZ (fun p => (P.get p).lossAt s), hord] at hzs
        simp at hzs
      · intro s
        rw [hsumA (fun p => (P.get p).lossAt s), hord, hinstr]
        simp [Instr.lossAt]
      · intro s
        rw [hsumA (fun p => (P.get p).lossAt s), hord, hinstr]
        simp only [Instr.lossAt, Nat.mul_one, Nat.sub_zero]
        exact hbr s
      · intro p hA
        by_cases hp : (p : ℕ) = (cs i).pc
        · have hpq : p = q := Fin.ext hp
          rw [hpq, hinstr]
          simpa [Instr.jumpPos, hpcn] using hb0
        · rw [if_neg hp] at hA; omega
      · intro p hZ
        by_cases hp : (p : ℕ) = (cs i).pc
        · rw [if_pos hp, show p = q from Fin.ext hp, hord] at hZ; omega
        · rw [if_neg hp] at hZ; omega
      · exact hb1
    · -- a decrement
      rcases eq_or_ne ((cs i).regs r) 0 with hz0 | hz0
      · -- the zero branch
        have hord : ordFlagK P (cs i) q = 0 := by
          unfold ordFlagK
          rw [hinstr]
          simp [Instr.branches, Instr.testReg, hz0]
        have hexec : cs (i + 1) = ⟨jzero, (cs i).regs⟩ := by
          rw [hnext, hget, hinstr]
          simp only [Instr.exec]
          rw [if_pos hz0]
        have hpcn : (cs (i + 1)).pc = jzero := by rw [hexec]
        have hrn : ∀ s, (cs (i + 1)).regs s = (cs i).regs s := by intro s; rw [hexec]
        refine ⟨hsum1, hsumPc.symm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega, ?_⟩ <;>
          (try dsimp only)
        · rw [Finset.sum_add_distrib, hsumA (fun p => (P.get p).jumpPos),
            hsumZ (fun p => (P.get p).jumpZero), hord, hinstr]
          simp [Instr.jumpZero, hpcn]
        · intro s
          rw [hsumA (fun p => (P.get p).lossAt s), hsumA (fun p => (P.get p).gainAt s), hord,
            hrn s]
          simp
        · intro p
          by_cases hp : (p : ℕ) = (cs i).pc
          · have hpq : p = q := Fin.ext hp
            rw [if_pos hp, hpq, hord, hinstr]
            simp [Instr.branches]
          · simp [hp]
        · intro s hzs
          rw [hsumZ (fun p => (P.get p).lossAt s), hord, hinstr] at hzs
          simp only [Instr.lossAt, Nat.sub_zero, Nat.mul_one] at hzs
          by_cases hs : r = s
          · subst hs; exact hz0
          · rw [if_neg hs] at hzs; omega
        · intro s
          rw [hsumA (fun p => (P.get p).lossAt s), hord]
          simp
        · intro s
          rw [hsumA (fun p => (P.get p).lossAt s), hord]
          simpa using hbr s
        · intro p hA
          by_cases hp : (p : ℕ) = (cs i).pc
          · rw [if_pos hp, show p = q from Fin.ext hp, hord] at hA; omega
          · rw [if_neg hp] at hA; omega
        · intro p hZ
          by_cases hp : (p : ℕ) = (cs i).pc
          · have hpq : p = q := Fin.ext hp
            rw [hpq, hinstr]
            simpa [Instr.jumpZero, hpcn] using hb0
          · rw [if_neg hp] at hZ; omega
        · exact hb1
      · -- the positive branch
        have hord : ordFlagK P (cs i) q = 1 := by
          unfold ordFlagK
          rw [hinstr]
          simp [Instr.branches, Instr.testReg, hz0]
        have hexec : cs (i + 1)
            = ⟨jpos, Function.update (cs i).regs r ((cs i).regs r - 1)⟩ := by
          rw [hnext, hget, hinstr]
          simp only [Instr.exec]
          rw [if_neg hz0]
        have hpcn : (cs (i + 1)).pc = jpos := by rw [hexec]
        have hpos : 0 < (cs i).regs r := Nat.pos_of_ne_zero hz0
        have hrn : ∀ s, (cs (i + 1)).regs s + (if r = s then 1 else 0) = (cs i).regs s := by
          intro s
          rw [hexec]
          by_cases hs : s = r
          · subst hs; simp; omega
          · simp [Function.update_of_ne hs, Ne.symm hs]
        refine ⟨hsum1, hsumPc.symm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega, ?_⟩ <;>
          (try dsimp only)
        · rw [Finset.sum_add_distrib, hsumA (fun p => (P.get p).jumpPos),
            hsumZ (fun p => (P.get p).jumpZero), hord, hinstr]
          simp [Instr.jumpPos, hpcn]
        · intro s
          rw [hsumA (fun p => (P.get p).lossAt s), hsumA (fun p => (P.get p).gainAt s), hord,
            hinstr]
          simp only [Instr.lossAt, Instr.gainAt, Nat.mul_one, Nat.add_zero]
          exact hrn s
        · intro p
          by_cases hp : (p : ℕ) = (cs i).pc
          · have hpq : p = q := Fin.ext hp
            rw [if_pos hp, hpq, hord, hinstr]
            simp [Instr.branches]
          · simp [hp]
        · intro s hzs
          exfalso
          rw [hsumZ (fun p => (P.get p).lossAt s), hord] at hzs
          simp at hzs
        · intro s
          rw [hsumA (fun p => (P.get p).lossAt s), hord, hinstr]
          simp only [Instr.lossAt, Nat.mul_one]
          have := hrn s
          by_cases hs : r = s
          · subst hs; rw [if_pos rfl] at this ⊢; omega
          · rw [if_neg hs] at this ⊢; omega
        · intro s
          rw [hsumA (fun p => (P.get p).lossAt s), hord, hinstr]
          simp only [Instr.lossAt, Nat.mul_one]
          have := hbr s
          omega
        · intro p hA
          by_cases hp : (p : ℕ) = (cs i).pc
          · have hpq : p = q := Fin.ext hp
            rw [hpq, hinstr]
            simpa [Instr.jumpPos, hpcn] using hb0
          · rw [if_neg hp] at hA; omega
        · intro p hZ
          by_cases hp : (p : ℕ) = (cs i).pc
          · rw [if_pos hp, show p = q from Fin.ext hp, hord] at hZ; omega
          · rw [if_neg hp] at hZ; omega
        · exact hb1
  · rintro ⟨A, Z, res, h⟩ i hi
    obtain ⟨hone, hpcH, hpcN, hupd, hzb, hzero, hres, hresb, htA, htZ, hpb, hrb⟩ := h i hi
    obtain ⟨q, hq1, hq0⟩ := exists_unique_of_sum_eq_one hone
    have hcollapse : ∀ f : Fin P.length → ℕ,
        (∑ p : Fin P.length, f p * (A i p + Z i p)) = f q * (A i q + Z i q) :=
      fun f => sum_eq_of_vanishing fun p hp => by
        have := hq0 p hp; rw [show A i p + Z i p = 0 from by omega, Nat.mul_zero]
    have hpcq : (cs i).pc = (q : ℕ) := by
      rw [hpcH, show (∑ p : Fin P.length, (p : ℕ) * (A i p + Z i p))
        = (q : ℕ) * (A i q + Z i q) from hcollapse _, hq1, mul_one]
    have hpcLt : (cs i).pc < P.length := by rw [hpcq]; exact q.isLt
    have hAZ : (A i q = 1 ∧ Z i q = 0) ∨ (A i q = 0 ∧ Z i q = 1) := by omega
    have hsumA : ∀ f : Fin P.length → ℕ,
        (∑ p : Fin P.length, f p * A i p) = f q * A i q :=
      fun f => sum_eq_of_vanishing fun p hp => by
        have := hq0 p hp; rw [show A i p = 0 from by omega, Nat.mul_zero]
    have hsumZ : ∀ f : Fin P.length → ℕ,
        (∑ p : Fin P.length, f p * Z i p) = f q * Z i q :=
      fun f => sum_eq_of_vanishing fun p hp => by
        have := hq0 p hp; rw [show Z i p = 0 from by omega, Nat.mul_zero]
    have hget : step P (cs i) = (P.get ⟨(cs i).pc, hpcLt⟩).exec (cs i).regs :=
      step_of_getElem? (by simp)
    have hqe : (⟨(cs i).pc, hpcLt⟩ : Fin P.length) = q := Fin.ext hpcq
    rw [hqe] at hget
    have hnext : cs (i + 1) = step P (cs i) := by
      rw [hget]
      rcases hinstr : (P.get q) with ⟨r, j⟩ | ⟨r, jpos, jzero⟩
      · -- an increment: the zero selector is forced off
        have hZq : Z i q = 0 := by
          have := hzb q
          rw [hinstr] at this
          simpa [Instr.branches] using this
        have hAq : A i q = 1 := by omega
        have hpcn : (cs (i + 1)).pc = j := by
          rw [hpcN, Finset.sum_add_distrib, hsumA (fun p => (P.get p).jumpPos),
            hsumZ (fun p => (P.get p).jumpZero), hAq, hZq, hinstr]
          simp [Instr.jumpPos]
        have hrn : ∀ s, (cs (i + 1)).regs s
            = (cs i).regs s + (if r = s then 1 else 0) := by
          intro s
          have hu := hupd s
          rw [hsumA (fun p => (P.get p).lossAt s), hsumA (fun p => (P.get p).gainAt s), hAq,
            hinstr] at hu
          simp only [Instr.lossAt, Instr.gainAt, Nat.mul_one, Nat.add_zero] at hu
          exact hu
        simp only [Instr.exec]
        refine config_ext (by simpa using hpcn) fun s => ?_
        change (cs (i + 1)).regs s = Function.update (cs i).regs r ((cs i).regs r + 1) s
        rcases eq_or_ne s r with rfl | hs
        · rw [Function.update_self]
          have h1 := hrn s
          rw [if_pos rfl] at h1
          omega
        · rw [Function.update_of_ne hs]
          have h1 := hrn s
          rw [if_neg (Ne.symm hs)] at h1
          omega
      · rcases hAZ with ⟨hAq, hZq⟩ | ⟨hAq, hZq⟩
        · -- the positive branch
          have hloss : (∑ p : Fin P.length, (P.get p).lossAt r * A i p) = 1 := by
            rw [hsumA (fun p => (P.get p).lossAt r), hAq, hinstr]
            simp [Instr.lossAt]
          have hpos : 0 < (cs i).regs r := by have := hres r; omega
          have hpcn : (cs (i + 1)).pc = jpos := by
            rw [hpcN, Finset.sum_add_distrib, hsumA (fun p => (P.get p).jumpPos),
              hsumZ (fun p => (P.get p).jumpZero), hAq, hZq, hinstr]
            simp [Instr.jumpPos]
          have hrn : ∀ s, (cs (i + 1)).regs s + (if r = s then 1 else 0) = (cs i).regs s := by
            intro s
            have hu := hupd s
            rw [hsumA (fun p => (P.get p).lossAt s), hsumA (fun p => (P.get p).gainAt s), hAq,
              hinstr] at hu
            simp only [Instr.lossAt, Instr.gainAt, Nat.mul_one, Nat.add_zero] at hu
            exact hu
          simp only [Instr.exec]
          rw [if_neg (by omega : ¬ (cs i).regs r = 0)]
          refine config_ext (by simpa using hpcn) fun s => ?_
          change (cs (i + 1)).regs s = Function.update (cs i).regs r ((cs i).regs r - 1) s
          rcases eq_or_ne s r with rfl | hs
          · rw [Function.update_self]
            have h1 := hrn s
            rw [if_pos rfl] at h1
            omega
          · rw [Function.update_of_ne hs]
            have h1 := hrn s
            rw [if_neg (Ne.symm hs)] at h1
            omega
        · -- the zero branch
          have hzsum : (∑ p : Fin P.length, (P.get p).lossAt r * Z i p) = 1 := by
            rw [hsumZ (fun p => (P.get p).lossAt r), hZq, hinstr]
            simp [Instr.lossAt]
          have hr0 : (cs i).regs r = 0 := hzero r hzsum
          have hpcn : (cs (i + 1)).pc = jzero := by
            rw [hpcN, Finset.sum_add_distrib, hsumA (fun p => (P.get p).jumpPos),
              hsumZ (fun p => (P.get p).jumpZero), hAq, hZq, hinstr]
            simp [Instr.jumpZero]
          have hrn : ∀ s, (cs (i + 1)).regs s = (cs i).regs s := by
            intro s
            have hu := hupd s
            rw [hsumA (fun p => (P.get p).lossAt s), hsumA (fun p => (P.get p).gainAt s),
              hAq] at hu
            simp only [Nat.mul_zero, Nat.add_zero] at hu
            exact hu
          simp only [Instr.exec]
          rw [if_pos hr0]
          exact config_ext (by simpa using hpcn) fun s => by simpa using hrn s
    have hfits : FitsConfig w (step P (cs i)) := by rw [← hnext]; exact hfit (i + 1)
    have := encodedStep_configCode (hfit i) hfits hpcLt
    rwa [← hnext] at this

end RegisterMachine

end Hilbert10


/- Source: Hilbert10.Internal.SelectorRegsGlobal, Hilbert10 v2.3.0, Apache-2.0. -/
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# The selector encoding for many registers: the global layer

#49, phase 4, second layer. `SelectorRegs` reduced the encoded step relation for an
arbitrary `P : Program (k + 1)` to `BlockStepK`. This file packs the blocks.

## The lane family

A configuration of a `k + 1`-register machine has `k + 2` fields, so the lanes are indexed by
`Fin (k + 2)`: lane `0` is the program counter and lane `r.succ` is register `r`. The data width
is `w * (k + 2)` and the outer guarded block is one bit wider. Reassembly is

```
R = ∑ j : Fin (k + 2), (2 ^ w) ^ (j : ℕ) * X j
```

which is `fieldsCode_configCode_eq_lanes` at register arity `k + 1`. Blockwise it says the block
of `R` is the `fieldsCode` of its lanes' blocks, so the decoder reads each lane off directly —
the one-register file had to do this by hand with a `mod` and a `div`.

The residuals stay indexed by `Fin (k + 1)`: they are per *register*, not per field, since the
program counter has no residual.

## What did not change

The selector family is still one per branch, still one-hot across the program, and still
independent of the register count. Every register equation is bounded by `subSum_le_one`, so no
new carry appears. The masks are the same two constants at the wider block.

## Scope

`globalConditionsK_iff` is the equivalence. Packaging it into `Aggregation (k + 1)` is
`SelectorRegsDioph`, the layer above.
-/

namespace Hilbert10

namespace RegisterMachine

variable {k : ℕ} {P : Program (k + 1)} {w n R : ℕ}

/-! ### Masks at an arbitrary block width -/

/-- The `w`-bit data mask over `t` blocks of width `W`. -/
def laneMaskAt (W w t : ℕ) : ℕ := (2 ^ w - 1) * geom (2 ^ W) t

/-- The one-bit-per-block mask over `t` blocks of width `W`. -/
def bitMaskAt (W t : ℕ) : ℕ := geom (2 ^ W) t

theorem lane_normAt {W w t X : ℕ} (hv : w ≤ W) (h : Nat.IsBinarySubmask X (laneMaskAt W w t)) :
    X = fieldsCode W (fun i : Fin t => configField W X i) ∧
      ∀ i : Fin t, configField W X i < 2 ^ w :=
  packed_eq_fieldsCode hv h

theorem selector_normAt {W t S : ℕ} (hW : 1 ≤ W)
    (h : Nat.IsBinarySubmask S (bitMaskAt W t)) :
    S = fieldsCode W (fun i : Fin t => configField W S i) ∧
      ∀ i : Fin t, configField W S i < 2 := by
  have hb : Nat.IsBinarySubmask S ((2 ^ 1 - 1) * geom (2 ^ W) t) := by
    simpa [bitMaskAt] using h
  have := packed_eq_fieldsCode (v := 1) (W := W) hW hb
  simpa using this

theorem laneOfAt {W w t : ℕ} (hv : w ≤ W) (f : Fin t → ℕ) (hf : ∀ i, f i < 2 ^ w) :
    Nat.IsBinarySubmask (fieldsCode W f) (laneMaskAt W w t) := by
  have hlt : (2 : ℕ) ^ w ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) hv
  rw [laneMaskAt]
  refine (isBinarySubmask_constMask_iff hv).mpr
    ⟨fieldsCode_lt (fun i => lt_of_lt_of_le (hf i) hlt), fun i hi => ?_⟩
  rw [field_fieldsCode (fun j => lt_of_lt_of_le (hf j) hlt) ⟨i, hi⟩]
  exact hf ⟨i, hi⟩

theorem bitOfAt {W t : ℕ} (hW : 1 ≤ W) (f : Fin t → ℕ) (hf : ∀ i, f i < 2) :
    Nat.IsBinarySubmask (fieldsCode W f) (bitMaskAt W t) := by
  have hlt : (2 : ℕ) ≤ 2 ^ W := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) hW
  rw [bitMaskAt, show geom (2 ^ W) t = (2 ^ 1 - 1) * geom (2 ^ W) t from by norm_num]
  refine (isBinarySubmask_constMask_iff (v := 1) hW).mpr
    ⟨fieldsCode_lt (fun i => lt_of_lt_of_le (hf i) hlt), fun i hi => ?_⟩
  rw [field_fieldsCode (fun j => lt_of_lt_of_le (hf j) hlt) ⟨i, hi⟩]
  simpa using hf ⟨i, hi⟩

/-! ### Branches -/

/-- The instruction index a branch belongs to. -/
def branchIdx (P : Program (k + 1)) : Fin P.length ⊕ Fin P.length → ℕ
  | .inl p => (p : ℕ)
  | .inr p => (p : ℕ)

/-- The target a branch jumps to. -/
def branchTgt (P : Program (k + 1)) : Fin P.length ⊕ Fin P.length → ℕ
  | .inl p => (P.get p).jumpPos
  | .inr p => (P.get p).jumpZero

theorem branchIdx_lt (hlen : P.length < 2 ^ w) (c : Fin P.length ⊕ Fin P.length) :
    branchIdx P c < 2 ^ w := by
  cases c with
  | inl p => exact lt_of_lt_of_le p.isLt (by omega)
  | inr p => exact lt_of_lt_of_le p.isLt (by omega)

/-! ### Carry bounds at the wider block -/

theorem two_pow_lt_block (w k : ℕ) : 2 ^ w < 2 ^ (w * (k + 2) + 1) :=
  Nat.pow_lt_pow_right (by norm_num) (by nlinarith)

theorem two_mul_length_lt_block (hlen : P.length < 2 ^ w) :
    2 * P.length < 2 ^ (w * (k + 2) + 1) := by
  have h1 : (2 : ℕ) ^ (w + 1) ≤ 2 ^ (w * (k + 2) + 1) :=
    Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have h2 : (2 : ℕ) ^ (w + 1) = 2 * 2 ^ w := by rw [pow_succ]; ring
  omega

/-- The zero branch's carry bound at the wider block. -/
theorem zero_carry_block {x s z : ℕ} (hx : x < 2 ^ w) (hs : s ≤ 1) (hz : z < 2 ^ w) :
    x + s * (2 ^ w - 1) + z < 2 ^ (w * (k + 2) + 1) := by
  have hpos : 0 < (2 : ℕ) ^ w := Nat.two_pow_pos w
  have hpos2 : 0 < (2 : ℕ) ^ (w * (k + 2) + 1) := Nat.two_pow_pos _
  have hdouble : (2 : ℕ) ^ (w * (k + 2) + 1) = 2 * 2 ^ (w * (k + 2)) := by rw [pow_succ]; ring
  have hsq : (2 : ℕ) ^ w * 2 ^ w ≤ 2 ^ (w * (k + 2)) := by
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have hsb : s * (2 ^ w - 1) ≤ 2 ^ w - 1 := by
    calc s * (2 ^ w - 1) ≤ 1 * (2 ^ w - 1) := Nat.mul_le_mul_right _ hs
      _ = 2 ^ w - 1 := one_mul _
  rcases Nat.lt_or_ge (2 ^ w) 2 with hsmall | hbig
  · have h1 : (2 : ℕ) ^ w = 1 := by omega
    have hzero : x + s * (2 ^ w - 1) + z = 0 := by rw [h1]; omega
    omega
  · have h4 : 2 * 2 ^ w ≤ 2 ^ w * 2 ^ w := Nat.mul_le_mul_right _ hbig
    omega

/-! ### The global conditions -/

/-- **The global selector conditions for an arbitrary program on `k + 1` registers.**

`X j` is lane `j` of the packed run: `X 0` the program counter, `X r.succ` register `r`.
`S (.inl p)` and `S (.inr p)` are instruction `p`'s two branch lanes, and `Res r`, `Zres r` are
register `r`'s two residual lanes. -/
def GlobalConditionsK (P : Program (k + 1)) (w n R : ℕ) (X : Fin (k + 2) → ℕ)
    (S : Fin P.length ⊕ Fin P.length → ℕ) (Res Zres : Fin (k + 1) → ℕ) : Prop :=
  P.length < 2 ^ w ∧
  (∀ j, Nat.IsBinarySubmask (X j) (laneMaskAt (w * (k + 2) + 1) w (n + 1))) ∧
  R = ∑ j : Fin (k + 2), (2 ^ w) ^ (j : ℕ) * X j ∧
  (∀ c, Nat.IsBinarySubmask (S c) (bitMaskAt (w * (k + 2) + 1) n)) ∧
  (∑ c, S c) = bitMaskAt (w * (k + 2) + 1) n ∧
  X 0 % (2 ^ (w * (k + 2) + 1)) ^ n = ∑ c, branchIdx P c * S c ∧
  X 0 / 2 ^ (w * (k + 2) + 1) = ∑ c, branchTgt P c * S c ∧
  (∀ r, X r.succ / 2 ^ (w * (k + 2) + 1)
      + ∑ p : Fin P.length, (P.get p).lossAt r * S (.inl p)
    = X r.succ % (2 ^ (w * (k + 2) + 1)) ^ n
      + ∑ p : Fin P.length, (P.get p).gainAt r * S (.inl p)) ∧
  (∀ p, (P.get p).branches = 0 → S (.inr p) = 0) ∧
  (∀ r, X r.succ % (2 ^ (w * (k + 2) + 1)) ^ n
      + (∑ p : Fin P.length, (P.get p).lossAt r * S (.inr p)) * (2 ^ w - 1) + Zres r
    = laneMaskAt (w * (k + 2) + 1) w n) ∧
  (∀ r, Nat.IsBinarySubmask (Zres r) (laneMaskAt (w * (k + 2) + 1) w n)) ∧
  (∀ r, X r.succ % (2 ^ (w * (k + 2) + 1)) ^ n
    = Res r + ∑ p : Fin P.length, (P.get p).lossAt r * S (.inl p)) ∧
  (∀ r, Nat.IsBinarySubmask (Res r) (laneMaskAt (w * (k + 2) + 1) w n)) ∧
  (∀ c, S c = 0 ∨ branchTgt P c < 2 ^ w)

/-! ### Soundness -/

/-- **Soundness of the global system.** -/
theorem globalConditionsK_sound {X : Fin (k + 2) → ℕ}
    {S : Fin P.length ⊕ Fin P.length → ℕ} {Res Zres : Fin (k + 1) → ℕ}
    (h : GlobalConditionsK P w n R X S Res Zres) :
    P.length < 2 ^ w ∧
      Nat.IsBinarySubmask R (guardMask (w * (k + 2)) (n + 1)) ∧
      ∀ i < n, EncodedStep P w (configField (w * (k + 2) + 1) R i)
        (configField (w * (k + 2) + 1) R (i + 1)) := by
  obtain ⟨hlen, hmX, hR, hmS, hsum, hpcEq, hjump, hupd, hzb, hzeq, hzm, hres, hresm, htgt⟩ := h
  have hwW : w ≤ w * (k + 2) + 1 := by nlinarith
  have h1W : 1 ≤ w * (k + 2) + 1 := by omega
  have hwlt : (2 : ℕ) ^ w < 2 ^ (w * (k + 2) + 1) := two_pow_lt_block w k
  have hpowmul : ((2 : ℕ) ^ w) ^ (k + 2) = 2 ^ (w * (k + 2)) := by rw [← pow_mul]
  have hstep : (2 : ℕ) ^ (w * (k + 2)) < 2 ^ (w * (k + 2) + 1) :=
    Nat.pow_lt_pow_right (by norm_num) (by omega)
  -- normalise every packed witness once
  have eX : ∀ j, X j = fieldsCode (w * (k + 2) + 1)
      (fun i : Fin (n + 1) => configField (w * (k + 2) + 1) (X j) i) :=
    fun j => (lane_normAt hwW (hmX j)).1
  have bX : ∀ j, ∀ i : Fin (n + 1), configField (w * (k + 2) + 1) (X j) i < 2 ^ w :=
    fun j => (lane_normAt hwW (hmX j)).2
  have eS : ∀ c, S c = fieldsCode (w * (k + 2) + 1)
      (fun i : Fin n => configField (w * (k + 2) + 1) (S c) i) :=
    fun c => (selector_normAt h1W (hmS c)).1
  have bS : ∀ c, ∀ i : Fin n, configField (w * (k + 2) + 1) (S c) i < 2 :=
    fun c => (selector_normAt h1W (hmS c)).2
  have eRes : ∀ r, Res r = fieldsCode (w * (k + 2) + 1)
      (fun i : Fin n => configField (w * (k + 2) + 1) (Res r) i) :=
    fun r => (lane_normAt hwW (hresm r)).1
  have bRes : ∀ r, ∀ i : Fin n, configField (w * (k + 2) + 1) (Res r) i < 2 ^ w :=
    fun r => (lane_normAt hwW (hresm r)).2
  have bZres : ∀ r, ∀ i : Fin n, configField (w * (k + 2) + 1) (Zres r) i < 2 ^ w :=
    fun r => (lane_normAt hwW (hzm r)).2
  have eZres : ∀ r, Zres r = fieldsCode (w * (k + 2) + 1)
      (fun i : Fin n => configField (w * (k + 2) + 1) (Zres r) i) :=
    fun r => (lane_normAt hwW (hzm r)).1
  -- the lanes reassemble `R` blockwise
  have hbd : ∀ i : Fin (n + 1),
      fieldsCode w (fun j : Fin (k + 2) => configField (w * (k + 2) + 1) (X j) i)
        < 2 ^ (w * (k + 2) + 1) := by
    intro i
    have h1 := fieldsCode_lt (w := w) (fun j : Fin (k + 2) => bX j i)
    omega
  have hRe : R = fieldsCode (w * (k + 2) + 1) (fun i : Fin (n + 1) =>
      fieldsCode w (fun j : Fin (k + 2) => configField (w * (k + 2) + 1) (X j) i)) := by
    rw [hR, show (∑ j : Fin (k + 2), (2 ^ w) ^ (j : ℕ) * X j)
        = ∑ j : Fin (k + 2), (2 ^ w) ^ (j : ℕ) * fieldsCode (w * (k + 2) + 1)
          (fun i : Fin (n + 1) => configField (w * (k + 2) + 1) (X j) i) from
      Finset.sum_congr rfl fun j _ => congrArg _ (eX j),
      fieldsCode_sum_smul]
    exact congrArg _ (funext fun i => (fieldsCode_eq_sum w _).symm)
  have hblk : ∀ i : Fin (n + 1), configField (w * (k + 2) + 1) R i
      = fieldsCode w (fun j : Fin (k + 2) => configField (w * (k + 2) + 1) (X j) i) := by
    intro i
    rw [hRe, field_fieldsCode hbd i]
  have hRblk : ∀ i : Fin (n + 1), configField (w * (k + 2) + 1) R i < 2 ^ (w * (k + 2)) := by
    intro i
    rw [hblk i]
    have h1 := fieldsCode_lt (w := w) (fun j : Fin (k + 2) => bX j i)
    omega
  have hRlt : R < (2 ^ (w * (k + 2) + 1)) ^ (n + 1) := by
    rw [hRe]
    exact fieldsCode_lt hbd
  refine ⟨hlen, isBinarySubmask_guardMask_iff.mpr ⟨hRlt, fun i hi => hRblk ⟨i, hi⟩⟩, ?_⟩
  -- decode: each lane is read off directly
  set cs : ℕ → Config (k + 1) :=
    fun i => decodeConfig w (configField (w * (k + 2) + 1) R i) with hcs
  have hcode : ∀ i : Fin (n + 1), configCode w (cs i) = configField (w * (k + 2) + 1) R i :=
    fun i => configCode_decodeConfig (by simpa using hRblk i)
  have hfitcs : ∀ i, FitsConfig w (cs i) := fun _ => fits_decodeConfig
  have hlane : ∀ (i : Fin (n + 1)) (j : Fin (k + 2)),
      configField w (configField (w * (k + 2) + 1) R i) (j : ℕ)
        = configField (w * (k + 2) + 1) (X j) i := by
    intro i j
    rw [hblk i, field_fieldsCode (fun j => bX j i) j]
  have hpcv : ∀ i : Fin (n + 1), (cs i).pc = configField (w * (k + 2) + 1) (X 0) i := by
    intro i
    change configField w (configField (w * (k + 2) + 1) R i) 0 = _
    exact hlane i 0
  have hregv : ∀ (i : Fin (n + 1)) (r : Fin (k + 1)),
      (cs i).regs r = configField (w * (k + 2) + 1) (X r.succ) i := by
    intro i r
    change configField w (configField (w * (k + 2) + 1) R i) ((r : ℕ) + 1) = _
    exact hlane i r.succ
  -- the selectors are one-hot in every block
  have hone : ∀ i : Fin n,
      (∑ c : Fin P.length ⊕ Fin P.length, configField (w * (k + 2) + 1) (S c) i) = 1 := by
    have hbit : bitMaskAt (w * (k + 2) + 1) n
        = fieldsCode (w * (k + 2) + 1) (fun _ : Fin n => 1) := by
      rw [fieldsCode_const]; simp [bitMaskAt]
    have hkey : fieldsCode (w * (k + 2) + 1)
        (fun i : Fin n => ∑ c : Fin P.length ⊕ Fin P.length,
          configField (w * (k + 2) + 1) (S c) i)
        = fieldsCode (w * (k + 2) + 1) (fun _ : Fin n => 1) := by
      rw [← fieldsCode_sum (w * (k + 2) + 1) Finset.univ
        (fun c => fun i : Fin n => configField (w * (k + 2) + 1) (S c) i),
        show (∑ c : Fin P.length ⊕ Fin P.length, fieldsCode (w * (k + 2) + 1)
            (fun i : Fin n => configField (w * (k + 2) + 1) (S c) i))
            = ∑ c : Fin P.length ⊕ Fin P.length, S c from
          Finset.sum_congr rfl fun c _ => (eS c).symm, hsum, hbit]
    have hcard : Fintype.card (Fin P.length ⊕ Fin P.length) = 2 * P.length := by
      rw [Fintype.card_sum, Fintype.card_fin]; ring
    have h2L : 2 * P.length < 2 ^ (w * (k + 2) + 1) := two_mul_length_lt_block hlen
    have hbdd : ∀ i : Fin n,
        (∑ c : Fin P.length ⊕ Fin P.length, configField (w * (k + 2) + 1) (S c) i)
          < 2 ^ (w * (k + 2) + 1) := by
      intro i
      have hle : (∑ c : Fin P.length ⊕ Fin P.length, configField (w * (k + 2) + 1) (S c) i)
          ≤ ∑ _c : Fin P.length ⊕ Fin P.length, 1 :=
        Finset.sum_le_sum fun c _ => by have := bS c i; omega
      simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, hcard] at hle
      omega
    have hone_lt : (1 : ℕ) < 2 ^ (w * (k + 2) + 1) := by
      calc (1 : ℕ) < 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (w * (k + 2) + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact fun i => congrFun (fieldsCode_injective hbdd (fun _ => hone_lt) hkey) i
  have honeL : ∀ i : Fin n, (∑ p : Fin P.length,
      (configField (w * (k + 2) + 1) (S (.inl p)) i
        + configField (w * (k + 2) + 1) (S (.inr p)) i)) = 1 := by
    intro i
    calc (∑ p : Fin P.length, (configField (w * (k + 2) + 1) (S (.inl p)) i
          + configField (w * (k + 2) + 1) (S (.inr p)) i))
        = (∑ p : Fin P.length, configField (w * (k + 2) + 1) (S (.inl p)) i)
            + ∑ p : Fin P.length, configField (w * (k + 2) + 1) (S (.inr p)) i :=
          Finset.sum_add_distrib
      _ = ∑ c : Fin P.length ⊕ Fin P.length, configField (w * (k + 2) + 1) (S c) i :=
          (Fintype.sum_sum_type (fun c => configField (w * (k + 2) + 1) (S c) i)).symm
      _ = 1 := hone i
  -- truncation and shift, for every lane
  have hmod : ∀ j : Fin (k + 2), X j % (2 ^ (w * (k + 2) + 1)) ^ n
      = fieldsCode (w * (k + 2) + 1)
        (fun i : Fin n => configField (w * (k + 2) + 1) (X j) i) := by
    intro j
    conv_lhs => rw [eX j]
    exact fieldsCode_mod_pow (fun i => lt_trans (bX j i) hwlt)
  have hdiv : ∀ j : Fin (k + 2), X j / 2 ^ (w * (k + 2) + 1)
      = fieldsCode (w * (k + 2) + 1)
        (fun i : Fin n => configField (w * (k + 2) + 1) (X j) ((i : ℕ) + 1)) := by
    intro j
    conv_lhs => rw [eX j]
    exact fieldsCode_div _ _ (lt_trans (bX j 0) hwlt)
  -- the sub-sums, blockwise
  have hsubA : ∀ (g : Fin P.length → ℕ), (∀ p, g p ≤ 1) → ∀ i : Fin n,
      (∑ p : Fin P.length, g p * configField (w * (k + 2) + 1) (S (.inl p)) i) ≤ 1 :=
    fun g hg i => (subSum_le_one hg (honeL i)).1
  have hsubZ : ∀ (g : Fin P.length → ℕ), (∀ p, g p ≤ 1) → ∀ i : Fin n,
      (∑ p : Fin P.length, g p * configField (w * (k + 2) + 1) (S (.inr p)) i) ≤ 1 :=
    fun g hg i => (subSum_le_one hg (honeL i)).2
  have hlossle : ∀ r : Fin (k + 1), ∀ p : Fin P.length, (P.get p).lossAt r ≤ 1 :=
    fun r p => Instr.lossAt_le_one r _
  have hgainle : ∀ r : Fin (k + 1), ∀ p : Fin P.length, (P.get p).gainAt r ≤ 1 :=
    fun r p => Instr.gainAt_le_one r _
  -- the aggregate equations, blockwise
  have hA : ∀ i : Fin n, configField (w * (k + 2) + 1) (X 0) i
      = ∑ p : Fin P.length, (p : ℕ) * (configField (w * (k + 2) + 1) (S (.inl p)) i
        + configField (w * (k + 2) + 1) (S (.inr p)) i) := by
    have heq : (∑ c : Fin P.length ⊕ Fin P.length, branchIdx P c * fieldsCode (w * (k + 2) + 1)
        (fun i : Fin n => configField (w * (k + 2) + 1) (S c) i))
        = fieldsCode (w * (k + 2) + 1)
          (fun i : Fin n => configField (w * (k + 2) + 1) (X 0) i) := by
      rw [← hmod 0, hpcEq]
      exact Finset.sum_congr rfl fun c _ => congrArg _ (eS c).symm
    have hkey := (fieldsCode_selected_smul_eq_iff (m := branchIdx P) hone
      (fun c _ => Or.inr (lt_trans (branchIdx_lt hlen c) hwlt))
      (fun i => lt_trans (bX 0 i.castSucc) hwlt)).mp heq
    intro i
    calc configField (w * (k + 2) + 1) (X 0) i
        = ∑ c : Fin P.length ⊕ Fin P.length,
            branchIdx P c * configField (w * (k + 2) + 1) (S c) i := (hkey i).symm
      _ = (∑ p : Fin P.length,
            branchIdx P (.inl p) * configField (w * (k + 2) + 1) (S (.inl p)) i)
            + ∑ p : Fin P.length,
              branchIdx P (.inr p) * configField (w * (k + 2) + 1) (S (.inr p)) i :=
          Fintype.sum_sum_type (fun c => branchIdx P c * configField (w * (k + 2) + 1) (S c) i)
      _ = ∑ p : Fin P.length, ((p : ℕ) * configField (w * (k + 2) + 1) (S (.inl p)) i
            + (p : ℕ) * configField (w * (k + 2) + 1) (S (.inr p)) i) :=
          Finset.sum_add_distrib.symm
      _ = ∑ p : Fin P.length, (p : ℕ) * (configField (w * (k + 2) + 1) (S (.inl p)) i
            + configField (w * (k + 2) + 1) (S (.inr p)) i) :=
          Finset.sum_congr rfl fun p _ => (Nat.mul_add _ _ _).symm
  have hB : ∀ i : Fin n, configField (w * (k + 2) + 1) (X 0) ((i : ℕ) + 1)
      = ∑ p : Fin P.length, ((P.get p).jumpPos * configField (w * (k + 2) + 1) (S (.inl p)) i
        + (P.get p).jumpZero * configField (w * (k + 2) + 1) (S (.inr p)) i) := by
    have heq : (∑ c : Fin P.length ⊕ Fin P.length, branchTgt P c * fieldsCode (w * (k + 2) + 1)
        (fun i : Fin n => configField (w * (k + 2) + 1) (S c) i))
        = fieldsCode (w * (k + 2) + 1)
          (fun i : Fin n => configField (w * (k + 2) + 1) (X 0) ((i : ℕ) + 1)) := by
      rw [← hdiv 0, hjump]
      exact Finset.sum_congr rfl fun c _ => congrArg _ (eS c).symm
    have hkey := (fieldsCode_selected_smul_eq_iff (m := branchTgt P) hone
      (fun c _ => by
        rcases htgt c with hzero | hfit
        · exact Or.inl fun i => by rw [hzero]; simp [configField]
        · exact Or.inr (lt_trans hfit hwlt))
      (fun i => by
        have h1 : configField (w * (k + 2) + 1) (X 0) ((i : ℕ) + 1) < 2 ^ w :=
          bX 0 ⟨(i : ℕ) + 1, by omega⟩
        exact lt_trans h1 hwlt)).mp heq
    intro i
    calc configField (w * (k + 2) + 1) (X 0) ((i : ℕ) + 1)
        = ∑ c : Fin P.length ⊕ Fin P.length,
            branchTgt P c * configField (w * (k + 2) + 1) (S c) i := (hkey i).symm
      _ = (∑ p : Fin P.length,
            branchTgt P (.inl p) * configField (w * (k + 2) + 1) (S (.inl p)) i)
            + ∑ p : Fin P.length,
              branchTgt P (.inr p) * configField (w * (k + 2) + 1) (S (.inr p)) i :=
          Fintype.sum_sum_type (fun c => branchTgt P c * configField (w * (k + 2) + 1) (S c) i)
      _ = ∑ p : Fin P.length,
            ((P.get p).jumpPos * configField (w * (k + 2) + 1) (S (.inl p)) i
              + (P.get p).jumpZero * configField (w * (k + 2) + 1) (S (.inr p)) i) :=
          Finset.sum_add_distrib.symm
  have hC : ∀ (r : Fin (k + 1)) (i : Fin n),
      configField (w * (k + 2) + 1) (X r.succ) ((i : ℕ) + 1)
        + ∑ p : Fin P.length,
          (P.get p).lossAt r * configField (w * (k + 2) + 1) (S (.inl p)) i
      = configField (w * (k + 2) + 1) (X r.succ) i
        + ∑ p : Fin P.length,
          (P.get p).gainAt r * configField (w * (k + 2) + 1) (S (.inl p)) i := by
    intro r
    have heq : fieldsCode (w * (k + 2) + 1)
        (fun i : Fin n => configField (w * (k + 2) + 1) (X r.succ) ((i : ℕ) + 1)
          + ∑ p : Fin P.length,
            (P.get p).lossAt r * configField (w * (k + 2) + 1) (S (.inl p)) i)
        = fieldsCode (w * (k + 2) + 1)
          (fun i : Fin n => configField (w * (k + 2) + 1) (X r.succ) i
            + ∑ p : Fin P.length,
              (P.get p).gainAt r * configField (w * (k + 2) + 1) (S (.inl p)) i) := by
      rw [← fieldsCode_add, ← fieldsCode_add, ← fieldsCode_sum_smul, ← fieldsCode_sum_smul,
        ← hdiv r.succ, ← hmod r.succ,
        show (∑ p : Fin P.length, (P.get p).lossAt r * fieldsCode (w * (k + 2) + 1)
            (fun i : Fin n => configField (w * (k + 2) + 1) (S (.inl p)) i))
          = ∑ p : Fin P.length, (P.get p).lossAt r * S (.inl p) from
            Finset.sum_congr rfl fun p _ => congrArg _ (eS _).symm,
        show (∑ p : Fin P.length, (P.get p).gainAt r * fieldsCode (w * (k + 2) + 1)
            (fun i : Fin n => configField (w * (k + 2) + 1) (S (.inl p)) i))
          = ∑ p : Fin P.length, (P.get p).gainAt r * S (.inl p) from
            Finset.sum_congr rfl fun p _ => congrArg _ (eS _).symm]
      exact hupd r
    refine fun i => congrFun (fieldsCode_injective (fun i => ?_) (fun i => ?_) heq) i
    · have h1 : configField (w * (k + 2) + 1) (X r.succ) ((i : ℕ) + 1) < 2 ^ w :=
        bX r.succ ⟨(i : ℕ) + 1, by omega⟩
      have h2 := hsubA (fun p => (P.get p).lossAt r) (hlossle r) i
      omega
    · have h1 : configField (w * (k + 2) + 1) (X r.succ) (i : ℕ) < 2 ^ w :=
        bX r.succ i.castSucc
      have h2 := hsubA (fun p => (P.get p).gainAt r) (hgainle r) i
      omega
  have hD : ∀ (r : Fin (k + 1)) (i : Fin n),
      configField (w * (k + 2) + 1) (X r.succ) i
      + (∑ p : Fin P.length,
          (P.get p).lossAt r * configField (w * (k + 2) + 1) (S (.inr p)) i) * (2 ^ w - 1)
      + configField (w * (k + 2) + 1) (Zres r) i = 2 ^ w - 1 := by
    intro r
    have hlaneEq : laneMaskAt (w * (k + 2) + 1) w n
        = fieldsCode (w * (k + 2) + 1) (fun _ : Fin n => 2 ^ w - 1) :=
      (fieldsCode_const _ _).symm
    have heq : fieldsCode (w * (k + 2) + 1)
        (fun i : Fin n => configField (w * (k + 2) + 1) (X r.succ) i
          + (∑ p : Fin P.length,
              (P.get p).lossAt r * configField (w * (k + 2) + 1) (S (.inr p)) i) * (2 ^ w - 1)
          + configField (w * (k + 2) + 1) (Zres r) i)
        = fieldsCode (w * (k + 2) + 1) (fun _ : Fin n => 2 ^ w - 1) := by
      rw [← fieldsCode_add, ← fieldsCode_add, ← hlaneEq, ← hzeq r, ← hmod r.succ, ← eZres r,
        show (fun i : Fin n => (∑ p : Fin P.length,
            (P.get p).lossAt r * configField (w * (k + 2) + 1) (S (.inr p)) i) * (2 ^ w - 1))
          = (fun i : Fin n => (2 ^ w - 1) * ∑ p : Fin P.length,
            (P.get p).lossAt r * configField (w * (k + 2) + 1) (S (.inr p)) i) from
            funext fun i => Nat.mul_comm _ _,
        ← fieldsCode_smul, ← fieldsCode_sum_smul,
        show (∑ p : Fin P.length, (P.get p).lossAt r * fieldsCode (w * (k + 2) + 1)
            (fun i : Fin n => configField (w * (k + 2) + 1) (S (.inr p)) i))
          = ∑ p : Fin P.length, (P.get p).lossAt r * S (.inr p) from
            Finset.sum_congr rfl fun p _ => congrArg _ (eS _).symm]
      rw [Nat.mul_comm (2 ^ w - 1)
        (∑ p : Fin P.length, (P.get p).lossAt r * S (.inr p))]
    refine fun i => congrFun (fieldsCode_injective (fun i => ?_)
      (fun _ => lt_trans (by omega : 2 ^ w - 1 < 2 ^ w) hwlt) heq) i
    have h1 : configField (w * (k + 2) + 1) (X r.succ) (i : ℕ) < 2 ^ w := bX r.succ i.castSucc
    exact zero_carry_block h1 (hsubZ (fun p => (P.get p).lossAt r) (hlossle r) i) (bZres r i)
  have hE : ∀ (r : Fin (k + 1)) (i : Fin n),
      configField (w * (k + 2) + 1) (X r.succ) i
        = configField (w * (k + 2) + 1) (Res r) i
          + ∑ p : Fin P.length,
            (P.get p).lossAt r * configField (w * (k + 2) + 1) (S (.inl p)) i := by
    intro r
    have heq : fieldsCode (w * (k + 2) + 1)
        (fun i : Fin n => configField (w * (k + 2) + 1) (X r.succ) i)
        = fieldsCode (w * (k + 2) + 1)
          (fun i : Fin n => configField (w * (k + 2) + 1) (Res r) i
            + ∑ p : Fin P.length,
              (P.get p).lossAt r * configField (w * (k + 2) + 1) (S (.inl p)) i) := by
      rw [← fieldsCode_add, ← fieldsCode_sum_smul, ← hmod r.succ, ← eRes r,
        show (∑ p : Fin P.length, (P.get p).lossAt r * fieldsCode (w * (k + 2) + 1)
            (fun i : Fin n => configField (w * (k + 2) + 1) (S (.inl p)) i))
          = ∑ p : Fin P.length, (P.get p).lossAt r * S (.inl p) from
            Finset.sum_congr rfl fun p _ => congrArg _ (eS _).symm]
      exact hres r
    refine fun i => congrFun (fieldsCode_injective
      (fun i => lt_trans (show configField (w * (k + 2) + 1) (X r.succ) (i : ℕ) < 2 ^ w from
        bX r.succ i.castSucc) hwlt) (fun i => ?_) heq) i
    have h1 : configField (w * (k + 2) + 1) (Res r) (i : ℕ) < 2 ^ w := bRes r i
    have h2 := hsubA (fun p => (P.get p).lossAt r) (hlossle r) i
    omega
  -- assemble
  intro i hi
  rw [show configField (w * (k + 2) + 1) R i = configCode w (cs i) from (hcode ⟨i, by omega⟩).symm,
    show configField (w * (k + 2) + 1) R (i + 1) = configCode w (cs (i + 1)) from
      (hcode ⟨i + 1, by omega⟩).symm]
  refine (blockStepK_iff P w n cs hfitcs).mpr
    ⟨fun i p => configField (w * (k + 2) + 1) (S (.inl p)) i,
      fun i p => configField (w * (k + 2) + 1) (S (.inr p)) i,
      fun i r => configField (w * (k + 2) + 1) (Res r) i, ?_⟩ i hi
  intro j hj
  dsimp only
  refine ⟨honeL ⟨j, hj⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show (cs j).pc = configField (w * (k + 2) + 1) (X 0) j from hpcv ⟨j, by omega⟩]
    exact hA ⟨j, hj⟩
  · rw [show (cs (j + 1)).pc = configField (w * (k + 2) + 1) (X 0) (j + 1) from
      hpcv ⟨j + 1, by omega⟩]
    exact hB ⟨j, hj⟩
  · intro r
    rw [show (cs (j + 1)).regs r = configField (w * (k + 2) + 1) (X r.succ) (j + 1) from
        hregv ⟨j + 1, by omega⟩ r,
      show (cs j).regs r = configField (w * (k + 2) + 1) (X r.succ) j from hregv ⟨j, by omega⟩ r]
    exact hC r ⟨j, hj⟩
  · intro p
    dsimp only
    rcases Nat.eq_zero_or_pos ((P.get p).branches) with hz | hz
    · rw [hzb p hz]
      simp [configField]
    · have h1 : configField (w * (k + 2) + 1) (S (.inr p)) j < 2 := bS (.inr p) ⟨j, hj⟩
      omega
  · intro r hzsum
    have hd := hD r ⟨j, hj⟩
    dsimp only at hd
    rw [hzsum, one_mul] at hd
    rw [show (cs j).regs r = configField (w * (k + 2) + 1) (X r.succ) j from hregv ⟨j, by omega⟩ r]
    have h1 : configField (w * (k + 2) + 1) (X r.succ) j < 2 ^ w :=
      bX r.succ (⟨j, by omega⟩ : Fin (n + 1))
    have h2 : configField (w * (k + 2) + 1) (Zres r) j < 2 ^ w := bZres r (⟨j, hj⟩ : Fin n)
    have h3 : 0 < (2 : ℕ) ^ w := Nat.two_pow_pos w
    omega
  · intro r
    rw [show (cs j).regs r = configField (w * (k + 2) + 1) (X r.succ) j from hregv ⟨j, by omega⟩ r]
    exact hE r ⟨j, hj⟩
  · exact fun r => bRes r ⟨j, hj⟩
  · intro p hA1
    dsimp only at hA1
    rcases htgt (.inl p) with hzero | hfit
    · rw [hzero] at hA1; simp [configField] at hA1
    · exact hfit
  · intro p hZ1
    dsimp only at hZ1
    rcases htgt (.inr p) with hzero | hfit
    · rw [hzero] at hZ1; simp [configField] at hZ1
    · exact hfit
  · exact (hfitcs (j + 1)).1
  · exact (hfitcs (j + 1)).2

/-! ### Completeness -/

/-- **Completeness of the global system.** -/
theorem globalConditionsK_complete (hlen : P.length < 2 ^ w)
    (hmask : Nat.IsBinarySubmask R (guardMask (w * (k + 2)) (n + 1)))
    (hstep : ∀ i < n, EncodedStep P w (configField (w * (k + 2) + 1) R i)
      (configField (w * (k + 2) + 1) R (i + 1))) :
    ∃ (X : Fin (k + 2) → ℕ) (S : Fin P.length ⊕ Fin P.length → ℕ)
      (Res Zres : Fin (k + 1) → ℕ), GlobalConditionsK P w n R X S Res Zres := by
  have hwW : w ≤ w * (k + 2) + 1 := by nlinarith
  have h1W : 1 ≤ w * (k + 2) + 1 := by omega
  have hwlt : (2 : ℕ) ^ w < 2 ^ (w * (k + 2) + 1) := two_pow_lt_block w k
  obtain ⟨hRlt, hRblk⟩ := isBinarySubmask_guardMask_iff.mp hmask
  have hRlt' : R < (2 ^ (w * (k + 2) + 1)) ^ (n + 1) := hRlt
  set cs : ℕ → Config (k + 1) :=
    fun i => decodeConfig w (configField (w * (k + 2) + 1) R i) with hcs
  have hblkR : ∀ i : Fin (n + 1), configField (w * (k + 2) + 1) R i < 2 ^ (w * (k + 2)) :=
    fun i => hRblk i i.isLt
  have hfitcs : ∀ i, FitsConfig w (cs i) := fun _ => fits_decodeConfig
  have hcode : ∀ i : Fin (n + 1), configCode w (cs i) = configField (w * (k + 2) + 1) R i :=
    fun i => configCode_decodeConfig (by simpa using hblkR i)
  have hstep' : ∀ i < n,
      EncodedStep P w (configCode w (cs i)) (configCode w (cs (i + 1))) := by
    intro i hi
    rw [show configCode w (cs i) = configField (w * (k + 2) + 1) R i from hcode ⟨i, by omega⟩,
      show configCode w (cs (i + 1)) = configField (w * (k + 2) + 1) R (i + 1) from
        hcode ⟨i + 1, by omega⟩]
    exact hstep i hi
  obtain ⟨A, Z, res, hbs⟩ := (blockStepK_iff P w n cs hfitcs).mp hstep'
  have hbs' : ∀ i : Fin n, BlockStepK P w (cs (i : ℕ)).pc (cs ((i : ℕ) + 1)).pc
      (cs (i : ℕ)).regs (cs ((i : ℕ) + 1)).regs (res (i : ℕ)) (A (i : ℕ)) (Z (i : ℕ)) :=
    fun i => hbs i i.isLt
  -- the lane family and the selector family
  set lane : Fin (k + 2) → Fin (n + 1) → ℕ :=
    fun j i => (@Fin.cons (k + 1) (fun _ => ℕ) (cs (i : ℕ)).pc (cs (i : ℕ)).regs) j with hlane
  have hlaneb : ∀ (j : Fin (k + 2)) (i : Fin (n + 1)), lane j i < 2 ^ w := by
    intro j i
    refine Fin.cases ?_ ?_ j
    · simpa [hlane] using (hfitcs (i : ℕ)).1
    · intro r; simpa [hlane] using (hfitcs (i : ℕ)).2 r
  have hlane0 : ∀ i : Fin (n + 1), lane 0 i = (cs (i : ℕ)).pc := fun i => by simp [hlane]
  have hlaneS : ∀ (r : Fin (k + 1)) (i : Fin (n + 1)),
      lane r.succ i = (cs (i : ℕ)).regs r := fun r i => by simp [hlane]
  set selv : Fin P.length ⊕ Fin P.length → Fin n → ℕ :=
    Sum.elim (fun p i => A (i : ℕ) p) (fun p i => Z (i : ℕ) p) with hselv
  have hone : ∀ i : Fin n, (∑ c : Fin P.length ⊕ Fin P.length, selv c i) = 1 := by
    intro i
    calc (∑ c : Fin P.length ⊕ Fin P.length, selv c i)
        = (∑ p : Fin P.length, A (i : ℕ) p) + ∑ p : Fin P.length, Z (i : ℕ) p :=
          Fintype.sum_sum_type (fun c => selv c i)
      _ = ∑ p : Fin P.length, (A (i : ℕ) p + Z (i : ℕ) p) := Finset.sum_add_distrib.symm
      _ = 1 := (hbs' i).1
  have hbnd : ∀ (c : Fin P.length ⊕ Fin P.length) (i : Fin n), selv c i < 2 := by
    intro c i
    have hle : selv c i ≤ ∑ c' : Fin P.length ⊕ Fin P.length, selv c' i :=
      Finset.single_le_sum (f := fun c' => selv c' i) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ c)
    rw [hone i] at hle
    omega
  have hbitEq : bitMaskAt (w * (k + 2) + 1) n
      = fieldsCode (w * (k + 2) + 1) (fun _ : Fin n => 1) := by
    rw [fieldsCode_const]; simp [bitMaskAt]
  have hlaneEq : laneMaskAt (w * (k + 2) + 1) w n
      = fieldsCode (w * (k + 2) + 1) (fun _ : Fin n => 2 ^ w - 1) :=
    (fieldsCode_const _ _).symm
  have hmod : ∀ j : Fin (k + 2),
      (fieldsCode (w * (k + 2) + 1) (lane j)) % (2 ^ (w * (k + 2) + 1)) ^ n
        = fieldsCode (w * (k + 2) + 1) (fun i : Fin n => lane j i.castSucc) :=
    fun j => fieldsCode_mod_pow (fun i => lt_trans (hlaneb j i) hwlt)
  have hdiv : ∀ j : Fin (k + 2),
      (fieldsCode (w * (k + 2) + 1) (lane j)) / 2 ^ (w * (k + 2) + 1)
        = fieldsCode (w * (k + 2) + 1) (fun i : Fin n => lane j i.succ) :=
    fun j => fieldsCode_div _ _ (lt_trans (hlaneb j 0) hwlt)
  -- the zero residual, blockwise
  have hzsum : ∀ (r : Fin (k + 1)) (i : Fin n),
      (∑ p : Fin P.length, (P.get p).lossAt r * Z (i : ℕ) p) ≤ 1 :=
    fun r i => (subSum_le_one (fun p => Instr.lossAt_le_one r _) (hbs' i).1).2
  have hzres : ∀ (r : Fin (k + 1)) (i : Fin n),
      (cs (i : ℕ)).regs r
        + (∑ p : Fin P.length, (P.get p).lossAt r * Z (i : ℕ) p) * (2 ^ w - 1)
        + ((2 ^ w - 1) - ((cs (i : ℕ)).regs r
          + (∑ p : Fin P.length, (P.get p).lossAt r * Z (i : ℕ) p) * (2 ^ w - 1)))
      = 2 ^ w - 1 := by
    intro r i
    have h1 : (cs (i : ℕ)).regs r < 2 ^ w := (hfitcs (i : ℕ)).2 r
    have h2 := hzsum r i
    rcases (by omega : (∑ p : Fin P.length, (P.get p).lossAt r * Z (i : ℕ) p) = 0
        ∨ (∑ p : Fin P.length, (P.get p).lossAt r * Z (i : ℕ) p) = 1) with h | h
    · rw [h]; omega
    · rw [h, (hbs' i).2.2.2.2.2.1 r h]; omega
  refine ⟨fun j => fieldsCode (w * (k + 2) + 1) (lane j),
    fun c => fieldsCode (w * (k + 2) + 1) (selv c),
    fun r => fieldsCode (w * (k + 2) + 1)
      (fun i : Fin n => res (i : ℕ) r),
    fun r => fieldsCode (w * (k + 2) + 1) (fun i : Fin n =>
      (2 ^ w - 1) - ((cs (i : ℕ)).regs r
        + (∑ p : Fin P.length, (P.get p).lossAt r * Z (i : ℕ) p) * (2 ^ w - 1))),
    hlen, fun j => laneOfAt hwW _ (hlaneb j), ?_, fun c => bitOfAt h1W _ (hbnd c), ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `R` is the scaled sum of its lanes
    have h1 : fieldsCode (w * (k + 2) + 1)
        (fun i : Fin (n + 1) => configField (w * (k + 2) + 1) R i) = R :=
      fieldsCode_configField hRlt'
    calc R = fieldsCode (w * (k + 2) + 1) (fun i : Fin (n + 1) => configCode w (cs (i : ℕ))) := by
          rw [← h1]
          exact congrArg _ (funext fun i => (hcode i).symm)
      _ = ∑ j : Fin (k + 2), (2 ^ w) ^ (j : ℕ) * fieldsCode (w * (k + 2) + 1) (lane j) :=
          fieldsCode_configCode_eq_lanes w (fun i : Fin (n + 1) => cs (i : ℕ))
  · -- the branches partition every block
    dsimp only
    rw [fieldsCode_sum (w * (k + 2) + 1) Finset.univ selv, hbitEq]
    exact congrArg _ (funext hone)
  · -- program-counter agreement
    dsimp only
    rw [hmod 0, fieldsCode_sum_smul]
    refine congrArg _ (funext fun i => ?_)
    calc lane 0 i.castSucc = (cs (i : ℕ)).pc := hlane0 i.castSucc
      _ = ∑ p : Fin P.length, (p : ℕ) * (A (i : ℕ) p + Z (i : ℕ) p) := (hbs' i).2.1
      _ = ∑ p : Fin P.length, ((p : ℕ) * A (i : ℕ) p + (p : ℕ) * Z (i : ℕ) p) :=
          Finset.sum_congr rfl fun p _ => Nat.mul_add _ _ _
      _ = (∑ p : Fin P.length, (p : ℕ) * A (i : ℕ) p)
            + ∑ p : Fin P.length, (p : ℕ) * Z (i : ℕ) p := Finset.sum_add_distrib
      _ = ∑ c : Fin P.length ⊕ Fin P.length, branchIdx P c * selv c i :=
          (Fintype.sum_sum_type (fun c => branchIdx P c * selv c i)).symm
  · -- the jump
    dsimp only
    rw [hdiv 0, fieldsCode_sum_smul]
    refine congrArg _ (funext fun i => ?_)
    calc lane 0 i.succ = (cs ((i : ℕ) + 1)).pc := hlane0 i.succ
      _ = ∑ p : Fin P.length, ((P.get p).jumpPos * A (i : ℕ) p
            + (P.get p).jumpZero * Z (i : ℕ) p) := (hbs' i).2.2.1
      _ = (∑ p : Fin P.length, (P.get p).jumpPos * A (i : ℕ) p)
            + ∑ p : Fin P.length, (P.get p).jumpZero * Z (i : ℕ) p := Finset.sum_add_distrib
      _ = ∑ c : Fin P.length ⊕ Fin P.length, branchTgt P c * selv c i :=
          (Fintype.sum_sum_type (fun c => branchTgt P c * selv c i)).symm
  · -- the register updates
    intro r
    dsimp only
    rw [hdiv r.succ, hmod r.succ, fieldsCode_sum_smul, fieldsCode_sum_smul, fieldsCode_add,
      fieldsCode_add]
    refine congrArg _ (funext fun i => ?_)
    rw [hlaneS r i.succ, hlaneS r i.castSucc]
    exact (hbs' i).2.2.2.1 r
  · -- only a decrement takes a zero branch
    intro p hp
    dsimp only
    have hz : ∀ i : Fin n, Z (i : ℕ) p = 0 := by
      intro i
      have := (hbs' i).2.2.2.2.1 p
      omega
    rw [show selv (.inr p) = (fun _ : Fin n => 0) from funext hz]
    simp
  · -- the zero branch
    intro r
    dsimp only
    rw [hmod r.succ, fieldsCode_sum_smul, Nat.mul_comm (fieldsCode (w * (k + 2) + 1)
        (fun i : Fin n => ∑ p : Fin P.length,
          (P.get p).lossAt r * selv (.inr p) i)) (2 ^ w - 1),
      fieldsCode_smul, fieldsCode_add, fieldsCode_add, hlaneEq]
    refine congrArg _ (funext fun i => ?_)
    rw [hlaneS r i.castSucc, Nat.mul_comm (2 ^ w - 1)]
    exact hzres r i
  · intro r
    exact laneOfAt hwW _ fun i => by have := (hfitcs (i : ℕ)).2 r; omega
  · -- the positive residuals
    intro r
    dsimp only
    rw [hmod r.succ, fieldsCode_sum_smul, fieldsCode_add]
    refine congrArg _ (funext fun i => ?_)
    rw [hlaneS r i.castSucc]
    exact (hbs' i).2.2.2.2.2.2.1 r
  · intro r
    exact laneOfAt hwW _ fun i => (hbs' i).2.2.2.2.2.2.2.1 r
  · -- each selected target fits
    intro c
    dsimp only
    by_cases hall : ∀ i : Fin n, selv c i = 0
    · left
      rw [show selv c = (fun _ : Fin n => 0) from funext hall]
      simp
    · right
      push Not at hall
      obtain ⟨i, hi⟩ := hall
      have h1 : selv c i = 1 := by have := hbnd c i; omega
      cases c with
      | inl p => exact (hbs' i).2.2.2.2.2.2.2.2.1 p h1
      | inr p => exact (hbs' i).2.2.2.2.2.2.2.2.2.1 p h1

/-- **The global equivalence, for an arbitrary program on `k + 1` registers.** -/
theorem globalConditionsK_iff (P : Program (k + 1)) (w n R : ℕ) :
    (P.length < 2 ^ w ∧ Nat.IsBinarySubmask R (guardMask (w * (k + 2)) (n + 1)) ∧
        ∀ i < n, EncodedStep P w (configField (w * (k + 2) + 1) R i)
          (configField (w * (k + 2) + 1) R (i + 1))) ↔
      ∃ (X : Fin (k + 2) → ℕ) (S : Fin P.length ⊕ Fin P.length → ℕ)
        (Res Zres : Fin (k + 1) → ℕ), GlobalConditionsK P w n R X S Res Zres := by
  constructor
  · rintro ⟨hlen, hmask, hstep⟩
    exact globalConditionsK_complete hlen hmask hstep
  · rintro ⟨_, _, _, _, h⟩
    exact globalConditionsK_sound h

end RegisterMachine

end Hilbert10


/- Source: Hilbert10.Internal.SelectorRegsDioph, Hilbert10 v2.3.0, Apache-2.0. -/
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# `Aggregation (k + 1)`

#49, phase 4, final layer. `SelectorRegsGlobal` reduced the bounded conjunction of encoded
steps, for an arbitrary `P : Program (k + 1)`, to `GlobalConditionsK`. Representing that
discharges `Aggregation` at every register count.

## What scales and what does not

Compared with `Spike/SelectorProgramDioph`, three witness families are indexed rather than
single: the lanes by `Fin (k + 2)`, and the two residual families by `Fin (k + 1)`. The selector
family is unchanged, and so is the number of *kinds* of condition. Everything that grows does so
as an `ExpDioph.fin_and` or an `ExpTerm.sumTerm` over an index type fixed by the program and its
register count — never by the run length `N`, which is the quantifier the obligation is about.

## Main results

* `RegisterMachine.expDioph_stepBundle_regs` — `StepBundle` for every `P : Program (k + 1)`
* `RegisterMachine.aggregation_succ` — `Aggregation (k + 1)`, for every `k`
* `RegisterMachine.dioph_accepts_regs` — acceptance by any register machine is Diophantine
-/

namespace Hilbert10

namespace RegisterMachine

variable {α : Type} {k : ℕ}

/-- The witness block: the lanes, the branch selectors, the two residual families, and the
geometric sum. -/
abbrev RegsWitness (P : Program (k + 1)) :=
  Fin (k + 2) ⊕ (Fin P.length ⊕ Fin P.length) ⊕ Fin (k + 1) ⊕ Fin (k + 1) ⊕ Unit

namespace RegsWitness

/-- Lane `j`. -/
abbrev lane {P : Program (k + 1)} (j : Fin (k + 2)) : RegsWitness P := .inl j
/-- Branch selector `c`. -/
abbrev sel {P : Program (k + 1)} (c : Fin P.length ⊕ Fin P.length) : RegsWitness P :=
  .inr (.inl c)
/-- Register `r`'s positive residual. -/
abbrev pos {P : Program (k + 1)} (r : Fin (k + 1)) : RegsWitness P := .inr (.inr (.inl r))
/-- Register `r`'s zero residual. -/
abbrev zero {P : Program (k + 1)} (r : Fin (k + 1)) : RegsWitness P :=
  .inr (.inr (.inr (.inl r)))
/-- The geometric sum. -/
abbrev geo {P : Program (k + 1)} : RegsWitness P := .inr (.inr (.inr (.inr ())))

end RegsWitness

open RegsWitness in
/-- The body under the witnesses: the geometric sum is pinned, and the rest is
`GlobalConditionsK` verbatim. -/
def regsBody (P : Program (k + 1)) (N W R : ExpTerm α) :
    Set ((α ⊕ RegsWitness P) → ℕ) :=
  {u | u (.inr geo) * 2 ^ ((W.map Sum.inl).eval u * (k + 2) + 1) + 1
        = u (.inr geo)
          + (2 ^ ((W.map Sum.inl).eval u * (k + 2) + 1)) ^ (N.map Sum.inl).eval u ∧
      GlobalConditionsK P ((W.map Sum.inl).eval u) ((N.map Sum.inl).eval u)
        ((R.map Sum.inl).eval u) (fun j => u (.inr (lane j))) (fun c => u (.inr (sel c)))
        (fun r => u (.inr (pos r))) (fun r => u (.inr (zero r)))}

open RegsWitness in
theorem expDioph_regsBody (P : Program (k + 1)) (N W R : ExpTerm α) :
    ExpDioph (regsBody P N W R) := by
  set W' : ExpTerm (α ⊕ RegsWitness P) := W.map Sum.inl with hW'
  set N' : ExpTerm (α ⊕ RegsWitness P) := N.map Sum.inl with hN'
  set R' : ExpTerm (α ⊕ RegsWitness P) := R.map Sum.inl with hR'
  set pw : ExpTerm (α ⊕ RegsWitness P) := .pow (.const 2) W' with hpw
  set B : ExpTerm (α ⊕ RegsWitness P) :=
    .pow (.const 2) (.add (.mul W' (.const (k + 2))) (.const 1)) with hB
  set Bn : ExpTerm (α ⊕ RegsWitness P) := .pow B N' with hBn
  set vX : Fin (k + 2) → ExpTerm (α ⊕ RegsWitness P) :=
    fun j => .var (.inr (lane j)) with hvX
  set vS : Fin P.length ⊕ Fin P.length → ExpTerm (α ⊕ RegsWitness P) :=
    fun c => .var (.inr (sel c)) with hvS
  set vRes : Fin (k + 1) → ExpTerm (α ⊕ RegsWitness P) :=
    fun r => .var (.inr (pos r)) with hvRes
  set vZres : Fin (k + 1) → ExpTerm (α ⊕ RegsWitness P) :=
    fun r => .var (.inr (zero r)) with hvZres
  set vG : ExpTerm (α ⊕ RegsWitness P) := .var (.inr geo) with hvG
  set laneN : ExpTerm (α ⊕ RegsWitness P) := .mul (.sub pw (.const 1)) vG with hlaneN
  set laneS : ExpTerm (α ⊕ RegsWitness P) :=
    .mul (.sub pw (.const 1)) (.add (.const 1) (.mul B vG)) with hlaneS
  -- the conditions, assembled from the last one back
  have c14 : ExpDioph {u : (α ⊕ RegsWitness P) → ℕ |
      ∀ c, u (.inr (sel c)) = 0 ∨ branchTgt P c < 2 ^ W'.eval u} :=
    ExpDioph.fin_and fun c =>
      ExpDioph.or (ExpDioph.of_eq (s := vS c) (t := .const 0))
        (ExpDioph.of_lt (s := .const (branchTgt P c)) (t := pw))
  have c13 : ExpDioph {u : (α ⊕ RegsWitness P) → ℕ |
      ∀ r, Nat.IsBinarySubmask (u (.inr (pos r))) (laneN.eval u)} :=
    ExpDioph.fin_and fun r => ExpDioph.of_isBinarySubmask (vRes r) laneN
  have c12 : ExpDioph {u : (α ⊕ RegsWitness P) → ℕ |
      ∀ r, (ExpTerm.mod (vX r.succ) Bn).eval u
        = (ExpTerm.add (vRes r) (ExpTerm.sumTerm fun p : Fin P.length =>
            .mul (.const ((P.get p).lossAt r)) (vS (.inl p)))).eval u} :=
    ExpDioph.fin_and fun r => ExpDioph.of_eq
      (s := .mod (vX r.succ) Bn)
      (t := .add (vRes r) (ExpTerm.sumTerm fun p : Fin P.length =>
        .mul (.const ((P.get p).lossAt r)) (vS (.inl p))))
  have c11 : ExpDioph {u : (α ⊕ RegsWitness P) → ℕ |
      ∀ r, Nat.IsBinarySubmask (u (.inr (zero r))) (laneN.eval u)} :=
    ExpDioph.fin_and fun r => ExpDioph.of_isBinarySubmask (vZres r) laneN
  have c10 : ExpDioph {u : (α ⊕ RegsWitness P) → ℕ |
      ∀ r, (ExpTerm.add (.add (.mod (vX r.succ) Bn)
          (.mul (ExpTerm.sumTerm fun p : Fin P.length =>
            .mul (.const ((P.get p).lossAt r)) (vS (.inr p))) (.sub pw (.const 1))))
        (vZres r)).eval u = laneN.eval u} :=
    ExpDioph.fin_and fun r => ExpDioph.of_eq
      (s := .add (.add (.mod (vX r.succ) Bn)
        (.mul (ExpTerm.sumTerm fun p : Fin P.length =>
          .mul (.const ((P.get p).lossAt r)) (vS (.inr p))) (.sub pw (.const 1)))) (vZres r))
      (t := laneN)
  have c9 : ExpDioph {u : (α ⊕ RegsWitness P) → ℕ |
      ∀ p, (P.get p).branches = 0 → u (.inr (sel (.inr p))) = 0} :=
    ExpDioph.fin_and fun p => by
      by_cases hp : (P.get p).branches = 0
      · exact (ExpDioph.of_eq (s := vS (.inr p)) (t := .const 0)).congr fun u => by
          simp only [Set.mem_setOf_eq, hvS, ExpTerm.eval]
          exact ⟨fun h _ => h, fun h => h hp⟩
      · exact ExpDioph.of_true.congr fun u => by
          simp only [Set.mem_univ, true_iff]
          exact fun h => absurd h hp
  have c8 : ExpDioph {u : (α ⊕ RegsWitness P) → ℕ |
      ∀ r, (ExpTerm.add (.div (vX r.succ) B) (ExpTerm.sumTerm fun p : Fin P.length =>
          .mul (.const ((P.get p).lossAt r)) (vS (.inl p)))).eval u
        = (ExpTerm.add (.mod (vX r.succ) Bn) (ExpTerm.sumTerm fun p : Fin P.length =>
          .mul (.const ((P.get p).gainAt r)) (vS (.inl p)))).eval u} :=
    ExpDioph.fin_and fun r => ExpDioph.of_eq
      (s := .add (.div (vX r.succ) B) (ExpTerm.sumTerm fun p : Fin P.length =>
        .mul (.const ((P.get p).lossAt r)) (vS (.inl p))))
      (t := .add (.mod (vX r.succ) Bn) (ExpTerm.sumTerm fun p : Fin P.length =>
        .mul (.const ((P.get p).gainAt r)) (vS (.inl p))))
  have c7 := ExpDioph.and (ExpDioph.of_eq (s := .div (vX 0) B)
    (t := ExpTerm.sumTerm fun c => .mul (.const (branchTgt P c)) (vS c)))
    (ExpDioph.and c8 (ExpDioph.and c9 (ExpDioph.and c10
      (ExpDioph.and c11 (ExpDioph.and c12 (ExpDioph.and c13 c14))))))
  have c6 := ExpDioph.and (ExpDioph.of_eq (s := .mod (vX 0) Bn)
    (t := ExpTerm.sumTerm fun c => .mul (.const (branchIdx P c)) (vS c))) c7
  have c5 := ExpDioph.and
    (ExpDioph.of_eq (s := ExpTerm.sumTerm fun c => vS c) (t := vG)) c6
  have c4 : ExpDioph {u : (α ⊕ RegsWitness P) → ℕ |
      ∀ c, Nat.IsBinarySubmask (u (.inr (sel c))) (vG.eval u)} :=
    ExpDioph.fin_and fun c => ExpDioph.of_isBinarySubmask (vS c) vG
  have c3 := ExpDioph.and (ExpDioph.of_eq (s := R')
    (t := ExpTerm.sumTerm fun j : Fin (k + 2) =>
      .mul (.pow pw (.const (j : ℕ))) (vX j))) (ExpDioph.and c4 c5)
  have c2 : ExpDioph {u : (α ⊕ RegsWitness P) → ℕ |
      ∀ j, Nat.IsBinarySubmask (u (.inr (lane j))) (laneS.eval u)} :=
    ExpDioph.fin_and fun j => ExpDioph.of_isBinarySubmask (vX j) laneS
  have c1 := ExpDioph.and (ExpDioph.of_lt (s := .const P.length) (t := pw))
    (ExpDioph.and c2 c3)
  have c0 := ExpDioph.and
    (ExpDioph.of_eq (s := .add (.mul vG B) (.const 1)) (t := .add vG Bn)) c1
  refine ExpDioph.congr c0 ?_
  intro u
  have hb : (2 : ℕ) ≤ 2 ^ (W'.eval u * (k + 2) + 1) := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (W'.eval u * (k + 2) + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, regsBody, GlobalConditionsK, laneMaskAt,
    bitMaskAt, geom_succ, hlaneN, hlaneS, hpw, hB, hBn, hvX, hvS, hvRes, hvZres, hvG,
    hW', hN', hR', ExpTerm.eval, ExpTerm.eval_sumTerm]
  constructor
  · rintro ⟨hpin, rest⟩
    have hG := geom_unique hb hpin
    refine ⟨hpin, ?_⟩
    rw [← hG]
    exact rest
  · rintro ⟨hpin, rest⟩
    have hG := geom_unique hb hpin
    refine ⟨hpin, ?_⟩
    rw [← hG] at rest
    exact rest

open RegsWitness in
/-- **The obligation, for every program on `k + 1` registers.** -/
theorem expDioph_stepBundle_regs (P : Program (k + 1)) (N W R : ExpTerm α) :
    ExpDioph (StepBundle P N W R) := by
  refine ExpDioph.congr (ExpDioph.ex (expDioph_regsBody P N W R)) fun v => ?_
  simp only [StepBundle, regsBody, Set.mem_setOf_eq, ExpTerm.eval_map, Sum.elim_comp_inl,
    Sum.elim_inr, show k + 1 + 1 = k + 2 from rfl]
  rw [globalConditionsK_iff]
  constructor
  · rintro ⟨u, _, h⟩
    exact ⟨fun j => u (lane j), fun c => u (sel c), fun r => u (pos r), fun r => u (zero r), h⟩
  · rintro ⟨X, S, Res, Zres, h⟩
    refine ⟨Sum.elim X (Sum.elim S (Sum.elim Res (Sum.elim Zres
      (fun _ => geom (2 ^ (W.eval v * (k + 2) + 1)) (N.eval v))))), geom_spec _ _, h⟩

/-- **`Aggregation` at every register count.** -/
theorem aggregation_succ (k : ℕ) : Aggregation (k + 1) :=
  fun P N W R => expDioph_stepBundle_regs P N W R

/-- **Acceptance by any register machine is Diophantine**, unconditionally. -/
theorem expDioph_accepts_regs (P : Program (k + 1)) (X Y : ExpTerm α) :
    ExpDioph {v : α → ℕ | Accepts P (X.eval v) (Y.eval v)} :=
  expDioph_accepts (aggregation_succ k) P X Y

theorem dioph_accepts_regs (P : Program (k + 1)) (X Y : ExpTerm α) :
    Dioph {v : α → ℕ | Accepts P (X.eval v) (Y.eval v)} :=
  (expDioph_accepts_regs P X Y).dioph

end RegisterMachine

end Hilbert10


/- Source: Hilbert10.DPRM, Hilbert10 v2.3.0, Apache-2.0. -/
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# DPRM on `ℕ`: the machine route's endpoint

Issue #23, first part. Two facts are already available and this file only joins them:

* `exists_machine_graph` (#20) compiles a `Nat.Partrec.Code` into a register machine whose
  accepted relation is the graph of `c.eval`;
* `dioph_accepts_regs` (#21, #49) says acceptance by an arbitrary register machine is
  Diophantine.

Composing them gives the graph of any partial recursive function, and projecting the output
gives its domain. A recursively enumerable predicate on `ℕ` is the domain of such a function,
which is the unary case of DPRM.

## Where the register count goes

`exists_machine_graph` produces a machine on `k + 1` registers, and `dioph_accepts_regs` is
stated for `Program (k + 1)`, so the two fit with no side condition: there is no `Aggregation 0`
to discharge, because a compiled machine always has at least one register.

## From `ℕ` to tuples

A machine consumes one number, while an `n`-ary predicate receives a `Fin n → ℕ`. The bridge is
`TupleCoding`, used in both directions: its decoder is computable, which carries a recursively
enumerable predicate on tuples to one on `ℕ`; its encoder's graph is Diophantine, which carries
the resulting condition back.

## The public statements

`REPred.dioph` and `dioph_iff_rePred` mention only `REPred` and `Dioph`. Nothing about register
machines, packed runs, selectors or `ExpDioph` appears in them, and the tuple coding is an
implementation detail of the proof rather than part of the interface.

## Main results

* `Nat.Partrec.graph_dioph`, `Nat.Partrec.dom_dioph`
* `REPred.dioph_nat` — the unary case
* `REPred.dioph`, `dioph_iff_rePred` — **DPRM**
-/

namespace Hilbert10

open Nat.Partrec (Code)
open RegisterMachine

/-- The graph of a `Nat.Partrec.Code` is Diophantine: compile it, then arithmetise the
machine's accepted relation. -/
private theorem dioph_code_graph (c : Code) :
    Dioph {v : Fin 2 → ℕ | v 1 ∈ c.eval (v 0)} := by
  obtain ⟨k, P, hP⟩ := exists_machine_graph c
  have hset : {v : Fin 2 → ℕ | v 1 ∈ c.eval (v 0)} = {v : Fin 2 → ℕ | Accepts P (v 0) (v 1)} :=
    Set.ext fun v => (hP (v 0) (v 1)).symm
  rw [hset]
  exact dioph_accepts_regs P (.var 0) (.var 1)

/-- **The graph of a partial recursive function is Diophantine.** -/
theorem Nat.Partrec.graph_dioph {f : ℕ →. ℕ} (hf : _root_.Nat.Partrec f) :
    Dioph {v : Fin 2 → ℕ | v 1 ∈ f (v 0)} := by
  obtain ⟨c, hc⟩ := Code.exists_code.mp hf
  have hset : {v : Fin 2 → ℕ | v 1 ∈ f (v 0)} = {v : Fin 2 → ℕ | v 1 ∈ c.eval (v 0)} := by
    rw [hc]
  rw [hset]
  exact dioph_code_graph c

/-- **The domain of a partial recursive function is Diophantine.** The output is projected out
as a witness, which is one `ExpDioph.ex` rather than a second arithmetisation. -/
theorem Nat.Partrec.dom_dioph {f : ℕ →. ℕ} (hf : _root_.Nat.Partrec f) :
    Dioph {v : Fin 1 → ℕ | (f (v 0)).Dom} := by
  obtain ⟨c, hc⟩ := Code.exists_code.mp hf
  obtain ⟨k, P, hP⟩ := exists_machine_graph c
  refine (ExpDioph.congr (ExpDioph.ex (expDioph_accepts_regs P
    (.var (Sum.inl 0)) (.var (Sum.inr ())))) fun v => ?_).dioph
  simp only [Set.mem_setOf_eq, Part.dom_iff_mem]
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w (), by rw [← hc]; exact (hP (v 0) (w ())).mp hw⟩
  · rintro ⟨y, hy⟩
    exact ⟨fun _ => y, (hP (v 0) y).mpr (by rw [hc]; exact hy)⟩

/-- **DPRM on `ℕ`.** A recursively enumerable predicate on the naturals is Diophantine.

The `Unit`-valued witness of `REPred` is turned into a partial function with the same domain,
exactly as in `HaltingComplete`; its domain is then Diophantine. -/
theorem REPred.dioph_nat {R : ℕ → Prop} (h : REPred R) : Dioph {v : Fin 1 → ℕ | R (v 0)} := by
  have hf : Partrec fun a : ℕ =>
      (Part.assert (R a) fun _ => Part.some ()).map fun _ => (0 : ℕ) :=
    h.map (Computable.const (0 : ℕ)).to₂
  set f : ℕ →. ℕ := fun a => (Part.assert (R a) fun _ => Part.some ()).map fun _ => (0 : ℕ)
    with hf_def
  have hdom : ∀ a, (f a).Dom ↔ R a := by
    intro a
    simp [hf_def, Part.assert]
  have hset : {v : Fin 1 → ℕ | R (v 0)} = {v : Fin 1 → ℕ | (f (v 0)).Dom} :=
    Set.ext fun v => (hdom (v 0)).symm
  rw [hset]
  exact Nat.Partrec.dom_dioph (Partrec.nat_iff.mp hf)

/-! ### From `ℕ` to tuples -/

/-- **DPRM.** A recursively enumerable predicate on `Fin n`-tuples is Diophantine.

The tuple is coded into one number, the unary case is applied to the decoded predicate, and the
coding is imposed by its own Diophantine graph. -/
theorem REPred.dioph {n : ℕ} {R : (Fin n → ℕ) → Prop} (h : REPred R) :
    Dioph {x : Fin n → ℕ | R x} := by
  have hRE : REPred fun z : ℕ => R (tupleDecode n z) :=
    Partrec.comp h (computable_tupleDecode n)
  have h1 : Dioph {v : Fin 1 → ℕ | R (tupleDecode n (v 0))} := REPred.dioph_nat hRE
  have h2 : Dioph {u : (Fin n ⊕ Unit) → ℕ | R (tupleDecode n (u (.inr ())))} :=
    Dioph.reindex_dioph (Fin n ⊕ Unit) (fun _ : Fin 1 => (Sum.inr () : Fin n ⊕ Unit)) h1
  have h3 : Dioph {u : (Fin n ⊕ Unit) → ℕ |
      tupleCode (fun i => u (.inl i)) = u (.inr ())} := (expDioph_tupleCode_graph n).dioph
  refine ((h3.inter h2).ex_dioph).ext fun v => ?_
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨x, hcode, hR⟩
    rw [← hcode] at hR
    rwa [tupleDecode_tupleCode] at hR
  · intro hv
    exact ⟨fun _ => tupleCode v, rfl, by rwa [tupleDecode_tupleCode]⟩

/-- **The characterisation.** Over the naturals, Diophantine and recursively enumerable coincide
for predicates on tuples. -/
theorem dioph_iff_rePred {n : ℕ} (R : (Fin n → ℕ) → Prop) :
    Dioph {x : Fin n → ℕ | R x} ↔ REPred R :=
  ⟨Dioph.rePred, REPred.dioph⟩

end Hilbert10


/- Source: Hilbert10.Internal.CodeAlgebra, Hilbert10 v2.3.0, Apache-2.0. -/
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# Arithmetic on encoded polynomials

Issue #28, second piece. The two solvability reductions substitute into a code, so they need to
build codes: constants, variables, sums, products, powers. This is the minimum those consumers
ask for, and it is deliberately **internal** — a wire-format algebra, not the polynomial DSL
parked in #29.

## The one real trap

Exponent vectors are ragged: `[2]` and `[0, 3]` are the same polynomial's monomials with
different presentations, and a trailing zero is invisible. So multiplying two monomials means
adding exponent vectors **with zero-extension**, and `List.zipWith` is wrong — it truncates to
the shorter vector, silently discarding the tail of the longer one.

`addExponents` is that operation, and `evalMonomialInt_addExponents` is the theorem everything
else rests on: once monomial multiplication is right, convolution multiplication of codes is
list-sum distributivity.

## One evaluation, two readings

Every law is proved for `evalInt` and then *derived* for `eval` through
`evalInt_map_natCast`, rather than proved twice. The natural evaluation is the integer one at a
cast assignment, so there is nothing separate to check.

## Not here

No general renaming. With the original variables in the first block, extending an assignment
leaves a code's value unchanged, and both consumers can build the variables they need directly
at the indices they want. If a consumer ever asks for a rename, add it then.

## Main definitions

* `Hilbert10.PolynomialCode.addExponents` — zero-extended pointwise addition
* `Hilbert10.PolynomialCode.const`, `X`, `add`, `neg`, `mul`, `pow`
-/

namespace Hilbert10

namespace PolynomialCode

/-! ### Zero-extended exponent addition -/

/-- Pointwise addition of exponent vectors, extending the shorter with zeros. `List.zipWith`
would truncate instead, which drops the longer vector's tail. -/
def addExponents : MonomialCode → MonomialCode → MonomialCode
  | [], f => f
  | e :: es, [] => e :: es
  | a :: es, b :: fs => (a + b) :: addExponents es fs

@[simp] theorem addExponents_nil_left (f : MonomialCode) : addExponents [] f = f := rfl

@[simp] theorem addExponents_nil_right : ∀ e : MonomialCode, addExponents e [] = e
  | [] => rfl
  | _ :: _ => rfl

/-- **Monomial multiplication is exponent addition.** Everything else in this file reduces to
this and list-sum distributivity. -/
theorem evalMonomialInt_addExponents :
    ∀ (e f : MonomialCode) (x : List ℤ),
      evalMonomialInt (addExponents e f) x = evalMonomialInt e x * evalMonomialInt f x
  | [], f, x => by simp [evalMonomialInt]
  | e :: es, [], x => by simp [evalMonomialInt]
  | a :: es, b :: fs, [] => by
    simp only [addExponents, evalMonomialInt, evalMonomialInt_addExponents es fs [], pow_add]
    ring
  | a :: es, b :: fs, v :: vs => by
    simp only [addExponents, evalMonomialInt, evalMonomialInt_addExponents es fs vs, pow_add]
    ring

/-! ### The operations -/

/-- The zero polynomial. -/
def zero : PolynomialCode := ⟨[]⟩

/-- A constant. -/
def const (c : ℤ) : PolynomialCode := ⟨[(c, [])]⟩

/-- The polynomial `1`. -/
def one : PolynomialCode := const 1

/-- The variable with index `i`. -/
def X (i : ℕ) : PolynomialCode := ⟨[(1, List.replicate i 0 ++ [1])]⟩

/-- Sum: sparse representations concatenate. -/
def add (p q : PolynomialCode) : PolynomialCode := ⟨p.terms ++ q.terms⟩

/-- Negation: negate every coefficient. -/
def neg (p : PolynomialCode) : PolynomialCode := ⟨p.terms.map fun t => (-t.1, t.2)⟩

/-- Product: convolution of the term lists, multiplying coefficients and adding exponents. -/
def mul (p q : PolynomialCode) : PolynomialCode :=
  ⟨p.terms.flatMap fun t => q.terms.map fun s => (t.1 * s.1, addExponents t.2 s.2)⟩

/-- Powers, by structural recursion. -/
def npow (p : PolynomialCode) : ℕ → PolynomialCode
  | 0 => one
  | n + 1 => mul p (npow p n)

/-! ### Evaluation laws, at an integer assignment -/

@[simp] theorem evalInt_zero (x : List ℤ) : evalInt zero x = 0 := rfl

@[simp] theorem evalInt_const (c : ℤ) (x : List ℤ) : evalInt (const c) x = c := by
  simp [evalInt, const, evalMonomialInt]

@[simp] theorem evalInt_one (x : List ℤ) : evalInt one x = 1 := by simp [one]

theorem evalMonomialInt_X : ∀ (i : ℕ) (x : List ℤ),
    evalMonomialInt (List.replicate i 0 ++ [1]) x = x.getD i 0
  | 0, [] => by simp [evalMonomialInt]
  | 0, v :: vs => by simp [evalMonomialInt]
  | i + 1, [] => by
    have ih := evalMonomialInt_X i ([] : List ℤ)
    simp only [List.replicate_succ, List.cons_append, evalMonomialInt, ih]
    simp
  | i + 1, v :: vs => by
    have ih := evalMonomialInt_X i vs
    simp only [List.replicate_succ, List.cons_append, evalMonomialInt, ih]
    simp

@[simp] theorem evalInt_X (i : ℕ) (x : List ℤ) : evalInt (X i) x = x.getD i 0 := by
  simp [evalInt, X, evalMonomialInt_X]

@[simp] theorem evalInt_add (p q : PolynomialCode) (x : List ℤ) :
    evalInt (add p q) x = evalInt p x + evalInt q x := by
  simp [evalInt, add]

@[simp] theorem evalInt_neg (p : PolynomialCode) (x : List ℤ) :
    evalInt (neg p) x = -evalInt p x := by
  simp only [evalInt, neg, List.map_map, Function.comp_def]
  induction p.terms with
  | nil => simp
  | cons t ts ih => simp only [List.map_cons, List.sum_cons, ih]; ring

private theorem sum_map_const_mul {α : Type*} (c : ℤ) (l : List α) (h : α → ℤ) :
    (l.map fun s => c * h s).sum = c * (l.map h).sum := by
  induction l with
  | nil => simp
  | cons a as ih => simp only [List.map_cons, List.sum_cons, ih, mul_add]

@[simp] theorem evalInt_mul (p q : PolynomialCode) (x : List ℤ) :
    evalInt (mul p q) x = evalInt p x * evalInt q x := by
  obtain ⟨ts⟩ := p
  simp only [evalInt, mul]
  induction ts with
  | nil => simp
  | cons t ts ih =>
    have hterm : (List.map (fun s : ℤ × MonomialCode =>
        (t.1 * s.1) * evalMonomialInt (addExponents t.2 s.2) x) q.terms).sum
        = (t.1 * evalMonomialInt t.2 x)
          * (List.map (fun s : ℤ × MonomialCode => s.1 * evalMonomialInt s.2 x) q.terms).sum := by
      rw [← sum_map_const_mul]
      congr 1
      exact List.map_congr_left fun s _ => by
        rw [evalMonomialInt_addExponents]; ring
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_map,
      Function.comp_def, List.map_cons, List.sum_cons, ih, hterm]
    ring

@[simp] theorem evalInt_npow (p : PolynomialCode) : ∀ (n : ℕ) (x : List ℤ),
    evalInt (npow p n) x = evalInt p x ^ n
  | 0, x => by simp [npow]
  | n + 1, x => by simp [npow, evalInt_npow p n x, pow_succ, mul_comm]



/-! ### Arity

Inequalities for multiplication and powers: equality fails for an empty term list, and for
exponent zero. -/

theorem length_addExponents : ∀ e f : MonomialCode,
    (addExponents e f).length = max e.length f.length
  | [], f => by simp
  | e :: es, [] => by simp
  | _ :: es, _ :: fs => by
    simp only [addExponents, List.length_cons, length_addExponents es fs]
    omega

/-- The bound direction of `arity`: it suffices to bound every term's exponent vector. -/
theorem arity_le_of_forall_term_length_le {p : PolynomialCode} {m : ℕ}
    (h : ∀ t ∈ p.terms, t.2.length ≤ m) : p.arity ≤ m := by
  obtain ⟨ts⟩ := p
  simp only [arity]
  induction ts with
  | nil => simp
  | cons t ts ih =>
    simp only [List.map_cons, List.foldr_cons, max_le_iff]
    exact ⟨h t (by simp), ih fun s hs => h s (by simp [hs])⟩

theorem arity_mk_append (s t : List (ℤ × MonomialCode)) :
    arity ⟨s ++ t⟩ = max (arity ⟨s⟩) (arity ⟨t⟩) := by
  simp only [arity, List.map_append]
  induction s with
  | nil => simp
  | cons a as ih => simp only [List.map_cons, List.cons_append, List.foldr_cons, ih, max_assoc]

@[simp] theorem arity_const (c : ℤ) : (const c).arity = 0 := rfl

@[simp] theorem arity_one : one.arity = 0 := rfl

@[simp] theorem arity_X (i : ℕ) : (X i).arity = i + 1 := by
  simp [arity, X]

@[simp] theorem arity_add (p q : PolynomialCode) :
    (add p q).arity = max p.arity q.arity := arity_mk_append _ _

@[simp] theorem arity_neg (p : PolynomialCode) : (neg p).arity = p.arity := by
  simp only [arity, neg, List.map_map, Function.comp_def]

theorem arity_mul_le (p q : PolynomialCode) : (mul p q).arity ≤ max p.arity q.arity := by
  refine arity_le_of_forall_term_length_le fun t ht => ?_
  simp only [mul, List.mem_flatMap, List.mem_map] at ht
  obtain ⟨a, ha, b, hb, rfl⟩ := ht
  simp only [length_addExponents, max_le_iff]
  exact ⟨le_max_of_le_left (length_le_arity ha), le_max_of_le_right (length_le_arity hb)⟩

theorem arity_npow_le (p : PolynomialCode) : ∀ n : ℕ, (npow p n).arity ≤ p.arity
  | 0 => by simp [npow]
  | n + 1 => by
    refine le_trans (arity_mul_le p (npow p n)) ?_
    simp [arity_npow_le p n]

/-! ### Index presentations, for computability

The structural definitions are the ones every semantic and arity proof uses. For primitive
recursiveness they are matched against index-based presentations, proved equal here once.
`List.zipWith` has no `Primrec` lemma in mathlib, so exponent addition goes through
`List.range` and `List.getD`, both of which do. -/

theorem getD_addExponents : ∀ (e f : MonomialCode) (i : ℕ),
    (addExponents e f).getD i 0 = e.getD i 0 + f.getD i 0
  | [], f, i => by simp
  | e :: es, [], i => by simp
  | a :: es, b :: fs, 0 => by simp [addExponents, List.getD]
  | a :: es, b :: fs, i + 1 => by
    simpa [addExponents, List.getD] using getD_addExponents es fs i

/-- The index presentation of exponent addition. -/
theorem addExponents_eq_range (e f : MonomialCode) :
    addExponents e f
      = (List.range (max e.length f.length)).map fun i => e.getD i 0 + f.getD i 0 := by
  refine List.ext_getElem (by simp [length_addExponents]) fun i h1 h2 => ?_
  have hlen : i < max e.length f.length := by
    simpa [length_addExponents] using h1
  rw [List.getElem_map, List.getElem_range]
  have := getD_addExponents e f i
  rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some] at this

/-! ### The same laws at a natural assignment

Derived, not reproved: the natural evaluation is the integer one at a cast assignment. -/

theorem eval_eq_evalInt (p : PolynomialCode) (x : List ℕ) :
    eval p x = evalInt p (x.map (Nat.cast : ℕ → ℤ)) := (evalInt_map_natCast p x).symm

@[simp] theorem eval_const (c : ℤ) (x : List ℕ) : eval (const c) x = c := by
  rw [eval_eq_evalInt, evalInt_const]

@[simp] theorem eval_one (x : List ℕ) : eval one x = 1 := by rw [one, eval_const]

@[simp] theorem eval_add (p q : PolynomialCode) (x : List ℕ) :
    eval (add p q) x = eval p x + eval q x := by
  rw [eval_eq_evalInt, eval_eq_evalInt p, eval_eq_evalInt q, evalInt_add]

@[simp] theorem eval_neg (p : PolynomialCode) (x : List ℕ) :
    eval (neg p) x = -eval p x := by
  rw [eval_eq_evalInt, eval_eq_evalInt p, evalInt_neg]

@[simp] theorem eval_mul (p q : PolynomialCode) (x : List ℕ) :
    eval (mul p q) x = eval p x * eval q x := by
  rw [eval_eq_evalInt, eval_eq_evalInt p, eval_eq_evalInt q, evalInt_mul]

@[simp] theorem eval_npow (p : PolynomialCode) (n : ℕ) (x : List ℕ) :
    eval (npow p n) x = eval p x ^ n := by
  rw [eval_eq_evalInt, eval_eq_evalInt p, evalInt_npow]

theorem getD_map_natCast (x : List ℕ) (i : ℕ) :
    (x.map (Nat.cast : ℕ → ℤ)).getD i 0 = ((x.getD i 0 : ℕ) : ℤ) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases x[i]? <;> simp

@[simp] theorem eval_X (i : ℕ) (x : List ℕ) : eval (X i) x = ((x.getD i 0 : ℕ) : ℤ) := by
  rw [eval_eq_evalInt, evalInt_X, getD_map_natCast]

/-! ### Folded sums

Both `fourSquares` and the sum-of-squares transformation build a sum of codes by
`foldr add zero`, so its evaluation and arity laws are stated once. -/

/-- Evaluating a folded sum of codes is the sum of the evaluations. -/
theorem evalInt_foldr_add {α : Type*} (l : List α) (f : α → PolynomialCode) (y : List ℤ) :
    evalInt ((l.map f).foldr add zero) y = (l.map fun i => evalInt (f i) y).sum := by
  induction l with
  | nil => simp [zero]
  | cons a as ih => simp only [List.map_cons, List.foldr_cons, evalInt_add, ih, List.sum_cons]

/-- A folded sum's arity is bounded by any common bound on its summands. -/
theorem arity_foldr_add_le {α : Type*} (l : List α) (f : α → PolynomialCode) (m : ℕ)
    (h : ∀ a ∈ l, (f a).arity ≤ m) : (((l.map f).foldr add zero)).arity ≤ m := by
  induction l with
  | nil => simp [zero, arity]
  | cons a as ih =>
    simp only [List.map_cons, List.foldr_cons, arity_add, max_le_iff]
    exact ⟨h a (by simp), ih fun b hb => h b (by simp [hb])⟩

end PolynomialCode

end Hilbert10


/- Source: Hilbert10.SubUV, Hilbert10 v2.3.0, Apache-2.0. -/
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# The difference substitution `x = u - v`

Issue #28, third piece. An integer root of `p` is a natural root of the code obtained by
replacing every variable `xᵢ` with `uᵢ - vᵢ`, because every integer is a difference of two
naturals. This file builds that code and proves what it evaluates to.

## Layout, frozen in #28

For `n := p.arity`, the transformed code uses `2 * n` variables: indices `0 .. n-1` carry `u` and
indices `n .. 2n-1` carry `v`, so variable `i` becomes `X i - X (n + i)`.

## An indexed structural recursion, not `List.enum`

`subUVMonomialFrom n i es` walks the exponent vector while carrying the index `i` of the variable
it is currently substituting for. Semantics, arity and primitive recursiveness all then follow
from the *same* recursion, which pairing the list with its indices first would obscure.

The helper contracts are strengthened with `i` for that reason: evaluation assumes
`i + es.length ≤ n`, and the arity bound is `n + i + es.length`. At `i = 0` every exponent vector
of `p` has length at most `p.arity`, which gives the frozen `2 * p.arity` bound immediately.

## Public, unlike its computability

`subUV` is one of the two reductions between the natural and integer formulations, and its
evaluation and arity theorems are meaningful on their own — so this file is API. What turns the
transformation into a many-one reduction is `Primrec subUV`, which is unsupported machinery and
stays in `Internal/SubUVComp.lean`, together with the index presentation that exists only to
prove it.

## Main definitions

* `Hilbert10.PolynomialCode.diffList`
* `Hilbert10.PolynomialCode.subUV`

## Main results

* `Hilbert10.PolynomialCode.eval_subUV`
* `Hilbert10.PolynomialCode.arity_subUV_le`
-/

namespace Hilbert10

namespace PolynomialCode

/-- The assignment `x = u - v`, componentwise. -/
def diffList (u v : List ℕ) : List ℤ :=
  List.zipWith (fun a b => (a : ℤ) - (b : ℤ)) u v

@[simp] theorem length_diffList (u v : List ℕ) :
    (diffList u v).length = min u.length v.length := by
  simp [diffList]

@[simp] theorem diffList_cons (a b : ℕ) (u v : List ℕ) :
    diffList (a :: u) (b :: v) = ((a : ℤ) - (b : ℤ)) :: diffList u v := rfl

/-- Peeling one component off the difference assignment. Proved by induction on the index
rather than through `getElem` on a `zipWith`, which simp normalises into an unhelpful shape. -/
theorem drop_diffList : ∀ (i : ℕ) (u v : List ℕ), i < u.length → i < v.length →
    (diffList u v).drop i
      = ((u.getD i 0 : ℤ) - (v.getD i 0 : ℤ)) :: (diffList u v).drop (i + 1)
  | 0, a :: u, b :: v, _, _ => by simp [List.getD]
  | i + 1, a :: u, b :: v, hu, hv => by
    have ih := drop_diffList i u v (by simpa using hu) (by simpa using hv)
    simpa [List.getD] using ih

/-- Every integer assignment is a difference of two natural ones, componentwise. -/
theorem diffList_toNat (y : List ℤ) :
    diffList (y.map Int.toNat) (y.map fun z => (-z).toNat) = y := by
  induction y with
  | nil => rfl
  | cons a as ih =>
    simp only [List.map_cons, diffList_cons, ih]
    congr 1
    omega

/-- The variable `xᵢ` after substitution: `uᵢ - vᵢ`, at the frozen block layout. -/
def diffVar (n i : ℕ) : PolynomialCode := add (X i) (neg (X (n + i)))

/-- The substitution applied to one exponent vector, carrying the index of the variable being
substituted for. -/
def subUVMonomialFrom (n : ℕ) : ℕ → MonomialCode → PolynomialCode
  | _, [] => one
  | i, e :: es => mul (npow (diffVar n i) e) (subUVMonomialFrom n (i + 1) es)

/-- **The difference substitution.** Each term's coefficient is kept and its monomial is
substituted; the results are appended, which is what `add` does on this representation. -/
def subUV (p : PolynomialCode) : PolynomialCode :=
  ⟨p.terms.flatMap fun t => (mul (const t.1) (subUVMonomialFrom p.arity 0 t.2)).terms⟩


/-! ### Arity -/

@[simp] theorem arity_diffVar (n i : ℕ) : (diffVar n i).arity = n + i + 1 := by
  simp only [diffVar, arity_add, arity_neg, arity_X]
  omega

theorem arity_subUVMonomialFrom (n : ℕ) : ∀ (i : ℕ) (es : MonomialCode),
    (subUVMonomialFrom n i es).arity ≤ n + i + es.length
  | _, [] => by simp [subUVMonomialFrom]
  | i, e :: es => by
    refine le_trans (arity_mul_le _ _) ?_
    have h1 : (npow (diffVar n i) e).arity ≤ n + i + 1 := by
      refine le_trans (arity_npow_le _ e) ?_
      simp
    have h2 := arity_subUVMonomialFrom n (i + 1) es
    simp only [List.length_cons, max_le_iff]
    omega

/-- **The frozen arity bound.** Every exponent vector of `p` has length at most `p.arity`, so at
`i = 0` the helper bound is `2 * p.arity`. -/
theorem arity_subUV_le (p : PolynomialCode) : (subUV p).arity ≤ 2 * p.arity := by
  refine arity_le_of_forall_term_length_le fun t ht => ?_
  simp only [subUV, List.mem_flatMap] at ht
  obtain ⟨s, hs, hts⟩ := ht
  have hlen : s.2.length ≤ p.arity := length_le_arity hs
  have hb : (mul (const s.1) (subUVMonomialFrom p.arity 0 s.2)).arity ≤ 2 * p.arity := by
    refine le_trans (arity_mul_le _ _) ?_
    have := arity_subUVMonomialFrom p.arity 0 s.2
    simp only [arity_const, max_le_iff]
    omega
  exact le_trans (length_le_arity hts) hb

/-! ### Evaluation -/

theorem eval_diffVar {n i : ℕ} {u v : List ℕ} (hu : u.length = n) (hi : i < n) :
    eval (diffVar n i) (u ++ v) = (u.getD i 0 : ℤ) - (v.getD i 0 : ℤ) := by
  have h1 : (u ++ v).getD i 0 = u.getD i 0 := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (hu ▸ hi)]
  have h2 : (u ++ v).getD (n + i) 0 = v.getD i 0 := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : u.length ≤ n + i), hu]
  simp only [diffVar, eval_add, eval_neg, eval_X, h1, h2]
  ring

theorem eval_subUVMonomialFrom {n : ℕ} {u v : List ℕ} (hu : u.length = n) (hv : v.length = n) :
    ∀ (i : ℕ) (es : MonomialCode), i + es.length ≤ n →
      eval (subUVMonomialFrom n i es) (u ++ v)
        = evalMonomialInt es ((diffList u v).drop i)
  | _, [], _ => by
    rw [show subUVMonomialFrom n _ [] = one from rfl, eval_one]
    rfl
  | i, e :: es, hle => by
    have hi : i < n := by simp only [List.length_cons] at hle; omega
    have hrec := eval_subUVMonomialFrom (u := u) (v := v) hu hv (i + 1) es
      (by simp only [List.length_cons] at hle; omega)
    have hdrop := drop_diffList i u v (by omega) (by omega)
    rw [show subUVMonomialFrom n i (e :: es)
        = mul (npow (diffVar n i) e) (subUVMonomialFrom n (i + 1) es) from rfl,
      eval_mul, eval_npow, eval_diffVar hu hi, hrec, hdrop, evalMonomialInt]

/-- **The frozen correctness statement.** At the two-block layout, the substituted code evaluates
over `ℕ` to what the original evaluates to over `ℤ` at the difference assignment. -/
theorem eval_subUV (p : PolynomialCode) {u v : List ℕ}
    (hu : u.length = p.arity) (hv : v.length = p.arity) :
    eval (subUV p) (u ++ v) = evalInt p (diffList u v) := by
  simp only [subUV, eval, evalInt, List.flatMap_def, List.map_flatten, List.sum_flatten,
    List.map_map, Function.comp_def]
  congr 1
  refine List.map_congr_left fun t ht => ?_
  have hlen : t.2.length ≤ p.arity := length_le_arity ht
  have h := eval_subUVMonomialFrom (u := u) (v := v) hu hv 0 t.2 (by omega)
  simp only [List.drop_zero] at h
  have := eval_mul (const t.1) (subUVMonomialFrom p.arity 0 t.2) (u ++ v)
  simp only [eval_const] at this
  rw [show ((mul (const t.1) (subUVMonomialFrom p.arity 0 t.2)).terms.map
      fun s => s.1 * evalMonomial s.2 (u ++ v)).sum
      = eval (mul (const t.1) (subUVMonomialFrom p.arity 0 t.2)) (u ++ v) from rfl, this, h]


end PolynomialCode

end Hilbert10


/- Source: Hilbert10.Internal.CodeAlgebraComp, Hilbert10 v2.3.0, Apache-2.0. -/
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# The code algebra is primitive recursive

Issue #28. Both reductions build their transformed code out of the same six operations, and both
need the map on codes to be computable, so the operation-level `Primrec` lemmas live here rather
than in either reduction.

## The integer dependency, certified by the proofs rather than predicted

Only two integer operations are reached:

* `Primrec.int_neg`, for `neg`;
* `Primrec.int_mul`, for the coefficients of a convolution product.

Nothing combines coefficients by integer *addition* — `add` is list append, and `const` merely
transports its coefficient. That is the minimal scope #36 should propose upstream.

## Main results

* `Hilbert10.PolynomialCode.primrec₂_add`, `primrec₂_mul`, `primrec₂_npow` and friends
-/

namespace Hilbert10

namespace PolynomialCode

open Primrec

/-! ### Exponent addition -/

theorem primrec₂_addExponents : Primrec₂ addExponents := by
  have h : Primrec fun q : MonomialCode × MonomialCode =>
      (List.range (max q.1.length q.2.length)).map fun i => q.1.getD i 0 + q.2.getD i 0 := by
    refine Primrec.list_map
      (Primrec.list_range.comp (Primrec₂.comp Primrec.nat_max
        (Primrec.list_length.comp Primrec.fst) (Primrec.list_length.comp Primrec.snd))) ?_
    exact Primrec₂.comp Primrec.nat_add
      (Primrec₂.comp (f := fun (l : MonomialCode) (n : ℕ) => l.getD n 0) (Primrec.list_getD 0)
        (Primrec.fst.comp Primrec.fst) Primrec.snd)
      (Primrec₂.comp (f := fun (l : MonomialCode) (n : ℕ) => l.getD n 0) (Primrec.list_getD 0)
        (Primrec.snd.comp Primrec.fst) Primrec.snd)
  exact h.of_eq fun q => (addExponents_eq_range q.1 q.2).symm

/-! ### The operations -/

theorem primrec_const : Primrec const := by
  have h : Primrec fun c : ℤ => mk [(c, ([] : MonomialCode))] :=
    primrec_mk.comp (Primrec.list_cons.comp
      (Primrec.id.pair (Primrec.const ([] : MonomialCode)))
      (Primrec.const []))
  exact h.of_eq fun c => rfl

theorem primrec_X : Primrec X := by
  have h : Primrec fun i : ℕ => mk [((1 : ℤ), List.replicate i 0 ++ [1])] := by
    have hexp : Primrec fun i : ℕ => List.replicate i (0 : ℕ) ++ [1] :=
      Primrec₂.comp Primrec.list_append Primrec.list_replicate_zero (Primrec.const [1])
    exact primrec_mk.comp (Primrec.list_cons.comp
      ((Primrec.const (1 : ℤ)).pair hexp) (Primrec.const []))
  exact h.of_eq fun i => rfl

theorem primrec₂_add : Primrec₂ add := by
  have h : Primrec fun q : PolynomialCode × PolynomialCode => mk (q.1.terms ++ q.2.terms) :=
    primrec_mk.comp (Primrec₂.comp Primrec.list_append
      (primrec_terms.comp Primrec.fst) (primrec_terms.comp Primrec.snd))
  exact h.of_eq fun q => rfl

theorem primrec_neg : Primrec neg := by
  have h : Primrec fun p : PolynomialCode => mk (p.terms.map fun t => (-t.1, t.2)) := by
    refine primrec_mk.comp (Primrec.list_map primrec_terms ?_)
    exact (Primrec.int_neg.comp (Primrec.fst.comp Primrec.snd)).pair
      (Primrec.snd.comp Primrec.snd)
  exact h.of_eq fun p => rfl

theorem primrec₂_mul : Primrec₂ mul := by
  have h : Primrec fun q : PolynomialCode × PolynomialCode =>
      mk (q.1.terms.flatMap fun t => q.2.terms.map fun s =>
        (t.1 * s.1, addExponents t.2 s.2)) := by
    refine primrec_mk.comp (Primrec.list_flatMap (primrec_terms.comp Primrec.fst) ?_)
    refine Primrec.list_map (primrec_terms.comp (Primrec.snd.comp Primrec.fst)) ?_
    exact (Primrec₂.comp Primrec.int_mul
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) (Primrec.fst.comp Primrec.snd)).pair
      (Primrec₂.comp primrec₂_addExponents
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) (Primrec.snd.comp Primrec.snd))
  exact h.of_eq fun q => rfl

theorem primrec₂_npow : Primrec₂ npow := by
  have h := Primrec.nat_rec' (f := fun q : PolynomialCode × ℕ => q.2)
    (g := fun _ : PolynomialCode × ℕ => one)
    (h := fun (q : PolynomialCode × ℕ) (r : ℕ × PolynomialCode) => mul q.1 r.2)
    Primrec.snd (Primrec.const one)
    (Primrec₂.comp primrec₂_mul (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))
  refine h.of_eq fun q => ?_
  obtain ⟨p, n⟩ := q
  induction n with
  | zero => rfl
  | succ m ih => simp only [npow, ← ih]

end PolynomialCode

end Hilbert10


/- Source: Hilbert10.Internal.SubUVComp, Hilbert10 v2.3.0, Apache-2.0. -/
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# The difference substitution is primitive recursive

Issue #28, third piece, computability half. `IntSolvable ≤₀ NatSolvable` needs a *computable* map
on codes, so this file proves `Primrec subUV`. Everything else about the substitution — semantics
and arity — lives on the structural definitions in `SubUV`; this file works through the index
presentations proved equal to them there.

## One vocabulary

The whole chain uses five list operations, all of which mathlib supplies `Primrec` lemmas for:
`list_range`, `list_map`, `list_getD`, `list_foldr`, `list_flatMap`. Nothing needs truncated
subtraction, and nothing needs a `zipWith` lemma — which mathlib does not have.

The operations of the code algebra are primitive recursive in `CodeAlgebraComp`, which is where
the integer dependency on #36 is certified; this file only assembles them.

## Main results

* `Hilbert10.PolynomialCode.primrec_subUV`
-/

namespace Hilbert10

namespace PolynomialCode

open Primrec

/-! ### Index presentation, for computability

`subUVMonomialFrom` increments its index in the recursive call, so `Primrec.list_foldr` does not
apply to it directly. The equivalent presentation below folds over `List.range`, where the index
is supplied rather than threaded, and it is proved equal to the structural definition once. Every
semantic and arity result stays on the structural one. -/

theorem subUVMonomialFrom_eq_foldr (n : ℕ) : ∀ (i : ℕ) (es : MonomialCode),
    subUVMonomialFrom n i es
      = (((List.range es.length).map fun j => npow (diffVar n (i + j)) (es.getD j 0)).foldr
          mul one)
  | _, [] => by simp [subUVMonomialFrom]
  | i, e :: es => by
    have ih := subUVMonomialFrom_eq_foldr n (i + 1) es
    rw [show subUVMonomialFrom n i (e :: es)
        = mul (npow (diffVar n i) e) (subUVMonomialFrom n (i + 1) es) from rfl, ih]
    simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map,
      List.foldr_cons, Function.comp_def]
    congr 2
    exact List.map_congr_left fun a _ => by
      rw [show i + 1 + a = i + (a + 1) from by omega]
      simp

/-! ### The substitution -/

private theorem primrec_diffVar : Primrec fun q : ℕ × ℕ => diffVar q.1 q.2 := by
  have h : Primrec fun q : ℕ × ℕ => add (X q.2) (neg (X (q.1 + q.2))) :=
    Primrec₂.comp primrec₂_add (primrec_X.comp Primrec.snd)
      (primrec_neg.comp (primrec_X.comp
        (Primrec₂.comp Primrec.nat_add Primrec.fst Primrec.snd)))
  exact h.of_eq fun q => rfl

private theorem primrec_subUVMonomialFrom :
    Primrec fun q : (ℕ × ℕ) × MonomialCode => subUVMonomialFrom q.1.1 q.1.2 q.2 := by
  have hfactors : Primrec fun q : (ℕ × ℕ) × MonomialCode =>
      (List.range q.2.length).map fun j => npow (diffVar q.1.1 (q.1.2 + j)) (q.2.getD j 0) := by
    refine Primrec.list_map (Primrec.list_range.comp (Primrec.list_length.comp Primrec.snd)) ?_
    refine Primrec₂.comp primrec₂_npow ?_ ?_
    · exact primrec_diffVar.comp
        ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
          (Primrec₂.comp Primrec.nat_add
            (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd))
    · exact Primrec₂.comp (f := fun (l : MonomialCode) (n : ℕ) => l.getD n 0)
        (Primrec.list_getD 0) (Primrec.snd.comp Primrec.fst) Primrec.snd
  have h : Primrec fun q : (ℕ × ℕ) × MonomialCode =>
      ((List.range q.2.length).map fun j =>
        npow (diffVar q.1.1 (q.1.2 + j)) (q.2.getD j 0)).foldr mul one := by
    refine Primrec.list_foldr (h := fun _ (r : PolynomialCode × PolynomialCode) => mul r.1 r.2)
      hfactors (Primrec.const one) ?_
    exact Primrec₂.comp primrec₂_mul (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  exact h.of_eq fun q => (subUVMonomialFrom_eq_foldr q.1.1 q.1.2 q.2).symm

/-- **The difference substitution is primitive recursive**, hence computable — which is what the
many-one reduction consumes. -/
theorem primrec_subUV : Primrec subUV := by
  have h : Primrec fun p : PolynomialCode =>
      mk (p.terms.flatMap fun t => (mul (const t.1) (subUVMonomialFrom p.arity 0 t.2)).terms) := by
    refine primrec_mk.comp (Primrec.list_flatMap primrec_terms ?_)
    refine primrec_terms.comp (Primrec₂.comp primrec₂_mul
      (primrec_const.comp (Primrec.fst.comp Primrec.snd)) ?_)
    exact primrec_subUVMonomialFrom.comp
      (((primrec_arity.comp Primrec.fst).pair (Primrec.const 0)).pair
        (Primrec.snd.comp Primrec.snd))
  exact h.of_eq fun p => rfl

theorem computable_subUV : Computable subUV := primrec_subUV.to_comp

end PolynomialCode

end Hilbert10


/- Source: Hilbert10.FourSquares, Hilbert10 v2.3.0, Apache-2.0. -/
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# The four-square constraint transformation

Issue #28, fourth piece. A natural root of `p` is an integer root of

```
p(x)² + Σ_{i < n} (xᵢ - (aᵢ² + bᵢ² + cᵢ² + dᵢ²))²
```

because over `ℤ` a sum of squares vanishes exactly when every summand does, and Lagrange's
theorem says the naturals are exactly the sums of four squares.

## Constraints, not substitution

The original variables are *kept*. Nothing is substituted into `p`, which is why this direction
does not expand every occurrence of every variable — unlike `x = u - v`, where the difference
really has to be substituted. That asymmetry between the two reductions is real and was expected.

## Layout, frozen in #28

For `n := p.arity`, the transformed code uses `5 * n` variables:

* `0 .. n-1` — the original `xᵢ`;
* `n + 4i .. n + 4i + 3` — the four-square witnesses for `xᵢ`.

## Public, unlike its computability

`fourSquares` is one of the two reductions between the natural and integer formulations, and the
square argument below is meaningful on its own — so this file is API. `Primrec fourSquares` is
what turns the transformation into a many-one reduction; it is unsupported machinery and stays in
`Internal/FourSquaresComp.lean`.

## Main definitions

* `Hilbert10.PolynomialCode.fourSq`
* `Hilbert10.PolynomialCode.fourSquares`

## Main results

* `Hilbert10.PolynomialCode.evalInt_fourSquares_eq_zero_iff`
* `Hilbert10.PolynomialCode.arity_fourSquares_le`
-/

namespace Hilbert10

namespace PolynomialCode

/-- The sum of four squares drawn from variable `i`'s witness block. -/
def fourSq (n i : ℕ) : PolynomialCode :=
  add (add (npow (X (n + 4 * i)) 2) (npow (X (n + 4 * i + 1)) 2))
    (add (npow (X (n + 4 * i + 2)) 2) (npow (X (n + 4 * i + 3)) 2))

/-- The constraint forcing `xᵢ` to equal a sum of four squares, as a square so that it is
nonnegative over `ℤ`. -/
def fourSqConstraint (n i : ℕ) : PolynomialCode :=
  npow (add (X i) (neg (fourSq n i))) 2

/-- **The four-square transformation.** -/
def fourSquares (p : PolynomialCode) : PolynomialCode :=
  add (npow p 2)
    (((List.range p.arity).map fun i => fourSqConstraint p.arity i).foldr add zero)

/-! ### Evaluation -/

@[simp] theorem evalInt_fourSq (n i : ℕ) (y : List ℤ) :
    evalInt (fourSq n i) y
      = (y.getD (n + 4 * i) 0) ^ 2 + (y.getD (n + 4 * i + 1) 0) ^ 2
        + ((y.getD (n + 4 * i + 2) 0) ^ 2 + (y.getD (n + 4 * i + 3) 0) ^ 2) := by
  simp [fourSq]

@[simp] theorem evalInt_fourSqConstraint (n i : ℕ) (y : List ℤ) :
    evalInt (fourSqConstraint n i) y
      = (y.getD i 0 - evalInt (fourSq n i) y) ^ 2 := by
  simp only [fourSqConstraint, evalInt_npow, evalInt_add, evalInt_neg, evalInt_X]
  ring

/-- The value of the transformed code: the original squared, plus one square per variable. -/
theorem evalInt_fourSquares (p : PolynomialCode) (y : List ℤ) :
    evalInt (fourSquares p) y
      = (evalInt p y) ^ 2
        + ((List.range p.arity).map fun i =>
            (y.getD i 0 - evalInt (fourSq p.arity i) y) ^ 2).sum := by
  simp only [fourSquares, evalInt_add, evalInt_npow, evalInt_foldr_add,
    evalInt_fourSqConstraint]

/-! ### The square argument, packaged once

Everything about sums of squares happens here, so neither direction of the root equivalence has
to repeat it. -/

private theorem sq_nonneg' (a : ℤ) : 0 ≤ a ^ 2 := by
  rw [pow_two, ← Int.natAbs_mul_self]
  exact Int.natCast_nonneg _

private theorem sq_eq_zero' {a : ℤ} (h : a ^ 2 = 0) : a = 0 := by
  by_contra hne
  rw [pow_two] at h
  exact mul_ne_zero hne hne h

private theorem list_sum_nonneg : ∀ {l : List ℤ}, (∀ x ∈ l, 0 ≤ x) → 0 ≤ l.sum
  | [], _ => by simp
  | a :: as, h => by
    have hrec := list_sum_nonneg (l := as) fun x hx => h x (by simp [hx])
    have ha := h a (by simp)
    simp only [List.sum_cons]
    omega

private theorem sum_eq_zero_of_nonneg : ∀ {l : List ℤ}, (∀ x ∈ l, 0 ≤ x) → l.sum = 0 →
    ∀ x ∈ l, x = 0
  | [], _, _ => by simp
  | a :: as, h, hs => by
    have ha : 0 ≤ a := h a (by simp)
    have has : 0 ≤ as.sum := list_sum_nonneg fun x hx => h x (by simp [hx])
    have hsum : a + as.sum = 0 := by simpa using hs
    have ha0 : a = 0 := by omega
    have has0 : as.sum = 0 := by omega
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact ha0
    · exact sum_eq_zero_of_nonneg (fun z hz => h z (by simp [hz])) has0 x hx'

/-- A sum of four squares is nonnegative. Stated here so the root proof learns `0 ≤ y.getD i 0`
from the packaged constraint without unfolding `fourSq`. -/
theorem evalInt_fourSq_nonneg (n i : ℕ) (y : List ℤ) : 0 ≤ evalInt (fourSq n i) y := by
  rw [evalInt_fourSq]
  have h1 := sq_nonneg' (y.getD (n + 4 * i) 0)
  have h2 := sq_nonneg' (y.getD (n + 4 * i + 1) 0)
  have h3 := sq_nonneg' (y.getD (n + 4 * i + 2) 0)
  have h4 := sq_nonneg' (y.getD (n + 4 * i + 3) 0)
  omega

/-- **The transformed code vanishes exactly when the original does and every constraint holds.**
A sum of squares over `ℤ` is zero only if every square is. -/
theorem evalInt_fourSquares_eq_zero_iff (p : PolynomialCode) (y : List ℤ) :
    evalInt (fourSquares p) y = 0 ↔
      evalInt p y = 0 ∧
        ∀ i < p.arity, y.getD i 0 = evalInt (fourSq p.arity i) y := by
  rw [evalInt_fourSquares]
  constructor
  · intro h
    have hsq : (0 : ℤ) ≤ (evalInt p y) ^ 2 := sq_nonneg' _
    have hterms : ∀ z ∈ (List.range p.arity).map fun i =>
        (y.getD i 0 - evalInt (fourSq p.arity i) y) ^ 2, (0 : ℤ) ≤ z := by
      intro z hz
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hz
      exact sq_nonneg' _
    have hsum : (0 : ℤ) ≤ ((List.range p.arity).map fun i =>
        (y.getD i 0 - evalInt (fourSq p.arity i) y) ^ 2).sum := list_sum_nonneg hterms
    have h1 : (evalInt p y) ^ 2 = 0 := by omega
    have h2 : ((List.range p.arity).map fun i =>
        (y.getD i 0 - evalInt (fourSq p.arity i) y) ^ 2).sum = 0 := by omega
    refine ⟨sq_eq_zero' h1, fun i hi => ?_⟩
    have hmem : (y.getD i 0 - evalInt (fourSq p.arity i) y) ^ 2 ∈
        (List.range p.arity).map fun i => (y.getD i 0 - evalInt (fourSq p.arity i) y) ^ 2 :=
      List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
    have := sum_eq_zero_of_nonneg hterms h2 _ hmem
    have hz : y.getD i 0 - evalInt (fourSq p.arity i) y = 0 := sq_eq_zero' this
    omega
  · rintro ⟨hp, hc⟩
    rw [hp]
    have : ((List.range p.arity).map fun i =>
        (y.getD i 0 - evalInt (fourSq p.arity i) y) ^ 2) = (List.range p.arity).map fun _ => 0 := by
      refine List.map_congr_left fun i hi => ?_
      rw [hc i (List.mem_range.mp hi)]
      ring
    rw [this]
    simp

/-! ### Arity -/

theorem arity_fourSq_le (n i : ℕ) : (fourSq n i).arity ≤ n + 4 * i + 4 := by
  have h : ∀ k : ℕ, (npow (X k) 2).arity ≤ k + 1 := fun k =>
    le_trans (arity_npow_le _ 2) (by simp)
  simp only [fourSq, arity_add, max_le_iff]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · exact le_trans (h _) (by omega)
  · exact le_trans (h _) (by omega)
  · exact le_trans (h _) (by omega)
  · exact le_trans (h _) (by omega)

theorem arity_fourSqConstraint_le (n i : ℕ) :
    (fourSqConstraint n i).arity ≤ max (i + 1) (n + 4 * i + 4) := by
  refine le_trans (arity_npow_le _ 2) ?_
  simp only [arity_add, arity_neg, arity_X, max_le_iff]
  exact ⟨le_max_left _ _, le_trans (arity_fourSq_le n i) (le_max_right _ _)⟩

/-- **The frozen arity bound.** -/
theorem arity_fourSquares_le (p : PolynomialCode) : (fourSquares p).arity ≤ 5 * p.arity := by
  simp only [fourSquares, arity_add, max_le_iff]
  refine ⟨le_trans (arity_npow_le _ 2) (by omega), ?_⟩
  refine arity_foldr_add_le _ _ _ fun i hi => ?_
  have hi' : i < p.arity := by simpa using hi
  refine le_trans (arity_fourSqConstraint_le p.arity i) ?_
  simp only [max_le_iff]
  omega

end PolynomialCode

end Hilbert10


/- Source: Hilbert10.Internal.FourSquaresComp, Hilbert10 v2.3.0, Apache-2.0. -/
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# The four-square transformation is primitive recursive

Issue #28, fourth piece, computability half. `NatSolvable ≤₀ IntSolvable` needs a *computable* map
on codes, so this file proves `Primrec fourSquares`. Everything semantic lives in `FourSquares`.

Unlike the difference substitution, nothing here is substituted into `p`: the transformed code is
built from `p` itself, the arity, and one constraint per variable. The only shape that needs work
is the fold over `List.range p.arity`, and the same `list_range`/`list_map`/`list_foldr` vocabulary
covers it. No integer operation beyond the two already certified in `CodeAlgebraComp` is reached.

## Main results

* `Hilbert10.PolynomialCode.primrec_fourSquares`
-/

namespace Hilbert10

namespace PolynomialCode

open Primrec

private theorem primrec_npow_X {α : Type*} [Primcodable α] {k : α → ℕ} (hk : Primrec k) :
    Primrec fun a => npow (X (k a)) 2 :=
  Primrec₂.comp primrec₂_npow (primrec_X.comp hk) (Primrec.const 2)

private theorem primrec_fourSq : Primrec fun q : ℕ × ℕ => fourSq q.1 q.2 := by
  have hbase : Primrec fun q : ℕ × ℕ => q.1 + 4 * q.2 :=
    Primrec₂.comp Primrec.nat_add Primrec.fst
      (Primrec₂.comp Primrec.nat_mul (Primrec.const 4) Primrec.snd)
  have hoff : ∀ c : ℕ, Primrec fun q : ℕ × ℕ => q.1 + 4 * q.2 + c := fun c =>
    Primrec₂.comp Primrec.nat_add hbase (Primrec.const c)
  have h : Primrec fun q : ℕ × ℕ =>
      add (add (npow (X (q.1 + 4 * q.2)) 2) (npow (X (q.1 + 4 * q.2 + 1)) 2))
        (add (npow (X (q.1 + 4 * q.2 + 2)) 2) (npow (X (q.1 + 4 * q.2 + 3)) 2)) :=
    Primrec₂.comp primrec₂_add
      (Primrec₂.comp primrec₂_add (primrec_npow_X hbase) (primrec_npow_X (hoff 1)))
      (Primrec₂.comp primrec₂_add (primrec_npow_X (hoff 2)) (primrec_npow_X (hoff 3)))
  exact h.of_eq fun q => rfl

private theorem primrec_fourSqConstraint :
    Primrec fun q : ℕ × ℕ => fourSqConstraint q.1 q.2 := by
  have h : Primrec fun q : ℕ × ℕ => npow (add (X q.2) (neg (fourSq q.1 q.2))) 2 :=
    Primrec₂.comp primrec₂_npow
      (Primrec₂.comp primrec₂_add (primrec_X.comp Primrec.snd)
        (primrec_neg.comp primrec_fourSq))
      (Primrec.const 2)
  exact h.of_eq fun q => rfl

/-- **The four-square transformation is primitive recursive**, hence computable — which is what
the many-one reduction consumes. -/
theorem primrec_fourSquares : Primrec fourSquares := by
  have hconstraints : Primrec fun p : PolynomialCode =>
      (List.range p.arity).map fun i => fourSqConstraint p.arity i := by
    refine Primrec.list_map (Primrec.list_range.comp primrec_arity) ?_
    exact primrec_fourSqConstraint.comp ((primrec_arity.comp Primrec.fst).pair Primrec.snd)
  have hfold : Primrec fun p : PolynomialCode =>
      (((List.range p.arity).map fun i => fourSqConstraint p.arity i).foldr add zero) := by
    refine Primrec.list_foldr (h := fun _ (r : PolynomialCode × PolynomialCode) => add r.1 r.2)
      hconstraints (Primrec.const zero) ?_
    exact Primrec₂.comp primrec₂_add (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  have h : Primrec fun p : PolynomialCode =>
      add (npow p 2)
        (((List.range p.arity).map fun i => fourSqConstraint p.arity i).foldr add zero) :=
    Primrec₂.comp primrec₂_add
      (Primrec₂.comp primrec₂_npow Primrec.id (Primrec.const 2)) hfold
  exact h.of_eq fun p => rfl

theorem computable_fourSquares : Computable fourSquares := primrec_fourSquares.to_comp

end PolynomialCode

end Hilbert10


/- Source: Hilbert10.IntSolvable, Hilbert10 v2.3.0, Apache-2.0. -/
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# Integer solvability, and its equivalence with the natural version

Issue #28. `IntSolvable` is Hilbert's own question for the encoded wire format: does the coded
polynomial have an **integer** root? This file defines it and proves that it holds exactly when
the difference-substituted code has a natural root.

## Why the equivalence is stated on codes

`intSolvable_iff_natSolvable_subUV` is the mathematical content of the reduction
`IntSolvable ≤₀ NatSolvable`; what the reduction adds is that `subUV` is computable. Keeping the
two apart means the arithmetic can be checked without reading a computability proof, and the
computability proof does not have to re-establish any arithmetic.

## Both directions normalise first

The predicates quantify over arbitrary-length assignments, while the two-block reading needs a
fixed boundary at `p.arity`. Each direction therefore normalises its witness to an exact length
before splitting: integer witnesses through `exists_length_eq_arity_evalInt_eq`, natural ones
through the arity bound `arity_subUV_le` and zero-extension. Skipping that step would let a short
witness make `take` and `drop` describe the wrong blocks.

## Main results

* `Hilbert10.IntSolvable`, `Hilbert10.intSolvable_iff_arity`,
  `Hilbert10.intSolvable_iff_of_denote_eq`
* `Hilbert10.intSolvable_iff_natSolvable_subUV`
* `Hilbert10.intSolvable_manyOneReducible_natSolvable`
* `Hilbert10.natSolvable_iff_intSolvable_fourSquares`
* `Hilbert10.natSolvable_manyOneReducible_intSolvable`
* `Hilbert10.natSolvable_manyOneEquiv_intSolvable`
-/

namespace Hilbert10

open PolynomialCode

/-- **Hilbert's tenth problem over the integers**, for the encoded wire format. -/
def IntSolvable (p : PolynomialCode) : Prop := ∃ x : List ℤ, p.evalInt x = 0

theorem intSolvable_iff (p : PolynomialCode) :
    IntSolvable p ↔ ∃ x : List ℤ, p.evalInt x = 0 := Iff.rfl

/-- An integer root may always be taken to have length exactly `arity`, matching
`natSolvable_iff_arity`. -/
theorem intSolvable_iff_arity (p : PolynomialCode) :
    IntSolvable p ↔ ∃ x : List ℤ, x.length = p.arity ∧ p.evalInt x = 0 := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨y, hy, hyx⟩ := p.exists_length_eq_evalInt_eq x (m := p.arity) le_rfl
    exact ⟨y, hy, hyx.trans hx⟩
  · rintro ⟨x, _, hx⟩
    exact ⟨x, hx⟩

/-- **Integer solvability depends only on the denoted polynomial**, as
`natSolvable_iff_of_denote_eq` says for the natural version. -/
theorem intSolvable_iff_of_denote_eq {p q : PolynomialCode} (h : p.denote = q.denote) :
    IntSolvable p ↔ IntSolvable q :=
  exists_congr fun x => by rw [PolynomialCode.evalInt_eq_of_denote_eq h]

/-- **The reduction, as an equivalence of codes.** An integer root of `p` is exactly a natural
root of the difference-substituted code. -/
theorem intSolvable_iff_natSolvable_subUV (p : PolynomialCode) :
    IntSolvable p ↔ NatSolvable (subUV p) := by
  constructor
  · rintro ⟨x, hx⟩
    -- normalise the integer witness, then split it componentwise
    obtain ⟨y, hylen, hy⟩ := exists_length_eq_arity_evalInt_eq p x
    refine ⟨y.map Int.toNat ++ y.map fun z => (-z).toNat, ?_⟩
    rw [eval_subUV p (by simpa using hylen) (by simpa using hylen), diffList_toNat, hy, hx]
  · rintro ⟨w, hw⟩
    -- normalise the natural witness to exactly `2 * p.arity`, then split it in half
    set n := p.arity with hn
    set w' := (w ++ List.replicate (2 * n) 0).take (2 * n) with hw'
    have hw'len : w'.length = 2 * n := by
      simp only [hw', List.length_take, List.length_append, List.length_replicate]
      omega
    have hw'eval : eval (subUV p) w' = 0 := by
      have hsplit : (w ++ List.replicate (2 * n) 0)
          = w' ++ (w ++ List.replicate (2 * n) 0).drop (2 * n) := by
        simp [hw']
      have hlen : (subUV p).arity ≤ w'.length := by
        rw [hw'len]; exact arity_subUV_le p
      calc eval (subUV p) w'
          = eval (subUV p) (w' ++ (w ++ List.replicate (2 * n) 0).drop (2 * n)) :=
            (eval_append_of_arity_le hlen _).symm
        _ = eval (subUV p) (w ++ List.replicate (2 * n) 0) := by rw [← hsplit]
        _ = eval (subUV p) w := eval_append_replicate_zero _ _ _
        _ = 0 := hw
    refine ⟨diffList (w'.take n) (w'.drop n), ?_⟩
    have hu : (w'.take n).length = n := by
      simp only [List.length_take, hw'len]
      omega
    have hv : (w'.drop n).length = n := by
      simp only [List.length_drop, hw'len]
      omega
    rw [← eval_subUV p hu hv, List.take_append_drop, hw'eval]

/-- **Integer solvability reduces to natural solvability.** The computable map is the difference
substitution; the equivalence above is its correctness. -/
theorem intSolvable_manyOneReducible_natSolvable : IntSolvable ≤₀ NatSolvable :=
  ⟨subUV, computable_subUV, intSolvable_iff_natSolvable_subUV⟩

/-! ### The other direction: four squares

Natural roots become integer roots of the constraint code. Nothing is substituted into `p`; the
original variables are kept and each is forced to be a sum of four integer squares. -/

/-- **The four-square equivalence.** -/
theorem natSolvable_iff_intSolvable_fourSquares (p : PolynomialCode) :
    NatSolvable p ↔ IntSolvable (fourSquares p) := by
  set n := p.arity with hn
  constructor
  · rintro hp
    obtain ⟨x, hxlen, hx⟩ := (natSolvable_iff_arity p).mp hp
    -- Lagrange supplies four witnesses for every coordinate
    choose a b c d hw using fun i : ℕ => Nat.sum_four_squares (x.getD i 0)
    set w : ℕ → ℕ := fun k =>
      if k % 4 = 0 then a (k / 4) else if k % 4 = 1 then b (k / 4)
      else if k % 4 = 2 then c (k / 4) else d (k / 4) with hwdef
    refine ⟨x.map (Nat.cast : ℕ → ℤ)
        ++ (List.range (4 * n)).map fun k => ((w k : ℕ) : ℤ), ?_⟩
    set y : List ℤ := x.map (Nat.cast : ℕ → ℤ)
      ++ (List.range (4 * n)).map fun k => ((w k : ℕ) : ℤ) with hy
    have hfirst : (x.map (Nat.cast : ℕ → ℤ)).length = n := by
      simp only [List.length_map, hxlen, hn]
    -- the original block
    have hx0 : ∀ i < n, y.getD i 0 = ((x.getD i 0 : ℕ) : ℤ) := by
      intro i hi
      rw [hy, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < _),
        ← List.getD_eq_getElem?_getD, getD_map_natCast]
    -- the interleaved witness block, stated only at `n + (4 * i + r)`
    have hacc : ∀ i r : ℕ, i < n → r < 4 →
        y.getD (n + (4 * i + r)) 0 = ((w (4 * i + r) : ℕ) : ℤ) := by
      intro i r hi hr
      have hlt : 4 * i + r < 4 * n := by omega
      rw [hy, List.getD_eq_getElem?_getD,
        List.getElem?_append_right (by omega : (x.map (Nat.cast : ℕ → ℤ)).length ≤ n + (4 * i + r))]
      rw [hfirst, show n + (4 * i + r) - n = 4 * i + r from by omega,
        List.getElem?_map, List.getElem?_range hlt]
      simp
    refine (evalInt_fourSquares_eq_zero_iff p y).mpr ⟨?_, fun i hi => ?_⟩
    · -- `p` only reads the first block
      have : evalInt p y = evalInt p (x.map (Nat.cast : ℕ → ℤ)) := by
        rw [hy]
        exact evalInt_append_of_arity_le (by rw [hfirst]) _
      rw [this, evalInt_map_natCast, hx]
    · -- each constraint holds by Lagrange
      have e0 := hacc i 0 hi (by omega)
      have e1 := hacc i 1 hi (by omega)
      have e2 := hacc i 2 hi (by omega)
      have e3 := hacc i 3 hi (by omega)
      have hw0 : w (4 * i + 0) = a i := by simp [hwdef]
      have hw1 : w (4 * i + 1) = b i := by
        have hm : (4 * i + 1) % 4 = 1 := by omega
        have hd : (4 * i + 1) / 4 = i := by omega
        simp [hwdef, hm, hd]
      have hw2 : w (4 * i + 2) = c i := by
        have hm : (4 * i + 2) % 4 = 2 := by omega
        have hd : (4 * i + 2) / 4 = i := by omega
        simp [hwdef, hm, hd]
      have hw3 : w (4 * i + 3) = d i := by
        have hm : (4 * i + 3) % 4 = 3 := by omega
        have hd : (4 * i + 3) / 4 = i := by omega
        simp [hwdef, hm, hd]
      rw [hx0 i hi, evalInt_fourSq,
        show n + 4 * i + 3 = n + (4 * i + 3) from by omega,
        show n + 4 * i + 2 = n + (4 * i + 2) from by omega,
        show n + 4 * i + 1 = n + (4 * i + 1) from by omega,
        show n + 4 * i = n + (4 * i + 0) from by omega,
        e0, e1, e2, e3, hw0, hw1, hw2, hw3, ← hw i]
      push_cast
      ring
  · rintro ⟨y₀, hy₀⟩
    -- normalise to the full frozen length, then split off the first block
    obtain ⟨y, hylen, hyval⟩ :=
      exists_length_eq_evalInt_eq (fourSquares p) y₀ (arity_fourSquares_le p)
    have hzero : evalInt (fourSquares p) y = 0 := by rw [hyval, hy₀]
    obtain ⟨hp, hc⟩ := (evalInt_fourSquares_eq_zero_iff p y).mp hzero
    have hnonneg : ∀ i < n, 0 ≤ y.getD i 0 := by
      intro i hi
      rw [hc i hi]
      exact evalInt_fourSq_nonneg _ _ _
    refine (natSolvable_iff_arity p).mpr ⟨(y.take n).map Int.toNat, ?_, ?_⟩
    · simp only [List.length_map, List.length_take, hylen]
      omega
    have hcast : ((y.take n).map Int.toNat).map (Nat.cast : ℕ → ℤ) = y.take n := by
      refine List.ext_getElem (by simp) fun i h1 h2 => ?_
      have hi : i < n := by
        simp only [List.length_take, hylen] at h2
        omega
      have := hnonneg i hi
      simp only [List.getElem_map, List.getElem_take]
      have hy0 : y.getD i 0 = y[i]'(by omega) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
        simp
      rw [hy0] at this
      omega
    rw [eval_eq_evalInt, hcast]
    have hsplit : evalInt p (y.take n) = evalInt p y := by
      have harity : p.arity ≤ (y.take n).length := by
        simp only [List.length_take, hylen]
        omega
      have := evalInt_append_of_arity_le (p := p) (x := y.take n) harity (y.drop n)
      rw [List.take_append_drop] at this
      exact this.symm
    rw [hsplit, hp]

/-- **Natural solvability reduces to integer solvability.** The computable map is the four-square
transformation; the equivalence above is its correctness. With
`intSolvable_manyOneReducible_natSolvable`, the two formulations of Hilbert's tenth problem for
the wire format are many-one equivalent. -/
theorem natSolvable_manyOneReducible_intSolvable : NatSolvable ≤₀ IntSolvable :=
  ⟨fourSquares, computable_fourSquares, natSolvable_iff_intSolvable_fourSquares⟩

/-- **The two formulations have the same many-one degree.** Packaged with mathlib's
`ManyOneEquiv`, so that downstream results can transport reducibility facts along it. -/
theorem natSolvable_manyOneEquiv_intSolvable : ManyOneEquiv NatSolvable IntSolvable :=
  ⟨natSolvable_manyOneReducible_intSolvable, intSolvable_manyOneReducible_natSolvable⟩

/-! ### Zero-arity regression

At `p.arity = 0` the frozen layout has no variables at all and the constraint list is empty, so the
transformation degenerates to `p²`. Both truth values are checked, since an off-by-one in the empty
`List.range` would make the equivalence vacuously true rather than visibly wrong. -/

example : IntSolvable (fourSquares (const 0)) :=
  (natSolvable_iff_intSolvable_fourSquares _).mp ⟨[], by simp⟩

example : ¬ IntSolvable (fourSquares (const 1)) := by
  rw [← natSolvable_iff_intSolvable_fourSquares]
  rintro ⟨x, hx⟩
  simp at hx

end Hilbert10


/- Source: Hilbert10.Endpoints, Hilbert10 v2.3.0, Apache-2.0. -/
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# H10 endpoints: recursively enumerable predicates reduce to `NatSolvable`

Issue #25. DPRM (#23) says a recursively enumerable predicate is Diophantine; #35 says a
represented predicate many-one reduces to `NatSolvable`. This file is the wrapper that composes
them, so the only content here is the shuffle between `R : ℕ → Prop` and the unary tuple
predicate `fun v : Fin 1 → ℕ => R (v 0)` that `Dioph` is stated for.

## The code is fixed per relation

The polynomial is obtained by eliminating an existential inside a proposition, so it is chosen
*for each* `R` and there is no function from predicates to codes here. Nothing in this
development produces a code uniform in `R`, and nothing needs one — the reduction
`fun a => code.instantiate [a]` is computable because `code` is a constant. See
`Specialization.lean` and #1's scope argument.

## Arbitrary domains, including the empty one

`REPred.manyOneReducible_natSolvable'` is the same statement for a predicate on any
`Primcodable` type, with **no `Inhabited` hypothesis**. #26 offered two ways to get there:
carry `[Inhabited α]`, or hand-roll the transported predicate `fun n => ∃ a, encode a = n ∧ R a`.
Neither was needed. Nonemptiness is decided inside the proof: when `α` is inhabited, mathlib's
`toNat` applies and `manyOneReducible_toNat` supplies the reduction; when it is empty, any
computable function is a reduction because the equivalence it has to satisfy is vacuous.

Recording that so it is not re-litigated: the case split costs two lines and keeps the
hypothesis off the statement, which is what a completeness theorem should look like.

## What the endpoints say

`NatSolvable` is **many-one complete among recursively enumerable predicates**: it is itself
recursively enumerable (#14), and every recursively enumerable predicate reduces to it. That is
the computability-theoretic content of Hilbert's tenth problem, and it says more than
undecidability — undecidability is the corollary obtained by reducing the halting problem.

The same holds for the integer formulation Hilbert actually asked about. `NatSolvable` and
`IntSolvable` are many-one equivalent (#28), so completeness and undecidability transfer in both
directions; neither transfer needs computability of integer evaluation.

## Main results

* `Hilbert10.REPred.manyOneReducible_natSolvable`
* `Hilbert10.REPred.manyOneReducible_natSolvable'`
* `Hilbert10.natSolvable_re_complete`
* `Hilbert10.halting_manyOneReducible_natSolvable`
* `Hilbert10.not_computablePred_natSolvable`, `Hilbert10.not_rePred_not_natSolvable`
* `Hilbert10.intSolvable_re_complete`
* `Hilbert10.not_computablePred_intSolvable`, `Hilbert10.not_rePred_not_intSolvable`
-/

namespace Hilbert10

/-- A unary predicate on `ℕ`, read as a predicate on one-element tuples, stays recursively
enumerable: it is the original composed with the computable projection.

Stated as a plain lemma rather than for dot notation, since `REPred` unfolds through `Partrec`
to `Nat.Partrec` and dot notation resolves against that. -/
theorem REPred.fin_one {R : ℕ → Prop} (hR : REPred R) : REPred fun v : Fin 1 → ℕ => R (v 0) :=
  Partrec.comp hR ((Primrec.fin_app.comp Primrec.id (Primrec.const 0)).to_comp)

/-- **Every recursively enumerable predicate on `ℕ` many-one reduces to `NatSolvable`.**

DPRM supplies a Diophantine representation, the normal form turns it into a polynomial, and the
specialisation lemma turns that into a computable reduction. -/
theorem REPred.manyOneReducible_natSolvable {R : ℕ → Prop} (hR : REPred R) :
    R ≤₀ NatSolvable :=
  representsNat_manyOneReducible_natSolvable
    ((dioph_iff_exists_fin_mvPolynomial _).mp (REPred.dioph (REPred.fin_one hR)))

/-- **The same, for a predicate on any `Primcodable` type.** No `Inhabited` hypothesis: the empty
case is handled separately, where the reduction's equivalence is vacuous. -/
theorem REPred.manyOneReducible_natSolvable' {α : Type*} [Primcodable α] {R : α → Prop}
    (hR : REPred R) : R ≤₀ NatSolvable := by
  by_cases hne : Nonempty α
  · obtain ⟨a₀⟩ := hne
    haveI : Inhabited α := ⟨a₀⟩
    have hRE : REPred fun n : ℕ => R ((Encodable.decode (α := α) n).getD default) :=
      Partrec.comp hR (Computable.option_getD Computable.decode (Computable.const default))
    exact manyOneReducible_toNat.trans (REPred.manyOneReducible_natSolvable hRE)
  · exact ⟨fun _ => ⟨[]⟩, Computable.const _, fun a => absurd ⟨a⟩ hne⟩

/-! ### The endpoints

`rePred_natSolvable` is the other half of completeness and lives in `DiophToRE` (#14): evaluating
an encoded polynomial at a witness is computable, so solvability is recursively enumerable. -/

/-- **`NatSolvable` is many-one complete among recursively enumerable predicates.** Together with
`rePred_natSolvable` this is the computability-theoretic form of Hilbert's tenth problem. -/
theorem natSolvable_re_complete {α : Type*} [Primcodable α] {R : α → Prop} (hR : REPred R) :
    R ≤₀ NatSolvable :=
  REPred.manyOneReducible_natSolvable' hR

/-- **The halting problem reduces to `NatSolvable`.** An instance of completeness, and the one
that makes the undecidability corollary immediate. -/
theorem halting_manyOneReducible_natSolvable :
    (fun c : Nat.Partrec.Code => (Nat.Partrec.Code.eval c 0).Dom) ≤₀ NatSolvable :=
  natSolvable_re_complete (ComputablePred.halting_problem_re 0)

/-- **Hilbert's tenth problem over the naturals is undecidable.** -/
theorem not_computablePred_natSolvable : ¬ ComputablePred NatSolvable := fun h =>
  ComputablePred.halting_problem 0
    (ComputablePred.computable_of_manyOneReducible halting_manyOneReducible_natSolvable h)

/-- **Insolubility is not recursively enumerable.** Solvability is (`rePred_natSolvable`), so if
its complement were too the problem would be decidable. This is the precise sense in which a
search for roots cannot be complemented by a search for certificates that none exist. -/
theorem not_rePred_not_natSolvable : ¬ REPred fun p => ¬ NatSolvable p := fun h =>
  not_computablePred_natSolvable
    (ComputablePred.computable_iff_re_compl_re'.2 ⟨rePred_natSolvable, h⟩)

/-! ### The integer formulation

#28. Both reductions live in `IntSolvable`; recursive enumerability transfers backwards along the
one into `NatSolvable` (by `REPred.of_manyOneReducible`, which is deliberately below DPRM in
`Computability`), and completeness forwards along the one out of it. That is why no computability
of integer *evaluation* is needed anywhere. -/

/-- **Integer solvability is recursively enumerable.** Obtained from the reduction rather than
from computability of `evalInt`, which nothing needs. -/
theorem rePred_intSolvable : REPred IntSolvable :=
  REPred.of_manyOneReducible intSolvable_manyOneReducible_natSolvable rePred_natSolvable

/-- **`IntSolvable` is many-one complete among recursively enumerable predicates.** Completeness
travels along the four-square reduction; `rePred_intSolvable` is the other half. -/
theorem intSolvable_re_complete {α : Type*} [Primcodable α] {R : α → Prop} (hR : REPred R) :
    R ≤₀ IntSolvable :=
  (natSolvable_re_complete hR).trans natSolvable_manyOneReducible_intSolvable

/-- **The halting problem reduces to `IntSolvable`.** -/
theorem halting_manyOneReducible_intSolvable :
    (fun c : Nat.Partrec.Code => (Nat.Partrec.Code.eval c 0).Dom) ≤₀ IntSolvable :=
  intSolvable_re_complete (ComputablePred.halting_problem_re 0)

/-- **Hilbert's tenth problem, in the form Hilbert asked it, is undecidable.** No algorithm
decides whether an encoded polynomial has an integer root. -/
theorem not_computablePred_intSolvable : ¬ ComputablePred IntSolvable := fun h =>
  ComputablePred.halting_problem 0
    (ComputablePred.computable_of_manyOneReducible halting_manyOneReducible_intSolvable h)

/-- **Integer insolubility is not recursively enumerable**, for the same reason as the natural
version. -/
theorem not_rePred_not_intSolvable : ¬ REPred fun p => ¬ IntSolvable p := fun h =>
  not_computablePred_intSolvable
    (ComputablePred.computable_iff_re_compl_re'.2 ⟨rePred_intSolvable, h⟩)

end Hilbert10


/- Source: Hilbert10.SumSquares, Hilbert10 v2.3.0, Apache-2.0. -/
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# The sum-of-squares transformation

Issue #53, first layer. A finite system of equations `p₁ = 0, …, pₖ = 0` with one shared
assignment has a solution exactly when the single equation

```
p₁² + ⋯ + pₖ² = 0
```

does, because over `ℤ` a sum of squares vanishes exactly when every summand does. The same
argument carries the natural formulation, since `eval` is `evalInt` restricted along the cast.

## The shared assignment is the contract

`sumSquaresCode` says nothing about relabelling variables: every member of the system reads the
*same* assignment, and a variable index means the same variable in every equation. That is the
point of a system, and it is what distinguishes "one witness for the whole system" from "a
witness for each equation" — see the contradictory pair in `Systems.lean`. Any relabelling or
fresh-variable machinery is a separate consumer's concern (#57).

## Public, unlike its computability

Like `subUV` and `fourSquares`, the transformation is API and its square argument stands alone;
`Primrec sumSquaresCode`, which turns it into a many-one reduction, is in
`Internal/SumSquaresComp.lean`.

## Main definitions

* `Hilbert10.PolynomialCode.sumSquaresCode`
* `Hilbert10.PolynomialCode.systemArity`

## Main results

* `Hilbert10.PolynomialCode.evalInt_sumSquaresCode`, `eval_sumSquaresCode`
* `Hilbert10.PolynomialCode.evalInt_sumSquaresCode_eq_zero_iff`, `eval_sumSquaresCode_eq_zero_iff`
* `Hilbert10.PolynomialCode.arity_sumSquaresCode_le`
-/

namespace Hilbert10

namespace PolynomialCode

/-- The sum of the squares of a list of codes. -/
def sumSquaresCode (ps : List PolynomialCode) : PolynomialCode :=
  (ps.map fun p => mul p p).foldr add zero

/-- The arity of a system: the largest arity of a member, `0` for the empty system. -/
def systemArity (ps : List PolynomialCode) : ℕ := (ps.map arity).foldr max 0

@[simp] theorem sumSquaresCode_nil : sumSquaresCode [] = ⟨[]⟩ := rfl

@[simp] theorem systemArity_nil : systemArity [] = 0 := rfl

@[simp] theorem systemArity_cons (p : PolynomialCode) (ps : List PolynomialCode) :
    systemArity (p :: ps) = max p.arity (systemArity ps) := rfl

theorem arity_le_systemArity {p : PolynomialCode} {ps : List PolynomialCode} (h : p ∈ ps) :
    p.arity ≤ systemArity ps := by
  induction ps with
  | nil => simp at h
  | cons q qs ih =>
    rw [systemArity_cons]
    rcases List.mem_cons.mp h with rfl | h'
    · exact le_max_left _ _
    · exact le_max_of_le_right (ih h')

/-! ### Evaluation -/

/-- **The evaluation formula, over `ℤ`.** -/
theorem evalInt_sumSquaresCode (ps : List PolynomialCode) (x : List ℤ) :
    evalInt (sumSquaresCode ps) x = (ps.map fun p => (evalInt p x) ^ 2).sum := by
  rw [sumSquaresCode, evalInt_foldr_add]
  congr 1
  exact List.map_congr_left fun p _ => by rw [evalInt_mul, sq]

/-- **The evaluation formula, over `ℕ`**, through the cast bridge. -/
theorem eval_sumSquaresCode (ps : List PolynomialCode) (x : List ℕ) :
    eval (sumSquaresCode ps) x = (ps.map fun p => (eval p x) ^ 2).sum := by
  rw [← evalInt_map_natCast, evalInt_sumSquaresCode]
  simp only [evalInt_map_natCast]

/-! ### A sum of squares vanishes exactly when every summand does -/

private theorem freerSumSquares_sq_nonneg (a : ℤ) : 0 ≤ a ^ 2 := by
  rw [pow_two, ← Int.natAbs_mul_self]
  exact Int.natCast_nonneg _

private theorem sum_map_sq_nonneg {α : Type*} (f : α → ℤ) :
    ∀ l : List α, 0 ≤ (l.map fun a => f a ^ 2).sum
  | [] => le_rfl
  | a :: as => by
    have h := sum_map_sq_nonneg f as
    have ha : 0 ≤ f a ^ 2 := freerSumSquares_sq_nonneg _
    simp only [List.map_cons, List.sum_cons]
    omega

theorem sum_map_sq_eq_zero_iff {α : Type*} (f : α → ℤ) :
    ∀ l : List α, (l.map fun a => f a ^ 2).sum = 0 ↔ ∀ a ∈ l, f a = 0
  | [] => by simp
  | a :: as => by
    have has := sum_map_sq_nonneg f as
    have ha : 0 ≤ f a ^ 2 := freerSumSquares_sq_nonneg _
    rw [List.map_cons, List.sum_cons, List.forall_mem_cons, ← sum_map_sq_eq_zero_iff f as]
    constructor
    · intro h
      have h1 : f a ^ 2 = 0 := by omega
      exact ⟨pow_eq_zero_iff two_ne_zero |>.mp h1, by omega⟩
    · rintro ⟨h1, h2⟩
      rw [h1, h2]
      simp

/-- **The pointwise zero equivalence, over `ℤ`.** -/
theorem evalInt_sumSquaresCode_eq_zero_iff (ps : List PolynomialCode) (x : List ℤ) :
    evalInt (sumSquaresCode ps) x = 0 ↔ ∀ p ∈ ps, evalInt p x = 0 := by
  rw [evalInt_sumSquaresCode]
  exact sum_map_sq_eq_zero_iff _ ps

/-- **The pointwise zero equivalence, over `ℕ`.** -/
theorem eval_sumSquaresCode_eq_zero_iff (ps : List PolynomialCode) (x : List ℕ) :
    eval (sumSquaresCode ps) x = 0 ↔ ∀ p ∈ ps, eval p x = 0 := by
  rw [eval_sumSquaresCode]
  exact sum_map_sq_eq_zero_iff _ ps

/-! ### Arity -/

/-- **The transformation introduces no variables**: its arity is bounded by the system's. -/
theorem arity_sumSquaresCode_le (ps : List PolynomialCode) :
    (sumSquaresCode ps).arity ≤ systemArity ps :=
  arity_foldr_add_le _ _ _ fun p hp =>
    (arity_mul_le p p).trans (by rw [max_self]; exact arity_le_systemArity hp)

end PolynomialCode

end Hilbert10


/- Source: Hilbert10.Degree, Hilbert10 v2.3.0, Apache-2.0. -/
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# A syntactic degree bound

Issue #57, first checkpoint. The quartic result is a statement about *degree*, so the wire format
needs a notion of degree that can be read off a code and checked by `decide`. `degreeBound` is
the largest exponent sum among the terms — conservative, because cancellation is ignored: the
code for `x − x` has bound `1` and denotes `0`. What makes it honest is `totalDegree_denote_le`:
the bound dominates the total degree of the polynomial the code denotes, so "degree at most
four" of a code is a fact about the polynomial, not only about its presentation.

## Main definitions

* `Hilbert10.PolynomialCode.monomialDegree`, `degreeBound`, `systemDegreeBound`

## Main results

* `Hilbert10.PolynomialCode.totalDegree_denote_le`
* `Hilbert10.PolynomialCode.degreeBound_le_iff`, the workhorse for every bound on a construction
-/

namespace Hilbert10

namespace PolynomialCode

/-- The degree of a monomial code: the sum of its exponents. -/
def monomialDegree (e : MonomialCode) : ℕ := e.sum

/-- A conservative syntactic degree bound: the largest monomial degree among the terms, `0` for
the zero code. Cancellation is ignored. -/
def degreeBound (p : PolynomialCode) : ℕ :=
  (p.terms.map fun t => monomialDegree t.2).foldr max 0

/-- The degree bound of a system: the largest bound of a member, `0` when empty. -/
def systemDegreeBound (ps : List PolynomialCode) : ℕ := (ps.map degreeBound).foldr max 0

/-- `foldr max 0` is bounded by `d` exactly when every entry is. -/
theorem foldr_max_le_iff (d : ℕ) : ∀ l : List ℕ, l.foldr max 0 ≤ d ↔ ∀ a ∈ l, a ≤ d
  | [] => by simp
  | a :: as => by
    simp only [List.foldr_cons, max_le_iff, List.forall_mem_cons, foldr_max_le_iff d as]

theorem degreeBound_le_iff (p : PolynomialCode) (d : ℕ) :
    p.degreeBound ≤ d ↔ ∀ t ∈ p.terms, monomialDegree t.2 ≤ d := by
  simp only [degreeBound, foldr_max_le_iff, List.forall_mem_map]

theorem monomialDegree_le_degreeBound {p : PolynomialCode} {t : ℤ × MonomialCode}
    (ht : t ∈ p.terms) : monomialDegree t.2 ≤ p.degreeBound :=
  (degreeBound_le_iff p _).mp le_rfl t ht

theorem systemDegreeBound_le_iff (ps : List PolynomialCode) (d : ℕ) :
    systemDegreeBound ps ≤ d ↔ ∀ p ∈ ps, p.degreeBound ≤ d := by
  simp only [systemDegreeBound, foldr_max_le_iff, List.forall_mem_map]

theorem systemArity_le_iff (ps : List PolynomialCode) (m : ℕ) :
    systemArity ps ≤ m ↔ ∀ p ∈ ps, p.arity ≤ m := by
  simp only [systemArity, foldr_max_le_iff, List.forall_mem_map]

theorem degreeBound_le_systemDegreeBound {p : PolynomialCode} {ps : List PolynomialCode}
    (h : p ∈ ps) : p.degreeBound ≤ systemDegreeBound ps :=
  (systemDegreeBound_le_iff ps _).mp le_rfl p h

@[simp] theorem degreeBound_mk_nil : degreeBound ⟨[]⟩ = 0 := rfl

@[simp] theorem systemDegreeBound_nil : systemDegreeBound [] = 0 := rfl

/-! ### The bound dominates the denotation's total degree -/

open MvPolynomial in
private theorem totalDegree_list_sum_le :
    ∀ l : List (MvPolynomial ℕ ℤ), l.sum.totalDegree ≤ (l.map totalDegree).foldr max 0
  | [] => by simp
  | a :: as => by
    simp only [List.sum_cons, List.map_cons, List.foldr_cons]
    exact (totalDegree_add _ _).trans (max_le_max le_rfl (totalDegree_list_sum_le as))

/-- **The syntactic bound dominates the total degree of the denoted polynomial.** -/
theorem totalDegree_denote_le (p : PolynomialCode) : p.denote.totalDegree ≤ p.degreeBound := by
  rw [denote]
  refine (totalDegree_list_sum_le _).trans ?_
  rw [foldr_max_le_iff]
  intro a ha
  simp only [List.map_map, List.mem_map, Function.comp_def] at ha
  obtain ⟨t, ht, rfl⟩ := ha
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, Nat.zero_add]
  exact (totalDegree_denoteMonomial_le t.2).trans (monomialDegree_le_degreeBound ht)

end PolynomialCode

end Hilbert10


/- Source: Hilbert10.Internal.CodeAlgebraDegree, Hilbert10 v2.3.0, Apache-2.0. -/
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# Degree bounds for the code algebra

Issue #57. How `degreeBound` behaves under the six internal operations, stated as bounds
(`≤`) because the bound itself is only an upper estimate. Everything is proved through
`degreeBound_le_iff`, term by term.

## Main results

* `Hilbert10.PolynomialCode.degreeBound_add_le`, `degreeBound_mul_le`, `degreeBound_npow_le`,
  `degreeBound_foldr_add_le` and friends
-/

namespace Hilbert10

namespace PolynomialCode

theorem sum_addExponents : ∀ e f : MonomialCode, (addExponents e f).sum = e.sum + f.sum
  | [], f => by simp [addExponents]
  | e :: es, [] => by simp [addExponents]
  | a :: es, b :: fs => by
    simp only [addExponents, List.sum_cons, sum_addExponents es fs]
    omega

@[simp] theorem degreeBound_zero : zero.degreeBound = 0 := rfl

@[simp] theorem degreeBound_const (c : ℤ) : (const c).degreeBound = 0 := rfl

@[simp] theorem degreeBound_one : one.degreeBound = 0 := rfl

@[simp] theorem degreeBound_X (i : ℕ) : (X i).degreeBound = 1 := by
  simp [degreeBound, X, monomialDegree]

theorem degreeBound_add_le (p q : PolynomialCode) :
    (add p q).degreeBound ≤ max p.degreeBound q.degreeBound := by
  rw [degreeBound_le_iff]
  intro t ht
  rcases List.mem_append.mp ht with h | h
  · exact le_max_of_le_left (monomialDegree_le_degreeBound h)
  · exact le_max_of_le_right (monomialDegree_le_degreeBound h)

theorem degreeBound_neg_le (p : PolynomialCode) : (neg p).degreeBound ≤ p.degreeBound := by
  rw [degreeBound_le_iff]
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact monomialDegree_le_degreeBound (t := s) hs

theorem degreeBound_mul_le (p q : PolynomialCode) :
    (mul p q).degreeBound ≤ p.degreeBound + q.degreeBound := by
  rw [degreeBound_le_iff]
  intro t ht
  simp only [mul, List.mem_flatMap, List.mem_map] at ht
  obtain ⟨a, ha, b, hb, rfl⟩ := ht
  simp only [monomialDegree, sum_addExponents]
  exact Nat.add_le_add (monomialDegree_le_degreeBound ha) (monomialDegree_le_degreeBound hb)

theorem degreeBound_npow_le (p : PolynomialCode) :
    ∀ n : ℕ, (npow p n).degreeBound ≤ n * p.degreeBound
  | 0 => by simp [npow]
  | n + 1 => by
    refine (degreeBound_mul_le p (npow p n)).trans ?_
    have := degreeBound_npow_le p n
    rw [Nat.succ_mul]
    omega

theorem degreeBound_foldr_add_le {α : Type*} (l : List α) (f : α → PolynomialCode) (m : ℕ)
    (h : ∀ a ∈ l, (f a).degreeBound ≤ m) : ((l.map f).foldr add zero).degreeBound ≤ m := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons, List.foldr_cons]
    refine (degreeBound_add_le _ _).trans (max_le (h a (by simp)) ?_)
    exact ih fun b hb => h b (by simp [hb])

end PolynomialCode

end Hilbert10


/- Source: Hilbert10.QuadraticGates, Hilbert10 v2.3.0, Apache-2.0. -/
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# Elementary gates of degree at most two, and the allocation contract

Issue #57, first checkpoint. Lowering a polynomial equation to a system of quadratic equations
introduces one auxiliary variable per intermediate value, and a *gate* is the single equation
that defines such a variable: a constant, a copy, a sum or a product of variables read earlier.
This module provides the four gate codes, their exact semantics at every assignment, their
degree bounds (`≤ 2`, the point of the exercise) and their arities, together with the contract
the compiler of the next checkpoint must respect.

## The allocation contract

A gate *writes* one variable, its `out`, and *reads* only variables with smaller index. A list of
gates is `WellOrdered n` when the gates write `n, n + 1, …` in order and each reads below what
it writes. That ordering is what makes soundness an induction (`exists_extension`): any
assignment of the first `n` variables extends, gate by gate, to one satisfying every gate — and
it rules out circular "definitions" of intermediate values, which an equation for every
auxiliary variable alone would not.

Gate constants are naturals. Signed coefficients are handled by the compiler keeping positive and
negative contributions in separate accumulators, so that a natural assignment extends to a
natural one (`exists_extension` is stated over any semiring, so it serves `ℕ` and `ℤ` alike).

## Main definitions

* `Hilbert10.PolynomialCode.constGate`, `eqGate`, `addGate`, `mulGate`
* `Hilbert10.Gate`, `Gate.code`, `Gate.Holds`, `Gate.Fresh`, `Hilbert10.WellOrdered`

## Main results

* `Hilbert10.PolynomialCode.evalInt_constGate_eq_zero_iff` and the other three, over `ℤ` and `ℕ`
* `Hilbert10.PolynomialCode.degreeBound_mulGate_le` and the other three
* `Hilbert10.Gate.evalInt_code_eq_zero_iff`, `Gate.eval_code_eq_zero_iff`,
  `Gate.degreeBound_code_le`, `Gate.arity_code_le`
* `Hilbert10.exists_extension`
* `Hilbert10.PolynomialCode.degreeBound_sumSquaresCode_le`
-/

namespace Hilbert10

namespace PolynomialCode

/-! ### The four gate codes -/

/-- `xᵢ − c`. -/
def constGate (i : ℕ) (c : ℤ) : PolynomialCode := add (X i) (const (-c))

/-- `xᵢ − xⱼ`. -/
def eqGate (i j : ℕ) : PolynomialCode := add (X i) (neg (X j))

/-- `xᵢ − (xⱼ + xₖ)`. -/
def addGate (i j k : ℕ) : PolynomialCode := add (X i) (neg (add (X j) (X k)))

/-- `xᵢ − xⱼ xₖ`. -/
def mulGate (i j k : ℕ) : PolynomialCode := add (X i) (neg (mul (X j) (X k)))

/-! ### Semantics over `ℤ` -/

theorem evalInt_constGate_eq_zero_iff (i : ℕ) (c : ℤ) (x : List ℤ) :
    evalInt (constGate i c) x = 0 ↔ x.getD i 0 = c := by
  simp only [constGate, evalInt_add, evalInt_X, evalInt_const, ← sub_eq_add_neg, sub_eq_zero]

theorem evalInt_eqGate_eq_zero_iff (i j : ℕ) (x : List ℤ) :
    evalInt (eqGate i j) x = 0 ↔ x.getD i 0 = x.getD j 0 := by
  simp only [eqGate, evalInt_add, evalInt_X, evalInt_neg, ← sub_eq_add_neg, sub_eq_zero]

theorem evalInt_addGate_eq_zero_iff (i j k : ℕ) (x : List ℤ) :
    evalInt (addGate i j k) x = 0 ↔ x.getD i 0 = x.getD j 0 + x.getD k 0 := by
  simp only [addGate, evalInt_add, evalInt_X, evalInt_neg, ← sub_eq_add_neg, sub_eq_zero]

theorem evalInt_mulGate_eq_zero_iff (i j k : ℕ) (x : List ℤ) :
    evalInt (mulGate i j k) x = 0 ↔ x.getD i 0 = x.getD j 0 * x.getD k 0 := by
  simp only [mulGate, evalInt_add, evalInt_X, evalInt_neg, evalInt_mul, ← sub_eq_add_neg,
    sub_eq_zero]

/-! ### Semantics over `ℕ`, through the cast bridge -/

theorem eval_constGate_eq_zero_iff (i : ℕ) (c : ℤ) (x : List ℕ) :
    eval (constGate i c) x = 0 ↔ ((x.getD i 0 : ℕ) : ℤ) = c := by
  rw [← evalInt_map_natCast, evalInt_constGate_eq_zero_iff, getD_map_natCast]

theorem eval_eqGate_eq_zero_iff (i j : ℕ) (x : List ℕ) :
    eval (eqGate i j) x = 0 ↔ x.getD i 0 = x.getD j 0 := by
  rw [← evalInt_map_natCast, evalInt_eqGate_eq_zero_iff, getD_map_natCast, getD_map_natCast]
  exact Nat.cast_inj

theorem eval_addGate_eq_zero_iff (i j k : ℕ) (x : List ℕ) :
    eval (addGate i j k) x = 0 ↔ x.getD i 0 = x.getD j 0 + x.getD k 0 := by
  rw [← evalInt_map_natCast, evalInt_addGate_eq_zero_iff, getD_map_natCast, getD_map_natCast,
    getD_map_natCast, ← Nat.cast_add]
  exact Nat.cast_inj

theorem eval_mulGate_eq_zero_iff (i j k : ℕ) (x : List ℕ) :
    eval (mulGate i j k) x = 0 ↔ x.getD i 0 = x.getD j 0 * x.getD k 0 := by
  rw [← evalInt_map_natCast, evalInt_mulGate_eq_zero_iff, getD_map_natCast, getD_map_natCast,
    getD_map_natCast, ← Nat.cast_mul]
  exact Nat.cast_inj

/-! ### Degree: the gates are quadratic -/

theorem degreeBound_constGate_le (i : ℕ) (c : ℤ) : (constGate i c).degreeBound ≤ 1 := by
  refine (degreeBound_add_le _ _).trans ?_
  simp

theorem degreeBound_eqGate_le (i j : ℕ) : (eqGate i j).degreeBound ≤ 1 := by
  refine (degreeBound_add_le _ _).trans (max_le (by simp) ?_)
  exact (degreeBound_neg_le _).trans (by simp)

theorem degreeBound_addGate_le (i j k : ℕ) : (addGate i j k).degreeBound ≤ 1 := by
  refine (degreeBound_add_le _ _).trans (max_le (by simp) ?_)
  refine (degreeBound_neg_le _).trans ((degreeBound_add_le _ _).trans ?_)
  simp

theorem degreeBound_mulGate_le (i j k : ℕ) : (mulGate i j k).degreeBound ≤ 2 := by
  refine (degreeBound_add_le _ _).trans (max_le (by simp) ?_)
  refine (degreeBound_neg_le _).trans ((degreeBound_mul_le _ _).trans ?_)
  simp

/-! ### Arity -/

theorem arity_constGate_le (i : ℕ) (c : ℤ) : (constGate i c).arity ≤ i + 1 := by
  simp [constGate]

theorem arity_eqGate_le (i j : ℕ) : (eqGate i j).arity ≤ max (i + 1) (j + 1) := by
  simp [eqGate]

theorem arity_addGate_le (i j k : ℕ) :
    (addGate i j k).arity ≤ max (i + 1) (max (j + 1) (k + 1)) := by
  simp [addGate]

theorem arity_mulGate_le (i j k : ℕ) :
    (mulGate i j k).arity ≤ max (i + 1) (max (j + 1) (k + 1)) := by
  simp only [mulGate, arity_add, arity_neg, arity_X]
  exact max_le_max le_rfl ((arity_mul_le _ _).trans (by simp))

/-! ### The sum of squares at most doubles the degree -/

/-- **`sumSquaresCode` at most doubles the degree bound.** With quadratic members this is the
quartic bound of #57. -/
theorem degreeBound_sumSquaresCode_le (ps : List PolynomialCode) :
    (sumSquaresCode ps).degreeBound ≤ 2 * systemDegreeBound ps := by
  refine degreeBound_foldr_add_le _ _ _ fun p hp => ?_
  refine (degreeBound_mul_le p p).trans ?_
  have := degreeBound_le_systemDegreeBound hp
  omega

end PolynomialCode

/-! ### Gates as data, and the allocation contract -/

/-- An elementary gate: the equation defining variable `out` from variables read earlier. The
constant of a `const` gate is a natural number; signs are the compiler's business. -/
inductive Gate
  /-- `x_out = c`. -/
  | const (out : ℕ) (c : ℕ)
  /-- `x_out = x_i`. -/
  | copy (out i : ℕ)
  /-- `x_out = x_i + x_j`. -/
  | add (out i j : ℕ)
  /-- `x_out = x_i * x_j`. -/
  | mul (out i j : ℕ)
  deriving DecidableEq, Repr

namespace Gate

/-- The variable a gate writes. -/
def out : Gate → ℕ
  | const o _ => o
  | copy o _ => o
  | add o _ _ => o
  | mul o _ _ => o

/-- The variables a gate reads. -/
def reads : Gate → List ℕ
  | const _ _ => []
  | copy _ i => [i]
  | add _ i j => [i, j]
  | mul _ i j => [i, j]

/-- The gate's equation, as a code. -/
def code : Gate → PolynomialCode
  | const o c => PolynomialCode.constGate o c
  | copy o i => PolynomialCode.eqGate o i
  | add o i j => PolynomialCode.addGate o i j
  | mul o i j => PolynomialCode.mulGate o i j

/-- The value a gate computes from an assignment, over any semiring. -/
def value {R : Type*} [Semiring R] : Gate → List R → R
  | const _ c, _ => c
  | copy _ i, x => x.getD i 0
  | add _ i j, x => x.getD i 0 + x.getD j 0
  | mul _ i j, x => x.getD i 0 * x.getD j 0

/-- The gate's equation holds at an assignment: the output variable carries the computed value. -/
def Holds {R : Type*} [Semiring R] (g : Gate) (x : List R) : Prop := x.getD g.out 0 = g.value x

instance {R : Type*} [Semiring R] [DecidableEq R] (g : Gate) (x : List R) :
    Decidable (g.Holds x) := by
  unfold Holds
  infer_instance

/-- The equation holds at a natural assignment exactly when it holds at its cast. -/
theorem holds_map_natCast (g : Gate) (x : List ℕ) :
    g.Holds (x.map (Nat.cast : ℕ → ℤ)) ↔ g.Holds x := by
  cases g <;> simp only [Holds, value, out, PolynomialCode.getD_map_natCast] <;> norm_cast

/-- **A gate's code vanishes exactly when its equation holds**, over `ℤ`. -/
theorem evalInt_code_eq_zero_iff (g : Gate) (x : List ℤ) :
    PolynomialCode.evalInt g.code x = 0 ↔ g.Holds x := by
  cases g <;> simp [code, Holds, out, value, PolynomialCode.evalInt_constGate_eq_zero_iff,
    PolynomialCode.evalInt_eqGate_eq_zero_iff, PolynomialCode.evalInt_addGate_eq_zero_iff,
    PolynomialCode.evalInt_mulGate_eq_zero_iff]

/-- **A gate's code vanishes exactly when its equation holds**, over `ℕ`. -/
theorem eval_code_eq_zero_iff (g : Gate) (x : List ℕ) :
    PolynomialCode.eval g.code x = 0 ↔ g.Holds x := by
  cases g <;> simp [code, Holds, out, value, PolynomialCode.eval_constGate_eq_zero_iff,
    PolynomialCode.eval_eqGate_eq_zero_iff, PolynomialCode.eval_addGate_eq_zero_iff,
    PolynomialCode.eval_mulGate_eq_zero_iff]

/-- **Every gate is quadratic.** -/
theorem degreeBound_code_le (g : Gate) : g.code.degreeBound ≤ 2 := by
  cases g with
  | const o c => exact (PolynomialCode.degreeBound_constGate_le o c).trans one_le_two
  | copy o i => exact (PolynomialCode.degreeBound_eqGate_le o i).trans one_le_two
  | add o i j => exact (PolynomialCode.degreeBound_addGate_le o i j).trans one_le_two
  | mul o i j => exact PolynomialCode.degreeBound_mulGate_le o i j

/-- A gate that reads below what it writes uses no variable beyond its output. -/
theorem arity_code_le (g : Gate) (h : ∀ r ∈ g.reads, r < g.out) : g.code.arity ≤ g.out + 1 := by
  cases g with
  | const o c => exact PolynomialCode.arity_constGate_le o c
  | copy o i =>
    have hi := h i (by simp [reads])
    exact (PolynomialCode.arity_eqGate_le o i).trans (by simp [out] at hi ⊢; omega)
  | add o i j =>
    have hi := h i (by simp [reads])
    have hj := h j (by simp [reads])
    exact (PolynomialCode.arity_addGate_le o i j).trans (by simp [out] at hi hj ⊢; omega)
  | mul o i j =>
    have hi := h i (by simp [reads])
    have hj := h j (by simp [reads])
    exact (PolynomialCode.arity_mulGate_le o i j).trans (by simp [out] at hi hj ⊢; omega)

/-- The value depends only on the variables read. -/
theorem value_congr {R : Type*} [Semiring R] (g : Gate) {x y : List R}
    (h : ∀ r ∈ g.reads, x.getD r 0 = y.getD r 0) : g.value x = g.value y := by
  cases g <;> simp_all [reads, value]

/-- **The allocation contract for one gate**: it writes `n` and reads only below `n`. -/
def Fresh (g : Gate) (n : ℕ) : Prop := g.out = n ∧ ∀ r ∈ g.reads, r < n

end Gate

/-- **The allocation contract for a gate list**: starting at `n`, the gates write `n, n + 1, …`
in order, each reading only original variables (below `n`) or the outputs of earlier gates. -/
def WellOrdered : ℕ → List Gate → Prop
  | _, [] => True
  | n, g :: gs => g.Fresh n ∧ WellOrdered (n + 1) gs

@[simp] theorem wellOrdered_nil (n : ℕ) : WellOrdered n [] := trivial

@[simp] theorem wellOrdered_cons (n : ℕ) (g : Gate) (gs : List Gate) :
    WellOrdered n (g :: gs) ↔ g.Fresh n ∧ WellOrdered (n + 1) gs := Iff.rfl

private theorem getD_of_take_eq {R : Type*} [Zero R] {y x : List R} {n : ℕ} (h : y.take n = x)
    {r : ℕ} (hr : r < n) : y.getD r 0 = x.getD r 0 := by
  rw [← h, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hr]

/-- **Soundness of the contract.** An assignment of the first `n` variables extends, along a
well-ordered gate list, to an assignment of `n + gs.length` variables satisfying every gate; the
original variables are preserved as a prefix. Over any semiring, so natural inputs get natural
auxiliary values. -/
theorem exists_extension {R : Type*} [Semiring R] :
    ∀ (gs : List Gate) (n : ℕ), WellOrdered n gs → ∀ x : List R, x.length = n →
      ∃ y : List R, y.length = n + gs.length ∧ y.take n = x ∧ ∀ g ∈ gs, g.Holds y
  | [], n, _, x, hx => ⟨x, by simp [hx], by rw [← hx, List.take_length], by simp⟩
  | g :: gs, n, ⟨⟨hout, hreads⟩, hwo⟩, x, hx => by
    obtain ⟨y, hy, hyx, hgs⟩ :=
      exists_extension gs (n + 1) hwo (x ++ [g.value x]) (by simp [hx])
    have hsplit : y = (x ++ [g.value x]) ++ y.drop (n + 1) := by
      rw [← hyx, List.take_append_drop]
    have hyn : y.take n = x := by
      rw [hsplit, List.append_assoc, List.take_left' hx]
    refine ⟨y, by simp [hy]; omega, hyn, ?_⟩
    rw [List.forall_mem_cons]
    refine ⟨?_, hgs⟩
    have hval : g.value y = g.value x :=
      g.value_congr fun r hr => getD_of_take_eq hyn (hreads r hr)
    have hread : y.getD n 0 = g.value x := by
      rw [hsplit, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [hx]), ← hx,
        List.getElem?_concat_length, Option.getD_some]
    change y.getD g.out 0 = g.value y
    rw [hout, hread, hval]

/-! ### Regression examples -/

/-- The degree bounds are computable, and exact on the gates. -/
example : (PolynomialCode.mulGate 2 0 1).degreeBound = 2 := by decide
example : (PolynomialCode.addGate 2 0 1).degreeBound = 1 := by decide
example : (PolynomialCode.constGate 0 7).degreeBound = 1 := by decide
example : (PolynomialCode.eqGate 0 1).degreeBound = 1 := by decide

/-- `x₂ = x₀ · x₁`, then `x₃ = x₂ + x₀`: two original variables, two gates, well ordered. -/
example : WellOrdered 2 [Gate.mul 2 0 1, Gate.add 3 2 0] := by
  simp [WellOrdered, Gate.Fresh, Gate.reads, Gate.out]

/-- A gate that reads what it writes is not fresh: circular definitions are excluded. -/
example : ¬ (Gate.copy 3 3).Fresh 3 := by simp [Gate.Fresh, Gate.reads, Gate.out]

/-- A gate that reads a *later* variable is not fresh either. -/
example : ¬ WellOrdered 2 [Gate.add 2 0 3, Gate.const 3 1] := by
  simp [WellOrdered, Gate.Fresh, Gate.reads, Gate.out]

/-- The extension theorem, instantiated: `[3, 4]` extends to `[3, 4, 12, 15]`. -/
example : ∀ g ∈ [Gate.mul 2 0 1, Gate.add 3 2 0], g.Holds ([3, 4, 12, 15] : List ℕ) := by
  decide

end Hilbert10


/- Source: Hilbert10.Internal.SumSquaresComp, Hilbert10 v2.3.0, Apache-2.0. -/
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# The sum-of-squares transformation is primitive recursive

Issue #53, third layer. `sumSquaresCode` is a `map` of `mul` under a `foldr` of `add`, so its
computability is exactly mathlib's `Primrec.list_map` and `Primrec.list_foldr` applied to the
operation-level lemmas of `Internal/CodeAlgebraComp.lean`. Nothing new about codes is proved.

## Main results

* `Hilbert10.PolynomialCode.primrec_sumSquaresCode`
* `Hilbert10.PolynomialCode.computable_sumSquaresCode`
-/

namespace Hilbert10

namespace PolynomialCode

theorem primrec_sumSquaresCode : Primrec sumSquaresCode := by
  refine (Primrec.list_foldr (f := fun ps : List PolynomialCode => ps.map fun p => mul p p)
    (g := fun _ => zero) (h := fun _ q => add q.1 q.2) ?_ (Primrec.const zero) ?_).of_eq
    fun ps => rfl
  · exact Primrec.list_map (f := fun ps => ps) (g := fun _ p => mul p p) Primrec.id
      (Primrec₂.comp primrec₂_mul Primrec.snd Primrec.snd)
  · exact Primrec₂.comp primrec₂_add (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)

theorem computable_sumSquaresCode : Computable sumSquaresCode := primrec_sumSquaresCode.to_comp

end PolynomialCode

end Hilbert10


/- Source: Hilbert10.Systems, Hilbert10 v2.3.0, Apache-2.0. -/
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# Finite systems of equations with a shared assignment

Issue #53. A *system* is a list of codes, and it is solvable when **one** assignment is a root of
every member. This module defines the two system predicates, proves each equivalent to single
solvability of the sum-of-squares code with *the same witness*, and packages the equivalences
as many-one reductions in both directions. Systems and single equations therefore have the same
many-one degree, over `ℕ` and over `ℤ`.

## One witness for the whole system

The contract is the shared assignment. `x₀ = 0` and `x₀ = 1` are each solvable, but their system
is not, and that pair is the regression test that distinguishes the definition below from "a
witness for each equation". Nothing here relabels variables between equations; a consumer that
needs fresh variables (#57) supplies its own allocation.

## Main definitions

* `Hilbert10.SystemNatSolvable`, `Hilbert10.SystemIntSolvable`

## Main results

* `Hilbert10.systemNatSolvable_iff_natSolvable_sumSquaresCode`,
  `Hilbert10.systemIntSolvable_iff_intSolvable_sumSquaresCode`
* `Hilbert10.natSolvable_manyOneEquiv_systemNatSolvable`,
  `Hilbert10.intSolvable_manyOneEquiv_systemIntSolvable`
-/

namespace Hilbert10

open PolynomialCode

/-- **A system with a natural root**: one assignment at which every member vanishes. -/
def SystemNatSolvable (ps : List PolynomialCode) : Prop :=
  ∃ x : List ℕ, ∀ p ∈ ps, p.eval x = 0

/-- **A system with an integer root**: one assignment at which every member vanishes. -/
def SystemIntSolvable (ps : List PolynomialCode) : Prop :=
  ∃ x : List ℤ, ∀ p ∈ ps, p.evalInt x = 0

theorem systemNatSolvable_iff (ps : List PolynomialCode) :
    SystemNatSolvable ps ↔ ∃ x : List ℕ, ∀ p ∈ ps, p.eval x = 0 := Iff.rfl

theorem systemIntSolvable_iff (ps : List PolynomialCode) :
    SystemIntSolvable ps ↔ ∃ x : List ℤ, ∀ p ∈ ps, p.evalInt x = 0 := Iff.rfl

/-! ### Systems reduce to single equations, with the same witness -/

/-- **A system has a natural root exactly when its sum of squares does**, at the same
assignment. -/
theorem systemNatSolvable_iff_natSolvable_sumSquaresCode (ps : List PolynomialCode) :
    SystemNatSolvable ps ↔ NatSolvable (sumSquaresCode ps) :=
  exists_congr fun x => (eval_sumSquaresCode_eq_zero_iff ps x).symm

/-- **A system has an integer root exactly when its sum of squares does**, at the same
assignment. -/
theorem systemIntSolvable_iff_intSolvable_sumSquaresCode (ps : List PolynomialCode) :
    SystemIntSolvable ps ↔ IntSolvable (sumSquaresCode ps) :=
  exists_congr fun x => (evalInt_sumSquaresCode_eq_zero_iff ps x).symm

/-! ### Single equations are one-element systems -/

theorem natSolvable_iff_systemNatSolvable_singleton (p : PolynomialCode) :
    NatSolvable p ↔ SystemNatSolvable [p] :=
  exists_congr fun _ => by simp

theorem intSolvable_iff_systemIntSolvable_singleton (p : PolynomialCode) :
    IntSolvable p ↔ SystemIntSolvable [p] :=
  exists_congr fun _ => by simp

/-! ### The reductions -/

private theorem computable_singleton : Computable fun p : PolynomialCode => [p] :=
  (Primrec₂.comp Primrec.list_cons Primrec.id (Primrec.const [])).to_comp

theorem systemNatSolvable_manyOneReducible_natSolvable : SystemNatSolvable ≤₀ NatSolvable :=
  ⟨sumSquaresCode, computable_sumSquaresCode, systemNatSolvable_iff_natSolvable_sumSquaresCode⟩

theorem natSolvable_manyOneReducible_systemNatSolvable : NatSolvable ≤₀ SystemNatSolvable :=
  ⟨fun p => [p], computable_singleton, natSolvable_iff_systemNatSolvable_singleton⟩

theorem systemIntSolvable_manyOneReducible_intSolvable : SystemIntSolvable ≤₀ IntSolvable :=
  ⟨sumSquaresCode, computable_sumSquaresCode, systemIntSolvable_iff_intSolvable_sumSquaresCode⟩

theorem intSolvable_manyOneReducible_systemIntSolvable : IntSolvable ≤₀ SystemIntSolvable :=
  ⟨fun p => [p], computable_singleton, intSolvable_iff_systemIntSolvable_singleton⟩

/-- **Systems and single equations have the same many-one degree over `ℕ`.** -/
theorem natSolvable_manyOneEquiv_systemNatSolvable : ManyOneEquiv NatSolvable SystemNatSolvable :=
  ⟨natSolvable_manyOneReducible_systemNatSolvable, systemNatSolvable_manyOneReducible_natSolvable⟩

/-- **Systems and single equations have the same many-one degree over `ℤ`.** -/
theorem intSolvable_manyOneEquiv_systemIntSolvable : ManyOneEquiv IntSolvable SystemIntSolvable :=
  ⟨intSolvable_manyOneReducible_systemIntSolvable, systemIntSolvable_manyOneReducible_intSolvable⟩

/-! ### Regression examples

The specification tests for the shared-assignment contract. -/

/-- The empty system is satisfied by the empty assignment. -/
example : SystemNatSolvable [] := ⟨[], by simp⟩
example : SystemIntSolvable [] := ⟨[], by simp⟩

/-- `x₀ = 0`. -/
private def xEq0 : PolynomialCode := ⟨[(1, [1])]⟩
/-- `x₀ - 1 = 0`. -/
private def xEq1 : PolynomialCode := ⟨[(1, [1]), (-1, [])]⟩

example : NatSolvable xEq0 := ⟨[0], by decide⟩
example : NatSolvable xEq1 := ⟨[1], by decide⟩

/-- **The contradictory pair.** Each equation is solvable; the system is not, because one
assignment must serve both. This is the test that separates "one witness for the whole system"
from "a witness for each equation". -/
example : ¬ SystemNatSolvable [xEq0, xEq1] := by
  rintro ⟨x, hx⟩
  have h0 := hx xEq0 (by simp)
  have h1 := hx xEq1 (by simp)
  cases x with
  | nil => simp [xEq1, eval, evalMonomial] at h1
  | cons a as =>
    simp [xEq0, xEq1, eval, evalMonomial] at h0 h1
    omega

example : ¬ SystemIntSolvable [xEq0, xEq1] := by
  rintro ⟨x, hx⟩
  have h0 := hx xEq0 (by simp)
  have h1 := hx xEq1 (by simp)
  cases x with
  | nil => simp [xEq1, evalInt, evalMonomialInt] at h1
  | cons a as =>
    simp [xEq0, xEq1, evalInt, evalMonomialInt] at h0 h1
    omega

/-- A satisfiable pair genuinely sharing variables: `x₀ + x₁ = 5` and `x₀ - x₁ = 1`, solved by
`[3, 2]`. -/
example : SystemNatSolvable
    [⟨[(1, [1]), (1, [0, 1]), (-5, [])]⟩, ⟨[(1, [1]), (-1, [0, 1]), (-1, [])]⟩] :=
  ⟨[3, 2], by decide⟩

/-- Constant equations: `0 = 0` is satisfied by anything, `1 = 0` by nothing. -/
example : SystemNatSolvable [const 0, const 0] := ⟨[], by simp⟩
example : ¬ SystemNatSolvable [const 1] := by
  rintro ⟨x, hx⟩
  simpa using hx (const 1) (by simp)

/-- Ragged exponent vectors: arities `1` and `3` in one system, one assignment for both. -/
example : SystemNatSolvable [⟨[(1, [1])]⟩, ⟨[(1, [0, 0, 1]), (-1, [])]⟩] :=
  ⟨[0, 0, 1], by decide⟩
example : systemArity [⟨[(1, [1])]⟩, ⟨[(1, [0, 0, 1]), (-1, [])]⟩] = 3 := by decide

end Hilbert10


/- Source: Hilbert10.QuadraticLowering, Hilbert10 v2.3.0, Apache-2.0. -/
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# Quadratic lowering: compiling expressions to well-ordered gate lists

Issue #57, second checkpoint: the transformation from one polynomial equation to a system of
equations of degree at most two. Its first stage is **one monomial**; the second compiles the
**whole polynomial** into two accumulators; the third turns the gates into equations, appends
the terminal equality, and proves root equivalence over `ℕ` and `ℤ` with the bounds.
Compiling an exponent vector returns a gate list, the wire carrying the monomial's value, and
the next unused wire. The contract has three parts, and each later stage (powers, weighted
terms, the two accumulators) composes them without reopening the allocation argument:

* **well-ordering** — the gates are `WellOrdered next`, so `exists_extension` (completeness)
  applies;
* **bookkeeping** — the next unused wire is exactly `next + gates.length`, and the output wire
  lies below it;
* **soundness** — *any* assignment satisfying the gates reads the intended value from the output
  wire. This is the direction well-ordering exists for: existence of a satisfying extension says
  nothing about what a satisfying assignment must contain.

The empty exponent vector compiles to a wire holding `1`; zero exponents allocate nothing.

## Values, generically

`monomialValueFrom j e x` is the monomial's value read off an assignment by `getD`, over any
semiring, so one soundness proof serves `ℤ` and `ℕ`; `evalMonomialInt_eq_monomialValue` and
`evalMonomial_eq_monomialValue` connect it to the wire format's two evaluators.

## Main definitions

* `Hilbert10.Compiled`, `Hilbert10.mulPow`, `Hilbert10.compileMonomial`
* `Hilbert10.CompiledPoly`, `Hilbert10.compileTerm`, `Hilbert10.compilePoly`

## Main results

* `Hilbert10.compileMonomial_wellOrdered`, `compileMonomial_next`, `compileMonomial_out_lt`
* `Hilbert10.compileMonomial_sound`, and its `ℤ` and `ℕ` readings
* `Hilbert10.compilePoly_wellOrdered`, `compilePoly_length` (exact: `1 + Σ (exponent sum + 4)`),
  `compilePoly_next`, `compilePoly_pos_lt`, `compilePoly_neg_lt`
* `Hilbert10.compilePoly_sound` (`evalInt p y = y[pos] − y[neg]` at any satisfying `y`) and
  `compilePoly_sound_nat`
* `Hilbert10.quadraticSystem`, `gateCount`; `quadraticSystem_eval_zero_iff` (pointwise semantics),
  `evalInt_eq_zero_iff_exists_aux` (extension correctness), and the two root equivalences
  `intSolvable_iff_systemIntSolvable_quadraticSystem`,
  `natSolvable_iff_systemNatSolvable_quadraticSystem`
* `Hilbert10.systemDegreeBound_quadraticSystem_le` (`≤ 2`), `systemArity_quadraticSystem_le`
  (`≤ p.arity + gateCount p`), `quadraticSystem_length` (`gateCount p + 1`)
-/

namespace Hilbert10

open PolynomialCode

/-! ### Monomial values, read by `getD` -/

/-- The value of the exponent vector `e`, its first entry referring to variable `j`, at an
assignment, over any semiring. Variables past the end of the assignment read as `0`. -/
def monomialValueFrom {R : Type*} [Semiring R] : ℕ → MonomialCode → List R → R
  | _, [], _ => 1
  | j, a :: es, x => x.getD j 0 ^ a * monomialValueFrom (j + 1) es x

theorem evalMonomialInt_drop_eq (x : List ℤ) :
    ∀ (e : MonomialCode) (i : ℕ), evalMonomialInt e (x.drop i) = monomialValueFrom i e x := by
  intro e
  induction e with
  | nil => intro i; simp [monomialValueFrom]
  | cons a es ih =>
    intro i
    by_cases hi : i < x.length
    · rw [List.drop_eq_getElem_cons hi]
      simp only [evalMonomialInt, monomialValueFrom, List.getD_eq_getElem _ _ hi, ih]
    · have hnil : x.drop i = [] := List.drop_eq_nil_of_le (le_of_not_gt hi)
      have hnil' : x.drop (i + 1) = [] := List.drop_eq_nil_of_le (by omega)
      have h0 : x.getD i 0 = 0 := List.getD_eq_default _ _ (le_of_not_gt hi)
      rw [hnil]
      simp only [evalMonomialInt, monomialValueFrom, h0, ← ih (i + 1), hnil']

/-- The wire format's integer monomial evaluator, in `getD` form. -/
theorem evalMonomialInt_eq_monomialValue (e : MonomialCode) (x : List ℤ) :
    evalMonomialInt e x = monomialValueFrom 0 e x := by
  simpa using evalMonomialInt_drop_eq x e 0

theorem monomialValueFrom_map_natCast (x : List ℕ) :
    ∀ (e : MonomialCode) (j : ℕ),
      monomialValueFrom j e (x.map (Nat.cast : ℕ → ℤ)) = ((monomialValueFrom j e x : ℕ) : ℤ) := by
  intro e
  induction e with
  | nil => intro j; simp [monomialValueFrom]
  | cons a es ih =>
    intro j
    simp only [monomialValueFrom, getD_map_natCast, ih, Nat.cast_mul, Nat.cast_pow]

/-- The wire format's natural monomial evaluator, in `getD` form. -/
theorem evalMonomial_eq_monomialValue (e : MonomialCode) (x : List ℕ) :
    evalMonomial e x = ((monomialValueFrom 0 e x : ℕ) : ℤ) := by
  rw [← evalMonomialInt_map_natCast, evalMonomialInt_eq_monomialValue,
    monomialValueFrom_map_natCast]

/-! ### Well-ordering composes along `++` -/

theorem wellOrdered_append (n : ℕ) :
    ∀ gs₁ gs₂ : List Gate,
      WellOrdered n (gs₁ ++ gs₂) ↔ WellOrdered n gs₁ ∧ WellOrdered (n + gs₁.length) gs₂
  | [], gs₂ => by simp
  | g :: gs₁, gs₂ => by
    simp only [List.cons_append, wellOrdered_cons, List.length_cons, wellOrdered_append (n + 1)
      gs₁ gs₂, and_assoc]
    rw [Nat.add_assoc, Nat.add_comm gs₁.length 1]

/-! ### The output of a compilation -/

/-- A compiled expression: its defining gates, the wire carrying its value, and the next
unused wire. -/
structure Compiled where
  /-- The defining gates, well ordered from the wire the compilation started at. -/
  gates : List Gate
  /-- The wire carrying the expression's value. -/
  out : ℕ
  /-- The next unused wire. -/
  next : ℕ
  deriving DecidableEq, Repr

/-! ### Repeated multiplication by one variable -/

/-- `a` multiplications of wire `acc` by variable `j`, allocating from `next`. -/
def mulPow (j acc next : ℕ) : ℕ → Compiled
  | 0 => ⟨[], acc, next⟩
  | a + 1 =>
    let c := mulPow j next (next + 1) a
    ⟨Gate.mul next acc j :: c.gates, c.out, c.next⟩

theorem mulPow_next (j acc next : ℕ) : ∀ a : ℕ, (mulPow j acc next a).next = next + a
  | 0 => rfl
  | a + 1 => by
    simp only [mulPow, mulPow_next j next (next + 1) a]
    omega

theorem mulPow_length (j acc next : ℕ) : ∀ a : ℕ, (mulPow j acc next a).gates.length = a
  | 0 => rfl
  | a + 1 => by simp [mulPow, mulPow_length j next (next + 1) a]

theorem mulPow_out_lt (j : ℕ) :
    ∀ (a acc next : ℕ), acc < next → (mulPow j acc next a).out < next + a
  | 0, acc, next, h => by simpa [mulPow] using h
  | a + 1, acc, next, _ => by
    have := mulPow_out_lt j a next (next + 1) (Nat.lt_succ_self next)
    simp only [mulPow]
    omega

theorem mulPow_wellOrdered (j : ℕ) :
    ∀ (a acc next : ℕ), acc < next → j < next → WellOrdered next (mulPow j acc next a).gates
  | 0, _, _, _, _ => trivial
  | a + 1, acc, next, hacc, hj => by
    refine ⟨⟨rfl, ?_⟩, mulPow_wellOrdered j a next (next + 1) (Nat.lt_succ_self next) (by omega)⟩
    intro r hr
    simp only [Gate.reads, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> assumption

/-- **Soundness**: any assignment satisfying the gates reads `acc · xⱼᵃ` from the output. -/
theorem mulPow_sound {R : Type*} [Semiring R] (j : ℕ) (x : List R) :
    ∀ (a acc next : ℕ), (∀ g ∈ (mulPow j acc next a).gates, g.Holds x) →
      x.getD (mulPow j acc next a).out 0 = x.getD acc 0 * x.getD j 0 ^ a
  | 0, acc, next, _ => by simp [mulPow]
  | a + 1, acc, next, h => by
    simp only [mulPow, List.forall_mem_cons] at h
    obtain ⟨hg, hrest⟩ := h
    have ih := mulPow_sound j x a next (next + 1) hrest
    simp only [Gate.Holds, Gate.out, Gate.value] at hg
    simp only [mulPow, ih, hg, pow_succ', mul_assoc]

/-! ### One monomial -/

/-- Multiply wire `acc` by the monomial `es` whose first entry refers to variable `j`,
allocating from `next`. -/
def compileMonomialFrom (acc next : ℕ) : ℕ → MonomialCode → Compiled
  | _, [] => ⟨[], acc, next⟩
  | j, a :: es =>
    let c₁ := mulPow j acc next a
    let c₂ := compileMonomialFrom c₁.out c₁.next (j + 1) es
    ⟨c₁.gates ++ c₂.gates, c₂.out, c₂.next⟩

theorem compileMonomialFrom_next :
    ∀ (es : MonomialCode) (acc next j : ℕ),
      (compileMonomialFrom acc next j es).next = next + es.sum
  | [], _, _, _ => by simp [compileMonomialFrom]
  | a :: es, acc, next, j => by
    simp only [compileMonomialFrom, compileMonomialFrom_next es, mulPow_next, List.sum_cons]
    omega

theorem compileMonomialFrom_length :
    ∀ (es : MonomialCode) (acc next j : ℕ),
      (compileMonomialFrom acc next j es).gates.length = es.sum
  | [], _, _, _ => rfl
  | a :: es, acc, next, j => by
    simp [compileMonomialFrom, mulPow_length, compileMonomialFrom_length es]

theorem compileMonomialFrom_out_lt :
    ∀ (es : MonomialCode) (acc next j : ℕ), acc < next →
      (compileMonomialFrom acc next j es).out < next + es.sum
  | [], acc, next, j, h => by simpa [compileMonomialFrom] using h
  | a :: es, acc, next, j, h => by
    have h1 := mulPow_out_lt j a acc next h
    have h2 := compileMonomialFrom_out_lt es (mulPow j acc next a).out (mulPow j acc next a).next
      (j + 1) (by rw [mulPow_next]; exact h1)
    simp only [compileMonomialFrom, mulPow_next, List.sum_cons] at h2 ⊢
    omega

theorem compileMonomialFrom_wellOrdered :
    ∀ (es : MonomialCode) (acc next j : ℕ), acc < next → j + es.length ≤ next →
      WellOrdered next (compileMonomialFrom acc next j es).gates
  | [], _, _, _, _, _ => trivial
  | a :: es, acc, next, j, hacc, hj => by
    simp only [List.length_cons] at hj
    have h1 := mulPow_wellOrdered j a acc next hacc (by omega)
    have h2 := compileMonomialFrom_wellOrdered es (mulPow j acc next a).out
      (mulPow j acc next a).next (j + 1)
      (by rw [mulPow_next]; exact mulPow_out_lt j a acc next hacc) (by rw [mulPow_next]; omega)
    simp only [compileMonomialFrom, wellOrdered_append, mulPow_length]
    simp only [mulPow_next] at h2 ⊢
    exact ⟨h1, h2⟩

/-- **Soundness**: any assignment satisfying the gates reads `acc · (the monomial)` from the
output. -/
theorem compileMonomialFrom_sound {R : Type*} [Semiring R] (x : List R) :
    ∀ (es : MonomialCode) (acc next j : ℕ),
      (∀ g ∈ (compileMonomialFrom acc next j es).gates, g.Holds x) →
        x.getD (compileMonomialFrom acc next j es).out 0 = x.getD acc 0 * monomialValueFrom j es x
  | [], acc, next, j, _ => by simp [compileMonomialFrom, monomialValueFrom]
  | a :: es, acc, next, j, h => by
    simp only [compileMonomialFrom, List.forall_mem_append] at h
    obtain ⟨h1, h2⟩ := h
    have s1 := mulPow_sound j x a acc next h1
    have s2 := compileMonomialFrom_sound x es _ _ (j + 1) h2
    simp only [compileMonomialFrom, monomialValueFrom, s2, s1, mul_assoc]

/-- Compile one monomial, allocating from `next`: a wire holding `1`, then the multiplications.
The empty exponent vector compiles to that single wire. -/
def compileMonomial (e : MonomialCode) (next : ℕ) : Compiled :=
  let c := compileMonomialFrom next (next + 1) 0 e
  ⟨Gate.const next 1 :: c.gates, c.out, c.next⟩

theorem compileMonomial_next (e : MonomialCode) (n : ℕ) :
    (compileMonomial e n).next = n + 1 + e.sum := by
  simp [compileMonomial, compileMonomialFrom_next]

theorem compileMonomial_length (e : MonomialCode) (n : ℕ) :
    (compileMonomial e n).gates.length = 1 + e.sum := by
  simp [compileMonomial, compileMonomialFrom_length]
  omega

theorem compileMonomial_out_lt (e : MonomialCode) (n : ℕ) :
    (compileMonomial e n).out < (compileMonomial e n).next := by
  have := compileMonomialFrom_out_lt e n (n + 1) 0 (Nat.lt_succ_self n)
  simp only [compileMonomial, compileMonomialFrom_next]
  omega

/-- **Well-ordering**, given that the monomial reads only original variables below `n`. -/
theorem compileMonomial_wellOrdered (e : MonomialCode) (n : ℕ) (h : e.length ≤ n) :
    WellOrdered n (compileMonomial e n).gates :=
  ⟨⟨rfl, by simp [Gate.reads]⟩,
    compileMonomialFrom_wellOrdered e n (n + 1) 0 (Nat.lt_succ_self n) (by omega)⟩

/-- **Soundness**: any assignment satisfying the gates reads the monomial's value from the
output wire, over any semiring. -/
theorem compileMonomial_sound {R : Type*} [Semiring R] (e : MonomialCode) (n : ℕ) (x : List R)
    (h : ∀ g ∈ (compileMonomial e n).gates, g.Holds x) :
    x.getD (compileMonomial e n).out 0 = monomialValueFrom 0 e x := by
  simp only [compileMonomial, List.forall_mem_cons] at h
  obtain ⟨h0, hrest⟩ := h
  simp only [Gate.Holds, Gate.out, Gate.value, Nat.cast_one] at h0
  simp only [compileMonomial, compileMonomialFrom_sound x e n (n + 1) 0 hrest, h0, one_mul]

/-- The `ℤ` reading: the output wire carries `evalMonomialInt e x`. -/
theorem compileMonomial_sound_int (e : MonomialCode) (n : ℕ) (x : List ℤ)
    (h : ∀ g ∈ (compileMonomial e n).gates, g.Holds x) :
    x.getD (compileMonomial e n).out 0 = evalMonomialInt e x := by
  rw [compileMonomial_sound e n x h, evalMonomialInt_eq_monomialValue]

/-- The `ℕ` reading: the output wire carries `evalMonomial e x`, up to the cast. -/
theorem compileMonomial_sound_nat (e : MonomialCode) (n : ℕ) (x : List ℕ)
    (h : ∀ g ∈ (compileMonomial e n).gates, g.Holds x) :
    ((x.getD (compileMonomial e n).out 0 : ℕ) : ℤ) = evalMonomial e x := by
  rw [compileMonomial_sound e n x h, evalMonomial_eq_monomialValue]

/-! ### The whole polynomial, with two accumulators

A polynomial is compiled in one pass. The state carries the gates so far, the next unused wire,
and the two accumulator wires: `pos` collects the terms with nonnegative coefficient, `neg` those
with negative coefficient, each as a sum of `|c| · monomial`. Both start at one wire holding
`0`. Zero coefficients are processed like any other; skipping them would be an optimisation
with no role in correctness.

The invariant `evalInt p y = y[pos] − y[neg]` is stated over `ℤ` for *any* satisfying
assignment, and the natural reading is obtained through the cast — never through truncated
subtraction. -/

/-- A partially or fully compiled polynomial. -/
structure CompiledPoly where
  /-- The defining gates so far. -/
  gates : List Gate
  /-- The wire accumulating the terms with nonnegative coefficient. -/
  pos : ℕ
  /-- The wire accumulating the terms with negative coefficient. -/
  neg : ℕ
  /-- The next unused wire. -/
  next : ℕ
  deriving DecidableEq, Repr

/-- The gates one term adds: its monomial, a constant holding `|c|`, their product, and the
addition into the accumulator its sign selects. -/
def termGates (s : CompiledPoly) (t : ℤ × MonomialCode) : List Gate :=
  let cm := compileMonomial t.2 s.next
  cm.gates ++ [Gate.const cm.next t.1.natAbs, Gate.mul (cm.next + 1) cm.out cm.next,
    Gate.add (cm.next + 2) (if 0 ≤ t.1 then s.pos else s.neg) (cm.next + 1)]

/-- Compile one term onto the state. -/
def compileTerm (s : CompiledPoly) (t : ℤ × MonomialCode) : CompiledPoly :=
  let cm := compileMonomial t.2 s.next
  { gates := s.gates ++ termGates s t
    pos := if 0 ≤ t.1 then cm.next + 2 else s.pos
    neg := if 0 ≤ t.1 then s.neg else cm.next + 2
    next := cm.next + 3 }

/-- Compile a term list onto the state, left to right. -/
def compileTerms (s : CompiledPoly) : List (ℤ × MonomialCode) → CompiledPoly
  | [] => s
  | t :: ts => compileTerms (compileTerm s t) ts

/-- **Compile a polynomial**, allocating from `next`: a zero wire that both accumulators start
from, then the terms in order. -/
def compilePoly (p : PolynomialCode) (next : ℕ) : CompiledPoly :=
  compileTerms ⟨[Gate.const next 0], next, next, next + 1⟩ p.terms

theorem termGates_length (s : CompiledPoly) (t : ℤ × MonomialCode) :
    (termGates s t).length = t.2.sum + 4 := by
  simp only [termGates, List.length_append, compileMonomial_length, List.length_cons,
    List.length_nil]
  omega

theorem termGates_wellOrdered (s : CompiledPoly) (t : ℤ × MonomialCode) (hpos : s.pos < s.next)
    (hneg : s.neg < s.next) (he : t.2.length ≤ s.next) : WellOrdered s.next (termGates s t) := by
  have hout := compileMonomial_out_lt t.2 s.next
  have hnext := compileMonomial_next t.2 s.next
  simp only [termGates, wellOrdered_append, compileMonomial_length]
  refine ⟨compileMonomial_wellOrdered _ _ he, ?_⟩
  by_cases hc : 0 ≤ t.1 <;>
    simp only [hc, if_true, if_false, WellOrdered, Gate.Fresh, Gate.out, Gate.reads,
      List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true] <;>
    omega

/-- **Soundness of one term**: any assignment satisfying its gates moves `pos − neg` by exactly
`c · monomial`. -/
theorem termGates_sound (s : CompiledPoly) (t : ℤ × MonomialCode) (y : List ℤ)
    (h : ∀ g ∈ termGates s t, g.Holds y) :
    y.getD (compileTerm s t).pos 0 - y.getD (compileTerm s t).neg 0 =
      y.getD s.pos 0 - y.getD s.neg 0 + t.1 * evalMonomialInt t.2 y := by
  simp only [termGates, List.forall_mem_append, List.forall_mem_cons, List.mem_nil_iff,
    false_implies, implies_true, and_true] at h
  obtain ⟨hm, hk, hmul, hadd⟩ := h
  have hout := compileMonomial_sound_int t.2 s.next y hm
  simp only [Gate.Holds, Gate.out, Gate.value] at hk hmul hadd
  simp only [compileTerm]
  rw [Int.natCast_natAbs] at hk
  by_cases hc : 0 ≤ t.1
  · simp only [hc, if_true] at hadd ⊢
    rw [hadd, hmul, hout, hk, abs_of_nonneg hc]
    ring
  · simp only [hc, if_false] at hadd ⊢
    rw [hadd, hmul, hout, hk, abs_of_neg (lt_of_not_ge hc)]
    ring

theorem mem_gates_compileTerms (s : CompiledPoly) :
    ∀ ts, ∀ g ∈ s.gates, g ∈ (compileTerms s ts).gates
  | [], _, hg => hg
  | t :: ts, g, hg =>
    mem_gates_compileTerms (compileTerm s t) ts g (by simp [compileTerm, hg])

/-- The invariant carried along the fold: well ordered from `n`, exact bookkeeping, and both
accumulators already allocated. -/
structure CompiledPoly.Inv (n : ℕ) (s : CompiledPoly) : Prop where
  wellOrdered : WellOrdered n s.gates
  next_eq : s.next = n + s.gates.length
  pos_lt : s.pos < s.next
  neg_lt : s.neg < s.next

theorem CompiledPoly.Inv.compileTerm {n : ℕ} {s : CompiledPoly} (hs : s.Inv n)
    {t : ℤ × MonomialCode} (he : t.2.length ≤ n) : (Hilbert10.compileTerm s t).Inv n where
  wellOrdered := by
    simp only [Hilbert10.compileTerm, wellOrdered_append]
    rw [← hs.next_eq]
    exact ⟨hs.wellOrdered, termGates_wellOrdered s t hs.pos_lt hs.neg_lt
      (he.trans (by rw [hs.next_eq]; exact Nat.le_add_right n _))⟩
  next_eq := by
    have := compileMonomial_next t.2 s.next
    simp only [Hilbert10.compileTerm, List.length_append, termGates_length, hs.next_eq] at this ⊢
    omega
  pos_lt := by
    have := compileMonomial_next t.2 s.next
    have := hs.pos_lt
    simp only [Hilbert10.compileTerm]
    split_ifs <;> omega
  neg_lt := by
    have := compileMonomial_next t.2 s.next
    have := hs.neg_lt
    simp only [Hilbert10.compileTerm]
    split_ifs <;> omega

theorem CompiledPoly.Inv.compileTerms {n : ℕ} :
    ∀ (ts : List (ℤ × MonomialCode)) {s : CompiledPoly}, s.Inv n → (∀ t ∈ ts, t.2.length ≤ n) →
      (Hilbert10.compileTerms s ts).Inv n
  | [], _, hs, _ => hs
  | t :: ts, s, hs, h =>
    CompiledPoly.Inv.compileTerms ts (hs.compileTerm (h t (by simp)))
      fun u hu => h u (by simp [hu])

theorem compileTerms_length (s : CompiledPoly) :
    ∀ ts : List (ℤ × MonomialCode),
      (compileTerms s ts).gates.length = s.gates.length + (ts.map fun t => t.2.sum + 4).sum
  | [] => by simp [compileTerms]
  | t :: ts => by
    change (compileTerms (compileTerm s t) ts).gates.length = _
    rw [compileTerms_length (compileTerm s t) ts]
    simp only [compileTerm, List.length_append, termGates_length, List.map_cons, List.sum_cons]
    omega

theorem compileTerms_next (s : CompiledPoly) :
    ∀ ts : List (ℤ × MonomialCode),
      (compileTerms s ts).next = s.next + (ts.map fun t => t.2.sum + 4).sum
  | [] => by simp [compileTerms]
  | t :: ts => by
    change (compileTerms (compileTerm s t) ts).next = _
    rw [compileTerms_next (compileTerm s t) ts]
    simp only [compileTerm, compileMonomial_next, List.map_cons, List.sum_cons]
    omega

/-- **Soundness of the fold**: any satisfying assignment moves `pos − neg` by exactly the value
of the terms compiled. -/
theorem compileTerms_sound (y : List ℤ) :
    ∀ (ts : List (ℤ × MonomialCode)) (s : CompiledPoly),
      (∀ g ∈ (compileTerms s ts).gates, g.Holds y) →
        y.getD (compileTerms s ts).pos 0 - y.getD (compileTerms s ts).neg 0 =
          y.getD s.pos 0 - y.getD s.neg 0 + evalInt ⟨ts⟩ y
  | [], s, _ => by simp [compileTerms]
  | t :: ts, s, h => by
    have h1 : ∀ g ∈ termGates s t, g.Holds y := fun g hg =>
      h g (mem_gates_compileTerms _ ts g (by simp [compileTerm, hg]))
    have e1 := termGates_sound s t y h1
    have e2 := compileTerms_sound y ts (compileTerm s t) h
    simp only [compileTerms] at e2 ⊢
    rw [e2, e1, evalInt_mk_cons]
    ring

/-! ### The polynomial-level contracts -/

theorem compilePoly_inv (p : PolynomialCode) (n : ℕ) (h : p.arity ≤ n) :
    (compilePoly p n).Inv n := by
  have h0 : CompiledPoly.Inv n ⟨[Gate.const n 0], n, n, n + 1⟩ :=
    ⟨by simp [WellOrdered, Gate.Fresh, Gate.reads, Gate.out], rfl, Nat.lt_succ_self n,
      Nat.lt_succ_self n⟩
  exact CompiledPoly.Inv.compileTerms p.terms h0 fun t ht => (length_le_arity ht).trans h

/-- **Well-ordering**, given that allocation starts at or above the arity. -/
theorem compilePoly_wellOrdered (p : PolynomialCode) (n : ℕ) (h : p.arity ≤ n) :
    WellOrdered n (compilePoly p n).gates :=
  (compilePoly_inv p n h).wellOrdered

/-- **Exact bookkeeping**: one zero wire, then `exponent sum + 4` gates per term. -/
theorem compilePoly_length (p : PolynomialCode) (n : ℕ) :
    (compilePoly p n).gates.length = 1 + (p.terms.map fun t => t.2.sum + 4).sum := by
  simp [compilePoly, compileTerms_length]

/-- Bookkeeping needs no freshness hypothesis: the next wire is always `n + gates.length`. -/
theorem compilePoly_next (p : PolynomialCode) (n : ℕ) :
    (compilePoly p n).next = n + (compilePoly p n).gates.length := by
  rw [compilePoly_length]
  simp only [compilePoly, compileTerms_next]
  omega

theorem compilePoly_pos_lt (p : PolynomialCode) (n : ℕ) (h : p.arity ≤ n) :
    (compilePoly p n).pos < (compilePoly p n).next :=
  (compilePoly_inv p n h).pos_lt

theorem compilePoly_neg_lt (p : PolynomialCode) (n : ℕ) (h : p.arity ≤ n) :
    (compilePoly p n).neg < (compilePoly p n).next :=
  (compilePoly_inv p n h).neg_lt

/-- **Soundness over `ℤ`**: at any assignment satisfying the gates, the polynomial's value is
the positive accumulator minus the negative one. No freshness hypothesis: this is algebra. -/
theorem compilePoly_sound (p : PolynomialCode) (n : ℕ) (y : List ℤ)
    (h : ∀ g ∈ (compilePoly p n).gates, g.Holds y) :
    evalInt p y = y.getD (compilePoly p n).pos 0 - y.getD (compilePoly p n).neg 0 := by
  have hz : y.getD n 0 = 0 := by
    have := h (Gate.const n 0) (mem_gates_compileTerms _ p.terms _ (by simp))
    simpa [Gate.Holds, Gate.out, Gate.value] using this
  rw [compilePoly, compileTerms_sound y p.terms _ h, hz]
  simp

/-- **Soundness over `ℕ`**, through the cast: never a truncated subtraction. -/
theorem compilePoly_sound_nat (p : PolynomialCode) (n : ℕ) (y : List ℕ)
    (h : ∀ g ∈ (compilePoly p n).gates, g.Holds y) :
    eval p y =
      ((y.getD (compilePoly p n).pos 0 : ℕ) : ℤ) - ((y.getD (compilePoly p n).neg 0 : ℕ) : ℤ) := by
  rw [← evalInt_map_natCast, compilePoly_sound p n (y.map Nat.cast)
    (fun g hg => (Gate.holds_map_natCast g y).mpr (h g hg)), getD_map_natCast, getD_map_natCast]

/-! ### The quadratic system

The defining gates become equations, and one more equation — the terminal equality of the two
accumulators — is appended. That last equation is a *constraint*, not a gate: it allocates no
wire, takes no part in `WellOrdered`, and is exactly what relates the accumulators. Without it
every nonzero constant would be "solvable". -/

/-- The number of auxiliary variables the lowering allocates. -/
def gateCount (p : PolynomialCode) : ℕ := (compilePoly p p.arity).gates.length

/-- **The quadratic system of a polynomial**: its defining gates as equations, then the terminal
equality `pos = neg`. Allocation starts at `p.arity`, so the original variables are a prefix. -/
def quadraticSystem (p : PolynomialCode) : List PolynomialCode :=
  (compilePoly p p.arity).gates.map Gate.code ++
    [eqGate (compilePoly p p.arity).pos (compilePoly p p.arity).neg]

theorem quadraticSystem_length (p : PolynomialCode) :
    (quadraticSystem p).length = gateCount p + 1 := by
  simp [quadraticSystem, gateCount]

/-- **Pointwise semantics over `ℤ`**: the system vanishes at `y` exactly when every defining
gate holds and the two accumulators agree. -/
theorem quadraticSystem_eval_zero_iff (p : PolynomialCode) (y : List ℤ) :
    (∀ q ∈ quadraticSystem p, evalInt q y = 0) ↔
      (∀ g ∈ (compilePoly p p.arity).gates, g.Holds y) ∧
        y.getD (compilePoly p p.arity).pos 0 = y.getD (compilePoly p p.arity).neg 0 := by
  simp only [quadraticSystem, List.forall_mem_append, List.forall_mem_map,
    List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true,
    Gate.evalInt_code_eq_zero_iff, evalInt_eqGate_eq_zero_iff]

/-- **Pointwise semantics over `ℕ`.** -/
theorem quadraticSystem_eval_zero_iff_nat (p : PolynomialCode) (y : List ℕ) :
    (∀ q ∈ quadraticSystem p, eval q y = 0) ↔
      (∀ g ∈ (compilePoly p p.arity).gates, g.Holds y) ∧
        y.getD (compilePoly p p.arity).pos 0 = y.getD (compilePoly p p.arity).neg 0 := by
  simp only [quadraticSystem, List.forall_mem_append, List.forall_mem_map,
    List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true,
    Gate.eval_code_eq_zero_iff, eval_eqGate_eq_zero_iff]

/-! ### Extension correctness

Freshness guarantees the gates can be satisfied; the polynomial's arity guarantees that the
auxiliary suffix is invisible to it. Both are needed, and they are used at different steps. -/

/-- **Extension correctness over `ℤ`**: an exact-arity assignment is a root exactly when some
auxiliary suffix of length `gateCount p` makes the whole system vanish. -/
theorem evalInt_eq_zero_iff_exists_aux (p : PolynomialCode) (x : List ℤ)
    (hx : x.length = p.arity) :
    evalInt p x = 0 ↔
      ∃ aux : List ℤ, aux.length = gateCount p ∧
        ∀ q ∈ quadraticSystem p, evalInt q (x ++ aux) = 0 := by
  have hwo := compilePoly_wellOrdered p p.arity le_rfl
  constructor
  · intro h0
    obtain ⟨y, hy, hyx, hg⟩ := exists_extension _ _ hwo x hx
    refine ⟨y.drop p.arity, ?_, ?_⟩
    · simp [hy, gateCount]
    · have hsplit : x ++ y.drop p.arity = y := by rw [← hyx, List.take_append_drop]
      rw [hsplit, quadraticSystem_eval_zero_iff]
      refine ⟨hg, ?_⟩
      have hs := compilePoly_sound p p.arity y hg
      have hval : evalInt p y = 0 := by
        rw [← hsplit, evalInt_append_of_arity_le (by rw [hx])]
        exact h0
      rw [hval] at hs
      exact sub_eq_zero.mp hs.symm
  · rintro ⟨aux, -, hsys⟩
    rw [quadraticSystem_eval_zero_iff] at hsys
    obtain ⟨hg, heq⟩ := hsys
    have hs := compilePoly_sound p p.arity (x ++ aux) hg
    rw [evalInt_append_of_arity_le (by rw [hx]), heq, sub_self] at hs
    exact hs

/-- **Extension correctness over `ℕ`**: natural inputs get natural auxiliaries. -/
theorem eval_eq_zero_iff_exists_aux (p : PolynomialCode) (x : List ℕ)
    (hx : x.length = p.arity) :
    eval p x = 0 ↔
      ∃ aux : List ℕ, aux.length = gateCount p ∧
        ∀ q ∈ quadraticSystem p, eval q (x ++ aux) = 0 := by
  have hwo := compilePoly_wellOrdered p p.arity le_rfl
  constructor
  · intro h0
    obtain ⟨y, hy, hyx, hg⟩ := exists_extension _ _ hwo x hx
    refine ⟨y.drop p.arity, ?_, ?_⟩
    · simp [hy, gateCount]
    · have hsplit : x ++ y.drop p.arity = y := by rw [← hyx, List.take_append_drop]
      rw [hsplit, quadraticSystem_eval_zero_iff_nat]
      refine ⟨hg, ?_⟩
      have hs := compilePoly_sound_nat p p.arity y hg
      have hval : eval p y = 0 := by
        rw [← hsplit, eval_append_of_arity_le (by rw [hx])]
        exact h0
      rw [hval] at hs
      exact_mod_cast sub_eq_zero.mp hs.symm
  · rintro ⟨aux, -, hsys⟩
    rw [quadraticSystem_eval_zero_iff_nat] at hsys
    obtain ⟨hg, heq⟩ := hsys
    have hs := compilePoly_sound_nat p p.arity (x ++ aux) hg
    rw [eval_append_of_arity_le (by rw [hx]), heq, sub_self] at hs
    exact hs

/-! ### Root equivalence, unrestricted

Forward, the source witness is normalised to exact arity and extended. Backward, the entire
satisfying assignment is the source witness: `compilePoly_sound` holds at any length, and the
polynomial does not see the suffix, so no prefix has to be reconstructed. -/

/-- **A polynomial has an integer root exactly when its quadratic system does.** -/
theorem intSolvable_iff_systemIntSolvable_quadraticSystem (p : PolynomialCode) :
    IntSolvable p ↔ SystemIntSolvable (quadraticSystem p) := by
  constructor
  · intro h
    obtain ⟨x, hx, h0⟩ := (intSolvable_iff_arity p).mp h
    obtain ⟨aux, -, hsys⟩ := (evalInt_eq_zero_iff_exists_aux p x hx).mp h0
    exact ⟨x ++ aux, hsys⟩
  · rintro ⟨y, hy⟩
    rw [quadraticSystem_eval_zero_iff] at hy
    obtain ⟨hg, heq⟩ := hy
    refine ⟨y, ?_⟩
    rw [compilePoly_sound p p.arity y hg, heq, sub_self]

/-- **A polynomial has a natural root exactly when its quadratic system does.** -/
theorem natSolvable_iff_systemNatSolvable_quadraticSystem (p : PolynomialCode) :
    NatSolvable p ↔ SystemNatSolvable (quadraticSystem p) := by
  constructor
  · intro h
    obtain ⟨x, hx, h0⟩ := (natSolvable_iff_arity p).mp h
    obtain ⟨aux, -, hsys⟩ := (eval_eq_zero_iff_exists_aux p x hx).mp h0
    exact ⟨x ++ aux, hsys⟩
  · rintro ⟨y, hy⟩
    rw [quadraticSystem_eval_zero_iff_nat] at hy
    obtain ⟨hg, heq⟩ := hy
    refine ⟨y, ?_⟩
    rw [compilePoly_sound_nat p p.arity y hg, heq, sub_self]

/-! ### Bounds -/

/-- **Every equation of the system is quadratic.** -/
theorem systemDegreeBound_quadraticSystem_le (p : PolynomialCode) :
    systemDegreeBound (quadraticSystem p) ≤ 2 := by
  rw [systemDegreeBound_le_iff]
  simp only [quadraticSystem, List.forall_mem_append, List.forall_mem_map, List.forall_mem_cons,
    List.mem_nil_iff, false_implies, implies_true, and_true]
  exact ⟨fun g _ => Gate.degreeBound_code_le g, (degreeBound_eqGate_le _ _).trans one_le_two⟩

/-- In a well-ordered list starting at `n`, every gate writes below `n + length` and reads below
what it writes. -/
theorem WellOrdered.out_lt_and_reads_lt {n : ℕ} :
    ∀ {gs : List Gate}, WellOrdered n gs →
      ∀ g ∈ gs, g.out < n + gs.length ∧ ∀ r ∈ g.reads, r < g.out
  | [], _, g, hg => by simp at hg
  | g' :: gs, ⟨⟨hout, hreads⟩, hwo⟩, g, hg => by
    rcases List.mem_cons.mp hg with rfl | hg'
    · exact ⟨by simp [hout], by rw [hout]; exact hreads⟩
    · obtain ⟨h1, h2⟩ := WellOrdered.out_lt_and_reads_lt hwo g hg'
      exact ⟨by simp only [List.length_cons]; omega, h2⟩

/-- **The system uses at most `p.arity + gateCount p` variables.** -/
theorem systemArity_quadraticSystem_le (p : PolynomialCode) :
    systemArity (quadraticSystem p) ≤ p.arity + gateCount p := by
  have hwo := compilePoly_wellOrdered p p.arity le_rfl
  have hnext := compilePoly_next p p.arity
  rw [systemArity_le_iff]
  simp only [quadraticSystem, List.forall_mem_append, List.forall_mem_map, List.forall_mem_cons,
    List.mem_nil_iff, false_implies, implies_true, and_true, gateCount]
  refine ⟨fun g hg => ?_, ?_⟩
  · obtain ⟨hout, hreads⟩ := hwo.out_lt_and_reads_lt g hg
    exact (Gate.arity_code_le g hreads).trans (by omega)
  · have hp := compilePoly_pos_lt p p.arity le_rfl
    have hn := compilePoly_neg_lt p p.arity le_rfl
    exact (arity_eqGate_le _ _).trans (by omega)

/-! ### Regression examples -/

/-- The empty exponent vector: one wire, holding `1`. -/
example : compileMonomial [] 3 = ⟨[Gate.const 3 1], 3, 4⟩ := by decide

/-- Zero exponents allocate nothing: `x₂³` costs one constant and three multiplications. -/
example : (compileMonomial [0, 0, 3] 5).gates.length = 4 := by decide
example : (compileMonomial [0, 0, 3] 5).next = 9 := by decide

/-- `x₀² x₁` from wire `2`: the gates, in allocation order. -/
example : compileMonomial [2, 1] 2 =
    ⟨[Gate.const 2 1, Gate.mul 3 2 0, Gate.mul 4 3 0, Gate.mul 5 4 1], 5, 6⟩ := by
  decide

/-- Soundness, instantiated: at `x₀ = 3, x₁ = 4` the wires read `1, 3, 9, 36`, and the output
wire is the last. -/
example : ∀ g ∈ (compileMonomial [2, 1] 2).gates, g.Holds ([3, 4, 1, 3, 9, 36] : List ℕ) := by
  decide
example : ([3, 4, 1, 3, 9, 36] : List ℕ).getD (compileMonomial [2, 1] 2).out 0 = 36 := by
  decide

/-- The direction well-ordering exists for: a wrong value on the output wire cannot satisfy the
gates. -/
example : ¬ ∀ g ∈ (compileMonomial [2, 1] 2).gates, g.Holds ([3, 4, 1, 3, 9, 35] : List ℕ) := by
  decide

/-- The constant `1`: a zero wire, a `1` wire, `|1|`, their product, and the positive
accumulator. Five gates, `pos` last, `neg` still the zero wire. -/
example : compilePoly ⟨[(1, [])]⟩ 0 =
    ⟨[Gate.const 0 0, Gate.const 1 1, Gate.const 2 1, Gate.mul 3 1 2, Gate.add 4 0 3],
      4, 0, 5⟩ := by
  decide

/-- The constant `−1` takes the other branch: `neg` last, `pos` the zero wire. -/
example : (compilePoly ⟨[(-1, [])]⟩ 0).pos = 0 := by decide
example : (compilePoly ⟨[(-1, [])]⟩ 0).neg = 4 := by decide

/-- Soundness, instantiated on `−1`: the satisfying assignment reads `pos − neg = 0 − 1`. -/
example : ∀ g ∈ (compilePoly ⟨[(-1, [])]⟩ 0).gates, g.Holds ([0, 1, 1, 1, 1] : List ℤ) := by
  decide
example : ([0, 1, 1, 1, 1] : List ℤ).getD (compilePoly ⟨[(-1, [])]⟩ 0).pos 0 -
    ([0, 1, 1, 1, 1] : List ℤ).getD (compilePoly ⟨[(-1, [])]⟩ 0).neg 0 = -1 := by
  decide

/-- The count formula on `x₀ − 1` from wire `1`: `1 + (1 + 4) + (0 + 4)`. -/
example : (compilePoly ⟨[(1, [1]), (-1, [])]⟩ 1).gates.length = 10 := by decide

/-- **The first end-to-end rejections**: the constants `1` and `−1`, one per accumulator branch.
Without the terminal constraint both systems would be satisfiable. -/
example : ¬ SystemNatSolvable (quadraticSystem ⟨[(1, [])]⟩) := by
  rw [← natSolvable_iff_systemNatSolvable_quadraticSystem]
  rintro ⟨x, hx⟩
  simp [eval, evalMonomial] at hx

example : ¬ SystemIntSolvable (quadraticSystem ⟨[(-1, [])]⟩) := by
  rw [← intSolvable_iff_systemIntSolvable_quadraticSystem]
  rintro ⟨x, hx⟩
  simp [evalInt, evalMonomialInt] at hx

/-- The empty polynomial is satisfiable, and its system is one zero wire and the terminal equality
of that wire with itself. -/
example : SystemNatSolvable (quadraticSystem ⟨[]⟩) :=
  (natSolvable_iff_systemNatSolvable_quadraticSystem _).mp ⟨[], rfl⟩
example : quadraticSystem ⟨[]⟩ = [constGate 0 0, eqGate 0 0] := rfl

/-- **Cancellation**: `x₀ − x₀`. Both accumulators are nonzero at `x₀ = 3`, yet the terminal
equality holds; the system is satisfied at the extension `[3, 0, 1, 3, 1, 3, 3, 1, 3, 1, 3, 3]`,
where the positive accumulator (wire `6`) and the negative one (wire `11`) both read `3`. -/
example : ∀ q ∈ quadraticSystem ⟨[(1, [1]), (-1, [1])]⟩,
    evalInt q ([3, 0, 1, 3, 1, 3, 3, 1, 3, 1, 3, 3] : List ℤ) = 0 := by
  decide
example : SystemIntSolvable (quadraticSystem ⟨[(1, [1]), (-1, [1])]⟩) :=
  ⟨[3, 0, 1, 3, 1, 3, 3, 1, 3, 1, 3, 3], by decide⟩

/-- The bounds, instantiated on `x₀² + x₁ − 5`: `gateCount = 1 + 6 + 5 + 4 = 16`, so seventeen
equations of degree at most two, in at most `2 + 16` variables. -/
example : gateCount ⟨[(1, [2]), (1, [0, 1]), (-5, [])]⟩ = 16 := by decide
example : (quadraticSystem ⟨[(1, [2]), (1, [0, 1]), (-5, [])]⟩).length = 17 := by decide
example : systemDegreeBound (quadraticSystem ⟨[(1, [2]), (1, [0, 1]), (-5, [])]⟩) = 2 := by
  decide

end Hilbert10


/- Source: Hilbert10.Internal.QuadraticLoweringComp, Hilbert10 v2.3.0, Apache-2.0. -/
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

/-!
# The quadratic lowering is primitive recursive

Issue #57, third checkpoint. `quadraticSystem` is proved computable for the raw transformation:
none of the correctness certificates (`WellOrdered`, the invariants) become encoded data.

## Presentations

The structural definitions of `QuadraticLowering.lean` are kept. Where mathlib's computability
API wants a fold or a closed form, an equivalent presentation is introduced *here* and proved
equal to the structural one, so the public module never changes shape for the sake of a
`Primrec` proof:

* `mulPow` has a closed form over `List.range`;
* `compileMonomialFrom` is a `foldl` over the exponent vector carrying `(gates, acc, next, j)`;
* `compileTerms` is literally `foldl compileTerm`.

`Gate`, `Compiled` and `CompiledPoly` get `Primcodable` instances through explicit equivalences
with sums and products of naturals, following `PolynomialCodePrimcodable.lean`.

## Main results

* `Hilbert10.primrec_quadraticSystem`, `computable_quadraticSystem`
* `Hilbert10.PolynomialCode.primrec_degreeBound`, `primrecPred_degreeBound_le`
-/

namespace Hilbert10

open PolynomialCode Primrec

/-! ### Encodings -/

/-- `Gate` as a sum of tuples: the tag is the summand. -/
def Gate.equivSum : Gate ≃ (ℕ × ℕ) ⊕ ((ℕ × ℕ) ⊕ ((ℕ × ℕ × ℕ) ⊕ (ℕ × ℕ × ℕ))) where
  toFun
    | .const o c => .inl (o, c)
    | .copy o i => .inr (.inl (o, i))
    | .add o i j => .inr (.inr (.inl (o, i, j)))
    | .mul o i j => .inr (.inr (.inr (o, i, j)))
  invFun
    | .inl (o, c) => .const o c
    | .inr (.inl (o, i)) => .copy o i
    | .inr (.inr (.inl (o, i, j))) => .add o i j
    | .inr (.inr (.inr (o, i, j))) => .mul o i j
  left_inv g := by cases g <;> rfl
  right_inv s := by rcases s with _ | _ | _ | _ <;> rfl

instance : Primcodable Gate := Primcodable.ofEquiv _ Gate.equivSum

/-- `Compiled` as a triple. -/
def Compiled.equivProd : Compiled ≃ List Gate × ℕ × ℕ where
  toFun c := (c.gates, c.out, c.next)
  invFun q := ⟨q.1, q.2.1, q.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Primcodable Compiled := Primcodable.ofEquiv _ Compiled.equivProd

/-- `CompiledPoly` as a quadruple. -/
def CompiledPoly.equivProd : CompiledPoly ≃ List Gate × ℕ × ℕ × ℕ where
  toFun s := (s.gates, s.pos, s.neg, s.next)
  invFun q := ⟨q.1, q.2.1, q.2.2.1, q.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Primcodable CompiledPoly := Primcodable.ofEquiv _ CompiledPoly.equivProd

/-! ### Gates -/

theorem primrec_gate_const : Primrec fun q : ℕ × ℕ => Gate.const q.1 q.2 :=
  (Primrec.of_equiv_symm (e := Gate.equivSum)).comp Primrec.sumInl

theorem primrec_gate_mul : Primrec fun q : ℕ × ℕ × ℕ => Gate.mul q.1 q.2.1 q.2.2 :=
  (Primrec.of_equiv_symm (e := Gate.equivSum)).comp
    (Primrec.sumInr.comp (Primrec.sumInr.comp Primrec.sumInr))

theorem primrec_gate_add : Primrec fun q : ℕ × ℕ × ℕ => Gate.add q.1 q.2.1 q.2.2 :=
  (Primrec.of_equiv_symm (e := Gate.equivSum)).comp
    (Primrec.sumInr.comp (Primrec.sumInr.comp Primrec.sumInl))

/-- `Sum.elim` of primitive recursive functions is primitive recursive. -/
private theorem primrec_sumElim {α β σ : Type} [Primcodable α] [Primcodable β] [Primcodable σ]
    {f : α → σ} {g : β → σ} (hf : Primrec f) (hg : Primrec g) : Primrec (Sum.elim f g) :=
  (Primrec.sumCasesOn Primrec.id (hf.comp Primrec.snd).to₂ (hg.comp Primrec.snd).to₂).of_eq
    fun s => by cases s <;> rfl

/-- The gate codes, on the sum presentation. -/
private def codeOfSum : (ℕ × ℕ) ⊕ ((ℕ × ℕ) ⊕ ((ℕ × ℕ × ℕ) ⊕ (ℕ × ℕ × ℕ))) → PolynomialCode :=
  Sum.elim (fun q => constGate q.1 q.2) (Sum.elim (fun q => eqGate q.1 q.2)
    (Sum.elim (fun q => addGate q.1 q.2.1 q.2.2) (fun q => mulGate q.1 q.2.1 q.2.2)))

private theorem gate_code_eq (g : Gate) : g.code = codeOfSum (Gate.equivSum g) := by
  cases g <;> rfl

private theorem primrec_constGate : Primrec fun q : ℕ × ℕ => constGate q.1 (q.2 : ℤ) :=
  (Primrec₂.comp primrec₂_add (primrec_X.comp Primrec.fst)
    (primrec_const.comp (Primrec.int_neg.comp (Primrec.int_natCast.comp Primrec.snd)))).of_eq
    fun _ => rfl

private theorem primrec_eqGate : Primrec fun q : ℕ × ℕ => eqGate q.1 q.2 :=
  (Primrec₂.comp primrec₂_add (primrec_X.comp Primrec.fst)
    (primrec_neg.comp (primrec_X.comp Primrec.snd))).of_eq fun _ => rfl

private theorem primrec_addGate : Primrec fun q : ℕ × ℕ × ℕ => addGate q.1 q.2.1 q.2.2 :=
  (Primrec₂.comp primrec₂_add (primrec_X.comp Primrec.fst)
    (primrec_neg.comp (Primrec₂.comp primrec₂_add (primrec_X.comp (Primrec.fst.comp Primrec.snd))
      (primrec_X.comp (Primrec.snd.comp Primrec.snd))))).of_eq fun _ => rfl

private theorem primrec_mulGate : Primrec fun q : ℕ × ℕ × ℕ => mulGate q.1 q.2.1 q.2.2 :=
  (Primrec₂.comp primrec₂_add (primrec_X.comp Primrec.fst)
    (primrec_neg.comp (Primrec₂.comp primrec₂_mul (primrec_X.comp (Primrec.fst.comp Primrec.snd))
      (primrec_X.comp (Primrec.snd.comp Primrec.snd))))).of_eq fun _ => rfl

private theorem primrec_codeOfSum : Primrec codeOfSum :=
  primrec_sumElim primrec_constGate (primrec_sumElim primrec_eqGate
    (primrec_sumElim primrec_addGate primrec_mulGate))

theorem primrec_gate_code : Primrec Gate.code :=
  (primrec_codeOfSum.comp (Primrec.of_equiv (e := Gate.equivSum))).of_eq fun g =>
    (gate_code_eq g).symm

/-! ### `mulPow`, in closed form -/

/-- The closed form: gate `k` writes `next + k` and reads the previous wire (or `acc` first). -/
def mulPowC (j acc next a : ℕ) : Compiled :=
  ⟨(List.range a).map fun k => Gate.mul (next + k) (if k = 0 then acc else next + k - 1) j,
    if a = 0 then acc else next + (a - 1), next + a⟩

theorem mulPow_out_eq (j acc next : ℕ) :
    ∀ a : ℕ, (mulPow j acc next a).out = if a = 0 then acc else next + (a - 1)
  | 0 => rfl
  | a + 1 => by
    rw [mulPow]
    dsimp only
    rw [mulPow_out_eq j next (next + 1) a]
    by_cases ha : a = 0
    · subst ha
      simp
    · simp only [ha, if_false, Nat.add_one_ne_zero]
      omega

theorem mulPow_gates_eq (j acc next : ℕ) :
    ∀ a : ℕ, (mulPow j acc next a).gates =
      (List.range a).map fun k => Gate.mul (next + k) (if k = 0 then acc else next + k - 1) j
  | 0 => rfl
  | a + 1 => by
    rw [mulPow]
    dsimp only
    rw [mulPow_gates_eq j next (next + 1) a, List.range_succ_eq_map, List.map_cons, List.map_map,
      List.cons.injEq]
    refine ⟨by simp, List.map_congr_left fun k _ => ?_⟩
    simp only [Function.comp_def, Nat.succ_ne_zero, if_false]
    congr 1
    · omega
    · split_ifs <;> omega

theorem mulPow_eq_mulPowC (j a acc next : ℕ) : mulPow j acc next a = mulPowC j acc next a := by
  unfold mulPowC
  rw [← mulPow_gates_eq, ← mulPow_out_eq, ← mulPow_next]

theorem primrec_mulPowC : Primrec fun q : ℕ × ℕ × ℕ × ℕ => mulPowC q.1 q.2.1 q.2.2.1 q.2.2.2 := by
  -- projections
  have hj : Primrec fun q : ℕ × ℕ × ℕ × ℕ => q.1 := Primrec.fst
  have hacc : Primrec fun q : ℕ × ℕ × ℕ × ℕ => q.2.1 := Primrec.fst.comp Primrec.snd
  have hnext : Primrec fun q : ℕ × ℕ × ℕ × ℕ => q.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have ha : Primrec fun q : ℕ × ℕ × ℕ × ℕ => q.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hgates : Primrec fun q : ℕ × ℕ × ℕ × ℕ => (List.range q.2.2.2).map fun k =>
      Gate.mul (q.2.2.1 + k) (if k = 0 then q.2.1 else q.2.2.1 + k - 1) q.1 := by
    have harg : Primrec fun r : (ℕ × ℕ × ℕ × ℕ) × ℕ =>
        (r.1.2.2.1 + r.2, (if r.2 = 0 then r.1.2.1 else r.1.2.2.1 + r.2 - 1), r.1.1) := by
      refine (Primrec₂.comp Primrec.nat_add (hnext.comp Primrec.fst) Primrec.snd).pair ?_
      refine (Primrec.ite (PrimrecRel.comp (Primrec.eq (α := ℕ)) Primrec.snd
        (Primrec.const (0 : ℕ))) (hacc.comp Primrec.fst) ?_).pair (hj.comp Primrec.fst)
      exact Primrec₂.comp Primrec.nat_sub
        (Primrec₂.comp Primrec.nat_add (hnext.comp Primrec.fst) Primrec.snd)
        (Primrec.const (1 : ℕ))
    exact Primrec.list_map (Primrec.list_range.comp ha) (primrec_gate_mul.comp harg).to₂
  have hout : Primrec fun q : ℕ × ℕ × ℕ × ℕ =>
      if q.2.2.2 = 0 then q.2.1 else q.2.2.1 + (q.2.2.2 - 1) :=
    Primrec.ite (PrimrecRel.comp (Primrec.eq (α := ℕ)) ha (Primrec.const (0 : ℕ))) hacc
      (Primrec₂.comp Primrec.nat_add hnext
        (Primrec₂.comp Primrec.nat_sub ha (Primrec.const (1 : ℕ))))
  exact (Primrec.of_equiv_symm (e := Compiled.equivProd)).comp
    (hgates.pair (hout.pair (Primrec₂.comp Primrec.nat_add hnext ha)))

theorem primrec_mulPow : Primrec fun q : ℕ × ℕ × ℕ × ℕ => mulPow q.1 q.2.1 q.2.2.1 q.2.2.2 :=
  primrec_mulPowC.of_eq fun _ => (mulPow_eq_mulPowC _ _ _ _).symm

/-! ### `compileMonomialFrom`, as a fold -/

/-- The fold state: gates so far, accumulator wire, next wire, current variable. -/
private def monoStep (s : List Gate × ℕ × ℕ × ℕ) (a : ℕ) : List Gate × ℕ × ℕ × ℕ :=
  let c := mulPow s.2.2.2 s.2.1 s.2.2.1 a
  (s.1 ++ c.gates, c.out, c.next, s.2.2.2 + 1)

private theorem foldl_monoStep :
    ∀ (es : MonomialCode) (gates : List Gate) (acc next j : ℕ),
      es.foldl monoStep (gates, acc, next, j) =
        (gates ++ (compileMonomialFrom acc next j es).gates,
          (compileMonomialFrom acc next j es).out, (compileMonomialFrom acc next j es).next,
          j + es.length)
  | [], gates, acc, next, j => by simp [compileMonomialFrom]
  | a :: es, gates, acc, next, j => by
    rw [List.foldl_cons, monoStep, foldl_monoStep es]
    simp only [compileMonomialFrom, List.append_assoc, List.length_cons, Prod.mk.injEq, true_and]
    omega

private theorem primrec_monoStep : Primrec₂ monoStep := by
  have hc : Primrec fun q : (List Gate × ℕ × ℕ × ℕ) × ℕ =>
      mulPow q.1.2.2.2 q.1.2.1 q.1.2.2.1 q.2 :=
    primrec_mulPow.comp
      ((Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).pair
        ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
          ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).pair
            Primrec.snd)))
  have hgates : Primrec fun c : Compiled => c.gates :=
    Primrec.fst.comp (Primrec.of_equiv (e := Compiled.equivProd))
  have hout : Primrec fun c : Compiled => c.out :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.of_equiv (e := Compiled.equivProd)))
  have hnext : Primrec fun c : Compiled => c.next :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv (e := Compiled.equivProd)))
  have h : Primrec fun q : (List Gate × ℕ × ℕ × ℕ) × ℕ => monoStep q.1 q.2 :=
    (Primrec₂.comp Primrec.list_append (Primrec.fst.comp Primrec.fst) (hgates.comp hc)).pair
      ((hout.comp hc).pair ((hnext.comp hc).pair (Primrec₂.comp Primrec.nat_add
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
        (Primrec.const (1 : ℕ)))))
  exact h.to₂

theorem primrec_compileMonomialFrom :
    Primrec fun q : ℕ × ℕ × ℕ × MonomialCode => compileMonomialFrom q.1 q.2.1 q.2.2.1 q.2.2.2 := by
  have hfold : Primrec fun q : ℕ × ℕ × ℕ × MonomialCode =>
      q.2.2.2.foldl (fun s b => monoStep s b) (([] : List Gate), q.1, q.2.1, q.2.2.1) :=
    Primrec.list_foldl (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
      ((Primrec.const ([] : List Gate)).pair (Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))))
      (primrec_monoStep.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
  refine ((Primrec.of_equiv_symm (e := Compiled.equivProd)).comp
    ((Primrec.fst.comp hfold).pair ((Primrec.fst.comp (Primrec.snd.comp hfold)).pair
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hfold)))))).of_eq fun q => ?_
  rw [foldl_monoStep]
  rfl

theorem primrec_compileMonomial : Primrec₂ compileMonomial := by
  have hc : Primrec fun q : MonomialCode × ℕ => compileMonomialFrom q.2 (q.2 + 1) 0 q.1 :=
    primrec_compileMonomialFrom.comp (Primrec.snd.pair
      ((Primrec₂.comp Primrec.nat_add Primrec.snd (Primrec.const (1 : ℕ))).pair
        ((Primrec.const (0 : ℕ)).pair Primrec.fst)))
  have hgates : Primrec fun c : Compiled => c.gates :=
    Primrec.fst.comp (Primrec.of_equiv (e := Compiled.equivProd))
  have hout : Primrec fun c : Compiled => c.out :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.of_equiv (e := Compiled.equivProd)))
  have hnext : Primrec fun c : Compiled => c.next :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv (e := Compiled.equivProd)))
  have h : Primrec fun q : MonomialCode × ℕ => compileMonomial q.1 q.2 :=
    ((Primrec.of_equiv_symm (e := Compiled.equivProd)).comp
      ((Primrec₂.comp Primrec.list_cons
          (primrec_gate_const.comp (Primrec.snd.pair (Primrec.const (1 : ℕ))))
          (hgates.comp hc)).pair
        ((hout.comp hc).pair (hnext.comp hc)))).of_eq fun _ => rfl
  exact h.to₂

/-! ### Terms and the polynomial -/

private theorem primrec_compileTerm : Primrec₂ compileTerm := by
  have hsg : Primrec fun s : CompiledPoly => s.gates :=
    Primrec.fst.comp (Primrec.of_equiv (e := CompiledPoly.equivProd))
  have hsp : Primrec fun s : CompiledPoly => s.pos :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.of_equiv (e := CompiledPoly.equivProd)))
  have hsn : Primrec fun s : CompiledPoly => s.neg :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.of_equiv (e := CompiledPoly.equivProd))))
  have hsx : Primrec fun s : CompiledPoly => s.next :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.of_equiv (e := CompiledPoly.equivProd))))
  have hcg : Primrec fun c : Compiled => c.gates :=
    Primrec.fst.comp (Primrec.of_equiv (e := Compiled.equivProd))
  have hco : Primrec fun c : Compiled => c.out :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.of_equiv (e := Compiled.equivProd)))
  have hcx : Primrec fun c : Compiled => c.next :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv (e := Compiled.equivProd)))
  -- the compiled monomial of the term, from the state's next wire
  have hcm : Primrec fun q : CompiledPoly × (ℤ × MonomialCode) => compileMonomial q.2.2 q.1.next :=
    primrec_compileMonomial.comp (Primrec.snd.comp Primrec.snd) (hsx.comp Primrec.fst)
  have hnonneg : PrimrecPred fun q : CompiledPoly × (ℤ × MonomialCode) => 0 ≤ q.2.1 :=
    Primrec.int_nonneg.comp (Primrec.fst.comp Primrec.snd)
  have hnx := hcx.comp hcm
  have hplus : ∀ k : ℕ, Primrec fun q : CompiledPoly × (ℤ × MonomialCode) =>
      (compileMonomial q.2.2 q.1.next).next + k := fun k =>
    Primrec₂.comp Primrec.nat_add hnx (Primrec.const (k : ℕ))
  have hsel : Primrec fun q : CompiledPoly × (ℤ × MonomialCode) =>
      if 0 ≤ q.2.1 then q.1.pos else q.1.neg :=
    Primrec.ite hnonneg (hsp.comp Primrec.fst) (hsn.comp Primrec.fst)
  have htg : Primrec fun q : CompiledPoly × (ℤ × MonomialCode) => termGates q.1 q.2 := by
    refine (Primrec₂.comp Primrec.list_append (hcg.comp hcm) ?_).of_eq fun q => rfl
    refine Primrec₂.comp Primrec.list_cons
      (primrec_gate_const.comp (hnx.pair (Primrec.int_natAbs.comp (Primrec.fst.comp Primrec.snd))))
      ?_
    refine Primrec₂.comp Primrec.list_cons
      (primrec_gate_mul.comp ((hplus 1).pair ((hco.comp hcm).pair hnx))) ?_
    exact Primrec₂.comp Primrec.list_cons
      (primrec_gate_add.comp ((hplus 2).pair (hsel.pair (hplus 1))))
      (Primrec.const ([] : List Gate))
  have h : Primrec fun q : CompiledPoly × (ℤ × MonomialCode) => compileTerm q.1 q.2 :=
    ((Primrec.of_equiv_symm (e := CompiledPoly.equivProd)).comp
      ((Primrec₂.comp Primrec.list_append (hsg.comp Primrec.fst) htg).pair
        ((Primrec.ite hnonneg (hplus 2) (hsp.comp Primrec.fst)).pair
          ((Primrec.ite hnonneg (hsn.comp Primrec.fst) (hplus 2)).pair (hplus 3))))).of_eq
      fun _ => rfl
  exact h.to₂

private theorem compileTerms_eq_foldl (s : CompiledPoly) :
    ∀ ts : List (ℤ × MonomialCode), compileTerms s ts = ts.foldl compileTerm s
  | [] => rfl
  | t :: ts => compileTerms_eq_foldl (compileTerm s t) ts

private theorem primrec_compileTerms : Primrec₂ compileTerms := by
  have h : Primrec fun q : CompiledPoly × List (ℤ × MonomialCode) => compileTerms q.1 q.2 :=
    (Primrec.list_foldl (f := fun q : CompiledPoly × List (ℤ × MonomialCode) => q.2)
      (g := fun q => q.1) (h := fun _ r => compileTerm r.1 r.2) Primrec.snd Primrec.fst
      (primrec_compileTerm.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun q => (compileTerms_eq_foldl q.1 q.2).symm
  exact h.to₂

theorem primrec_compilePoly : Primrec₂ compilePoly := by
  have hinit : Primrec fun q : PolynomialCode × ℕ =>
      (⟨[Gate.const q.2 0], q.2, q.2, q.2 + 1⟩ : CompiledPoly) :=
    (Primrec.of_equiv_symm (e := CompiledPoly.equivProd)).comp
      ((Primrec₂.comp Primrec.list_cons
        (primrec_gate_const.comp (Primrec.snd.pair (Primrec.const (0 : ℕ))))
        (Primrec.const ([] : List Gate))).pair
        (Primrec.snd.pair (Primrec.snd.pair (Primrec₂.comp Primrec.nat_add Primrec.snd
          (Primrec.const (1 : ℕ))))))
  have h : Primrec fun q : PolynomialCode × ℕ => compilePoly q.1 q.2 :=
    (primrec_compileTerms.comp hinit (primrec_terms.comp Primrec.fst)).of_eq fun _ => rfl
  exact h.to₂

theorem primrec_quadraticSystem : Primrec quadraticSystem := by
  have hcp : Primrec fun p : PolynomialCode => compilePoly p p.arity :=
    primrec_compilePoly.comp Primrec.id primrec_arity
  have hsg : Primrec fun s : CompiledPoly => s.gates :=
    Primrec.fst.comp (Primrec.of_equiv (e := CompiledPoly.equivProd))
  have hsp : Primrec fun s : CompiledPoly => s.pos :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.of_equiv (e := CompiledPoly.equivProd)))
  have hsn : Primrec fun s : CompiledPoly => s.neg :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.of_equiv (e := CompiledPoly.equivProd))))
  refine (Primrec₂.comp Primrec.list_append
    (Primrec.list_map (hsg.comp hcp) (primrec_gate_code.comp Primrec.snd).to₂)
    (Primrec₂.comp Primrec.list_cons
      (primrec_eqGate.comp ((hsp.comp hcp).pair (hsn.comp hcp)))
      (Primrec.const ([] : List PolynomialCode)))).of_eq
    fun p => rfl

theorem computable_quadraticSystem : Computable quadraticSystem :=
  primrec_quadraticSystem.to_comp

/-! ### The degree test -/

namespace PolynomialCode

private theorem primrec_list_sum : Primrec fun l : List ℕ => l.sum := by
  refine (Primrec.list_foldr (f := fun l : List ℕ => l) (g := fun _ => 0)
    (h := fun _ q => q.1 + q.2) Primrec.id (Primrec.const (0 : ℕ))
    (Primrec₂.comp Primrec.nat_add (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun l => ?_
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem primrec_degreeBound : Primrec degreeBound := by
  refine (Primrec.list_foldr (f := fun p : PolynomialCode => p.terms) (g := fun _ => 0)
    (h := fun _ q => max q.1.2.sum q.2) primrec_terms (Primrec.const (0 : ℕ))
    (Primrec₂.comp Primrec.nat_max
      (primrec_list_sum.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun p => ?_
  simp only [degreeBound, monomialDegree]
  induction p.terms with
  | nil => rfl
  | cons t ts ih => simp [ih]

/-- **The degree test is primitive recursive**, which is what recursive enumerability of the
restricted problems needs — decidability alone would not do. -/
theorem primrecPred_degreeBound_le (d : ℕ) :
    PrimrecPred fun p : PolynomialCode => p.degreeBound ≤ d :=
  PrimrecRel.comp Primrec.nat_le primrec_degreeBound (Primrec.const d)

end PolynomialCode

end Hilbert10

end IntegerDPRM

section NumberRingReduction

namespace ManinBilinear

namespace KPDPRM

section General

variable {R κ η : Type*} [Ring R]

/-- A finite gate formula for the embedded integers, with free variable 0. -/
def IntGateDefinable (decode : κ → R) : Prop :=
  ∃ D : List (Gate κ), ∀ a : R,
    (∃ x : ℕ → R, x 0 = a ∧ ∀ g ∈ D, g.Holds decode x) ↔
      ∃ z : ℤ, (z : R) = a

def renameGate (f : ℕ → ℕ) (encode : κ → η) : Gate κ → Gate η
  | .inl (i,j,k) => Gate.add (f i) (f j) (f k)
  | .inr (.inl (i,j,k)) => Gate.mul (f i) (f j) (f k)
  | .inr (.inr (i,c)) => Gate.const (f i) (encode c)

@[simp] theorem holds_renameGate (decode : η → R) (x : ℕ → R)
    (f : ℕ → ℕ) (encode : κ → η) (g : Gate κ) :
    (renameGate f encode g).Holds decode x ↔ g.Holds (decode ∘ encode) (x ∘ f) := by
  rcases g with ⟨i,j,k⟩ | (⟨i,j,k⟩ | ⟨i,c⟩) <;> rfl

private theorem holds_of_agree (decode : κ → R) (g : Gate κ)
    (x y : ℕ → R) (h : ∀ i ∈ gateRegisters g, x i = y i) :
    g.Holds decode x ↔ g.Holds decode y := by
  rcases g with ⟨i,j,k⟩ | (⟨i,j,k⟩ | ⟨i,c⟩)
  · change (x i + x j = x k) ↔ y i + y j = y k
    rw [h i (by simp [gateRegisters]), h j (by simp [gateRegisters]), h k (by simp [gateRegisters])]
  · change (x i * x j = x k) ↔ y i * y j = y k
    rw [h i (by simp [gateRegisters]), h j (by simp [gateRegisters]), h k (by simp [gateRegisters])]
  · change (x i = decode c) ↔ y i = decode c
    rw [h i (by simp [gateRegisters])]

def mainRegister (i : ℕ) : ℕ := 2 * i

def witnessRegister (i j : ℕ) : ℕ :=
  if j = 0 then mainRegister i else 2 * Nat.pair i j + 1

@[simp] theorem witnessRegister_zero (i : ℕ) : witnessRegister i 0 = mainRegister i := by
  simp [witnessRegister]

def imposeIntegers (code : ℤ → κ) (D : List (Gate κ)) (S : List (Gate ℤ)) :
    List (Gate κ) :=
  S.map (renameGate mainRegister code) ++
    S.flatMap (fun g => (gateRegisters g).flatMap (fun i =>
      D.map (renameGate (witnessRegister i) id)))

private def mergeAssignments (a : ℕ → R) (w : ℕ → ℕ → R) (k : ℕ) : R :=
  if k % 2 = 0 then a (k / 2) else
    w (Nat.unpair (k / 2)).1 (Nat.unpair (k / 2)).2

omit [Ring R] in
@[simp] private theorem mergeAssignments_main (a : ℕ → R) (w : ℕ → ℕ → R) (i : ℕ) :
    mergeAssignments a w (mainRegister i) = a i := by
  simp [mergeAssignments, mainRegister]

omit [Ring R] in
@[simp] private theorem mergeAssignments_witness (a : ℕ → R) (w : ℕ → ℕ → R)
    (hw : ∀ i, w i 0 = a i) (i j : ℕ) :
    mergeAssignments a w (witnessRegister i j) = w i j := by
  by_cases h : j = 0
  · subst j
    simp [hw]
  · have hd : (2 * Nat.pair i j + 1) / 2 = Nat.pair i j := by omega
    simp [witnessRegister, h, mergeAssignments, hd, Nat.unpair_pair]

private theorem holds_intCast_iff [CharZero R] (x : ℕ → ℤ) (g : Gate ℤ) :
    g.Holds (fun z : ℤ => (z : R)) (fun i => (x i : R)) ↔ g.Holds id x := by
  rcases g with ⟨i,j,k⟩ | (⟨i,j,k⟩ | ⟨i,c⟩)
  · change ((x i : R) + (x j : R) = (x k : R)) ↔ x i + x j = x k
    rw [← Int.cast_add, Int.cast_inj]
  · change ((x i : R) * (x j : R) = (x k : R)) ↔ x i * x j = x k
    rw [← Int.cast_mul, Int.cast_inj]
  · exact Int.cast_inj

theorem imposeIntegers_correct [CharZero R] (decode : κ → R) (code : ℤ → κ)
    (hcode : ∀ z, decode (code z) = (z : R)) (D : List (Gate κ))
    (hD : ∀ a : R, (∃ x : ℕ → R, x 0 = a ∧ ∀ g ∈ D, g.Holds decode x) ↔
      ∃ z : ℤ, (z : R) = a) (S : List (Gate ℤ)) :
    gateSat decode (imposeIntegers code D S) ↔ gateSat (id : ℤ → ℤ) S := by
  classical
  have castDecode : decode ∘ code = fun z : ℤ => (z : R) := funext hcode
  constructor
  · rintro ⟨a, ha⟩
    have hint (g : Gate ℤ) (hg : g ∈ S) (i : ℕ) (hi : i ∈ gateRegisters g) :
        ∃ z : ℤ, (z : R) = a (mainRegister i) := by
      apply (hD _).mp
      refine ⟨a ∘ witnessRegister i, by simp, ?_⟩
      intro t ht
      have hmem : renameGate (witnessRegister i) id t ∈ imposeIntegers code D S :=
        List.mem_append_right _ (List.mem_flatMap.mpr ⟨g, hg,
          List.mem_flatMap.mpr ⟨i, hi, List.mem_map.mpr ⟨t, ht, rfl⟩⟩⟩)
      exact (holds_renameGate decode a (witnessRegister i) id t).mp (ha _ hmem)
    let z (i : ℕ) : ℤ :=
      if h : ∃ w : ℤ, (w : R) = a (mainRegister i) then Classical.choose h else 0
    refine ⟨z, fun g hg => (holds_intCast_iff (R := R) z g).mp ?_⟩
    apply (holds_of_agree (fun z : ℤ => (z : R)) g _ (a ∘ mainRegister) ?_).mpr
    · rw [← castDecode, ← holds_renameGate]
      exact ha _ (List.mem_append_left _
        (List.mem_map.mpr ⟨g, hg, rfl⟩))
    · intro i hi
      unfold z
      rw [dif_pos (hint g hg i hi)]
      exact Classical.choose_spec (hint g hg i hi)
  · rintro ⟨z, hz⟩
    have existsWitness (i : ℕ) := (hD (z i : R)).mpr ⟨z i, rfl⟩
    let w (i : ℕ) := Classical.choose (existsWitness i)
    have hw (i : ℕ) : w i 0 = (z i : R) ∧ ∀ t ∈ D, t.Holds decode (w i) :=
      Classical.choose_spec (existsWitness i)
    let a := mergeAssignments (fun i => (z i : R)) w
    refine ⟨a, fun t ht => ?_⟩
    rcases List.mem_append.mp ht with ht | ht
    · obtain ⟨g,hg,rfl⟩ := List.mem_map.mp ht
      rw [holds_renameGate, castDecode, show a ∘ mainRegister = (fun i => (z i : R)) from
        funext (fun i => mergeAssignments_main (fun k => (z k : R)) w i)]
      exact (holds_intCast_iff (R := R) z g).mpr (hz g hg)
    · obtain ⟨g,_,ht⟩ := List.mem_flatMap.mp ht
      obtain ⟨i,_,ht⟩ := List.mem_flatMap.mp ht
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp ht
      rw [holds_renameGate, Function.comp_id,
        show a ∘ witnessRegister i = w i from
          funext (fun j => mergeAssignments_witness _ _ (fun k => (hw k).1) i j)]
      exact (hw i).2 q hq

section Effective

variable [Primcodable κ]

private theorem primrec_sum_elim {A B C : Type*} [Primcodable A] [Primcodable B]
    [Primcodable C] {f : A → C} {g : B → C} (hf : Primrec f) (hg : Primrec g) :
    Primrec (Sum.elim f g) :=
  (Primrec.sumCasesOn Primrec.id (hf.comp₂ Primrec₂.right)
    (hg.comp₂ Primrec₂.right)).of_eq (fun a => by cases a <;> rfl)

private theorem primrec_mainRegister : Primrec mainRegister := Primrec.nat_double

private theorem primrec_witnessRegister (j : ℕ) : Primrec (fun i => witnessRegister i j) := by
  by_cases h : j = 0
  · subst j
    simpa only [witnessRegister_zero] using primrec_mainRegister
  · refine (Primrec.nat_double_succ.comp
      (Primrec₂.natPair.comp Primrec.id (Primrec.const j))).of_eq ?_
    intro i
    simp [witnessRegister, h]

private theorem primrec_gateRegisters : Primrec (gateRegisters (κ := ℤ)) := by
  have h₁ : Primrec (fun t : ℕ × ℕ × ℕ => [t.1,t.2.1,t.2.2]) :=
    Primrec.list_cons.comp Primrec.fst (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.list_cons.comp (Primrec.snd.comp Primrec.snd) (Primrec.const [])))
  have h₂ : Primrec (fun t : ℕ × ℤ => [t.1]) :=
    Primrec.list_cons.comp Primrec.fst (Primrec.const [])
  exact (primrec_sum_elim h₁ (primrec_sum_elim h₁ h₂)).of_eq (fun g => by
    rcases g with ⟨i,j,k⟩ | (⟨i,j,k⟩ | ⟨i,c⟩) <;> rfl)

private theorem primrec_rename_main (code : ℤ → κ) (hcode : Primrec code) :
    Primrec (renameGate mainRegister code) := by
  have ht : Primrec (fun t : ℕ × ℕ × ℕ =>
      (mainRegister t.1, mainRegister t.2.1, mainRegister t.2.2)) :=
    (primrec_mainRegister.comp Primrec.fst).pair
      ((primrec_mainRegister.comp (Primrec.fst.comp Primrec.snd)).pair
        (primrec_mainRegister.comp (Primrec.snd.comp Primrec.snd)))
  have hc : Primrec (fun t : ℕ × ℤ => (mainRegister t.1, code t.2)) :=
    (primrec_mainRegister.comp Primrec.fst).pair (hcode.comp Primrec.snd)
  refine (primrec_sum_elim (Primrec.sumInl.comp ht)
    (primrec_sum_elim (Primrec.sumInr.comp (Primrec.sumInl.comp ht))
      (Primrec.sumInr.comp (Primrec.sumInr.comp hc)))).of_eq ?_
  intro g
  rcases g with ⟨i,j,k⟩ | (⟨i,j,k⟩ | ⟨i,c⟩) <;> rfl

private theorem primrec_rename_witness (g : Gate κ) :
    Primrec (fun i => renameGate (witnessRegister i) id g) := by
  rcases g with ⟨i,j,k⟩ | (⟨i,j,k⟩ | ⟨i,c⟩)
  · exact Primrec.sumInl.comp ((primrec_witnessRegister i).pair
      ((primrec_witnessRegister j).pair (primrec_witnessRegister k)))
  · exact Primrec.sumInr.comp (Primrec.sumInl.comp ((primrec_witnessRegister i).pair
      ((primrec_witnessRegister j).pair (primrec_witnessRegister k))))
  · exact Primrec.sumInr.comp (Primrec.sumInr.comp ((primrec_witnessRegister i).pair
      (Primrec.const c)))

theorem primrec_imposeIntegers (code : ℤ → κ) (hcode : Primrec code) (D : List (Gate κ)) :
    Primrec (imposeIntegers code D) := by
  have hd : Primrec (fun i => D.map (renameGate (witnessRegister i) id)) := by
    induction D with
    | nil => exact Primrec.const []
    | cons g D ih => exact Primrec.list_cons.comp (primrec_rename_witness g) ih
  unfold imposeIntegers
  apply Primrec.list_append.comp
  · exact Primrec.list_map Primrec.id ((primrec_rename_main code hcode).comp₂ Primrec₂.right)
  · exact Primrec.list_flatMap Primrec.id
      ((Primrec.list_flatMap primrec_gateRegisters (hd.comp₂ Primrec₂.right)).comp₂ Primrec₂.right)

end Effective

/-- Encode an integer as the coordinates of its image in the chosen basis. -/
noncomputable def encodeInt {d : ℕ} (b : Module.Basis (Fin d) ℤ R) (z : ℤ) : List ℤ :=
  List.ofFn fun i => z * b.repr 1 i

theorem basisDecode_encodeInt {d : ℕ} (b : Module.Basis (Fin d) ℤ R) (z : ℤ) :
    basisDecode b (encodeInt b z) = (z : R) := by
  unfold basisDecode encodeInt
  simp only [List.getElem?_ofFn, Fin.isLt, dif_pos, Option.getD_some, mul_zsmul]
  rw [← Finset.smul_sum, b.sum_repr, zsmul_one]

theorem primrec_encodeInt {d : ℕ} (b : Module.Basis (Fin d) ℤ R) : Primrec (encodeInt b) := by
  unfold encodeInt
  exact Primrec.list_ofFn (fun i =>
    Ripple.BoundedUniversality.BGP.primrec2_int_mul.comp Primrec.id (Primrec.const (b.repr 1 i)))

theorem not_computablePred_gateSat_of_intGateDefinable [CharZero R] {d : ℕ}
    (b : Module.Basis (Fin d) ℤ R)
    (hℤ : ¬ ComputablePred (gateSat (id : ℤ → ℤ)))
    (hDef : IntGateDefinable (basisDecode b)) :
    ¬ ComputablePred (gateSat (basisDecode b)) := by
  obtain ⟨D, hD⟩ := hDef
  intro h
  apply hℤ
  exact computablePred_pullback
    (primrec_imposeIntegers (encodeInt b) (primrec_encodeInt b) D).to_comp
    (fun S => (imposeIntegers_correct (basisDecode b) (encodeInt b)
      (basisDecode_encodeInt b) D hD S).symm) h

/-- The finite-free ring arithmetic interface follows from integer gate
undecidability and Diophantine definability of the embedded integers. -/
theorem koymansPaganoFiniteFree_of_intGateDefinable
    (hℤ : ¬ ComputablePred (gateSat (id : ℤ → ℤ)))
    (hDef : ∀ (R : Type) [CommRing R] [Nontrivial R] (d : ℕ)
      (b : Module.Basis (Fin d) ℤ R), IntGateDefinable (basisDecode b)) :
    KoymansPaganoFiniteFree := by
  intro R _ _ d b
  let : Module.Free ℤ R := Module.Free.of_basis b
  let : CharZero R := charZero_of_inj_zero fun n hn => by
    have h : (n : ℤ) • (1 : R) = (0 : ℤ) • (1 : R) := by simpa using hn
    exact Int.ofNat_eq_zero.mp ((smul_left_injective ℤ (one_ne_zero : (1 : R) ≠ 0)) h)
  exact not_computablePred_gateSat_of_intGateDefinable b hℤ (hDef R d b)

end General

section FixedPolynomial

variable {R κ : Type*} [CommRing R]

private theorem wellOrdered_append (G H : List (Gate κ)) (start : ℕ)
    (hG : WellOrdered start G) (hH : WellOrdered (start + G.length) H) :
    WellOrdered start (G ++ H) := by
  induction G generalizing start with
  | nil => simpa using hH
  | cons g G ih =>
    obtain ⟨ho,hr,ht⟩ := hG
    exact ⟨ho,hr,ih (start+1) ht (by
      convert hH using 1 <;> simp <;> omega)⟩

private theorem evalTape_append (decode : κ → R) (G H : List (Gate κ)) (x : ℕ → R) :
    evalTape decode (G ++ H) x = evalTape decode H (evalTape decode G x) := by
  induction G generalizing x with
  | nil => rfl
  | cons g G ih => exact ih _

private theorem evalTape_last (decode : κ → R) (G : List (Gate κ))
    (x : ℕ → R) (g : Gate κ) :
    evalTape decode (G ++ [g]) x g.output =
      g.value decode (evalTape decode G x) := by
  rw [evalTape_append]
  simp [evalTape]

/-- Any fixed polynomial can be read as a finite tape starting above its inputs. -/
theorem exists_tape_of_polynomial (decode : κ → R) (hdecode : Function.Surjective decode)
    {n : ℕ} (P : MvPolynomial (Fin n) R) :
    ∀ start ≥ n, ∃ (G : List (Gate κ)) (k : ℕ),
      WellOrdered start G ∧ k < start + G.length ∧
      ∀ x : ℕ → R, evalTape decode G x k = MvPolynomial.eval (fun i : Fin n => x i) P := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    intro start _
    obtain ⟨v, rfl⟩ := hdecode c
    refine ⟨[Gate.const start v], start, ?_, by simp, ?_⟩
    · simp [WellOrdered, Gate.const, Gate.output, Gate.reads]
    · intro x
      simp [evalTape, Gate.const, Gate.output, Gate.value]
  | add P Q hP hQ =>
    intro start hstart
    obtain ⟨G,i,hG,hi,evG⟩ := hP start hstart
    have hstart' : n ≤ start + G.length := by omega
    obtain ⟨H,j,hH,hj,evH⟩ := hQ (start+G.length) hstart'
    let k := start + (G ++ H).length
    let g : Gate κ := Gate.add i j k
    refine ⟨(G++H)++[g], k,
      wellOrdered_append _ _ _ (wellOrdered_append G H start hG hH) ?_, ?_, ?_⟩
    · simp only [WellOrdered, Gate.add, Gate.output, Gate.reads, and_true, k, g, true_and]
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · simp only [List.length_append]; omega
      · have e : a = j := by simpa using ha
        subst a
        simp only [List.length_append]; omega
    · simp [k]
    · intro x
      have hlast := evalTape_last decode (G++H) x g
      change evalTape decode ((G++H)++[g]) x k = _ at hlast
      rw [hlast]
      change evalTape decode (G++H) x i + evalTape decode (G++H) x j = _
      rw [evalTape_append, evalTape_agrees decode H _ hH _ i hi, evG, evH, map_add]
      have hInputs : (fun a : Fin n => evalTape decode G x a) = fun a : Fin n => x a :=
        funext fun a => evalTape_agrees decode G start hG x a (lt_of_lt_of_le a.isLt hstart)
      rw [hInputs]
  | mul_X P v hP =>
    intro start hstart
    obtain ⟨G,i,hG,hi,evG⟩ := hP start hstart
    let k := start + G.length
    let g : Gate κ := Gate.mul i v k
    refine ⟨G++[g], k, wellOrdered_append _ _ _ hG ?_, ?_, ?_⟩
    · simp only [WellOrdered, Gate.mul, Gate.output, Gate.reads, and_true, k, g, true_and]
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hi
      · have e : a = v.val := by simpa using ha
        subst a
        have hv := v.isLt
        omega
    · simp [k]
    · intro x
      have hlast := evalTape_last decode G x g
      change evalTape decode (G++[g]) x k = _ at hlast
      rw [hlast]
      change evalTape decode G x i * evalTape decode G x v = _
      rw [evG, evalTape_agrees decode G start hG _ v (lt_of_lt_of_le v.isLt hstart),
        map_mul, MvPolynomial.eval_X]

/-- A polynomial definition of the integers with one free variable yields
a gate definition with distinguished register zero. -/
theorem intGateDefinable_of_fixed_polynomial (decode : κ → R)
    (hdecode : Function.Surjective decode) {n : ℕ}
    (P : MvPolynomial (Fin (n + 1)) R)
    (hP : ∀ a : R, (∃ w : Fin n → R, MvPolynomial.eval (Fin.cons a w) P = 0) ↔
      ∃ z : ℤ, (z : R) = a) :
    IntGateDefinable decode := by
  obtain ⟨zero,hz⟩ := hdecode 0
  obtain ⟨G,k,hG,_,evG⟩ := exists_tape_of_polynomial decode hdecode P (n+1) le_rfl
  refine ⟨compileTape zero G [k], fun a => ?_⟩
  rw [← hP]
  constructor
  · rintro ⟨x,h0,hx⟩
    have hG' : ∀ g ∈ G, g.Holds decode x :=
      fun g hg => hx g (List.mem_append_left _ hg)
    have hlast : (Gate.const k zero).Holds decode x :=
      hx _ (List.mem_append_right _ (by simp))
    have hek := congrFun (evalTape_eq_of_holds decode G x hG') k
    have hEval : MvPolynomial.eval (fun i : Fin (n+1) => x i) P = 0 := by
      rw [← evG, hek]
      exact hlast.trans hz
    refine ⟨fun i => x i.succ, ?_⟩
    have eq : Fin.cons a (fun i : Fin n => x i.succ) = (fun i : Fin (n+1) => x i) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using h0.symm
      · simp
    rwa [eq]
  · rintro ⟨w,hw⟩
    let v : Fin (n+1) → R := Fin.cons a w
    let x : ℕ → R := fun i => if h : i < n+1 then v ⟨i,h⟩ else 0
    have hex : (fun i : Fin (n+1) => x i) = v := by
      funext i
      simp only [x, dif_pos i.isLt]
    let y := evalTape decode G x
    refine ⟨y, ?_, ?_⟩
    · change evalTape decode G x 0 = a
      rw [evalTape_agrees decode G (n+1) hG _ 0 (by omega)]
      simp [x,v]
    · intro g hg
      unfold compileTape at hg
      rcases List.mem_append.mp hg with hg | hg
      · exact evalTape_holds decode G (n+1) hG x g hg
      · have e : g = Gate.const k zero := by simpa using hg
        subst g
        change evalTape decode G x k = decode zero
        rw [evG, hex, hz]
        exact hw

end FixedPolynomial

end KPDPRM
end ManinBilinear





/-! Reduction of the finite-free Koymans–Pagano case to finite free domains. -/

namespace ManinBilinear

open scoped BigOperators nonZeroDivisors

section PrimeQuotient

variable {R : Type*} [CommRing R]

theorem exists_prime_quotient_charZero [CharZero R] :
    ∃ I : Ideal R, I.IsPrime ∧ CharZero (R ⧸ I) := by
  let S := (nonZeroDivisors ℤ).map (Int.castRingHom R).toMonoidHom
  have hS : Disjoint ((⊥ : Ideal R) : Set R) S := by
    apply Set.disjoint_left.mpr
    intro x hx hxS
    obtain ⟨z, hz, hzx⟩ := Submonoid.mem_map.mp hxS
    have hx0 : x = 0 := Submodule.mem_bot R |>.mp hx
    have hz0 : z = 0 := Int.cast_injective (α := R) (by simpa [hx0] using hzx)
    exact (mem_nonZeroDivisors_iff_ne_zero.mp hz) hz0
  obtain ⟨I, hI, _, hIS⟩ := Ideal.exists_le_prime_disjoint (⊥ : Ideal R) S hS
  refine ⟨I, hI, ⟨fun {x y} hxy => ?_⟩⟩
  by_contra hne
  have hz : (x : ℤ) - (y : ℤ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hne)
  have hm : (((x : ℤ) - (y : ℤ) : ℤ) : R) ∈ I := by
    apply (Ideal.Quotient.eq_zero_iff_mem).mp
    simp [hxy]
  exact Set.disjoint_left.mp hIS hm
    (Submonoid.mem_map.mpr ⟨(x : ℤ) - (y : ℤ), mem_nonZeroDivisors_iff_ne_zero.mpr hz, rfl⟩)

theorem exists_free_prime_quotient [Nontrivial R] {d : ℕ}
    (b : Module.Basis (Fin d) ℤ R) :
    ∃ I : Ideal R, I.IsPrime ∧ ∃ k : ℕ, Nonempty (Module.Basis (Fin k) ℤ (R ⧸ I)) := by
  let : Module.Free ℤ R := Module.Free.of_basis b
  let : Module.Finite ℤ R := Module.Finite.of_basis b
  let : IsAddTorsionFree R := Module.isTorsionFree_int_iff_isAddTorsionFree.mp inferInstance
  let : CharZero R := CharZero.of_isAddTorsionFree R R
  obtain ⟨I, hI, hchar⟩ := exists_prime_quotient_charZero (R := R)
  let : I.IsPrime := hI
  let : CharZero (R ⧸ I) := hchar
  let : Module.Finite ℤ (R ⧸ I) :=
    Module.Finite.of_surjective (Ideal.Quotient.mk I).toAddMonoidHom.toIntLinearMap
      Ideal.Quotient.mk_surjective
  let B := Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := R ⧸ I)
  exact ⟨I, hI, B.1, ⟨B.2⟩⟩

theorem finite_ideal_generators {d : ℕ} (b : Module.Basis (Fin d) ℤ R) (I : Ideal R) :
    ∃ k : ℕ, ∃ c : Fin k → R, Ideal.span (Set.range c) = I := by
  let : Module.Finite ℤ R := Module.Finite.of_basis b
  let : IsNoetherian ℤ R := inferInstance
  obtain ⟨k, c, hc⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp
      (IsNoetherian.noetherian (I.restrictScalars ℤ))
  refine ⟨k, c, le_antisymm ?_ ?_⟩
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change c i ∈ I.restrictScalars ℤ
    rw [← hc]
    exact Submodule.subset_span (Set.mem_range_self i)
  · intro x hx
    have h : Submodule.span ℤ (Set.range c) ≤ (Ideal.span (Set.range c)).restrictScalars ℤ :=
      Submodule.span_le.mpr Ideal.subset_span
    exact h (hc.symm ▸ hx)

end PrimeQuotient



section QuotientCompiler

variable {κ κ' : Type*} [Primcodable κ]

/-- The shared variables are even. Each gate has a disjoint odd scratch bank. -/
private def qOrig (i : ℕ) := 2 * i
private def qAux (g : Gate κ) (i : ℕ) := 2 * Nat.pair (Encodable.encode g) i + 1

private def qEmbed : ℕ ⊕ (Gate κ × ℕ) → ℕ
  | .inl i => qOrig i
  | .inr (g,i) => qAux g i

private theorem qEmbed_inj : Function.Injective (qEmbed (κ := κ)) := by
  rintro (i | ⟨g,i⟩) (j | ⟨h,j⟩) he
  · congr 1
    change 2 * i = 2 * j at he
    omega
  · change 2 * i = 2 * Nat.pair (Encodable.encode h) j + 1 at he
    omega
  · change 2 * Nat.pair (Encodable.encode g) i + 1 = 2 * j at he
    omega
  · change 2 * Nat.pair (Encodable.encode g) i + 1 =
      2 * Nat.pair (Encodable.encode h) j + 1 at he
    have hp : Nat.pair (Encodable.encode g) i = Nat.pair (Encodable.encode h) j := by omega
    rcases Nat.pair_eq_pair.mp hp with ⟨hg, rfl⟩
    rw [Encodable.encode_injective hg]

private def qAcc (i : ℕ) := 4 * i + 1
private def qCoef (i : ℕ) := 4 * i + 2
private def qMult (i : ℕ) := 4 * i + 3
private def qTerm (i : ℕ) := 4 * i + 4

private def qFirst (lift : κ → κ') (g : Gate κ) : Gate κ' :=
  match g with
  | .inl (i,j,_) => Gate.add (qOrig i) (qOrig j) (qAux g 0)
  | .inr (.inl (i,j,_)) => Gate.mul (qOrig i) (qOrig j) (qAux g 0)
  | .inr (.inr (_,c)) => Gate.const (qAux g 0) (lift c)

private def qStep {k : ℕ} (gen : Fin k → κ') (g : Gate κ) (i : Fin k) : List (Gate κ') :=
  [Gate.const (qAux g (qCoef i)) (gen i),
   Gate.mul (qAux g (qMult i)) (qAux g (qCoef i)) (qAux g (qTerm i)),
   Gate.add (qAux g (qAcc i)) (qAux g (qTerm i)) (qAux g (qAcc (i+1)))]

private def qBlock {k : ℕ} (zero : κ') (gen : Fin k → κ') (lift : κ → κ')
    (g : Gate κ) : List (Gate κ') :=
  qFirst lift g :: Gate.const (qAux g (qAcc 0)) zero ::
    Gate.add (qAux g 0) (qAux g (qAcc k)) (qOrig g.output) ::
    (List.ofFn (qStep gen g)).flatten

def compileQuotientGates {k : ℕ} (zero : κ') (gen : Fin k → κ') (lift : κ → κ')
    (gs : List (Gate κ)) : List (Gate κ') :=
  gs.flatMap (qBlock zero gen lift)

private theorem qBlock_holds {R : Type*} [Ring R] {k : ℕ} (dec : κ' → R)
    (zero : κ') (gen : Fin k → κ') (lift : κ → κ') (g : Gate κ) (v : ℕ → R) :
    (∀ h ∈ qBlock zero gen lift g, h.Holds dec v) ↔
    (v (qAux g 0) = g.value (dec ∘ lift) (v ∘ qOrig)) ∧
    (v (qAux g (qAcc 0)) = dec zero) ∧
    (v (qAux g 0) + v (qAux g (qAcc k)) = v (qOrig g.output)) ∧
    (∀ i : Fin k, v (qAux g (qCoef i)) = dec (gen i) ∧
      v (qAux g (qMult i)) * v (qAux g (qCoef i)) = v (qAux g (qTerm i)) ∧
      v (qAux g (qAcc i)) + v (qAux g (qTerm i)) = v (qAux g (qAcc (i+1)))) := by
  have hfirst : (qFirst lift g).Holds dec v ↔
      v (qAux g 0) = g.value (dec ∘ lift) (v ∘ qOrig) := by
    rcases g with ⟨i,j,o⟩ | (⟨i,j,o⟩ | ⟨i,c⟩)
    · exact eq_comm
    · exact eq_comm
    · rfl
  rw [qBlock, List.forall_mem_cons, List.forall_mem_cons, List.forall_mem_cons, hfirst]
  change (_ ∧ _ ∧ _ ∧ _) ↔ _
  have hlast : (∀ h ∈ (List.ofFn (qStep gen g)).flatten, h.Holds dec v) ↔
      ∀ i : Fin k, ∀ h ∈ qStep gen g i, h.Holds dec v := by
    constructor
    · intro h i t ht
      exact h t (List.mem_flatten.mpr ⟨_, List.mem_ofFn.mpr ⟨i,rfl⟩, ht⟩)
    · intro h t ht
      obtain ⟨_, hmem, ht'⟩ := List.mem_flatten.mp ht
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hmem
      exact h i t ht'
  rw [hlast]
  simp only [qStep, List.forall_mem_cons, List.not_mem_nil, false_implies, forall_const,
    and_true]
  rfl


private noncomputable def qExtend {R : Type*} [Zero R] (x : ℕ → R)
    (w : Gate κ → ℕ → R) : ℕ → R :=
  Function.extend qEmbed (Sum.elim x (fun p => w p.1 p.2)) (fun _ => 0)

@[simp] private theorem qExtend_orig {R : Type*} [Zero R] (x : ℕ → R)
    (w : Gate κ → ℕ → R) (i : ℕ) : qExtend x w (qOrig i) = x i :=
  qEmbed_inj.extend_apply _ _ (.inl i)

@[simp] private theorem qExtend_aux {R : Type*} [Zero R] (x : ℕ → R)
    (w : Gate κ → ℕ → R) (g : Gate κ) (i : ℕ) : qExtend x w (qAux g i) = w g i :=
  qEmbed_inj.extend_apply _ _ (.inr (g,i))

private def qAt {R : Type*} [Zero R] {k : ℕ} (f : Fin k → R) (i : ℕ) : R :=
  if h : i < k then f ⟨i,h⟩ else 0

@[simp] private theorem qAt_coe {R : Type*} [Zero R] {k : ℕ}
    (f : Fin k → R) (i : Fin k) : qAt f i = f i := by
  simp [qAt, i.isLt]

private noncomputable def qValues {R : Type*} [Ring R] {k : ℕ}
    (a : R) (gen coef : Fin k → R) (slot : ℕ) : R :=
  if slot = 0 then a else
    let i := (slot-1)/4
    match (slot-1)%4 with
    | 0 => ∑ j ∈ Finset.range i, qAt coef j * qAt gen j
    | 1 => qAt gen i
    | 2 => qAt coef i
    | _ => qAt coef i * qAt gen i

@[simp] private theorem qValues_zero {R : Type*} [Ring R] {k : ℕ}
    (a : R) (gen coef : Fin k → R) : qValues a gen coef 0 = a := by
  simp [qValues]

@[simp] private theorem qValues_acc {R : Type*} [Ring R] {k : ℕ}
    (a : R) (gen coef : Fin k → R) (i : ℕ) :
    qValues a gen coef (qAcc i) = ∑ j ∈ Finset.range i, qAt coef j * qAt gen j := by
  have h0 : qAcc i ≠ 0 := by unfold qAcc; omega
  have h1 : (qAcc i - 1) % 4 = 0 := by unfold qAcc; omega
  have h2 : (qAcc i - 1) / 4 = i := by unfold qAcc; omega
  simp [qValues, h0, h1, h2]

@[simp] private theorem qValues_coef {R : Type*} [Ring R] {k : ℕ}
    (a : R) (gen coef : Fin k → R) (i : ℕ) :
    qValues a gen coef (qCoef i) = qAt gen i := by
  have h0 : qCoef i ≠ 0 := by unfold qCoef; omega
  have h1 : (qCoef i - 1) % 4 = 1 := by unfold qCoef; omega
  have h2 : (qCoef i - 1) / 4 = i := by unfold qCoef; omega
  simp [qValues, h0, h1, h2]

@[simp] private theorem qValues_mult {R : Type*} [Ring R] {k : ℕ}
    (a : R) (gen coef : Fin k → R) (i : ℕ) :
    qValues a gen coef (qMult i) = qAt coef i := by
  have h0 : qMult i ≠ 0 := by unfold qMult; omega
  have h1 : (qMult i - 1) % 4 = 2 := by unfold qMult; omega
  have h2 : (qMult i - 1) / 4 = i := by unfold qMult; omega
  simp [qValues, h0, h1, h2]

@[simp] private theorem qValues_term {R : Type*} [Ring R] {k : ℕ}
    (a : R) (gen coef : Fin k → R) (i : ℕ) :
    qValues a gen coef (qTerm i) = qAt coef i * qAt gen i := by
  have h0 : qTerm i ≠ 0 := by unfold qTerm; omega
  have h1 : (qTerm i - 1) % 4 = 3 := by unfold qTerm; omega
  have h2 : (qTerm i - 1) / 4 = i := by unfold qTerm; omega
  simp [qValues, h0, h1, h2]

omit [Primcodable κ] in
private theorem qValue_map {R S : Type*} [Ring R] [Ring S] (φ : R →+* S)
    (dec : κ' → R) (decQ : κ → S) (lift : κ → κ')
    (hl : ∀ c, φ (dec (lift c)) = decQ c) (x : ℕ → R) (g : Gate κ) :
    φ (g.value (dec ∘ lift) x) = g.value decQ (φ ∘ x) := by
  rcases g with ⟨i,j,o⟩ | (⟨i,j,o⟩ | ⟨i,c⟩)
  · exact map_add φ _ _
  · exact map_mul φ _ _
  · exact hl c

/-- A quotient gate is expressed over the original ring by a correction in the
kernel ideal. Scratch variables for different gate keys are disjoint. -/
theorem gateSat_compileQuotientGates {R S : Type*} [CommRing R] [CommRing S] {k : ℕ}
    (φ : R →+* S) (hφ : Function.Surjective φ) (dec : κ' → R) (decQ : κ → S)
    (zero : κ') (hz : dec zero = 0) (gen : Fin k → κ') (lift : κ → κ')
    (hg : Ideal.span (Set.range (dec ∘ gen)) = RingHom.ker φ)
    (hl : ∀ c, φ (dec (lift c)) = decQ c) (gs : List (Gate κ)) :
    gateSat dec (compileQuotientGates zero gen lift gs) ↔ gateSat decQ gs := by
  classical
  constructor
  · rintro ⟨v,hv⟩
    refine ⟨fun i => φ (v (qOrig i)), fun g hmem => ?_⟩
    obtain ⟨hfirst,hzero,hout,hsteps⟩ :=
      (qBlock_holds dec zero gen lift g v).mp fun h hh =>
        hv h (List.mem_flatMap.mpr ⟨g,hmem,hh⟩)
    have hacc (i : ℕ) (hi : i ≤ k) : φ (v (qAux g (qAcc i))) = 0 := by
      induction i with
      | zero => rw [hzero, hz, map_zero]
      | succ i ih =>
        obtain ⟨hc,hm,ha⟩ := hsteps ⟨i,hi⟩
        change v (qAux g (qCoef i)) = dec (gen ⟨i,hi⟩) at hc
        change v (qAux g (qMult i)) * v (qAux g (qCoef i)) = v (qAux g (qTerm i)) at hm
        change v (qAux g (qAcc i)) + v (qAux g (qTerm i)) =
          v (qAux g (qAcc (i+1))) at ha
        have hgen : φ (dec (gen ⟨i,hi⟩)) = 0 := by
          apply (RingHom.mem_ker (f := φ)).mp
          rw [← hg]
          exact Ideal.subset_span ⟨(⟨i,hi⟩ : Fin k), rfl⟩
        rw [← ha, map_add, ih (Nat.le_of_succ_le hi), ← hm, map_mul, hc, hgen,
          mul_zero, add_zero]
    apply (g.holds_iff_value decQ _).mpr
    have he := congrArg φ hout
    rw [map_add, hacc k le_rfl, add_zero, hfirst, qValue_map φ dec decQ lift hl] at he
    exact he
  · rintro ⟨y,hy⟩
    let x : ℕ → R := fun i => Classical.choose (hφ (y i))
    have hx : φ ∘ x = y := funext fun i => Classical.choose_spec (hφ (y i))
    let value (g : Gate κ) : R := g.value (dec ∘ lift) x
    have hdiff (g : Gate κ) (hmem : g ∈ gs) :
        x g.output - value g ∈ Ideal.span (Set.range (dec ∘ gen)) := by
      rw [hg]
      apply (RingHom.mem_ker (f := φ)).mpr
      rw [map_sub, sub_eq_zero, qValue_map φ dec decQ lift hl, hx,
        (g.holds_iff_value decQ y).mp (hy g hmem)]
      exact congrFun hx g.output
    have hsum (g : Gate κ) (hmem : g ∈ gs) :
        ∃ c : Fin k → R, ∑ i, c i * dec (gen i) = x g.output - value g :=
      Ideal.mem_span_range_iff_exists_fun.mp (hdiff g hmem)
    let coef (g : Gate κ) : Fin k → R :=
      if hmem : g ∈ gs then Classical.choose (hsum g hmem) else 0
    have hcoef (g : Gate κ) (hmem : g ∈ gs) :
        ∑ i, coef g i * dec (gen i) = x g.output - value g := by
      simpa [coef, hmem] using Classical.choose_spec (hsum g hmem)
    let w (g : Gate κ) := qValues (value g) (dec ∘ gen) (coef g)
    refine ⟨qExtend x w, fun h hh => ?_⟩
    obtain ⟨g,hmem,hh'⟩ := List.mem_flatMap.mp hh
    apply (qBlock_holds dec zero gen lift g _).mpr _ h hh'
    have hxx : qExtend x w ∘ qOrig = x := funext fun i => qExtend_orig x w i
    refine ⟨?_, ?_, ?_, fun i => ?_⟩
    · simp [w, value, hxx]
    · simp [w,hz]
    · simp only [qExtend_aux, qExtend_orig, w, qValues_zero, qValues_acc]
      rw [← Fin.sum_univ_eq_sum_range, show
        (∑ i : Fin k, qAt (coef g) i * qAt (dec ∘ gen) i) =
          ∑ i : Fin k, coef g i * dec (gen i) by simp]
      rw [hcoef g hmem, add_sub_cancel]
    · simp only [qExtend_aux, w, qValues_coef, qValues_mult, qValues_term,
        qValues_acc, qAt_coe, Function.comp_apply, true_and]
      rw [Finset.sum_range_succ, qAt_coe, qAt_coe]
      rfl

section Effectivity

variable [Primcodable κ']

private theorem qPrAdd {A : Type*} [Primcodable A] {f g h : A → ℕ}
    (hf : Primrec f) (hg : Primrec g) (hh : Primrec h) :
    Primrec (fun a => (Gate.add (f a) (g a) (h a) : Gate κ')) :=
  Primrec.sumInl.comp (hf.pair (hg.pair hh))

private theorem qPrMul {A : Type*} [Primcodable A] {f g h : A → ℕ}
    (hf : Primrec f) (hg : Primrec g) (hh : Primrec h) :
    Primrec (fun a => (Gate.mul (f a) (g a) (h a) : Gate κ')) :=
  Primrec.sumInr.comp (Primrec.sumInl.comp (hf.pair (hg.pair hh)))

private theorem qPrConst {A : Type*} [Primcodable A] {f : A → ℕ} {c : A → κ'}
    (hf : Primrec f) (hc : Primrec c) :
    Primrec (fun a => Gate.const (f a) (c a)) :=
  Primrec.sumInr.comp (Primrec.sumInr.comp (hf.pair hc))

private theorem qPrOrig : Primrec qOrig := Primrec.nat_double

private theorem qPrAux (i : ℕ) : Primrec (fun g : Gate κ => qAux g i) :=
  Primrec.nat_double_succ.comp (Primrec₂.natPair.comp Primrec.encode (Primrec.const i))

private theorem qPrOutput : Primrec (@Gate.output κ) := by
  let last : (ℕ × ℕ × ℕ) → ℕ := fun t => t.2.2
  have hl : Primrec last := Primrec.snd.comp Primrec.snd
  have hr : Primrec (Sum.elim last (Prod.fst : ℕ × κ → ℕ)) := by
    exact (Primrec.sumCasesOn Primrec.id (hl.comp₂ Primrec₂.right)
      (Primrec.fst.comp₂ Primrec₂.right)).of_eq (fun a => by cases a <;> rfl)
  exact (Primrec.sumCasesOn Primrec.id (hl.comp₂ Primrec₂.right)
    (hr.comp₂ Primrec₂.right)).of_eq (fun a => by rcases a with a | (b | c) <;> rfl)

private theorem qPrFirst (lift : κ → κ') (hl : Primrec lift) : Primrec (qFirst lift) := by
  have ha : Primrec₂ (fun g : Gate κ => fun t : ℕ × ℕ × ℕ =>
      (Gate.add (qOrig t.1) (qOrig t.2.1) (qAux g 0) : Gate κ')) := by
    change Primrec (fun p : Gate κ × (ℕ × ℕ × ℕ) =>
      (Gate.add (qOrig p.2.1) (qOrig p.2.2.1) (qAux p.1 0) : Gate κ'))
    exact qPrAdd (qPrOrig.comp (Primrec.fst.comp Primrec.snd))
      (qPrOrig.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
      ((qPrAux 0).comp Primrec.fst)
  let A := Gate κ × ((ℕ × ℕ × ℕ) ⊕ (ℕ × κ))
  have hm : Primrec₂ (fun p : A => fun t : ℕ × ℕ × ℕ =>
      (Gate.mul (qOrig t.1) (qOrig t.2.1) (qAux p.1 0) : Gate κ')) := by
    change Primrec (fun p : A × (ℕ × ℕ × ℕ) =>
      (Gate.mul (qOrig p.2.1) (qOrig p.2.2.1) (qAux p.1.1 0) : Gate κ'))
    exact qPrMul (qPrOrig.comp (Primrec.fst.comp Primrec.snd))
      (qPrOrig.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
      ((qPrAux 0).comp (Primrec.fst.comp Primrec.fst))
  have hc : Primrec₂ (fun p : A => fun t : ℕ × κ =>
      Gate.const (qAux p.1 0) (lift t.2)) := by
    change Primrec (fun p : A × (ℕ × κ) =>
      Gate.const (qAux p.1.1 0) (lift p.2.2))
    exact qPrConst ((qPrAux 0).comp (Primrec.fst.comp Primrec.fst))
      (hl.comp (Primrec.snd.comp Primrec.snd))
  have hr := Primrec.sumCasesOn (Primrec.snd : Primrec (Prod.snd : A → _)) hm hc
  exact (Primrec.sumCasesOn Primrec.id ha hr.to₂).of_eq (fun a => by
    rcases a with a | (b | c) <;> rfl)

private theorem qPrStep {k : ℕ} (gen : Fin k → κ') (i : Fin k) :
    Primrec (fun g : Gate κ => qStep gen g i) := by
  unfold qStep
  refine Primrec.list_cons.comp (qPrConst (qPrAux _) (Primrec.const _))
    (Primrec.list_cons.comp (qPrMul (qPrAux _) (qPrAux _) (qPrAux _))
      (Primrec.list_cons.comp (qPrAdd (qPrAux _) (qPrAux _) (qPrAux _))
        (Primrec.const [])))

/-- The quotient interpretation is a primitive-recursive transformation. -/
theorem primrec_compileQuotientGates {k : ℕ} (zero : κ') (gen : Fin k → κ')
    (lift : κ → κ') (hl : Primrec lift) :
    Primrec (compileQuotientGates zero gen lift) := by
  have h : Primrec (qBlock zero gen lift : Gate κ → List (Gate κ')) := by
    unfold qBlock
    refine Primrec.list_cons.comp (qPrFirst lift hl)
      (Primrec.list_cons.comp (qPrConst (qPrAux _) (Primrec.const _))
        (Primrec.list_cons.comp (qPrAdd (qPrAux _) (qPrAux _) (qPrOrig.comp qPrOutput))
          (Primrec.list_flatten.comp (Primrec.list_ofFn (qPrStep gen)))))
  exact Primrec.list_flatMap Primrec.id (h.comp₂ Primrec₂.right)

end Effectivity
end QuotientCompiler

section BasisLift

open Ripple.BoundedUniversality.BGP (primrec2_int_add primrec2_int_mul)

variable {R S : Type*} [CommRing R] [CommRing S] {d k : ℕ}

private theorem qDecode_encode (b : Module.Basis (Fin d) ℤ R) (v : R) :
    basisDecode b (List.ofFn (fun i => b.repr v i)) = v := by
  simpa [basisDecode, List.getElem?_ofFn] using b.sum_repr v

private noncomputable def qBasisLift (b : Module.Basis (Fin d) ℤ R)
    (lift : Fin k → R) (c : List ℤ) : List ℤ :=
  List.ofFn (fun i => b.repr (∑ j : Fin k, c[j.val]?.getD 0 • lift j) i)

private theorem qBasisLift_spec (b : Module.Basis (Fin d) ℤ R)
    (bQ : Module.Basis (Fin k) ℤ S) (φ : R →+* S)
    (lift : Fin k → R) (hl : ∀ j, φ (lift j) = bQ j) (c : List ℤ) :
    φ (basisDecode b (qBasisLift b lift c)) = basisDecode bQ c := by
  rw [qBasisLift, qDecode_encode, map_sum]
  simp only [basisDecode, map_zsmul, hl]

private theorem qPrIntSum {A : Type*} [Primcodable A] {n : ℕ} (f : Fin n → A → ℤ)
    (h : ∀ i, Primrec (f i)) : Primrec (fun a => ∑ i : Fin n, f i a) := by
  induction n with
  | zero => exact (Primrec.const (0 : ℤ)).of_eq (by simp)
  | succ n ih =>
    exact (primrec2_int_add.comp (h 0) (ih (fun i => f i.succ) (fun i => h i.succ))).of_eq
      (fun a => (Fin.sum_univ_succ (fun i => f i a)).symm)

private theorem qBasisLift_primrec (b : Module.Basis (Fin d) ℤ R) (lift : Fin k → R) :
    Primrec (qBasisLift b lift) := by
  unfold qBasisLift
  apply Primrec.list_ofFn
  intro i
  have h := qPrIntSum (A := List ℤ) (fun j : Fin k => fun c =>
    c[j.val]?.getD 0 * b.repr (lift j) i)
    (fun j => primrec2_int_mul.comp
      (Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.id (Primrec.const j.val))
        (Primrec.const 0))
      (Primrec.const (b.repr (lift j) i)))
  apply h.of_eq
  intro c
  let e : R →ₗ[ℤ] ℤ := (Finsupp.lapply i).comp b.repr.toLinearMap
  change (∑ j : Fin k, c[j.val]?.getD 0 * e (lift j)) =
    e (∑ j : Fin k, c[j.val]?.getD 0 • lift j)
  rw [map_sum]
  simp only [map_smul, Int.zsmul_eq_mul]

end BasisLift

/-- The same undecidability assertion restricted to finite free integral domains. -/
def KoymansPaganoFiniteFreeDomain : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (d : ℕ) (b : Module.Basis (Fin d) ℤ R),
    ¬ ComputablePred (gateSat (basisDecode b))

/-- Passing from a finite-free domain result to all finite-free rings is effective. -/
theorem koymansPaganoFiniteFree_of_domains
    (h : KoymansPaganoFiniteFreeDomain) : KoymansPaganoFiniteFree := by
  intro R _ _ d b hdec
  obtain ⟨I,hI,k,⟨bQ⟩⟩ := exists_free_prime_quotient b
  let : I.IsPrime := hI
  let φ := Ideal.Quotient.mk I
  have hφ : Function.Surjective φ := Ideal.Quotient.mk_surjective
  let lift : Fin k → R := fun i => Classical.choose (hφ (bQ i))
  have hl (i : Fin k) : φ (lift i) = bQ i := Classical.choose_spec (hφ (bQ i))
  obtain ⟨l,g,hg⟩ := finite_ideal_generators b I
  let code : Fin l → List ℤ := fun i => List.ofFn (fun j => b.repr (g i) j)
  have hcode : basisDecode b ∘ code = g := funext fun i => qDecode_encode b (g i)
  have hker : Ideal.span (Set.range (basisDecode b ∘ code)) = RingHom.ker φ := by
    rw [hcode, hg]
    change I = RingHom.ker (Ideal.Quotient.mk I)
    ext x
    exact Ideal.Quotient.eq_zero_iff_mem.symm.trans RingHom.mem_ker.symm
  have hz : basisDecode b [] = 0 := by simp [basisDecode]
  let q := compileQuotientGates [] code (qBasisLift b lift)
  have hq : Computable q :=
    (primrec_compileQuotientGates [] code _ (qBasisLift_primrec b lift)).to_comp
  apply h (R ⧸ I) k bQ
  apply computablePred_pullback hq _ hdec
  intro gs
  exact (gateSat_compileQuotientGates φ hφ _ _ [] hz code _ hker
    (qBasisLift_spec b bQ φ lift hl) gs).symm

end ManinBilinear

open scoped nonZeroDivisors
open scoped BigOperators

namespace ManinBilinear

/-- The fraction field of a finite integral domain over the integers is a number field. -/
theorem finiteOrder_numberField (A : Type) [CommRing A] [IsDomain A]
    [CharZero A] [Module.Finite ℤ A] : NumberField (FractionRing A) := by
  let : CharZero (FractionRing A) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective A (FractionRing A))
  let : Algebra.IsAlgebraic ℤ A := Algebra.IsAlgebraic.of_finite ℤ A
  letI : Algebra ℤ (FractionRing A) := Ring.toIntAlgebra _
  let : IsScalarTower ℤ A (FractionRing A) :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  let : IsScalarTower ℤ ℚ (FractionRing A) :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have hfin : Module.Finite ℚ (FractionRing A) := by
    rw [← Module.rank_lt_aleph0_iff, Algebra.IsAlgebraic.rank_of_isFractionRing ℤ ℚ A
      (FractionRing A), Module.rank_lt_aleph0_iff]
    infer_instance
  exact { to_charZero := inferInstance, to_finiteDimensional := hfin }

/-- The canonical embedding of an order into the ring of integers of its fraction field. -/
noncomputable def orderToIntegers (A : Type) [CommRing A] [IsDomain A]
    [Module.Finite ℤ A] : A →+* NumberField.RingOfIntegers (FractionRing A) where
  toFun x := by
    letI : Algebra ℤ (FractionRing A) := Ring.toIntAlgebra _
    refine ⟨algebraMap A (FractionRing A) x, ?_⟩
    obtain ⟨P, hm, he⟩ := IsIntegral.of_finite ℤ x
    refine ⟨P, hm, ?_⟩
    change P.eval₂ (algebraMap ℤ (FractionRing A)) (algebraMap A (FractionRing A) x) = 0
    have h : (algebraMap A (FractionRing A)).comp (algebraMap ℤ A) =
        algebraMap ℤ (FractionRing A) := Subsingleton.elim _ _
    rw [← h, ← Polynomial.hom_eval₂, he, map_zero]
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ x y)
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ x y)

theorem orderToIntegers_injective (A : Type) [CommRing A] [IsDomain A]
    [Module.Finite ℤ A] : Function.Injective (orderToIntegers A) :=
  fun _ _ h => IsFractionRing.injective A (FractionRing A) (congrArg Subtype.val h)

/-- Common denominator and numerators for any fixed finite list of integral elements. -/
theorem order_clear_denominators (A : Type) [CommRing A] [IsDomain A] [Module.Finite ℤ A]
    {n : ℕ} (x : Fin n → NumberField.RingOfIntegers (FractionRing A)) :
    ∃ (s : A) (num : Fin n → A), s ≠ 0 ∧
      ∀ i, orderToIntegers A (num i) = orderToIntegers A s * x i := by
  classical
  let F := FractionRing A
  let y : Fin n → F := fun i => algebraMap (NumberField.RingOfIntegers F) F (x i)
  let s := IsLocalization.commonDenom A⁰ Finset.univ y
  let num (i : Fin n) := IsLocalization.integerMultiple A⁰ Finset.univ y ⟨i, Finset.mem_univ i⟩
  refine ⟨s, num, ?_, fun i => ?_⟩
  · exact mem_nonZeroDivisors_iff_ne_zero.mp s.property
  · apply Subtype.ext
    change algebraMap A F (num i) = algebraMap A F (s : A) * y i
    simpa only [Submonoid.smul_def, Algebra.smul_def] using
      IsLocalization.map_integerMultiple A⁰ Finset.univ y ⟨i, Finset.mem_univ i⟩

end ManinBilinear


open scoped BigOperators

namespace ManinBilinear

variable {A S κ : Type*} [CommRing A] [CommRing S] [IsDomain S]

/-- An arithmetic gate on scaled values. In the multiplication case the
right-hand side acquires an extra factor of the scale. -/
def scaledGateHolds (d : A) (decode : κ → A) (x : ℕ → A) : Gate κ → Prop
  | .inl (i,j,k) => x i + x j = x k
  | .inr (.inl (i,j,k)) => x i * x j = d * x k
  | .inr (.inr (i,c)) => x i = decode c

theorem scaledGateHolds_iff (F : A →+* S) (hF : Function.Injective F)
    (d : A) (hd : F d ≠ 0) (decode : κ → S) (decode' : κ → A)
    (hc : ∀ c, F (decode' c) = F d * decode c)
    (x : ℕ → S) (y : ℕ → A) (hxy : ∀ i, F (y i) = F d * x i) (g : Gate κ) :
    scaledGateHolds d decode' y g ↔ g.Holds decode x := by
  rcases g with ⟨i,j,k⟩ | ⟨i,j,k⟩ | ⟨i,c⟩
  · change (y i + y j = y k) ↔ x i + x j = x k
    rw [← hF.eq_iff, map_add, hxy, hxy, hxy, ← mul_add]
    exact ⟨mul_left_cancel₀ hd, congrArg (F d * ·)⟩
  · change (y i * y j = d * y k) ↔ x i * x j = x k
    rw [← hF.eq_iff, map_mul, map_mul, hxy, hxy, hxy]
    rw [show F d * x i * (F d * x j) = (F d * F d) * (x i * x j) by ring,
      show F d * (F d * x k) = (F d * F d) * x k by ring]
    exact ⟨mul_left_cancel₀ (mul_ne_zero hd hd), congrArg ((F d * F d) * ·)⟩
  · change (y i = decode' c) ↔ x i = decode c
    rw [← hF.eq_iff, hxy, hc]
    exact ⟨mul_left_cancel₀ hd, congrArg (F d * ·)⟩

variable {n : ℕ}

/-- All numerator witnesses, with arbitrary order coefficients, decode to
elements of the larger ring. -/
theorem scaled_span_image (F : A →+* S) (d : A) (base : Fin n → S)
    (num : Fin n → A) (hn : ∀ i, F (num i) = F d * base i) (a : Fin n → A) :
    F (∑ i, a i * num i) = F d * ∑ i, F (a i) * base i := by
  simp only [map_sum, map_mul, hn, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by ring)

noncomputable def scaledDecode (num : Fin n → A) (cs : List ℤ) : A :=
  ∑ i : Fin n, cs[i.val]?.getD 0 • num i

omit [IsDomain S] in
theorem scaledDecode_spec (F : A →+* S) (d : A) (b : Module.Basis (Fin n) ℤ S)
    (num : Fin n → A) (hn : ∀ i, F (num i) = F d * b i) (c : List ℤ) :
    F (scaledDecode num c) = F d * basisDecode b c := by
  simp only [scaledDecode, basisDecode, map_sum, map_zsmul, hn, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by simp only [zsmul_eq_mul]; ring)

/-- Gate satisfiability in a finite larger ring has an exact scaled
presentation over the base ring, with linear-span membership witnesses. -/
theorem gateSat_iff_scaled (F : A →+* S) (hF : Function.Injective F)
    (d : A) (hd : F d ≠ 0) (b : Module.Basis (Fin n) ℤ S) (num : Fin n → A)
    (hn : ∀ i, F (num i) = F d * b i) (gs : List (Gate (List ℤ))) :
    gateSat (basisDecode b) gs ↔
    ∃ (y : ℕ → A) (a : ℕ → Fin n → A),
      (∀ i, y i = ∑ j, a i j * num j) ∧
      ∀ g ∈ gs, scaledGateHolds d (scaledDecode num) y g := by
  have hdec := scaledDecode_spec F d b num hn
  constructor
  · rintro ⟨x,hx⟩
    let a (i : ℕ) (j : Fin n) : A := (b.repr (x i) j : ℤ)
    let y (i : ℕ) : A := ∑ j, a i j * num j
    have hy (i : ℕ) : F (y i) = F d * x i := by
      rw [scaled_span_image F d b num hn]
      congr 1
      simpa only [a, map_intCast, zsmul_eq_mul] using b.sum_repr (x i)
    exact ⟨y,a,fun _ => rfl,fun g hg =>
      (scaledGateHolds_iff F hF d hd _ _ hdec x y hy g).mpr (hx g hg)⟩
  · rintro ⟨y,a,ha,hy⟩
    let x (i : ℕ) : S := ∑ j, F (a i j) * b j
    have hx (i : ℕ) : F (y i) = F d * x i := by
      rw [ha, scaled_span_image F d b num hn]
    exact ⟨x,fun g hg => (scaledGateHolds_iff F hF d hd _ _ hdec x y hx g).mp (hy g hg)⟩

end ManinBilinear


open scoped BigOperators

namespace ManinBilinear

private def scaledId (x tag k : ℕ) : ℕ := Nat.pair x (Nat.pair tag k)

private def scaledRegisters : Gate κ → List ℕ
  | .inl (i,j,k) => [i,j,k]
  | .inr (.inl (i,j,k)) => [i,j,k]
  | .inr (.inr (i,_)) => [i]

private def scaledBlock {n : ℕ} (zero scale : κ) (nums : Fin n → κ) (x : ℕ) :
    List (Gate κ) :=
  [Gate.const (scaledId x 2 0) scale,
   Gate.const (scaledId x 3 0) zero,
   Gate.mul (scaledId x 2 0) (scaledId x 0 0) (scaledId x 1 0),
   Gate.add (scaledId x 3 n) (scaledId x 3 0) (scaledId x 0 0)] ++
    (List.finRange n).flatMap fun (j : Fin n) =>
      [Gate.const (scaledId x 5 j) (nums j),
       Gate.mul (scaledId x 4 j) (scaledId x 5 j) (scaledId x 6 j),
       Gate.add (scaledId x 3 j) (scaledId x 6 j) (scaledId x 3 (j.val + 1))]

private def scaledMain (encode : κ → δ) : Gate κ → Gate δ
  | .inl (i,j,k) => Gate.add (scaledId i 0 0) (scaledId j 0 0) (scaledId k 0 0)
  | .inr (.inl (i,j,k)) => Gate.mul (scaledId i 0 0) (scaledId j 0 0) (scaledId k 1 0)
  | .inr (.inr (i,c)) => Gate.const (scaledId i 0 0) (encode c)

def compileScaledGates {n : ℕ} (zero scale : δ) (nums : Fin n → δ) (encode : κ → δ)
    (gs : List (Gate κ)) : List (Gate δ) :=
  gs.flatMap fun g => (scaledRegisters g).flatMap (scaledBlock zero scale nums) ++ [scaledMain encode g]

private def installScaled {A : Type*} [CommRing A] {n : ℕ}
    (d : A) (num : Fin n → A) (y : ℕ → A) (a : ℕ → Fin n → A) (k : ℕ) : A :=
  let t := Nat.unpair k
  let w := Nat.unpair t.2
  let terms (i : ℕ) := if h : i < n then a t.1 ⟨i,h⟩ * num ⟨i,h⟩ else 0
  match w.1 with
  | 0 => y t.1
  | 1 => d * y t.1
  | 2 => d
  | 3 => ∑ i ∈ Finset.range w.2, terms i
  | 4 => if h : w.2 < n then a t.1 ⟨w.2,h⟩ else 0
  | 5 => if h : w.2 < n then num ⟨w.2,h⟩ else 0
  | _ => terms w.2

private theorem block_sound {A δ : Type*} [CommRing A] {n : ℕ} (decode : δ → A)
    (zero scale : δ) (nums : Fin n → δ) (hz : decode zero = 0)
    (a : ℕ → A) (x : ℕ) (h : ∀ g ∈ scaledBlock zero scale nums x, g.Holds decode a) :
    (a (scaledId x 0 0) = ∑ j : Fin n, a (scaledId x 4 j) * decode (nums j)) ∧
      a (scaledId x 1 0) = decode scale * a (scaledId x 0 0) := by
  have hscale : a (scaledId x 2 0) = decode scale := h (Gate.const (scaledId x 2 0) scale) (by simp [scaledBlock])
  have hzero : a (scaledId x 3 0) = 0 := by
    have ht : a (scaledId x 3 0) = decode zero := h (Gate.const (scaledId x 3 0) zero) (by simp [scaledBlock])
    exact ht.trans hz
  have hmul : a (scaledId x 2 0) * a (scaledId x 0 0) = a (scaledId x 1 0) :=
    h (Gate.mul (scaledId x 2 0) (scaledId x 0 0) (scaledId x 1 0)) (by simp [scaledBlock])
  have hlast : a (scaledId x 3 n) + a (scaledId x 3 0) = a (scaledId x 0 0) :=
    h (Gate.add (scaledId x 3 n) (scaledId x 3 0) (scaledId x 0 0)) (by simp [scaledBlock])
  have step (j : Fin n) :
      a (scaledId x 3 (j.val+1)) =
        a (scaledId x 3 j) + a (scaledId x 4 j) * decode (nums j) := by
    have hm : ∀ g ∈ [Gate.const (scaledId x 5 j) (nums j),
          Gate.mul (scaledId x 4 j) (scaledId x 5 j) (scaledId x 6 j),
          Gate.add (scaledId x 3 j) (scaledId x 6 j) (scaledId x 3 (j.val+1))],
        g.Holds decode a := by
      intro g hg
      exact h g (List.mem_append_right _ (List.mem_flatMap.mpr ⟨j,by simp,hg⟩))
    have hnum : a (scaledId x 5 j) = decode (nums j) := hm (Gate.const (scaledId x 5 j) (nums j)) (by simp)
    have hp : a (scaledId x 4 j) * a (scaledId x 5 j) = a (scaledId x 6 j) := hm (Gate.mul (scaledId x 4 j) (scaledId x 5 j) (scaledId x 6 j)) (by simp)
    have hs : a (scaledId x 3 j) + a (scaledId x 6 j) = a (scaledId x 3 (j.val+1)) :=
      hm (Gate.add (scaledId x 3 j) (scaledId x 6 j) (scaledId x 3 (j.val+1))) (by simp)
    rw [← hs, ← hp, hnum]
  let term (j : ℕ) := if hj : j < n then a (scaledId x 4 j) * decode (nums ⟨j,hj⟩) else 0
  have accum (k : ℕ) (hk : k ≤ n) :
      a (scaledId x 3 k) = ∑ j ∈ Finset.range k, term j := by
    induction k with
    | zero => simpa using hzero
    | succ k ih =>
      have hk' : k < n := by omega
      rw [step ⟨k,hk'⟩, Finset.sum_range_succ, ih (by omega)]
      simp [term,hk']
  constructor
  · rw [← hlast, hzero, add_zero, accum n le_rfl, ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j _
    simp [term, j.isLt]
  · exact hmul.symm.trans (by rw [hscale])

private theorem block_complete {A δ : Type*} [CommRing A] {n : ℕ} (decode : δ → A)
    (zero scale : δ) (nums : Fin n → δ) (hz : decode zero = 0)
    (y : ℕ → A) (a : ℕ → Fin n → A) (hy : ∀ x, y x = ∑ j, a x j * decode (nums j))
    (x : ℕ) (g : Gate δ) (hg : g ∈ scaledBlock zero scale nums x) :
    g.Holds decode (installScaled (decode scale) (decode ∘ nums) y a) := by
  rcases List.mem_append.mp hg with h | h
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl | rfl | rfl
    · simp [Gate.const,Gate.Holds,installScaled,scaledId,Nat.unpair_pair]
    · simp [Gate.const,Gate.Holds,installScaled,scaledId,Nat.unpair_pair,hz]
    · simp [Gate.mul,Gate.Holds,installScaled,scaledId,Nat.unpair_pair]
    · simp only [Gate.add,Gate.Holds,installScaled,scaledId,Nat.unpair_pair,
        Finset.range_zero,Finset.sum_empty,add_zero,Function.comp_apply]
      rw [hy, ← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro j _
      simp [j.isLt]
  · obtain ⟨j,_,hj⟩ := List.mem_flatMap.mp h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl
    · simp [Gate.const,Gate.Holds,installScaled,scaledId,Nat.unpair_pair,j.isLt]
    · simp [Gate.mul,Gate.Holds,installScaled,scaledId,Nat.unpair_pair,j.isLt]
    · simp [Gate.add,Gate.Holds,installScaled,scaledId,Nat.unpair_pair,j.isLt,Finset.sum_range_succ]

theorem gateSat_compileScaled_iff {A κ δ : Type*} [CommRing A] {n : ℕ}
    (decode : δ → A) (zero scale : δ) (nums : Fin n → δ) (enc : κ → δ)
    (hz : decode zero = 0) (gs : List (Gate κ)) :
    gateSat decode (compileScaledGates zero scale nums enc gs) ↔
      ∃ (y : ℕ → A) (a : ℕ → Fin n → A),
        (∀ i, y i = ∑ j, a i j * decode (nums j)) ∧
        ∀ g ∈ gs, scaledGateHolds (decode scale) (decode ∘ enc) y g := by
  classical
  constructor
  · rintro ⟨v,hv⟩
    let used (x : ℕ) : Prop := ∃ g ∈ gs, x ∈ scaledRegisters g
    let y (x : ℕ) : A := if used x then v (scaledId x 0 0) else 0
    let a (x : ℕ) (j : Fin n) : A := if used x then v (scaledId x 4 j) else 0
    have hb (x : ℕ) (hx : used x) :=
      block_sound decode zero scale nums hz v x (by
        obtain ⟨g,hg,hx⟩ := hx
        intro q hq
        exact hv q (List.mem_flatMap.mpr ⟨g,hg,
          List.mem_append_left _ (List.mem_flatMap.mpr ⟨x,hx,hq⟩)⟩))
    refine ⟨y,a,?_,?_⟩
    · intro x
      by_cases hx : used x
      · simpa [y,a,hx] using (hb x hx).1
      · simp [y,a,hx]
    · intro g hg
      have hmain := hv (scaledMain enc g) (List.mem_flatMap.mpr ⟨g,hg,List.mem_append_right _ (by simp)⟩)
      rcases g with ⟨i,j,k⟩ | ⟨i,j,k⟩ | ⟨i,c⟩
      · have hi : used i := ⟨_,hg,by simp [scaledRegisters]⟩
        have hj : used j := ⟨_,hg,by simp [scaledRegisters]⟩
        have hk : used k := ⟨_,hg,by simp [scaledRegisters]⟩
        simpa [scaledGateHolds,y,hi,hj,hk,scaledMain,Gate.add,Gate.Holds] using hmain
      · have hi : used i := ⟨_,hg,by simp [scaledRegisters]⟩
        have hj : used j := ⟨_,hg,by simp [scaledRegisters]⟩
        have hk : used k := ⟨_,hg,by simp [scaledRegisters]⟩
        simpa [scaledGateHolds,y,hi,hj,hk,scaledMain,Gate.mul,Gate.Holds,(hb k hk).2] using hmain
      · have hi : used i := ⟨_,hg,by simp [scaledRegisters]⟩
        simpa [scaledGateHolds,y,hi,scaledMain,Gate.const,Gate.Holds] using hmain
  · rintro ⟨y,a,hy,hg⟩
    refine ⟨installScaled (decode scale) (decode ∘ nums) y a,fun q hq => ?_⟩
    obtain ⟨g,hm,hq⟩ := List.mem_flatMap.mp hq
    rcases List.mem_append.mp hq with hq | hq
    · obtain ⟨x,_,hx⟩ := List.mem_flatMap.mp hq
      exact block_complete decode zero scale nums hz y a hy x q hx
    · obtain rfl : q = scaledMain enc g := by simpa using hq
      have h := hg g hm
      rcases g with ⟨i,j,k⟩ | ⟨i,j,k⟩ | ⟨i,c⟩
      · simpa [scaledMain,Gate.add,Gate.Holds,installScaled,scaledId,Nat.unpair_pair,
          scaledGateHolds] using h
      · simpa [scaledMain,Gate.mul,Gate.Holds,installScaled,scaledId,Nat.unpair_pair,
          scaledGateHolds] using h
      · simpa [scaledMain,Gate.const,Gate.Holds,installScaled,scaledId,Nat.unpair_pair,
          scaledGateHolds] using h



section EffectiveScaled

variable {κ δ : Type*} [Primcodable κ] [Primcodable δ]

private theorem pr_scaledId (tag k : ℕ) : Primrec (fun x => scaledId x tag k) :=
  Primrec₂.natPair.comp Primrec.id (Primrec.const (Nat.pair tag k))

private theorem pr_gateConst {X : Type*} [Primcodable X] {i : X → ℕ} {c : X → δ}
    (hi : Primrec i) (hc : Primrec c) : Primrec (fun x => Gate.const (i x) (c x)) :=
  Primrec.sumInr.comp (Primrec.sumInr.comp (hi.pair hc))

private theorem pr_gateAdd {X : Type*} [Primcodable X] {i j k : X → ℕ}
    (hi : Primrec i) (hj : Primrec j) (hk : Primrec k) :
    Primrec (fun x => Gate.add (κ := δ) (i x) (j x) (k x)) :=
  Primrec.sumInl.comp (hi.pair (hj.pair hk))

private theorem pr_gateMul {X : Type*} [Primcodable X] {i j k : X → ℕ}
    (hi : Primrec i) (hj : Primrec j) (hk : Primrec k) :
    Primrec (fun x => Gate.mul (κ := δ) (i x) (j x) (k x)) :=
  Primrec.sumInr.comp (Primrec.sumInl.comp (hi.pair (hj.pair hk)))

private theorem pr_flatMap_const {X T Y : Type*} [Primcodable X] [Primcodable Y]
    (l : List T) (f : T → X → List Y) (hf : ∀ t, Primrec (f t)) :
    Primrec (fun x => l.flatMap (fun t => f t x)) := by
  induction l with
  | nil => exact Primrec.const []
  | cons t l ih => exact Primrec.list_append.comp (hf t) ih

private theorem pr_sumElim {L R T : Type*} [Primcodable L] [Primcodable R] [Primcodable T]
    {f : L → T} {g : R → T} (hf : Primrec f) (hg : Primrec g) :
    Primrec (Sum.elim f g) :=
  (Primrec.sumCasesOn Primrec.id (hf.comp₂ Primrec₂.right)
    (hg.comp₂ Primrec₂.right)).of_eq (fun a => by cases a <;> rfl)

theorem primrec_compileScaledGates {n : ℕ} (zero scale : δ) (nums : Fin n → δ)
    (enc : κ → δ) (henc : Primrec enc) :
    Primrec (compileScaledGates zero scale nums enc) := by
  have hb : Primrec (scaledBlock zero scale nums) := by
    unfold scaledBlock
    apply Primrec.list_append.comp
    · exact Primrec.list_cons.comp (pr_gateConst (pr_scaledId 2 0) (Primrec.const scale))
        (Primrec.list_cons.comp (pr_gateConst (pr_scaledId 3 0) (Primrec.const zero))
          (Primrec.list_cons.comp (pr_gateMul (pr_scaledId 2 0) (pr_scaledId 0 0) (pr_scaledId 1 0))
            (Primrec.list_cons.comp (pr_gateAdd (pr_scaledId 3 n) (pr_scaledId 3 0)
              (pr_scaledId 0 0)) (Primrec.const []))))
    · apply pr_flatMap_const
      intro j
      exact Primrec.list_cons.comp (pr_gateConst (pr_scaledId 5 j) (Primrec.const (nums j)))
        (Primrec.list_cons.comp (pr_gateMul (pr_scaledId 4 j) (pr_scaledId 5 j) (pr_scaledId 6 j))
          (Primrec.list_cons.comp (pr_gateAdd (pr_scaledId 3 j) (pr_scaledId 6 j)
            (pr_scaledId 3 (j.val+1))) (Primrec.const [])))
  have hr : Primrec (scaledRegisters (κ := κ)) := by
    have h3 : Primrec (fun x : ℕ × ℕ × ℕ => [x.1,x.2.1,x.2.2]) :=
      Primrec.list_cons.comp Primrec.fst
        (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
          (Primrec.list_cons.comp (Primrec.snd.comp Primrec.snd) (Primrec.const [])))
    have h1 : Primrec (fun x : ℕ × κ => [x.1]) :=
      Primrec.list_cons.comp Primrec.fst (Primrec.const [])
    exact (pr_sumElim h3 (pr_sumElim h3 h1)).of_eq (fun g => by
      rcases g with ⟨i,j,k⟩ | ⟨i,j,k⟩ | ⟨i,c⟩ <;> rfl)
  have hm : Primrec (scaledMain enc) := by
    have ha : Primrec (fun x : ℕ × ℕ × ℕ =>
        Gate.add (κ := δ) (scaledId x.1 0 0) (scaledId x.2.1 0 0) (scaledId x.2.2 0 0)) :=
      pr_gateAdd ((pr_scaledId 0 0).comp Primrec.fst)
        ((pr_scaledId 0 0).comp (Primrec.fst.comp Primrec.snd))
        ((pr_scaledId 0 0).comp (Primrec.snd.comp Primrec.snd))
    have hm' : Primrec (fun x : ℕ × ℕ × ℕ =>
        Gate.mul (κ := δ) (scaledId x.1 0 0) (scaledId x.2.1 0 0) (scaledId x.2.2 1 0)) :=
      pr_gateMul ((pr_scaledId 0 0).comp Primrec.fst)
        ((pr_scaledId 0 0).comp (Primrec.fst.comp Primrec.snd))
        ((pr_scaledId 1 0).comp (Primrec.snd.comp Primrec.snd))
    have hc : Primrec (fun x : ℕ × κ => Gate.const (scaledId x.1 0 0) (enc x.2)) :=
      pr_gateConst ((pr_scaledId 0 0).comp Primrec.fst) (henc.comp Primrec.snd)
    exact (pr_sumElim ha (pr_sumElim hm' hc)).of_eq (fun g => by
      rcases g with ⟨i,j,k⟩ | ⟨i,j,k⟩ | ⟨i,c⟩ <;> rfl)
  apply Primrec.list_flatMap Primrec.id
  exact (Primrec.list_append.comp (Primrec.list_flatMap hr (hb.comp₂ Primrec₂.right))
    (Primrec.list_cons.comp hm (Primrec.const []))).comp₂ Primrec₂.right

end EffectiveScaled


end ManinBilinear




open scoped BigOperators

namespace ManinBilinear

noncomputable def basisEncode {A : Type*} [CommRing A] {m : ℕ}
    (a : Module.Basis (Fin m) ℤ A) (x : A) : List ℤ :=
  List.ofFn fun i => a.repr x i

@[simp] theorem basisDecode_basisEncode {A : Type*} [CommRing A] {m : ℕ}
    (a : Module.Basis (Fin m) ℤ A) (x : A) : basisDecode a (basisEncode a x) = x := by
  simpa [basisDecode,basisEncode,List.getElem?_ofFn] using a.sum_repr x

private theorem pr_finiteIntSum {X : Type*} [Primcodable X]
    {n : ℕ} {f : Fin n → X → ℤ} (hf : ∀ i, Primrec (f i)) :
    Primrec (fun x => ∑ i, f i x) := by
  induction n with
  | zero =>
    simp only [Fin.sum_univ_zero]
    exact Primrec.const (0 : ℤ)
  | succ n ih =>
    simp only [Fin.sum_univ_succ]
    exact Ripple.BoundedUniversality.BGP.primrec2_int_add.comp (hf 0) (ih (fun i => hf i.succ))

theorem primrec_basisEncode_scaledDecode {A : Type*} [CommRing A] {m n : ℕ}
    (a : Module.Basis (Fin m) ℤ A) (num : Fin n → A) :
    Primrec (fun c => basisEncode a (scaledDecode num c)) := by
  unfold basisEncode
  apply Primrec.list_ofFn
  intro i
  have he (c : List ℤ) :
      a.repr (scaledDecode num c) i =
        ∑ j : Fin n, c[j.val]?.getD 0 * a.repr (num j) i := by
    simp only [scaledDecode,map_sum,map_zsmul,Finsupp.finsetSum_apply,
      Finsupp.smul_apply,Int.zsmul_eq_mul]
  apply Primrec.of_eq (pr_finiteIntSum (f := fun j c =>
    c[j.val]?.getD 0 * a.repr (num j) i) ?_) (fun c => (he c).symm)
  intro j
  exact Ripple.BoundedUniversality.BGP.primrec2_int_mul.comp
    ((Primrec.list_getD (0 : ℤ)).comp Primrec.id (Primrec.const j.val))
    (Primrec.const (a.repr (num j) i))

/-- Undecidability passes to a domain that contains a common nonzero
multiple of a fixed integral basis of the larger ring. -/
theorem not_computablePred_gateSat_of_scaled_basis
    {A S : Type*} [CommRing A] [CommRing S] [IsDomain S] {m n : ℕ}
    (F : A →+* S) (hF : Function.Injective F) (a : Module.Basis (Fin m) ℤ A)
    (b : Module.Basis (Fin n) ℤ S) (scale : A) (hscale : F scale ≠ 0)
    (num : Fin n → A) (hnum : ∀ i, F (num i) = F scale * b i)
    (hS : ¬ ComputablePred (gateSat (basisDecode b))) :
    ¬ ComputablePred (gateSat (basisDecode a)) := by
  let enc (c : List ℤ) := basisEncode a (scaledDecode num c)
  let trans := compileScaledGates (basisEncode a 0) (basisEncode a scale)
    (basisEncode a ∘ num) enc
  have hcomp : Computable trans :=
    (primrec_compileScaledGates _ _ _ enc (primrec_basisEncode_scaledDecode a num)).to_comp
  have hc (gs : List (Gate (List ℤ))) :
      gateSat (basisDecode b) gs ↔ gateSat (basisDecode a) (trans gs) := by
    rw [gateSat_compileScaled_iff _ _ _ _ _ (basisDecode_basisEncode a 0)]
    have he : basisDecode a ∘ enc = scaledDecode num :=
      funext fun c => basisDecode_basisEncode a _
    simpa only [he, Function.comp_apply, basisDecode_basisEncode] using
      gateSat_iff_scaled F hF scale hscale b num hnum gs
  exact fun hA => hS (computablePred_pullback hcomp hc hA)

/-- Exact number-ring arithmetic contract in the verified gate syntax. -/
def KoymansPaganoNumberRings : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ)
    (b : Module.Basis (Fin n) ℤ (NumberField.RingOfIntegers K)),
    ¬ ComputablePred (gateSat (basisDecode b))

theorem koymansPaganoFiniteFreeDomain_of_numberRings
    (h : KoymansPaganoNumberRings) : KoymansPaganoFiniteFreeDomain := by
  intro A _ _ m a
  let : Module.Finite ℤ A := Module.Finite.of_basis a
  let : Module.Free ℤ A := Module.Free.of_basis a
  let : IsAddTorsionFree A := Module.isTorsionFree_int_iff_isAddTorsionFree.mp inferInstance
  let : CharZero A := CharZero.of_isAddTorsionFree A A
  let K := FractionRing A
  let : NumberField K := finiteOrder_numberField A
  let b := Module.finBasis ℤ (NumberField.RingOfIntegers K)
  obtain ⟨d, num, hd, hn⟩ := order_clear_denominators A b
  have hF := orderToIntegers_injective A
  exact not_computablePred_gateSat_of_scaled_basis (orderToIntegers A) hF a b d
    (fun he => hd (hF (he.trans (map_zero _).symm))) num hn (h K _ b)

theorem koymansPaganoFiniteFree_iff_numberRings :
    KoymansPaganoFiniteFree ↔ KoymansPaganoNumberRings := by
  constructor
  · intro h K _ _ n b
    exact h (NumberField.RingOfIntegers K) n b
  · intro h
    exact koymansPaganoFiniteFree_of_domains (koymansPaganoFiniteFreeDomain_of_numberRings h)

theorem manin_bilinear_of_numberRings {m n p : ℕ}
    (B : (Fin m → ℤ) →ₗ[ℤ] (Fin n → ℤ) →ₗ[ℤ] (Fin p → ℤ)) (hB : B ≠ 0)
    (h : KoymansPaganoNumberRings) : ¬ ComputablePred (rawSat B) :=
  manin_bilinear_of_koymans_pagano B hB (koymansPaganoFiniteFree_iff_numberRings.mpr h)

/-- Diophantine definability in the ring of integers of every number field. -/
def NumberRingIntegerDefinitions : Prop :=
  ∀ (K : Type) [Field K] [NumberField K],
    ∃ (n : ℕ) (P : MvPolynomial (Fin (n+1)) (NumberField.RingOfIntegers K)),
      ∀ a : NumberField.RingOfIntegers K,
        (∃ w : Fin n → NumberField.RingOfIntegers K, MvPolynomial.eval (Fin.cons a w) P = 0) ↔
          ∃ z : ℤ, (z : NumberField.RingOfIntegers K) = a

theorem koymansPaganoNumberRings_of_integerDefinitions
    (hℤ : ¬ ComputablePred (gateSat (id : ℤ → ℤ)))
    (h : NumberRingIntegerDefinitions) : KoymansPaganoNumberRings := by
  intro K _ _ n b
  obtain ⟨_, P, hP⟩ := h K
  exact KPDPRM.not_computablePred_gateSat_of_intGateDefinable b hℤ
    (KPDPRM.intGateDefinable_of_fixed_polynomial _ (basisDecode_surjective b) P hP)

theorem manin_bilinear_of_numberRingIntegerDefinitions {m n p : ℕ}
    (B : (Fin m → ℤ) →ₗ[ℤ] (Fin n → ℤ) →ₗ[ℤ] (Fin p → ℤ)) (hB : B ≠ 0)
    (hℤ : ¬ ComputablePred (gateSat (id : ℤ → ℤ)))
    (h : NumberRingIntegerDefinitions) : ¬ ComputablePred (rawSat B) :=
  manin_bilinear_of_numberRings B hB (koymansPaganoNumberRings_of_integerDefinitions hℤ h)

end ManinBilinear



namespace ManinBilinear.KPDPRM

/-- Register 1 is reserved for zero. Every source register uses an even index. -/
def translateFreerGate : Hilbert10.Gate → Gate ℤ
  | .const o c => Gate.const (2*o) (c : ℤ)
  | .copy o i => Gate.add (2*i) 1 (2*o)
  | .add o i j => Gate.add (2*i) (2*j) (2*o)
  | .mul o i j => Gate.mul (2*i) (2*j) (2*o)

def translateFreerPolynomial (p : Hilbert10.PolynomialCode) : List (Gate ℤ) :=
  let s := Hilbert10.compilePoly p p.arity
  s.gates.map translateFreerGate ++ [Gate.const 1 0, Gate.add (2*s.pos) 1 (2*s.neg)]

private theorem translate_holds_iff (g : Hilbert10.Gate) (x : ℕ → ℤ) (y : List ℤ)
    (hz : x 1 = 0) (h : ∀ i ∈ g.out :: g.reads, x (2*i) = y.getD i 0) :
    (translateFreerGate g).Holds id x ↔ g.Holds y := by
  cases g with
  | const o c =>
    have ho := h o (by simp [Hilbert10.Gate.out])
    simp [translateFreerGate, Gate.const, Gate.Holds, Hilbert10.Gate.Holds,
      Hilbert10.Gate.out, Hilbert10.Gate.value, ho]
  | copy o i =>
    have ho := h o (by simp [Hilbert10.Gate.out])
    have hi := h i (by simp [Hilbert10.Gate.reads])
    simp [translateFreerGate, Gate.add, Gate.Holds, Hilbert10.Gate.Holds,
      Hilbert10.Gate.out, Hilbert10.Gate.value, ho, hi, hz, eq_comm]
  | add o i j =>
    have ho := h o (by simp [Hilbert10.Gate.out])
    have hi := h i (by simp [Hilbert10.Gate.reads])
    have hj := h j (by simp [Hilbert10.Gate.reads])
    simp [translateFreerGate, Gate.add, Gate.Holds, Hilbert10.Gate.Holds,
      Hilbert10.Gate.out, Hilbert10.Gate.value, ho, hi, hj, eq_comm]
  | mul o i j =>
    have ho := h o (by simp [Hilbert10.Gate.out])
    have hi := h i (by simp [Hilbert10.Gate.reads])
    have hj := h j (by simp [Hilbert10.Gate.reads])
    simp [translateFreerGate, Gate.mul, Gate.Holds, Hilbert10.Gate.Holds,
      Hilbert10.Gate.out, Hilbert10.Gate.value, ho, hi, hj, eq_comm]

theorem translateFreerPolynomial_correct (p : Hilbert10.PolynomialCode) :
    Hilbert10.IntSolvable p ↔ gateSat (id : ℤ → ℤ) (translateFreerPolynomial p) := by
  let s := Hilbert10.compilePoly p p.arity
  constructor
  · intro h
    obtain ⟨y,hy⟩ := (Hilbert10.intSolvable_iff_systemIntSolvable_quadraticSystem p).mp h
    obtain ⟨hg,he⟩ := (Hilbert10.quadraticSystem_eval_zero_iff p y).mp hy
    let x : ℕ → ℤ := fun i => if i % 2 = 0 then y.getD (i/2) 0 else 0
    have hzero : x 1 = 0 := by simp [x]
    have hx (i : ℕ) : x (2*i) = y.getD i 0 := by simp [x]
    refine ⟨x, fun g hmem => ?_⟩
    rcases List.mem_append.mp hmem with hmem | hmem
    · obtain ⟨g,hg',rfl⟩ := List.mem_map.mp hmem
      exact (translate_holds_iff g x y hzero fun i _ => hx i).mpr (hg g hg')
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl
      · exact hzero
      · change x (2*s.pos) + x 1 = x (2*s.neg)
        simpa [hzero, hx, s] using he
  · rintro ⟨x,hx⟩
    have hzero : x 1 = 0 := hx (Gate.const 1 0) (List.mem_append_right _ (by simp))
    have he : x (2*s.pos) = x (2*s.neg) := by
      have h : x (2*s.pos) + x 1 = x (2*s.neg) :=
        hx (Gate.add (2*s.pos) 1 (2*s.neg)) (List.mem_append_right _ (by simp [s]))
      simpa [hzero] using h
    let y := List.ofFn fun i : Fin s.next => x (2*i.val)
    have hGet (i : ℕ) (hi : i < s.next) : y.getD i 0 = x (2*i) := by
      simp [y, List.getD_eq_getElem?_getD, hi]
    have hg (g : Hilbert10.Gate) (hmem : g ∈ s.gates) : g.Holds y := by
      have hwell := Hilbert10.compilePoly_wellOrdered p p.arity le_rfl
      have hb := hwell.out_lt_and_reads_lt g hmem
      have hout : g.out < s.next := by
        simpa [s, Hilbert10.compilePoly_next] using hb.1
      apply (translate_holds_iff g x y hzero (fun i hi => ?_)).mp
      · exact hx _ (List.mem_append_left _ (List.mem_map.mpr ⟨g,hmem,rfl⟩))
      · rcases List.mem_cons.mp hi with rfl | hi
        · exact (hGet _ hout).symm
        · exact (hGet _ ((hb.2 _ hi).trans hout)).symm
    have hp := hGet s.pos (Hilbert10.compilePoly_pos_lt p p.arity le_rfl)
    have hn := hGet s.neg (Hilbert10.compilePoly_neg_lt p p.arity le_rfl)
    refine ⟨y, ?_⟩
    rw [Hilbert10.compilePoly_sound p p.arity y hg, hp, hn, he, sub_self]

private theorem primrec_sum {L R S : Type*} [Primcodable L] [Primcodable R] [Primcodable S]
    {f : L → S} {g : R → S} (hf : Primrec f) (hg : Primrec g) :
    Primrec (Sum.elim f g) :=
  (Primrec.sumCasesOn Primrec.id (hf.comp₂ Primrec₂.right)
    (hg.comp₂ Primrec₂.right)).of_eq (fun a => by cases a <;> rfl)

private theorem primrec_translateFreerGate : Primrec translateFreerGate := by
  have d := Primrec.nat_double
  have hconst : Primrec (fun p : ℕ × ℕ => Gate.const (2*p.1) (p.2 : ℤ)) :=
    Primrec.sumInr.comp (Primrec.sumInr.comp ((d.comp Primrec.fst).pair
      (Ripple.BoundedUniversality.BGP.primrec_int_ofNat.comp Primrec.snd)))
  have hcopy : Primrec (fun p : ℕ × ℕ => Gate.add (κ := ℤ) (2*p.2) 1 (2*p.1)) :=
    Primrec.sumInl.comp ((d.comp Primrec.snd).pair
      ((Primrec.const (1 : ℕ)).pair (d.comp Primrec.fst)))
  have htriple : Primrec (fun p : ℕ × ℕ × ℕ => (2*p.2.1,2*p.2.2,2*p.1)) :=
    (d.comp (Primrec.fst.comp Primrec.snd)).pair
      ((d.comp (Primrec.snd.comp Primrec.snd)).pair (d.comp Primrec.fst))
  refine ((primrec_sum hconst (primrec_sum hcopy (primrec_sum (Primrec.sumInl.comp htriple)
    (Primrec.sumInr.comp (Primrec.sumInl.comp htriple))))).comp
    (Primrec.of_equiv (e := Hilbert10.Gate.equivSum))).of_eq ?_
  intro g
  cases g <;> rfl

theorem primrec_translateFreerPolynomial : Primrec translateFreerPolynomial := by
  have hc : Primrec (fun p : Hilbert10.PolynomialCode => Hilbert10.compilePoly p p.arity) :=
    Hilbert10.primrec_compilePoly.comp Primrec.id Hilbert10.PolynomialCode.primrec_arity
  have hs : Primrec (fun p : Hilbert10.PolynomialCode =>
      Hilbert10.CompiledPoly.equivProd (Hilbert10.compilePoly p p.arity)) :=
    (Primrec.of_equiv (e := Hilbert10.CompiledPoly.equivProd)).comp hc
  have hpos : Primrec (fun p : Hilbert10.PolynomialCode =>
      2 * (Hilbert10.compilePoly p p.arity).pos) :=
    Primrec.nat_double.comp ((Primrec.fst.comp Primrec.snd).comp hs)
  have hneg : Primrec (fun p : Hilbert10.PolynomialCode =>
      2 * (Hilbert10.compilePoly p p.arity).neg) :=
    Primrec.nat_double.comp ((Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).comp hs)
  have hlast : Primrec (fun p : Hilbert10.PolynomialCode =>
      Gate.add (κ := ℤ) (2*(Hilbert10.compilePoly p p.arity).pos) 1
        (2*(Hilbert10.compilePoly p p.arity).neg)) :=
    Primrec.sumInl.comp (hpos.pair ((Primrec.const (1 : ℕ)).pair hneg))
  unfold translateFreerPolynomial
  exact Primrec.list_append.comp
    (Primrec.list_map (Primrec.fst.comp hs) (primrec_translateFreerGate.comp₂ Primrec₂.right))
    (Primrec.list_cons.comp (Primrec.const (Gate.const 1 (0 : ℤ)))
      (Primrec.list_cons.comp hlast (Primrec.const [])))

theorem not_computablePred_integerGateSat :
    ¬ ComputablePred (gateSat (id : ℤ → ℤ)) :=
  fun h => Hilbert10.not_computablePred_intSolvable
    (computablePred_pullback primrec_translateFreerPolynomial.to_comp
      translateFreerPolynomial_correct h)

end ManinBilinear.KPDPRM


open scoped BigOperators

namespace ManinBilinear

/-- The exact finite-free ring assertion now needs only the universal
number-ring Diophantine definability statement. Integer undecidability
is supplied by the checked DPRM development. -/
theorem koymansPaganoFiniteFree_of_numberRingIntegerDefinitions
    (h : NumberRingIntegerDefinitions) : KoymansPaganoFiniteFree :=
  koymansPaganoFiniteFree_iff_numberRings.mpr
    (koymansPaganoNumberRings_of_integerDefinitions KPDPRM.not_computablePred_integerGateSat h)

theorem manin_bilinear_of_numberRing_integer_definitions {m n p : ℕ}
    (B : (Fin m → ℤ) →ₗ[ℤ] (Fin n → ℤ) →ₗ[ℤ] (Fin p → ℤ)) (hB : B ≠ 0)
    (h : NumberRingIntegerDefinitions) : ¬ ComputablePred (rawSat B) :=
  manin_bilinear_of_koymans_pagano B hB
    (koymansPaganoFiniteFree_of_numberRingIntegerDefinitions h)

private theorem primrec_basisEncode_intCast {R : Type*} [CommRing R] {d : ℕ}
    (b : Module.Basis (Fin d) ℤ R) :
    Primrec (fun c : ℤ => basisEncode b (c : R)) := by
  unfold basisEncode
  apply Primrec.list_ofFn
  intro j
  apply (Ripple.BoundedUniversality.BGP.primrec2_int_mul.comp
    Primrec.id (Primrec.const (b.repr (1 : R) j))).of_eq
  intro c
  rw [show (c : R) = c • (1 : R) by simp [zsmul_eq_mul]]
  simp only [id_eq, map_zsmul, Finsupp.smul_apply, Int.zsmul_eq_mul]

/-- An unconditional consequence for finite-free rings with an integer quotient.
Any unital homomorphism to the integers is automatically surjective. -/
theorem not_computablePred_gateSat_of_integer_quotient
    {R : Type*} [CommRing R] {d : ℕ} (b : Module.Basis (Fin d) ℤ R) (φ : R →+* ℤ) :
    ¬ ComputablePred (gateSat (basisDecode b)) := by
  have hφ : Function.Surjective φ := fun z => ⟨(z : R), by simp⟩
  obtain ⟨k, g, hg⟩ := finite_ideal_generators b (RingHom.ker φ)
  let code := basisEncode b ∘ g
  let lift (z : ℤ) := basisEncode b (z : R)
  let trans := compileQuotientGates (basisEncode b 0) code lift
  have hcomp : Computable trans :=
    (primrec_compileQuotientGates _ _ _ (primrec_basisEncode_intCast b)).to_comp
  have hcode : basisDecode b ∘ code = g := funext fun j => basisDecode_basisEncode b _
  have hker : Ideal.span (Set.range (basisDecode b ∘ code)) = RingHom.ker φ := by rw [hcode, hg]
  have hl (z : ℤ) : φ (basisDecode b (lift z)) = id z := by simp [lift]
  intro hd
  apply KPDPRM.not_computablePred_integerGateSat
  exact computablePred_pullback hcomp (fun gs =>
    (gateSat_compileQuotientGates φ hφ _ _ _ (basisDecode_basisEncode b 0)
      code lift hker hl gs).symm) hd

/-- For maps whose reduced adjoint center admits an integer quotient,
the Manin decision problem is unconditionally undecidable. -/
theorem manin_bilinear_of_center_integer_quotient {m n p : ℕ}
    (B : (Fin m → ℤ) →ₗ[ℤ] (Fin n → ℤ) →ₗ[ℤ] (Fin p → ℤ))
    (φ : Center (reduced B) →+* ℤ) : ¬ ComputablePred (rawSat B) := by
  apply rawSat_reduced_undecidable B
  let C := reduced B
  let (e, f) := reducedBasis B
  have hright (v : RightReduced B) (hv : ∀ u : LeftReduced B, C u v = 0) : v = 0 := by
    have he : (reduced B).flip v = (reduced B).flip 0 :=
      LinearMap.ext (fun u => by simpa [C] using hv u)
    exact reduced_right_injective B he
  obtain ⟨s, g, hg⟩ := adjointGenerators (β := C)
  let b := centerBasis (β := C) hright
  have hneg : Primrec (fun x : ℤ => -x) :=
    (Ripple.BoundedUniversality.BGP.primrec2_int_mul.comp
      (Primrec.const (-1 : ℤ)) Primrec.id).of_eq (fun x => by simp)
  have hcomp := (compileCenterSystem_primrec_of_int
    Ripple.BoundedUniversality.BGP.primrec2_int_add
    Ripple.BoundedUniversality.BGP.primrec2_int_mul hneg C e.2 f.2 g b.2).to_comp
  intro h
  apply not_computablePred_gateSat_of_integer_quotient b.2 φ
  exact computablePred_pullback hcomp
    (fun gs => (compileCenterSystem_correct C e.2 f.2 g b.2
      (reduced_left_injective B) (reduced_right_injective B) hg gs).symm) h

end ManinBilinear

end NumberRingReduction

section NumberRingArithmetic

namespace ManinKP

open Polynomial

/-- The explicit polynomial in Poonen, "Rank stability makes rings of integers
diophantine", Lemma 2.1, has a root modulo every nonzero integer. -/
private theorem exists_int_dvd_guard (c : ℤ) (hc : c ≠ 0) :
    ∃ x : ℤ, c ∣ (2 * x - 1) * (3 * x - 1) := by
  let n := c.natAbs
  have hn : n ≠ 0 := by simpa [n] using hc
  let k := n.factorization 2
  let a : ℕ := 2 ^ k
  let b : ℕ := n / a
  have hab : a * b = n := Nat.ordProj_mul_ordCompl_eq_self n 2
  have h2b : Nat.Coprime 2 b := Nat.coprime_ordCompl Nat.prime_two hn
  have habC : IsCoprime (a : ℤ) (b : ℤ) := by
    exact (h2b.pow_left k).isCoprime
  have h3a : IsCoprime (3 : ℤ) (a : ℤ) := by
    exact ((by decide : Nat.Coprime 3 2).pow_right k).isCoprime
  obtain ⟨r, s, hrs⟩ := habC
  obtain ⟨u, v, huv⟩ := h3a
  obtain ⟨w, z, hwz⟩ := h2b.isCoprime
  let x := u * (s * (b : ℤ)) + w * (r * (a : ℤ))
  have hA : (a : ℤ) ∣ 3 * x - 1 := by
    refine ⟨-v + 3 * r * (w - u), ?_⟩
    rw [show x = u + r * (a : ℤ) * (w - u) by
      dsimp [x]
      rw [show s * (b : ℤ) = 1 - r * (a : ℤ) by linarith]
      ring]
    linear_combination huv
  have hB : (b : ℤ) ∣ 2 * x - 1 := by
    refine ⟨-z + 2 * s * (u - w), ?_⟩
    rw [show x = w + s * (b : ℤ) * (u - w) by
      dsimp [x]
      rw [show r * (a : ℤ) = 1 - s * (b : ℤ) by linarith]
      ring]
    linear_combination hwz
  refine ⟨x, Int.dvd_natAbs_self.trans ?_⟩
  have hProd : ((a : ℤ) * (b : ℤ)) ∣ (2 * x - 1) * (3 * x - 1) := by
    rw [mul_comm (a : ℤ) (b : ℤ)]
    exact mul_dvd_mul hB hA
  exact (by exact_mod_cast hab : (a : ℤ) * (b : ℤ) = (n : ℤ)) ▸ hProd

variable {R : Type*} [CommRing R] [IsDomain R]

/-- A nonzero integral element divides a nonzero rational integer. The
constant coefficient of the minimal polynomial provides the integer. -/
theorem exists_ne_zero_int_dvd_of_isIntegral {a : R} (hi : IsIntegral ℤ a) (ha : a ≠ 0) :
    ∃ c : ℤ, c ≠ 0 ∧ a ∣ (c : R) := by
  let p := minpoly ℤ a
  have hp0 : p.coeff 0 ≠ 0 := by
    intro hz
    have heq : p.divX * X = p := by simpa [hz] using divX_mul_X_add p
    have hzero : aeval a p.divX = 0 := by
      have he := congrArg (aeval a) heq
      change aeval a (p.divX * X) = aeval a p at he
      rw [map_mul, aeval_X, show aeval a p = 0 from minpoly.aeval ℤ a] at he
      exact (mul_eq_zero.mp he).resolve_right ha
    have hmon : p.divX.Monic := by
      have hm : p.leadingCoeff = 1 := (minpoly.monic hi).leadingCoeff
      rwa [← heq, leadingCoeff_mul_X] at hm
    exact (not_le_of_gt (degree_divX_lt (minpoly.ne_zero hi))) (minpoly.min ℤ a hmon hzero)
  refine ⟨p.coeff 0, hp0, -aeval a p.divX, ?_⟩
  have h := congrArg (aeval a) (X_mul_divX_add p)
  change aeval a (X * p.divX + C (p.coeff 0)) = aeval a p at h
  rw [map_add, map_mul, aeval_X, aeval_C, show aeval a p = 0 from minpoly.aeval ℤ a] at h
  rw [algebraMap_int_eq] at h
  rw [mul_neg, eq_neg_iff_add_eq_zero]
  simpa [add_comm] using h

variable [CharZero R]

/-- Uniform Diophantine denominator guard in a characteristic-zero integral
domain integral over the integers. Specializes to every number ring. -/
theorem ne_zero_iff_guard [Algebra.IsIntegral ℤ R] (a : R) :
    a ≠ 0 ↔ ∃ x y : R, (2 * x - 1) * (3 * x - 1) = y * a := by
  constructor
  · intro ha
    obtain ⟨c, hc, hd⟩ := exists_ne_zero_int_dvd_of_isIntegral
      (Algebra.IsIntegral.isIntegral a) ha
    obtain ⟨x, hx⟩ := exists_int_dvd_guard c hc
    have hxR := (algebraMap ℤ R).map_dvd hx
    obtain ⟨y, hy⟩ := hd.trans hxR
    exact ⟨x, y, by simpa [mul_comm] using hy⟩
  · rintro ⟨x, y, h⟩ rfl
    have hh : (2 * x - 1) * (3 * x - 1) = 0 := by simpa using h
    have hnon (k : ℤ) (hk : ¬ IsUnit k) : (k : R) * x - 1 ≠ 0 := by
      intro hz
      have hu : IsUnit (algebraMap ℤ R k) := by
        rw [algebraMap_int_eq]
        exact IsUnit.of_mul_eq_one x (sub_eq_zero.mp hz)
      exact hk ((isUnit_map_iff (algebraMap ℤ R) k).mp hu)
    rcases mul_eq_zero.mp hh with h2 | h3
    · exact hnon 2 (by decide) (by simpa using h2)
    · exact hnon 3 (by decide) (by simpa using h3)

open scoped NumberField in
theorem numberRing_ne_zero_iff_guard (K : Type*) [Field K] [NumberField K]
    (a : 𝓞 K) :
    a ≠ 0 ↔ ∃ x y : 𝓞 K, (2 * x - 1) * (3 * x - 1) = y * a :=
  ne_zero_iff_guard a

section FullRank

variable {M : Type*} [AddCommGroup M] [Module.Finite ℤ M]

/-- The finite-index step used in Poonen's rank-stability argument. This
applies to Mordell–Weil groups, including their torsion. -/
theorem finite_quotient_of_equal_rank (N : Submodule ℤ M)
    (h : Module.finrank ℤ N = Module.finrank ℤ M) : Finite (M ⧸ N) := by
  apply Module.finite_of_fg_torsion
  apply Module.finrank_eq_zero_iff_isTorsion.mp
  have hN := N.finrank_quotient_add_finrank
  rwa [h, Nat.add_eq_right] at hN

/-- A finite-index subgroup contains all multiples by one fixed positive
integer. The multiplier is the order of the quotient group. -/
theorem exists_pos_nsmul_mem_of_equal_rank (N : Submodule ℤ M)
    (h : Module.finrank ℤ N = Module.finrank ℤ M) :
    ∃ d : ℕ, 0 < d ∧ ∀ x : M, d • x ∈ N := by
  let : Finite (M ⧸ N) := finite_quotient_of_equal_rank N h
  let : Fintype (M ⧸ N) := Fintype.ofFinite _
  refine ⟨Fintype.card (M ⧸ N), Fintype.card_pos, fun x => ?_⟩
  rw [← Submodule.Quotient.mk_eq_zero]
  change N.mkQ (Fintype.card (M ⧸ N) • x) = 0
  rw [map_nsmul]
  exact card_nsmul_eq_zero

/-- Poonen's finite union of translates of the full ambient multiple subgroup.
In the Mordell–Weil application the translating points are fixed constants,
and the variable ranges over the ambient group. -/
theorem exists_finite_nsmul_cosets_of_equal_rank (N : Submodule ℤ M)
    (h : Module.finrank ℤ N = Module.finrank ℤ M) :
    ∃ (d : ℕ) (C : Finset M), 0 < d ∧
      ∀ x : M, x ∈ N ↔ ∃ c ∈ C, ∃ y : M, x = c + d • y := by
  classical
  obtain ⟨d, hd, hmul⟩ := exists_pos_nsmul_mem_of_equal_rank N h
  let H : AddSubgroup M := (nsmulAddMonoidHom (α := M) d).range
  let : AddGroup.FG M := Module.Finite.iff_addGroup_fg.mp inferInstance
  let : H.FiniteIndex := AddSubgroup.finiteIndex_range_nsmulAddMonoidHom_of_fg M hd.ne'
  let q : M →+ M ⧸ H := QuotientAddGroup.mk' H
  let Cq := Set.range fun c : N => q c
  let : Fintype Cq := Fintype.ofFinite _
  let rep (z : Cq) : N := z.property.choose
  have hrep (z : Cq) : q (rep z) = z := z.property.choose_spec
  refine ⟨d, Finset.univ.image fun z : Cq => (rep z : M), hd, fun x => ⟨?_, ?_⟩⟩
  · intro hx
    let z : Cq := ⟨q x, ⟨⟨x, hx⟩, rfl⟩⟩
    have he : q x = q (rep z) := (hrep z).symm
    have hzero : q (x - rep z) = 0 := by rw [map_sub, he, sub_self]
    have hH : x - rep z ∈ H := by
      exact (QuotientAddGroup.eq_zero_iff (x - (rep z : M))).mp hzero
    obtain ⟨y, hy⟩ := hH
    refine ⟨rep z, Finset.mem_image.mpr ⟨z, Finset.mem_univ _, rfl⟩, y, ?_⟩
    rw [show d • y = x - rep z from hy, add_sub_cancel]
  · rintro ⟨c, hc, y, rfl⟩
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hc
    exact N.add_mem (rep z).property (hmul y)

end FullRank

section GaloisIntersection

universe u

open NumberField
open scoped NumberField

/-- In a Galois number field, the maximal totally real subfield is the
intersection of a finite family of index-two subfields, as in Shlapentokh's
reduction reproduced in Poonen, Theorem 5.1. The family may be empty. -/
theorem exists_finite_quadratic_intersection (K : Type u) [Field K] [NumberField K]
    [IsGalois ℚ K] :
    ∃ (ι : Type u) (_ : Finite ι) (L : ι → IntermediateField ℚ K),
      (∀ i, Module.finrank (L i) K = 2) ∧
      ∀ x : K, x ∈ maximalRealSubfield K ↔ ∀ i, x ∈ L i := by
  let I := {σ : K ≃ₐ[ℚ] K // ∃ φ : K →+* ℂ, ComplexEmbedding.IsConj φ σ ∧ σ ≠ 1}
  let L (i : I) : IntermediateField ℚ K := IntermediateField.fixedField (Subgroup.zpowers i.val)
  refine ⟨I, inferInstance, L, ?_, fun x => ?_⟩
  · intro i
    obtain ⟨φ, hφ, hne⟩ := i.property
    change Module.finrank (IntermediateField.fixedField (Subgroup.zpowers i.val)) K = 2
    rw [IntermediateField.finrank_fixedField_eq_card, Nat.card_zpowers]
    exact ComplexEmbedding.orderOf_isConj_two_of_ne_one hφ hne
  · rw [mem_maximalRealSubfield_iff]
    constructor
    · intro hx i
      obtain ⟨φ, hφ, _⟩ := i.property
      have heq : i.val x = x := φ.injective ((hφ.eq x).trans (hx φ))
      exact (IntermediateField.mem_fixedField_iff _ x).mpr fun σ hσ =>
        smul_eq_self_of_mem_zpowers hσ heq
    · intro hx φ
      obtain ⟨σ, hσ⟩ := ComplexEmbedding.exists_comp_symm_eq_of_comp_eq
        (k := ℚ) φ (ComplexEmbedding.conjugate φ) (Subsingleton.elim _ _)
      have hconj : ComplexEmbedding.IsConj φ σ.symm := hσ.symm
      by_cases he : σ.symm = 1
      · have hr := (ComplexEmbedding.isConj_one_iff).mp (he ▸ hconj)
        exact RingHom.congr_fun (ComplexEmbedding.isReal_iff.mp hr) x
      · let i : I := ⟨σ.symm, φ, hconj, he⟩
        have hfix := (IntermediateField.mem_fixedField_iff _ x).mp (hx i)
          i.val (Subgroup.mem_zpowers _)
        exact (hconj.eq x).symm.trans (congrArg φ hfix)

/-- Being the image of an integer of the smaller field is equivalent to
having its underlying value in that field. -/
theorem ringOfIntegers_mem_range_iff {K L : Type*} [Field K] [Field L]
    (f : K →+* L) (x : 𝓞 L) :
    x ∈ Set.range (RingOfIntegers.mapRingHom f) ↔ (x : L) ∈ Set.range f := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨(y : K), rfl⟩
  · rintro ⟨y, hy⟩
    have hi : IsIntegral ℤ y :=
      (isIntegral_algHom_iff f.toIntAlgHom f.injective).mp (hy ▸ x.property)
    exact ⟨⟨y, hi⟩, RingOfIntegers.ext hy⟩

/-- The intersection of the rings of integers of the quadratic fixed
fields is the ring of integers of the maximal totally real subfield,
viewed inside the ambient ring of integers. -/
theorem ringOfIntegers_finite_quadratic_intersection (K : Type u) [Field K]
    [NumberField K] [IsGalois ℚ K] :
    ∃ (ι : Type u) (_ : Finite ι) (L : ι → IntermediateField ℚ K),
      (∀ i, Module.finrank (L i) K = 2) ∧
      ∀ x : 𝓞 K,
        x ∈ Set.range (RingOfIntegers.mapRingHom (maximalRealSubfield K).subtype) ↔
          ∀ i, x ∈ Set.range (RingOfIntegers.mapRingHom (L i).val.toRingHom) := by
  obtain ⟨ι, hf, L, hd, hL⟩ := exists_finite_quadratic_intersection K
  refine ⟨ι, hf, L, hd, fun x => ?_⟩
  simp only [ringOfIntegers_mem_range_iff]
  have hc (E : Subfield K) :
      (x : K) ∈ Set.range E.subtype ↔ (x : K) ∈ E := by
    exact ⟨fun ⟨y, hy⟩ => hy ▸ y.property, fun h => ⟨⟨(x : K), h⟩, rfl⟩⟩
  exact (hc _).trans ((hL (x : K)).trans (forall_congr' fun i => (hc (L i).toSubfield).symm))

end GaloisIntersection

section SystemDiophantine

universe u v
variable {R : Type u} [CommRing R]

/-- Definability by finitely many polynomial equations with finitely many
existentially quantified witnesses and one free variable. -/
def SystemDiophantine (S : Set R) : Prop :=
  ∃ (m n : Type v) (_ : Finite m) (_ : Finite n) (p : m → MvPolynomial (Unit ⊕ n) R),
    ∀ x : R, x ∈ S ↔ ∃ w : n → R, ∀ j : m, MvPolynomial.eval (Sum.elim (fun _ => x) w) (p j) = 0

/-- A finite intersection of polynomial-system predicates has an explicit
polynomial-system definition, by giving each formula its own witness variables. -/
theorem systemDiophantine_iInter {ι : Type v} [Finite ι] (S : ι → Set R)
    (h : ∀ i, SystemDiophantine.{u,v} (S i)) :
    SystemDiophantine.{u,v} (⋂ i, S i) := by
  classical
  choose m n hm hn p hp using h
  let : ∀ i, Finite (m i) := hm
  let : ∀ i, Finite (n i) := hn
  let f (i : ι) : Unit ⊕ n i → Unit ⊕ (Σ i, n i) := Sum.map id (Sigma.mk i)
  refine ⟨Σ i, m i, Σ i, n i, inferInstance, inferInstance,
    fun j => MvPolynomial.rename (f j.1) (p j.1 j.2), fun x => ?_⟩
  have he (w : (Σ i, n i) → R) (i : ι) :
      Sum.elim (fun _ : Unit => x) w ∘ f i =
      Sum.elim (fun _ : Unit => x) (fun k => w ⟨i, k⟩) := by
    funext a
    cases a <;> rfl
  constructor
  · intro hx
    have hs (i : ι) := (hp i x).mp (Set.mem_iInter.mp hx i)
    choose w hw using hs
    refine ⟨fun j => w j.1 j.2, fun j => ?_⟩
    rw [MvPolynomial.eval_rename, he]
    exact hw j.1 j.2
  · rintro ⟨w, hw⟩
    apply Set.mem_iInter.mpr
    intro i
    refine (hp i x).mpr ⟨fun k => w ⟨i, k⟩, fun j => ?_⟩
    simpa only [MvPolynomial.eval_rename, he] using hw ⟨i, j⟩

open NumberField
open scoped NumberField

/-- The finite-intersection step of Shlapentokh's descent, for predicates
given by finite existential polynomial systems. -/
theorem systemDiophantine_realRing_of_quadratic (K : Type u) [Field K] [NumberField K]
    [IsGalois ℚ K]
    (h : ∀ L : IntermediateField ℚ K, Module.finrank L K = 2 →
      SystemDiophantine.{u,u} (Set.range (RingOfIntegers.mapRingHom L.val.toRingHom))) :
    SystemDiophantine.{u,u}
      (Set.range (RingOfIntegers.mapRingHom (maximalRealSubfield K).subtype)) := by
  obtain ⟨ι, hf, L, hd, he⟩ := ringOfIntegers_finite_quadratic_intersection K
  let : Finite ι := hf
  let S (i : ι) : Set (𝓞 K) := Set.range (RingOfIntegers.mapRingHom (L i).val.toRingHom)
  have hE : Set.range (RingOfIntegers.mapRingHom (maximalRealSubfield K).subtype) =
      ⋂ i, S i := Set.ext fun x => (he x).trans Set.mem_iInter.symm
  rw [hE]
  exact systemDiophantine_iInter S fun i => h (L i) (hd i)

end SystemDiophantine

end ManinKP

end NumberRingArithmetic

section GaloisDescent

namespace ManinKP

universe u v w
variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]

/-- An existential polynomial definition over a smaller ring transfers to a larger
ring by imposing membership in the smaller ring on each input and witness. -/
theorem systemDiophantine_image (f : A →+* B) (hf : Function.Injective f)
    (hR : SystemDiophantine.{v,w} (Set.range f)) {S : Set A}
    (hS : SystemDiophantine.{u,w} S) : SystemDiophantine.{v,w} (f '' S) := by
  classical
  obtain ⟨m, n, hm, hn, p, hp⟩ := hS
  obtain ⟨r, s, hr, hs, q, hq⟩ := hR
  let := hm
  let := hn
  let := hr
  let := hs
  let W := n ⊕ ((Unit ⊕ n) × s)
  let j : Unit ⊕ n → Unit ⊕ W := Sum.map id Sum.inl
  let k (a : Unit ⊕ n) : Unit ⊕ s → Unit ⊕ W :=
    Sum.elim (fun _ => j a) (fun i => Sum.inr (Sum.inr (a, i)))
  let pol : m ⊕ ((Unit ⊕ n) × r) → MvPolynomial (Unit ⊕ W) B :=
    Sum.elim (fun i => MvPolynomial.rename j (MvPolynomial.map f (p i)))
      (fun z => MvPolynomial.rename (k z.1) (q z.2))
  refine ⟨m ⊕ ((Unit ⊕ n) × r), W, inferInstance, inferInstance, pol, fun b => ?_⟩
  let atB (b : B) (z : W → B) : Unit ⊕ W → B := Sum.elim (fun _ => b) z
  have hj (z : W → B) : atB b z ∘ j =
      Sum.elim (fun _ => b) (fun i => z (Sum.inl i)) := by
    funext a
    cases a <;> rfl
  have hk (z : W → B) (a : Unit ⊕ n) : atB b z ∘ k a =
      Sum.elim (fun _ => (atB b z ∘ j) a) (fun i => z (Sum.inr (a, i))) := by
    funext i
    cases i <;> rfl
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨y, hy⟩ := (hp a).mp ha
    let x : Unit ⊕ n → A := Sum.elim (fun _ => a) y
    have hs (i : Unit ⊕ n) := (hq (f (x i))).mp ⟨x i, rfl⟩
    choose w hw using hs
    let z : W → B := Sum.elim (f ∘ y) (fun i => w i.1 i.2)
    have he : atB (f a) z ∘ j = f ∘ x := by
      funext i
      cases i <;> rfl
    refine ⟨z, fun i => ?_⟩
    change MvPolynomial.eval (atB (f a) z) (pol i) = 0
    cases i with
    | inl i =>
      change MvPolynomial.eval (atB (f a) z)
        (MvPolynomial.rename j (MvPolynomial.map f (p i))) = 0
      rw [MvPolynomial.eval_rename, he, ← MvPolynomial.map_eval, hy i, map_zero]
    | inr i =>
      change MvPolynomial.eval (atB (f a) z) (MvPolynomial.rename (k i.1) (q i.2)) = 0
      rw [MvPolynomial.eval_rename]
      have hk' : atB (f a) z ∘ k i.1 =
          Sum.elim (fun _ => f (x i.1)) (w i.1) := by
        funext t
        cases t with
        | inl t => exact congrFun he i.1
        | inr t => rfl
      rw [hk']
      exact hw i.1 i.2
  · rintro ⟨z, hz⟩
    have hmem (i : Unit ⊕ n) : (atB b z ∘ j) i ∈ Set.range f := by
      apply (hq _).mpr
      refine ⟨fun t => z (Sum.inr (i, t)), fun l => ?_⟩
      have h := hz (Sum.inr (i, l))
      change MvPolynomial.eval (atB b z) (MvPolynomial.rename (k i) (q l)) = 0 at h
      rwa [MvPolynomial.eval_rename, hk] at h
    choose x hx using hmem
    let a : A := x (Sum.inl ())
    let y : n → A := x ∘ Sum.inr
    have he : atB b z ∘ j = f ∘ (Sum.elim (fun _ => a) y) := by
      funext i
      cases i with
      | inl i => cases i; exact (hx _).symm
      | inr i => exact (hx _).symm
    refine ⟨a, (hp a).mpr ⟨y, fun i => ?_⟩, hx (Sum.inl ())⟩
    have h := hz (Sum.inl i)
    change MvPolynomial.eval (atB b z)
      (MvPolynomial.rename j (MvPolynomial.map f (p i))) = 0 at h
    rw [MvPolynomial.eval_rename, he, ← MvPolynomial.map_eval, ← map_zero f] at h
    exact hf h

def integerImage (R : Type*) [CommRing R] : Set R := Set.range fun z : ℤ => (z : R)

theorem systemDiophantine_integerImage_of_range (f : A →+* B)
    (hf : Function.Injective f)
    (hR : SystemDiophantine.{v,w} (Set.range f))
    (hZ : SystemDiophantine.{u,w} (integerImage A)) :
    SystemDiophantine.{v,w} (integerImage B) := by
  have h := systemDiophantine_image f hf hR hZ
  have he : f '' integerImage A = integerImage B := by
    ext b
    constructor
    · rintro ⟨a, ⟨z, rfl⟩, rfl⟩
      exact ⟨z, (map_intCast f z).symm⟩
    · rintro ⟨z, rfl⟩
      exact ⟨(z : A), ⟨z, rfl⟩, map_intCast f z⟩
  rwa [he] at h

end ManinKP


open scoped BigOperators NumberField
open NumberField

namespace ManinKP

section Descent

universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- Applying a linear map coefficientwise after substitution commutes with
evaluating at base-ring inputs. -/
private theorem eval_linear_coefficients {σ : Type u} (t : A →ₗ[R] R)
    (q : MvPolynomial σ A) (w : σ → R) :
    MvPolynomial.eval w
      (∑ s ∈ q.support, MvPolynomial.monomial s (t (q.coeff s))) =
    t (MvPolynomial.eval (algebraMap R A ∘ w) q) := by
  classical
  calc
    _ = ∑ s ∈ q.support, t (q.coeff s) * s.prod (fun i e => w i ^ e) := by
      simp [MvPolynomial.eval_monomial]
    _ = t (∑ s ∈ q.support, q.coeff s *
        s.prod (fun i e => (algebraMap R A ∘ w) i ^ e)) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro s _
      have he : s.prod (fun i e => (algebraMap R A ∘ w) i ^ e) =
          algebraMap R A (s.prod fun i e => w i ^ e) := by
        simp [Finsupp.prod]
      rw [he, mul_comm (q.coeff s), ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
    _ = _ := by congr 1

/-- Finite existential polynomial systems descend along a ring map when the
extension has a finite spanning family and finitely many linear zero tests. -/
theorem systemDiophantine_preimage_of_linear_tests
    {I J : Type u} [Fintype I] [Finite J]
    (b : I → A) (t : J → A →ₗ[R] R)
    (hb : Function.Surjective (fun c : I → R => ∑ i, c i • b i))
    (ht : ∀ z : A, (∀ j, t j z = 0) → z = 0)
    {S : Set A} (h : SystemDiophantine.{u,u} S) :
    SystemDiophantine.{u,u} ((algebraMap R A) ⁻¹' S) := by
  classical
  obtain ⟨m, n, hm, hn, p, hp⟩ := h
  let : Finite m := hm
  let : Finite n := hn
  let σ := Unit ⊕ (n × I)
  let g : Unit ⊕ n → MvPolynomial σ A :=
    Sum.elim (fun _ => MvPolynomial.X (Sum.inl ())) fun k =>
      ∑ i, MvPolynomial.C (b i) * MvPolynomial.X (Sum.inr (k, i))
  let q (l : m) := MvPolynomial.eval₂ MvPolynomial.C g (p l)
  let Q (j : m × J) : MvPolynomial σ R :=
    ∑ s ∈ (q j.1).support, MvPolynomial.monomial s (t j.2 ((q j.1).coeff s))
  let lift (w : n × I → R) (k : n) : A := ∑ i, w (k, i) • b i
  let ev (x : R) (w : n × I → R) : σ → R := Sum.elim (fun _ => x) w
  have he (x : R) (w : n × I → R) (j : m × J) :
      MvPolynomial.eval (ev x w) (Q j) =
      t j.2 (MvPolynomial.eval (Sum.elim (fun _ => algebraMap R A x) (lift w)) (p j.1)) := by
    rw [show Q j = _ from rfl, eval_linear_coefficients]
    congr 1
    change MvPolynomial.eval (algebraMap R A ∘ ev x w)
      (MvPolynomial.eval₂ MvPolynomial.C g (p j.1)) = _
    rw [← MvPolynomial.eval_assoc]
    congr 2
    funext v
    cases v with
    | inl e => cases e; simp [g, ev, Function.comp_apply]
    | inr k =>
      simp [g, ev, lift, Function.comp_apply, Algebra.smul_def, mul_comm]
  refine ⟨m × J, n × I, inferInstance, inferInstance, Q, fun x => ?_⟩
  constructor
  · intro hx
    obtain ⟨w, hw⟩ := (hp (algebraMap R A x)).mp hx
    choose c hc using fun k => hb (w k)
    let w' : n × I → R := fun k => c k.1 k.2
    have hw' : lift w' = w := funext hc
    exact ⟨w', fun j => by
      change MvPolynomial.eval (ev x w') (Q j) = 0
      rw [he, hw', hw, map_zero]⟩
  · rintro ⟨w, hw⟩
    apply (hp (algebraMap R A x)).mpr
    refine ⟨lift w, fun l => ht _ fun j => ?_⟩
    exact (he x w (l,j)).symm.trans (hw (l,j))

end Descent

section NumberRings

universe u
variable (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]

private noncomputable def integerTrace (v : 𝓞 L) : 𝓞 L →ₗ[𝓞 K] 𝓞 K where
  toFun x := ⟨Algebra.trace K L ((x : L) * (v : L)), by
    let : IsScalarTower ℤ K L := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
    exact Algebra.isIntegral_trace ((x : 𝓞 L).property.mul v.property)⟩
  map_add' x y := Subtype.ext (by
    change Algebra.trace K L (((x : L) + (y : L)) * (v : L)) =
      Algebra.trace K L ((x : L) * (v : L)) + Algebra.trace K L ((y : L) * (v : L))
    rw [add_mul, map_add])
  map_smul' c x := Subtype.ext (by
    change Algebra.trace K L
      (algebraMap K L (c : K) * (x : L) * (v : L)) =
        (c : K) * Algebra.trace K L ((x : L) * (v : L))
    rw [mul_assoc]
    simpa only [Algebra.smul_def, smul_eq_mul, Algebra.algebraMap_self_apply] using (Algebra.trace K L).map_smul (c : K) ((x : L) * (v : L)))

private theorem integerTrace_separates (x : 𝓞 L)
    (hx : ∀ i, integerTrace K L (RingOfIntegers.basis L i) x = 0) : x = 0 := by
  let : IsScalarTower ℚ K L := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  let t := (Algebra.traceForm K L (x : L)).restrictScalars ℚ
  have ht : t = 0 := by
    apply (NumberField.integralBasis L).ext
    intro i
    change Algebra.traceForm K L (x : L) (NumberField.integralBasis L i) = 0
    rw [NumberField.integralBasis_apply, Algebra.traceForm_apply]
    exact congrArg Subtype.val (hx i)
  exact Subtype.ext ((traceForm_nondegenerate K L).1 _ fun y =>
    LinearMap.congr_fun ht y)

/-- Restrict a Diophantine set over a larger number ring to its preimage in
a smaller number ring. The relative ring of integers need not be free. -/
theorem systemDiophantine_ringOfIntegers_algebraMap_preimage {S : Set (𝓞 L)}
    (h : SystemDiophantine.{u,u} S) :
    SystemDiophantine.{u,u} ((algebraMap (𝓞 K) (𝓞 L)) ⁻¹' S) := by
  classical
  let I := Module.Free.ChooseBasisIndex ℤ (𝓞 L)
  let : Fintype I := Fintype.ofFinite I
  let b := RingOfIntegers.basis L
  apply systemDiophantine_preimage_of_linear_tests b (fun i => integerTrace K L (b i))
  · intro x
    refine ⟨fun i => (b.repr x i : 𝓞 K), ?_⟩
    simp only [Int.cast_smul_eq_zsmul]
    exact b.sum_repr x
  · exact integerTrace_separates K L
  · exact h

omit [Algebra K L] in
/-- A ring-hom formulation of restriction for later field descent. -/
theorem systemDiophantine_ringOfIntegers_preimage (f : K →+* L) {S : Set (𝓞 L)}
    (h : SystemDiophantine.{u,u} S) :
    SystemDiophantine.{u,u} (RingOfIntegers.mapRingHom f ⁻¹' S) := by
  let : Algebra K L := f.toAlgebra
  exact systemDiophantine_ringOfIntegers_algebraMap_preimage K L h

end NumberRings
end ManinKP


namespace ManinBilinear.KPDPRM

section
variable {R κ : Type*} [CommRing R]

private theorem wellOrdered_append_system (G H : List (Gate κ)) (start : ℕ)
    (hG : WellOrdered start G) (hH : WellOrdered (start + G.length) H) :
    WellOrdered start (G ++ H) := by
  induction G generalizing start with
  | nil => simpa using hH
  | cons g G ih =>
    obtain ⟨ho, hr, ht⟩ := hG
    exact ⟨ho, hr, ih (start + 1) ht (by
      convert hH using 1; simp; omega)⟩

private theorem evalTape_append_system (decode : κ → R) (G H : List (Gate κ)) (x : ℕ → R) :
    evalTape decode (G ++ H) x = evalTape decode H (evalTape decode G x) := by
  induction G generalizing x with
  | nil => rfl
  | cons g G ih => exact ih _

/-- Append disjoint tapes above the shared input registers. Every polynomial
is evaluated on the original common input, including all witness registers. -/
private theorem exists_tape_of_polynomial_list (decode : κ → R)
    (hdecode : Function.Surjective decode) {n : ℕ} (ps : List (MvPolynomial (Fin n) R)) :
    ∀ start ≥ n, ∃ (G : List (Gate κ)) (ks : List ℕ),
      WellOrdered start G ∧ (∀ k ∈ ks, k < start + G.length) ∧
      ∀ x : ℕ → R,
        (∀ k ∈ ks, evalTape decode G x k = 0) ↔
          (∀ p ∈ ps, MvPolynomial.eval (fun i : Fin n => x i) p = 0) := by
  induction ps with
  | nil =>
    intro start _
    exact ⟨[], [], by simp [WellOrdered], by simp, fun x => by simp⟩
  | cons p ps ih =>
    intro start hs
    obtain ⟨G, k, hG, hk, evG⟩ := exists_tape_of_polynomial decode hdecode p start hs
    obtain ⟨H, ks, hH, hks, evH⟩ := ih (start + G.length) (by omega)
    refine ⟨G ++ H, k :: ks, wellOrdered_append_system G H start hG hH, ?_, fun x => ?_⟩
    · intro i hi
      simp only [List.length_append]
      rcases List.mem_cons.mp hi with rfl | hi
      · omega
      · have := hks i hi
        omega
    · have hInputs : (fun i : Fin n => evalTape decode G x i) = fun i : Fin n => x i :=
        funext fun i => evalTape_agrees decode G start hG x i (lt_of_lt_of_le i.isLt hs)
      simp only [List.forall_mem_cons, evalTape_append_system,
        evalTape_agrees decode H _ hH _ k hk, evG, evH, hInputs]

/-- Compile a fixed finite polynomial list, sharing its free variable and all
witness variables, with register zero holding the free variable. -/
theorem exists_gates_of_fixed_polynomial_list (decode : κ → R)
    (hdecode : Function.Surjective decode) {n : ℕ}
    (ps : List (MvPolynomial (Fin (n + 1)) R)) :
    ∃ D : List (Gate κ), ∀ a : R,
      (∃ x : ℕ → R, x 0 = a ∧ ∀ g ∈ D, g.Holds decode x) ↔
      (∃ w : Fin n → R, ∀ p ∈ ps, MvPolynomial.eval (Fin.cons a w) p = 0) := by
  obtain ⟨zero, hz⟩ := hdecode 0
  obtain ⟨G, ks, hG, _, evG⟩ :=
    exists_tape_of_polynomial_list decode hdecode ps (n + 1) le_rfl
  refine ⟨compileTape zero G ks, fun a => ?_⟩
  constructor
  · rintro ⟨x, h0, hx⟩
    have hG' : ∀ g ∈ G, g.Holds decode x :=
      fun g hg => hx g (List.mem_append_left _ hg)
    have hAll : ∀ k ∈ ks, evalTape decode G x k = 0 := by
      intro k hk
      have hlast : (Gate.const k zero).Holds decode x :=
        hx _ (List.mem_append_right _ (List.mem_map.mpr ⟨k, hk, rfl⟩))
      rw [evalTape_eq_of_holds decode G x hG']
      exact hlast.trans hz
    have hInput : Fin.cons a (fun i : Fin n => x i.succ) =
        (fun i : Fin (n + 1) => x i) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using h0.symm
      · simp
    exact ⟨fun i => x i.succ, hInput ▸ (evG x).mp hAll⟩
  · rintro ⟨w, hw⟩
    let v : Fin (n + 1) → R := Fin.cons a w
    let x : ℕ → R := fun i => if h : i < n + 1 then v ⟨i,h⟩ else 0
    have hex : (fun i : Fin (n + 1) => x i) = v := by
      funext i
      simp only [x, dif_pos i.isLt]
    have hAll := (evG x).mpr (show ∀ p ∈ ps,
      MvPolynomial.eval (fun i : Fin (n + 1) => x i) p = 0 by rwa [hex])
    refine ⟨evalTape decode G x, ?_, ?_⟩
    · rw [evalTape_agrees decode G (n + 1) hG _ 0 (by omega)]
      simp [x, v]
    · intro g hg
      unfold compileTape at hg
      rcases List.mem_append.mp hg with hg | hg
      · exact evalTape_holds decode G (n + 1) hG x g hg
      · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hg
        change evalTape decode G x k = decode zero
        rw [hz]
        exact hAll k hk

universe v

/-- Translate a finite existential polynomial system with arbitrary finite
index types to a finite arithmetic-gate formula over the same ring. -/
theorem exists_gates_of_systemDiophantine (decode : κ → R)
    (hdecode : Function.Surjective decode) {S : Set R}
    (hS : ManinKP.SystemDiophantine.{_, v} S) :
    ∃ D : List (Gate κ), ∀ a : R,
      (∃ x : ℕ → R, x 0 = a ∧ ∀ g ∈ D, g.Holds decode x) ↔ a ∈ S := by
  classical
  obtain ⟨m, n, hm, hn, p, hp⟩ := hS
  let : Fintype m := Fintype.ofFinite m
  let : Fintype n := Fintype.ofFinite n
  let em := Fintype.equivFin m
  let en := Fintype.equivFin n
  let r : Unit ⊕ n → Fin (Fintype.card n + 1) :=
    Sum.elim (fun _ => 0) (fun i => (en i).succ)
  let ps := List.ofFn (fun j => MvPolynomial.rename r (p (em.symm j)))
  obtain ⟨D, hD⟩ := exists_gates_of_fixed_polynomial_list decode hdecode ps
  refine ⟨D, fun a => ?_⟩
  rw [hD a, hp a]
  have hInput (w : Fin (Fintype.card n) → R) :
      Fin.cons a w ∘ r = Sum.elim (fun _ : Unit => a) (w ∘ en) := by
    funext i
    cases i <;> simp [r, Function.comp_def]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w ∘ en, fun j => ?_⟩
    have hj : MvPolynomial.rename r (p j) ∈ ps := by
      apply List.mem_ofFn.mpr
      exact ⟨em j, by simp⟩
    simpa only [MvPolynomial.eval_rename, hInput] using hw _ hj
  · rintro ⟨w, hw⟩
    refine ⟨w ∘ en.symm, fun q hq => ?_⟩
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hq
    rw [MvPolynomial.eval_rename, hInput]
    simpa [Function.comp_def] using hw (em.symm j)

/-- An existential polynomial system defining the integer image is already
sufficient for the verified integer-to-ring undecidability transfer. -/
theorem intGateDefinable_of_systemDiophantine (decode : κ → R)
    (hdecode : Function.Surjective decode)
    (h : ManinKP.SystemDiophantine.{_, v} (Set.range (Int.cast : ℤ → R))) :
    IntGateDefinable decode :=
  exists_gates_of_systemDiophantine decode hdecode h

end
end ManinBilinear.KPDPRM


namespace ManinKP

open scoped BigOperators NumberField
open NumberField

universe u v

section LinearCombination

variable {R : Type u} [CommRing R] {ι : Type v} [Fintype ι]

/-- Finite linear combinations with coefficients in a Diophantine set are
Diophantine. The coefficient equations receive separate witness variables. -/
theorem systemDiophantine_linearCombination (b : ι → R) {S : Set R}
    (hS : SystemDiophantine.{u, v} S) :
    SystemDiophantine.{u, v}
      {x | ∃ c : ι → R, (∀ i, c i ∈ S) ∧ ∑ i, c i * b i = x} := by
  classical
  obtain ⟨m, n, hm, hn, p, hp⟩ := hS
  let : Finite m := hm
  let : Finite n := hn
  let W := ι ⊕ (ι × n)
  let r (i : ι) : Unit ⊕ n → Unit ⊕ W :=
    Sum.elim (fun _ => Sum.inr (Sum.inl i)) (fun j => Sum.inr (Sum.inr (i, j)))
  let q : Unit ⊕ (ι × m) → MvPolynomial (Unit ⊕ W) R :=
    Sum.elim
      (fun _ => (∑ i, MvPolynomial.X (Sum.inr (Sum.inl i)) * MvPolynomial.C (b i)) -
        MvPolynomial.X (Sum.inl ()))
      (fun j => MvPolynomial.rename (r j.1) (p j.2))
  refine ⟨Unit ⊕ (ι × m), W, inferInstance, inferInstance, q, fun x => ?_⟩
  let val (w : W → R) : Unit ⊕ W → R := Sum.elim (fun _ => x) w
  have hsum (w : W → R) :
      MvPolynomial.eval (val w) (q (.inl ())) = (∑ i, w (.inl i) * b i) - x := by
    simp [q, val]
  have hcoeff (w : W → R) (i : ι) (j : m) :
      MvPolynomial.eval (val w) (q (.inr (i, j))) =
        MvPolynomial.eval (Sum.elim (fun _ : Unit => w (.inl i)) (fun k => w (.inr (i, k))))
          (p j) := by
    change MvPolynomial.eval (val w) (MvPolynomial.rename (r i) (p j)) = _
    rw [MvPolynomial.eval_rename]
    have he : val w ∘ r i =
        Sum.elim (fun _ : Unit => w (.inl i)) (fun k => w (.inr (i, k))) := by
      funext a
      cases a <;> rfl
    rw [he]
  change (∃ c : ι → R, (∀ i, c i ∈ S) ∧ ∑ i, c i * b i = x) ↔
    ∃ w : W → R, ∀ j, MvPolynomial.eval (val w) (q j) = 0
  constructor
  · rintro ⟨c, hc, hx⟩
    have hWitness (i : ι) := (hp (c i)).mp (hc i)
    choose w hw using hWitness
    refine ⟨Sum.elim c (fun j => w j.1 j.2), ?_⟩
    rintro (_ | ⟨i, j⟩)
    · rw [hsum]
      exact sub_eq_zero.mpr hx
    · rw [hcoeff]
      exact hw i j
  · rintro ⟨w, hw⟩
    refine ⟨fun i => w (.inl i), fun i => (hp _).mpr ?_, ?_⟩
    · refine ⟨fun k => w (.inr (i, k)), fun j => ?_⟩
      rw [← hcoeff]
      exact hw (.inr (i, j))
    · apply sub_eq_zero.mp
      rw [← hsum]
      exact hw (.inl ())

end LinearCombination

/-- The finite spanning step of Poonen's relative definition. A Diophantine
set containing the integers and lying in the image of the smaller number
ring gives a definition of the whole image using an integral basis. -/
theorem systemDiophantine_ringOfIntegers_of_integer_subset
    {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L]
    (f : K →+* L) {S : Set (𝓞 L)} (hS : SystemDiophantine.{u, v} S)
    (hInt : Set.range (Int.cast : ℤ → 𝓞 L) ⊆ S)
    (hSub : S ⊆ Set.range (RingOfIntegers.mapRingHom f)) :
    SystemDiophantine.{u, v} (Set.range (RingOfIntegers.mapRingHom f)) := by
  classical
  let g := RingOfIntegers.mapRingHom f
  let I := ULift.{v} (Fin (Module.finrank ℤ (𝓞 K)))
  let b : Module.Basis I ℤ (𝓞 K) :=
    (Module.finBasis ℤ (𝓞 K)).reindex Equiv.ulift.symm
  let v := fun i => g (b i)
  have hspan :
      {x | ∃ c : I → 𝓞 L, (∀ i, c i ∈ S) ∧ ∑ i, c i * v i = x} = Set.range g := by
    ext x
    change (∃ c : I → 𝓞 L, (∀ i, c i ∈ S) ∧ ∑ i, c i * v i = x) ↔ x ∈ Set.range g
    constructor
    · rintro ⟨c, hc, hx⟩
      have hpre i := hSub (hc i)
      choose w hw using hpre
      refine ⟨∑ i, w i * b i, ?_⟩
      rw [map_sum, ← hx]
      change ∀ i : I, g (w i) = c i at hw
      simp only [map_mul, hw, v]
    · rintro ⟨y, rfl⟩
      refine ⟨fun i => ((b.repr y i : ℤ) : 𝓞 L),
        fun i => hInt ⟨b.repr y i, rfl⟩, ?_⟩
      have hsum := congrArg g (b.sum_repr y)
      simpa [map_sum, map_zsmul, zsmul_eq_mul, v] using hsum
  exact hspan ▸ systemDiophantine_linearCombination v hS

end ManinKP


namespace ManinKP

open NumberField IntermediateField
open scoped NumberField

/-- The classical totally real base case in finite polynomial-system syntax. -/
def TotallyRealIntegerSystems : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyReal K],
    SystemDiophantine.{0,0} (integerImage (𝓞 K))

/-- The relative definition needed by the quadratic descent in a Galois closure. -/
def QuadraticIntegerRingSystems : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsGalois ℚ K]
    (L : IntermediateField ℚ K), Module.finrank L K = 2 →
    SystemDiophantine.{0,0} (Set.range (RingOfIntegers.mapRingHom L.val.toRingHom))

theorem integerSystems_of_galois (hreal : TotallyRealIntegerSystems)
    (hquad : QuadraticIntegerRingSystems)
    (K : Type) [Field K] [NumberField K] [IsGalois ℚ K] :
    SystemDiophantine.{0,0} (integerImage (𝓞 K)) := by
  let E := maximalRealSubfield K
  let f : 𝓞 E →+* 𝓞 K := RingOfIntegers.mapRingHom E.subtype
  have hf : Function.Injective f := by
    intro x y h
    apply RingOfIntegers.ext
    apply E.subtype.injective
    exact congrArg (fun a : 𝓞 K => (a : K)) h
  exact systemDiophantine_integerImage_of_range f hf
    (systemDiophantine_realRing_of_quadratic K (hquad K)) (hreal E)

theorem integerSystems_of_real_and_quadratic (hreal : TotallyRealIntegerSystems)
    (hquad : QuadraticIntegerRingSystems)
    (K : Type) [Field K] [NumberField K] :
    SystemDiophantine.{0,0} (integerImage (𝓞 K)) := by
  let : Algebra.IsAlgebraic ℚ K := NumberField.isAlgebraic K
  let : IsAlgClosure ℚ (AlgebraicClosure K) :=
    ⟨AlgebraicClosure.isAlgClosed K, Algebra.IsAlgebraic.trans ℚ K (AlgebraicClosure K)⟩
  let : IsGalois ℚ (AlgebraicClosure K) := IsAlgClosure.isGalois ℚ (AlgebraicClosure K)
  let L := ↥(normalClosure ℚ K (AlgebraicClosure K))
  let : FiniteDimensional ℚ L := normalClosure.is_finiteDimensional ℚ K (AlgebraicClosure K)
  let : NumberField L := {}
  let : IsGalois ℚ L := IsGalois.normalClosure ℚ K (AlgebraicClosure K)
  let f : K →+* L := algebraMap K L
  let g : 𝓞 K →+* 𝓞 L := RingOfIntegers.mapRingHom f
  have hg : Function.Injective g := by
    intro x y h
    apply RingOfIntegers.ext
    apply f.injective
    exact congrArg (fun a : 𝓞 L => (a : L)) h
  have h := systemDiophantine_ringOfIntegers_preimage K L f
    (integerSystems_of_galois hreal hquad L)
  have he : g ⁻¹' integerImage (𝓞 L) = integerImage (𝓞 K) := by
    ext x
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨z, hg ?_⟩
      exact (map_intCast g z).trans hz
    · rintro ⟨z, rfl⟩
      exact ⟨z, (map_intCast g z).symm⟩
  exact he ▸ h


theorem koymansPaganoFiniteFree_of_real_and_quadratic (hreal : TotallyRealIntegerSystems)
    (hquad : QuadraticIntegerRingSystems) : ManinBilinear.KoymansPaganoFiniteFree := by
  apply ManinBilinear.koymansPaganoFiniteFree_iff_numberRings.mpr
  intro K _ _ n b
  have h := integerSystems_of_real_and_quadratic hreal hquad K
  exact ManinBilinear.KPDPRM.not_computablePred_gateSat_of_intGateDefinable b
    ManinBilinear.KPDPRM.not_computablePred_integerGateSat
    (ManinBilinear.KPDPRM.intGateDefinable_of_systemDiophantine _
      (ManinBilinear.basisDecode_surjective b) h)

theorem manin_bilinear_of_real_and_quadratic {m n p : ℕ}
    (B : (Fin m → ℤ) →ₗ[ℤ] (Fin n → ℤ) →ₗ[ℤ] (Fin p → ℤ)) (hB : B ≠ 0)
    (hreal : TotallyRealIntegerSystems) (hquad : QuadraticIntegerRingSystems) :
    ¬ ComputablePred (ManinBilinear.rawSat B) :=
  ManinBilinear.manin_bilinear_of_koymans_pagano B hB
    (koymansPaganoFiniteFree_of_real_and_quadratic hreal hquad)

/-- A quadratic Diophantine sandwich suffices by finite spanning over the integers. -/
def QuadraticIntegerSandwichSystems : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsGalois ℚ K]
    (L : IntermediateField ℚ K), Module.finrank L K = 2 →
    ∃ S : Set (𝓞 K), SystemDiophantine.{0,0} S ∧ integerImage (𝓞 K) ⊆ S ∧
      S ⊆ Set.range (RingOfIntegers.mapRingHom L.val.toRingHom)

theorem quadraticIntegerRingSystems_of_sandwich (h : QuadraticIntegerSandwichSystems) :
    QuadraticIntegerRingSystems := by
  intro K _ _ _ L hL
  obtain ⟨S, hS, hInt, hSub⟩ := h K L hL
  exact systemDiophantine_ringOfIntegers_of_integer_subset
    L.val.toRingHom hS hInt hSub

theorem manin_bilinear_of_real_and_quadratic_sandwich {m n p : ℕ}
    (B : (Fin m → ℤ) →ₗ[ℤ] (Fin n → ℤ) →ₗ[ℤ] (Fin p → ℤ)) (hB : B ≠ 0)
    (hreal : TotallyRealIntegerSystems) (hquad : QuadraticIntegerSandwichSystems) :
    ¬ ComputablePred (ManinBilinear.rawSat B) :=
  manin_bilinear_of_real_and_quadratic B hB hreal
    (quadraticIntegerRingSystems_of_sandwich hquad)

end ManinKP

end GaloisDescent

section ProvisionalEndpoint

/-!
Provisional integration check for Manin's Conjecture 7.2.

The only placeholder is undecidability over the rings of integers of number
fields, expressed in the arithmetic gate syntax of the checked Manin reduction.
Teamwork-LEAP reports a formalization of number-ring undecidability. Once its
source is available, inspect its exact theorem and replace the placeholder with
an audited proof and any required encoding adapter.
-/

namespace ManinBilinear.Provisional

/-- Placeholder for the upstream number-ring undecidability proof. -/
theorem numberRingUndecidabilityPending : KoymansPaganoNumberRings := by
  sorry

/-- The Manin statement, staged with the explicit arithmetic placeholder. -/
theorem manin_bilinear_pending_number_ring_proof {m n p : ℕ}
    (B : (Fin m → ℤ) →ₗ[ℤ] (Fin n → ℤ) →ₗ[ℤ] (Fin p → ℤ)) (hB : B ≠ 0) :
    ¬ ComputablePred (rawSat B) :=
  manin_bilinear_of_numberRings B hB numberRingUndecidabilityPending

end ManinBilinear.Provisional

end ProvisionalEndpoint

#print axioms ManinBilinear.manin_bilinear_of_numberRings
#print axioms ManinBilinear.KPDPRM.not_computablePred_integerGateSat
#print axioms ManinBilinear.manin_bilinear_of_center_integer_quotient
#print axioms ManinKP.manin_bilinear_of_real_and_quadratic_sandwich
#print axioms ManinBilinear.Provisional.manin_bilinear_pending_number_ring_proof

/-
Ripple license notice
Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
-/

/-
Cameron Freer’s Hilbert10 license notice
Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to the Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by the Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding any notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   Copyright 2026 Cameron Freer

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
-/
