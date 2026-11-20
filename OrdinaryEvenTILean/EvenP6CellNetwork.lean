import EvenP6Incidence
import EvenP6Support
import EvenP6TensorWords

namespace EvenTI.CellPreparation

open scoped BigOperators TensorProduct
open EvenOrdinaryTI.Cells Module

variable {K : Type} [Field K] {d m : ℕ}
variable {width : Fin d → ℕ}
variable {X : (i : Fin d) → Fin (width i) → Type}
  [∀ i v, Field (X i v)] [∀ i v, Algebra K (X i v)]
variable {Y : Fin m → Type} [∀ j, Field (Y j)] [∀ j, Algebra K (Y j)]
  [∀ j, DecidableEq (Y j)]

abbrev Modes (X : (i : Fin d) → Fin (width i) → Type) := fun i => ∀ v, X i v

variable (f : ∀ (j : Fin m) (i : Fin d), Modes X i →ₐ[K] Y j)

def selectedLabel (j : Fin m) (i : Fin d) : Σ k, Fin (width k) :=
  ⟨i, activeBlock (f j i)⟩

def selectedValue (x : ∀ i v, (X i v)ˣ) (j : Fin m) (i : Fin d) : (Y j)ˣ :=
  Units.map (activeFieldEmbedding (f j i)).toRingHom.toMonoidHom
    (x i (activeBlock (f j i)))

/-- On repeated-primary axes the supplied branch has already acted.
For the other axes this selects the same variable on every incidence.
Dual factors use the inverse of the variable on their corresponding axis. -/
def modeValue (keep negative : ∀ i, Fin (width i) → Bool)
    (x : ∀ i v, (X i v)ˣ) : ∀ i v, (X i v)ˣ :=
  fun i v => if keep i v then (if negative i v then (x i v)⁻¹ else x i v) else 1

private theorem activeIndex_covers (a : ∀ j, Y j) (j : Fin m) (h : a j ≠ 0) :
    ∃ r : Fin (activeCells a).card, activeIndex a r = j := by
  let j' : ↥(activeCells a) := ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩
  exact ⟨(activeOrder a).symm j', congrArg Subtype.val ((activeOrder a).apply_symm_apply j')⟩

abbrev DecodedModeTensor (X : (i : Fin d) → Fin (width i) → Type)
    [∀ i v, Field (X i v)] [∀ i v, Algebra K (X i v)] :=
  ⨂[K] i, Modes X i

variable (E : DecodedModeTensor (K := K) X ≃ₐ[K] (∀ j, Y j))

/-- Correctness of the installed live nonzero-cell equations. The same
global variable indexed by mode and primary block is read in every cell. -/
theorem liveCellEquations_iff (T S : DecodedModeTensor (K := K) X)
    (hE : ∀ j i (x : Modes X i), f j i x = embedding E j i x)
    (a b : ∀ j, Y j) (ha : a = E T) (hb : b = E S) (x : ∀ i v, (X i v)ˣ) :
    (PiTensorProduct.tprod K (fun i v => (x i v : X i v)) * T = S) ↔
      ∃ c : ∀ r : Fin (activeCells a).card, (Y (activeIndex a r))ˣ,
        liveRatios a b = some c ∧
        ∀ r, (∏ i : Fin d, selectedValue f x (activeIndex a r) i) = c r := by
  have hprod (j : Fin m) :
      (↑(∏ i : Fin d, selectedValue f x j i) : Y j) =
        ∏ i : Fin d, embedding E j i (fun v => (x i v : X i v)) := by
    calc
      _ = ∏ i : Fin d, (selectedValue f x j i : Y j) := by simp
      _ = _ := by
        apply Finset.prod_congr rfl
        intro i _
        rw [← hE, activeFieldEmbedding_spec]
        rfl
  have happly (j : Fin m) :
      E (PiTensorProduct.tprod K (fun i v => (x i v : X i v)) * T) j =
        (↑(∏ i : Fin d, selectedValue f x j i) : Y j) * a j := by
    rw [cell_multiplication, hprod, ha]
  constructor
  · intro h
    have hs (j : Fin m) : a j = 0 ↔ b j = 0 := by
      have hx := happly j
      rw [h, ← hb] at hx
      constructor
      · intro hz
        rw [hx, hz, mul_zero]
      · intro hz
        rw [hx] at hz
        exact (mul_eq_zero.mp hz).resolve_left (Units.ne_zero _)
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp
      (Option.isSome_iff_ne_none.mpr (fun h' => (liveRatios_none_iff a b).mp h' hs))
    have hratio := (liveRatios_correct a b hc).2
    refine ⟨c, hc, fun r => Units.ext ?_⟩
    have hx := happly (activeIndex a r)
    rw [h, ← hb] at hx
    exact mul_right_cancel₀ (activeIndex_ne_zero a r) (hx.symm.trans (hratio r).symm)
  · rintro ⟨c, hc, hx⟩
    obtain ⟨hh, hratio⟩ := liveRatios_correct a b hc
    apply E.injective
    funext j
    rw [happly, ← hb]
    by_cases hz : a j = 0
    · rw [hz, mul_zero, (hh j).mp hz]
    · obtain ⟨r, rfl⟩ := activeIndex_covers a j hz
      rw [hx]
      exact hratio r

#print axioms liveCellEquations_iff

end EvenTI.CellPreparation
