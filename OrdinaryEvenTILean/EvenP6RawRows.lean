import EvenP6CellsProduct
import EvenP6CellNetwork
import EvenP6Install

namespace EvenTI.CellPreparation

open scoped BigOperators
open EvenTI.CellProducer EvenOrdinaryTI.LiveRows

variable {K Q : Type} [Field K] [Fintype K] [DecidableEq K]
  [CommRing Q] [Algebra K Q] [DecidableEq Q] {N d : ℕ}
variable {width : Fin d → ℕ}
variable {X : (i : Fin d) → Fin (width i) → Type}
  [∀ i v, Field (X i v)] [∀ i v, Algebra K (X i v)]
variable (enum : Fin (Fintype.card K) ≃ K) (C : Q ≃ₗ[K] (Fin N → K))
variable [∀ i : Fin (rawCells enum C).length, CellFieldCertificate C ((rawCells enum C).get i)]
variable (mode : ∀ i, Modes X i →ₐ[K] Q)

def rawModeIncidence (j : Fin (rawCells enum C).length) (i : Fin d) :
    Modes X i →ₐ[K] ProducedCell enum C j :=
  compactAlgebraMap C ((rawCells enum C).get j) (mode i)

def rawRatios (T S : Q) :=
  liveRatios (compactProductPack enum C T) (compactProductPack enum C S)

def rawOrigins (T : Q) (r : Fin (activeCells (compactProductPack enum C T)).card) (i : Fin d) :
    Fin (∑ i, width i) :=
  finSigmaFinEquiv (selectedLabel (rawModeIncidence enum C mode)
    (activeIndex (compactProductPack enum C T) r) i)

/-- Emit the live source-index bank directly from the actual cell labels
and nonzero support. The same mode-block pair has one address. -/
def rawSources (T : Q) : List ℕ :=
  SmithSourceBank (rawOrigins enum C mode T)

theorem rawSources_length (T : Q) :
    (rawSources enum C mode T).length ≤ 3 * (rawCells enum C).length * (d + 2) := by
  unfold rawSources SmithSourceBank
  rw [List.length_ofFn]
  calc
    _ ≤ RowCount (rawCells enum C).length d * 3 :=
      Nat.mul_le_mul_right 3 (Nat.mul_le_mul_right _ (activeCells_card_le _))
    _ = _ := by simp only [RowCount]; ac_rfl

set_option maxHeartbeats 1000000
/-- The ratios and incidence maps are constructed from the actual cells.
Their equations are equivalent to the original algebra multiplication. -/
theorem rawRows_iff (T S : Q) (x : ∀ i v, (X i v)ˣ) :
    (∏ i : Fin d, mode i (fun v => (x i v : X i v))) * T = S ↔
    ∃ c : ∀ r : Fin (activeCells (compactProductPack enum C T)).card,
      (ProducedCell enum C (activeIndex (compactProductPack enum C T) r))ˣ,
      rawRatios enum C T S = some c ∧
      ∀ r, (∏ i : Fin d, selectedValue (rawModeIncidence enum C mode) x
        (activeIndex (compactProductPack enum C T) r) i) = c r := by
  let E := compactProductEquiv enum C
  let a := compactProductPack enum C T
  let b := compactProductPack enum C S
  let f := rawModeIncidence enum C mode
  let u (j : Fin (rawCells enum C).length) := ∏ i : Fin d, selectedValue f x j i
  have h (j : Fin (rawCells enum C).length) :
      E ((∏ i : Fin d, mode i (fun v => (x i v : X i v))) * T) j = (u j).val * a j := by
    rw [map_mul, map_prod, Pi.mul_apply, Finset.prod_apply]
    congr 1
    calc
      _ = ∏ i : Fin d, f j i (fun v => (x i v : X i v)) := rfl
      _ = ∏ i : Fin d, (selectedValue f x j i : ProducedCell enum C j) := by
        apply Finset.prod_congr rfl
        intro i _
        rw [activeFieldEmbedding_spec]
        rfl
      _ = (u j).val := by simp [u]
  constructor
  · intro he
    have hh (j) : b j = (u j).val * a j := by
      change E S j = _
      rw [← he]
      exact h j
    have hs (j) : a j = 0 ↔ b j = 0 := by
      constructor
      · intro hz
        rw [hh, hz, mul_zero]
      · intro hz
        rw [hh] at hz
        exact (mul_eq_zero.mp hz).resolve_left (Units.ne_zero _)
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp
      (Option.isSome_iff_ne_none.mpr (fun h' => (liveRatios_none_iff a b).mp h' hs))
    refine ⟨c, hc, fun r => Units.ext ?_⟩
    exact mul_right_cancel₀ (activeIndex_ne_zero a r)
      ((hh (activeIndex a r)).symm.trans ((liveRatios_correct a b hc).2 r).symm)
  · rintro ⟨c, hc, hh⟩
    apply E.injective
    funext j
    have hr := liveRatios_correct a b hc
    change _ = b j
    rw [h]
    by_cases hz : a j = 0
    · rw [hz, mul_zero, (hr.1 j).mp hz]
    · let j' : ↥(activeCells a) := ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩⟩
      have hj : activeIndex a ((activeOrder a).symm j') = j :=
        congrArg Subtype.val ((activeOrder a).apply_symm_apply j')
      let r := (activeOrder a).symm j'
      change activeIndex a r = j at hj
      rw [← hj]
      have hv : u (activeIndex a r) = c r := hh r
      exact (congrArg (fun v : (ProducedCell enum C (activeIndex a r))ˣ =>
        v.val * a (activeIndex a r)) hv).trans (hr.2 r)

#print axioms rawSources_length
#print axioms rawRows_iff

end EvenTI.CellPreparation
