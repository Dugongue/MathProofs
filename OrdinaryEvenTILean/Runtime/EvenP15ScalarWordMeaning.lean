import EvenP15ScalarWord
import EvenP15ScalarMatrixMeaning

set_option autoImplicit false

namespace EvenTI.P15Scalar

open EvenTI.Contract EvenTI.Action
open EvenTI.P12Scalar (rawScalarModes)
open Lax51.TuringPolytime (TuringPolytime)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {d n : ℕ}

/-- A completed recovered matrix frame has exactly the Boolean used by
the scalar-stabilizer branch. No matrix inverse or witness action check
is performed by this digit scan. -/
theorem scalarWordSpec_eq_rawScalarModes (D : FieldEncoding K) (hn : 0 < n)
    (M : Fin d → Matrix (Fin n) (Fin n) K) (payload : List ℕ)
    (hRows : ∀ (i : Fin d) (j k : Fin n),
      (d::n::payload).getD (2+i.val*(n*n)+(j.val*n+k.val)) 0 = (D (M i j k)).val) :
    scalarWordSpec (D 0).val (d::n::payload) = if rawScalarModes M then [1] else [0] := by
  have he := rawScalarModes_iff_bankModes D hn M (d::n::payload)
    (fun i => 2+i.val*(n*n)) hRows
  have hf : FoldedScalarModes (D 0).val (d::n::payload) d n ↔ rawScalarModes M = true := by
    rw [he]
    constructor
    · intro h i
      exact h i.val i.isLt
    · intro h i hi
      exact h ⟨i,hi⟩
  simp [scalarWordSpec,hf]

theorem scalarWord_binary_on_recovered (D : FieldEncoding K) :
    ∃ g, TuringPolytime g ∧
      ∀ {d n : ℕ} (M : Fin d → Matrix (Fin n) (Fin n) K) (payload : List ℕ),
        0 < d → 0 < n → payload.length=d*(n*n) →
        (∀ a ∈ payload,a≤Fintype.card K) →
        (∀ (i : Fin d) (j k : Fin n), (d::n::payload).getD
          (2+i.val*(n*n)+(j.val*n+k.val)) 0 = (D (M i j k)).val) →
        g (d::n::payload) = if rawScalarModes M then [1] else [0] := by
  obtain ⟨g,hg,h⟩ := scalarWord_binary (D 0).val (Fintype.card K)
  refine ⟨g,hg,?_⟩
  intro d n M payload hd hn hl hDigits hRows
  exact (h _ ⟨d,n,payload,rfl,hd,hn,hl,hDigits⟩).trans
    (scalarWordSpec_eq_rawScalarModes D hn M payload hRows)

#print axioms scalarWordSpec_eq_rawScalarModes
#print axioms scalarWord_binary_on_recovered
end EvenTI.P15Scalar