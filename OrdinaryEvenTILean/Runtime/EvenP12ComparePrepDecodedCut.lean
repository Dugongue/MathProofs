import EvenP12ComparePrepFourBudget

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace EvenTI.P12ComparePrep

open EvenTI.Action EvenTI.Contract EvenTI.P10Scan
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax51.BinaryWordEncoding (bitSize)
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val)
open Mathproof.P15RecogIMPDot20261007 (qN)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- Initial extents for the paid four-cut routine, specified from the literal
input. Only the raw words and the two fixed ABI arrays need storage. -/
def comparisonDecodedExtent (D : FieldEncoding K) (F : FieldPresentation K)
    (w : List ℕ) : String → ℕ :=
  match decodePair D w with
  | none => fun _ => 0
  | some p =>
    comparisonInitExt F (pairCutSlotCount.value (p.n^(p.d/2))) w.length (fun _ => 0)

theorem comparisonDecodedExtent_lt (D : FieldEncoding K) (F : FieldPresentation K)
    (w : List ℕ) (a : String) :
    comparisonDecodedExtent D F w a < (comparisonWordPoly F).eval (bitSize w) := by
  rw [comparisonWordPoly_eval]
  cases hp : decodePair D w with
  | none =>
    simp only [comparisonDecodedExtent,hp]
    unfold comparisonWordBudget fixedMetadataCap
    omega
  | some p =>
    simp only [comparisonDecodedExtent,hp]
    let M := pairCutSlotCount.value (bitSize w)
    let S := pairCutSlotCount.value (p.n^(p.d/2))
    have hSM : S ≤ M := by
      simpa only [Address.evaluate_rangePoly,M,S] using fourBanks_slots_poly D w hp
    have hSM' : S*F.e ≤ M*F.e := Nat.mul_le_mul_right _ hSM
    have hLen := Lax51Proofs.Encoding.length_le_bitSize w
    have he : M*(F.e+1) = M*F.e+M := by rw [Nat.mul_add,Nat.mul_one]
    change comparisonInitExt F S w.length (fun _ => 0) a < M*(F.e+1)+2*bitSize w+fixedMetadataCap F
    by_cases hm : a = canonical.mem
    · simp only [comparisonInitExt,canonicalInitExt,if_pos hm]
      rw [he]
      unfold fixedMetadataCap
      omega
    · by_cases hs : a = canonical.scratch
      · simp only [comparisonInitExt,canonicalInitExt,if_neg hm,if_pos hs]
        unfold fixedMetadataCap
        omega
      · by_cases hr : a = rawPairIO.array
        · simp only [comparisonInitExt,canonicalInitExt,if_neg hm,if_neg hs,if_pos hr]
          unfold fixedMetadataCap
          omega
        · simp only [comparisonInitExt,canonicalInitExt,if_neg hm,if_neg hs,if_neg hr]
          unfold fixedMetadataCap
          omega

/-- The four installed bases are available starting from a raw valid input.
The result preserves its exact words and gives automatically bounded
addresses, fixed-field constants, and all four nullity registers. -/
theorem comparisonFourFromDecoded_run (D : FieldEncoding K) (F : FieldPresentation K)
    (w : List ℕ) {p : ParsedPair K} (hp : decodePair D w = some p) :
    let L := bitSize w
    let B := (comparisonWordPoly F).eval L
    ∃ (a : ℕ) (h : p.d = a+a) (τ : Env),
      let T := cast (congrArg (fun d => Tensor K d p.n) h) p.source
      let S := cast (congrArg (fun d => Tensor K d p.n) h) p.target
      let m := p.n^a
      Run B (comparisonFourReadyProgram D F)
        (initEnv (comparisonDecodedExtent D F w) (w.length::w)) τ
        (40*(L+1)+3*F.e+26+4*oneCutCostBound F L) ∧
      Slots F canonical qN.WS (pairCutSlotCount.value m) B τ ∧
      τ.vars shapePower.out = m ∧ τ.arrs rawPairIO.array = w ∧ τ.vars qN.WS = F.e+1 ∧
      val F canonical qN.WS τ (constantsBase.value m) = 0 ∧
      (∀ j : Fin 4, InstalledCut F T S j τ) ∧ τ.inp = [] ∧ τ.out = [] := by
  dsimp only
  obtain ⟨_,_,_,hD,hE,hN⟩ := decodePair_some hp
  cases p with
  | mk d n T S =>
    change d % 2 = 0 at hE
    change 4 ≤ d at hD
    change 2 ≤ n at hN
    obtain ⟨a,ha⟩ := Nat.even_iff.mpr hE
    change d = a+a at ha
    subst d
    have hh : (a+a)/2 = a := by omega
    have hW : comparisonInput D T S = w := decodePair_reencode D w hp
    have hExt : comparisonDecodedExtent D F w =
        comparisonInitExt F (pairCutSlotCount.value (n^a)) w.length (fun _ => 0) := by
      unfold comparisonDecodedExtent
      rw [hp]
      dsimp only
      rw [hh]
    obtain ⟨τ,r,hSlots,hM,hBank,hWS,hZero,hCuts,hIn,hOut⟩ :=
      comparisonFourBinarySized_run D F T S (fun _ => 0) (by omega) hN
    refine ⟨a,rfl,τ,?_,?_,hM,hBank.trans hW,hWS,hZero,hCuts,hIn,hOut⟩
    · simpa only [hW,hExt] using r
    · simpa only [hW] using hSlots

#print axioms comparisonDecodedExtent_lt
#print axioms comparisonFourFromDecoded_run
end EvenTI.P12ComparePrep
