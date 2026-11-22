import EvenP15RecoverResidueStore
import EvenP8PrefixTransporter

namespace EvenTI.P15Recover

open scoped BigOperators
open EvenTI.Part8 EvenTI.CellPreparation EvenOrdinaryTI.LiveRows EvenOrdinaryTI.CellPrefix
open EvenTI.P12Compare (recoverLinear recoverLinear_sound recoverLinear_complete)

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

theorem recoverLinear_available {M m n : ℕ} [NeZero M]
    (A : Matrix (Fin m) (Fin n) (ZMod M)) (b : Fin m → ZMod M) :
    (recoverLinear A b).isSome = true ↔ ∃ x, A.mulVec x = b := by
  constructor
  · intro h
    obtain ⟨x,hx⟩ := Option.isSome_iff_exists.mp h
    exact ⟨x,recoverLinear_sound A b hx⟩
  · exact recoverLinear_complete A b

theorem recoverLinear_row_iff {M m n : ℕ} [NeZero M]
    (A : Matrix (Fin m) (Fin n) (ZMod M)) (b : Fin m → ZMod M) :
    (recoverLinear A b).isSome = (smithRowSolve A.transpose b).isSome := by
  apply Bool.eq_iff_iff.mpr
  rw [recoverLinear_available,smithRowSolve_isSome_iff]
  constructor
  · rintro ⟨x,hx⟩
    exact ⟨x,fun i => by
      simpa only [Matrix.mulVec,dotProduct,Matrix.transpose_apply,mul_comm] using congrFun hx i⟩
  · rintro ⟨x,hx⟩
    exact ⟨x,funext fun i => by
      simpa only [Matrix.mulVec,dotProduct,Matrix.transpose_apply,mul_comm] using hx i⟩

section Residual
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {s t d : ℕ}
variable (X : Fin s → Type) (Y : Fin t → Type)
  [∀ v, Field (X v)] [∀ j, Field (Y j)] [∀ v, Fintype (X v)] [∀ j, Fintype (Y j)]
  [∀ v, Algebra K (X v)] [∀ j, Algebra K (Y j)]
variable (orig : Fin t → Fin d → Fin s) (emb : ∀ j i, X (orig j i) →ₐ[K] Y j)

local notation "h" => (Fintype.card K - 1)
private local instance baseOrder : NeZero h := ⟨(Nat.sub_pos_of_lt Fintype.one_lt_card).ne'⟩
local notation "V" => VarCount s t d
local notation "J" => RowCount t d
local notation "P" => (physicalVarField X Y)
local notation "Q" => (physicalRowField Y)
local notation "eval" => (prefixEvaluation X Y orig emb)

private def readResidual (views : ∀ r : Fin J, DenseFieldView (K := K) (Q r))
    (c : ∀ j, (Y j)ˣ) (u : ∀ v : Fin V, (P v)ˣ) (r : Fin J) : Option Kˣ :=
  referencePullbackUnit (baseFieldView (K := K)).coordinates (views r).coordinates
    (Algebra.ofId K (Q r)) ((physicalRHS Y c r) / eval u r)

/-- Replace the old Smith-selected witness by the deterministic coordinate
recovery value. The two algorithms accept exactly the same base residuals. -/
def correctResidualCRT (enum : Fin (Fintype.card K) ≃ K)
    (views : ∀ r : Fin J, DenseFieldView (K := K) (Q r))
    (c : ∀ j, (Y j)ˣ) (u : ∀ v : Fin V, (P v)ˣ) : Option (∀ v : Fin V, (P v)ˣ) :=
  (baseUnitLog enum).bind fun L =>
    (collectSites (readResidual X Y orig emb views c u)).bind fun rho =>
      (recoverLinear (baseEquationMatrix (K := K) orig) (fun r => L.encode (rho r))).map fun z =>
        u * baseAssignment X Y (fun v => L.decode (z v))

theorem correctResidualCRT_available (enum : Fin (Fintype.card K) ≃ K)
    (views : ∀ r : Fin J, DenseFieldView (K := K) (Q r))
    (c : ∀ j, (Y j)ˣ) (u : ∀ v : Fin V, (P v)ˣ) :
    (correctResidualCRT X Y orig emb enum views c u).isSome =
      (correctBaseResidual X Y orig emb enum views c u).isSome := by
  unfold correctResidualCRT correctBaseResidual
  cases hL : baseUnitLog enum with
  | none => rfl
  | some L =>
    simp only [Option.bind_some]
    change ((collectSites (readResidual X Y orig emb views c u)).bind _).isSome =
      ((collectSites (readResidual X Y orig emb views c u)).bind _).isSome
    cases hData : collectSites (readResidual X Y orig emb views c u) with
    | none => rfl
    | some x =>
      simp only [Option.bind_some,Option.isSome_map]
      rw [recoverLinear_row_iff]
      cases smithRowSolve (baseEquationMatrix (K:=K) orig).transpose (fun r => L.encode (x r)) <;> rfl

private theorem newBaseEvaluation (a : Fin V → Kˣ) (r : Fin J) :
    eval (baseAssignment X Y a) r = baseUnit (baseRow orig a r) := by
  change physicalValue X Y orig (fun j i => (emb j i).toRingHom) _ r = _
  unfold baseAssignment baseRow physicalValue ternary
  have hEq (e : Fin 3) : physicalInc X Y orig (fun j i => (emb j i).toRingHom) r e =
      (prefixAlgInc X Y orig emb r e).toRingHom := rfl
  simp only [hEq,map_baseUnit]
  simp only [baseUnit,map_mul,map_inv]

private theorem collectValue {n : ℕ} {A : Fin n → Type} (read : ∀ i, Option (A i))
    (a : ∀ i, A i) (ha : collectSites read = some a) (i : Fin n) : read i = some (a i) := by
  unfold collectSites at ha
  split at ha
  · obtain rfl := Option.some.inj ha
    exact (Option.some_get _).symm
  · contradiction

theorem correctResidualCRT_sound (enum : Fin (Fintype.card K) ≃ K)
    (views : ∀ r : Fin J, DenseFieldView (K := K) (Q r))
    (c : ∀ j, (Y j)ˣ) (u a : ∀ v : Fin V, (P v)ˣ)
    (ha : correctResidualCRT X Y orig emb enum views c u = some a) :
    eval a = physicalRHS Y c := by
  unfold correctResidualCRT at ha
  obtain ⟨L,_,h₁⟩ := Option.bind_eq_some_iff.mp ha
  obtain ⟨rho,hRead,h₂⟩ := Option.bind_eq_some_iff.mp h₁
  obtain ⟨z,hz,rfl⟩ := Option.map_eq_some_iff.mp h₂
  have hz' := recoverLinear_sound (baseEquationMatrix (K := K) orig) (fun r => L.encode (rho r)) hz
  funext r
  have he := collectValue _ rho hRead r
  change referencePullbackUnit (baseFieldView (K := K)).coordinates (views r).coordinates
    (Algebra.ofId K (Q r)) ((physicalRHS Y c r) / eval u r) = some (rho r) at he
  have hRes : baseUnit (rho r) = physicalRHS Y c r / eval u r :=
    (referencePullbackUnit_spec _ _ _ _ _).mp he
  have hzRow : baseRow orig (fun v => L.decode (z v)) r = rho r := by
    rw [← decode_baseEquationMatrix,congrFun hz' r]
    exact L.mulEquiv.apply_symm_apply _
  rw [map_mul]
  change eval u r * eval (baseAssignment X Y _) r = _
  rw [newBaseEvaluation, hzRow, hRes, mul_comm (eval u r), div_mul_cancel]

#print axioms recoverLinear_row_iff
#print axioms correctResidualCRT_available
#print axioms correctResidualCRT_sound

end Residual
end EvenTI.P15Recover
