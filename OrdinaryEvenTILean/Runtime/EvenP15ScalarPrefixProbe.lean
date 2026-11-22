import EvenP15ScalarKernelProbe
import EvenP9BaseKernelScan

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false

namespace EvenTI.P15Scalar
open EvenTI.Part8 EvenTI.CellPreparation EvenOrdinaryTI.LiveRows EvenOrdinaryTI.CellPrefix
open Mathproof.P15NetworkDefs20261007 Matrix

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {s t d : ℕ}
variable (X : Fin s → Type) (Y : Fin t → Type)
  [∀ v, Field (X v)] [∀ j, Field (Y j)] [∀ v, Fintype (X v)] [∀ j, Fintype (Y j)]
  [∀ v, Algebra K (X v)] [∀ j, Algebra K (Y j)]
variable (orig : Fin t → Fin d → Fin s) (emb : ∀ j i, X (orig j i) →ₐ[K] Y j)

local notation "M" => (Fintype.card K - 1)
local notation "V" => (VarCount s t d)
local notation "U" => (PhysicalAssignment (d := d) X Y)
local notation "baseMatrix" => (baseEquationMatrix (K := K) orig)
local notation "ev" => (prefixEvaluation X Y orig emb)
private local instance baseOrder : NeZero M := ⟨(Nat.sub_pos_of_lt Fintype.one_lt_card).ne'⟩

local macro "baseEval" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `EvenP8BaseResidual
    `EvenTI.Part8.baseEvaluation))

def liftBaseCoordinates (L : BaseUnitLog K) :
    Multiplicative (Fin V → ZMod M) →* U where
  toFun z := baseAssignment X Y (fun j => L.decode (z.toAdd j))
  map_one' := by
    funext j
    change baseUnit (L.mulEquiv 1) = 1
    rw [map_one]
    exact map_one _
  map_mul' x y := by
    funext j
    let a := Multiplicative.ofAdd (x.toAdd j)
    let b := Multiplicative.ofAdd (y.toAdd j)
    change baseUnit (L.mulEquiv (a*b)) = baseUnit (L.mulEquiv a) * baseUnit (L.mulEquiv b)
    rw [map_mul L.mulEquiv]
    exact map_mul _ _ _

theorem liftBaseCoordinates_kernel_iff (L : BaseUnitLog K) (z : Fin V → ZMod M) :
    ev (liftBaseCoordinates (d := d) X Y L (Multiplicative.ofAdd z)) = 1 ↔ (baseMatrix).mulVec z = 0 := by
  have he (r : Fin (RowCount t d)) :
      ev (liftBaseCoordinates (d := d) X Y L (Multiplicative.ofAdd z)) r =
        baseUnit (L.decode ((baseMatrix).mulVec z r)) := by
    change ev (baseAssignment X Y (fun j => L.decode (z j))) r = _
    rw [baseEval X Y orig emb,decode_baseEquationMatrix orig L z r]
  have hzero (r : Fin (RowCount t d)) :
      (baseUnit (K := K) (A := physicalRowField Y r) (L.decode 0)) = 1 := by
    change baseUnit (L.mulEquiv 1) = 1
    rw [map_one]
    exact map_one _
  constructor
  · intro hh
    funext r
    have hs : baseUnit (K := K) (A := physicalRowField Y r) (L.decode ((baseMatrix).mulVec z r)) =
        baseUnit (L.decode 0) := (he r).symm.trans ((congrFun hh r).trans (hzero r).symm)
    exact congrArg Multiplicative.toAdd (L.mulEquiv.injective (units_map_injective _ hs))
  · intro h
    funext r
    have rz : (baseMatrix).mulVec z r = 0 := congrFun h r
    rw [he,rz,hzero]
    rfl

theorem liftBaseCoordinates_covers_kernel (L : BaseUnitLog K)
    (hCap : ∀ a : U, ev a = 1 → a ^ M = 1)
    (a : U) (ha : ev a = 1) :
    ∃ z : Fin V → ZMod M, (baseMatrix).mulVec z = 0 ∧
      liftBaseCoordinates (d := d) X Y L (Multiplicative.ofAdd z) = a := by
  have hu (v : Fin V) : ∃ u : Kˣ, baseUnit u = a v := by
    apply units_mem_range_of_pow (algebraMap K (physicalVarField X Y v)) M (dvd_refl M)
    exact congrFun (hCap a ha) v
  choose u hu using hu
  let z : Fin V → ZMod M := fun i => L.encode (u i)
  have hz (i : Fin V) : L.decode (z i) = u i := L.mulEquiv.apply_symm_apply (u i)
  have he : liftBaseCoordinates (d := d) X Y L (Multiplicative.ofAdd z) = a := by
    funext i
    change baseUnit (L.decode (z i)) = a i
    rw [hz]
    exact hu i
  refine ⟨z,(liftBaseCoordinates_kernel_iff X Y orig emb L z).mp ?_,he⟩
  rwa [he]

/-- Coordinate fixing on B and U gives the same answer as Smith right
columns on every subgroup test over the capped homogeneous kernel. -/
theorem scanRecoveryBaseProbes_eq (L : BaseUnitLog K) (enum : Fin (Fintype.card K) ≃ K)
    (test : U → Bool) (P : Subgroup U) (hTest : ∀ a, ev a = 1 → (test a = true ↔ a ∈ P))
    (hCap : ∀ a : U, ev a = 1 → a ^ M = 1) :
    scanRecoveryKernelProbes baseMatrix (fun z => test (liftBaseCoordinates (d := d) X Y L (Multiplicative.ofAdd z))) =
      scanPrefixBaseColumns X Y orig enum test := by
  let lift := liftBaseCoordinates (d := d) X Y L
  let R : AddSubgroup (Fin V → ZMod M) :=
    { carrier := {z | lift (Multiplicative.ofAdd z) ∈ P}
      zero_mem' := by
        change lift 1 ∈ P
        rw [map_one]
        exact P.one_mem
      add_mem' := by
        intro x y hx hy
        change lift (Multiplicative.ofAdd x * Multiplicative.ofAdd y) ∈ P
        rw [map_mul]
        exact P.mul_mem hx hy
      neg_mem' := by
        intro x hx
        change lift (Multiplicative.ofAdd x)⁻¹ ∈ P
        rw [map_inv]
        exact P.inv_mem hx }
  apply Bool.eq_iff_iff.mpr
  rw [scanPrefixBaseColumns_iff_on_kernel X Y orig emb enum test P hTest hCap,
    scanRecoveryKernelProbes_iff baseMatrix _ R (fun z hz =>
      hTest _ ((liftBaseCoordinates_kernel_iff X Y orig emb L z).mpr hz))]
  constructor
  · intro h a ha
    obtain ⟨z,hz,rfl⟩ := liftBaseCoordinates_covers_kernel X Y orig emb L hCap a ha
    exact h z hz
  · intro h z hz
    exact h _ ((liftBaseCoordinates_kernel_iff X Y orig emb L z).mpr hz)

#print axioms liftBaseCoordinates_kernel_iff
#print axioms liftBaseCoordinates_covers_kernel
#print axioms scanRecoveryBaseProbes_eq
end EvenTI.P15Scalar