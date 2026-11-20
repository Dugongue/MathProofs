import Mathproof.Meta.IMPAutoTactics20261004
import Mathproof.Meta.Problem18IMPFieldLayout20261001

/-! Counted writes into one row-major integer bank, with an exact frame. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Problem17CellCRT46
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18IMPFieldLayout20261001

def remE (a b : Expr) : Expr :=
  .bin .sub a (.bin .mul (.bin .div a b) b)

theorem remE_eval {B a b : ℕ} {σ : Env} {A C : Expr}
    (hA : A.evalB B σ = some a) (hC : C.evalB B σ = some b) (ha : a < B) :
    (remE A C).evalB B σ = some (a%b) := by
  have hDiv : a/b < B := (Nat.div_le_self _ _).trans_lt ha
  have hProd : (a/b)*b < B := (Nat.div_mul_le_self _ _).trans_lt ha
  have hM : a-(a/b)*b = a%b := by
    have h := Nat.div_add_mod a b
    rw [Nat.mul_comm b (a/b)] at h
    omega
  rw [← hM]
  exact evalB_bin hA (evalB_bin (evalB_bin hA hC hDiv) hC hProd) (by change a-(a/b)*b<B; omega)

def writeIndex := "CellCRT.table.index"
def writeValue := "CellCRT.table.value"
def writeCount := "CellCRT.table.count"

def writeBody (dst : String) (load : Com) : Com :=
  .seq load (.seq (.store dst (.var writeIndex) (.var writeValue))
    (.assign writeIndex (.bin .add (.var writeIndex) (.lit 1))))

def writeLoop (dst : String) (load : Com) : Com :=
  .while (.lt (.var writeIndex) (.var writeCount)) (writeBody dst load)

def writeTable (dst : String) (load : Com) : Com :=
  .seq (.assign writeIndex (.lit 0)) (writeLoop dst load)

def writeTableCost (P n : ℕ) : ℕ := (P+11)*n+6

theorem writeTable_run (dst : String) (load : Com) {B n P : ℕ} {σ : Env} (f : ℕ → ℕ)
    (hn : n < B) (hc : σ.vars writeCount = n) (hcap : n ≤ (σ.arrs dst).length)
    (hw : writeCount ∉ scalarWrites load) (hword : ∀ i < n, f i < B)
    (hload : ∀ i < n, ∀ ρ, ρ.vars writeIndex = i →
      Frame (writeLoop dst load) (σ.setVar writeIndex 0) ρ →
      Run B load ρ (ρ.setVar writeValue (f i)) P) :
    ∃ τ, Run B (writeTable dst load) σ τ (writeTableCost P n) ∧
      SegInv (σ.arrs dst) (τ.arrs dst) 0 n f ∧ Frame (writeTable dst load) σ τ := by
  apply run_of_vc
  simp only [writeTable,vc,Ok_lit,nomv_lit]
  refine ⟨by omega,?_⟩
  let σ1 := σ.setVar writeIndex 0
  have hW : writeCount ∉ scalarWrites (writeBody dst load) := by
    simp only [writeBody,scalarWrites,Finset.union_empty,Finset.empty_union,Finset.mem_union,Finset.mem_singleton,not_or]
    exact ⟨hw,by decide⟩
  refine wp_for_var n (P+7) (fun i ρ => SegInv (σ.arrs dst) (ρ.arrs dst) 0 i f)
    hn (by simp [σ1,vars_setVar]) (by simpa [σ1,vars_setVar,impStrEq] using hc)
    hW (SegInv.zero _ _ _) ?_ ?_
  · intro i hi ρ hI hidx hfr
    let η := ρ.setVar writeValue (f i)
    let ν := η.setArr dst i (f i)
    let τ := ν.setVar writeIndex (i+1)
    have hηi : η.vars writeIndex = i := by simpa [η,vars_setVar,impStrEq] using hidx
    have hηv : η.vars writeValue = f i := by simp [η,vars_setVar]
    have hηcap : n ≤ (η.arrs dst).length := by rw [show η.arrs = ρ.arrs from rfl,hfr.len]; exact hcap
    have eI : (Expr.var writeIndex).evalB B η = some i :=
      (evalB_var (by rw [hηi]; omega)).trans (congrArg some hηi)
    have eV : (Expr.var writeValue).evalB B η = some (f i) :=
      (evalB_var (by rw [hηv]; exact hword i hi)).trans (congrArg some hηv)
    have r1 : Run B load ρ η P := hload i hi ρ hidx hfr
    have r2 : Run B (.store dst (.var writeIndex) (.var writeValue)) η ν 3 :=
      Run.store eI eV (by omega)
    have hνi : ν.vars writeIndex = i := hηi
    have ev : (.bin .add (.var writeIndex) (.lit 1) : Expr).evalB B ν = some (i+1) := by
      have ev' : (Expr.var writeIndex).evalB B ν = some i :=
        (evalB_var (by rw [hνi]; omega)).trans (congrArg some hνi)
      exact evalB_bin ev' (evalB_lit (by omega)) (by change i+1 < B; omega)
    have r3 : Run B (.assign writeIndex (.bin .add (.var writeIndex) (.lit 1))) ν τ 4 := Run.assign ev
    have hRun : Run B (writeBody dst load) ρ τ (P+7) := by
      simpa only [writeBody,show 3+4=7 by decide] using r1.seq (r2.seq r3)
    have hseg : SegInv (σ.arrs dst) (τ.arrs dst) 0 (i+1) f := by
      have hρlen : n ≤ (ρ.arrs dst).length := by rw [hfr.len]; exact hcap
      have hlen : 0+i < (ρ.arrs dst).length := by simpa using hi.trans_le hρlen
      have hs := hI.step hlen (show f i = f i from rfl)
      simpa [τ,ν,η,arrs_setVar,arrs_setArr] using hs
    exact vc_of_run hRun (fun k hk => ⟨hseg,by simp [τ,vars_setVar],hk⟩)
  · intro τ k hSeg _ _ hk
    refine ⟨?_,fun fr => ⟨hSeg,fr⟩⟩
    unfold writeTableCost
    simp only [Expr.size]
    rw [show P+7+4=P+11 by omega] at hk
    omega

#print axioms writeTable_run
end Problem17CellCRT46



