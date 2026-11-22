import EvenP14CutRankControl
import EvenP14CutRankLayout
import Mathproof.Meta.Problem18P34AssemblyMatrixGatherSetup20261003

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 12000

namespace EvenTI.P12ComparePrep

open EvenTI.Action EvenTI.Contract EvenTI.LiveSpectral
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18IMPFieldPresentation20261001 (slice)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val val_setVar regNames NoVar)
open Mathproof.Problem18P34AssemblyMatrixGatherSetup20261003
  (commands install commands_run installed_arrays installed_slots installed_scalar)
open Mathproof.P15RecogIMPDot20261007 (qN dT dU dZ)
open Mathproof.P15RecogIMPProgram20261007 (rOs)
open Mathproof.P15DecideIMPKerBasis20261007 (kAM kOUT)
open Mathproof.P15DecideIMPRowKer20261007 (tNR tD tRB)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

def cutRankRawOrder : String := "even_compare_rank_order"
def cutRankRawWidth : String := "even_compare_rank_width"

def rankAddressOffset (k : ℕ) : Address :=
  .add augmentedMatrixBase (.mul (.litSucc k) .side)

def cutRankAssign : List (String × Expr) :=
  [(cutRankLimit,.bin .div (.var cutRankRawOrder) (.lit 2)),
    (retainedSrc,(rankAddressOffset 0).expr),
    (dT,(Address.add constantsBase (.litSucc 1)).expr),
    (dU,(Address.add constantsBase (.litSucc 2)).expr),
    (dZ,constantsBase.expr),
    (rOs,(Address.add constantsBase (.litSucc 0)).expr),
    (tNR,.bin .div (.var shapePower.out) (.var cutRankRawWidth)),
    (tD,.var cutRankRawWidth),
    (tRB,(rankAddressOffset 1).expr),
    (kAM,(rankAddressOffset 2).expr),
    (kOUT,(rankAddressOffset 4).expr)]

def cutRankConfigNames : List String := cutRankAssign.map Prod.fst

def cutRankConfigure : Com :=
  .seq (.assign cutRankRawOrder (.get rawPairIO.array (.lit 0)))
    (.seq (.assign cutRankRawWidth (.get rawPairIO.array (.lit 1))) (commands cutRankAssign))

def cutRankConfigCost : ℕ := ((cutRankAssign.map fun p => p.2.size+1).sum)+7

private def rankInstalledVars (d n m : ℕ) : List (String × ℕ) :=
  [(cutRankLimit,d+1),(retainedSrc,placedRankSource m),
    (dT,constantsBase.value m+2),(dU,constantsBase.value m+3),(dZ,constantsBase.value m),
    (rOs,constantsBase.value m+1),(tNR,n^d),(tD,n),
    (tRB,placedRankRows m),(kAM,placedRankAugmented m),(kOUT,placedRankOutput m)]

private theorem rankInstalledVars_names (d n m : ℕ) (p : String × ℕ)
    (hp : p ∈ rankInstalledVars d n m) :
    canonical.e ≠ p.1 ∧ canonical.p ≠ p.1 ∧ canonical.modBase ≠ p.1 ∧
      canonical.exp ≠ p.1 ∧ qN.WS ≠ p.1 := by
  simp only [rankInstalledVars,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with h|h|h|h|h|h|h|h|h|h|h <;> rw [h] <;> simp only [Prod.fst] <;> decide

/-- Derive the retained-rank ABI from the raw tensor-pair header and the
already computed cut side. The scalar setup preserves every field slot. -/
theorem cutRankConfigure_run (F : FieldPresentation K)
    {d n B : ℕ} {σ : Env} (x : Coord (d+1) n → K) (tail : List ℕ)
    (hd : 1 ≤ d) (hn : 2 ≤ n)
    (hB : pairCutSlotCount.value (n^(d+1))+n^(d+1)+n^(d+1)+10 < B)
    (hS : Slots F canonical qN.WS (pairCutSlotCount.value (n^(d+1))) B σ)
    (hHead : σ.arrs rawPairIO.array = ((d+1)+(d+1))::n::tail)
    (hSide : σ.vars shapePower.out = n^(d+1)) (hABI : σ.vars qN.WS = F.e+1)
    (hForm : ∀ u : Coord (d+1) n, val F canonical qN.WS σ
      (placedRankSource (n^(d+1))+(inputCoordOrder n (d+1) u).val) = x u)
    (hZero : val F canonical qN.WS σ (constantsBase.value (n^(d+1))) = 0)
    (hOne : val F canonical qN.WS σ (constantsBase.value (n^(d+1))+1) = 1) :
    let m := n^(d+1)
    ∃ τ, Run B cutRankConfigure σ τ cutRankConfigCost ∧
      CutRankBank F x (placedRankSource m) (placedRankRows m) (placedRankAugmented m)
        (placedRankOutput m) (constantsBase.value m) (pairCutSlotCount.value m) B τ ∧
      (∀ s, val F canonical qN.WS τ s = val F canonical qN.WS σ s) ∧
      (∀ r, r ∉ cutRankConfigNames →
        r ≠ cutRankRawOrder → r ≠ cutRankRawWidth → τ.vars r = σ.vars r) ∧
      τ.arrs=σ.arrs ∧ τ.inp=σ.inp ∧ τ.out=σ.out := by
  dsimp only
  let m := n^(d+1)
  let Z := constantsBase.value m
  let S := pairCutSlotCount.value m
  have hPos : 0 < m := pow_pos (by omega) _
  have hEnough : (d+1) ≤ m := (Nat.lt_two_pow_self (n:=d+1)).le.trans (Nat.pow_le_pow_left hn _)
  have hrM : n^d ≤ m := Nat.pow_le_pow_right (by omega) (by omega)
  have hFit := placedRankFits_of_cut hd hn hB
  have hnB : n < B := by have := hFit.layout.s_b; omega
  have hD : (d+1)+(d+1)<B := by change S+m+m+10<B at hB; omega
  have hzS : Z+4≤S := hFit.layout.z_s
  have hOutZ : placedRankOutput m+n*n≤Z := hFit.layout.out_z
  have hAugOut : placedRankAugmented m+n*(n^d+n)≤placedRankOutput m := hFit.layout.am_out
  have hRB : placedRankRows m+n^d*n≤placedRankAugmented m := hFit.rows_before_augmented
  have hSrc : placedRankSource m+n^d*n≤placedRankRows m := hFit.source_before_rows
  have hMainBound : S+m+m+10<B := hB
  have hLive : m<B := by omega
  have hZBound : Z+3<B := by omega
  have hOutBound : placedRankOutput m<B :=
    (Nat.le_add_right _ _).trans_lt (hOutZ.trans_lt (by omega))
  have hAugBound : placedRankAugmented m<B :=
    (Nat.le_add_right _ _).trans_lt (hAugOut.trans_lt hOutBound)
  have hRowsBound : placedRankRows m<B :=
    (Nat.le_add_right _ _).trans_lt (hRB.trans_lt hAugBound)
  have hSrcBound : placedRankSource m<B :=
    (Nat.le_add_right _ _).trans_lt (hSrc.trans_lt hRowsBound)
  let σ₀ := σ.setVar cutRankRawOrder ((d+1)+(d+1))
  let ρ := σ₀.setVar cutRankRawWidth n
  have r₀ : Run B (.assign cutRankRawOrder (.get rawPairIO.array (.lit 0))) σ σ₀ 3 :=
    Run.assign (evalB_get (evalB_lit (by omega)) (by rw [hHead]; rfl) hD)
  have r₁ : Run B (.assign cutRankRawWidth (.get rawPairIO.array (.lit 1))) σ₀ ρ 3 :=
    Run.assign (evalB_get (evalB_lit (by omega)) (by change (σ.arrs rawPairIO.array)[1]? = _; rw [hHead]; rfl) hnB)
  have getV {r : String} {w : ℕ} (h : ρ.vars r=w) (hw : w<B) :
      (Expr.var r).evalB B ρ = some w := evalB_var_iff.mpr ⟨h.symm,h ▸ hw⟩
  have hh : ρ.vars shapePower.out=m := by
    change σ.vars shapePower.out=m
    exact hSide
  have eOrder := getV (r:=cutRankRawOrder) (w:=(d+1)+(d+1)) (by rfl) hD
  have eWidth := getV (r:=cutRankRawWidth) (w:=n) (by rfl) hnB
  have eM := getV hh hLive
  have eLimit : (Expr.bin .div (.var cutRankRawOrder) (.lit 2)).evalB B ρ=some (d+1) := by
    have e := evalB_bin (op:=.div) eOrder (evalB_lit (by omega : 2<B))
      (show ((d+1)+(d+1))/2<B by omega)
    simpa [Bop.apply,
      show ((d+1)+(d+1))/2=d+1 by omega] using e
  have eRows : (Expr.bin .div (.var shapePower.out) (.var cutRankRawWidth)).evalB B ρ=some (n^d) := by
    have hDiv : m/n=n^d := by
      change n^(d+1)/n=n^d
      rw [pow_succ,Nat.mul_div_cancel _ (by omega)]
    have e := evalB_bin (op:=.div) eM eWidth (show m/n<B by rw [hDiv]; omega)
    simpa [Bop.apply,hDiv] using e
  have ev (a : Address) (ha : a.value m<B) : a.expr.evalB B ρ=some (a.value m) :=
    Address.eval hh hPos a ha
  let vals := rankInstalledVars d n m
  let τ := install vals ρ
  have hSρ : Slots F canonical qN.WS S B ρ :=
    Slots.setVar F canonical (Slots.setVar F canonical hS (by decide) (by decide) _)
      (by decide) (by decide) _
  have hEval : List.Forall₂ (fun (p : String × Expr) v => p.2.evalB B ρ=some v)
      cutRankAssign (vals.map Prod.snd) := by
    refine .cons eLimit (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_
      (.cons eRows (.cons eWidth (.cons ?_ (.cons ?_ (.cons ?_ .nil))))))))))
    · have hSrcAddr : (rankAddressOffset 0).value m = placedRankSource m := by
        simp [rankAddressOffset,placedRankSource,Address.value]
      simpa only [hSrcAddr] using ev (rankAddressOffset 0) (by simpa only [hSrcAddr] using hSrcBound)
    · exact ev _ (by change Z+2<B; omega)
    · exact ev _ (by change Z+3<B; omega)
    · exact ev _ (by change Z<B; omega)
    · exact ev _ (by change Z+1<B; omega)
    · exact ev _ (show placedRankRows m<B from hRowsBound)
    · exact ev _ (show placedRankAugmented m<B from hAugBound)
    · exact ev _ (show placedRankOutput m<B from hOutBound)
  have hNoVar : ∀ p ∈ cutRankAssign, ∀ q ∈ cutRankAssign, NoVar p.1 q.2 := by
    intro p hp q hq
    have hFresh : p.1 ≠ cutRankRawOrder ∧ p.1 ≠ cutRankRawWidth ∧ p.1 ≠ shapePower.out := by
      simp only [cutRankAssign,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with e|e|e|e|e|e|e|e|e|e|e <;> rw [e] <;> simp only [Prod.fst] <;> decide
    simp only [cutRankAssign,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with e|e|e|e|e|e|e|e|e|e|e <;> rw [e] <;> simp only [Prod.snd]
    all_goals first
      | exact Address.noVar _ hFresh.2.2
      | simp [NoVar,hFresh.1,hFresh.2.1,hFresh.2.2,
          Ne.symm hFresh.1,Ne.symm hFresh.2.1,Ne.symm hFresh.2.2]
  have hZip : List.zip (cutRankAssign.map Prod.fst) (vals.map Prod.snd)=vals := by rfl
  have r₂ : Run B (commands cutRankAssign) ρ τ (((cutRankAssign.map fun p => p.2.size+1).sum)+1) := by
    have hRun := commands_run cutRankAssign (vals.map Prod.snd) ρ (by rfl) hEval hNoVar
    rwa [hZip] at hRun
  have hKeep (r : String) (hr : r ∉ vals.map Prod.fst) : τ.vars r=ρ.vars r :=
    installed_scalar _ _ _ (fun p hp he => hr (List.mem_map.mpr ⟨p,hp,he.symm⟩))
  have hws : τ.vars qN.WS=σ.vars qN.WS := by
    have h0 : qN.WS ∉ (rankInstalledVars d n m).map Prod.fst := by
      simpa only [rankInstalledVars,List.map_cons,List.map_nil,Prod.fst] using
        (show qN.WS ∉ (rankInstalledVars 0 0 0).map Prod.fst by decide)
    exact (hKeep _ h0).trans rfl
  have hFrame := installed_arrays vals ρ
  have v (s : ℕ) : val F canonical qN.WS τ s=val F canonical qN.WS σ s := by
    unfold val slice
    rw [hws,show τ.arrs=σ.arrs from hFrame.1]
  refine ⟨τ,(r₀.seq (r₁.seq r₂)).mono (by unfold cutRankConfigCost; omega),
    ⟨installed_slots F vals ρ hSρ (rankInstalledVars_names d n m),?_,
      fun u => (v _).trans (hForm u),(v _).trans hZero,(v _).trans hOne⟩,
    v,?_,hFrame.1,hFrame.2.1,hFrame.2.2⟩
  · intro p hp
    simp only [cutRankArgs,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with he|he|he|he|he|he|he|he|he|he|he|he <;> rw [he] <;>
      first | rfl | exact hws.trans hABI
  · intro r hr h0 h1
    exact (hKeep r hr).trans (by simp [ρ,σ₀,h0,h1])

#print axioms cutRankConfigure_run
end EvenTI.P12ComparePrep
