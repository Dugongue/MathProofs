import EvenP17TrialReciprocalSweep
import EvenP17ExecutionCells

set_option autoImplicit false
set_option maxHeartbeats 550000

namespace EvenTI.P19Trial

open EvenTI.Action EvenTI.Contract EvenTI.PrimaryAlignment EvenTI.TrialProducer EvenTI.P10Scan
open Mathproof.EvenTI.Reciprocal.Coverage (HigherModes)
open EvenTI.P17Trial EvenTI.P17Execution
open EvenTI.P16Execution (crossN crossA crossStride)
open Lax13Proofs.Imp Lax13Proofs.Reasoning

theorem singularOrder_fromReciprocal {l : ℕ} (i : Fin ((l+1)+(l+1))) :
    singularOrder l i=((reciprocalOrder l i).2,!(reciprocalOrder l i).1) := by
  refine Fin.addCases ?_ ?_ i
  · intro j
    rw [reciprocalOrder_first]
    change ((Equiv.boolProdEquivSum (Fin (l+1))).symm
      (finSumFinEquiv.symm (Fin.castAdd (l+1) j))).swap = (j,false)
    rw [finSumFinEquiv_symm_apply_castAdd] <;> rfl
  · intro j
    rw [reciprocalOrder_second]
    change ((Equiv.boolProdEquivSum (Fin (l+1))).symm
      (finSumFinEquiv.symm (Fin.natAdd (l+1) j))).swap = (j,true)
    rw [finSumFinEquiv_symm_apply_natAdd] <;> rfl

/-- The singular order reverses the Boolean labels of the checked
reciprocal sweep. Both retain increasing mode index inside each side. -/
theorem higherTwoSweeps_run {B n l : ℕ}
    (visit : Bool → Com) (cost : Bool → ℕ) (ctx : Env → Prop)
    (payload : (Fin (l+1) × Bool) → List ℕ)
    (hn : 2≤n) (hnB : n<B) (haB : n^l<B) (hlB : l+1<B)
    (hIdx : ∀ τ i, ctx τ → ctx (τ.setVar reciprocalSweepIndex i))
    (hStride : ∀ τ k, ctx τ → ctx (τ.setVar crossStride k))
    (hVisit : ∀ (side : Bool) ρ (i : Fin (l+1)), ctx ρ →
      ρ.vars reciprocalSweepIndex=i.val → ρ.vars crossStride=n^(l-i.val) → ρ.vars crossN=n →
      ∃ τ, Run B (visit side) ρ τ (cost side) ∧ ctx τ ∧ τ.vars reciprocalSweepIndex=i.val ∧
        τ.vars crossStride=n^(l-i.val) ∧ τ.vars crossN=ρ.vars crossN ∧ τ.vars crossA=ρ.vars crossA ∧
        τ.vars reciprocalSweepLimit=ρ.vars reciprocalSweepLimit ∧ τ.inp=ρ.inp ∧
        τ.out=ρ.out++payload (i,side))
    {σ : Env} (hCtx : ctx σ) (hN : σ.vars crossN=n) (hA : σ.vars crossA=n^l)
    (hL : σ.vars reciprocalSweepLimit=l+1) :
    ∃ τ, Run B (reciprocalTwoSweeps (visit false) (visit true)) σ τ
      (((cost false+12)*(l+1)+8)+((cost true+12)*(l+1)+8)) ∧
      ctx τ ∧ τ.inp=σ.inp ∧ τ.out=σ.out++(List.ofFn (fun i => payload (singularOrder l i))).flatten := by
  let p : HigherModes l → List ℕ := fun i => payload (i.2,!i.1)
  obtain ⟨τ,r,hτ,hI,hOut⟩ := reciprocalTwoSweeps_run (fun b => visit (!b)) (fun b => cost (!b))
    ctx p hn hnB haB hlB hIdx hStride
    (fun b ρ i h hI hS hN => hVisit (!b) ρ i h hI hS hN) hCtx hN hA hL
  have hOrder : (fun i => p (reciprocalOrder l i))=(fun i => payload (singularOrder l i)) := by
    funext i
    rw [singularOrder_fromReciprocal]
  exact ⟨τ,r,hτ,hI,hOrder ▸ hOut⟩

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

private theorem lengths_flatMap {α : Type} (xs : List α) (enc : α → List ℕ)
    (w : ℕ) (hw : ∀ a ∈ xs, (enc a).length=w) : (xs.flatMap enc).length=xs.length*w := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.flatMap_cons,List.length_append,List.length_cons,
      hw a List.mem_cons_self,ih (fun b hb => hw b (List.mem_cons_of_mem _ hb)),Nat.add_mul,Nat.one_mul]
    omega

theorem higherTrialWords_exact (D : FieldEncoding K) {l n : ℕ}
    (ell rho : Coord (l+1) n → K) (A : Fin (l+1) × Bool → Matrix (Fin n) (Fin n) K) :
    let p := (PreparedTrial.higher (ell,rho) A : PreparedTrial K l n)
    let q := (l+1)+(l+1)
    preparedTrialWords D p =
      [2,1+q*(n*n+2),q] ++
      (List.ofFn (fun i => blockW (numberedAnchorWords D (numeric (A (singularOrder l i)))))).flatten ++
      (cutFormWords D ell ++ cutFormWords D rho) := by
  dsimp only
  let p := (PreparedTrial.higher (ell,rho) A : PreparedTrial K l n)
  let q := (l+1)+(l+1)
  let xs := numberedAnchors p
  let ys := xs.map (numberedAnchorWords D)
  have hx : xs.length=q := by simp [xs,p,numberedAnchors,q] <;> omega
  have hy : ys.length=q := by simp [ys,hx]
  have hBlock (w : List ℕ) (hw : w ∈ ys) : (blockW w).length=n*n+2 := by
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hw
    have hb' : b ∈ List.ofFn (fun i : Fin q => numeric (A (singularOrder l i))) := hb
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hb'
    simp [blockW,numberedAnchorWords,numeric,Nat.add_assoc]
  have hLen := lengths_flatMap ys blockW (n*n+2) hBlock
  have hE : (listW ys).length=1+q*(n*n+2) := by
    simp only [listW,List.length_cons,hLen,hy]
    omega
  have hPay : ys.flatMap blockW =
      (List.ofFn (fun i => blockW (numberedAnchorWords D (numeric (A (singularOrder l i)))))).flatten := by
    dsimp only [ys,xs,p,numberedAnchors]
    simp only [List.flatMap_def,List.map_ofFn,Function.comp_def]
  change 2::pairW (listW ys) (cutFormWords D ell ++ cutFormWords D rho) =
    [2,1+q*(n*n+2),q] ++ _ ++ _
  unfold pairW
  rw [hE,←hPay]
  simp only [listW,hy,List.append_assoc,List.cons_append,List.nil_append]

#print axioms singularOrder_fromReciprocal
#print axioms higherTwoSweeps_run
#print axioms higherTrialWords_exact
end EvenTI.P19Trial
