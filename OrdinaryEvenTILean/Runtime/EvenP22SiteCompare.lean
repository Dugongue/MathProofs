import EvenP22SiteKeys
import Mathproof.Meta.Problem18PairLargeFinalLoop20261004

namespace EvenTI.P22Site.Compare
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18PairLargeFinalLoop20261004
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem17Primary47ExternalArchive (Archived)
open scoped Polynomial

set_option autoImplicit false
set_option maxHeartbeats 500000

def flag : String := "even.P22.site.key.equal"
def code (src dst : String) : Com :=
  .seq (.assign flag (.lit 1)) (cmpLoop src flag (rhsPair dst) 0)

/-- Paid direct comparison of immutable external byte windows, without copying
 either polynomial into the field workspace. -/
theorem words_run (src dst : String) {B a b n : ℕ} {σ : Env}
    (hB : 1 < B)
    (hs : σ.vars cS = a) (hd : σ.vars cD = b) (hn : σ.vars cCnt = n)
    (hfitA : a+n ≤ (σ.arrs src).length) (hfitB : b+n ≤ (σ.arrs dst).length)
    (hsizeA : (σ.arrs src).length < B) (hsizeB : (σ.arrs dst).length < B)
    (hwordA : ∀ k < n, (σ.arrs src).getD (a+k) 0 < B)
    (hwordB : ∀ k < n, (σ.arrs dst).getD (b+k) 0 < B) :
    ∃ τ, Run B (code src dst) σ τ (20*n+8) ∧
      τ.vars flag ≤ 1 ∧
      (τ.vars flag = 1 ↔ ∀ k < n,
        (σ.arrs src).getD (a+k) 0 = (σ.arrs dst).getD (b+k) 0) ∧
      (∀ x, x ≠ cIdx → x ≠ flag → τ.vars x = σ.vars x) ∧
      τ.arrs = σ.arrs ∧ τ.inp = σ.inp ∧ τ.out = σ.out := by
  classical
  let ρ := σ.setVar flag 1
  have r0 : Run B (.assign flag (.lit 1)) σ ρ 2 := Run.assign (evalB_lit hB)
  have hρs : ρ.vars cS = a := by simpa [ρ,show cS ≠ flag by decide] using hs
  have hρd : ρ.vars cD = b := by simpa [ρ,show cD ≠ flag by decide] using hd
  have hρn : ρ.vars cCnt = n := by simpa [ρ,show cCnt ≠ flag by decide] using hn
  obtain ⟨τ,hr,hfl,hv,ha,hi,ho⟩ := cmpLoop_run
    (B:=B) (n:=n) src flag (rhsPair dst) 0 (by decide) (by decide) (by decide)
    hρs hρn hfitA hsizeA hwordA (by omega)
    (fun k => (ρ.arrs dst).getD (b+k) 0) (by
      intro η harr hvars hk
      have hb : η.vars cD = b := (hvars _ (by decide) (by decide)).trans hρd
      have hix : b+η.vars cIdx < (ρ.arrs dst).length := by
        change b+η.vars cIdx < (σ.arrs dst).length
        omega
      have e : (Expr.add (.var cD) (.var cIdx)).evalB B η = some (b+η.vars cIdx) := by
        have h := evalB_bin (op:=Bop.add)
          (evalB_var (σ:=η) (x:=cD) (B:=B) (by rw [hb]; omega))
          (evalB_var (x:=cIdx) (by omega)) (by change η.vars cD+η.vars cIdx < B; omega)
        simpa only [hb,Bop.apply] using h
      have hg : (η.arrs dst)[b+η.vars cIdx]? =
          some ((ρ.arrs dst).getD (b+η.vars cIdx) 0) := by
        rw [harr,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hix]
        rfl
      exact evalB_get e hg (hwordB _ hk))
  have hflag : τ.vars flag =
      if ∀ k < n, (σ.arrs src).getD (a+k) 0 = (σ.arrs dst).getD (b+k) 0 then 1 else 0 := by
    simpa [ρ] using hfl
  refine ⟨τ,(r0.seq hr).mono (by simp [code,rhsPair,Expr.size]; omega),?_,?_,?_,ha,hi,ho⟩
  · rw [hflag]
    split <;> omega
  · rw [hflag]
    by_cases h : ∀ k < n, (σ.arrs src).getD (a+k) 0 = (σ.arrs dst).getD (b+k) 0
    · rw [if_pos h]
      exact ⟨fun _ => h,fun _ => rfl⟩
    · rw [if_neg h]
      exact ⟨by omega,fun hp => False.elim (h hp)⟩
  · intro x hx hf
    exact (hv x hx hf).trans (by simp [ρ,hf])

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- Linear byte-window equality is the exact two-coordinate row key equality. -/
theorem words_iff_key (F : FieldPresentation K) (σ : Env) (a b : String)
    (cap i j : ℕ) :
    (∀ k < cap*F.e,
      (σ.arrs a).getD (F.e*(i*cap)+k) 0 =
      (σ.arrs b).getD (F.e*(j*cap)+k) 0) ↔
    Keys.rowKey F σ a cap i = Keys.rowKey F σ b cap j := by
  have he := F.degree_pos
  constructor
  · intro h
    funext kt
    rcases kt with ⟨k,t⟩
    have hb : F.e*k.val+t.val < cap*F.e := by
      calc
        _ < F.e*(k.val+1) := by rw [Nat.mul_add,Nat.mul_one]; omega
        _ ≤ _ := by simpa only [Nat.mul_comm] using Nat.mul_le_mul_left F.e (Nat.succ_le_of_lt k.isLt)
    have hh := h (F.e*k.val+t.val) hb
    simpa only [Keys.rowKey,Nat.mul_add,Nat.add_assoc] using hh
  · intro h k hk
    let c : Fin cap := ⟨k/F.e,(Nat.div_lt_iff_lt_mul he).2 hk⟩
    let t : Fin F.e := ⟨k%F.e,Nat.mod_lt _ he⟩
    have hh := congrFun h (c,t)
    have hd : F.e*c.val+t.val = k := by
      simpa only [c,t,Nat.mul_comm] using Nat.div_add_mod k F.e
    change (σ.arrs a).getD (F.e*(i*cap+c.val)+t.val) 0 =
      (σ.arrs b).getD (F.e*(j*cap+c.val)+t.val) 0 at hh
    have e1 : F.e*(i*cap+c.val)+t.val = F.e*(i*cap)+k := by rw [Nat.mul_add,Nat.add_assoc,hd]
    have e2 : F.e*(j*cap+c.val)+t.val = F.e*(j*cap)+k := by rw [Nat.mul_add,Nat.add_assoc,hd]
    simpa only [e1,e2] using hh

/-- The checked paid comparison returns exactly polynomial equality for actual
 archived key windows, regardless of factor-table ordering. -/
theorem archive_run (F : FieldPresentation K)
    {σ : Env} {a am b bm : String} {cap B : ℕ} {f : K[X]} {L M : List K[X]}
    (ha : Archived F a am cap f L σ) (hb : Archived F b bm cap f M σ)
    (hf : f ≠ 0) (hc : f.natDegree < cap) (i : Fin L.length) (j : Fin M.length)
    (hB : F.p < B) (h1 : 1 < B)
    (hs : σ.vars cS = F.e*(i.val*cap)) (hd : σ.vars cD = F.e*(j.val*cap))
    (hn : σ.vars cCnt = cap*F.e)
    (hfitA : F.e*(i.val*cap)+cap*F.e ≤ (σ.arrs a).length)
    (hfitB : F.e*(j.val*cap)+cap*F.e ≤ (σ.arrs b).length)
    (hsizeA : (σ.arrs a).length < B) (hsizeB : (σ.arrs b).length < B) :
    ∃ τ, Run B (code a b) σ τ (20*(cap*F.e)+8) ∧
      τ.vars flag ≤ 1 ∧ (τ.vars flag = 1 ↔ L.get i = M.get j) ∧
      (∀ x, x ≠ cIdx → x ≠ flag → τ.vars x = σ.vars x) ∧
      τ.arrs = σ.arrs ∧ τ.inp = σ.inp ∧ τ.out = σ.out := by
  have word (words mult : String) (P : List K[X])
      (h : Archived F words mult cap f P σ) (idx : Fin P.length)
      (k : ℕ) (hk : k < cap*F.e) :
      (σ.arrs words).getD (F.e*(idx.val*cap)+k) 0 < B := by
    let c : Fin cap := ⟨k/F.e,(Nat.div_lt_iff_lt_mul F.degree_pos).2 hk⟩
    let t : Fin F.e := ⟨k%F.e,Nat.mod_lt _ F.degree_pos⟩
    have hd : F.e*c.val+t.val = k := by
      simpa only [c,t,Nat.mul_comm] using Nat.div_add_mod k F.e
    have heq : F.e*(idx.val*cap)+k = F.e*(idx.val*cap+c.val)+t.val := by
      rw [Nat.mul_add,Nat.add_assoc,hd]
    rw [heq]
    change Keys.rowKey F σ words cap idx.val (c,t) < B
    rw [Keys.rowKey_decode F h idx c t]
    exact (F.coordinate ((P.get idx).coeff (cap-1-c.val)) t).isLt.trans hB
  obtain ⟨τ,hr,hv,hq,hvars,harr,hin,hout⟩ := words_run a b h1 hs hd hn hfitA hfitB hsizeA hsizeB
    (word a am L ha i) (word b bm M hb j)
  exact ⟨τ,hr,hv,hq.trans ((words_iff_key F σ a b cap i.val j.val).trans
    (Keys.rowKey_eq_iff F ha hb hf hc i j)),hvars,harr,hin,hout⟩

/-- The finite raw-byte matcher selects precisely the same polynomial even
 when both tables have unrelated physical orders. -/
theorem archiveEquiv_polynomial (F : FieldPresentation K)
    {σ : Env} {a am b bm : String} {cap : ℕ} {f : K[X]} {L M : List K[X]}
    (ha : Archived F a am cap f L σ) (hb : Archived F b bm cap f M σ)
    (hf : f ≠ 0) (hc : f.natDegree < cap) (i : Fin L.length) :
    L.get i = M.get (Keys.archiveEquiv F ha hb hf hc i) := by
  apply ((Keys.rowKey_eq_iff F ha hb hf hc i _)).mp
  symm
  unfold Keys.archiveEquiv
  exact Keys.keyEquiv_spec (A:=Fin cap × Fin F.e → ℕ)
    (fun i : Fin L.length => Keys.rowKey F σ a cap i.val)
    (fun j : Fin M.length => Keys.rowKey F σ b cap j.val) _ _ _ _ i
#print axioms archiveEquiv_polynomial
#print axioms words_run
#print axioms words_iff_key
#print axioms archive_run
end EvenTI.P22Site.Compare





