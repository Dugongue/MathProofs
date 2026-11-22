import EvenP22SiteCompare

namespace EvenTI.P22Site.Lookup
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18PairLargeFinalLoop20261004

set_option autoImplicit false
set_option maxHeartbeats 700000

def cursor : String := "even.P22.site.lookup.cursor"
def count : String := "even.P22.site.lookup.count"
def answer : String := "even.P22.site.lookup.answer"
def hit : Cond := .eq (.var Compare.flag) (.lit 1)
def saveHit : Com := .ite hit (.assign answer (.var cursor)) .skip

def body (src dst : String) : Com :=
  .seq (.assign cD (.mul (.var cursor) (.var cCnt)))
    (.seq (Compare.code src dst) saveHit)

def program (src dst : String) : Com := forLoop cursor count (body src dst)

/-- A real paid nested loop over every candidate byte row. The exact match
 relation is a semantic specification of the installed bytes, not a callable
 oracle. The polynomial archive wrapper supplies it by unique raw keys. -/
theorem run (src dst : String) {B a n M target : ℕ} {σ : Env}
    (hB : 1 < B) (hM : M < B) (ht : target < M)
    (hs : σ.vars cS = a) (hn : σ.vars cCnt = n) (hc : σ.vars count = M)
    (hfitA : a+n ≤ (σ.arrs src).length) (hfitB : M*n ≤ (σ.arrs dst).length)
    (hsizeA : (σ.arrs src).length < B) (hsizeB : (σ.arrs dst).length < B)
    (hwordA : ∀ k < n, (σ.arrs src).getD (a+k) 0 < B)
    (hwordB : ∀ i < M, ∀ k < n, (σ.arrs dst).getD (i*n+k) 0 < B)
    (hmatch : ∀ i < M,
      (∀ k < n, (σ.arrs src).getD (a+k) 0 = (σ.arrs dst).getD (i*n+k) 0) ↔ i=target) :
    ∃ τ, Run B (program src dst) σ τ ((20*n+40)*M+6) ∧
      τ.vars answer = target ∧ τ.arrs = σ.arrs ∧
      τ.inp = σ.inp ∧ τ.out = σ.out ∧ Frame (program src dst) σ τ := by
  let I (i : ℕ) (ρ : Env) : Prop :=
    ρ.arrs = σ.arrs ∧ ρ.vars cS = a ∧ ρ.vars cCnt = n ∧
      ρ.vars answer = (if target < i then target else σ.vars answer) ∧
      ρ.inp = σ.inp ∧ ρ.out = σ.out
  have h0 : I 0 (σ.setVar cursor 0) := by
    exact ⟨rfl,by simpa [show cS ≠ cursor by decide] using hs,
      by simpa [show cCnt ≠ cursor by decide] using hn,
      by simp [show answer ≠ cursor by decide],rfl,rfl⟩
  obtain ⟨τ,hr,hI,hend⟩ := forLoop_run (B:=B) (n:=M) (P:=20*n+32)
    cursor count (body src dst) (by decide) I hc hM h0 (by
      intro i hi ρ hρ hix hcnt
      obtain ⟨harr,hsrc,hnρ,hans,hin,hout⟩ := hρ
      have hprod : i*n+n ≤ M*n := by
        calc
          _ = (i+1)*n := by ring
          _ ≤ M*n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hi)
      have hprodB : i*n < B := by omega
      have ee : (Expr.mul (.var cursor) (.var cCnt)).evalB B ρ = some (i*n) := by
        have h := evalB_bin (op:=Bop.mul)
          (evalB_var (σ:=ρ) (x:=cursor) (B:=B) (by omega))
          (evalB_var (x:=cCnt) (by omega)) (by change ρ.vars cursor*ρ.vars cCnt < B; rw [hix,hnρ]; exact hprodB)
        simpa only [hix,hnρ,Bop.apply] using h
      let η := ρ.setVar cD (i*n)
      have ra : Run B (.assign cD (.mul (.var cursor) (.var cCnt))) ρ η 4 := Run.assign ee
      obtain ⟨ζ,rz,hflag,hkey,hvars,harrζ,hinζ,houtζ⟩ := Compare.words_run src dst
        (σ:=η) (a:=a) (b:=i*n) (n:=n) hB
        (by simpa [η,show cS ≠ cD by decide] using hsrc)
        (by simp [η])
        (by simpa [η,show cCnt ≠ cD by decide] using hnρ)
        (by simpa only [η,arrs_setVar,harr] using hfitA)
        (by simpa only [η,arrs_setVar,harr] using hprod.trans hfitB)
        (by simpa only [η,arrs_setVar,harr] using hsizeA)
        (by simpa only [η,arrs_setVar,harr] using hsizeB)
        (by simpa only [η,arrs_setVar,harr] using hwordA)
        (by simpa only [η,arrs_setVar,harr] using hwordB i hi)
      have hzA : ζ.arrs = σ.arrs := harrζ.trans harr
      have hzIn : ζ.inp = σ.inp := hinζ.trans hin
      have hzOut : ζ.out = σ.out := houtζ.trans hout
      have hzV (x : String) (hx : x ≠ cIdx) (hf : x ≠ Compare.flag) (hd : x ≠ cD) :
          ζ.vars x = ρ.vars x := (hvars x hx hf).trans (by simp [η,hd])
      have hzix : ζ.vars cursor = i := (hzV _ (by decide) (by decide) (by decide)).trans hix
      have hzcnt : ζ.vars count = M := (hzV _ (by decide) (by decide) (by decide)).trans hcnt
      have hzsrc : ζ.vars cS = a := (hzV _ (by decide) (by decide) (by decide)).trans hsrc
      have hzn : ζ.vars cCnt = n := (hzV _ (by decide) (by decide) (by decide)).trans hnρ
      have hzans : ζ.vars answer = if target < i then target else σ.vars answer :=
        (hzV _ (by decide) (by decide) (by decide)).trans hans
      have hk : ζ.vars Compare.flag = 1 ↔ i=target := by
        exact hkey.trans (by simpa only [η,arrs_setVar,harr] using hmatch i hi)
      have ec := evalB_condEq
        (evalB_var (σ:=ζ) (x:=Compare.flag) (B:=B) (by omega))
        (evalB_lit (σ:=ζ) (B:=B) (n:=1) hB)
      by_cases he : i=target
      · have hf := hk.mpr he
        have eh : hit.evalB B ζ = some true := by simpa [hit,hf] using ec
        have ev : (Expr.var cursor).evalB B ζ = some i := by
          simpa only [hzix] using evalB_var (σ:=ζ) (x:=cursor) (B:=B) (by omega)
        let δ := ζ.setVar answer i
        have rs : Run B saveHit ζ δ 7 := (Run.ite_true eh (Run.assign ev)).mono (by simp [hit,Cond.size,Expr.size])
        have rr : Run B (body src dst) ρ δ (20*n+32) :=
          (ra.seq (rz.seq rs)).mono (by omega)
        refine ⟨δ,rr,by simpa [δ,show cursor ≠ answer by decide] using hzix,
          by simpa [δ,show count ≠ answer by decide] using hzcnt,?_⟩
        refine ⟨hzA,?_,?_,?_,hzIn,hzOut⟩
        · simpa [δ,show cS ≠ cursor by decide,show cS ≠ answer by decide] using hzsrc
        · simpa [δ,show cCnt ≠ cursor by decide,show cCnt ≠ answer by decide] using hzn
        · have ht' : target < i+1 := by omega
          simp [δ,show answer ≠ cursor by decide,ht',he]
      · have hf : ζ.vars Compare.flag ≠ 1 := fun h => he (hk.mp h)
        have eh : hit.evalB B ζ = some false := by simpa [hit,hf] using ec
        have rs : Run B saveHit ζ ζ 7 := (Run.ite_false eh Run.skip).mono (by simp [hit,Cond.size,Expr.size])
        have rr : Run B (body src dst) ρ ζ (20*n+32) :=
          (ra.seq (rz.seq rs)).mono (by omega)
        refine ⟨ζ,rr,hzix,hzcnt,hzA,?_,?_,?_,hzIn,hzOut⟩
        · simpa [show cS ≠ cursor by decide] using hzsrc
        · simpa [show cCnt ≠ cursor by decide] using hzn
        · have heq : (target < i) ↔ target < i+1 := by omega
          simpa only [vars_setVar,show answer ≠ cursor by decide,if_false,← heq] using hzans)
  obtain ⟨harr,_,_,hans,hin,hout⟩ := hI
  have ans : τ.vars answer = target := by simpa only [if_pos ht] using hans
  exact ⟨τ,hr,ans,harr,hin,hout,Frame.of_run hr⟩

open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem17Primary47ExternalArchive (Archived)
open scoped Polynomial

/-- Physical finite-row lookup specialized to two actual archives. Coverage,
 uniqueness and the matching target are derived from the stored raw keys. -/
theorem archive_run {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (F : FieldPresentation K) {σ : Env} {a am b bm : String} {cap B : ℕ}
    {f : K[X]} {L M : List K[X]}
    (ha : Archived F a am cap f L σ) (hb : Archived F b bm cap f M σ)
    (hf : f ≠ 0) (hc : f.natDegree < cap) (i : Fin L.length)
    (hp : F.p < B) (h1 : 1 < B) (hM : M.length < B)
    (hs : σ.vars cS = F.e*(i.val*cap))
    (hn : σ.vars cCnt = cap*F.e) (hcount : σ.vars count = M.length)
    (hfitA : F.e*(i.val*cap)+cap*F.e ≤ (σ.arrs a).length)
    (hfitB : M.length*(cap*F.e) ≤ (σ.arrs b).length)
    (hsizeA : (σ.arrs a).length < B) (hsizeB : (σ.arrs b).length < B) :
    ∃ τ, Run B (program a b) σ τ ((20*(cap*F.e)+40)*M.length+6) ∧
      τ.vars answer = (Keys.archiveEquiv F ha hb hf hc i).val ∧
      τ.arrs = σ.arrs ∧ τ.inp = σ.inp ∧ τ.out = σ.out ∧
      Frame (program a b) σ τ := by
  let target := Keys.archiveEquiv F ha hb hf hc i
  have htarget : Keys.rowKey F σ b cap target.val = Keys.rowKey F σ a cap i.val := by
    apply (Keys.rowKey_eq_iff F hb ha hf hc target i).mpr
    exact (Compare.archiveEquiv_polynomial F ha hb hf hc i).symm
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
    exact (F.coordinate ((P.get idx).coeff (cap-1-c.val)) t).isLt.trans hp
  apply run a b h1 hM target.isLt hs hn hcount hfitA hfitB hsizeA hsizeB
    (word a am L ha i)
  · intro j hj k hk
    have hw := word b bm M hb ⟨j,hj⟩ k hk
    have hoff : j*(cap*F.e) = F.e*(j*cap) := by ring
    simpa only [hoff] using hw
  · intro j hj
    have hlinear :
        (∀ k < cap*F.e, (σ.arrs a).getD (F.e*(i.val*cap)+k) 0 =
          (σ.arrs b).getD (j*(cap*F.e)+k) 0) ↔
        Keys.rowKey F σ a cap i.val = Keys.rowKey F σ b cap j := by
      have hoff : j*(cap*F.e) = F.e*(j*cap) := by ring
      simpa only [hoff] using Compare.words_iff_key F σ a b cap i.val j
    rw [hlinear]
    constructor
    · intro hkey
      have heq : (⟨j,hj⟩ : Fin M.length) = target :=
        Keys.rowKey_injective F hb hf hc (hkey.symm.trans htarget.symm)
      exact congrArg Fin.val heq
    · intro hjt
      simpa only [hjt] using htarget.symm
def loadAnswer (sites : String) : Com := .assign answer (.get sites (.var answer))

/-- Finish a successful row lookup by reading the actual installed native
 slot/address word at that index. -/
theorem loadAnswer_run (sites : String) {σ : Env} {B idx value : ℕ}
    (hidx : σ.vars answer = idx) (hfit : idx < (σ.arrs sites).length)
    (hsize : (σ.arrs sites).length < B)
    (hvalue : (σ.arrs sites).getD idx 0 = value) (hword : value < B) :
    ∃ τ, Run B (loadAnswer sites) σ τ 3 ∧ τ.vars answer = value ∧
      τ.arrs = σ.arrs ∧ τ.inp = σ.inp ∧ τ.out = σ.out ∧
      Frame (loadAnswer sites) σ τ := by
  have ee : (Expr.var answer).evalB B σ = some idx := by
    simpa only [hidx] using evalB_var (σ:=σ) (x:=answer) (B:=B) (by omega)
  have hg : (σ.arrs sites)[idx]? = some value := by
    rw [← hvalue,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hfit]
    rfl
  have hr : Run B (loadAnswer sites) σ (σ.setVar answer value) 3 :=
    Run.assign (evalB_get ee hg hword)
  exact ⟨σ.setVar answer value,hr,by simp,rfl,rfl,rfl,Frame.of_run hr⟩
#print axioms loadAnswer_run
#print axioms archive_run
#print axioms run
end EvenTI.P22Site.Lookup





