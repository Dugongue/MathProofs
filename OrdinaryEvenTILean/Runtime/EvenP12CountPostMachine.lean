import EvenP12CountPostLoop
import Mathproof.Meta.Problem18IMPPolynomialCompiler20261001
import Mathproof.Meta.Problem18RAMLax51ProofsRamToTMPolytime20261001

namespace EvenTI.P12CountPost

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Compile
open Mathproof.Problem18IMPPolynomialCompiler20261001
open Mathproof.Problem18IMPFieldAddition20261001 (getD_set_same getD_set_other)
open Lax51.BinaryWordEncoding Lax51.RamPolytime Lax51.TuringPolytime

set_option autoImplicit false
set_option maxHeartbeats 680000

variable {G : Type} [CommGroup G] {q : ℕ}

def collectRows (q : ℕ) : ℕ → List ℕ → List (Fin q → ℕ)
  | 0, _ => []
  | d + 1, w => (fun i => w.getD i.val 0) :: collectRows q d (w.drop q)

theorem collectRows_length (q d : ℕ) (xs : List ℕ) : (collectRows q d xs).length = d := by
  induction d generalizing xs with
  | zero => rfl
  | succ d ih => simp [collectRows, ih]

theorem collectRows_words (q d : ℕ) (xs : List ℕ) (h : q*d ≤ xs.length) :
    rowWords (collectRows q d xs) = xs.take (q*d) := by
  induction d generalizing xs with
  | zero => simp [collectRows, rowWords]
  | succ d ih =>
    have h₁ : q ≤ xs.length := by rw [Nat.mul_succ] at h; omega
    have h₂ : q*d ≤ (xs.drop q).length := by
      rw [Nat.mul_succ] at h
      simp only [List.length_drop]; omega
    have heq : (List.finRange q).map (fun i => xs.getD i.val 0) = xs.take q := by
      apply List.ext_getElem
      · simp [List.length_take, Nat.min_eq_left h₁]
      · intro i ha hb
        have hi : i < q := by simpa using ha
        simp [List.finRange, List.map_ofFn, List.getElem_ofFn, List.getElem_take,
          List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hi.trans_le h₁)]
    change (List.finRange q).map (fun i => xs.getD i.val 0) ++
      rowWords (collectRows q d (xs.drop q)) = _
    rw [heq, ih _ h₂, Nat.mul_succ, Nat.add_comm (q*d) q, List.take_add]

def initial (id : Fin q) (j : Fin q) : ℕ := if j = id then 1 else 0

def tableKernel (enum : Fin q ≃ G) : List ℕ → List ℕ
  | [] => [0]
  | d :: xs => if q*d ≤ xs.length then
      [finishRows enum (initial (enum.symm 1)) (collectRows q d xs) (enum.symm 1)] else [0]

def shapeTest (q : ℕ) : Cond :=
  .lt (.sub (.var "cd_len") (.lit 1)) (.mul (.lit q) (.var "cd_count"))

def tableProg (enum : Fin q ≃ G) : Com :=
  .seq (.read "cd_len")
    (.ite (.lt (.lit 0) (.var "cd_len"))
      (.seq (.read "cd_count")
        (.ite (shapeTest q) (.write (.lit 0))
          (.seq (.store "cd_old" (.lit (enum.symm 1).val) (.lit 1))
            (.seq (countLoop enum) (.write (.get "cd_old" (.lit (enum.symm 1).val)))))))
      (.write (.lit 0)))

def tableLayout : Layout :=
  ⟨["cd_len", "cd_count", "cd_answer"], ["cd_old", "cd_new", "cd_allow"], 16⟩

private theorem install_ok (a : String) (ha : a ∈ tableLayout.arrays)
    (E : Fin q → Expr) (hE : ∀ i, Expr.Ok tableLayout (E i) 1) (js : List (Fin q)) :
    Com.Ok tableLayout (install a E js) := by
  induction js with
  | nil => trivial
  | cons i js ih =>
    exact ⟨⟨ha, trivial, hE i, by decide⟩, ih⟩

private theorem readInstall_ok (js : List (Fin q)) :
    Com.Ok tableLayout (readInstall "cd_allow" js) := by
  induction js with
  | nil => trivial
  | cons i js ih =>
    change _ ∧ _ ∧ _; exact ⟨by simp [Com.Ok,tableLayout], by simp [Com.Ok,Expr.Ok,tableLayout], ih⟩

private theorem rowExpr_ok (enum : Fin q ≃ G) (j : Fin q) :
    Expr.Ok tableLayout (rowExpr enum j) 1 := by
  have h (xs : List (Fin q)) :
      Expr.Ok tableLayout (sumExpr (xs.map (rowTerm enum j))) 1 := by
    induction xs with
    | nil => trivial
    | cons k ks ih =>
      refine ⟨ih, ?_, by decide⟩
      simp [rowTerm, oneBit, Expr.Ok, tableLayout]
  exact h _

theorem tableProg_ok (enum : Fin q ≃ G) : Com.Ok tableLayout (tableProg enum) := by
  have hrow : Com.Ok tableLayout (rowProg enum) := by
    exact ⟨readInstall_ok _, install_ok _ (by decide) _ (rowExpr_ok enum) _,
      install_ok _ (by decide) _ (fun i => by simp [copyExpr,Expr.Ok,tableLayout]) _⟩
  simpa [tableProg, Com.Ok, Cond.Ok, Expr.Ok, tableLayout, shapeTest, countCond, countLoop, decCount,
    condExpr] using hrow

theorem tableProg_run {B : ℕ} (enum : Fin q ≃ G) (w : List ℕ)
    (h1 : 1 < B) (hq : q < B) (hLen : w.length < B)
    (hWord : ∀ a ∈ w, a < B) (hMul : ∀ a ∈ w, q*a < B)
    (hPow : q^w.length < B) :
    ∃ t, Run B (tableProg enum) (initEnv (fun _ => q) (w.length :: w)) t
      ((rowCost enum + 8)*w.length + 40) ∧ t.out = tableKernel enum w := by
  let s := initEnv (fun _ => q) (w.length :: w)
  let s₁ := {s.setVar "cd_len" w.length with inp := w}
  have hr : Run B (.read "cd_len") s s₁ 1 := Run.read rfl
  have hlo : (Expr.var "cd_len").evalB B s₁ = some w.length := by
    have he : s₁.vars "cd_len" = w.length := by simp [s₁]
    rw [← he]; exact evalB_var (by rw [he]; exact hLen)
  have hc := evalB_condLt (e := .lit 0) (evalB_lit (by omega : 0 < B)) hlo
  cases w with
  | nil =>
    have hc₀ : (Cond.lt (.lit 0) (.var "cd_len")).evalB B s₁ = some false := hc
    have hw₀ := Run.write (σ := s₁) (evalB_lit (by omega : 0 < B))
    refine ⟨_, (hr.seq (Run.ite_false hc₀ hw₀)).mono ?_, ?_⟩
    · simp
    · simp [s₁,s,initEnv, tableKernel]
  | cons d xs =>
    have hc₁ : (Cond.lt (.lit 0) (.var "cd_len")).evalB B s₁ = some true := by simpa using hc
    let s₂ := {s₁.setVar "cd_count" d with inp := xs}
    have hd := hWord d (by simp)
    have hrd : Run B (.read "cd_count") s₁ s₂ 1 := Run.read rfl
    have hll : s₂.vars "cd_len" = xs.length+1 := by simp [s₂,s₁]
    have hdd : s₂.vars "cd_count" = d := by simp [s₂]
    have hel : (Expr.var "cd_len").evalB B s₂ = some (xs.length + 1) := by
      rw [← hll]; exact evalB_var (hll ▸ hLen)
    have hed : (Expr.var "cd_count").evalB B s₂ = some d := by
      rw [← hdd]; exact evalB_var (hdd ▸ hd)
    have hrem : (Expr.sub (.var "cd_len") (.lit 1)).evalB B s₂ = some xs.length := by
      have hlt : (xs.length+1) - 1 < B :=
        (Nat.sub_le _ _).trans_lt hLen
      simpa using evalB_bin (op := .sub) hel (evalB_lit h1) hlt
    have hcap : (Expr.mul (.lit q) (.var "cd_count")).evalB B s₂ = some (q*d) :=
      evalB_bin (evalB_lit hq) hed (hMul d (by simp))
    have hg := evalB_condLt hrem hcap
    by_cases good : q*d ≤ xs.length
    · have g : (shapeTest q).evalB B s₂ = some false := by
        simpa [shapeTest, Nat.not_lt.mpr good] using hg
      let e := enum.symm 1
      let s₃ := s₂.setArr "cd_old" e.val 1
      have hs : (s₂.arrs "cd_old").length = q := by simp [s₂,s₁,s,initEnv]
      have hstore : Run B (.store "cd_old" (.lit e.val) (.lit 1)) s₂ s₃ 3 :=
        Run.store (evalB_lit (e.isLt.trans hq)) (evalB_lit h1) (by rw [hs]; exact e.isLt)
      have hab : ∀ b, (s₃.arrs b).length = q := by
        intro b
        by_cases h : b = "cd_old" <;> simp [s₃,s₂,s₁,s,initEnv,Env.setArr,h]
      have hold (i : Fin q) : (s₃.arrs "cd_old").getD i.val 0 = initial e i := by
        by_cases h : i = e
        · subst i
          simp only [initial, if_pos rfl, s₃, Env.setArr]
          exact getD_set_same _ _ _ (by rw [hs]; exact e.isLt)
        · have hne : e.val ≠ i.val := fun hn => h (Fin.ext hn).symm
          simp only [initial,h,if_false,s₃,Env.setArr,if_true]
          rw [getD_set_other _ _ _ _ (by rw [hs]; exact i.isLt) hne]
          simp [s₂,s₁,s,initEnv]
      let rows := collectRows q d xs
      have hrows : rows.length = d := collectRows_length q d xs
      have hw₃ : s₃.inp = rowWords rows ++ xs.drop (q*d) := by
        rw [show rowWords rows = xs.take (q*d) from collectRows_words q d xs good,
          List.take_append_drop]
        rfl
      have hq₁ : 1 ≤ q := by have := e.isLt; omega
      have hdle : d ≤ (d :: xs).length :=
        (show d ≤ q*d by simpa using Nat.mul_le_mul_right d hq₁).trans (good.trans (by simp))
      have hpow : q^(0 + rows.length) < B := by
        rw [Nat.zero_add, hrows]
        exact (Nat.pow_le_pow_right hq₁ hdle).trans_lt hPow
      obtain ⟨t,ht,hvals,hlen,hin,hout⟩ := countLoop_run enum rows s₃ (initial e) 0 _
        (by simpa only [hrows, s₃, vars_setArr] using hdd) hw₃ (by rw [hab]) (by rw [hab]) (by rw [hab])
        h1 hq.le hq₁ (by rw [hrows]; exact hd) hold (fun i => by by_cases h : i=e <;> simp [initial,h])
        hpow (by
          intro a ha
          have hm : a ∈ xs.take (q*d) := (collectRows_words q d xs good) ▸ ha
          exact hWord a (List.mem_cons_of_mem _ (List.mem_of_mem_take hm)))
      let val := finishRows enum (initial e) rows e
      have hv : val < B := by
        have hgrow : ∀ (ys : List (Fin q → ℕ)) (v : Fin q → ℕ) (m : ℕ),
            (∀ k, v k ≤ q^m) → ∀ k, finishRows enum v ys k ≤ q^(m+ys.length) := by
          intro ys
          induction ys with
          | nil => intro v m H k; simpa [finishRows] using H k
          | cons a ys ih =>
            intro v m H k
            have he : ∀ j, rowValue enum a v j ≤ q^(m+1) := fun j => by
              rw [pow_succ']; exact rowValue_le enum a v _ H j
            have hh := ih (rowValue enum a v) (m+1) he k
            rw [show m+1+ys.length = m+(a::ys).length by simp; omega] at hh
            exact hh
        exact (hgrow rows (initial e) 0 (fun i => by by_cases h : i=e <;> simp [initial,h]) e).trans_lt hpow
      have hw : (Expr.get "cd_old" (.lit e.val)).evalB B t = some val :=
        readBank t "cd_old" e.val val (by rw [hlen, hab]; exact e.isLt) (e.isLt.trans hq) (hvals e) hv
      have houtRun := Run.write hw
      refine ⟨{t with out := t.out ++ [val]}, ?_, ?_⟩
      · have hh : Run B (tableProg enum) s {t with out := t.out ++ [val]} _ :=
          hr.seq (Run.ite_true hc₁ (hrd.seq (Run.ite_false g (hstore.seq (ht.seq houtRun)))))
        apply hh.mono
        simp only [shapeTest, size_condLt, size_sub, size_mul, size_get, size_lit,
          size_var, loopCost, hrows]
        have := Nat.mul_le_mul_left (rowCost enum + 8) hdle
        omega
      · change t.out ++ [val] = _
        rw [hout]
        simp [s₃,s₂,s₁,s,initEnv, tableKernel, good, val,rows,e]
    · have g : (shapeTest q).evalB B s₂ = some true := by
        simpa [shapeTest, Nat.lt_of_not_ge good] using hg
      have hzero := Run.write (σ := s₂) (evalB_lit (by omega : 0 < B))
      refine ⟨_, (hr.seq (Run.ite_true hc₁ (hrd.seq (Run.ite_true g hzero)))).mono ?_, ?_⟩
      · simp [shapeTest] <;> omega
      · simp [s₂,s₁,s,initEnv,tableKernel,good]

theorem tableKernel_ramPolytime (enum : Fin q ≃ G) : RamPolytime (tableKernel enum) := by
  let P : Polynomial ℕ := Polynomial.C (q+2) * Polynomial.X + Polynomial.C (q+3)
  let T : Polynomial ℕ := Polynomial.C (rowCost enum + 8) * Polynomial.X + Polynomial.C 40
  apply ramPolytime_of_bounded_imp tableLayout (tableProg enum) (tableKernel enum) P T (tableProg_ok enum)
  intro xs
  let s := bitSize xs
  let E := P.eval s + s + 1
  let B := 2^E
  have he : E = (q+2)*s + (q+3) + s + 1 := by simp [E,P]
  have hs := Lax51Proofs.Encoding.length_le_bitSize xs
  have h1 : 1 < B := Nat.one_lt_two_pow (by rw [he]; omega)
  have hq : q < B := (Nat.lt_two_pow_self (n := q)).trans_le
    (Nat.pow_le_pow_right (by decide) (by rw [he]; omega))
  have hLen : xs.length < B := (Nat.lt_two_pow_self (n := xs.length)).trans_le
    (Nat.pow_le_pow_right (by decide) (by rw [he]; omega))
  have ha (a : ℕ) (h : a ∈ xs) : a < 2^(s+1) :=
    Lax51Proofs.Encoding.mem_lt_two_pow_bitSize_add_one h
  have hw (a : ℕ) (h : a ∈ xs) : a < B :=
    (ha a h).trans_le (Nat.pow_le_pow_right (by decide) (by rw [he]; omega))
  have hm (a : ℕ) (h : a ∈ xs) : q*a < B := by
    calc
      _ ≤ 2^q*a := Nat.mul_le_mul_right _ Nat.lt_two_pow_self.le
      _ < 2^q * 2^(s+1) := Nat.mul_lt_mul_of_pos_left (ha _ h) (by positivity)
      _ = 2^(q+(s+1)) := (pow_add _ _ _).symm
      _ ≤ B := Nat.pow_le_pow_right (by decide) (by rw [he]; omega)
  have hp : q^xs.length < B := by
    calc
      _ ≤ (2^q)^xs.length := Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
      _ = 2^(q*xs.length) := (pow_mul _ _ _).symm
      _ < B := Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) (by
        rw [he]
        have h := Nat.mul_le_mul_left q (show xs.length ≤ s from hs)
        rw [Nat.add_mul] 
        omega)
  obtain ⟨t,ht,ho⟩ := tableProg_run enum xs h1 hq hLen hw hm hp
  refine ⟨fun _ => q, t, ht.mono ?_, ho⟩
  simpa [T,s] using Nat.add_le_add_right (Nat.mul_le_mul_left (rowCost enum+8) hs) 40

theorem tableKernel_turingPolytime (enum : Fin q ≃ G) : TuringPolytime (tableKernel enum) :=
  Lax51Proofs.RamToTM.ramPolytime_to_turingPolytime (tableKernel_ramPolytime enum)

#print axioms tableKernel_turingPolytime
end EvenTI.P12CountPost
