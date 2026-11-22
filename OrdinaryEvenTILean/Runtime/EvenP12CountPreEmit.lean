
import EvenP12CountPreSegments


namespace EvenTI.P12CountPre
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open EvenTI.Action EvenTI.Contract EvenTI.P10Oracle

set_option autoImplicit false

def digitLookup (rows : List (Nat × Nat)) (fallback : Nat) (v : Nat) : Nat :=
  match rows with
  | [] => fallback
  | (a,b) :: r => if v = a then b else digitLookup r fallback v

def digitWrite : List (Nat × Nat) → Nat → Com
  | [], b => .write (.lit b)
  | (a,b) :: r, c => .ite (.eq (.var "word") (.lit a)) (.write (.lit b)) (digitWrite r c)

theorem digitWrite_run (rows : List (Nat × Nat)) (d : Nat) {B : Nat} {σ : Env}
    (hd : d < B) (hword : σ.vars "word" < B)
    (hv : ∀ p ∈ rows, p.1 < B ∧ p.2 < B) :
    Run B (digitWrite rows d) σ {σ with out := σ.out ++ [digitLookup rows d (σ.vars "word")]}
      (4 * rows.length + 2) := by
  induction rows with
  | nil => exact Run.write (evalB_lit hd)
  | cons row rows ih =>
    rcases row with ⟨a,b⟩
    have ha := hv (a,b) (List.mem_cons_self)
    have ev := evalB_condEq (B := B) (σ := σ) (evalB_var hword) (evalB_lit ha.1)
    by_cases h : σ.vars "word" = a
    · have he : (Cond.eq (.var "word") (.lit a)).evalB B σ = some true := by simpa [h] using ev
      simp only [digitLookup, digitWrite, h, if_true, List.length_cons]
      exact (Run.ite_true (d := digitWrite rows d) he (Run.write (evalB_lit ha.2))).mono (by simp <;> omega)
    · have he : (Cond.eq (.var "word") (.lit a)).evalB B σ = some false := by simpa [h] using ev
      simp only [digitLookup, digitWrite, h, if_false, List.length_cons]
      exact (Run.ite_false (c := .write (.lit b)) he
        (ih (fun p hp => hv p (List.mem_cons_of_mem (a,b) hp)))).mono (by simp <;> omega)

def bankBody (writeWord : Com) : Com :=
  .seq (.assign "word" (.get "data" (.var "cursor"))) (.seq writeWord advanceCursor)

def bankGuard : Cond := .lt (.var "cursor") (.var "stop")

def bankLoop (writeWord : Com) : Com := .while bankGuard (bankBody writeWord)

private theorem slice_drop_cons {z : List Nat} {j stop : Nat}
    (hj : j < stop) (hs : stop ≤ z.length) :
    (z.take stop).drop j = z[j]'(hj.trans_le hs) :: (z.take stop).drop (j+1) := by
  have h : j < (z.take stop).length := by rw [List.length_take, min_eq_left hs]; exact hj
  rw [List.drop_eq_getElem_cons h, List.getElem_take]

/-- Replay a materialized interval through a checked one-word operation. The
program and bounds are uniform in the interval address and length. -/
theorem bankLoop_run (z : List Nat) {start stop B c : Nat} {σ : Env} (writeWord : Com)
    (f : Nat → Nat) (hwrite : ∀ t : Env, t.vars "word" < B →
      Run B writeWord t {t with out := t.out ++ [f (t.vars "word")]} c)
    (hstart : start ≤ stop) (hstop : stop ≤ z.length)
    (hc : σ.vars "cursor" = start) (hs : σ.vars "stop" = stop)
    (hBank : σ.arrs "data" = sentinelWords z) (hLen : z.length < B) (hB : 1 < B)
    (hWords : ∀ v ∈ z, v < B) :
    ∃ τ, Run B (bankLoop writeWord) σ τ ((c+11)*(stop-start)+4) ∧
      (∀ v, v ≠ "cursor" → v ≠ "word" → τ.vars v = σ.vars v) ∧
      τ.arrs = σ.arrs ∧ τ.inp = σ.inp ∧ τ.vars "cursor" = stop ∧
      τ.out = σ.out ++ ((z.take stop).drop start).map f := by
  let I (t : Env) : Prop :=
    t.vars "cursor" ≤ stop ∧ (∀ v, v ≠ "cursor" → v ≠ "word" → t.vars v = σ.vars v) ∧
      t.arrs = σ.arrs ∧ t.inp = σ.inp ∧
      t.out ++ ((z.take stop).drop (t.vars "cursor")).map f =
        σ.out ++ ((z.take stop).drop start).map f
  let V (t : Env) : Nat := stop - t.vars "cursor"
  have g (t : Env) (ht : I t) :
      bankGuard.evalB B t = some (decide (t.vars "cursor" < stop)) := by
    have horig := ht.2.1 "stop" (by decide) (by decide)
    have g' := evalB_condLt (σ := t) (B := B) (e := .var "cursor") (f := .var "stop")
      (evalB_var (by have := ht.1; omega)) (evalB_var (by rw [horig,hs]; omega))
    simpa only [bankGuard,horig,hs] using g'
  have step (t : Env) (ht : I t) (hcond : bankGuard.evalB B t = some true) :
      ∃ t', Run B (bankBody writeWord) t t' (c+7) ∧ I t' ∧ V t' < V t := by
    rw [g t ht] at hcond
    have hcur : t.vars "cursor" < stop := by simpa using hcond
    let j := t.vars "cursor"
    have hj : j < z.length := hcur.trans_le hstop
    let a := z[j]
    have ha : a < B := hWords a (List.getElem_mem hj)
    have e : (Expr.get "data" (.var "cursor")).evalB B t = some a := by
      refine evalB_get (evalB_var (by omega)) ?_ ha
      rw [ht.2.2.1,hBank]
      unfold sentinelWords
      rw [List.getElem?_append_left hj, List.getElem?_eq_getElem hj]
    let t₁ := t.setVar "word" a
    let t₂ := {t₁ with out := t₁.out ++ [f a]}
    let t₃ := t₂.setVar "cursor" (j+1)
    have r₁ : Run B (.assign "word" (.get "data" (.var "cursor"))) t t₁ 3 := Run.assign e
    have r₂ : Run B writeWord t₁ t₂ c := by simpa [t₁,t₂] using hwrite t₁ (by simpa [t₁] using ha)
    have ei : (Expr.add (.var "cursor") (.lit 1)).evalB B t₂ = some (j+1) := by
      have ee := evalB_bin (B := B) (σ := t₂) (op := .add)
        (evalB_var (x := "cursor") (by simp [t₂,t₁]; omega)) (evalB_lit (n := 1) hB)
        (by simp [t₂,t₁]; omega)
      simpa [t₂,t₁,j] using ee
    have r₃ : Run B advanceCursor t₂ t₃ 4 := Run.assign ei
    refine ⟨t₃,(r₁.seq (r₂.seq r₃)).mono (by omega),⟨?_,?_,?_,?_,?_⟩,?_⟩
    · simp [t₃,j]; omega
    · intro v hvc hvw
      simp [t₃,t₂,t₁,hvc,hvw,ht.2.1 _ hvc hvw]
    · simpa [t₃,t₂,t₁] using ht.2.2.1
    · simpa [t₃,t₂,t₁] using ht.2.2.2.1
    · have hh := ht.2.2.2.2
      change t.out ++ ((z.take stop).drop j).map f = _ at hh
      rw [slice_drop_cons hcur hstop] at hh
      simpa [t₃,t₂,t₁,List.append_assoc,a] using hh
    · simp [V,t₃,j]; omega
  obtain ⟨τ,hr,ht,hf⟩ := Run.while_count I V (c+7) (fun t h => ⟨_,g t h⟩) step
    ⟨by rw [hc]; exact hstart, fun _ _ _ => rfl, rfl, rfl, by rw [hc]⟩
  rw [g τ ht] at hf
  have hend : τ.vars "cursor" = stop := by
    have h₁ := ht.1
    have : ¬ τ.vars "cursor" < stop := by simpa using hf
    omega
  refine ⟨τ,hr.mono ?_,ht.2.1,ht.2.2.1,ht.2.2.2.1,hend,?_⟩
  · simp [bankGuard,V,hc,show 4 + (c + 7) = c + 11 by omega]
  · have hnil : (z.take stop).drop (τ.vars "cursor") = [] := by rw [hend]; simp
    simpa [hnil] using ht.2.2.2.2

variable {K : Type} [Field K] [Fintype K]

/-- This is a constant table for the fixed coefficient field. Input matrix
digits on the oracle tape are shifted by one. -/
def scalarDigit (F : FieldEncoding K) (u : Kˣ) (v : Nat) : Nat :=
  (F ((u : K) * decodeDigit F (v-1))).val + 1

def scalarRows (F : FieldEncoding K) (u : Kˣ) : List (Nat × Nat) :=
  (List.range (Fintype.card K + 1)).map fun v => (v,scalarDigit F u v)

theorem scalarRows_lookup (F : FieldEncoding K) (u : Kˣ) (v : Nat) :
    digitLookup (scalarRows F u) ((F 0).val + 1) v = scalarDigit F u v := by
  have hh (xs : List Nat) (h : v ∈ xs) :
      digitLookup (xs.map (fun x => (x,scalarDigit F u x))) ((F 0).val + 1) v = scalarDigit F u v := by
    induction xs with
    | nil => simp at h
    | cons x xs ih =>
      by_cases hx : v = x
      · simp [digitLookup,hx]
      · have hmem := (List.mem_cons.mp h).resolve_left hx
        simp only [List.map_cons,digitLookup,if_neg hx]
        exact ih hmem
  by_cases h : v < Fintype.card K + 1
  · exact hh _ (List.mem_range.mpr h)
  · have hf : scalarDigit F u v = (F 0).val + 1 := by
      have huv : ¬ v-1 < Fintype.card K := by omega
      simp [scalarDigit,decodeDigit,huv]
    rw [hf]
    have hn : v ∉ List.range (Fintype.card K + 1) := by simpa using h
    unfold scalarRows
    generalize List.range (Fintype.card K + 1) = xs at hn ⊢
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      have hx : v ≠ x := fun e => hn (e ▸ List.mem_cons_self)
      have hxs : v ∉ xs := fun hm => hn (List.mem_cons_of_mem x hm)
      simp only [List.map_cons,digitLookup,if_neg hx]
      exact ih hxs

theorem scalarWord_run (F : FieldEncoding K) (u : Kˣ) {B : Nat} {t : Env}
    (hB : Fintype.card K + 1 < B) (hword : t.vars "word" < B) :
    Run B (digitWrite (scalarRows F u) ((F 0).val+1)) t
      {t with out := t.out ++ [scalarDigit F u (t.vars "word")]}
      (4 * (Fintype.card K + 1) + 2) := by
  have hrows : ∀ p ∈ scalarRows F u, p.1 < B ∧ p.2 < B := by
    intro p hp
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hp
    have hvl := List.mem_range.mp hv
    have he := (F ((u : K) * decodeDigit F (v-1))).isLt
    unfold scalarDigit
    omega
  have h0 := (F 0).isLt
  have rr := digitWrite_run (scalarRows F u) ((F 0).val+1) (by omega) hword hrows
  rw [scalarRows_lookup F u] at rr
  simpa only [scalarRows,List.length_map,List.length_range] using rr

/-- The real matrix-digit serializer from a committed word bank. -/
theorem scalarBank_run (F : FieldEncoding K) (u : Kˣ)
    (z : List Nat) {start stop B : Nat} {σ : Env}
    (hstart : start ≤ stop) (hstop : stop ≤ z.length)
    (hc : σ.vars "cursor" = start) (hs : σ.vars "stop" = stop)
    (hBank : σ.arrs "data" = sentinelWords z) (hLen : z.length < B)
    (hB : Fintype.card K + 1 < B) (hWords : ∀ v ∈ z, v < B) :
    ∃ τ, Run B (bankLoop (digitWrite (scalarRows F u) ((F 0).val+1))) σ τ
      ((4 * (Fintype.card K + 1) + 13)*(stop-start)+4) ∧
      (∀ v, v ≠ "cursor" → v ≠ "word" → τ.vars v = σ.vars v) ∧
      τ.arrs = σ.arrs ∧ τ.inp = σ.inp ∧ τ.vars "cursor" = stop ∧
      τ.out = σ.out ++ ((z.take stop).drop start).map (scalarDigit F u) := by
  have hnon : 0 < Fintype.card K := Fintype.card_pos
  have h1 : 1 < B := by omega
  have h := bankLoop_run z (digitWrite (scalarRows F u) ((F 0).val + 1)) (scalarDigit F u)
    (fun t ht => scalarWord_run F u hB ht) hstart hstop hc hs hBank hLen h1 hWords
  simpa [show 4 * (Fintype.card K + 1) + 2 + 11 = 4 * (Fintype.card K + 1) + 13 by omega] using h

#print axioms bankLoop_run
#print axioms scalarBank_run
end EvenTI.P12CountPre

