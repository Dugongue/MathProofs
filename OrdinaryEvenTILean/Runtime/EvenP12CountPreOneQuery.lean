import EvenP12CountPreEmit

namespace EvenTI.P12CountPre

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open EvenTI.Action EvenTI.Contract EvenTI.P10Oracle

set_option autoImplicit false

variable {K : Type} [Field K] [Fintype K]

def directWord : Com := .write (.var "word")

theorem directWord_run {B : Nat} {t : Env} (ht : t.vars "word" < B) :
    Run B directWord t {t with out := t.out ++ [t.vars "word"]} 2 := by
  exact Run.write (evalB_var ht)

def headerProgram : Com :=
  .seq (.write (.var "paramEnd"))
    (.seq (.assign "cursor" (.lit 1))
      (.seq (.assign "stop" (.var "paramEnd"))
        (.seq (bankLoop directWord)
          (.seq (.write (.var "modeWord")) (.write (.var "dimWord"))))))

def matrixProgram (F : FieldEncoding K) (u : Kˣ) : Com :=
  .seq (.assign "cursor" (.var "matrixStart"))
    (.seq (.assign "stop" (.var "matrixEnd"))
      (.seq (bankLoop (digitWrite (scalarRows F u) ((F 0).val + 1))) (.write (.lit 0))))

def oneQueryProgram (F : FieldEncoding K) (u : Kˣ) : Com :=
  .seq headerProgram (matrixProgram F u)

theorem headerProgram_run (z : List Nat) {B e m n : Nat} {σ : Env}
    (he : σ.vars "paramEnd" = e) (hm : σ.vars "modeWord" = m) (hn : σ.vars "dimWord" = n)
    (he1 : 1 ≤ e) (hez : e ≤ z.length) (hBank : σ.arrs "data" = sentinelWords z)
    (hLen : z.length < B) (hB : 1 < B) (hMb : m < B) (hNb : n < B)
    (hWords : ∀ v ∈ z, v < B) :
    ∃ τ, Run B headerProgram σ τ (13 * e + 16) ∧
      (∀ v, v ≠ "cursor" → v ≠ "stop" → v ≠ "word" → τ.vars v = σ.vars v) ∧
      τ.arrs = σ.arrs ∧ τ.inp = σ.inp ∧
      τ.out = σ.out ++ e :: ((z.take e).drop 1) ++ [m,n] := by
  let t₁ := {σ with out := σ.out ++ [e]}
  let t₂ := t₁.setVar "cursor" 1
  let t₃ := t₂.setVar "stop" e
  have r₁ : Run B (.write (.var "paramEnd")) σ t₁ 2 := Run.write
    (by rw [evalB_var_iff,he]; exact ⟨rfl,hez.trans_lt hLen⟩)
  have r₂ : Run B (.assign "cursor" (.lit 1)) t₁ t₂ 2 := Run.assign (evalB_lit hB)
  have r₃ : Run B (.assign "stop" (.var "paramEnd")) t₂ t₃ 2 := Run.assign
    (by rw [evalB_var_iff]; simpa [t₂,t₁,he] using hez.trans_lt hLen)
  obtain ⟨t₄,r₄,hv,ha,hi,hc,ho⟩ := bankLoop_run z (σ := t₃) directWord id
    (fun _ ht => directWord_run ht) he1 hez (by simp [t₃,t₂]) (by simp [t₃])
    (by simpa [t₃,t₂,t₁] using hBank) hLen hB hWords
  have hm' : t₄.vars "modeWord" = m := by rw [hv "modeWord" (by decide) (by decide)]; simpa [t₃,t₂,t₁] using hm
  have hn' : t₄.vars "dimWord" = n := by rw [hv "dimWord" (by decide) (by decide)]; simpa [t₃,t₂,t₁] using hn
  let t₅ := {t₄ with out := t₄.out ++ [m]}
  let t₆ := {t₅ with out := t₅.out ++ [n]}
  have r₅ : Run B (.write (.var "modeWord")) t₄ t₅ 2 := Run.write
    (by rw [evalB_var_iff,hm']; exact ⟨rfl,hMb⟩)
  have r₆ : Run B (.write (.var "dimWord")) t₅ t₆ 2 := Run.write
    (by rw [evalB_var_iff]; simpa [t₅,hn'] using hNb)
  have hr : Run B headerProgram σ t₆ (13*e+16) :=
    (r₁.seq (r₂.seq (r₃.seq (r₄.seq (r₅.seq r₆))))).mono (by omega)
  refine ⟨t₆,hr,?_,?_,?_,?_⟩
  · intro v hvc hvs hvw
    simp [t₆,t₅,hv v hvc hvw,t₃,t₂,t₁,hvc,hvs]
  · simpa [t₆,t₅,t₃,t₂,t₁] using ha
  · simpa [t₆,t₅,t₃,t₂,t₁] using hi
  · simp [t₆,t₅,ho,t₃,t₂,t₁,List.append_assoc]

theorem matrixProgram_run (F : FieldEncoding K) (u : Kˣ) (z : List Nat)
    {B a b : Nat} {σ : Env}
    (ha : σ.vars "matrixStart" = a) (hb : σ.vars "matrixEnd" = b) (hab : a ≤ b) (hbz : b ≤ z.length)
    (hBank : σ.arrs "data" = sentinelWords z) (hLen : z.length < B)
    (hB : Fintype.card K + 1 < B) (hWords : ∀ v ∈ z, v < B) :
    ∃ τ, Run B (matrixProgram F u) σ τ ((4 * (Fintype.card K + 1) + 13)*(b-a)+10) ∧
      (∀ v, v ≠ "cursor" → v ≠ "stop" → v ≠ "word" → τ.vars v = σ.vars v) ∧
      τ.arrs = σ.arrs ∧ τ.inp = σ.inp ∧
      τ.out = σ.out ++ ((z.take b).drop a).map (scalarDigit F u) ++ [0] := by
  let t₁ := σ.setVar "cursor" a
  let t₂ := t₁.setVar "stop" b
  have r₁ : Run B (.assign "cursor" (.var "matrixStart")) σ t₁ 2 := Run.assign
    (by rw [evalB_var_iff,ha]; exact ⟨rfl,hab.trans_lt (hbz.trans_lt hLen)⟩)
  have r₂ : Run B (.assign "stop" (.var "matrixEnd")) t₁ t₂ 2 := Run.assign
    (by rw [evalB_var_iff]; simpa [t₁,hb] using hbz.trans_lt hLen)
  obtain ⟨t₃,r₃,hv,harr,hin,hcur,hout⟩ := scalarBank_run F u z (σ := t₂) hab hbz
    (by simp [t₂,t₁]) (by simp [t₂]) (by simpa [t₂,t₁] using hBank) hLen hB hWords
  let t₄ := {t₃ with out := t₃.out ++ [0]}
  have r₄ : Run B (.write (.lit 0)) t₃ t₄ 2 := Run.write (evalB_lit (by omega))
  have hr : Run B (matrixProgram F u) σ t₄ ((4*(Fintype.card K+1)+13)*(b-a)+10) :=
    (r₁.seq (r₂.seq (r₃.seq r₄))).mono (by omega)
  refine ⟨t₄,hr,?_,?_,?_,?_⟩
  · intro v hvc hvs hvw
    simp [t₄,hv v hvc hvw,t₂,t₁,hvc,hvs]
  · simpa [t₄,t₂,t₁] using harr
  · simpa [t₄,t₂,t₁] using hin
  · simp [t₄,hout,t₂,t₁]

/-- Emit one precisely delimited query, reading its header and matrix from the
same verified bank. The fields other than the three scratch cells are preserved. -/
theorem oneQueryProgram_run (F : FieldEncoding K) (u : Kˣ) (z : List Nat)
    {B e m n a b : Nat} {σ : Env}
    (he : σ.vars "paramEnd" = e) (hm : σ.vars "modeWord" = m) (hn : σ.vars "dimWord" = n)
    (ha : σ.vars "matrixStart" = a) (hb : σ.vars "matrixEnd" = b)
    (he1 : 1 ≤ e) (hez : e ≤ z.length) (hab : a ≤ b) (hbz : b ≤ z.length)
    (hBank : σ.arrs "data" = sentinelWords z) (hLen : z.length < B)
    (hB : Fintype.card K + 1 < B) (hMb : m < B) (hNb : n < B)
    (hWords : ∀ v ∈ z, v < B) :
    ∃ τ, Run B (oneQueryProgram F u) σ τ
        (13 * e + (4 * (Fintype.card K + 1) + 13)*(b-a)+26) ∧
      (∀ v, v ≠ "cursor" → v ≠ "stop" → v ≠ "word" → τ.vars v = σ.vars v) ∧
      τ.arrs = σ.arrs ∧ τ.inp = σ.inp ∧
      τ.out = σ.out ++ [e] ++ ((z.take e).drop 1) ++ [m,n] ++
        ((z.take b).drop a).map (scalarDigit F u) ++ [0] := by
  have hcard : 0 < Fintype.card K := Fintype.card_pos
  obtain ⟨t,rt,hv,harr,hin,hout⟩ := headerProgram_run z he hm hn he1 hez hBank hLen
    (by omega) hMb hNb hWords
  have ha' := (hv "matrixStart" (by decide) (by decide) (by decide)).trans ha
  have hb' := (hv "matrixEnd" (by decide) (by decide) (by decide)).trans hb
  obtain ⟨τ,rr,hv',harr',hin',hout'⟩ :=
    matrixProgram_run F u z ha' hb' hab hbz ((congrFun harr "data").trans hBank) hLen hB hWords
  refine ⟨τ,(rt.seq rr).mono (by omega),?_,harr'.trans harr,hin'.trans hin,?_⟩
  · intro v hc hs hw
    exact (hv' v hc hs hw).trans (hv v hc hs hw)
  · simp [hout',hout,List.append_assoc]

#print axioms oneQueryProgram_run
end EvenTI.P12CountPre
