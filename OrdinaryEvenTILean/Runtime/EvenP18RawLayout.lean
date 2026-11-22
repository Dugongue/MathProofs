import EvenP17ReciprocalTrial
import EvenP12ComparePrepKernelLayout

set_option autoImplicit false
set_option maxRecDepth 20000
namespace EvenTI.P18Execution

open EvenTI.P12Compare EvenTI.P12ComparePrep EvenTI.P15Execution EvenTI.P16Execution
open EvenTI.P15Trial EvenTI.P16Trial EvenTI.P17Trial EvenTI.P17Execution
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18ClaudeIMPSlots20261001 (NoVar)
open Mathproof.P15RecogIMPDot20261007 (qN dT dU dZ)
open Mathproof.Problem18P34AssemblyMatrixGatherSetup20261003 (commands install commands_run installed_scalar)

def reciprocalRawOffsets (m : ℕ) : ReciprocalOffsets :=
  ⟨4,4+m*m,7+6*(m*m),7+7*(m*m),7+5*(m*m),2,3,0,1⟩

def reciprocalRawSlots (m : ℕ) : ℕ := 7+8*(m*m)

theorem reciprocalRawOffsets_fit {m n : ℕ} (h : n*n ≤ m) :
    let L := reciprocalRawOffsets m
    L.src+m*m ≤ L.inv ∧ L.inv+4*(m*m)+3 ≤ reciprocalRawSlots m ∧
      L.inv+m*m ≤ L.out ∧ L.out+n*n ≤ L.cross ∧
      L.cross+(n*n)*(n*n) ≤ L.square ∧
      L.square+(n*n)*(n*n) ≤ reciprocalRawSlots m := by
  dsimp [reciprocalRawOffsets,reciprocalRawSlots]
  have h₁ : n*n ≤ m*m := h.trans (Nat.le_mul_self m)
  have h₂ := Nat.mul_le_mul h h
  omega

inductive RawBindWord where
  | address (a : Address)
  | zero
  | width
  | order
  | inner
  | widthSquare

def RawBindWord.read : RawBindWord → Expr
  | .address a => a.expr
  | .zero => .lit 0
  | .width => .var shapePower.base
  | .order => .var rawOrder
  | .inner => .div (.var shapePower.out) (.var shapePower.base)
  | .widthSquare => .mul (.var shapePower.base) (.var shapePower.base)

def RawBindWord.value (m n d : ℕ) : RawBindWord → ℕ
  | .address a => a.value m
  | .zero => 0
  | .width => n
  | .order => d
  | .inner => m/n
  | .widthSquare => n*n

theorem RawBindWord.eval (a : RawBindWord) {m n d B : ℕ} {s : Env}
    (hm : s.vars shapePower.out=m) (hn : s.vars shapePower.base=n) (hd : s.vars rawOrder=d)
    (hPos : 0 < m) (hmB : m < B) (hnB : n < B) (hFits : a.value m n d < B) :
    a.read.evalB B s = some (a.value m n d) := by
  cases a with
  | address a => exact a.eval hm hPos hFits
  | zero => exact evalB_lit hFits
  | width => exact evalB_var_iff.mpr ⟨hn.symm,hn ▸ hFits⟩
  | order => exact evalB_var_iff.mpr ⟨hd.symm,hd ▸ hFits⟩
  | inner =>
    exact evalB_bin (evalB_var_iff.mpr ⟨hm.symm,hm ▸ hmB⟩)
      (evalB_var_iff.mpr ⟨hn.symm,hn ▸ hnB⟩) hFits
  | widthSquare =>
    have he := evalB_var_iff.mpr ⟨hn.symm,hn ▸ hnB⟩
    exact evalB_bin he he hFits

theorem RawBindWord.noVar (a : RawBindWord) {r : String}
    (hm : r≠shapePower.out) (hn : r≠shapePower.base) (hd : r≠rawOrder) :
    NoVar r a.read := by
  cases a with
  | address a => exact a.noVar hm
  | zero => trivial
  | width => simp [RawBindWord.read,NoVar,hn,Ne.symm hn]
  | order => simp [RawBindWord.read,NoVar,hd,Ne.symm hd]
  | inner => simp [RawBindWord.read,NoVar,hm,hn,Ne.symm hm,Ne.symm hn]
  | widthSquare => simp [RawBindWord.read,NoVar,hn,Ne.symm hn]

def layoutAddr (c k : ℕ) : Address := .add (.litSucc c) (.mul (.litSucc k) cutArea)

def reciprocalRawBindings (target : Bool) : List (String × RawBindWord) :=
  [(loadBase,.address (.litSucc 3)),(loadLength,.address cutArea),(inputBase,.address (inputOffset target)),
    (inverseSizeWord,.address .side),(inverseInputWord,.address (.litSucc 3)),
    (inverseOutputWord,.address (layoutAddr 3 0)),
    (crossN,.width),(crossA,.inner),(crossSource,.address (.litSucc 3)),
    (crossInverse,.address (layoutAddr 3 0)),(anchorSideWord,.width),
    (anchorCrossWord,.address (layoutAddr 6 5)),(anchorSquareWord,.address (layoutAddr 6 6)),
    (anchorTraceWord,.address (layoutAddr 6 4)),
    (anchorUnitWord,.address (.litSucc 0)),(dZ,.zero),
    (dT,.address (.litSucc 1)),(dU,.address (.litSucc 2)),
    (fieldVectorStart,.address (layoutAddr 6 4)),(fieldVectorLength,.widthSquare),
    (emitAnchorWidth,.width),(reciprocalCountWord,.order)]

def reciprocalRawSetup (target : Bool) : Com :=
  commands ((reciprocalRawBindings target).map fun p => (p.1,p.2.read))

def reciprocalRawSetupCost (target : Bool) : ℕ :=
  ((reciprocalRawBindings target).map fun p => p.2.read.size+1).sum+1

def reciprocalRawRegisters (target : Bool) (m n d : ℕ) : List (String × Nat) :=
  (reciprocalRawBindings target).map fun p => (p.1,p.2.value m n d)

private theorem zip_values (xs : List (String × RawBindWord)) (m n d : ℕ) :
    List.zip (xs.map Prod.fst) (xs.map fun p => p.2.value m n d) =
      xs.map fun p => (p.1,p.2.value m n d) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem reciprocalRawSetup_run (target : Bool) {m n d B : ℕ} {s : Env}
    (hm : s.vars shapePower.out=m) (hn : s.vars shapePower.base=n) (hd : s.vars rawOrder=d)
    (hPos : 0 < m) (hmB : m < B) (hnB : n < B)
    (hFits : ∀ p ∈ reciprocalRawBindings target, p.2.value m n d < B) :
    Run B (reciprocalRawSetup target) s (install (reciprocalRawRegisters target m n d) s)
      (reciprocalRawSetupCost target) := by
  let xs := reciprocalRawBindings target
  let es := xs.map fun p => (p.1,p.2.read)
  let vs := xs.map fun p => p.2.value m n d
  have aux (ys : List (String × RawBindWord)) (hf : ∀ p ∈ ys, p.2.value m n d < B) :
      List.Forall₂ (fun (p : String × Expr) v => p.2.evalB B s = some v)
        (ys.map fun p => (p.1,p.2.read)) (ys.map fun p => p.2.value m n d) := by
    induction ys with
    | nil => exact .nil
    | cons a as ih =>
      exact .cons (a.2.eval hm hn hd hPos hmB hnB (hf a List.mem_cons_self))
        (ih fun p hp => hf p (List.mem_cons_of_mem a hp))
  have hNames : ∀ x ∈ xs.map Prod.fst, x≠shapePower.out ∧ x≠shapePower.base ∧ x≠rawOrder := by
    cases target <;> decide
  have hNoVar : ∀ p ∈ es, ∀ q ∈ es, NoVar p.1 q.2 := by
    intro p hp q hq
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hp
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp hq
    have h := hNames v.1 (List.mem_map.mpr ⟨v,hv,rfl⟩)
    exact u.2.noVar h.1 h.2.1 h.2.2
  have r := commands_run es vs s (by simp [es,vs]) (aux xs hFits) hNoVar
  have he : List.zip (es.map Prod.fst) vs = reciprocalRawRegisters target m n d := by
    simpa [es,vs,xs,reciprocalRawRegisters,List.map_map,Function.comp_def] using zip_values xs m n d
  rw [he] at r
  simpa [reciprocalRawSetup,reciprocalRawSetupCost,es,xs,List.map_map,Function.comp_def] using r

#print axioms reciprocalRawOffsets_fit
#print axioms reciprocalRawSetup_run
private theorem installed_member (xs : List (String × ℕ)) (s : Env) {r : String} {v : ℕ}
    (hn : (xs.map Prod.fst).Nodup) (h : (r,v) ∈ xs) :
    (install xs s).vars r=v := by
  induction xs generalizing s with
  | nil => simp at h
  | cons x xs ih =>
    obtain ⟨hnx,hnxs⟩ := List.nodup_cons.mp hn
    rcases List.mem_cons.mp h with he|hh
    · subst x
      rw [install,installed_scalar _ _ _ ?_]
      · simp
      · intro p hp he
        exact hnx (List.mem_map.mpr ⟨p,hp,he.symm⟩)
    · exact ih _ hnxs hh

theorem reciprocalRawRegisters_at (target : Bool) (m n d : ℕ) (s : Env)
    {r : String} {p : RawBindWord} (hp : (r,p) ∈ reciprocalRawBindings target) :
    (install (reciprocalRawRegisters target m n d) s).vars r=p.value m n d := by
  apply installed_member
  · simp only [reciprocalRawRegisters,List.map_map,Function.comp_def]
    cases target <;> decide
  · exact List.mem_map.mpr ⟨(r,p),hp,rfl⟩

/-- The fixed address bank and its caller registers fit whenever their decoded
shape and the original word list fit. -/
theorem reciprocalRawBindings_fit (target : Bool) {m n d B : ℕ}
    (hmB : reciprocalRawSlots m < B) (hd : d < B) (hn : n*n ≤ m) (hnB : n < B) :
    ∀ p ∈ reciprocalRawBindings target, p.2.value m n d < B := by
  intro p hp
  have hm : m ≤ m*m := Nat.le_mul_self m
  have hDiv : m/n ≤ m := Nat.div_le_self ..
  have hSq : n*n ≤ m*m := hn.trans hm
  change 7+8*(m*m) < B at hmB
  cases target <;>
    simp only [reciprocalRawBindings,List.mem_cons,List.not_mem_nil,or_false] at hp <;>
    rcases hp with hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp <;>
    subst p <;> simp only [RawBindWord.value,inputOffset,layoutAddr,cutArea,Address.value,
      Bool.false_eq_true,if_false,if_true,Nat.reduceAdd] <;> omega

#print axioms reciprocalRawRegisters_at
#print axioms reciprocalRawBindings_fit
end EvenTI.P18Execution


