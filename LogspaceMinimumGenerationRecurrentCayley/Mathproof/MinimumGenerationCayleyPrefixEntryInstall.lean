import Mathproof.MinimumGenerationCayleyPrefixLeafEntry
import Mathproof.MinimumGenerationTapeInstall

namespace Mathproof.MinimumGeneration.CayleyPrefixLeaf

open SearchTransducer
open InputPosition (work)

set_option backward.isDefEq.respectTransparency false

def prefixBanks : Fin machine.workTapes ↪ Fin 18 :=
  ⟨Fin.castLE (by decide), fun _ _ h => Fin.ext (congrArg (fun i : Fin 18 => i.val) h)⟩

private def sourceBank (i : Fin 11) : Fin 18 :=
  if i = 1 then 12
  else if i = 4 then 13
  else if i.val < 6 then 11
  else if i = 7 then 15
  else if i = 9 then 16
  else if i = 10 then 17
  else 14

def copySource (i : Fin 18) : Option (Fin 18) :=
  if h : i.val < 11 then some (sourceBank ⟨i.val, h⟩) else none

def template (n x y identity cut : Nat) (i : Fin 18) : Int → Option Bool :=
  let w := TableIO.width n
  if i = 11 then work (encodeLabel (2*w) 0)
  else if i = 12 then work (encodeLabel (2*w) x)
  else if i = 13 then work (encodeLabel (2*w) n)
  else if i = 14 then work (encodeLabel w 0)
  else if i = 15 then work (encodeLabel w y)
  else if i = 16 then work (encodeLabel w identity)
  else if i = 17 then work (encodeLabel w cut)
  else fun _ => none

/-- The seven live templates and the blank boundary of the disposable banks. -/
def Templates (n x y identity cut : Nat) (cells : Fin 18 → Int → Option Bool) : Prop :=
  (∀ i : Fin 18, 11 ≤ i.val → cells i = template n x y identity cut i) ∧
    ∀ i : Fin 18, i.val < 11 → ∀ p : Int,
      p < 1 ∨ (2 * TableIO.width n : Nat) < p → cells i p = none

abbrev installMachine := TapeInstall.machine (11 : Fin 18) copySource

private theorem source_high (i : Fin 11) : 11 ≤ (sourceBank i).val := by
  fin_cases i <;> decide

private theorem template_eq (n x y identity cut : Nat) (i : Fin 11) :
    template n x y identity cut (sourceBank i) = entryRegisters n x y identity cut i := by
  fin_cases i <;> rfl

private theorem work_outside (bits : List Bool) {B : Nat} (hb : bits.length ≤ B)
    (p : Int) (hp : p < 1 ∨ (B : Int) < p) : work bits p = none := by
  rcases hp with h | h
  · simp [work, show p ≤ 0 by omega]
  · simp only [work, if_neg (show ¬ p ≤ 0 by omega)]
    exact List.getElem?_eq_none (by omega)

private theorem template_outside (n x y identity cut : Nat) (i : Fin 11) (p : Int)
    (hp : p < 1 ∨ (2 * TableIO.width n : Nat) < p) :
    entryRegisters n x y identity cut i p = none := by
  fin_cases i <;> exact work_outside _ (by simp <;> omega) p hp

/-- Install all eleven literal prefix-call registers from the seven physical
templates. The reusable registers are preserved and all heads rewind. -/
theorem executeInstall {n : Nat} (M : Mul (Fin n)) (x y identity cut : Nat)
    (cells : Fin 18 → Int → Option Bool) (prior : List Bool)
    (ready : Templates n x y identity cut cells) :
    let raw := @encodeCayley n M
    let w := TableIO.width n
    let rawHead : Int := ↑(n+1 : Nat)
    let start := TapeInstall.start (11 : Fin 18) copySource rawHead cells prior
    let finish := TapeInstall.stop (11 : Fin 18) copySource rawHead cells prior (2*w)
    installMachine.BoundedSegment raw (2*w+1) start finish (2*w+2+2*w+1) ∧
      installMachine.step raw finish = none ∧
      (∀ i : Fin machine.workTapes, finish.workCell (prefixBanks i) =
        entryRegisters n x y identity cut i) ∧
      ∀ j : Fin 18, 11 ≤ j.val → finish.workCell j = cells j := by
  let raw := @encodeCayley n M
  let w := TableIO.width n
  have input : n+1 ≤ raw.length := by
    change n+1 ≤ (@encodeCayley n M).length
    rw [@length_encodeCayley n M]
    omega
  have head : (-1 : Int) ≤ (↑(n+1 : Nat) : Int) ∧ (↑(n+1 : Nat) : Int) ≤ raw.length :=
    ⟨by omega, by exact_mod_cast input⟩
  obtain ⟨run,halt⟩ := TapeInstall.execute (11 : Fin 18) copySource (by decide)
    raw (encodeLabel (2*w) 0) prior (↑(n+1 : Nat) : Int) cells (ready.1 11 (by decide)) head
  rw [length_encodeLabel] at run halt
  refine ⟨run,halt,?_,?_⟩
  · intro i
    change TapeInstall.installed copySource cells (2*w) (prefixBanks i) =
      entryRegisters n x y identity cut i
    have hi : (prefixBanks i).val < 11 := i.isLt
    have hs : copySource (prefixBanks i) = some (sourceBank i) := by
      simp [copySource, prefixBanks, hi]
    rw [TapeInstall.installed_exact copySource cells (2*w) _ _ hs]
    · exact (ready.1 _ (source_high i)).trans (template_eq n x y identity cut i)
    · intro p hp
      rw [ready.2 _ hi p hp, ready.1 _ (source_high i), template_eq]
      exact (template_outside n x y identity cut i p hp).symm
  · intro j hj
    exact TapeInstall.installed_source copySource cells (2*w) j
      (by simp [copySource, show ¬ j.val < 11 by omega])

end Mathproof.MinimumGeneration.CayleyPrefixLeaf
