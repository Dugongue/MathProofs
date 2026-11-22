import Mathlib.Data.List.Basic

namespace RankCondenserFour

inductive ProbeTree (Q : Type*) where
  | leaf : Bool → ProbeTree Q
  | ask : Q → ProbeTree Q → ProbeTree Q → ProbeTree Q

def zeroPath {Q : Type*} : ProbeTree Q → List Q
  | .leaf _ => []
  | .ask q no _ => q :: zeroPath no

def run {Q : Type*} (oracle : Q → Bool) : ProbeTree Q → Bool
  | .leaf b => b
  | .ask q no yes => if oracle q then run oracle yes else run oracle no

theorem blind_transcript {Q : Type*} (oracle : Q → Bool) (tree : ProbeTree Q)
    (h : ∀ q ∈ zeroPath tree, oracle q = false) :
    run oracle tree = run (fun _ => false) tree := by
  induction tree with
  | leaf b => rfl
  | ask q no yes ihNo ihYes =>
      have hq : oracle q = false := h q (by simp [zeroPath])
      have hno : ∀ a ∈ zeroPath no, oracle a = false := by
        intro a ha
        exact h a (by simp [zeroPath, ha])
      simpa [run, hq] using ihNo hno

end RankCondenserFour
