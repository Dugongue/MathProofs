import EvenFlattening
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fintype.Option

namespace Mathproof.EvenTI.Reciprocal.Coverage

open EvenTI.Action

noncomputable section

abbrev High (l n : Nat) := Fin (n^l / 2)
abbrev Low (l n : Nat) := Fin (n^l - n^l / 2)
abbrev OtherModes (n : Nat) := Fin (n - 1)
abbrev Chosen (l n : Nat) := Fin (n^l / 5)

def highChoice (l n : Nat) : Chosen l n ↪ High l n :=
  Fin.castLEEmb (by omega)

def lowChoice (l n : Nat) : Chosen l n ↪ Low l n :=
  Fin.castLEEmb (by omega)

def bundleEquiv (l n : Nat) : Sum (High l n) (Low l n) ≃ Coord l n :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, cut_side_card]
    omega)

def distinguishedEquiv (n : Nat) (hn : 1 ≤ n) : Option (OtherModes n) ≃ Fin n :=
  Fintype.equivOfCardEq (by rw [Fintype.card_option, Fintype.card_fin, Fintype.card_fin]; omega)

def leftRegroup {l n : Nat} (hn : 1 ≤ n) (i : Fin (l+1)) :
    Sum (High l n) (Low l n) × Option (OtherModes n) ≃ Coord (l+1) n :=
  (Equiv.prodCongr (bundleEquiv l n) (distinguishedEquiv n hn)).trans
    ((Equiv.prodComm _ _).trans (retainedMode i))

abbrev rightRegroup {l n : Nat} (i : Fin (l+1)) :
    Fin n × Coord l n ≃ Coord (l+1) n :=
  retainedMode i

theorem higherOrderBundle_size {l n : Nat} (hl : 2 ≤ l) (hn : 0 < n) :
    n^2 ≤ Fintype.card (Coord l n) := by
  rw [cut_side_card]
  exact Nat.pow_le_pow_right hn hl

theorem regroup_card_rows {l n : Nat} (hn : 1 ≤ n) (i : Fin (l+1)) :
    Fintype.card (Sum (High l n) (Low l n) × Option (OtherModes n)) = n^(l+1) :=
  (Fintype.card_congr (leftRegroup hn i)).trans (cut_side_card n (l+1))

#print axioms leftRegroup
#print axioms highChoice
#print axioms lowChoice
#print axioms higherOrderBundle_size

end
end Mathproof.EvenTI.Reciprocal.Coverage
