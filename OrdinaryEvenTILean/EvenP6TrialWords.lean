import EvenP6WordReindex
import EvenP6FourTransport

namespace EvenTI.CellPreparation

open EvenTI.Action EvenTI.TrialProducer EvenTI.PrimaryAlignment
open Mathproof.EvenTI.Reciprocal.Coverage (HigherModes)

variable {K : Type} [Field K] [DecidableEq K] {l n : ℕ}

def reciprocalPhysicalOrder (l : ℕ) : Fin ((l + 1) + (l + 1)) ≃ Fin ((l + 1) + (l + 1)) :=
  (reciprocalOrder l).trans (((Equiv.boolProdEquivSum _).trans (Equiv.sumComm _ _)).trans finSumFinEquiv)

def singularPhysicalOrder (l : ℕ) : Fin ((l + 1) + (l + 1)) ≃ Fin ((l + 1) + (l + 1)) :=
  (singularOrder l).trans ((Equiv.prodComm _ _).trans
    ((Equiv.boolProdEquivSum _).trans finSumFinEquiv))

def ordinarySiteOrder (l : ℕ) : Fin (l + l + 2) ≃ Fin ((l + 1) + (l + 1)) :=
  finCongr (by omega)

def fourSiteOrder : Fin (2 + 2) ≃ FourSite :=
  finProdFinEquiv.symm.trans (Equiv.prodCongr finTwoEquiv finTwoEquiv)

def fourSiteMode (i : Fin (2 + 2)) : Fin 2 :=
  finTwoEquiv.symm (fourSiteOrder i).1

def fourSiteNegative (i : Fin (2 + 2)) : Bool := (fourSiteOrder i).2

def enlargedWidth (ell : Coord 2 n → K) : ℕ :=
  (n - rawFrameWidth ell) + (rawFrameWidth ell + (n - rawFrameWidth ell))

def fourModeWidth (ell rho : Coord 2 n → K) (i : Fin 2) : ℕ :=
  if finTwoEquiv i then enlargedWidth rho else enlargedWidth ell

def fourNumericOrder (ell rho : Coord 2 n → K) (i : Fin (2 + 2)) :
    Fin (fourModeWidth ell rho (fourSiteMode i)) ≃
      fourWidth (RawEnlargedIndex ell) (RawEnlargedIndex rho) (fourSiteOrder i) := by
  unfold fourModeWidth fourSiteMode
  rw [Equiv.apply_symm_apply]
  generalize (fourSiteOrder i) = b
  rcases b with ⟨a, z⟩
  cases a
  · exact (enlargedOrder (rawFrameWidth ell) (n - rawFrameWidth ell)).symm
  · exact (enlargedOrder (rawFrameWidth rho) (n - rawFrameWidth rho)).symm

structure TrialWords (K : Type) where
  modeCount : ℕ
  sites : ℕ
  mode : Fin (sites + 2) → Fin modeCount
  minus : Fin (sites + 2) → Bool
  width : Fin modeCount → ℕ
  source : Grid K (fun i => Fin (width (mode i)))
  target : Grid K (fun i => Fin (width (mode i)))

def ordinaryTrialWords (o : Fin ((l + 1) + (l + 1)) ≃ Fin ((l + 1) + (l + 1)))
    (T S : Dense K l n) : TrialWords K :=
  let e := (ordinarySiteOrder l).trans o
  ⟨l + l + 2, l + l, id, fun _ => false, fun _ => n,
    reindexWords e (fun _ => Equiv.refl _) T, reindexWords e (fun _ => Equiv.refl _) S⟩

/-- Materialize the dense arrays for the actual trial pair. On the enlarged
branch the target is read in the source dimensions after the two size tests. -/
def pairedTrialWords (T S : Dense K l n) (P Q : PreparedTrial K l n) : Option (TrialWords K) :=
  match P, Q with
  | .reciprocal _, .reciprocal _ => some (ordinaryTrialWords (reciprocalPhysicalOrder l) T S)
  | .higher _ _, .higher _ _ => some (ordinaryTrialWords (singularPhysicalOrder l) T S)
  | .orderFour hl p _ _, .orderFour hr q _ _ =>
    if ha : rawFrameWidth q.1 = rawFrameWidth p.1 then
      if hb : rawFrameWidth q.2 = rawFrameWidth p.2 then
        let w := fourModeWidth p.1 p.2
        let e := fourNumericOrder p.1 p.2
        let fL := enlargedIndexEquiv ha (congrArg (fun d => n - d) ha)
        let fR := enlargedIndexEquiv hb (congrArg (fun d => n - d) hb)
        let f := fun i => (e i).trans (show
            fourWidth (RawEnlargedIndex p.1) (RawEnlargedIndex p.2) (fourSiteOrder i) ≃
            fourWidth (RawEnlargedIndex q.1) (RawEnlargedIndex q.2) (fourSiteOrder i) from by
          generalize (fourSiteOrder i) = b
          rcases b with ⟨a, z⟩
          cases a
          · exact fL
          · exact fR)
        some ⟨2, 2, fourSiteMode, fourSiteNegative, w,
          reindexWords fourSiteOrder e (rawEnlargedWords p.1 p.2 (castFour hl T)),
          reindexWords fourSiteOrder f (rawEnlargedWords q.1 q.2 (castFour hr S))⟩
      else none
    else none
  | _, _ => none

theorem pairedTrialWords_total [Fintype K] (T : Dense K l n) (g : Changes K ((l + 1) + (l + 1)) n)
    (P Q : PreparedTrial K l n) (hm : PreparedMatch T g P Q) :
    ∃ w, pairedTrialWords T (act g T) P Q = some w := by
  cases hm with
  | reciprocal A h => exact ⟨_, rfl⟩
  | higher hl p h => exact ⟨_, rfl⟩
  | four hl p h =>
    subst l
    unfold fourTrial pairedTrialWords
    dsimp only
    have hL : rawFrameWidth (moveLeftForm (l := 2) (r := 2)
        (castFourChanges (l := 1) rfl g) p.1) = rawFrameWidth p.1 :=
      rawFrameWidth_move (leftModes (l := 2) (r := 2) g) p.1
    have hR : rawFrameWidth (moveRightForm (l := 2) (r := 2)
        (castFourChanges (l := 1) rfl g) p.2) = rawFrameWidth p.2 :=
      rawFrameWidth_move (rightModes (l := 2) (r := 2) g) p.2
    rw [dif_pos hL, dif_pos hR]
    exact ⟨_, rfl⟩

#print axioms pairedTrialWords
#print axioms pairedTrialWords_total

end EvenTI.CellPreparation
