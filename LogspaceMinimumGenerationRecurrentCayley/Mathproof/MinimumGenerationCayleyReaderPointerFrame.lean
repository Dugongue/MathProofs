import Mathproof.MinimumGenerationCayleyReaderFrame

namespace Mathproof.MinimumGeneration.CayleyQueryPrefixModel

open InputPosition (work)

theorem shadowAddressCell {n : Nat} (G : Group (Fin n)) (cut : Nat)
    (s t : Fin (n+n)) (p : Nat) :
    cells G cut s t p 4 = work (encodeLabel (width n) p) := by
  rfl

theorem liveAddressCell {n : Nat} (G : Group (Fin n)) (cut : Nat)
    (s t : Fin (n+n)) (p : Nat) :
    cells G cut s t p 33 = work (encodeLabel (width n) p) := by
  rfl

/-- The prepared reader duplicates the virtual pointer into coordinate scratch
and the persistent address tape. Every other prepared tape is independent
of the pointer. -/
theorem cells_unchangedAwayFromAddress {n : Nat} (G : Group (Fin n)) (cut : Nat)
    (s t : Fin (n+n)) (p q : Nat) (i : Fin 35) (notScratch : i ≠ 4)
    (notLive : i ≠ 33) : cells G cut s t p i = cells G cut s t q i := by
  have scratch : i.val ≠ 4 := fun h => notScratch (Fin.ext h)
  unfold cells
  split
  · rename_i lt
    unfold CayleyQueryCoordinates.entryCells
    split
    · rename_i low
      have away : (⟨i.val, low⟩ : Fin 5) ≠ CayleyQueryDispatch.OffsetInstall.offsetBank :=
        fun e => scratch (congrArg Fin.val e)
      simp [CayleyQueryDispatch.OffsetInstall.live, away]
    · rfl
  · have away : i ≠ addressBank := notLive
    simp [away]

/-- The exact persistent address word fits in the reader's restored interval. -/
theorem addressOutside {n : Nat} (G : Group (Fin n)) (cut : Nat)
    (s t : Fin (n+n)) (p : Nat) (z : Int)
    (away : rawSpace (@encodeCayley n G.toMul) < z.natAbs) :
    work (encodeLabel (width n) p) z = none := by
  rw [← liveAddressCell G cut s t p]
  exact CayleyReaderFrame.entryOutside G cut s t p 33 z away

end Mathproof.MinimumGeneration.CayleyQueryPrefixModel
