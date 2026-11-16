import Mathproof.MinimumGenerationCayleyReaderCycle
import Mathproof.MinimumGenerationNativeBipartiteCall

namespace Mathproof.MinimumGeneration.NativePhysicalReader

open SearchTransducer VirtualCallbackDriver
open InputPosition (work)
open VirtualTapeStep (routed pointerBank)
open CayleyQueryPrefixModel (rawSpace cells keep width)

def readerBank (M : SearchTransducer) : Fin 74 ↪ Fin (74 + M.workTapes) :=
  ⟨Fin.castAdd _, fun _ _ h => Fin.ext (congrArg (fun i : Fin (74 + M.workTapes) => i.val) h)⟩

def nativeBank (M : SearchTransducer) : Fin M.workTapes ↪ Fin (74 + M.workTapes) :=
  ⟨Fin.natAdd 74, fun _ _ h => Fin.ext (Nat.add_left_cancel (congrArg (fun i : Fin (74 + M.workTapes) => i.val) h))⟩

abbrev address : Fin 74 := CayleyReaderCycle.originalBank 33

def playbackBanks (M : SearchTransducer) : Fin (routed M).workTapes ↪ Fin (74 + M.workTapes) where
  toFun i := if h : i.val < M.workTapes then nativeBank M ⟨i.val,h⟩ else readerBank M address
  inj' i j he := by
    dsimp only at he
    split at he <;> split at he
    · exact Fin.ext (congrArg (fun i : Fin M.workTapes => i.val) ((nativeBank M).injective he))
    · have h := congrArg Fin.val he
      change 74 + i.val = 33 at h
      omega
    · have h := congrArg Fin.val he
      change 33 = 74 + j.val at h
      omega
    · have h₁ : i.val < M.workTapes + 1 := i.isLt
      have h₂ : j.val < M.workTapes + 1 := j.isLt
      exact Fin.ext (by omega)

@[simp] theorem playbackNative (M : SearchTransducer) (i : Fin M.workTapes) :
    playbackBanks M i.castSucc = nativeBank M i := by
  unfold playbackBanks
  simp [i.isLt]

@[simp] theorem playbackPointer (M : SearchTransducer) :
    playbackBanks M (pointerBank M) = readerBank M address := by
  simp [playbackBanks, pointerBank]

theorem native_not_reader (M : SearchTransducer) (i : Fin M.workTapes) :
    nativeBank M i ∉ Set.range (readerBank M) := by
  rintro ⟨j,h⟩
  have v := congrArg Fin.val h
  change j.val = 74 + i.val at v
  have := j.isLt
  omega

theorem reader_not_playback (M : SearchTransducer) (j : Fin 74) (h : j ≠ address) :
    readerBank M j ∉ Set.range (playbackBanks M) := by
  rintro ⟨i,hi⟩
  refine Fin.lastCases ?_ (fun a => ?_) i hi
  · change playbackBanks M (pointerBank M) = readerBank M j → False
    rw [playbackPointer]
    exact fun eq => h ((readerBank M).injective eq.symm)
  · rw [playbackNative]
    exact fun hEq => native_not_reader M a ⟨j,hEq.symm⟩

abbrev callback (M : SearchTransducer) : Callback :=
  ⟨CayleyReaderCycle.machine.relocateBanks (readerBank M), CayleyReaderCycle.callback.returnCell⟩

theorem originalBank_restore (i : Fin 35) :
    CayleyReaderCycle.restoreBanks (CayleyReaderRestore.readerBanks i) =
      CayleyReaderCycle.originalBank i := by
  apply Fin.ext
  change (if i.val < 35 then i.val else i.val+35) = i.val
  rw [if_pos i.isLt]

theorem cells_address {n : ℕ} (G : Group (Fin n)) (cut : ℕ) (s t : Fin (n+n)) (p : ℕ) :
    cells G cut s t p 33 = work (encodeLabel (width n) p) := by
  rfl

theorem pointer_of_ready {n : ℕ} {G : Group (Fin n)} {cut : ℕ} {s t : Fin (n+n)}
    {p : ℕ} {clock : List Bool} {old : Fin 74 → Int → Option Bool}
    (ready : CayleyReaderCycle.Ready G cut s t p clock old) :
    old address = work (encodeLabel (width n) p) := by
  have a := ready.body.live 33 (by change 21 ≤ (33 : Fin 35).val ∧ (33 : Fin 35).val ≠ 22 ∧ (33 : Fin 35).val ≠ 25; decide)
  rw [originalBank_restore, cells_address] at a
  exact a

private theorem cells_unchanged {n : ℕ} (G : Group (Fin n)) (cut : ℕ) (s t : Fin (n+n))
    (p q : ℕ) (i : Fin 35) (hk : i ∈ keep) (hi : i ≠ 33) :
    cells G cut s t p i = cells G cut s t q i := by
  have hn : ¬ i.val < 10 := by
    change 21 ≤ i.val ∧ i.val ≠ 22 ∧ i.val ≠ 25 at hk
    omega
  have hd : i ≠ CayleyQueryPrefixModel.addressBank := hi
  simp [cells, hn, hd]

/-- Changing only the routed address preserves the recurrent reader's exact
bank layout at the new value. -/
theorem changeAddress {n : ℕ} {G : Group (Fin n)} {cut : ℕ} {s t : Fin (n+n)}
    {p q : ℕ} {clock : List Bool} {old new : Fin 74 → Int → Option Bool}
    (ready : CayleyReaderCycle.Ready G cut s t p clock old)
    (same : ∀ j, j ≠ address → new j = old j)
    (addressValue : new address = work (encodeLabel (width n) q)) :
    CayleyReaderCycle.Ready G cut s t q clock new := by
  refine ⟨⟨?_,ready.body.clockEnough,?_,?_,?_,?_,?_⟩,?_⟩
  · exact (same _ (by decide)).trans ready.body.clockWord
  · exact (same _ (by decide)).trans ready.body.cardinality
  · exact (same _ (by decide)).trans ready.body.order
  · exact (same _ (by decide)).trans ready.body.clean
  · intro i hi
    rw [originalBank_restore]
    by_cases eq : i = 33
    · subst i
      exact addressValue.trans (cells_address G cut s t q).symm
    · have ne : CayleyReaderCycle.originalBank i ≠ address :=
        fun h => eq (Fin.ext (congrArg (fun j : Fin 74 => j.val) h))
      rw [same _ ne, ← originalBank_restore]
      exact (ready.body.live i hi).trans (cells_unchanged G cut s t p q i hi eq)
  · intro i z hz
    rw [originalBank_restore]
    by_cases eq : i = 33
    · subst i
      rw [addressValue]
      exact CayleyReaderFrame.workOutside
        (by rw [length_encodeLabel]; exact (Nat.le_succ _).trans (CayleyQueryPrefixModel.width_le G))
        z hz
    · have ne : CayleyReaderCycle.originalBank i ≠ address :=
        fun h => eq (Fin.ext (congrArg (fun j : Fin 74 => j.val) h))
      rw [same _ ne, ← originalBank_restore]
      exact ready.body.outside i z hz
  · intro i
    exact (same _ (fun eq => by
      have v := congrArg Fin.val eq
      change 35 + i.val = 33 at v
      omega)).trans (ready.shadows i)

end Mathproof.MinimumGeneration.NativePhysicalReader
