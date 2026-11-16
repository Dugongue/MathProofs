import Mathproof.MinimumGenerationHeaderSetup
import Mathproof.MinimumGenerationPhysicalInverse

namespace Mathproof.MinimumGeneration.RawIdentity

open SearchTransducer
open InputScan (counterBits counterTape)
open RegisterInit (prepareZeros zeroStart zeroDone)
open HeaderSetup (payloadEntry payloadConfig)

private def native (i : Fin 5) : SearchTransducer :=
  if i = 0 then HeaderSetup.machine else if i = 1 ∨ i = 2 then prepareZeros
  else if i = 3 then payloadEntry 4 else PhysicalInverse.machine

private theorem nativeStates (i : Fin 5) : (native i).states ≤ 30 := by
  fin_cases i <;> decide

private def headerBanks : Fin HeaderSetup.machine.workTapes ↪ Fin 4 :=
  ⟨fun i => i.castLE (by decide), fun _ _ h => Fin.ext (congrArg (fun i : Fin 4 => i.val) h)⟩

private def zeroSecond : Fin prepareZeros.workTapes ↪ Fin 4 :=
  ⟨fun i => if i.val = 0 then 0 else 2, by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all⟩

private def zeroThird : Fin prepareZeros.workTapes ↪ Fin 4 :=
  ⟨fun i => if i.val = 0 then 0 else 3, by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all⟩

private def scanBanks : Fin PhysicalInverse.machine.workTapes ↪ Fin 4 :=
  ⟨fun i => i.succ, fun _ _ h => Fin.ext (Nat.add_right_cancel (congrArg Fin.val h))⟩

private def banks (i : Fin 5) : Fin (native i).workTapes ↪ Fin 4 := by
  by_cases h₀ : i = 0
  · subst i
    exact headerBanks
  by_cases h₁ : i = 1
  · subst i
    exact zeroSecond
  by_cases h₂ : i = 2
  · subst i
    exact zeroThird
  by_cases h₃ : i = 3
  · subst i
    exact Function.Embedding.refl (Fin 4)
  have h₄ : i = 4 := by fin_cases i <;> simp_all
  subst i
  exact scanBanks

private def next (i : Fin 5) (_ : Fin (native i).states) : Option (Fin 5) :=
  if i = 0 then some 1 else if i = 1 then some 2 else if i = 2 then some 3
  else if i = 3 then some 4 else none

/-- Blank-start machine: native header setup, two bank initializations,
payload positioning, and the checked first-row scanner. -/
def stages : Stages 5 30 4 :=
  Stages.ofMachines 0 native nativeStates banks next

abbrev machine : SearchTransducer := stages.machine

private def layout (bits : List Bool) (filled : ℕ) (t : Fin 4) : Int → Option Bool :=
  if t = 0 then counterTape 0 bits
  else if t.val ≤ filled then counterTape 0 (List.replicate bits.length false)
  else fun _ => none

private def cfg (i : Fin 5) (q : Fin 30) (input : Int) (cells : Fin 4 → Int → Option Bool) :
    (stages.component i).Config :=
  ⟨q, input, fun _ => 0, cells, []⟩

private def lifted (i : Fin 5) (c : (native i).Config) (xs : Fin 4 → Int → Option Bool) :
    (stages.component i).Config :=
  (native i).padConfig (nativeStates i) (banks i)
    ((native i).bankConfig (banks i) c (fun _ => 0) xs)

private theorem liftRun (i : Fin 5) {word : List Bool} {B k : ℕ}
    {c d : (native i).Config} (xs : Fin 4 → Int → Option Bool)
    (hr : (native i).BoundedSegment word B c d k) :
    (stages.component i).BoundedSegment word B (lifted i c xs) (lifted i d xs) k :=
  (native i).padMachine_segment (nativeStates i) (banks i)
    ((native i).relocateBanks_segment (banks i) hr (fun _ _ => by simp))

private theorem liftStop (i : Fin 5) {word : List Bool} {c : (native i).Config}
    (xs : Fin 4 → Int → Option Bool) (hr : (native i).step word c = none) :
    (stages.component i).step word (lifted i c xs) = none := by
  change ((native i).padMachine (nativeStates i) (banks i)).step word
    ((native i).padConfig (nativeStates i) (banks i)
      ((native i).bankConfig (banks i) c (fun _ => 0) xs)) = none
  rw [(native i).padMachine_step, (native i).relocateBanks_step, hr]
  rfl

private theorem liftHead {i : Fin 5} (c : (native i).Config) (xs : Fin 4 → Int → Option Bool)
    (zero : ∀ t, c.workHead t = 0) : (lifted i c xs).workHead = fun _ => 0 := by
  funext t
  change ((native i).bankConfig (banks i) c (fun _ => 0) xs).workHead t = 0
  by_cases ht : t ∈ Set.range (banks i)
  · obtain ⟨j, rfl⟩ := ht
    rw [bankConfig_head_image, zero]
  · exact ((native i).bankConfig_frame (banks i) c (fun _ => 0) xs ht).1

private theorem liftCellImage {i : Fin 5} (c : (native i).Config)
    (xs : Fin 4 → Int → Option Bool) (t : Fin (native i).workTapes) :
    (lifted i c xs).workCell (banks i t) = c.workCell t :=
  (native i).bankConfig_cell_image (banks i) c (fun _ => 0) xs t

private theorem liftCellFrame {i : Fin 5} (c : (native i).Config)
    (xs : Fin 4 → Int → Option Bool) {t : Fin 4} (h : t ∉ Set.range (banks i)) :
    (lifted i c xs).workCell t = xs t :=
  ((native i).bankConfig_frame (banks i) c (fun _ => 0) xs h).2

private theorem initialReady :
    stages.tag 0 (lifted 0 HeaderSetup.machine.initial (fun _ _ => none)) = machine.initial := by
  change _ = stages.machine.initial
  simp [Stages.tag, Stages.machine, lifted, padConfig, bankConfig, Stages.ofMachines,
    SearchTransducer.initial]
  refine ⟨⟨rfl, rfl⟩, ?_, ?_⟩
  · funext t
    fin_cases t <;> rfl
  · funext t
    fin_cases t <;> rfl

private theorem cfgEnter (i j : Fin 5) (state : Fin 30) (input : Int)
    (xs : Fin 4 → Int → Option Bool) :
    stages.enter j (cfg i state input xs) = cfg j (stages.entry j) input xs := rfl


private theorem cfgEq {i : Fin 5} {c : (stages.component i).Config}
    {position : Int} {memory : Fin 4 → Int → Option Bool}
    (hin : c.inputHead = position) (hheads : c.workHead = fun _ => 0)
    (hc : c.workCell = memory) (hout : c.outputReversed = []) :
    c = cfg i c.state position memory := by
  cases c
  simp_all only [cfg]

private theorem zeroRun (word : List Bool) (n : ℕ) (bits : List Bool) (B : ℕ)
    (hn : n ≤ word.length) (hB : bits.length + 1 ≤ B) :
    prepareZeros.BoundedSegment word B (zeroStart n bits []) (zeroDone n bits [])
      (bits.length + 2 + bits.length + 1) ∧
    prepareZeros.step word (zeroDone n bits []) = none := by
  obtain ⟨run, stop⟩ := RegisterInit.prepareZeros_correct word bits [] n
  refine ⟨PhysicalEntry.segment_of_prefix run ?_, stop⟩
  intro t x hx
  obtain ⟨hin, _, _, hh⟩ := RegisterInit.prepareZeros_bounds word bits [] n t x hx
  refine ⟨by rw [hin]; omega, by rw [hin]; omega, ?_⟩
  intro j
  obtain ⟨lo, hi⟩ := hh j
  have eq := Int.natAbs_of_nonneg lo
  omega

private theorem headerExit (n : ℕ) (x : HeaderSetup.machine.Config)
    (input : x.inputHead = n) (heads : ∀ i, x.workHead i = 0)
    (order : x.workCell ⟨0, by decide⟩ = counterTape 0 (counterBits n))
    (zero : x.workCell ⟨1, by decide⟩ = counterTape 0 (List.replicate (counterBits n).length false))
    (output : x.outputReversed = []) :
    let d := lifted 0 x (fun _ _ => none)
    d = cfg 0 d.state n (layout (counterBits n) 1) := by
  dsimp only
  apply cfgEq input (liftHead (i := 0) x _ heads) ?_ output
  funext i
  fin_cases i
  · exact (liftCellImage (i := 0) x _ ⟨0, by decide⟩).trans order
  · exact (liftCellImage (i := 0) x _ ⟨1, by decide⟩).trans zero
  · rfl
  · rfl

private theorem enterZeroSecond (q : Fin 30) (n : ℕ) (bits : List Bool) :
    stages.enter 1 (cfg 0 q n (layout bits 1)) =
      lifted 1 (zeroStart n bits []) (layout bits 1) := by
  rw [cfgEnter]
  simp only [cfg, lifted, padConfig, bankConfig]
  congr 1
  · funext t
    fin_cases t <;> rfl
  · funext t
    fin_cases t <;> try rfl
    funext p
    change none = counterTape 0 [] p
    simp [counterTape]

private theorem zeroSecondExit (n : ℕ) (bits : List Bool) :
    let d := lifted 1 (zeroDone n bits []) (layout bits 1)
    d = cfg 1 d.state n (layout bits 2) := by
  dsimp only
  apply cfgEq rfl (liftHead (i := 1) (zeroDone n bits []) _ (fun _ => rfl)) ?_ rfl
  funext t
  fin_cases t
  · rfl
  · rfl
  · exact (liftCellImage (i := 1) (zeroDone n bits []) _ ⟨1, by decide⟩).trans
      (RegisterInit.zeroDone_bank bits [] n)
  · rfl

private theorem enterZeroThird (q : Fin 30) (n : ℕ) (bits : List Bool) :
    stages.enter 2 (cfg 1 q n (layout bits 2)) =
      lifted 2 (zeroStart n bits []) (layout bits 2) := by
  rw [cfgEnter]
  simp only [cfg, lifted, padConfig, bankConfig]
  congr 1
  · funext t
    fin_cases t <;> rfl
  · funext t
    fin_cases t <;> try rfl
    funext p
    change none = counterTape 0 [] p
    simp [counterTape]

private theorem zeroThirdExit (n : ℕ) (bits : List Bool) :
    let d := lifted 2 (zeroDone n bits []) (layout bits 2)
    d = cfg 2 d.state n (layout bits 3) := by
  dsimp only
  apply cfgEq rfl (liftHead (i := 2) (zeroDone n bits []) _ (fun _ => rfl)) ?_ rfl
  funext t
  fin_cases t
  · rfl
  · rfl
  · rfl
  · exact (liftCellImage (i := 2) (zeroDone n bits []) _ ⟨1, by decide⟩).trans
      (RegisterInit.zeroDone_bank bits [] n)

private theorem payloadLift (q : Fin 2) (n : Int) (bits : List Bool) :
    lifted 3 (payloadConfig 4 q n (fun _ => 0) (layout bits 3) []) (layout bits 3) =
      cfg 3 (q.castLE (by decide)) n (layout bits 3) := by
  simp only [cfg, lifted, padConfig, bankConfig, payloadConfig]
  congr 1
  · funext t
    fin_cases t <;> rfl
  · funext t
    fin_cases t <;> rfl


private theorem zeroLabel (w : ℕ) : encodeLabel w 0 = List.replicate w false := by
  have h : Nat.testBit 0 = fun _ => false := by
    funext i
    exact Nat.testBit_lt_two_pow (Nat.two_pow_pos i)
  simp [encodeLabel, h]

private theorem scanEnter (q : Fin 30) (n : ℕ) (hn : 0 < n) :
    let w := TableIO.width n
    let start := PhysicalInverse.stages.tag 0
      (PhysicalInverse.entry (n + 1) (List.replicate w false)
        (encodeLabel w 0) (encodeLabel w 0) [])
    stages.enter 4 (cfg 3 q ((n : Int) + 1) (layout (counterBits n) 3)) =
      lifted 4 start (layout (counterBits n) 3) := by
  dsimp only
  let bits := counterBits n
  let w := TableIO.width n
  let start := PhysicalInverse.stages.tag 0
      (PhysicalInverse.entry (n + 1) (List.replicate w false) (encodeLabel w 0) (encodeLabel w 0) [])
  have wBits : bits.length = w := by
    change (counterBits n).length = w
    rw [InputScan.counterBits_eq_encodeLabel n (by omega)]
    simp [encodeLabel, w, TableIO.width]
  have hCells : (lifted 4 start (layout bits 3)).workCell = layout bits 3 := by
    funext t
    fin_cases t
    · rfl
    · change InputPosition.work _ = counterTape 0 (List.replicate bits.length false)
      rw [HeaderSetup.counterTape_eq_marked, wBits]
    · change InputPosition.work (encodeLabel w 0) = counterTape 0 (List.replicate bits.length false)
      rw [HeaderSetup.counterTape_eq_marked, wBits, zeroLabel]
    · change InputPosition.work (encodeLabel w 0) = counterTape 0 (List.replicate bits.length false)
      rw [HeaderSetup.counterTape_eq_marked, wBits, zeroLabel]
  have hLift := cfgEq (i := 4) (show (lifted 4 start (layout bits 3)).inputHead = (n : Int) + 1 from rfl)
    (liftHead (i := 4) start _ (fun _ => rfl)) hCells rfl
  change stages.enter 4 (cfg 3 q ((n : Int) + 1) (layout bits 3)) =
    lifted 4 start (layout bits 3)
  rw [cfgEnter, hLift]
  rfl

private theorem nextLift (i : Fin 5) (c : (native i).Config) (xs : Fin 4 → Int → Option Bool) :
    stages.next i (lifted i c xs).state = next i c.state := by
  unfold lifted padConfig stages
  apply Stages.ofMachines_next_at

/-- Run the raw identity search with its full return frame. The order, both
raw-width zero words, and the discovered identity occupy the four parked banks. -/
theorem physicalFrameFromRaw (n : ℕ) (G : Group (Fin n)) :
    let word := @encodeCayley n G.toMul
    let w := TableIO.width n
    ∃ (ticks : ℕ) (result : machine.Config),
      machine.BoundedSegment word (2 * (Nat.log2 (word.length + 1) + 1)) machine.initial result ticks ∧
      machine.step word result = none ∧ result.workHead = (fun _ => 0) ∧ result.outputReversed = [] ∧
      result.workCell = fun i => InputPosition.work
        (encodeLabel w (if i = 0 then n else if i = 3 then G.toOne.one.val else 0)) := by
  let word := @encodeCayley n G.toMul
  let w := TableIO.width n
  let bits := counterBits n
  let W := Nat.log2 (word.length + 1) + 1
  let B := 2 * W
  have positive : 0 < n := (Nat.zero_le _).trans_lt G.toOne.one.isLt
  have hn : n ≤ word.length := by
    change n ≤ (@encodeCayley n G.toMul).length
    rw [@length_encodeCayley n G.toMul]
    omega
  have bitsWidth : bits.length = w := by
    change (counterBits n).length = w
    rw [InputScan.counterBits_eq_encodeLabel n (by omega)]
    simp [encodeLabel, w, TableIO.width]
  have hw : w ≤ W := by
    have h : bits.length ≤ W := InputScan.counterBits_length_le n (word.length + 1) (by omega)
    exact bitsWidth ▸ h
  have hB : bits.length + 1 ≤ B := by omega
  have hW : w + 1 ≤ B := by omega
  obtain ⟨k₀, e₀, he₀, halt₀, space₀, input₀, heads₀, order₀, zero₀, out₀⟩ :=
    HeaderSetup.setup_cayley n G.toMul
  have h0 : HeaderSetup.machine.BoundedSegment word B HeaderSetup.machine.initial e₀ k₀ := by
    refine ⟨by rw [runFrom_initial]; exact he₀, ?_⟩
    intro k hk c hc
    rw [runFrom_initial] at hc
    exact space₀ k c hc
  have run₀ := liftRun 0 (fun _ _ => none) h0
  have stop₀ := liftStop 0 (fun _ _ => none) halt₀
  let d₀ := lifted 0 e₀ (fun _ _ => none)
  have move₀ : stages.next 0 d₀.state = some 1 := (nextLift 0 e₀ _).trans rfl
  have jump₀ : stages.enter 1 d₀ = lifted 1 (zeroStart n bits []) (layout bits 1) := by
    have h := headerExit n e₀ input₀ heads₀ order₀ zero₀ out₀
    change d₀ = _ at h
    rw [h]
    exact enterZeroSecond _ n bits
  obtain ⟨hz, haltZ⟩ := zeroRun word n bits B hn hB
  have run₁ := liftRun 1 (layout bits 1) hz
  have stop₁ := liftStop 1 (layout bits 1) haltZ
  let d₁ := lifted 1 (zeroDone n bits []) (layout bits 1)
  have move₁ : stages.next 1 d₁.state = some 2 := (nextLift 1 (zeroDone n bits []) _).trans rfl
  have jump₁ : stages.enter 2 d₁ = lifted 2 (zeroStart n bits []) (layout bits 2) := by
    have h := zeroSecondExit n bits
    change d₁ = _ at h
    rw [h]
    exact enterZeroThird _ n bits
  have run₂ := liftRun 2 (layout bits 2) hz
  have stop₂ := liftStop 2 (layout bits 2) haltZ
  let d₂ := lifted 2 (zeroDone n bits []) (layout bits 2)
  have move₂ : stages.next 2 d₂.state = some 3 := (nextLift 2 (zeroDone n bits []) _).trans rfl
  let c₃ := payloadConfig 4 0 n (fun _ => 0) (layout bits 3) []
  let e₃ := payloadConfig 4 1 ((n : Int) + 1) (fun _ => 0) (layout bits 3) []
  have jump₂ : stages.enter 3 d₂ = lifted 3 c₃ (layout bits 3) := by
    have h := zeroThirdExit n bits
    change d₂ = _ at h
    rw [h, cfgEnter]
    unfold c₃
    rw [payloadLift]
    rfl
  obtain ⟨h3, halt3⟩ := HeaderSetup.payloadEntry_correct 4 n G.toMul
    (fun _ => 0) (layout bits 3) [] B (by simp)
  have run₃ := liftRun 3 (layout bits 3) h3
  have stop₃ := liftStop 3 (layout bits 3) halt3
  let d₃ := lifted 3 e₃ (layout bits 3)
  have move₃ : stages.next 3 d₃.state = some 4 := (nextLift 3 e₃ _).trans rfl
  let c₄ := PhysicalInverse.stages.tag 0
      (PhysicalInverse.entry (n + 1) (List.replicate w false) (encodeLabel w 0) (encodeLabel w 0) [])
  have jump₃ : stages.enter 4 d₃ = lifted 4 c₄ (layout bits 3) := by
    unfold d₃ e₃
    rw [payloadLift]
    exact scanEnter _ n positive
  let row : Fin n := ⟨0,positive⟩
  have off : TableIO.offset n row.val 0 = n+1 := by simp [TableIO.offset,row]
  have native := PhysicalInverse.physicalRightSolve_frame n G row row G.toOne.one (G.mul_one row) []
  dsimp only at native
  rw [off] at native
  obtain ⟨k₄, e₄, h4, halt4, cells4, out4, heads4, cap4, target4⟩ := native
  have run₄ := liftRun 4 (layout bits 3) (PhysicalEntry.segment_mono h4 hW)
  have stop₄ := liftStop 4 (layout bits 3) halt4
  let d₄ := lifted 4 e₄ (layout bits 3)
  have move₄ : stages.next 4 d₄.state = none := (nextLift 4 e₄ _).trans rfl
  have route₄ : stages.Routed word B 4 (stages.enter 4 d₃) 4 d₄ k₄ := by
    rw [jump₃]
    exact .finish run₄
  have route₃ := Stages.Routed.call run₃ stop₃ move₃ route₄
  rw [← jump₂] at route₃
  have route₂ := Stages.Routed.call run₂ stop₂ move₂ route₃
  rw [← jump₁] at route₂
  have route₁ := Stages.Routed.call run₁ stop₁ move₁ route₂
  rw [← jump₀] at route₁
  obtain ⟨run, stop⟩ := stages.routed_stop
    (Stages.Routed.call run₀ stop₀ move₀ route₁) stop₄ move₄
  rw [initialReady] at run
  refine ⟨_,stages.tag 4 d₄,run,stop,?_,out4,?_⟩
  · exact liftHead (i := 4) e₄ (layout bits 3) (fun j => congrFun heads4 j)
  · funext i
    fin_cases i
    · have frame : (0 : Fin 4) ∉ Set.range (banks (4 : Fin 5)) := by
        rintro ⟨j,h⟩
        change Fin 3 at j
        fin_cases j <;> contradiction
      change d₄.workCell 0 = InputPosition.work (encodeLabel w n)
      rw [liftCellFrame (i := 4) e₄ (layout bits 3) frame]
      change counterTape 0 (counterBits n) = _
      rw [HeaderSetup.counterTape_eq_marked,InputScan.counterBits_eq_encodeLabel n positive.ne']
      rfl
    · exact (liftCellImage (i := 4) e₄ (layout bits 3) (0 : Fin 3)).trans cap4
    · exact (liftCellImage (i := 4) e₄ (layout bits 3) (1 : Fin 3)).trans target4
    · exact (liftCellImage (i := 4) e₄ (layout bits 3) (2 : Fin 3)).trans cells4

/-- The raw identity search starts from blank work tapes and has logarithmic workspace. -/
theorem physicalIdentityFromRaw (n : ℕ) (G : Group (Fin n)) :
    let word := @encodeCayley n G.toMul
    let w := TableIO.width n
    ∃ (ticks : ℕ) (result : machine.Config),
      machine.after word ticks = some result ∧ machine.step word result = none ∧
      machine.logarithmicWorkspace 2 word ∧
      result.workCell 3 = InputPosition.work (encodeLabel w G.toOne.one.val) := by
  obtain ⟨ticks,result,run,stop,_,_,cells⟩ := physicalFrameFromRaw n G
  exact ⟨ticks,result,(runFrom_initial machine _ _).symm.trans run.1,stop,
    (BoundedSegment.logspaceOutput machine run stop).1,congrFun cells 3⟩

end Mathproof.MinimumGeneration.RawIdentity
