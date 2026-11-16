import Mathproof.MinimumGenerationRegisterInit
import Mathproof.MinimumGenerationPhysicalEntry

namespace Mathproof.MinimumGeneration.HeaderSetup

open SearchTransducer
open InputScan (headerMachine scanned counterBits counterTape)

private def orderBank : Fin headerMachine.workTapes ↪ Fin 2 where
  toFun _ := 0
  inj' i j _ := by
    change Fin 1 at i j
    exact Subsingleton.elim i j

private def pairBanks : Fin RegisterInit.prepareZeros.workTapes ↪ Fin 2 :=
  Function.Embedding.refl (Fin 2)

def machine : SearchTransducer :=
  thenMachine headerMachine RegisterInit.prepareZeros orderBank pairBanks

private def headerConfig (c : headerMachine.Config) :
    (headerMachine.relocateBanks orderBank).Config :=
  headerMachine.bankConfig orderBank c (fun _ => 0) (fun _ _ => none)

private def zeroConfig (c : RegisterInit.prepareZeros.Config) :
    (RegisterInit.prepareZeros.relocateBanks pairBanks).Config :=
  RegisterInit.prepareZeros.bankConfig pairBanks c (fun _ => 0) (fun _ _ => none)

private theorem initial_ready :
    machine.initial = thenLeft headerMachine RegisterInit.prepareZeros orderBank pairBanks
      (headerConfig headerMachine.initial) := by
  have hc : (headerConfig headerMachine.initial).workCell = fun _ _ => none := by
    funext i
    fin_cases i <;> rfl
  have hh : (headerConfig headerMachine.initial).workHead = fun _ => 0 := by
    funext i
    fin_cases i <;> rfl
  change _ = thenLeft headerMachine RegisterInit.prepareZeros orderBank pairBanks _
  unfold thenLeft
  rw [hc, hh]
  rfl

private theorem handoff (n : ℕ) :
    thenEntry headerMachine RegisterInit.prepareZeros orderBank pairBanks
      (headerConfig (scanned n)) = zeroConfig (RegisterInit.zeroStart n (counterBits n) []) := by
  have hc : (headerConfig (scanned n)).workCell =
      (zeroConfig (RegisterInit.zeroStart n (counterBits n) [])).workCell := by
    funext i
    fin_cases i
    · rfl
    · funext p
      change none = counterTape 0 [] p
      simp [counterTape]
  have hh : (headerConfig (scanned n)).workHead =
      (zeroConfig (RegisterInit.zeroStart n (counterBits n) [])).workHead := by
    funext i
    fin_cases i <;> rfl
  exact congrArg₂ (fun h c => (⟨RegisterInit.prepareZeros.initialState,
    (n : Int), h, c, []⟩ : (RegisterInit.prepareZeros.relocateBanks pairBanks).Config)) hh hc

private theorem zeroConfig_cells (q : RegisterInit.prepareZeros.Config) :
    (zeroConfig q).workCell = q.workCell := by
  funext i
  fin_cases i <;> rfl

/-- From the raw input and entirely blank work tapes, initialize the binary
order bank and a companion zero bank. Both are ready at the live delimiter. -/
theorem setup_cayley (n : ℕ) (M : Mul (Fin n)) :
    let word := @encodeCayley n M
    ∃ (t : ℕ) (c : machine.Config),
      machine.after word t = some c ∧ machine.step word c = none ∧
      machine.logarithmicWorkspace 2 word ∧ c.inputHead = (n : Int) ∧
      (∀ i, c.workHead i = 0) ∧
      c.workCell ⟨0, by decide⟩ = counterTape 0 (counterBits n) ∧
      c.workCell ⟨1, by decide⟩ = counterTape 0 (List.replicate (counterBits n).length false) ∧
      c.outputReversed = [] := by
  let word := @encodeCayley n M
  let W := Nat.log2 (word.length + 1) + 1
  let bits := counterBits n
  let B := 2 * W
  have hn : n ≤ word.length := by
    change n ≤ (@encodeCayley n M).length
    rw [@length_encodeCayley n M]
    omega
  obtain ⟨⟨k, hk⟩, hhalt, hspace⟩ := @InputScan.headerMachine_cayley n M
  have ha : headerMachine.BoundedSegment word W headerMachine.initial (scanned n) k := by
    refine ⟨by rw [runFrom_initial]; exact hk, ?_⟩
    intro t _ x hx
    rw [runFrom_initial] at hx
    simpa only [Bounded, Nat.one_mul] using hspace t x hx
  have ha' := relocateBanks_segment headerMachine orderBank
    (PhysicalEntry.segment_mono ha (show W ≤ B by omega))
    (heads := fun _ => 0) (cells := fun _ _ => none) (by simp)
  have hhalt' : (headerMachine.relocateBanks orderBank).step word (headerConfig (scanned n)) = none := by
    unfold headerConfig
    rw [relocateBanks_step, hhalt]
    rfl
  have hw : bits.length ≤ W := InputScan.counterBits_length_le n (word.length+1) (by omega)
  have hW : 0 < W := by simp [W]
  let cZ := RegisterInit.zeroDone (n : Int) bits []
  obtain ⟨hz, hzh⟩ := RegisterInit.prepareZeros_correct word bits [] n
  have hb : RegisterInit.prepareZeros.BoundedSegment word B
      (RegisterInit.zeroStart (n : Int) bits []) cZ (bits.length+2+bits.length+1) := by
    apply PhysicalEntry.segment_of_prefix hz
    intro t x hx
    obtain ⟨hi, _, _, hh⟩ := RegisterInit.prepareZeros_bounds word bits [] n t x hx
    refine ⟨by rw [hi]; omega, by rw [hi]; omega, ?_⟩
    intro i
    obtain ⟨h0, hmax⟩ := hh i
    have he : ((x.workHead i).natAbs : Int) = x.workHead i :=
      Int.natAbs_of_nonneg h0
    omega
  have hb' := relocateBanks_segment RegisterInit.prepareZeros pairBanks hb
    (heads := fun _ => 0) (cells := fun _ _ => none) (by simp)
  change (RegisterInit.prepareZeros.relocateBanks pairBanks).BoundedSegment word B
    (zeroConfig (RegisterInit.zeroStart (n : Int) bits [])) (zeroConfig cZ) _ at hb'
  rw [← handoff n] at hb'
  let final := thenRight headerMachine RegisterInit.prepareZeros orderBank pairBanks (zeroConfig cZ)
  have hr := thenSegment headerMachine RegisterInit.prepareZeros orderBank pairBanks ha' hhalt' hb'
  change machine.BoundedSegment word B
    (thenLeft headerMachine RegisterInit.prepareZeros orderBank pairBanks
      (headerConfig headerMachine.initial)) final _ at hr
  rw [← initial_ready] at hr
  have hf : machine.step word final = none := by
    change (thenMachine headerMachine RegisterInit.prepareZeros orderBank pairBanks).step word
      (thenRight headerMachine RegisterInit.prepareZeros orderBank pairBanks (zeroConfig cZ)) = none
    rw [thenStep_right]
    unfold zeroConfig
    rw [relocateBanks_step, hzh]
    rfl
  have hspace' := (BoundedSegment.logspaceOutput machine hr hf).1
  refine ⟨_, final, (runFrom_initial machine word _).symm.trans hr.1, hf, hspace',
    rfl, ?_, rfl, ?_, rfl⟩
  · intro i
    fin_cases i <;> rfl
  · change (zeroConfig cZ).workCell (1 : Fin 2) = _
    rw [zeroConfig_cells]
    exact RegisterInit.zeroDone_bank bits [] n

theorem counterTape_eq_marked (bits : List Bool) :
    counterTape 0 bits = InputPosition.work bits := by
  funext p
  by_cases h : p ≤ 0 <;> simp [counterTape, InputPosition.work, h]

/-- The one physical move from the checked unary delimiter to the table
payload. The same transition can be placed in any caller layout. -/
def payloadEntry (tapes : ℕ) : SearchTransducer where
  states := 2
  workTapes := tapes
  initialState := 0
  transition q input _ := match q.val, input with
    | 0, .data false => some (1, .right, (fun _ => ⟨none, .stay⟩), none)
    | _, _ => none

def payloadConfig (tapes : ℕ) (q : Fin 2) (position : Int)
    (heads : Fin tapes → Int) (cells : Fin tapes → Int → Option Bool) (out : List Bool) :
    (payloadEntry tapes).Config :=
  ⟨q, position, heads, cells, out⟩

theorem payloadEntry_correct (tapes n : ℕ) (M : Mul (Fin n))
    (heads : Fin tapes → Int) (cells : Fin tapes → Int → Option Bool)
    (out : List Bool) (B : ℕ) (h : ∀ i, (heads i).natAbs ≤ B) :
    let word := @encodeCayley n M
    let e := payloadEntry tapes
    e.BoundedSegment word B (payloadConfig tapes 0 (n : Int) heads cells out)
      (payloadConfig tapes 1 ((n : Int)+1) heads cells out) 1 ∧
      e.step word (payloadConfig tapes 1 ((n : Int)+1) heads cells out) = none := by
  let word := @encodeCayley n M
  let e := payloadEntry tapes
  let c := payloadConfig tapes 0 (n : Int) heads cells out
  let d := payloadConfig tapes 1 ((n : Int)+1) heads cells out
  have hr : readInput word (n : Int) = .data false := by
    obtain ⟨b, hb⟩ := @InputScan.headed_encodeCayley n M
    change readInput (@encodeCayley n M) (n : Int) = _
    rw [hb]
    exact InputScan.read_headed_false n b
  have hn : n + 1 ≤ word.length := by
    change n+1 ≤ (@encodeCayley n M).length
    rw [@length_encodeCayley n M]
    omega
  have hs : e.step word c = some d := by
    simp [e, c, d, SearchTransducer.step, payloadEntry, payloadConfig,
      Mathproof.Multitape.Locality.moveOffset, hr]
  have hp : e.runFrom word c 1 = some d := hs
  refine ⟨⟨hp, ?_⟩, by rfl⟩
  intro k hk x hx
  have h01 : k = 0 ∨ k = 1 := by omega
  rcases h01 with rfl | rfl
  · change some c = some x at hx
    cases hx
    exact ⟨by change (-1 : Int) ≤ n; omega,
      by change (n : Int) ≤ (word.length : Int); omega, h⟩
  · rw [hp] at hx
    cases hx
    exact ⟨by change (-1 : Int) ≤ (n : Int)+1; omega,
      by change (n : Int)+1 ≤ (word.length : Int); omega, h⟩

end Mathproof.MinimumGeneration.HeaderSetup
