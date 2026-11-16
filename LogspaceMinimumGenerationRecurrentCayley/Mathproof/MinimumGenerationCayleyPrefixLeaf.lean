import Mathproof.MinimumGenerationOuterCayleyQuery
import Mathproof.MinimumGenerationPrefixQuotientVerdict

namespace Mathproof.MinimumGeneration.CayleyPrefixLeaf

open SearchTransducer
open ReingoldLiveInput (difference)
open OuterCayleyQuery (solver)
open InputPosition (work)

set_option backward.isDefEq.respectTransparency false

abbrev P := PrefixQuotientVerdict.machine

def quotientBanks : Fin solver.workTapes ↪ Fin 11 :=
  ⟨Fin.castLE (by decide), fun _ _ h => Fin.ext (congrArg (fun i : Fin 11 => i.val) h)⟩

def verdictBanks : Fin P.workTapes ↪ Fin 11 :=
  ⟨Fin.natAdd 8, fun _ _ h => Fin.ext (Nat.add_left_cancel (congrArg (fun i : Fin 11 => i.val) h))⟩

abbrev machine := OuterCayleyQuery.machine P quotientBanks verdictBanks

private def parked : Fin 11 → Int := fun _ => 0

def frame (n identity cut : Nat) (i : Fin 11) : Int → Option Bool :=
  if i = 9 then work (encodeLabel (TableIO.width n) identity)
  else if i = 10 then work (encodeLabel (TableIO.width n) cut) else fun _ => none

def entry (n x y identity cut : Nat) (prior : List Bool) : machine.Config :=
  OuterCayleyQuery.entry P quotientBanks verdictBanks n x y prior parked (frame n identity cut)

def bit (state : Fin P.states) : Bool :=
  PrefixQuotientVerdict.answer ⟨state, 0, fun _ => 0, fun _ _ => none, []⟩

private theorem answer_state (d : P.Config) : bit d.state = PrefixQuotientVerdict.answer d := rfl

private theorem out₉ : (9 : Fin 11) ∉ Set.range quotientBanks := by
  rintro ⟨i, hi⟩
  have h := congrArg (fun t : Fin 11 => t.val) hi
  change i.val = 9 at h
  have := i.isLt
  change i.val < 9 at this
  omega

private theorem out₁₀ : (10 : Fin 11) ∉ Set.range quotientBanks := by
  rintro ⟨i, hi⟩
  have h := congrArg (fun t : Fin 11 => t.val) hi
  change i.val = 10 at h
  have := i.isLt
  change i.val < 9 at this
  omega

private theorem config_eq {M : SearchTransducer} (c d : M.Config)
    (state : c.state = d.state) (input : c.inputHead = d.inputHead)
    (heads : c.workHead = d.workHead) (cells : c.workCell = d.workCell)
    (output : c.outputReversed = d.outputReversed) : c = d := by
  cases c
  cases d
  simp_all

/-- On prepared oriented endpoints, the inner prefix adjacency call reads the
actual Cayley table and returns an exact bit, including the identity edge. -/
theorem execute {n : Nat} (G : Group (Fin n)) (x y : Fin n) (cut : Nat)
    (hcut : cut ≤ n) (prior : List Bool) :
    let raw := @encodeCayley n G.toMul
    let B := 3 * (Nat.log2 (raw.length + 1) + 1)
    ∃ (k : Nat) (v : Fin P.states) (d : machine.Config),
      machine.BoundedSegment raw B (entry n x.val y.val G.toOne.one.val cut prior) d k ∧
      machine.step raw d = none ∧ d.state = Fin.natAdd solver.states v ∧
      (bit v = true ↔ difference G x y = G.toOne.one ∨ (difference G x y).val < cut) ∧
      d.outputReversed = prior := by
  let raw := @encodeCayley n G.toMul
  let B := 3 * (Nat.log2 (raw.length + 1) + 1)
  let w := TableIO.width n
  let a := (difference G x y).val
  let id := G.toOne.one.val
  let accept : Fin n → Bool := fun z => decide (z.val = id ∨ z.val < cut)
  have nraw : n ≤ raw.length := by
    change n ≤ (@encodeCayley n G.toMul).length
    rw [@length_encodeCayley n G.toMul]
    omega
  have lo : n.log2 ≤ (raw.length + 1).log2 :=
    (Nat.le_log2 (by omega)).2 ((Nat.log2_self_le (by have := x.isLt; omega)).trans (by omega))
  have wB : w + 1 ≤ B := by dsimp [w, TableIO.width, B]; omega
  have fits : n < 2^w := Nat.lt_log2_self
  obtain ⟨k, v, d, run, halt, state, test, output, _⟩ :=
    OuterCayleyQuery.execute G x y P quotientBanks verdictBanks 0 rfl bit accept prior parked
      (frame n id cut) B le_rfl (by simp [parked]) (by
    dsimp only
    intro c hc hstate hout unchanged hhead hlabel
    set l := PrefixQuotientVerdict.labels w a id cut
    let p := PrefixQuotientVerdict.start c.inputHead prior l
    obtain ⟨t, e, walk, stop, eq, _, prints, _⟩ :=
      PrefixQuotientVerdict.execute raw prior c.inputHead w a id cut ⟨hc.1,hc.2.1⟩
        ((difference G x y).isLt.trans fits) (G.toOne.one.isLt.trans fits) (hcut.trans_lt fits)
    let unpacked := P.bankConfig verdictBanks p c.workHead c.workCell
    have cells : unpacked.workCell = c.workCell := by
      funext i
      by_cases h : i ∈ Set.range verdictBanks
      · obtain ⟨j,rfl⟩ := h
        rw [show unpacked.workCell (verdictBanks j) = p.workCell j from
          P.bankConfig_cell_image verdictBanks p c.workHead c.workCell j]
        fin_cases j
        · exact hlabel.symm
        · exact ((unchanged 9 out₉).2).symm
        · exact ((unchanged 10 out₁₀).2).symm
      · exact (P.bankConfig_frame verdictBanks p c.workHead c.workCell h).2
    have heads : unpacked.workHead = c.workHead := by
      funext i
      by_cases h : i ∈ Set.range verdictBanks
      · obtain ⟨j,rfl⟩ := h
        rw [show unpacked.workHead (verdictBanks j) = 0 from
          P.bankConfig_head_image verdictBanks p c.workHead c.workCell j]
        fin_cases j
        · exact hhead.symm
        · exact ((unchanged 9 out₉).1).symm
        · exact ((unchanged 10 out₁₀).1).symm
      · exact (P.bankConfig_frame verdictBanks p c.workHead c.workCell h).1
    have start : unpacked = c := by
      have hinit : unpacked.state = c.state := hstate.symm
      have hOut : unpacked.outputReversed = c.outputReversed := hout.symm
      have hInput : unpacked.inputHead = c.inputHead := rfl
      exact config_eq _ _ hinit hInput heads cells hOut
    let last := P.bankConfig verdictBanks e c.workHead c.workCell
    have move : (P.relocateBanks verdictBanks).BoundedSegment raw B unpacked last t :=
      P.relocateBanks_segment verdictBanks (PhysicalEntry.segment_mono walk wB) (fun i _ => hc.2.2 i)
    rw [start] at move
    refine ⟨t, last, move, ?_, ?_, prints.trans hout.symm, ?_⟩
    · unfold last
      rw [relocateBanks_step, stop]
      rfl
    · apply Bool.eq_iff_iff.mpr
      rw [show bit last.state = PrefixQuotientVerdict.answer e from answer_state e]
      exact eq.trans (by simp [accept, a])
    · intro i h
      exact P.bankConfig_frame verdictBanks e c.workHead c.workCell h)
  refine ⟨k, v, d, run, halt, state, ?_, output⟩
  rw [test]
  simp [accept, id, Fin.ext_iff]

end Mathproof.MinimumGeneration.CayleyPrefixLeaf
