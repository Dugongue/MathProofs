import Mathproof.MinimumGenerationCayleyQueryPrefixModel
import Mathproof.MinimumGenerationCayleyPrefixFromEndpoints

namespace Mathproof.MinimumGeneration.CayleyQueryPrefix

open SearchTransducer
open InputPosition (work)
open CayleyQueryPrefixModel
open CayleyPrefixLeaf (template crossStart endpointsMachine endpointsStart EndpointTemplates executeFromEndpoints)

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def leftBank (ab : Fin 5 × Fin 5) : Fin 35 := coordBanks (CayleyQueryCoordinates.slot ab.1)
def rightBank (ab : Fin 5 × Fin 5) : Fin 35 := coordBanks (CayleyQueryCoordinates.slot ab.2)

abbrev leaf (ab : Fin 5 × Fin 5) := CayleyPrefixLeaf.crossMachine prefixBanks (leftBank ab) (rightBank ab)

def states : ℕ := 105 + (leaf (0,0)).states

theorem fit : CayleyQueryCoordinates.machine.states ≤ states := by
  change 105 ≤ 105 + (leaf (0,0)).states
  omega

private theorem padFit (ab : Fin 5 × Fin 5) : (leaf ab).states ≤ states := by
  change (leaf (0,0)).states ≤ 105 + (leaf (0,0)).states
  omega

private def sameBanks : Fin 35 ↪ Fin 35 := Function.Embedding.refl _

/-- The physically executable cross-side branches, indexed by the selected
source banks. Each branch contains both width copies and the raw table leaf. -/
abbrev cross : CayleyQueryRouter.CrossBranch states 35 where
  entry ab := (leaf ab).initialState.castLE (padFit ab)
  transition ab := (leaf ab).padTransition (padFit ab) sameBanks
  answer ab q := if h : q.val < (leaf ab).states then
    CayleyPrefixLeaf.crossBit prefixBanks (leftBank ab) (rightBank ab) ⟨q.val,h⟩ else false

private theorem crossAnswer (ab : Fin 5 × Fin 5) (q : Fin (leaf ab).states) :
    cross.answer ab (q.castLE (padFit ab)) = CayleyPrefixLeaf.crossBit prefixBanks
      (leftBank ab) (rightBank ab) q := by
  simp only [Fin.val_castLE, dif_pos q.isLt, Fin.eta]

private theorem cfgEq {P : SearchTransducer} (c d : P.Config)
    (s : c.state = d.state) (i : c.inputHead = d.inputHead) (h : c.workHead = d.workHead)
    (t : c.workCell = d.workCell) (o : c.outputReversed = d.outputReversed) : c = d := by
  cases c
  cases d
  simp_all

private theorem rankHigh (i : Fin 18) : (prefixBanks i).val = 10+i.val := rfl

private theorem externalRight (ab : Fin 5 × Fin 5) : rightBank ab ≠ prefixBanks 12 := by
  intro eq
  have e := congrArg (fun i : Fin 35 => i.val) eq
  have l := (CayleyQueryCoordinates.slot ab.2).isLt
  change (CayleyQueryCoordinates.slot ab.2).val = 22 at e
  omega

private theorem markOutside {xs : List Bool} {width : ℕ} (hlen : xs.length ≤ width)
    (p : Int) (outside : p < 1 ∨ (width : Int) < p) : work xs p = none := by
  unfold work
  by_cases h : p ≤ 0
  · simp [h]
  · rw [if_neg h]
    apply List.getElem?_eq_none
    omega

private theorem immTemplate (n x y id cut : ℕ) (i : Fin 18)
    (row : i ≠ 12) (col : i ≠ 15) :
    template n 0 0 id cut i = template n x y id cut i := by
  simp only [template, if_neg row, if_neg col]

private theorem lowTemplate (n id cut : ℕ) (i : Fin 18) (h : i.val < 11) :
    template n 0 0 id cut i = fun _ => none := by
  fin_cases i <;> first | rfl | (simp at h)

private theorem dark {n : ℕ} (G : Group (Fin n)) (cut : ℕ) (s t : Fin (n+n)) (p : ℕ)
    {current : Fin 35 → Int → Option Bool}
    (holds : ∀ j ∈ need ∪ keep, current j = cells G cut s t p j) (j : Fin 18) :
    current (prefixBanks j) = template n 0 0 G.toOne.one.val cut j := by
  have hj : prefixBanks j ∈ need := by
    change 10 ≤ (prefixBanks j).val ∧ (prefixBanks j).val < 28
    rw [rankHigh]
    have := j.isLt
    omega
  exact (holds _ (.inl hj)).trans (cells_prefix G cut s t p j)

private theorem workShape (ab : Fin 5 × Fin 5) (n : ℕ)
    (cells : Fin 35 → Int → Option Bool) (prior : List Bool) (j : Fin 35) :
    let c := crossStart prefixBanks (leftBank ab) (rightBank ab) n cells prior
    c.workHead j = 0 ∧ c.workCell j = cells j := by
  let A := endpointsMachine prefixBanks (leftBank ab) (rightBank ab)
  let c := endpointsStart prefixBanks (leftBank ab) (rightBank ab) n cells prior
  have a : (A.bankConfig sameBanks c c.workHead c.workCell).workHead j = c.workHead j :=
    bankConfig_head_image A sameBanks c c.workHead c.workCell j
  have b : (A.bankConfig sameBanks c c.workHead c.workCell).workCell j = c.workCell j :=
    bankConfig_cell_image A sameBanks c c.workHead c.workCell j
  change (A.bankConfig sameBanks c c.workHead c.workCell).workHead j = 0 ∧
      (A.bankConfig sameBanks c c.workHead c.workCell).workCell j = cells j
  rw [a,b]
  let Row := TapeInstall.machine (prefixBanks 11)
    (fun i => if i = prefixBanks 12 then some (leftBank ab) else none)
  let c₀ := TapeInstall.start (prefixBanks 11)
    (fun i => if i = prefixBanks 12 then some (leftBank ab) else none) (↑(n+1 : ℕ) : Int) cells prior
  exact ⟨bankConfig_head_image Row sameBanks c₀ c₀.workHead c₀.workCell j,
    bankConfig_cell_image Row sameBanks c₀ c₀.workHead c₀.workCell j⟩

/-- All oriented branch contracts are discharged by the actual copy and
Cayley-table machines in the fixed physical layout. -/
theorem port {n : ℕ} (G : Group (Fin n)) (cut : ℕ) (hCut : cut ≤ n)
    (s t : Fin (n+n)) (p : ℕ) (prior : List Bool) :
    let raw := @encodeCayley n G.toMul
    CayleyQueryRouter.CrossPort addressBank markerBank guardBanks coordBanks cross fit
      (edge G cut) raw prior (width n) (rawSpace raw) (↑(n+1 : ℕ) : Int) need keep (cells G cut s t p) := by
  unfold CayleyQueryRouter.CrossPort
  dsimp only
  intro ab
  intro x y c cs ci co ch cx cy hold
  let T := CayleyQueryRouter.stages addressBank markerBank guardBanks coordBanks cross fit
  change c.state = T.entry (CayleyQueryRouter.fork ab) at cs
  rw [CayleyQueryRouter.crossEntry addressBank markerBank guardBanks coordBanks cross fit ab] at cs
  let L := CayleyQueryRouter.liftCross addressBank markerBank guardBanks coordBanks cross fit ab
  let P := leaf ab
  let left := leftBank ab
  let right := rightBank ab
  let layout := cells G cut s t p
  let raw := @encodeCayley n G.toMul
  let C := rawSpace raw
  have know := dark G cut s t p hold
  have holdTemplate : EndpointTemplates prefixBanks left right n x.val y.val G.toOne.one.val cut
      (width n) c.workCell := by
    refine ⟨by unfold width; omega,cx,cy,externalRight ab,?_,?_,?_,?_⟩
    · intro i _ hr hc
      exact (know i).trans (immTemplate n x.val y.val G.toOne.one.val cut i hr hc)
    · intro z hz
      rw [know 12]
      change work (encodeLabel (2*TableIO.width n) 0) z = none
      exact markOutside (by simp [encodeLabel]) z hz
    · intro z hz
      rw [know 15]
      change work (encodeLabel (TableIO.width n) 0) z = none
      exact markOutside (by simp [encodeLabel]) z hz
    · intro i h z _
      rw [know i, lowTemplate n G.toOne.one.val cut i h]
  have copyCap : 2 * TableIO.width n + 1 ≤ C := by
    change 2 * TableIO.width n + 1 ≤ rawSpace (@encodeCayley n G.toMul)
    have h := width_le G
    unfold width at h
    omega
  have queryCap : 3 * (Nat.log2 (raw.length + 1) + 1) ≤ C := by
    unfold C rawSpace
    omega
  obtain ⟨k,d,run,halt,bit,printed,external,internal⟩ :=
    executeFromEndpoints prefixBanks left right G x y cut (width n) C hCut prior c.workCell
      holdTemplate copyCap queryCap
  let start := crossStart prefixBanks left right n c.workCell prior
  let a := P.padConfig (padFit ab) sameBanks (P.bankConfig sameBanks start c.workHead c.workCell)
  let b := P.padConfig (padFit ab) sameBanks (P.bankConfig sameBanks d c.workHead c.workCell)
  have entry : c = L a := by
    refine cfgEq c (L a) cs ci ?_ ?_ co
    · funext j
      change c.workHead j = (P.bankConfig sameBanks start c.workHead c.workCell).workHead j
      rw [show (P.bankConfig sameBanks start c.workHead c.workCell).workHead j = start.workHead j
        from bankConfig_head_image P sameBanks start c.workHead c.workCell j]
      exact (ch j).trans ((workShape ab n c.workCell prior j).1.symm)
    · funext j
      change c.workCell j = (P.bankConfig sameBanks start c.workHead c.workCell).workCell j
      exact ((bankConfig_cell_image P sameBanks start c.workHead c.workCell j).trans
        (workShape ab n c.workCell prior j).2).symm
  have lift := relocateBanks_segment P sameBanks (heads := c.workHead) (cells := c.workCell) run
    (fun j _ => by rw [ch]; exact Nat.zero_le _)
  have seg := P.padMachine_segment (padFit ab) sameBanks lift
  have terminates := relocateBanks_step P sameBanks raw d c.workHead c.workCell
  rw [halt] at terminates
  have paddedExit := P.padMachine_step (padFit ab) sameBanks raw (P.bankConfig sameBanks d c.workHead c.workCell)
  have hs : (cross.machine ab).step raw b = none := paddedExit.trans (congrArg _ terminates)
  have outBit : cross.answer ab b.state = edge G cut x y := by
    change cross.answer ab (d.state.castLE (padFit ab)) = _
    rw [crossAnswer]
    apply Bool.eq_iff_iff.mpr
    simpa [edge] using bit
  have route := CayleyQueryRouter.liftCross_segment addressBank markerBank guardBanks coordBanks cross fit ab seg
  have done := CayleyQueryRouter.liftCross_step addressBank markerBank guardBanks coordBanks cross fit ab raw b
  rw [hs] at done
  change (T.component (CayleyQueryRouter.fork ab)).BoundedSegment raw C (L a) (L b) k at route
  rw [← entry] at route
  refine ⟨k,L b,route,done,outBit,printed,?_⟩
  intro j hj
  have fixed : d.workHead j = 0 ∧ d.workCell j = c.workCell j := by
    by_cases h : j ∈ Set.range prefixBanks
    · obtain ⟨i,rfl⟩ := h
      change 21 ≤ (prefixBanks i).val ∧ (prefixBanks i).val ≠ 22 ∧
        (prefixBanks i).val ≠ 25 at hj
      rw [rankHigh] at hj
      exact internal i (by omega) (fun z => by subst i; omega) (fun z => by subst i; omega)
    · exact external j h
  exact ⟨(bankConfig_head_image P sameBanks d c.workHead c.workCell j).trans fixed.1,
    (bankConfig_cell_image P sameBanks d c.workHead c.workCell j).trans
      (fixed.2.trans (hold j (.inr hj)))⟩

abbrev machine := CayleyQueryRouter.machine addressBank markerBank guardBanks coordBanks cross fit

abbrev callback := CayleyQueryRouter.callback addressBank markerBank guardBanks coordBanks cross fit

/-- Complete physical prefix-Cayley read, from any legal shifted virtual
address on the prepared fixed layout. No adjacency callback is assumed. -/
theorem execute {n : ℕ} (G : Group (Fin n)) (cut : ℕ) (hCut : cut ≤ n)
    (s t : Fin (n+n)) (p : ℕ) (prior : List Bool)
    (legal : p ≤ Connectivity.ustconHeaderLength s t + (n+n)*(n+n) + 1) :
    let raw := @encodeCayley n G.toMul
    ∃ k d, machine.BoundedSegment raw (rawSpace raw)
        (CayleyQueryRouter.start addressBank markerBank guardBanks coordBanks cross fit
          (↑(n+1 : ℕ) : Int) (cells G cut s t p) prior) d k ∧
      machine.step raw d = none ∧
      callback.returnCell d.state =
        Connectivity.ustconCell (BipartiteCayley.bits G (fun _ => true) cut) s t ((p : Int)-1) ∧
      d.outputReversed = prior ∧ ∀ j ∈ keep, d.workHead j = 0 ∧ d.workCell j = cells G cut s t p j :=
  CayleyQueryPrefixModel.execute cross fit G cut s t p prior legal (port G cut hCut s t p prior)

end Mathproof.MinimumGeneration.CayleyQueryPrefix
