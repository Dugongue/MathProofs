import Mathproof.MinimumGenerationCayleyQueryRouter
import Mathproof.MinimumGenerationCayleyPrefixEntryInstall

namespace Mathproof.MinimumGeneration.CayleyQueryPrefixModel

open SearchTransducer ReingoldLiveInput
open Connectivity (ustconHeaderLength ustconCell)
open InputPosition (work)

set_option backward.isDefEq.respectTransparency false

/-- The cross-side adjacency returned by the checked prefix leaf. -/
def edge {n : ℕ} (G : Group (Fin n)) (cut : ℕ) (x y : Fin n) : Bool :=
  decide (difference G x y = G.toOne.one ∨ (difference G x y).val < cut)

theorem bits {n : ℕ} (G : Group (Fin n)) (cut : ℕ) :
    CayleyQueryRouter.matrixBits (edge G cut) = BipartiteCayley.bits G (fun _ => true) cut := by
  funext a b
  unfold CayleyQueryRouter.matrixBits BipartiteCayley.bits
  cases h : BipartiteCayley.endpoints a b with
  | none => rfl
  | some e =>
    obtain ⟨x,y⟩ := e
    let _ : Group (Fin n) := G
    let _ : Mul (Fin n) := G.toMul
    let _ : Inv (Fin n) := G.toInv
    let _ : One (Fin n) := G.toOne
    have eq : difference G x y = G.toOne.one ↔ x = y := by
      change x⁻¹*y = 1 ↔ x = y
      exact inv_mul_eq_one
    apply Bool.eq_iff_iff.mpr
    simp [edge,eq]

def width (n : ℕ) : ℕ := 4 * TableIO.width n

def rawSpace (raw : List Bool) : ℕ := 5 * (Nat.log2 (raw.length + 1) + 1)

/-- The legal shifted addresses, both normalized matrix coordinates, and the
matrix size fit in four times the original element-label width. -/
theorem bounds {n : ℕ} (s t : Fin (n+n)) :
    ustconHeaderLength s t + (n+n)*(n+n) + 1 < 2 ^ width n ∧
    n+n < 2 ^ width n ∧ (n+n)*(n+n) ≤ 2 ^ width n := by
  let v := TableIO.width n
  let q := 2 ^ v
  have fits : n < q := Nat.lt_log2_self
  have qge : 2 ≤ q := by
    show 2 ≤ 2 ^ (Nat.log2 n + 1)
    rw [pow_succ]
    have p : 0 < 2 ^ Nat.log2 n := Nat.two_pow_pos _
    omega
  have lo : ustconHeaderLength s t + (n+n)*(n+n) + 1 < 4 * (n+1)^2 := by
    unfold ustconHeaderLength
    have hs := s.isLt
    have ht := t.isLt
    nlinarith
  have h1 : 4 * (n+1)^2 ≤ 4*q^2 := Nat.mul_le_mul_left _
    (Nat.pow_le_pow_left (by omega) _)
  have h2 : 4*q^2 ≤ q^4 := by
    rw [show q^4=q^2*q^2 by ring]
    exact Nat.mul_le_mul_right _ (by
      rw [pow_two]
      exact Nat.mul_le_mul qge qge)
  have exp : (2^width n : ℕ) = q^4 := by
    change 2 ^ (4*v) = (2 ^ v)^4
    rw [Nat.mul_comm 4 v, pow_mul]
  have full := lo.trans_le (h1.trans h2)
  rw [← exp] at full
  have hs : 0 < n+n := s.isLt.pos
  have m2 : n+n ≤ (n+n)*(n+n) := by
    conv_lhs => rw [← Nat.mul_one (n+n)]
    exact Nat.mul_le_mul_left _ (by omega)
  exact ⟨full,by omega,by omega⟩

theorem width_le {n : ℕ} (G : Group (Fin n)) :
    width n + 1 ≤ rawSpace (@encodeCayley n G.toMul) := by
  let raw := @encodeCayley n G.toMul
  have hlength : n ≤ raw.length := by
    change n ≤ (@encodeCayley n G.toMul).length
    rw [@length_encodeCayley n G.toMul]
    omega
  have hlog : n.log2 ≤ (raw.length + 1).log2 := by
    apply (Nat.le_log2 (by omega)).2
    exact (Nat.log2_self_le (Nat.ne_of_gt G.toOne.one.isLt.pos)).trans (by omega)
  change width n + 1 ≤ rawSpace raw
  unfold width TableIO.width rawSpace
  omega

section FixedLayout

def coordBanks : Fin 10 ↪ Fin 35 :=
  ⟨Fin.castAdd 25, fun _ _ h => Fin.ext (congrArg (fun i : Fin 35 => i.val) h)⟩

def prefixBanks : Fin 18 ↪ Fin 35 :=
  ⟨fun i => ⟨10+i.val, by have := i.isLt; omega⟩,
    fun _ _ h => Fin.ext (Nat.add_left_cancel (congrArg (fun i : Fin 35 => i.val) h))⟩

def markerBank (i : Fin 5) : Fin 35 := ⟨28+i.val, by have := i.isLt; omega⟩

def addressBank : Fin 35 := 33
def headerBank : Fin 35 := 34

def guardBanks : Fin 2 ↪ Fin 35 where
  toFun i := if i = 0 then headerBank else 4
  inj' := by intro a b h; fin_cases a <;> fin_cases b <;> first | rfl | contradiction

def need : Set (Fin 35) := {j | 10 ≤ j.val ∧ j.val < 28}
def keep : Set (Fin 35) := {j | 21 ≤ j.val ∧ j.val ≠ 22 ∧ j.val ≠ 25}

/-- The exact prepared words for one physical call. The shadow address used
by the subtractor is bank four; bank 33 retains the original pointer. -/
def cells {n : ℕ} (G : Group (Fin n)) (cut : ℕ) (s t : Fin (n+n)) (p : ℕ)
    (j : Fin 35) : Int → Option Bool :=
  if h : j.val < 10 then CayleyQueryCoordinates.entryCells (width n) n p ⟨j.val,h⟩
  else if h : j.val < 28 then CayleyPrefixLeaf.template n 0 0 G.toOne.one.val cut
    ⟨j.val-10,by omega⟩
  else if h : j.val < 33 then
    work (encodeLabel (width n) (VirtualMarkerScan.boundaryAddresses s t ⟨j.val-28,by omega⟩))
  else if j = addressBank then work (encodeLabel (width n) p)
  else work (encodeLabel (width n) (ustconHeaderLength s t+1))

theorem cells_prefix {n : ℕ} (G : Group (Fin n)) (cut : ℕ) (s t : Fin (n+n)) (p : ℕ)
    (j : Fin 18) :
    cells G cut s t p (prefixBanks j) = CayleyPrefixLeaf.template n 0 0 G.toOne.one.val cut j := by
  unfold cells
  have eq : (prefixBanks j).val = 10+j.val := rfl
  have high : ¬ (prefixBanks j).val < 10 := by rw [eq]; omega
  have low : (prefixBanks j).val < 28 := by rw [eq]; have := j.isLt; omega
  rw [dif_neg high, dif_pos low]
  have index : (⟨(prefixBanks j).val-10,by have := j.isLt; omega⟩ : Fin 18) = j :=
    Fin.ext (by change (_ : ℕ) - _ = _; rw [eq]; omega)
  rw [index]

private theorem cells_marker {n : ℕ} (G : Group (Fin n)) (cut : ℕ) (s t : Fin (n+n)) (p : ℕ)
    (j : Fin 5) :
    cells G cut s t p (markerBank j) =
      work (encodeLabel (width n) (VirtualMarkerScan.boundaryAddresses s t j)) := by
  unfold cells
  have eq : (markerBank j).val = 28+j.val := rfl
  have a : ¬ (markerBank j).val < 10 := by rw [eq]; omega
  have b : ¬ (markerBank j).val < 28 := by rw [eq]; omega
  have c : (markerBank j).val < 33 := by rw [eq]; have := j.isLt; omega
  rw [dif_neg a, dif_neg b,dif_pos c]
  have index : (⟨(markerBank j).val-28,by have := j.isLt; omega⟩ : Fin 5) = j :=
    Fin.ext (by change (_ : ℕ) - _ = _; rw [eq]; omega)
  rw [index]

private theorem cells_coord {n : ℕ} (G : Group (Fin n)) (cut : ℕ) (s t : Fin (n+n)) (p : ℕ)
    (j : Fin 10) :
    cells G cut s t p (coordBanks j) = CayleyQueryCoordinates.entryCells (width n) n p j := by
  unfold cells
  have eq : (coordBanks j).val = j.val := rfl
  rw [dif_pos (by rw [eq]; exact j.isLt)]
  rfl

private theorem block_word (xs : List Bool) : TapeArithmetic.block (work xs) 1 xs := by
  intro i
  simp [work, show ¬ (1 + (i.val : Int) ≤ 0) by omega,
    show 1 + (i.val : Int) - 1 = (i.val : Int) by omega]

private theorem right_blank (w a : ℕ) : work (encodeLabel w a) ((w : Int)+1) = none := by
  simp [work, encodeLabel, show ¬ ((w : Int) + 1 ≤ 0) by omega]

private theorem markerFitAll {n : ℕ} (s t : Fin (n+n)) (i : Fin 5) :
    VirtualMarkerScan.boundaryAddresses s t i < 2 ^ width n := by
  have total := (bounds s t).1
  fin_cases i <;> simp [VirtualMarkerScan.boundaryAddresses] at * <;> unfold ustconHeaderLength at * <;> omega

private theorem disjoint : ∀ j ∈ need ∪ keep, j ∉ Set.range coordBanks := by
  intro j mem
  rintro ⟨u,rfl⟩
  have hlt := u.isLt
  change (10 ≤ u.val ∧ u.val < 28) ∨ (21 ≤ u.val ∧ u.val ≠ 22 ∧ u.val ≠ 25) at mem
  omega

private theorem preparedLayout {n : ℕ} (G : Group (Fin n)) (cut : ℕ) (s t : Fin (n+n)) (p : ℕ)
    (addr : p ≤ ustconHeaderLength s t + (n+n)*(n+n) + 1) :
    let raw := @encodeCayley n G.toMul
    VirtualMarkerScan.Layout addressBank markerBank raw (rawSpace raw) (width n) p
      (VirtualMarkerScan.boundaryAddresses s t) (↑(n+1 : ℕ) : Int) (fun _ => 0) (cells G cut s t p) := by
  let raw := @encodeCayley n G.toMul
  have hlen : n+1 ≤ raw.length := by
    change n+1 ≤ (@encodeCayley n G.toMul).length
    rw [@length_encodeCayley n G.toMul]
    omega
  refine ⟨addr.trans_lt (bounds s t).1, markerFitAll s t, ⟨by omega, by exact_mod_cast hlen⟩,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j z lo hi
    have cap := width_le G
    simp only [TapeRegisters.finish, Int.zero_add] at hi
    split at hi <;> omega
  · change TapeArithmetic.block (work (encodeLabel (width n) p)) 1 _
    exact block_word _
  · rw [Int.zero_add]
    change work (encodeLabel (width n) p) ((width n : Int)+1) = none
    exact right_blank _ _
  · intro i
    rw [cells_marker G cut s t p i]
    exact block_word _
  · intro i
    rw [cells_marker G cut s t p i]
    rfl
  · intro i
    rw [cells_marker G cut s t p i]
    rw [Int.zero_add]
    exact right_blank _ _

/-- Execute the prefix Cayley reader in the fixed 35-bank layout. The
cross-side port supplies the already prepared physical prefix leaf. -/
theorem execute {S : ℕ} (cross : CayleyQueryRouter.CrossBranch S 35)
    (fit : CayleyQueryCoordinates.machine.states ≤ S) {n : ℕ}
    (G : Group (Fin n)) (cut : ℕ) (s t : Fin (n+n)) (p : ℕ) (prior : List Bool)
    (addr : p ≤ ustconHeaderLength s t + (n+n)*(n+n) + 1)
    (ports :
      let raw := @encodeCayley n G.toMul
      CayleyQueryRouter.CrossPort addressBank markerBank guardBanks coordBanks cross fit
        (edge G cut) raw prior (width n) (rawSpace raw) (↑(n+1 : ℕ) : Int) need keep (cells G cut s t p)) :
    let raw := @encodeCayley n G.toMul
    let M := CayleyQueryRouter.machine addressBank markerBank guardBanks coordBanks cross fit
    ∃ k d, M.BoundedSegment raw (rawSpace raw)
        (CayleyQueryRouter.start addressBank markerBank guardBanks coordBanks cross fit
          (↑(n+1 : ℕ) : Int) (cells G cut s t p) prior) d k ∧
      M.step raw d = none ∧
      CayleyQueryRouter.result addressBank markerBank guardBanks coordBanks cross fit d.state =
        ustconCell (BipartiteCayley.bits G (fun _ => true) cut) s t ((p : Int)-1) ∧
      d.outputReversed = prior ∧ ∀ j ∈ keep, d.workHead j = 0 ∧ d.workCell j = cells G cut s t p j := by
  obtain ⟨_,mfit,matrixFit⟩ := bounds s t
  simpa only [bits G cut] using
    CayleyQueryRouter.execute addressBank markerBank guardBanks coordBanks cross fit
      (edge G cut) s t (preparedLayout G cut s t p addr) (width_le G) addr
      mfit matrixFit (by rfl) (by rfl) (cells_coord G cut s t p) need keep disjoint ports

end FixedLayout

end Mathproof.MinimumGeneration.CayleyQueryPrefixModel
