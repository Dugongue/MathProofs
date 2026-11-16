import Mathproof.MinimumGenerationCayleyQueryDispatch
import Mathproof.MinimumGenerationTapeInstall

namespace Mathproof.MinimumGeneration.CayleyQueryDispatch

open InputPosition (work)
open SearchTransducer

private theorem length_label (w x : ℕ) : (encodeLabel w x).length = w := by simp [encodeLabel]

private theorem peek_label {w x k : ℕ} (h : k < w) :
    (encodeLabel w x)[k]? = some (x.testBit k) := by
  simp [encodeLabel, List.getElem?_eq_getElem (by simpa using h : k < (List.range w).length),
    List.getElem_range]

private theorem at_label_in (v w x : ℕ) (hvw : v ≤ w) (p : Int)
    (lo : 1 ≤ p) (hi : p ≤ (v : Int)) :
    work (encodeLabel w x) p = work (encodeLabel v x) p := by
  unfold work
  have nz : ¬ p ≤ 0 := by omega
  rw [if_neg nz, if_neg nz]
  have low : (p - 1).toNat < v := by omega
  exact (peek_label (low.trans_le hvw)).trans (peek_label low).symm

private theorem at_label_out (v x : ℕ) (p : Int) (outside : p < 1 ∨ (v : Int) < p) :
    work (encodeLabel v x) p = none := by
  unfold work
  by_cases h : p ≤ 0
  · simp [h]
  · rw [if_neg h]
    apply List.getElem?_eq_none
    rw [length_label]
    omega

/-- A physical installation sweep copies a normalized virtual endpoint onto
its exact raw-width register. The source may be a wider virtual coordinate. -/
theorem installedLabel {W v w x : ℕ} (copy : Fin W → Option (Fin W))
    (cells : Fin W → Int → Option Bool) (dst src : Fin W) (hvw : v ≤ w)
    (read : cells src = work (encodeLabel w x)) (mapped : copy dst = some src)
    (outside : ∀ p, p < 1 ∨ (v : Int) < p → cells dst p = none) :
    TapeInstall.installed copy cells v dst = work (encodeLabel v x) := by
  funext p
  unfold TapeInstall.installed
  by_cases hp : 1 ≤ p ∧ p ≤ (v : Int)
  · rw [if_pos hp, mapped, Option.elim_some, read]
    exact at_label_in v w x hvw p hp.1 hp.2
  · have hOut : p < 1 ∨ (v : Int) < p := by omega
    rw [if_neg hp, outside p hOut, at_label_out v x p hOut]

/-- Read two selected endpoint banks and install their low bits in the exact
raw label width, without writing either original bank. -/
theorem executeEndpointInstall {W v w x y : ℕ} (clock dstX dstY srcX srcY : Fin W)
    (copy : Fin W → Option (Fin W)) (clockFixed : copy clock = none)
    (word tick prior : List Bool) (park : Int) (cells : Fin W → Int → Option Bool)
    (hvw : v ≤ w) (clockWidth : tick.length = v) (clockWord : cells clock = work tick)
    (hx : cells srcX = work (encodeLabel w x)) (hy : cells srcY = work (encodeLabel w y))
    (copyX : copy dstX = some srcX) (copyY : copy dstY = some srcY)
    (fixedX : copy srcX = none) (fixedY : copy srcY = none)
    (outX : ∀ p, p < 1 ∨ (v : Int) < p → cells dstX p = none)
    (outY : ∀ p, p < 1 ∨ (v : Int) < p → cells dstY p = none)
    (hPark : (-1 : Int) ≤ park ∧ park ≤ word.length) :
    let P := TapeInstall.machine clock copy
    let finish := TapeInstall.stop clock copy park cells prior v
    P.BoundedSegment word (v + 1) (TapeInstall.start clock copy park cells prior) finish
      (v + 2 + v + 1) ∧ P.step word finish = none ∧
    finish.workCell dstX = work (encodeLabel v x) ∧
    finish.workCell dstY = work (encodeLabel v y) ∧
    finish.workCell srcX = cells srcX ∧ finish.workCell srcY = cells srcY ∧
    finish.inputHead = park ∧ finish.outputReversed = prior ∧ (∀ j, finish.workHead j = 0) := by
  obtain ⟨run, halt⟩ :=
    TapeInstall.execute clock copy clockFixed word tick prior park cells clockWord hPark
  rw [clockWidth] at run halt
  exact ⟨run, halt, installedLabel copy cells dstX srcX hvw hx copyX outX,
    installedLabel copy cells dstY srcY hvw hy copyY outY,
    TapeInstall.installed_source copy cells v srcX fixedX,
    TapeInstall.installed_source copy cells v srcY fixedY, rfl, rfl, fun _ => rfl⟩

end Mathproof.MinimumGeneration.CayleyQueryDispatch
