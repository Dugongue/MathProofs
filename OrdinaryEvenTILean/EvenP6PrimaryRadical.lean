import EvenP6PrimaryCoefficients
import Mathproof.Meta.P15FactorIMPRadMath20261007

namespace EvenTI.PrimaryProducer

open scoped Polynomial
open Polynomial Mathproof.P15FactorRef20261007 Mathproof.P15FactorIMP20261007
open EvenTI.Contract

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

theorem monicListLast {O : FOps K} (hO : Agree O)
    {f : List K} (hn : Norm f) (hm : (toPoly f).Monic) :
    f ≠ [] ∧ lastL O f = 1 := by
  have he : f ≠ [] := by
    intro h
    exact hm.ne_zero (by simp [h, toPoly])
  refine ⟨he, ?_⟩
  rw [lastL_eq hO he, ← (norm_props hn he).2.2]
  exact hm.leadingCoeff

/-- The checked P15 radical update, evaluated on lists in characteristic
two as well as in odd characteristic. -/
def radicalRound (O : FOps K) (f : List K) (d : ℕ) (r : List K) : List K :=
  let x := [O.zero, O.one]
  let q := gcdL O f (subL O (powModL O x (O.card ^ d) f) x)
  let g := gcdL O r q
  mulL O r (divModL O g q).1

theorem radicalRound_spec {O : FOps K} (hO : Agree O) {f r : List K} {d : ℕ}
    (hn : Norm f) (hm : (toPoly f).Monic) (hr : RInv (toPoly f) (toPoly r) d) :
    RInv (toPoly f) (toPoly (radicalRound O f (d+1) r)) (d+1) := by
  let x := [O.zero, O.one]
  let z := powModL O x (O.card ^ (d+1)) f
  let q := gcdL O f (subL O z x)
  let g := gcdL O r q
  obtain ⟨hne,hlast⟩ := monicListLast hO hn hm
  have hx : toPoly x = (X : K[X]) := by simp [x, toPoly, hO.zero, hO.one]
  have hz : toPoly z = ((X : K[X]) ^ (Fintype.card K ^ (d+1))) %ₘ toPoly f := by
    rw [show z = powModL O x (O.card ^ (d+1)) f from rfl,
      (powModL_spec hO hn hlast hne _ _).1, hx, hO.card]
  have hq : toPoly q = gcd (toPoly f) (toPoly z - X) := by
    rw [show q = gcdL O f (subL O z x) from rfl, (gcdL_spec hO _ _).1, toPoly_subL hO, hx]
  obtain ⟨hg,hgn⟩ := gcdL_spec hO r q
  have hgm : (toPoly g).Monic := by
    rw [show g = gcdL O r q from rfl, hg]
    exact gcd_monic' hr.1.ne_zero
  obtain ⟨hg0,hg1⟩ := monicListLast hO hgn hgm
  have hdiv : toPoly (divModL O g q).1 = toPoly q / toPoly g := by
    rw [(divModL_spec hO hgn hg1 hg0 q).1, divByMonic_eq_div _ hgm]
  have hcong : toPoly f ∣ toPoly z - X ^ (Fintype.card K ^ (d+1)) := by
    rw [hz]
    exact dvd_modByMonic_sub _ _
  have hstep := rinv_step hm.ne_zero hr hcong
  change RInv (toPoly f) (toPoly (mulL O r (divModL O g q).1)) (d+1)
  rw [toPoly_mulL hO, hdiv, show toPoly g = gcd (toPoly r) (toPoly q) from hg, hq]
  exact hstep

def radicalRounds (O : FOps K) (f : List K) : ℕ → List K
  | 0 => [O.one]
  | d+1 => radicalRound O f (d+1) (radicalRounds O f d)

theorem radicalRounds_spec {O : FOps K} (hO : Agree O) (f : List K) (d : ℕ)
    (hn : Norm f) (hm : (toPoly f).Monic) :
    RInv (toPoly f) (toPoly (radicalRounds O f d)) d := by
  induction d with
  | zero =>
    simpa [radicalRounds, toPoly_one hO] using (rinv_zero (toPoly f))
  | succ d ih => exact radicalRound_spec hO hn hm ih

def radicalCoefficients (O : FOps K) (f : List K) : List K :=
  let input := trim O f
  trim O (radicalRounds O input (input.length-1))

theorem radicalCoefficients_spec {O : FOps K} (hO : Agree O) {f : List K}
    (hm : (toPoly f).Monic) :
    toPoly (radicalCoefficients O f) = radP (toPoly f) ∧ Norm (radicalCoefficients O f) := by
  let input := trim O f
  obtain ⟨hi,hin⟩ := trim_spec hO f
  have him : (toPoly input).Monic := by
    change (toPoly (trim O f)).Monic
    rwa [hi]
  have hr := radicalRounds_spec hO input (input.length-1) hin him
  have he := rinv_eq_radP him.ne_zero hr (natDegree_toPoly_le input)
  unfold radicalCoefficients
  refine ⟨?_, (trim_spec hO _).2⟩
  rw [(trim_spec hO _).1, he, hi]

#print axioms radicalCoefficients_spec

end EvenTI.PrimaryProducer
