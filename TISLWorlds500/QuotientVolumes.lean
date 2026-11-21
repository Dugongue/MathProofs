import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

namespace QuotientVolumes

theorem volume_covariance {F : Type*} [Field F]
    (a b c sourceFrame targetFrame sourceForm targetForm scale : F)
    (hs : sourceFrame ≠ 0) (ht : targetFrame ≠ 0) (hc : c ≠ 0)
    (hframe : a * b * c * targetFrame = sourceFrame)
    (hform : sourceForm = scale * b * targetForm) :
    a * (sourceForm / sourceFrame) = (scale * targetForm) / (c * targetFrame) := by
  rw [← mul_div_assoc, hform]
  apply (div_eq_div_iff hs (mul_ne_zero hc ht)).2
  linear_combination (scale * targetForm) * hframe

theorem corrected_projective_mark {F : Type*} [Field F]
    (a b c sourceFrame targetFrame sourceForm targetForm scale : F)
    (hs : sourceFrame ≠ 0) (ht : targetFrame ≠ 0) (hc : c ≠ 0) (he : scale ≠ 0)
    (hframe : a * b * c * targetFrame = sourceFrame)
    (hform : sourceForm = scale * b * targetForm) :
    (a * (sourceForm / sourceFrame)) / scale = targetForm / (c * targetFrame) := by
  rw [volume_covariance a b c sourceFrame targetFrame sourceForm targetForm scale
    hs ht hc hframe hform]
  field_simp

end QuotientVolumes
