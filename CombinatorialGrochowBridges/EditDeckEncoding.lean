import Mathlib.Algebra.Polynomial.Roots

namespace EditDeckEncoding

theorem root_product_eq_iff {R : Type*} [CommRing R] [IsDomain R]
    (s t : Multiset R) :
    (s.map (fun a => Polynomial.X - Polynomial.C a)).prod =
      (t.map (fun a => Polynomial.X - Polynomial.C a)).prod ↔ s = t := by
  constructor
  · intro h
    simpa only [Polynomial.roots_multiset_prod_X_sub_C] using congrArg Polynomial.roots h
  · rintro rfl
    rfl

end EditDeckEncoding
