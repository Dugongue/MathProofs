import EvenNextQuadraticCovariance

/-! Characteristic polynomials of the literal enlarged singular cuts. -/
namespace Mathproof.EvenOrdinaryTISingular.EnlargedCut

open scoped BigOperators
open Matrix Polynomial EvenTI.AnchorCovariance

variable {K : Type*} [Field K] {a b k m : ℕ}

abbrev Index (a k : ℕ) := Fin k ⊕ (Fin a ⊕ Fin k)
def live : Fin a → Index a k := Sum.inr ∘ Sum.inl

def allowed : Index a k → Index a k → Prop
  | .inl _, .inl _ => False
  | .inl _, .inr _ => True
  | .inr (.inl _), .inr _ => True
  | _, _ => False

theorem allowed_trans {i j l : Index a k} (h : allowed i j) (g : allowed j l) :
    allowed i l := by
  rcases i with i | (i | i) <;> rcases j with j | (j | j) <;>
    rcases l with l | (l | l) <;> simp_all [allowed]

theorem live_only {i l : Fin a} {j : Index a k}
    (h : allowed (live i) j) (g : allowed j (live l)) :
    ∃ u, live u = j := by
  rcases j with j | (j | j)
  · exact False.elim h
  · exact ⟨j,rfl⟩
  · exact False.elim g

def Supported (M : Matrix (Index a k) (Index a k) K) : Prop :=
  ∀ i j, ¬ allowed i j → M i j = 0

def PairSupported (Z : Matrix (Index a k × Index b m) (Index a k × Index b m) K) : Prop :=
  ∀ i j, ¬ (allowed i.1 j.1 ∧ allowed i.2 j.2) → Z i j = 0

def crop (Z : Matrix (Index a k × Index b m) (Index a k × Index b m) K) :
    Matrix (Fin a × Fin b) (Fin a × Fin b) K :=
  Z.submatrix (Prod.map live live) (Prod.map live live)

theorem supported_mul
    {Z W : Matrix (Index a k × Index b m) (Index a k × Index b m) K}
    (hZ : PairSupported Z) (hW : PairSupported W) : PairSupported (Z * W) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro s hs
  by_cases h : allowed i.1 s.1 ∧ allowed i.2 s.2
  · rw [hW _ _ (fun g => hij ⟨allowed_trans h.1 g.1, allowed_trans h.2 g.2⟩), mul_zero]
  · rw [hZ _ _ h, zero_mul]

theorem crop_mul
    {Z W : Matrix (Index a k × Index b m) (Index a k × Index b m) K}
    (hZ : PairSupported Z) (hW : PairSupported W) :
    crop (Z * W) = crop Z * crop W := by
  classical
  ext i j
  let e : (Fin a × Fin b) ↪ (Index a k × Index b m) :=
    ⟨fun p => (live p.1, live p.2), fun x y h => Prod.ext
      (Sum.inl.inj (Sum.inr.inj (congrArg Prod.fst h)))
      (Sum.inl.inj (Sum.inr.inj (congrArg Prod.snd h)))⟩
  let g (x : Index a k × Index b m) : K :=
    Z (e i) x * W x (e j)
  change (∑ x, g x) = ∑ p, g (e p)
  rw [← Finset.sum_map Finset.univ e g]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro x _ hx
  by_cases hA : allowed (e i).1 x.1 ∧ allowed (e i).2 x.2
  · by_cases hB : allowed x.1 (e j).1 ∧ allowed x.2 (e j).2
    · obtain ⟨l,hl⟩ := live_only hA.1 hB.1
      obtain ⟨r,hr⟩ := live_only hA.2 hB.2
      exact (hx (Finset.mem_map.mpr ⟨(l,r), Finset.mem_univ _, Prod.ext hl hr⟩)).elim
    · exact (mul_eq_zero.mpr (Or.inr (hW _ _ hB)))
  · exact (mul_eq_zero.mpr (Or.inl (hZ _ _ hA)))

theorem supported_traceLeft
    {Z : Matrix (Index a k × Index b m) (Index a k × Index b m) K}
    (hZ : PairSupported Z) : Supported (partialTraceLeft Z) := by
  intro i j h
  change (∑ s, Z (i,s) (j,s)) = 0
  exact Finset.sum_eq_zero (fun s _ => hZ _ _ (fun g => h g.1))

theorem supported_traceRight
    {Z : Matrix (Index a k × Index b m) (Index a k × Index b m) K}
    (hZ : PairSupported Z) : Supported (partialTraceRight Z) := by
  intro i j h
  change (∑ s, Z (s,i) (s,j)) = 0
  exact Finset.sum_eq_zero (fun s _ => hZ _ _ (fun g => h g.2))

theorem crop_traceLeft
    {Z : Matrix (Index a k × Index b m) (Index a k × Index b m) K}
    (hZ : PairSupported Z) :
    (partialTraceLeft Z).submatrix live live = partialTraceLeft (crop Z) := by
  ext i j
  change (∑ s : Index b m, Z (live i,s) (live j,s)) = ∑ s : Fin b, Z (live i,live s) (live j,live s)
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  have hR (s : Fin m) : Z (live i, Sum.inl s) (live j, Sum.inl s) = 0 :=
    hZ _ _ (fun h => h.2.elim)
  have hA (s : Fin m) : Z (live i, Sum.inr (Sum.inr s)) (live j, Sum.inr (Sum.inr s)) = 0 :=
    hZ _ _ (fun h => h.2.elim)
  simp only [live, Function.comp_def] at hR hA ⊢
  simp [hR,hA]

theorem crop_traceRight
    {Z : Matrix (Index a k × Index b m) (Index a k × Index b m) K}
    (hZ : PairSupported Z) :
    (partialTraceRight Z).submatrix live live = partialTraceRight (crop Z) := by
  ext i j
  change (∑ s : Index a k, Z (s,live i) (s,live j)) = ∑ s : Fin a, Z (live s,live i) (live s,live j)
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  have hR (s : Fin k) : Z (Sum.inl s, live i) (Sum.inl s, live j) = 0 :=
    hZ _ _ (fun h => h.1.elim)
  have hA (s : Fin k) : Z (Sum.inr (Sum.inr s), live i) (Sum.inr (Sum.inr s), live j) = 0 :=
    hZ _ _ (fun h => h.1.elim)
  simp only [live, Function.comp_def] at hR hA ⊢
  simp [hR,hA]

theorem charpoly_supported {M : Matrix (Index a k) (Index a k) K}
    (h : Supported M) :
    M.charpoly = Polynomial.X ^ (2*k) * (M.submatrix live live).charpoly := by
  have hBlock : M = Matrix.fromBlocks 0 (M.submatrix Sum.inl Sum.inr) 0
      (Matrix.fromBlocks (M.submatrix live live)
        (M.submatrix live (Sum.inr ∘ Sum.inr)) 0 0) := by
    ext i j
    rcases i with i | (i | i) <;> rcases j with j | (j | j) <;>
      first | rfl | exact h _ _ id
  conv_lhs => rw [hBlock]
  simp only [Matrix.charpoly_fromBlocks_zero₂₁, Matrix.charpoly_zero, Fintype.card_fin]
  rw [← mul_assoc, mul_comm (Polynomial.X ^ k) (M.submatrix live live).charpoly, mul_assoc,
    ← pow_add, ← two_mul, mul_comm]

/-- Both literal enlarged quadratic covariants have the live characteristic
polynomial with exactly twice the respective radical dimension as padding. -/
theorem quadratic_charpoly_padding
    (Z : Matrix (Index a k × Index b m) (Index a k × Index b m) K)
    (hZ : PairSupported Z) :
    (partialTraceLeft (Z ^ 2)).charpoly =
        Polynomial.X ^ (2*k) * (partialTraceLeft (crop Z ^ 2)).charpoly ∧
    (partialTraceRight (Z ^ 2)).charpoly =
        Polynomial.X ^ (2*m) * (partialTraceRight (crop Z ^ 2)).charpoly := by
  rw [pow_two, pow_two]
  have h := supported_mul hZ hZ
  constructor
  · rw [charpoly_supported (supported_traceLeft h), crop_traceLeft h, crop_mul hZ hZ]
  · rw [charpoly_supported (supported_traceRight h), crop_traceRight h, crop_mul hZ hZ]

end Mathproof.EvenOrdinaryTISingular.EnlargedCut

#print axioms Mathproof.EvenOrdinaryTISingular.EnlargedCut.quadratic_charpoly_padding





