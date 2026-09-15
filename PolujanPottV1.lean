import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Polujan--Pott V.1

A self-contained, Mathlib-only certificate of two cubic vectorial
(12,2)-bent functions with isomorphic graph translation developments
that are not EA-equivalent.
-/

namespace PolujanPottV1

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

abbrev 𝔽₂ := Bool
/-- Six bits in a compact product representation; addition is coordinatewise XOR. -/
abbrev K := 𝔽₂ × 𝔽₂ × 𝔽₂ × 𝔽₂ × 𝔽₂ × 𝔽₂
abbrev W := 𝔽₂ × 𝔽₂
abbrev V := K × K
abbrev Point := V × W

def coordK (x : K) (i : Fin 6) : 𝔽₂ :=
  if i = 0 then x.1 else if i = 1 then x.2.1 else if i = 2 then x.2.2.1
  else if i = 3 then x.2.2.2.1 else if i = 4 then x.2.2.2.2.1 else x.2.2.2.2.2

def mkK (f : Fin 6 → 𝔽₂) : K := (f 0, f 1, f 2, f 3, f 4, f 5)
def bitNat (n i : ℕ) : 𝔽₂ := decide ((n / 2 ^ i) % 2 = 1)
def decode (n : ℕ) : K := (bitNat n 0, bitNat n 1, bitNat n 2, bitNat n 3, bitNat n 4, bitNat n 5)

theorem coordK_add (x y : K) (i : Fin 6) : coordK (x + y) i = coordK x i + coordK y i := by
  fin_cases i <;> rfl
def redLow : ℕ := 27
def xt (a : ℕ) : ℕ := if 32 ≤ a then Nat.xor ((a - 32) * 2) redLow else a * 2
def xtIter : ℕ → ℕ → ℕ | 0, a => a | n + 1, a => xt (xtIter n a)
def gmulNat (a b : ℕ) : ℕ :=
  (List.range 6).foldl
    (fun acc i => if (b / 2 ^ i) % 2 = 1 then Nat.xor acc (xtIter i a) else acc) 0
def mulK (x y : K) : K :=
  let x₀ := coordK x 0; let x₁ := coordK x 1; let x₂ := coordK x 2
  let x₃ := coordK x 3; let x₄ := coordK x 4; let x₅ := coordK x 5
  let y₀ := coordK y 0; let y₁ := coordK y 1; let y₂ := coordK y 2
  let y₃ := coordK y 3; let y₄ := coordK y 4; let y₅ := coordK y 5
  (x₀*y₀ + x₁*y₅ + x₂*y₄ + x₃*y₃ + x₃*y₅ + x₄*y₂ + x₄*y₄ + x₄*y₅ + x₅*y₁ + x₅*y₃ + x₅*y₄ + x₅*y₅,
   x₀*y₁ + x₁*y₀ + x₁*y₅ + x₂*y₄ + x₂*y₅ + x₃*y₃ + x₃*y₄ + x₃*y₅ + x₄*y₂ + x₄*y₃ + x₄*y₄ + x₅*y₁ + x₅*y₂ + x₅*y₃,
   x₀*y₂ + x₁*y₁ + x₂*y₀ + x₂*y₅ + x₃*y₄ + x₃*y₅ + x₄*y₃ + x₄*y₄ + x₄*y₅ + x₅*y₂ + x₅*y₃ + x₅*y₄,
   x₀*y₃ + x₁*y₂ + x₁*y₅ + x₂*y₁ + x₂*y₄ + x₃*y₀ + x₃*y₃ + x₄*y₂ + x₅*y₁,
   x₀*y₄ + x₁*y₃ + x₁*y₅ + x₂*y₂ + x₂*y₄ + x₂*y₅ + x₃*y₁ + x₃*y₃ + x₃*y₄ + x₃*y₅ + x₄*y₀ + x₄*y₂ + x₄*y₃ + x₄*y₄ + x₄*y₅ + x₅*y₁ + x₅*y₂ + x₅*y₃ + x₅*y₄ + x₅*y₅,
   x₀*y₅ + x₁*y₄ + x₂*y₃ + x₂*y₅ + x₃*y₂ + x₃*y₄ + x₃*y₅ + x₄*y₁ + x₄*y₃ + x₄*y₄ + x₄*y₅ + x₅*y₀ + x₅*y₂ + x₅*y₃ + x₅*y₄ + x₅*y₅)

def sqK (x : K) : K := mulK x x
def sqIterK : ℕ → K → K | 0, x => x | n + 1, x => sqK (sqIterK n x)

/-- Frobenius fourth power, expanded as its linear coordinate map. -/
def pow20 (y : K) : K := mulK (sqIterK 4 y) (sqIterK 2 y)
def pow21 (y : K) : K := mulK (pow20 y) y

def L (z : K) : W :=
  (coordK z 3,
   coordK z 0 + coordK z 1 + coordK z 2 + coordK z 3 + coordK z 4 + coordK z 5)

theorem mulK_add_left (x y z : K) : mulK (x + y) z = mulK x z + mulK y z := by
  ext <;> simp [mulK, coordK_add] <;> ring

theorem mulK_add_right (x y z : K) : mulK x (y + z) = mulK x y + mulK x z := by
  ext <;> simp [mulK, coordK_add] <;> ring

theorem L_add (x y : K) : L (x + y) = L x + L y := by
  ext <;> simp [L, coordK_add] <;> ring

def F₁ (p : V) : W := L (mulK p.1 p.2)
def F₂ (p : V) : W := F₁ p + L (pow21 p.2)

def component (c w : W) : 𝔽₂ := c.1 * w.1 + c.2 * w.2

theorem component_add (c u v : W) :
    component c (u + v) = component c u + component c v := by
  revert c u v
  decide +kernel

def pair (c : W) (x y : K) : 𝔽₂ := component c (L (mulK x y))

theorem pair_add_right (c : W) (x y z : K) :
    pair c x (y + z) = pair c x y + pair c x z := by
  simp only [pair, mulK_add_right, L_add, component_add]

def sgn (u : 𝔽₂) : ℤ := if u = 0 then 1 else -1

theorem sgn_add (u v : 𝔽₂) : sgn (u + v) = sgn u * sgn v := by
  revert u v
  decide +kernel

def MM (G : K → W) (p : V) : W := L (mulK p.1 p.2) + G p.2

def walsh (c : W) (F : V → W) (a b : K) : ℤ :=
  ∑ y : K, ∑ x : K,
    sgn (component c (F (x, y)) + pair c x a + pair c y b)

def IsBentComponent (c : W) (F : V → W) : Prop :=
  ∀ a b : K, walsh c F a b ^ 2 = 4096

/-- Standard vectorial bentness: every nonzero output component has flat Walsh spectrum. -/
def IsVectorialBent (F : V → W) : Prop :=
  ∀ c : W, c ≠ 0 → IsBentComponent c F

theorem pair_add_left (c : W) (x y z : K) :
    pair c (x + y) z = pair c x z + pair c y z := by
  simp only [pair, mulK_add_left, L_add, component_add]

theorem mulK_zero_right (x : K) : mulK x 0 = 0 := by
  ext <;> simp [mulK, coordK]

theorem L_zero : L 0 = 0 := by
  ext <;> simp [L, coordK]
def basisK (i : Fin 6) : K := mkK fun j => decide (j = i)

theorem pair_has_nonzero_direction :
    ∀ c : W, c ≠ 0 → ∀ z : K, z ≠ 0 → ∃ i : Fin 6, pair c (basisK i) z = 1 := by
  decide +kernel

theorem sgn_add_one (u : 𝔽₂) : sgn (u + 1) = -sgn u := by
  cases u <;> rfl

theorem character_sum_zero (χ : K → 𝔽₂)
    (hadd : ∀ x y, χ (x + y) = χ x + χ y)
    (e : K) (he : χ e = 1) : (∑ x : K, sgn (χ x)) = 0 := by
  have hreindex : (∑ x : K, sgn (χ (x + e))) = ∑ x : K, sgn (χ x) := by
    simpa using Equiv.sum_comp (Equiv.addRight e) (fun x : K => sgn (χ x))
  have hs : (∑ x : K, sgn (χ x)) = -(∑ x : K, sgn (χ x)) := by
    calc
      (∑ x : K, sgn (χ x)) = ∑ x : K, sgn (χ (x + e)) := hreindex.symm
      _ = ∑ x : K, -sgn (χ x) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [hadd, he, sgn_add_one]
      _ = -(∑ x : K, sgn (χ x)) := by simp
  omega

theorem pair_orthogonality :
    ∀ c : W, c ≠ 0 → ∀ z : K,
      (∑ x : K, sgn (pair c x z)) = if z = 0 then 64 else 0 := by
  intro c hc z
  by_cases hz : z = 0
  · subst z
    simp only [pair, mulK_zero_right, L_zero]
    norm_num [component, sgn]
  · rw [if_neg hz]
    obtain ⟨i, hi⟩ := pair_has_nonzero_direction c hc z hz
    exact character_sum_zero (fun x => pair c x z) (fun x y => pair_add_left c x y z) (basisK i) hi

/-! The generic Maiorana--McFarland collapse is included here so the certificate has no
 dependency on the older V.1 development. -/

theorem MM_walsh_collapses
    {A : Type*} [Fintype A] [DecidableEq A] [AddCommGroup A]
    (N : ℤ) (inner : A → A → ℤ)
    (horth : ∀ z : A, (∑ x : A, inner x z) = if z = 0 then N else 0)
    (π : A → A) (hπ : Function.Bijective π)
    (ε : A → ℤ) (a : A) :
    ∃ y₀ : A, π y₀ + a = 0 ∧
      (∑ y : A, ε y * (∑ x : A, inner x (π y + a))) = N * ε y₀ := by
  classical
  obtain ⟨y₀, hy₀⟩ := hπ.surjective (-a)
  have hzero : π y₀ + a = 0 := by rw [hy₀]; exact neg_add_cancel a
  refine ⟨y₀, hzero, ?_⟩
  have hterm : ∀ y : A, ε y * (∑ x : A, inner x (π y + a)) =
      ε y * (if π y + a = 0 then N else 0) := by
    intro y
    rw [horth]
  simp only [hterm]
  rw [Finset.sum_eq_single y₀]
  · rw [if_pos hzero]
    ring
  · intro y _ hne
    have hne' : π y + a ≠ 0 := by
      intro hcon
      have hpa : π y = -a := by
        calc
          π y = π y + a - a := by abel
          _ = 0 - a := by rw [hcon]
          _ = -a := zero_sub a
      have : π y = π y₀ := by rw [hpa, hy₀]
      exact hne (hπ.injective this)
    rw [if_neg hne']
    ring
  · intro hmem
    exact absurd (Finset.mem_univ y₀) hmem

theorem MM_walsh_sq_constant
    {A : Type*} [Fintype A] [DecidableEq A] [AddCommGroup A]
    (N : ℤ) (inner : A → A → ℤ)
    (horth : ∀ z : A, (∑ x : A, inner x z) = if z = 0 then N else 0)
    (π : A → A) (hπ : Function.Bijective π)
    (ε : A → ℤ) (hε : ∀ y, ε y = 1 ∨ ε y = -1) (a : A) :
    (∑ y : A, ε y * (∑ x : A, inner x (π y + a))) ^ 2 = N ^ 2 := by
  obtain ⟨y₀, _, hsum⟩ := MM_walsh_collapses N inner horth π hπ ε a
  rcases hε y₀ with h | h
  · rw [hsum, h]
    ring
  · rw [hsum, h]
    ring
theorem walsh_MM_factor (c : W) (G : K → W) (a b : K) :
    walsh c (MM G) a b =
      ∑ y : K, sgn (component c (G y) + pair c y b) *
        (∑ x : K, sgn (pair c x (y + a))) := by
  classical
  unfold walsh
  apply Finset.sum_congr rfl
  intro y _
  calc
    (∑ x : K, sgn (component c (MM G (x, y)) + pair c x a + pair c y b)) =
        ∑ x : K, sgn (component c (G y) + pair c y b) * sgn (pair c x (y + a)) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [← sgn_add]
      congr 1
      have hcomponent : component c (MM G (x, y)) = pair c x y + component c (G y) := by
        simp only [MM, component_add, pair]
      rw [hcomponent, pair_add_right]
      abel
    _ = sgn (component c (G y) + pair c y b) *
          (∑ x : K, sgn (pair c x (y + a))) := by
      simpa using (Finset.mul_sum Finset.univ
        (fun x : K => sgn (pair c x (y + a)))
        (sgn (component c (G y) + pair c y b))).symm
theorem MM_isVectorialBent (G : K → W) : IsVectorialBent (MM G) := by
  intro c hc a b
  rw [walsh_MM_factor]
  have h := MM_walsh_sq_constant
    (A := K) 64
    (fun x z => sgn (pair c x z))
    (pair_orthogonality c hc)
    (fun y => y) Function.bijective_id
    (fun y => sgn (component c (G y) + pair c y b))
    (by
      intro y
      unfold sgn
      split_ifs <;> simp)
    a
  norm_num at h ⊢
  exact h

def diff {A B : Type*} [Add A] [Sub B] (f : A → B) (a x : A) : B := f (x + a) - f x
def thirdDiff {A B : Type*} [Add A] [Sub B] (f : A → B) (a b c x : A) : B :=
  diff (diff (diff f a) b) c x
def DegreeLE2 {A B : Type*} [Add A] [Sub B] [Zero B] (f : A → B) : Prop :=
  ∀ a b c x, thirdDiff f a b c x = 0

theorem thirdDiff_precomp_affine
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (f : A → B) (e : A ≃+ A) (s a b c x : A) :
    thirdDiff (fun z => f (e z + s)) a b c x =
      thirdDiff f (e a) (e b) (e c) (e x + s) := by
  simp [thirdDiff, diff, map_add]
  congr 1 <;> abel

theorem thirdDiff_postcomp
    {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (f : A → B) (e : B →+ C) (a b c x : A) :
    thirdDiff (fun z => e (f z)) a b c x = e (thirdDiff f a b c x) := by
  simp [thirdDiff, diff, map_sub]

theorem thirdDiff_add
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (f g : A → B) (a b c x : A) :
    thirdDiff (fun z => f z + g z) a b c x =
      thirdDiff f a b c x + thirdDiff g a b c x := by
  simp [thirdDiff, diff]
  abel

theorem affine_thirdDiff_zero
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (q : A →+ B) (r : B) (a b c x : A) :
    thirdDiff (fun z => q z + r) a b c x = 0 := by
  simp [thirdDiff, diff, map_add]

def EAEquivalent (f g : V → W) : Prop :=
  ∃ (input : V ≃+ V) (inputShift : V) (output : W ≃+ W)
      (affinePart : V →+ W) (outputShift : W),
    ∀ x, g x = output (f (input x + inputShift)) + affinePart x + outputShift

theorem biadditive_degreeLE2
    {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (q : A → B → C)
    (hleft : ∀ x y z, q (x + y) z = q x z + q y z)
    (hright : ∀ x y z, q x (y + z) = q x y + q x z) :
    DegreeLE2 (fun p : A × B => q p.1 p.2) := by
  intro a b c x
  simp only [thirdDiff, diff, Prod.fst_add, Prod.snd_add]
  simp only [hleft, hright]
  abel

theorem traceMul_biadditive_left (x y z : K) :
    L (mulK (x + y) z) = L (mulK x z) + L (mulK y z) := by
  rw [mulK_add_left, L_add]
theorem traceMul_biadditive_right (x y z : K) :
    L (mulK x (y + z)) = L (mulK x y) + L (mulK x z) := by
  rw [mulK_add_right, L_add]

theorem F₁_degreeLE2 : DegreeLE2 F₁ := by
  exact biadditive_degreeLE2 (fun x y => L (mulK x y))
    traceMul_biadditive_left traceMul_biadditive_right

def kOfNat (n : ℕ) : K := decode n
def Incides (F : V → W) (p b : Point) : Prop := p.2 = F (p.1 + b.1) + b.2

def rho (p : Point) : Point := (((p.1.1 + pow20 p.1.2), p.1.2), p.2)
theorem Bool_add_self (x : 𝔽₂) : x + x = 0 := by
  cases x <;> rfl
theorem K_add_self (x : K) : x + x = 0 := by
  rcases x with ⟨x₀, x₁, x₂, x₃, x₄, x₅⟩
  ext <;> apply Bool_add_self

theorem rho_involutive (p : Point) : rho (rho p) = p := by
  rcases p with ⟨⟨x, y⟩, z⟩
  change (((x + pow20 y + pow20 y, y), z)) = (((x, y), z))
  congr 3
  calc
    x + pow20 y + pow20 y = x + (pow20 y + pow20 y) := add_assoc _ _ _
    _ = x + 0 := by rw [K_add_self]
    _ = x := add_zero x
def rhoEquiv : Point ≃ Point where
  toFun := rho
  invFun := rho
  left_inv := rho_involutive
  right_inv := rho_involutive

theorem mulK_comm (x y : K) : mulK x y = mulK y x := by
  ext <;> simp [mulK] <;> ring

theorem sqK_add (x y : K) : sqK (x + y) = sqK x + sqK y := by
  simp only [sqK, mulK_add_left, mulK_add_right]
  rw [mulK_comm y x]
  have hcross : mulK x y + mulK x y = 0 := K_add_self _
  calc
    mulK x x + mulK x y + (mulK x y + mulK y y) =
        mulK x x + (mulK x y + mulK x y) + mulK y y := by abel
    _ = mulK x x + mulK y y := by rw [hcross]; simp

theorem sqIterK_add (n : ℕ) (x y : K) :
    sqIterK n (x + y) = sqIterK n x + sqIterK n y := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [sqIterK]
      rw [ih, sqK_add]

theorem pow20_add_expansion (x y : K) :
    pow20 (x + y) =
      pow20 x + mulK (sqIterK 4 x) (sqIterK 2 y) +
        mulK (sqIterK 4 y) (sqIterK 2 x) + pow20 y := by
  simp only [pow20, sqIterK_add, mulK_add_left, mulK_add_right]
  abel

theorem W_add_self (x : W) : x + x = 0 := by
  rcases x with ⟨x₀, x₁⟩
  ext <;> apply Bool_add_self

def normCore (q b : K) : W :=
  L (mulK (mulK (sqIterK 4 q) (sqIterK 2 b)) q) +
  L (mulK (mulK (sqIterK 4 b) (sqIterK 2 q)) q)

theorem norm_expression_eq_core (v b : K) :
    L (mulK (pow20 v + pow20 b) (v + b)) + L (pow21 (v + b)) =
      normCore (v + b) b := by
  let q := v + b
  have hv : v = q + b := by
    dsimp [q]
    calc
      v = v + 0 := by simp
      _ = v + (b + b) := by rw [K_add_self b]
      _ = (v + b) + b := by abel
  have hp :
      pow20 v + pow20 b =
        pow20 q + mulK (sqIterK 4 q) (sqIterK 2 b) +
          mulK (sqIterK 4 b) (sqIterK 2 q) := by
    rw [hv]
    calc
      pow20 (q + b) + pow20 b =
          (pow20 q + mulK (sqIterK 4 q) (sqIterK 2 b) +
            mulK (sqIterK 4 b) (sqIterK 2 q)) + (pow20 b + pow20 b) := by
        rw [pow20_add_expansion]
        abel
      _ = (pow20 q + mulK (sqIterK 4 q) (sqIterK 2 b) +
            mulK (sqIterK 4 b) (sqIterK 2 q)) + 0 := by rw [K_add_self]
      _ = pow20 q + mulK (sqIterK 4 q) (sqIterK 2 b) +
            mulK (sqIterK 4 b) (sqIterK 2 q) := by simp
  rw [show v + b = q by rfl, hp]
  simp only [normCore, pow21, mulK_add_left, L_add]
  calc
    _ = (L (mulK (pow20 q) q) + L (mulK (pow20 q) q)) +
        (L (mulK (mulK (sqIterK 4 q) (sqIterK 2 b)) q) +
          L (mulK (mulK (sqIterK 4 b) (sqIterK 2 q)) q)) := by abel
    _ = 0 +
        (L (mulK (mulK (sqIterK 4 q) (sqIterK 2 b)) q) +
          L (mulK (mulK (sqIterK 4 b) (sqIterK 2 q)) q)) := by rw [W_add_self]
    _ = _ := by simp
theorem normCore_add (q b c : K) :
    normCore q (b + c) = normCore q b + normCore q c := by
  simp only [normCore, sqIterK_add, mulK_add_left, mulK_add_right, L_add]
  abel

theorem mulK_zero_left (x : K) : mulK 0 x = 0 := by
  rw [mulK_comm, mulK_zero_right]

theorem sqIterK_zero (n : ℕ) : sqIterK n 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [sqIterK, sqK, ih, mulK_zero_left]

def bitBasis (b : K) (i : Fin 6) : K :=
  if coordK b i then basisK i else 0

def basisExpansion (b : K) : K :=
  bitBasis b 0 + bitBasis b 1 + bitBasis b 2 +
    bitBasis b 3 + bitBasis b 4 + bitBasis b 5

theorem basisExpansion_eq (b : K) : basisExpansion b = b := by
  revert b
  decide +kernel

theorem normCore_zero (q : K) : normCore q 0 = 0 := by
  simp [normCore, sqIterK_zero, mulK_zero_left, mulK_zero_right, L_zero]

/-- The sole finite leaf in the design proof: 64 field elements times six basis directions. -/
theorem normCore_basis :
    ∀ q : K, ∀ i : Fin 6, normCore q (basisK i) = 0 := by
  decide +kernel

theorem normCore_zero_all (q b : K) : normCore q b = 0 := by
  rw [← basisExpansion_eq b]
  simp only [basisExpansion, normCore_add]
  have hbit : ∀ i : Fin 6, normCore q (bitBasis b i) = 0 := by
    intro i
    unfold bitBasis
    split
    · exact normCore_basis q i
    · exact normCore_zero q
  rw [hbit 0, hbit 1, hbit 2, hbit 3, hbit 4, hbit 5]
  abel

theorem norm_trace_identity (v b : K) :
    L (mulK (pow20 v + pow20 b) (v + b)) + L (pow21 (v + b)) = 0 := by
  rw [norm_expression_eq_core, normCore_zero_all]
theorem all_translate_transport (u v a b : K) :
    F₁ (u + a, v + b) =
      F₂ ((u + pow20 v) + (a + pow20 b), v + b) := by
  have harg :
      (u + pow20 v) + (a + pow20 b) = (u + a) + (pow20 v + pow20 b) := by
    abel
  rw [harg]
  simp only [F₁, F₂, mulK_add_left, L_add]
  have hnorm := norm_trace_identity v b
  have htail :
      L (mulK (pow20 v) (v + b)) +
        (L (mulK (pow20 b) (v + b)) + L (pow21 (v + b))) = 0 := by
    rw [← add_assoc, ← L_add, ← mulK_add_left]
    exact hnorm
  calc
    L (mulK u (v + b)) + L (mulK a (v + b)) =
        (L (mulK u (v + b)) + L (mulK a (v + b))) + 0 := by simp
    _ = (L (mulK u (v + b)) + L (mulK a (v + b))) +
        (L (mulK (pow20 v) (v + b)) +
          (L (mulK (pow20 b) (v + b)) + L (pow21 (v + b)))) := by rw [htail]
    _ = _ := by abel

/-- The ordinary coordinate dot product on the six-bit presentation of `K`. -/
def dotK (x u : K) : 𝔽₂ :=
  coordK x 0 * coordK u 0 + coordK x 1 * coordK u 1 +
  coordK x 2 * coordK u 2 + coordK x 3 * coordK u 3 +
  coordK x 4 * coordK u 4 + coordK x 5 * coordK u 5

/-- Coordinate frequency representing `x ↦ pair c x a`. -/
def freq (c : W) (a : K) : K :=
  (pair c (basisK 0) a, pair c (basisK 1) a, pair c (basisK 2) a,
   pair c (basisK 3) a, pair c (basisK 4) a, pair c (basisK 5) a)

theorem pair_eq_dot_freq (c : W) (x a : K) :
    pair c x a = dotK x (freq c a) := by
  revert c x a
  decide +kernel

theorem freq_zero (c : W) : freq c 0 = 0 := by
  ext <;> simp [freq, pair, mulK_zero_right, L_zero, component]

theorem freq_add (c : W) (a b : K) :
    freq c (a + b) = freq c a + freq c b := by
  ext <;> simp [freq, pair_add_right]

/-- The trace-pair frequency change is an additive endomorphism. -/
def freqHom (c : W) : K →+ K where
  toFun := freq c
  map_zero' := freq_zero c
  map_add' := freq_add c

theorem freq_kernel_trivial (c : W) (hc : c ≠ 0) (a : K)
    (ha : freq c a = 0) : a = 0 := by
  by_contra hne
  obtain ⟨i, hi⟩ := pair_has_nonzero_direction c hc a hne
  have hzero : pair c (basisK i) a = 0 := by
    rw [pair_eq_dot_freq, ha]
    simp [dotK, coordK]
  exact one_ne_zero (hi.symm.trans hzero)

theorem freq_injective (c : W) (hc : c ≠ 0) :
    Function.Injective (freq c) := by
  intro a b hab
  have hzero : freq c (a - b) = 0 := by
    calc
      freq c (a - b) = freq c a - freq c b := map_sub (freqHom c) a b
      _ = 0 := by rw [hab, sub_self]
  exact sub_eq_zero.mp (freq_kernel_trivial c hc (a - b) hzero)

theorem freq_bijective (c : W) (hc : c ≠ 0) :
    Function.Bijective (freq c) := by
  refine ⟨freq_injective c hc, ?_⟩
  exact (Finite.injective_iff_surjective.mp (freq_injective c hc))

/-- Ordinary Walsh coefficient using the coordinate dot product on both input halves. -/
def coordinateWalsh (c : W) (F : V → W) (u v : K) : ℤ :=
  ∑ y : K, ∑ x : K,
    sgn (component c (F (x, y)) + dotK x u + dotK y v)

def IsCoordinateBentComponent (c : W) (F : V → W) : Prop :=
  ∀ u v : K, coordinateWalsh c F u v ^ 2 = 4096

def IsCoordinateVectorialBent (F : V → W) : Prop :=
  ∀ c : W, c ≠ 0 → IsCoordinateBentComponent c F

theorem coordinateWalsh_freq (c : W) (F : V → W) (a b : K) :
    coordinateWalsh c F (freq c a) (freq c b) = walsh c F a b := by
  unfold coordinateWalsh walsh
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  rw [← pair_eq_dot_freq c x a, ← pair_eq_dot_freq c y b]

theorem vectorialBent_implies_coordinate {F : V → W}
    (hF : IsVectorialBent F) : IsCoordinateVectorialBent F := by
  intro c hc u v
  obtain ⟨a, ha⟩ := (freq_bijective c hc).surjective u
  obtain ⟨b, hb⟩ := (freq_bijective c hc).surjective v
  subst u
  subst v
  rw [coordinateWalsh_freq]
  exact hF c hc a b

abbrev IsStandardVectorialBent := IsCoordinateVectorialBent

def pow7 (y : K) : K := mulK (mulK (sqIterK 2 y) (sqIterK 1 y)) y

def G₁ (p : V) : W := F₁ p + L (pow7 p.2)
def G₂ (p : V) : W := G₁ p + L (pow21 p.2)

def fourthDiff {A B : Type*} [Add A] [Sub B] (f : A → B)
    (a b c d x : A) : B := diff (diff (diff (diff f a) b) c) d x

def DegreeLE3 {A B : Type*} [Add A] [Sub B] [Zero B] (f : A → B) : Prop :=
  ∀ a b c d x, fourthDiff f a b c d x = 0

theorem trilinear_diagonal_degreeLE3
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (T : A → A → A → B)
    (h₁ : ∀ x y z w, T (x + y) z w = T x z w + T y z w)
    (h₂ : ∀ x y z w, T x (y + z) w = T x y w + T x z w)
    (h₃ : ∀ x y z w, T x y (z + w) = T x y z + T x y w) :
    DegreeLE3 (fun x => T x x x) := by
  intro a b c d x
  simp only [fourthDiff, diff]
  simp only [h₁, h₂, h₃]
  abel

def T7 (u v w : K) : W :=
  L (mulK (mulK (sqIterK 2 u) (sqIterK 1 v)) w)

def T21 (u v w : K) : W :=
  L (mulK (mulK (sqIterK 4 u) (sqIterK 2 v)) w)

theorem T7_add₁ (x y z w : K) : T7 (x + y) z w = T7 x z w + T7 y z w := by
  simp only [T7, sqIterK_add, mulK_add_left, L_add]

theorem T7_add₂ (x y z w : K) : T7 x (y + z) w = T7 x y w + T7 x z w := by
  simp only [T7, sqIterK_add, mulK_add_right, mulK_add_left, L_add]

theorem T7_add₃ (x y z w : K) : T7 x y (z + w) = T7 x y z + T7 x y w := by
  simp only [T7, mulK_add_right, L_add]

theorem T21_add₁ (x y z w : K) : T21 (x + y) z w = T21 x z w + T21 y z w := by
  simp only [T21, sqIterK_add, mulK_add_left, L_add]

theorem T21_add₂ (x y z w : K) : T21 x (y + z) w = T21 x y w + T21 x z w := by
  simp only [T21, sqIterK_add, mulK_add_right, mulK_add_left, L_add]

theorem T21_add₃ (x y z w : K) : T21 x y (z + w) = T21 x y z + T21 x y w := by
  simp only [T21, mulK_add_right, L_add]

theorem L_pow7_degreeLE3 : DegreeLE3 (fun y : K => L (pow7 y)) := by
  exact trilinear_diagonal_degreeLE3 T7 T7_add₁ T7_add₂ T7_add₃

theorem L_pow21_degreeLE3 : DegreeLE3 (fun y : K => L (pow21 y)) := by
  exact trilinear_diagonal_degreeLE3 T21 T21_add₁ T21_add₂ T21_add₃

theorem DegreeLE3.snd {A B C : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] {f : B → C} (hf : DegreeLE3 f) :
    DegreeLE3 (fun p : A × B => f p.2) := by
  intro a b c d x
  simpa [fourthDiff, diff] using hf a.2 b.2 c.2 d.2 x.2

theorem degreeLE2_degreeLE3
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    {f : A → B} (hf : DegreeLE2 f) : DegreeLE3 f := by
  intro a b c d x
  change thirdDiff f a b c (x + d) - thirdDiff f a b c x = 0
  rw [hf, hf]
  simp

theorem fourthDiff_add
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (f g : A → B) (a b c d x : A) :
    fourthDiff (fun z => f z + g z) a b c d x =
      fourthDiff f a b c d x + fourthDiff g a b c d x := by
  simp [fourthDiff, diff]
  abel

theorem DegreeLE3.add
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    {f g : A → B} (hf : DegreeLE3 f) (hg : DegreeLE3 g) :
    DegreeLE3 (fun x => f x + g x) := by
  intro a b c d x
  rw [fourthDiff_add, hf, hg, zero_add]

theorem G₁_degreeLE3 : DegreeLE3 G₁ := by
  exact (degreeLE2_degreeLE3 F₁_degreeLE2).add L_pow7_degreeLE3.snd

theorem G₂_degreeLE3 : DegreeLE3 G₂ := by
  exact G₁_degreeLE3.add L_pow21_degreeLE3.snd

theorem G₁_eq_MM : G₁ = MM (fun y => L (pow7 y)) := by
  funext p
  rfl

theorem G₂_eq_MM : G₂ = MM (fun y => L (pow7 y) + L (pow21 y)) := by
  funext p
  simp only [G₂, G₁, F₁, MM]
  abel

theorem G₁_isVectorialBent : IsVectorialBent G₁ := by
  rw [G₁_eq_MM]
  exact MM_isVectorialBent (fun y => L (pow7 y))

theorem G₂_isVectorialBent : IsVectorialBent G₂ := by
  rw [G₂_eq_MM]
  exact MM_isVectorialBent (fun y => L (pow7 y) + L (pow21 y))

theorem G₁_isStandardVectorialBent : IsStandardVectorialBent G₁ :=
  vectorialBent_implies_coordinate G₁_isVectorialBent

theorem G₂_isStandardVectorialBent : IsStandardVectorialBent G₂ :=
  vectorialBent_implies_coordinate G₂_isVectorialBent

open Set

theorem G_all_translate_transport (u v a b : K) :
    G₁ (u + a, v + b) =
      G₂ ((u + pow20 v) + (a + pow20 b), v + b) := by
  unfold G₁ G₂
  rw [all_translate_transport u v a b]
  simp only [F₂, G₁]
  exact add_right_comm _ _ _

theorem G_incidence_transport (p b : Point) :
    Incides G₁ p b ↔ Incides G₂ (rho p) (rho b) := by
  rcases p with ⟨⟨u, v⟩, w⟩
  rcases b with ⟨⟨a, b⟩, c⟩
  change w = G₁ (u + a, v + b) + c ↔
    w = G₂ ((u + pow20 v) + (a + pow20 b), v + b) + c
  rw [← G_all_translate_transport u v a b]

def blockSet (F : V → W) (b : Point) : Set Point :=
  {p | Incides F p b}

def Development (F : V → W) :=
  {B : Set Point // ∃ b : Point, B = blockSet F b}

def DevelopmentIncides (F : V → W) (p : Point) (B : Development F) : Prop :=
  p ∈ B.1

theorem rho_image_GblockSet₁₂ (b : Point) :
    rho '' blockSet G₁ b = blockSet G₂ (rho b) := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    change Incides G₁ p b at hp
    change Incides G₂ (rho p) (rho b)
    exact (G_incidence_transport p b).mp hp
  · intro hq
    change Incides G₂ q (rho b) at hq
    refine ⟨rho q, ?_, rho_involutive q⟩
    change Incides G₁ (rho q) b
    apply (G_incidence_transport (rho q) b).mpr
    simpa only [rho_involutive] using hq

theorem rho_image_GblockSet₂₁ (b : Point) :
    rho '' blockSet G₂ b = blockSet G₁ (rho b) := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    change Incides G₂ p b at hp
    change Incides G₁ (rho p) (rho b)
    apply (G_incidence_transport (rho p) (rho b)).mpr
    simpa only [rho_involutive] using hp
  · intro hq
    change Incides G₁ q (rho b) at hq
    refine ⟨rho q, ?_, rho_involutive q⟩
    change Incides G₂ (rho q) b
    have h := (G_incidence_transport q (rho b)).mp hq
    simpa only [rho_involutive] using h

theorem rho_image_involutive (S : Set Point) :
    rho '' (rho '' S) = S := by
  ext p
  constructor
  · rintro ⟨q, ⟨r, hr, rfl⟩, hq⟩
    have : r = p := by simpa only [rho_involutive] using hq
    simpa only [← this] using hr
  · intro hp
    exact ⟨rho p, ⟨p, hp, rfl⟩, rho_involutive p⟩

def developmentMap₁₂ (B : Development G₁) : Development G₂ := by
  refine ⟨rho '' B.1, ?_⟩
  rcases B.2 with ⟨b, hB⟩
  refine ⟨rho b, ?_⟩
  rw [hB]
  exact rho_image_GblockSet₁₂ b

def developmentMap₂₁ (B : Development G₂) : Development G₁ := by
  refine ⟨rho '' B.1, ?_⟩
  rcases B.2 with ⟨b, hB⟩
  refine ⟨rho b, ?_⟩
  rw [hB]
  exact rho_image_GblockSet₂₁ b

def developmentEquiv : Development G₁ ≃ Development G₂ where
  toFun := developmentMap₁₂
  invFun := developmentMap₂₁
  left_inv := by
    intro B
    apply Subtype.ext
    exact rho_image_involutive B.1
  right_inv := by
    intro B
    apply Subtype.ext
    exact rho_image_involutive B.1

structure StandardDevelopmentIso (F G : V → W) where
  pointEquiv : Point ≃ Point
  blockEquiv : Development F ≃ Development G
  incidence_iff :
    ∀ p B, DevelopmentIncides F p B ↔
      DevelopmentIncides G (pointEquiv p) (blockEquiv B)

theorem development_incidence_transport (p : Point) (B : Development G₁) :
    DevelopmentIncides G₁ p B ↔
      DevelopmentIncides G₂ (rhoEquiv p) (developmentEquiv B) := by
  change p ∈ B.1 ↔ rho p ∈ rho '' B.1
  constructor
  · intro hp
    exact ⟨p, hp, rfl⟩
  · rintro ⟨q, hq, hqp⟩
    have : q = p := rhoEquiv.injective hqp
    simpa only [this] using hq

def standardTranslationDevelopmentIso :
    StandardDevelopmentIso G₁ G₂ where
  pointEquiv := rhoEquiv
  blockEquiv := developmentEquiv
  incidence_iff := development_incidence_transport

theorem standard_cubic_developments_are_isomorphic :
    Nonempty (StandardDevelopmentIso G₁ G₂) :=
  ⟨standardTranslationDevelopmentIso⟩

def thirdTensor (f : V → W) (a b c : V) : W := thirdDiff f a b c 0

theorem thirdDiff_eq_thirdTensor {f : V → W} (hf : DegreeLE3 f)
    (a b c x : V) : thirdDiff f a b c x = thirdTensor f a b c := by
  have h := hf a b c x 0
  change thirdDiff f a b c (0 + x) - thirdDiff f a b c 0 = 0 at h
  rw [zero_add] at h
  exact sub_eq_zero.mp h

theorem thirdTensor_ea_covariant {f g : V → W} (hf : DegreeLE3 f)
    (hEA : EAEquivalent f g) :
    ∃ (input : V ≃+ V) (output : W ≃+ W),
      ∀ a b c, thirdTensor g a b c =
        output (thirdTensor f (input a) (input b) (input c)) := by
  obtain ⟨input, inputShift, output, affinePart, outputShift, h⟩ := hEA
  refine ⟨input, output, ?_⟩
  intro a b c
  unfold thirdTensor
  rw [show thirdDiff g a b c 0 = thirdDiff
      (fun z => output (f (input z + inputShift)) + (affinePart z + outputShift))
      a b c 0 by
        congr 1
        funext z
        rw [h]
        abel]
  rw [thirdDiff_add]
  have hout : thirdDiff (fun z => output (f (input z + inputShift))) a b c 0 =
      output (thirdDiff (fun z => f (input z + inputShift)) a b c 0) := by
    simpa using thirdDiff_postcomp (fun z => f (input z + inputShift))
      output.toAddMonoidHom a b c 0
  rw [hout, thirdDiff_precomp_affine, affine_thirdDiff_zero]
  rw [thirdDiff_eq_thirdTensor hf]
  simp only [add_zero]
  rfl

abbrev DirectionTriple := V × V × V

def TripleZero (f : V → W) :=
  {d : DirectionTriple // thirdTensor f d.1 d.2.1 d.2.2 = 0}

noncomputable local instance tripleZeroFinite (f : V → W) : Finite (TripleZero f) :=
  Finite.of_injective Subtype.val Subtype.val_injective

noncomputable def thirdZeroCount (f : V → W) : Nat :=
  @Fintype.card (TripleZero f) (Fintype.ofFinite _)

theorem thirdZeroCount_ea_invariant {f g : V → W}
    (hf : DegreeLE3 f) (hEA : EAEquivalent f g) :
    thirdZeroCount f = thirdZeroCount g := by
  obtain ⟨input, output, hcov⟩ := thirdTensor_ea_covariant hf hEA
  let E : DirectionTriple ≃ DirectionTriple :=
    input.toEquiv.prodCongr (input.toEquiv.prodCongr input.toEquiv)
  have hz : TripleZero g ≃ TripleZero f := by
    refine
      { toFun := fun d => ⟨E d.1, ?_⟩
        invFun := fun d => ⟨E.symm d.1, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · have hout : output (thirdTensor f (input d.1.1) (input d.1.2.1)
          (input d.1.2.2)) = 0 := by
        rw [← hcov]
        exact d.2
      exact output.injective (hout.trans output.map_zero.symm)
    · change thirdTensor g (input.symm d.1.1) (input.symm d.1.2.1)
          (input.symm d.1.2.2) = 0
      rw [hcov]
      simp only [AddEquiv.apply_symm_apply, d.2, map_zero]
    · intro d
      apply Subtype.ext
      exact E.left_inv d.1
    · intro d
      apply Subtype.ext
      exact E.right_inv d.1
  letI : Fintype (TripleZero f) := Fintype.ofFinite _
  letI : Fintype (TripleZero g) := Fintype.ofFinite _
  unfold thirdZeroCount
  exact (Fintype.card_congr hz).symm

/-- The six-term polarization of a trilinear diagonal. -/
def symm3 {A B : Type*} [Add B] (T : A → A → A → B) (a b c : A) : B :=
  T a b c + T a c b + T b a c + T b c a + T c a b + T c b a

theorem thirdDiff_trilinear_diagonal
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (T : A → A → A → B)
    (h₁ : ∀ x y z w, T (x + y) z w = T x z w + T y z w)
    (h₂ : ∀ x y z w, T x (y + z) w = T x y w + T x z w)
    (h₃ : ∀ x y z w, T x y (z + w) = T x y z + T x y w)
    (a b c x : A) :
    thirdDiff (fun y => T y y y) a b c x = symm3 T a b c := by
  simp only [thirdDiff, diff, symm3]
  simp only [h₁, h₂, h₃]
  abel

theorem thirdDiff_L_pow7 (a b c x : K) :
    thirdDiff (fun y : K => L (pow7 y)) a b c x = symm3 T7 a b c := by
  simpa only [pow7, T7] using
    thirdDiff_trilinear_diagonal T7 T7_add₁ T7_add₂ T7_add₃ a b c x

theorem thirdDiff_L_pow21 (a b c x : K) :
    thirdDiff (fun y : K => L (pow21 y)) a b c x = symm3 T21 a b c := by
  simpa only [pow21, pow20, T21] using
    thirdDiff_trilinear_diagonal T21 T21_add₁ T21_add₂ T21_add₃ a b c x

theorem thirdDiff_snd
    {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (f : B → C) (a b c x : A × B) :
    thirdDiff (fun p : A × B => f p.2) a b c x =
      thirdDiff f a.2 b.2 c.2 x.2 := by
  simp [thirdDiff, diff]

theorem thirdDiff_G₁_on_y (a b c : K) (x : V) :
    thirdDiff G₁ (0, a) (0, b) (0, c) x = symm3 T7 a b c := by
  change thirdDiff (fun p : V => F₁ p + L (pow7 p.2))
    (0, a) (0, b) (0, c) x = _
  rw [thirdDiff_add, F₁_degreeLE2, zero_add]
  exact (thirdDiff_snd (A := K) (B := K) (C := W)
    (fun y : K => L (pow7 y)) (0, a) (0, b) (0, c) x).trans
      (thirdDiff_L_pow7 a b c x.2)

theorem thirdDiff_G₂_on_y (a b c : K) (x : V) :
    thirdDiff G₂ (0, a) (0, b) (0, c) x =
      symm3 T7 a b c + symm3 T21 a b c := by
  change thirdDiff (fun p : V => G₁ p + L (pow21 p.2))
    (0, a) (0, b) (0, c) x = _
  rw [thirdDiff_add, thirdDiff_G₁_on_y]
  have hsnd := thirdDiff_snd (A := K) (B := K) (C := W)
    (fun y : K => L (pow21 y)) (0, a) (0, b) (0, c) x
  rw [hsnd, thirdDiff_L_pow21]

def k1 : K := kOfNat 1
def k2 : K := kOfNat 2
def k4 : K := kOfNat 4
def k16 : K := kOfNat 16

theorem symm3_T7_124_value : symm3 T7 k1 k2 k4 = (1, 0) := by
  decide +kernel

theorem symm3_T7_124_nonzero : symm3 T7 k1 k2 k4 ≠ 0 := by
  rw [symm3_T7_124_value]
  decide

theorem symm3_T7_T21_1216_value :
    symm3 T7 k1 k2 k16 + symm3 T21 k1 k2 k16 = (0, 1) := by
  decide +kernel

theorem symm3_T7_T21_1216_nonzero :
    symm3 T7 k1 k2 k16 + symm3 T21 k1 k2 k16 ≠ 0 := by
  rw [symm3_T7_T21_1216_value]
  decide

theorem G₁_explicit_thirdDerivative :
    thirdDiff G₁ (0, k1) (0, k2) (0, k4) 0 ≠ 0 := by
  rw [thirdDiff_G₁_on_y]
  exact symm3_T7_124_nonzero

theorem G₂_explicit_thirdDerivative :
    thirdDiff G₂ (0, k1) (0, k2) (0, k16) 0 ≠ 0 := by
  rw [thirdDiff_G₂_on_y]
  exact symm3_T7_T21_1216_nonzero

theorem G₁_not_degreeLE2 : ¬ DegreeLE2 G₁ := by
  intro h
  exact G₁_explicit_thirdDerivative (h (0, k1) (0, k2) (0, k4) 0)

theorem G₂_not_degreeLE2 : ¬ DegreeLE2 G₂ := by
  intro h
  exact G₂_explicit_thirdDerivative (h (0, k1) (0, k2) (0, k16) 0)

/-- Both members of the stronger pair have algebraic degree exactly three in derivative form. -/
theorem G₁_degree_exactly_three : DegreeLE3 G₁ ∧ ¬ DegreeLE2 G₁ :=
  ⟨G₁_degreeLE3, G₁_not_degreeLE2⟩

theorem G₂_degree_exactly_three : DegreeLE3 G₂ ∧ ¬ DegreeLE2 G₂ :=
  ⟨G₂_degreeLE3, G₂_not_degreeLE2⟩

def yTensor₁ (a b c : K) : W :=
  thirdDiff (fun y : K => L (pow7 y)) a b c 0

def yTensor₂ (a b c : K) : W :=
  thirdDiff (fun y : K => L (pow7 y) + L (pow21 y)) a b c 0

theorem thirdTensor_G₁_depends_only_on_y (a b c : V) :
    thirdTensor G₁ a b c = yTensor₁ a.2 b.2 c.2 := by
  unfold thirdTensor yTensor₁ G₁
  rw [thirdDiff_add, F₁_degreeLE2, zero_add]
  exact thirdDiff_snd (fun y : K => L (pow7 y)) a b c 0

theorem thirdTensor_G₂_depends_only_on_y (a b c : V) :
    thirdTensor G₂ a b c = yTensor₂ a.2 b.2 c.2 := by
  unfold yTensor₂
  change thirdDiff G₂ a b c 0 = _
  unfold G₂
  rw [thirdDiff_add]
  change thirdTensor G₁ a b c +
    thirdDiff (fun p : V => L (pow21 p.2)) a b c 0 = _
  rw [thirdTensor_G₁_depends_only_on_y]
  have h21 : thirdDiff (fun p : V => L (pow21 p.2)) a b c 0 =
      thirdDiff (fun y : K => L (pow21 y)) a.2 b.2 c.2 0 := by
    simpa using thirdDiff_snd (fun y : K => L (pow21 y)) a b c (0 : V)
  rw [h21]
  unfold yTensor₁
  rw [thirdDiff_add]
abbrev YDirectionTriple := K × K × K

def YTripleZero (T : K → K → K → W) :=
  {d : YDirectionTriple // T d.1 d.2.1 d.2.2 = 0}

noncomputable local instance yTripleZeroFinite
    (T : K → K → K → W) : Finite (YTripleZero T) :=
  Finite.of_injective Subtype.val Subtype.val_injective

def tripleZeroEquiv
    (f : V → W) (T : K → K → K → W)
    (h : ∀ a b c, thirdTensor f a b c = T a.2 b.2 c.2) :
    TripleZero f ≃ (K × K × K) × YTripleZero T where
  toFun d :=
    ((d.1.1.1, (d.1.2.1.1, d.1.2.2.1)),
      ⟨(d.1.1.2, (d.1.2.1.2, d.1.2.2.2)), by
        rw [← h d.1.1 d.1.2.1 d.1.2.2]
        exact d.2⟩)
  invFun d :=
    ⟨((d.1.1, d.2.1.1), ((d.1.2.1, d.2.1.2.1),
        (d.1.2.2, d.2.1.2.2))), by
      change thirdTensor f (d.1.1, d.2.1.1) (d.1.2.1, d.2.1.2.1)
        (d.1.2.2, d.2.1.2.2) = 0
      rw [h (d.1.1, d.2.1.1) (d.1.2.1, d.2.1.2.1)
        (d.1.2.2, d.2.1.2.2)]
      exact d.2.2⟩
  left_inv := by
    intro d
    apply Subtype.ext
    rfl
  right_inv := by
    intro d
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      rfl

noncomputable def yThirdZeroCount (T : K → K → K → W) : Nat :=
  @Fintype.card (YTripleZero T) (Fintype.ofFinite _)

set_option linter.style.haveILetI false in
theorem thirdZeroCount_eq_64_cubed_mul_yThirdZeroCount
    (f : V → W) (T : K → K → K → W)
    (h : ∀ a b c, thirdTensor f a b c = T a.2 b.2 c.2) :
    thirdZeroCount f = 64 ^ 3 * yThirdZeroCount T := by
  letI : Fintype (TripleZero f) := Fintype.ofFinite _
  letI : Fintype (YTripleZero T) := Fintype.ofFinite _
  unfold thirdZeroCount yThirdZeroCount
  rw [Fintype.card_congr (tripleZeroEquiv f T h)]
  have hK : Fintype.card K = 64 := by decide
  simp [Fintype.card_prod, hK]
theorem thirdZeroCount_G₁_factor :
    thirdZeroCount G₁ = 64 ^ 3 * yThirdZeroCount yTensor₁ :=
  thirdZeroCount_eq_64_cubed_mul_yThirdZeroCount
    G₁ yTensor₁ thirdTensor_G₁_depends_only_on_y

theorem thirdZeroCount_G₂_factor :
    thirdZeroCount G₂ = 64 ^ 3 * yThirdZeroCount yTensor₂ :=
  thirdZeroCount_eq_64_cubed_mul_yThirdZeroCount
    G₂ yTensor₂ thirdTensor_G₂_depends_only_on_y

def mulN (a b : Fin 64) : Fin 64 := ⟨gmulNat a.val b.val % 64, Nat.mod_lt _ (by decide)⟩
def toK (a : Fin 64) : K := decode a.val

@[simp] theorem mulN_row_0 (b : Fin 64) :
    toK (mulN ⟨0, by decide⟩ b) = mulK (toK ⟨0, by decide⟩) (toK b) := by
  revert b
  decide +kernel

@[simp] theorem mulN_row_1 (b : Fin 64) :
    toK (mulN ⟨1, by decide⟩ b) = mulK (toK ⟨1, by decide⟩) (toK b) := by
  revert b
  decide +kernel

@[simp] theorem mulN_row_2 (b : Fin 64) :
    toK (mulN ⟨2, by decide⟩ b) = mulK (toK ⟨2, by decide⟩) (toK b) := by
  revert b
  decide +kernel

@[simp] theorem mulN_row_3 (b : Fin 64) :
    toK (mulN ⟨3, by decide⟩ b) = mulK (toK ⟨3, by decide⟩) (toK b) := by
  revert b
  decide +kernel

@[simp] theorem mulN_row_4 (b : Fin 64) :
    toK (mulN ⟨4, by decide⟩ b) = mulK (toK ⟨4, by decide⟩) (toK b) := by
  revert b
  decide +kernel

@[simp] theorem mulN_row_5 (b : Fin 64) :
    toK (mulN ⟨5, by decide⟩ b) = mulK (toK ⟨5, by decide⟩) (toK b) := by
  revert b
  decide +kernel

@[simp] theorem mulN_row_6 (b : Fin 64) :
    toK (mulN ⟨6, by decide⟩ b) = mulK (toK ⟨6, by decide⟩) (toK b) := by
  revert b
  decide +kernel

@[simp] theorem mulN_row_7 (b : Fin 64) :
    toK (mulN ⟨7, by decide⟩ b) = mulK (toK ⟨7, by decide⟩) (toK b) := by
  revert b
  decide +kernel

@[simp] theorem mulN_row_8 (b : Fin 64) :
    toK (mulN ⟨8, by decide⟩ b) = mulK (toK ⟨8, by decide⟩) (toK b) := by
  revert b
  decide +kernel

@[simp] theorem mulN_row_9 (b : Fin 64) :
    toK (mulN ⟨9, by decide⟩ b) = mulK (toK ⟨9, by decide⟩) (toK b) := by
  revert b
  decide +kernel

@[simp] theorem mulN_row_10 (b : Fin 64) :
    toK (mulN ⟨10, by decide⟩ b) = mulK (toK ⟨10, by decide⟩) (toK b) := by
  revert b
  decide +kernel

@[simp] theorem mulN_row_11 (b : Fin 64) :
    toK (mulN ⟨11, by decide⟩ b) = mulK (toK ⟨11, by decide⟩) (toK b) := by
  revert b
  decide +kernel

@[simp] theorem mulN_row_12 (b : Fin 64) :
    toK (mulN ⟨12, by decide⟩ b) = mulK (toK ⟨12, by decide⟩) (toK b) := by
  revert b
  decide +kernel

@[simp] theorem mulN_row_13 (b : Fin 64) :
    toK (mulN ⟨13, by decide⟩ b) = mulK (toK ⟨13, by decide⟩) (toK b) := by
  revert b
  decide +kernel

@[simp] theorem mulN_row_14 (b : Fin 64) :
    toK (mulN ⟨14, by decide⟩ b) = mulK (toK ⟨14, by decide⟩) (toK b) := by
  revert b
  decide +kernel

@[simp] theorem mulN_row_15 (b : Fin 64) :
    toK (mulN ⟨15, by decide⟩ b) = mulK (toK ⟨15, by decide⟩) (toK b) := by
  revert b
  decide +kernel

@[simp] theorem mulN_row_16 (b : Fin 64) :
    toK (mulN ⟨16, by decide⟩ b) = mulK (toK ⟨16, by decide⟩) (toK b) := by
  revert b
  decide +kernel

@[simp] theorem mulN_row_17 (b : Fin 64) :
    toK (mulN ⟨17, by decide⟩ b) = mulK (toK ⟨17, by decide⟩) (toK b) := by
  revert b
  decide +kernel

@[simp] theorem mulN_row_18 (b : Fin 64) :
    toK (mulN ⟨18, by decide⟩ b) = mulK (toK ⟨18, by decide⟩) (toK b) := by
  revert b
  decide +kernel

@[simp] theorem mulN_row_19 (b : Fin 64) :
    toK (mulN ⟨19, by decide⟩ b) = mulK (toK ⟨19, by decide⟩) (toK b) := by
  revert b
  decide +kernel

@[simp] theorem mulN_row_20 (b : Fin 64) :
    toK (mulN ⟨20, by decide⟩ b) = mulK (toK ⟨20, by decide⟩) (toK b) := by
  revert b
  decide +kernel

@[simp] theorem mulN_row_21 (b : Fin 64) :
    toK (mulN ⟨21, by decide⟩ b) = mulK (toK ⟨21, by decide⟩) (toK b) := by
  revert b
  decide +kernel

@[simp] theorem mulN_row_22 (b : Fin 64) :
    toK (mulN ⟨22, by decide⟩ b) = mulK (toK ⟨22, by decide⟩) (toK b) := by
  revert b
  decide +kernel

@[simp] theorem mulN_row_23 (b : Fin 64) :
    toK (mulN ⟨23, by decide⟩ b) = mulK (toK ⟨23, by decide⟩) (toK b) := by
  revert b
  decide +kernel

@[simp] theorem mulN_row_24 (b : Fin 64) :
    toK (mulN ⟨24, by decide⟩ b) = mulK (toK ⟨24, by decide⟩) (toK b) := by
  revert b
  decide +kernel

@[simp] theorem mulN_row_25 (b : Fin 64) :
    toK (mulN ⟨25, by decide⟩ b) = mulK (toK ⟨25, by decide⟩) (toK b) := by
  revert b
  decide +kernel

@[simp] theorem mulN_row_26 (b : Fin 64) :
    toK (mulN ⟨26, by decide⟩ b) = mulK (toK ⟨26, by decide⟩) (toK b) := by
  revert b
  decide +kernel

@[simp] theorem mulN_row_27 (b : Fin 64) :
    toK (mulN ⟨27, by decide⟩ b) = mulK (toK ⟨27, by decide⟩) (toK b) := by
  revert b
  decide +kernel

@[simp] theorem mulN_row_28 (b : Fin 64) :
    toK (mulN ⟨28, by decide⟩ b) = mulK (toK ⟨28, by decide⟩) (toK b) := by
  revert b
  decide +kernel

@[simp] theorem mulN_row_29 (b : Fin 64) :
    toK (mulN ⟨29, by decide⟩ b) = mulK (toK ⟨29, by decide⟩) (toK b) := by
  revert b
  decide +kernel

@[simp] theorem mulN_row_30 (b : Fin 64) :
    toK (mulN ⟨30, by decide⟩ b) = mulK (toK ⟨30, by decide⟩) (toK b) := by
  revert b
  decide +kernel

@[simp] theorem mulN_row_31 (b : Fin 64) :
    toK (mulN ⟨31, by decide⟩ b) = mulK (toK ⟨31, by decide⟩) (toK b) := by
  revert b
  decide +kernel

@[simp] theorem mulN_row_32 (b : Fin 64) :
    toK (mulN ⟨32, by decide⟩ b) = mulK (toK ⟨32, by decide⟩) (toK b) := by
  revert b
  decide +kernel

@[simp] theorem mulN_row_33 (b : Fin 64) :
    toK (mulN ⟨33, by decide⟩ b) = mulK (toK ⟨33, by decide⟩) (toK b) := by
  revert b
  decide +kernel

@[simp] theorem mulN_row_34 (b : Fin 64) :
    toK (mulN ⟨34, by decide⟩ b) = mulK (toK ⟨34, by decide⟩) (toK b) := by
  revert b
  decide +kernel

@[simp] theorem mulN_row_35 (b : Fin 64) :
    toK (mulN ⟨35, by decide⟩ b) = mulK (toK ⟨35, by decide⟩) (toK b) := by
  revert b
  decide +kernel

@[simp] theorem mulN_row_36 (b : Fin 64) :
    toK (mulN ⟨36, by decide⟩ b) = mulK (toK ⟨36, by decide⟩) (toK b) := by
  revert b
  decide +kernel

@[simp] theorem mulN_row_37 (b : Fin 64) :
    toK (mulN ⟨37, by decide⟩ b) = mulK (toK ⟨37, by decide⟩) (toK b) := by
  revert b
  decide +kernel

@[simp] theorem mulN_row_38 (b : Fin 64) :
    toK (mulN ⟨38, by decide⟩ b) = mulK (toK ⟨38, by decide⟩) (toK b) := by
  revert b
  decide +kernel

@[simp] theorem mulN_row_39 (b : Fin 64) :
    toK (mulN ⟨39, by decide⟩ b) = mulK (toK ⟨39, by decide⟩) (toK b) := by
  revert b
  decide +kernel

@[simp] theorem mulN_row_40 (b : Fin 64) :
    toK (mulN ⟨40, by decide⟩ b) = mulK (toK ⟨40, by decide⟩) (toK b) := by
  revert b
  decide +kernel

@[simp] theorem mulN_row_41 (b : Fin 64) :
    toK (mulN ⟨41, by decide⟩ b) = mulK (toK ⟨41, by decide⟩) (toK b) := by
  revert b
  decide +kernel

@[simp] theorem mulN_row_42 (b : Fin 64) :
    toK (mulN ⟨42, by decide⟩ b) = mulK (toK ⟨42, by decide⟩) (toK b) := by
  revert b
  decide +kernel

@[simp] theorem mulN_row_43 (b : Fin 64) :
    toK (mulN ⟨43, by decide⟩ b) = mulK (toK ⟨43, by decide⟩) (toK b) := by
  revert b
  decide +kernel

@[simp] theorem mulN_row_44 (b : Fin 64) :
    toK (mulN ⟨44, by decide⟩ b) = mulK (toK ⟨44, by decide⟩) (toK b) := by
  revert b
  decide +kernel

@[simp] theorem mulN_row_45 (b : Fin 64) :
    toK (mulN ⟨45, by decide⟩ b) = mulK (toK ⟨45, by decide⟩) (toK b) := by
  revert b
  decide +kernel

@[simp] theorem mulN_row_46 (b : Fin 64) :
    toK (mulN ⟨46, by decide⟩ b) = mulK (toK ⟨46, by decide⟩) (toK b) := by
  revert b
  decide +kernel

@[simp] theorem mulN_row_47 (b : Fin 64) :
    toK (mulN ⟨47, by decide⟩ b) = mulK (toK ⟨47, by decide⟩) (toK b) := by
  revert b
  decide +kernel

@[simp] theorem mulN_row_48 (b : Fin 64) :
    toK (mulN ⟨48, by decide⟩ b) = mulK (toK ⟨48, by decide⟩) (toK b) := by
  revert b
  decide +kernel

@[simp] theorem mulN_row_49 (b : Fin 64) :
    toK (mulN ⟨49, by decide⟩ b) = mulK (toK ⟨49, by decide⟩) (toK b) := by
  revert b
  decide +kernel

@[simp] theorem mulN_row_50 (b : Fin 64) :
    toK (mulN ⟨50, by decide⟩ b) = mulK (toK ⟨50, by decide⟩) (toK b) := by
  revert b
  decide +kernel

@[simp] theorem mulN_row_51 (b : Fin 64) :
    toK (mulN ⟨51, by decide⟩ b) = mulK (toK ⟨51, by decide⟩) (toK b) := by
  revert b
  decide +kernel

@[simp] theorem mulN_row_52 (b : Fin 64) :
    toK (mulN ⟨52, by decide⟩ b) = mulK (toK ⟨52, by decide⟩) (toK b) := by
  revert b
  decide +kernel

@[simp] theorem mulN_row_53 (b : Fin 64) :
    toK (mulN ⟨53, by decide⟩ b) = mulK (toK ⟨53, by decide⟩) (toK b) := by
  revert b
  decide +kernel

@[simp] theorem mulN_row_54 (b : Fin 64) :
    toK (mulN ⟨54, by decide⟩ b) = mulK (toK ⟨54, by decide⟩) (toK b) := by
  revert b
  decide +kernel

@[simp] theorem mulN_row_55 (b : Fin 64) :
    toK (mulN ⟨55, by decide⟩ b) = mulK (toK ⟨55, by decide⟩) (toK b) := by
  revert b
  decide +kernel

@[simp] theorem mulN_row_56 (b : Fin 64) :
    toK (mulN ⟨56, by decide⟩ b) = mulK (toK ⟨56, by decide⟩) (toK b) := by
  revert b
  decide +kernel

@[simp] theorem mulN_row_57 (b : Fin 64) :
    toK (mulN ⟨57, by decide⟩ b) = mulK (toK ⟨57, by decide⟩) (toK b) := by
  revert b
  decide +kernel

@[simp] theorem mulN_row_58 (b : Fin 64) :
    toK (mulN ⟨58, by decide⟩ b) = mulK (toK ⟨58, by decide⟩) (toK b) := by
  revert b
  decide +kernel

@[simp] theorem mulN_row_59 (b : Fin 64) :
    toK (mulN ⟨59, by decide⟩ b) = mulK (toK ⟨59, by decide⟩) (toK b) := by
  revert b
  decide +kernel

@[simp] theorem mulN_row_60 (b : Fin 64) :
    toK (mulN ⟨60, by decide⟩ b) = mulK (toK ⟨60, by decide⟩) (toK b) := by
  revert b
  decide +kernel

@[simp] theorem mulN_row_61 (b : Fin 64) :
    toK (mulN ⟨61, by decide⟩ b) = mulK (toK ⟨61, by decide⟩) (toK b) := by
  revert b
  decide +kernel

@[simp] theorem mulN_row_62 (b : Fin 64) :
    toK (mulN ⟨62, by decide⟩ b) = mulK (toK ⟨62, by decide⟩) (toK b) := by
  revert b
  decide +kernel

@[simp] theorem mulN_row_63 (b : Fin 64) :
    toK (mulN ⟨63, by decide⟩ b) = mulK (toK ⟨63, by decide⟩) (toK b) := by
  revert b
  decide +kernel

theorem toK_mulN (a b : Fin 64) : toK (mulN a b) = mulK (toK a) (toK b) := by
  fin_cases a
  · exact mulN_row_0 b
  · exact mulN_row_1 b
  · exact mulN_row_2 b
  · exact mulN_row_3 b
  · exact mulN_row_4 b
  · exact mulN_row_5 b
  · exact mulN_row_6 b
  · exact mulN_row_7 b
  · exact mulN_row_8 b
  · exact mulN_row_9 b
  · exact mulN_row_10 b
  · exact mulN_row_11 b
  · exact mulN_row_12 b
  · exact mulN_row_13 b
  · exact mulN_row_14 b
  · exact mulN_row_15 b
  · exact mulN_row_16 b
  · exact mulN_row_17 b
  · exact mulN_row_18 b
  · exact mulN_row_19 b
  · exact mulN_row_20 b
  · exact mulN_row_21 b
  · exact mulN_row_22 b
  · exact mulN_row_23 b
  · exact mulN_row_24 b
  · exact mulN_row_25 b
  · exact mulN_row_26 b
  · exact mulN_row_27 b
  · exact mulN_row_28 b
  · exact mulN_row_29 b
  · exact mulN_row_30 b
  · exact mulN_row_31 b
  · exact mulN_row_32 b
  · exact mulN_row_33 b
  · exact mulN_row_34 b
  · exact mulN_row_35 b
  · exact mulN_row_36 b
  · exact mulN_row_37 b
  · exact mulN_row_38 b
  · exact mulN_row_39 b
  · exact mulN_row_40 b
  · exact mulN_row_41 b
  · exact mulN_row_42 b
  · exact mulN_row_43 b
  · exact mulN_row_44 b
  · exact mulN_row_45 b
  · exact mulN_row_46 b
  · exact mulN_row_47 b
  · exact mulN_row_48 b
  · exact mulN_row_49 b
  · exact mulN_row_50 b
  · exact mulN_row_51 b
  · exact mulN_row_52 b
  · exact mulN_row_53 b
  · exact mulN_row_54 b
  · exact mulN_row_55 b
  · exact mulN_row_56 b
  · exact mulN_row_57 b
  · exact mulN_row_58 b
  · exact mulN_row_59 b
  · exact mulN_row_60 b
  · exact mulN_row_61 b
  · exact mulN_row_62 b
  · exact mulN_row_63 b

def sqIterN : Nat → Fin 64 → Fin 64
  | 0, a => a
  | n + 1, a => mulN (sqIterN n a) (sqIterN n a)

theorem toK_sqIterN (n : Nat) (a : Fin 64) :
    toK (sqIterN n a) = sqIterK n (toK a) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [sqIterN, sqIterK]
      rw [toK_mulN, ih]
      rfl

def bitN (z i : Nat) : Bool := decide ((z / 2^i) % 2 = 1)
def toW (z : Fin 4) : W := (bitN z.val 0, bitN z.val 1)
def addWN (a b : Fin 4) : Fin 4 :=
  ⟨Nat.xor a.val b.val % 4, Nat.mod_lt _ (by decide)⟩

theorem toW_addWN (a b : Fin 4) : toW (addWN a b) = toW a + toW b := by
  revert a b
  decide +kernel

def LCode (z : Nat) : Nat :=
  ((z / 8) % 2) +
  2 * (((z % 2) + ((z / 2) % 2) + ((z / 4) % 2) + ((z / 8) % 2) +
    ((z / 16) % 2) + ((z / 32) % 2)) % 2)

def LN (z : Fin 64) : Fin 4 := ⟨LCode z.val % 4, Nat.mod_lt _ (by decide)⟩

theorem toW_LN (z : Fin 64) : toW (LN z) = L (toK z) := by
  revert z
  decide +kernel

def T7N (u v w : Fin 64) : Fin 4 :=
  LN (mulN (mulN (sqIterN 2 u) (sqIterN 1 v)) w)

def T21N (u v w : Fin 64) : Fin 4 :=
  LN (mulN (mulN (sqIterN 4 u) (sqIterN 2 v)) w)

theorem toW_T7N (u v w : Fin 64) :
    toW (T7N u v w) = T7 (toK u) (toK v) (toK w) := by
  unfold T7N T7
  rw [toW_LN, toK_mulN, toK_mulN, toK_sqIterN, toK_sqIterN]

theorem toW_T21N (u v w : Fin 64) :
    toW (T21N u v w) = T21 (toK u) (toK v) (toK w) := by
  unfold T21N T21
  rw [toW_LN, toK_mulN, toK_mulN, toK_sqIterN, toK_sqIterN]

def symmN (T : Fin 64 → Fin 64 → Fin 64 → Fin 4) (a b c : Fin 64) : Fin 4 :=
  addWN (addWN (addWN (addWN (addWN
    (T a b c) (T a c b)) (T b a c)) (T b c a)) (T c a b)) (T c b a)

theorem toW_symmN (T : Fin 64 → Fin 64 → Fin 64 → Fin 4)
    (U : K → K → K → W)
    (h : ∀ a b c, toW (T a b c) = U (toK a) (toK b) (toK c))
    (a b c : Fin 64) :
    toW (symmN T a b c) = symm3 U (toK a) (toK b) (toK c) := by
  simp only [symmN, symm3, toW_addWN, h]

def tensor1N (a b c : Fin 64) : Fin 4 := symmN T7N a b c
def tensor2N (a b c : Fin 64) : Fin 4 :=
  addWN (symmN T7N a b c) (symmN T21N a b c)

theorem toW_tensor1N (a b c : Fin 64) :
    toW (tensor1N a b c) = symm3 T7 (toK a) (toK b) (toK c) := by
  exact toW_symmN T7N T7 toW_T7N a b c

theorem toW_tensor2N (a b c : Fin 64) :
    toW (tensor2N a b c) =
      symm3 T7 (toK a) (toK b) (toK c) +
      symm3 T21 (toK a) (toK b) (toK c) := by
  unfold tensor2N
  rw [toW_addWN, toW_symmN T7N T7 toW_T7N, toW_symmN T21N T21 toW_T21N]

theorem toW_tensor1N_yTensor (a b c : Fin 64) :
    toW (tensor1N a b c) = yTensor₁ (toK a) (toK b) (toK c) := by
  rw [toW_tensor1N]
  unfold yTensor₁
  symm
  exact thirdDiff_L_pow7 (toK a) (toK b) (toK c) 0

theorem toW_tensor2N_yTensor (a b c : Fin 64) :
    toW (tensor2N a b c) = yTensor₂ (toK a) (toK b) (toK c) := by
  rw [toW_tensor2N]
  unfold yTensor₂
  rw [thirdDiff_add, thirdDiff_L_pow7, thirdDiff_L_pow21]

theorem toK_bijective : Function.Bijective toK := by
  decide +kernel

noncomputable def toKEquiv : Fin 64 ≃ K := Equiv.ofBijective toK toK_bijective

theorem toW_injective : Function.Injective toW := by
  decide +kernel

abbrev RawDirectionTriple := Fin 64 × Fin 64 × Fin 64

def RawTripleZero (T : Fin 64 → Fin 64 → Fin 64 → Fin 4) :=
  {d : RawDirectionTriple // T d.1 d.2.1 d.2.2 = 0}

noncomputable local instance rawTripleZeroFinite
    (T : Fin 64 → Fin 64 → Fin 64 → Fin 4) : Finite (RawTripleZero T) :=
  Finite.of_injective Subtype.val Subtype.val_injective

noncomputable def rawThirdZeroCount
    (T : Fin 64 → Fin 64 → Fin 64 → Fin 4) : Nat :=
  Nat.card (RawTripleZero T)

noncomputable def rawZeroEquiv
    (T : Fin 64 → Fin 64 → Fin 64 → Fin 4)
    (U : K → K → K → W)
    (h : ∀ a b c, toW (T a b c) = U (toK a) (toK b) (toK c)) :
    RawTripleZero T ≃ YTripleZero U where
  toFun d :=
    ⟨(toK d.1.1, toK d.1.2.1, toK d.1.2.2), by
      rw [← h]
      rw [d.2]
      rfl⟩
  invFun d := by
    let a := toKEquiv.symm d.1.1
    let b := toKEquiv.symm d.1.2.1
    let c := toKEquiv.symm d.1.2.2
    refine ⟨(a, b, c), ?_⟩
    apply toW_injective
    rw [h]
    change U (toK a) (toK b) (toK c) = 0
    have ha : toK a = d.1.1 := by
      change toKEquiv a = d.1.1
      exact toKEquiv.apply_symm_apply d.1.1
    have hb : toK b = d.1.2.1 := by
      change toKEquiv b = d.1.2.1
      exact toKEquiv.apply_symm_apply d.1.2.1
    have hc : toK c = d.1.2.2 := by
      change toKEquiv c = d.1.2.2
      exact toKEquiv.apply_symm_apply d.1.2.2
    rw [ha, hb, hc]
    exact d.2
  left_inv := by
    intro d
    apply Subtype.ext
    apply Prod.ext
    · change toKEquiv.symm (toKEquiv d.1.1) = d.1.1
      exact toKEquiv.symm_apply_apply d.1.1
    · apply Prod.ext
      · change toKEquiv.symm (toKEquiv d.1.2.1) = d.1.2.1
        exact toKEquiv.symm_apply_apply d.1.2.1
      · change toKEquiv.symm (toKEquiv d.1.2.2) = d.1.2.2
        exact toKEquiv.symm_apply_apply d.1.2.2
  right_inv := by
    intro d
    apply Subtype.ext
    apply Prod.ext
    · change toKEquiv (toKEquiv.symm d.1.1) = d.1.1
      exact toKEquiv.apply_symm_apply d.1.1
    · apply Prod.ext
      · change toKEquiv (toKEquiv.symm d.1.2.1) = d.1.2.1
        exact toKEquiv.apply_symm_apply d.1.2.1
      · change toKEquiv (toKEquiv.symm d.1.2.2) = d.1.2.2
        exact toKEquiv.apply_symm_apply d.1.2.2

theorem yThirdZeroCount_eq_raw
    (T : Fin 64 → Fin 64 → Fin 64 → Fin 4)
    (U : K → K → K → W)
    (h : ∀ a b c, toW (T a b c) = U (toK a) (toK b) (toK c)) :
    yThirdZeroCount U = rawThirdZeroCount T := by
  unfold yThirdZeroCount rawThirdZeroCount
  have hy : Nat.card (YTripleZero U) =
      @Fintype.card (YTripleZero U) (Fintype.ofFinite _) :=
    @Nat.card_eq_fintype_card (YTripleZero U) (Fintype.ofFinite _)
  exact hy.symm.trans (Nat.card_congr (rawZeroEquiv T U h)).symm

theorem yCount1_eq_raw :
    yThirdZeroCount yTensor₁ = rawThirdZeroCount tensor1N :=
  yThirdZeroCount_eq_raw tensor1N yTensor₁ toW_tensor1N_yTensor

theorem yCount2_eq_raw :
    yThirdZeroCount yTensor₂ = rawThirdZeroCount tensor2N :=
  yThirdZeroCount_eq_raw tensor2N yTensor₂ toW_tensor2N_yTensor

/-- Zeros in the third-coordinate row indexed by `(a,b)`. -/
def RawRowZero (T : Fin 64 → Fin 64 → Fin 64 → Fin 4) (a b : Fin 64) :=
  {c : Fin 64 // T a b c = 0}

noncomputable local instance rawRowZeroFinite
    (T : Fin 64 → Fin 64 → Fin 64 → Fin 4) (a b : Fin 64) :
    Finite (RawRowZero T a b) :=
  Finite.of_injective Subtype.val Subtype.val_injective

noncomputable local instance rawRowZeroFintype
    (T : Fin 64 → Fin 64 → Fin 64 → Fin 4) (a b : Fin 64) :
    Fintype (RawRowZero T a b) :=
  Fintype.ofFinite _
/-- A zero triple is equivalently a choice of its first two coordinates and a zero in that row. -/
def rawTripleZeroSigmaEquiv
    (T : Fin 64 → Fin 64 → Fin 64 → Fin 4) :
    RawTripleZero T ≃ (Σ a : Fin 64, Σ b : Fin 64, RawRowZero T a b) where
  toFun d := ⟨d.1.1, d.1.2.1, ⟨d.1.2.2, d.2⟩⟩
  invFun d := ⟨(d.1, d.2.1, d.2.2.1), d.2.2.2⟩
  left_inv := by
    intro d
    rfl
  right_inv := by
    intro d
    rfl

/-- Structural row decomposition of the raw third-tensor zero count. -/
theorem rawThirdZeroCount_eq_sum_row_card
    (T : Fin 64 → Fin 64 → Fin 64 → Fin 4) :
    rawThirdZeroCount T =
      ∑ a : Fin 64, ∑ b : Fin 64, Nat.card (RawRowZero T a b) := by
  unfold rawThirdZeroCount
  rw [Nat.card_congr (rawTripleZeroSigmaEquiv T)]
  rw [Nat.card_sigma]
  apply Fintype.sum_congr
  intro a
  exact Nat.card_sigma

theorem natCard_RawRowZero_eq_filter
    (T : Fin 64 → Fin 64 → Fin 64 → Fin 4) (a b : Fin 64) :
    Nat.card (RawRowZero T a b) =
      ((Finset.univ : Finset (Fin 64)).filter fun c => T a b c = 0).card := by
  unfold RawRowZero
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

noncomputable def rowTotal
    (T : Fin 64 → Fin 64 → Fin 64 → Fin 4) (a : Fin 64) : Nat :=
  ∑ b : Fin 64, Nat.card (RawRowZero T a b)

theorem row_0 :
    rowTotal tensor1N ⟨0, by decide⟩ = 4096 ∧
    rowTotal tensor2N ⟨0, by decide⟩ = 4096 := by
  constructor <;> (unfold rowTotal; simp_rw [natCard_RawRowZero_eq_filter]; rfl)

theorem row_1 :
    rowTotal tensor1N ⟨1, by decide⟩ = 1600 ∧
    rowTotal tensor2N ⟨1, by decide⟩ = 2176 := by
  constructor <;> (unfold rowTotal; simp_rw [natCard_RawRowZero_eq_filter]; rfl)

theorem row_2 :
    rowTotal tensor1N ⟨2, by decide⟩ = 1216 ∧
    rowTotal tensor2N ⟨2, by decide⟩ = 1408 := by
  constructor <;> (unfold rowTotal; simp_rw [natCard_RawRowZero_eq_filter]; rfl)

theorem row_3 :
    rowTotal tensor1N ⟨3, by decide⟩ = 1216 ∧
    rowTotal tensor2N ⟨3, by decide⟩ = 1408 := by
  constructor <;> (unfold rowTotal; simp_rw [natCard_RawRowZero_eq_filter]; rfl)

theorem row_4 :
    rowTotal tensor1N ⟨4, by decide⟩ = 1216 ∧
    rowTotal tensor2N ⟨4, by decide⟩ = 1408 := by
  constructor <;> (unfold rowTotal; simp_rw [natCard_RawRowZero_eq_filter]; rfl)

theorem row_5 :
    rowTotal tensor1N ⟨5, by decide⟩ = 1216 ∧
    rowTotal tensor2N ⟨5, by decide⟩ = 1408 := by
  constructor <;> (unfold rowTotal; simp_rw [natCard_RawRowZero_eq_filter]; rfl)

theorem row_6 :
    rowTotal tensor1N ⟨6, by decide⟩ = 1600 ∧
    rowTotal tensor2N ⟨6, by decide⟩ = 1600 := by
  constructor <;> (unfold rowTotal; simp_rw [natCard_RawRowZero_eq_filter]; rfl)

theorem row_7 :
    rowTotal tensor1N ⟨7, by decide⟩ = 1216 ∧
    rowTotal tensor2N ⟨7, by decide⟩ = 1408 := by
  constructor <;> (unfold rowTotal; simp_rw [natCard_RawRowZero_eq_filter]; rfl)

theorem row_8 :
    rowTotal tensor1N ⟨8, by decide⟩ = 1600 ∧
    rowTotal tensor2N ⟨8, by decide⟩ = 1600 := by
  constructor <;> (unfold rowTotal; simp_rw [natCard_RawRowZero_eq_filter]; rfl)

theorem row_9 :
    rowTotal tensor1N ⟨9, by decide⟩ = 1216 ∧
    rowTotal tensor2N ⟨9, by decide⟩ = 1408 := by
  constructor <;> (unfold rowTotal; simp_rw [natCard_RawRowZero_eq_filter]; rfl)

theorem row_10 :
    rowTotal tensor1N ⟨10, by decide⟩ = 1216 ∧
    rowTotal tensor2N ⟨10, by decide⟩ = 1408 := by
  constructor <;> (unfold rowTotal; simp_rw [natCard_RawRowZero_eq_filter]; rfl)

theorem row_11 :
    rowTotal tensor1N ⟨11, by decide⟩ = 1216 ∧
    rowTotal tensor2N ⟨11, by decide⟩ = 1408 := by
  constructor <;> (unfold rowTotal; simp_rw [natCard_RawRowZero_eq_filter]; rfl)

theorem row_12 :
    rowTotal tensor1N ⟨12, by decide⟩ = 1216 ∧
    rowTotal tensor2N ⟨12, by decide⟩ = 1408 := by
  constructor <;> (unfold rowTotal; simp_rw [natCard_RawRowZero_eq_filter]; rfl)

theorem row_13 :
    rowTotal tensor1N ⟨13, by decide⟩ = 1216 ∧
    rowTotal tensor2N ⟨13, by decide⟩ = 1408 := by
  constructor <;> (unfold rowTotal; simp_rw [natCard_RawRowZero_eq_filter]; rfl)

theorem row_14 :
    rowTotal tensor1N ⟨14, by decide⟩ = 1600 ∧
    rowTotal tensor2N ⟨14, by decide⟩ = 1600 := by
  constructor <;> (unfold rowTotal; simp_rw [natCard_RawRowZero_eq_filter]; rfl)

theorem row_15 :
    rowTotal tensor1N ⟨15, by decide⟩ = 1600 ∧
    rowTotal tensor2N ⟨15, by decide⟩ = 1600 := by
  constructor <;> (unfold rowTotal; simp_rw [natCard_RawRowZero_eq_filter]; rfl)

theorem row_16 :
    rowTotal tensor1N ⟨16, by decide⟩ = 1216 ∧
    rowTotal tensor2N ⟨16, by decide⟩ = 1408 := by
  constructor <;> (unfold rowTotal; simp_rw [natCard_RawRowZero_eq_filter]; rfl)

theorem row_17 :
    rowTotal tensor1N ⟨17, by decide⟩ = 1216 ∧
    rowTotal tensor2N ⟨17, by decide⟩ = 1408 := by
  constructor <;> (unfold rowTotal; simp_rw [natCard_RawRowZero_eq_filter]; rfl)

theorem row_18 :
    rowTotal tensor1N ⟨18, by decide⟩ = 1216 ∧
    rowTotal tensor2N ⟨18, by decide⟩ = 1408 := by
  constructor <;> (unfold rowTotal; simp_rw [natCard_RawRowZero_eq_filter]; rfl)

theorem row_19 :
    rowTotal tensor1N ⟨19, by decide⟩ = 1216 ∧
    rowTotal tensor2N ⟨19, by decide⟩ = 1408 := by
  constructor <;> (unfold rowTotal; simp_rw [natCard_RawRowZero_eq_filter]; rfl)

theorem row_20 :
    rowTotal tensor1N ⟨20, by decide⟩ = 1600 ∧
    rowTotal tensor2N ⟨20, by decide⟩ = 1600 := by
  constructor <;> (unfold rowTotal; simp_rw [natCard_RawRowZero_eq_filter]; rfl)

theorem row_21 :
    rowTotal tensor1N ⟨21, by decide⟩ = 1216 ∧
    rowTotal tensor2N ⟨21, by decide⟩ = 1408 := by
  constructor <;> (unfold rowTotal; simp_rw [natCard_RawRowZero_eq_filter]; rfl)

theorem row_22 :
    rowTotal tensor1N ⟨22, by decide⟩ = 1600 ∧
    rowTotal tensor2N ⟨22, by decide⟩ = 2176 := by
  constructor <;> (unfold rowTotal; simp_rw [natCard_RawRowZero_eq_filter]; rfl)

theorem row_23 :
    rowTotal tensor1N ⟨23, by decide⟩ = 1600 ∧
    rowTotal tensor2N ⟨23, by decide⟩ = 2176 := by
  constructor <;> (unfold rowTotal; simp_rw [natCard_RawRowZero_eq_filter]; rfl)

theorem row_24 :
    rowTotal tensor1N ⟨24, by decide⟩ = 1216 ∧
    rowTotal tensor2N ⟨24, by decide⟩ = 1408 := by
  constructor <;> (unfold rowTotal; simp_rw [natCard_RawRowZero_eq_filter]; rfl)

theorem row_25 :
    rowTotal tensor1N ⟨25, by decide⟩ = 1216 ∧
    rowTotal tensor2N ⟨25, by decide⟩ = 1408 := by
  constructor <;> (unfold rowTotal; simp_rw [natCard_RawRowZero_eq_filter]; rfl)

theorem row_26 :
    rowTotal tensor1N ⟨26, by decide⟩ = 1216 ∧
    rowTotal tensor2N ⟨26, by decide⟩ = 1408 := by
  constructor <;> (unfold rowTotal; simp_rw [natCard_RawRowZero_eq_filter]; rfl)

theorem row_27 :
    rowTotal tensor1N ⟨27, by decide⟩ = 1600 ∧
    rowTotal tensor2N ⟨27, by decide⟩ = 1600 := by
  constructor <;> (unfold rowTotal; simp_rw [natCard_RawRowZero_eq_filter]; rfl)

theorem row_28 :
    rowTotal tensor1N ⟨28, by decide⟩ = 1216 ∧
    rowTotal tensor2N ⟨28, by decide⟩ = 1408 := by
  constructor <;> (unfold rowTotal; simp_rw [natCard_RawRowZero_eq_filter]; rfl)

theorem row_29 :
    rowTotal tensor1N ⟨29, by decide⟩ = 1216 ∧
    rowTotal tensor2N ⟨29, by decide⟩ = 1408 := by
  constructor <;> (unfold rowTotal; simp_rw [natCard_RawRowZero_eq_filter]; rfl)

theorem row_30 :
    rowTotal tensor1N ⟨30, by decide⟩ = 1216 ∧
    rowTotal tensor2N ⟨30, by decide⟩ = 1408 := by
  constructor <;> (unfold rowTotal; simp_rw [natCard_RawRowZero_eq_filter]; rfl)

theorem row_31 :
    rowTotal tensor1N ⟨31, by decide⟩ = 1216 ∧
    rowTotal tensor2N ⟨31, by decide⟩ = 1408 := by
  constructor <;> (unfold rowTotal; simp_rw [natCard_RawRowZero_eq_filter]; rfl)

theorem row_32 :
    rowTotal tensor1N ⟨32, by decide⟩ = 1216 ∧
    rowTotal tensor2N ⟨32, by decide⟩ = 1408 := by
  constructor <;> (unfold rowTotal; simp_rw [natCard_RawRowZero_eq_filter]; rfl)

theorem row_33 :
    rowTotal tensor1N ⟨33, by decide⟩ = 1600 ∧
    rowTotal tensor2N ⟨33, by decide⟩ = 1600 := by
  constructor <;> (unfold rowTotal; simp_rw [natCard_RawRowZero_eq_filter]; rfl)

theorem row_34 :
    rowTotal tensor1N ⟨34, by decide⟩ = 1600 ∧
    rowTotal tensor2N ⟨34, by decide⟩ = 2176 := by
  constructor <;> (unfold rowTotal; simp_rw [natCard_RawRowZero_eq_filter]; rfl)

theorem row_35 :
    rowTotal tensor1N ⟨35, by decide⟩ = 1600 ∧
    rowTotal tensor2N ⟨35, by decide⟩ = 2176 := by
  constructor <;> (unfold rowTotal; simp_rw [natCard_RawRowZero_eq_filter]; rfl)

theorem row_36 :
    rowTotal tensor1N ⟨36, by decide⟩ = 1600 ∧
    rowTotal tensor2N ⟨36, by decide⟩ = 1600 := by
  constructor <;> (unfold rowTotal; simp_rw [natCard_RawRowZero_eq_filter]; rfl)

theorem row_37 :
    rowTotal tensor1N ⟨37, by decide⟩ = 1216 ∧
    rowTotal tensor2N ⟨37, by decide⟩ = 1408 := by
  constructor <;> (unfold rowTotal; simp_rw [natCard_RawRowZero_eq_filter]; rfl)

theorem row_38 :
    rowTotal tensor1N ⟨38, by decide⟩ = 1216 ∧
    rowTotal tensor2N ⟨38, by decide⟩ = 1408 := by
  constructor <;> (unfold rowTotal; simp_rw [natCard_RawRowZero_eq_filter]; rfl)

theorem row_39 :
    rowTotal tensor1N ⟨39, by decide⟩ = 1600 ∧
    rowTotal tensor2N ⟨39, by decide⟩ = 1600 := by
  constructor <;> (unfold rowTotal; simp_rw [natCard_RawRowZero_eq_filter]; rfl)

theorem row_40 :
    rowTotal tensor1N ⟨40, by decide⟩ = 1216 ∧
    rowTotal tensor2N ⟨40, by decide⟩ = 1408 := by
  constructor <;> (unfold rowTotal; simp_rw [natCard_RawRowZero_eq_filter]; rfl)

theorem row_41 :
    rowTotal tensor1N ⟨41, by decide⟩ = 1600 ∧
    rowTotal tensor2N ⟨41, by decide⟩ = 1600 := by
  constructor <;> (unfold rowTotal; simp_rw [natCard_RawRowZero_eq_filter]; rfl)

theorem row_42 :
    rowTotal tensor1N ⟨42, by decide⟩ = 1216 ∧
    rowTotal tensor2N ⟨42, by decide⟩ = 1408 := by
  constructor <;> (unfold rowTotal; simp_rw [natCard_RawRowZero_eq_filter]; rfl)

theorem row_43 :
    rowTotal tensor1N ⟨43, by decide⟩ = 1600 ∧
    rowTotal tensor2N ⟨43, by decide⟩ = 1600 := by
  constructor <;> (unfold rowTotal; simp_rw [natCard_RawRowZero_eq_filter]; rfl)

theorem row_44 :
    rowTotal tensor1N ⟨44, by decide⟩ = 1216 ∧
    rowTotal tensor2N ⟨44, by decide⟩ = 1408 := by
  constructor <;> (unfold rowTotal; simp_rw [natCard_RawRowZero_eq_filter]; rfl)

theorem row_45 :
    rowTotal tensor1N ⟨45, by decide⟩ = 1216 ∧
    rowTotal tensor2N ⟨45, by decide⟩ = 1408 := by
  constructor <;> (unfold rowTotal; simp_rw [natCard_RawRowZero_eq_filter]; rfl)

theorem row_46 :
    rowTotal tensor1N ⟨46, by decide⟩ = 1216 ∧
    rowTotal tensor2N ⟨46, by decide⟩ = 1408 := by
  constructor <;> (unfold rowTotal; simp_rw [natCard_RawRowZero_eq_filter]; rfl)

theorem row_47 :
    rowTotal tensor1N ⟨47, by decide⟩ = 1600 ∧
    rowTotal tensor2N ⟨47, by decide⟩ = 1600 := by
  constructor <;> (unfold rowTotal; simp_rw [natCard_RawRowZero_eq_filter]; rfl)

theorem row_48 :
    rowTotal tensor1N ⟨48, by decide⟩ = 1600 ∧
    rowTotal tensor2N ⟨48, by decide⟩ = 1600 := by
  constructor <;> (unfold rowTotal; simp_rw [natCard_RawRowZero_eq_filter]; rfl)

theorem row_49 :
    rowTotal tensor1N ⟨49, by decide⟩ = 1216 ∧
    rowTotal tensor2N ⟨49, by decide⟩ = 1408 := by
  constructor <;> (unfold rowTotal; simp_rw [natCard_RawRowZero_eq_filter]; rfl)

theorem row_50 :
    rowTotal tensor1N ⟨50, by decide⟩ = 1216 ∧
    rowTotal tensor2N ⟨50, by decide⟩ = 1408 := by
  constructor <;> (unfold rowTotal; simp_rw [natCard_RawRowZero_eq_filter]; rfl)

theorem row_51 :
    rowTotal tensor1N ⟨51, by decide⟩ = 1216 ∧
    rowTotal tensor2N ⟨51, by decide⟩ = 1408 := by
  constructor <;> (unfold rowTotal; simp_rw [natCard_RawRowZero_eq_filter]; rfl)

theorem row_52 :
    rowTotal tensor1N ⟨52, by decide⟩ = 1600 ∧
    rowTotal tensor2N ⟨52, by decide⟩ = 2176 := by
  constructor <;> (unfold rowTotal; simp_rw [natCard_RawRowZero_eq_filter]; rfl)

theorem row_53 :
    rowTotal tensor1N ⟨53, by decide⟩ = 1600 ∧
    rowTotal tensor2N ⟨53, by decide⟩ = 2176 := by
  constructor <;> (unfold rowTotal; simp_rw [natCard_RawRowZero_eq_filter]; rfl)

theorem row_54 :
    rowTotal tensor1N ⟨54, by decide⟩ = 1216 ∧
    rowTotal tensor2N ⟨54, by decide⟩ = 1408 := by
  constructor <;> (unfold rowTotal; simp_rw [natCard_RawRowZero_eq_filter]; rfl)

theorem row_55 :
    rowTotal tensor1N ⟨55, by decide⟩ = 1216 ∧
    rowTotal tensor2N ⟨55, by decide⟩ = 1408 := by
  constructor <;> (unfold rowTotal; simp_rw [natCard_RawRowZero_eq_filter]; rfl)

theorem row_56 :
    rowTotal tensor1N ⟨56, by decide⟩ = 1216 ∧
    rowTotal tensor2N ⟨56, by decide⟩ = 1408 := by
  constructor <;> (unfold rowTotal; simp_rw [natCard_RawRowZero_eq_filter]; rfl)

theorem row_57 :
    rowTotal tensor1N ⟨57, by decide⟩ = 1216 ∧
    rowTotal tensor2N ⟨57, by decide⟩ = 1408 := by
  constructor <;> (unfold rowTotal; simp_rw [natCard_RawRowZero_eq_filter]; rfl)

theorem row_58 :
    rowTotal tensor1N ⟨58, by decide⟩ = 1216 ∧
    rowTotal tensor2N ⟨58, by decide⟩ = 1408 := by
  constructor <;> (unfold rowTotal; simp_rw [natCard_RawRowZero_eq_filter]; rfl)

theorem row_59 :
    rowTotal tensor1N ⟨59, by decide⟩ = 1216 ∧
    rowTotal tensor2N ⟨59, by decide⟩ = 1408 := by
  constructor <;> (unfold rowTotal; simp_rw [natCard_RawRowZero_eq_filter]; rfl)

theorem row_60 :
    rowTotal tensor1N ⟨60, by decide⟩ = 1216 ∧
    rowTotal tensor2N ⟨60, by decide⟩ = 1408 := by
  constructor <;> (unfold rowTotal; simp_rw [natCard_RawRowZero_eq_filter]; rfl)

theorem row_61 :
    rowTotal tensor1N ⟨61, by decide⟩ = 1216 ∧
    rowTotal tensor2N ⟨61, by decide⟩ = 1408 := by
  constructor <;> (unfold rowTotal; simp_rw [natCard_RawRowZero_eq_filter]; rfl)

theorem row_62 :
    rowTotal tensor1N ⟨62, by decide⟩ = 1216 ∧
    rowTotal tensor2N ⟨62, by decide⟩ = 1408 := by
  constructor <;> (unfold rowTotal; simp_rw [natCard_RawRowZero_eq_filter]; rfl)

theorem row_63 :
    rowTotal tensor1N ⟨63, by decide⟩ = 1600 ∧
    rowTotal tensor2N ⟨63, by decide⟩ = 1600 := by
  constructor <;> (unfold rowTotal; simp_rw [natCard_RawRowZero_eq_filter]; rfl)

def expected1 (a : Fin 64) : Nat :=
  match a.val with
  | 0 => 4096
  | 1 => 1600
  | 2 => 1216
  | 3 => 1216
  | 4 => 1216
  | 5 => 1216
  | 6 => 1600
  | 7 => 1216
  | 8 => 1600
  | 9 => 1216
  | 10 => 1216
  | 11 => 1216
  | 12 => 1216
  | 13 => 1216
  | 14 => 1600
  | 15 => 1600
  | 16 => 1216
  | 17 => 1216
  | 18 => 1216
  | 19 => 1216
  | 20 => 1600
  | 21 => 1216
  | 22 => 1600
  | 23 => 1600
  | 24 => 1216
  | 25 => 1216
  | 26 => 1216
  | 27 => 1600
  | 28 => 1216
  | 29 => 1216
  | 30 => 1216
  | 31 => 1216
  | 32 => 1216
  | 33 => 1600
  | 34 => 1600
  | 35 => 1600
  | 36 => 1600
  | 37 => 1216
  | 38 => 1216
  | 39 => 1600
  | 40 => 1216
  | 41 => 1600
  | 42 => 1216
  | 43 => 1600
  | 44 => 1216
  | 45 => 1216
  | 46 => 1216
  | 47 => 1600
  | 48 => 1600
  | 49 => 1216
  | 50 => 1216
  | 51 => 1216
  | 52 => 1600
  | 53 => 1600
  | 54 => 1216
  | 55 => 1216
  | 56 => 1216
  | 57 => 1216
  | 58 => 1216
  | 59 => 1216
  | 60 => 1216
  | 61 => 1216
  | 62 => 1216
  | 63 => 1600
  | _ => 0

def expected2 (a : Fin 64) : Nat :=
  match a.val with
  | 0 => 4096
  | 1 => 2176
  | 2 => 1408
  | 3 => 1408
  | 4 => 1408
  | 5 => 1408
  | 6 => 1600
  | 7 => 1408
  | 8 => 1600
  | 9 => 1408
  | 10 => 1408
  | 11 => 1408
  | 12 => 1408
  | 13 => 1408
  | 14 => 1600
  | 15 => 1600
  | 16 => 1408
  | 17 => 1408
  | 18 => 1408
  | 19 => 1408
  | 20 => 1600
  | 21 => 1408
  | 22 => 2176
  | 23 => 2176
  | 24 => 1408
  | 25 => 1408
  | 26 => 1408
  | 27 => 1600
  | 28 => 1408
  | 29 => 1408
  | 30 => 1408
  | 31 => 1408
  | 32 => 1408
  | 33 => 1600
  | 34 => 2176
  | 35 => 2176
  | 36 => 1600
  | 37 => 1408
  | 38 => 1408
  | 39 => 1600
  | 40 => 1408
  | 41 => 1600
  | 42 => 1408
  | 43 => 1600
  | 44 => 1408
  | 45 => 1408
  | 46 => 1408
  | 47 => 1600
  | 48 => 1600
  | 49 => 1408
  | 50 => 1408
  | 51 => 1408
  | 52 => 2176
  | 53 => 2176
  | 54 => 1408
  | 55 => 1408
  | 56 => 1408
  | 57 => 1408
  | 58 => 1408
  | 59 => 1408
  | 60 => 1408
  | 61 => 1408
  | 62 => 1408
  | 63 => 1600
  | _ => 0

theorem rowTotal_tensor1N_exact (a : Fin 64) : rowTotal tensor1N a = expected1 a := by
  fin_cases a
  · exact row_0.1
  · exact row_1.1
  · exact row_2.1
  · exact row_3.1
  · exact row_4.1
  · exact row_5.1
  · exact row_6.1
  · exact row_7.1
  · exact row_8.1
  · exact row_9.1
  · exact row_10.1
  · exact row_11.1
  · exact row_12.1
  · exact row_13.1
  · exact row_14.1
  · exact row_15.1
  · exact row_16.1
  · exact row_17.1
  · exact row_18.1
  · exact row_19.1
  · exact row_20.1
  · exact row_21.1
  · exact row_22.1
  · exact row_23.1
  · exact row_24.1
  · exact row_25.1
  · exact row_26.1
  · exact row_27.1
  · exact row_28.1
  · exact row_29.1
  · exact row_30.1
  · exact row_31.1
  · exact row_32.1
  · exact row_33.1
  · exact row_34.1
  · exact row_35.1
  · exact row_36.1
  · exact row_37.1
  · exact row_38.1
  · exact row_39.1
  · exact row_40.1
  · exact row_41.1
  · exact row_42.1
  · exact row_43.1
  · exact row_44.1
  · exact row_45.1
  · exact row_46.1
  · exact row_47.1
  · exact row_48.1
  · exact row_49.1
  · exact row_50.1
  · exact row_51.1
  · exact row_52.1
  · exact row_53.1
  · exact row_54.1
  · exact row_55.1
  · exact row_56.1
  · exact row_57.1
  · exact row_58.1
  · exact row_59.1
  · exact row_60.1
  · exact row_61.1
  · exact row_62.1
  · exact row_63.1

theorem rowTotal_tensor2N_exact (a : Fin 64) : rowTotal tensor2N a = expected2 a := by
  fin_cases a
  · exact row_0.2
  · exact row_1.2
  · exact row_2.2
  · exact row_3.2
  · exact row_4.2
  · exact row_5.2
  · exact row_6.2
  · exact row_7.2
  · exact row_8.2
  · exact row_9.2
  · exact row_10.2
  · exact row_11.2
  · exact row_12.2
  · exact row_13.2
  · exact row_14.2
  · exact row_15.2
  · exact row_16.2
  · exact row_17.2
  · exact row_18.2
  · exact row_19.2
  · exact row_20.2
  · exact row_21.2
  · exact row_22.2
  · exact row_23.2
  · exact row_24.2
  · exact row_25.2
  · exact row_26.2
  · exact row_27.2
  · exact row_28.2
  · exact row_29.2
  · exact row_30.2
  · exact row_31.2
  · exact row_32.2
  · exact row_33.2
  · exact row_34.2
  · exact row_35.2
  · exact row_36.2
  · exact row_37.2
  · exact row_38.2
  · exact row_39.2
  · exact row_40.2
  · exact row_41.2
  · exact row_42.2
  · exact row_43.2
  · exact row_44.2
  · exact row_45.2
  · exact row_46.2
  · exact row_47.2
  · exact row_48.2
  · exact row_49.2
  · exact row_50.2
  · exact row_51.2
  · exact row_52.2
  · exact row_53.2
  · exact row_54.2
  · exact row_55.2
  · exact row_56.2
  · exact row_57.2
  · exact row_58.2
  · exact row_59.2
  · exact row_60.2
  · exact row_61.2
  · exact row_62.2
  · exact row_63.2

theorem rawThirdZeroCount_tensor1N_exact : rawThirdZeroCount tensor1N = 88768 := by
  rw [rawThirdZeroCount_eq_sum_row_card]
  change (∑ a : Fin 64, rowTotal tensor1N a) = 88768
  simp_rw [rowTotal_tensor1N_exact]
  rfl

theorem rawThirdZeroCount_tensor2N_exact : rawThirdZeroCount tensor2N = 100864 := by
  rw [rawThirdZeroCount_eq_sum_row_card]
  change (∑ a : Fin 64, rowTotal tensor2N a) = 100864
  simp_rw [rowTotal_tensor2N_exact]
  rfl

theorem yThirdZeroCount_G₁_exact :
    yThirdZeroCount yTensor₁ = 88768 :=
  yCount1_eq_raw.trans rawThirdZeroCount_tensor1N_exact

theorem yThirdZeroCount_G₂_exact :
    yThirdZeroCount yTensor₂ = 100864 :=
  yCount2_eq_raw.trans rawThirdZeroCount_tensor2N_exact

theorem thirdZeroCount_G₁_exact :
    thirdZeroCount G₁ = 23269998592 := by
  rw [thirdZeroCount_G₁_factor, yThirdZeroCount_G₁_exact]
  norm_num

theorem thirdZeroCount_G₂_exact :
    thirdZeroCount G₂ = 26440892416 := by
  rw [thirdZeroCount_G₂_factor, yThirdZeroCount_G₂_exact]
  norm_num

theorem G₁_not_EAEquivalent_G₂ : ¬ EAEquivalent G₁ G₂ := by
  intro hEA
  have hcount := thirdZeroCount_ea_invariant G₁_degreeLE3 hEA
  rw [thirdZeroCount_G₁_exact, thirdZeroCount_G₂_exact] at hcount
  norm_num at hcount

def IsCubic (F : V → W) : Prop :=
  DegreeLE3 F ∧ ¬ DegreeLE2 F

def SameDegreeV1Witness (F G : V → W) : Prop :=
  IsStandardVectorialBent F ∧
  IsStandardVectorialBent G ∧
  IsCubic F ∧
  IsCubic G ∧
  Nonempty (StandardDevelopmentIso F G) ∧
  ¬ EAEquivalent F G

theorem G₁_G₂_sameDegreeV1Witness :
    SameDegreeV1Witness G₁ G₂ := by
  refine ⟨G₁_isStandardVectorialBent, G₂_isStandardVectorialBent, ?_, ?_,
    standard_cubic_developments_are_isomorphic, G₁_not_EAEquivalent_G₂⟩
  · exact G₁_degree_exactly_three
  · exact G₂_degree_exactly_three

/-- Same-degree affirmative solution of Polujan--Pott Open Problem V.1:
two cubic vectorial (12,2)-bent maps have isomorphic graph translation
developments while lying in different EA-equivalence classes. -/
theorem polujanPottV1_sameDegree_affirmative :
    ∃ F G : V → W, SameDegreeV1Witness F G :=
  ⟨G₁, G₂, G₁_G₂_sameDegreeV1Witness⟩

end PolujanPottV1
