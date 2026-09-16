import Mathlib

set_option maxHeartbeats 800000

/-!
A self-contained formalization of Polujan's Problem 3.65.

For vectorial bent maps in the Nyberg range, a permutation preserves their
vanishing flats exactly when the maps are EA-equivalent.  Every declaration
used by the proof is collected in this namespace; only Mathlib is imported.
-/

namespace Mathproof.Polujan365
open scoped BigOperators
/-! Concrete binary Walsh analysis for the bent-graph spectral certificate.
Characters, orthogonality, inversion and Parseval are proved, not assumed. -/
abbrev Bit := ZMod 2
abbrev Cube (ι : Type*) := ι → Bit

theorem bit_cases (x : Bit) : x=0 ∨ x=1 :=
  (by decide : ∀ x : ZMod 2, x=0 ∨ x=1) x

def sign (x : Bit) : ℝ := if x=0 then 1 else -1

@[simp] theorem sign_zero : sign 0=1 := by simp [sign]
@[simp] theorem sign_one : sign 1 = -1 := by norm_num [sign]

theorem sign_add (x y : Bit) : sign (x+y)=sign x*sign y := by
  rcases bit_cases x with rfl | rfl
  · rw [zero_add, sign_zero, one_mul]
  · rcases bit_cases y with rfl | rfl
    · rw [add_zero, sign_zero, mul_one]
    · rw [show (1 : Bit)+1=0 from rfl, sign_zero, sign_one]
      norm_num

theorem sign_sq (x : Bit) : (sign x)^2=1 := by
  rcases bit_cases x with rfl | rfl <;> norm_num

theorem twice {V : Type*} [AddCommGroup V] [Module Bit V] (v : V) : v+v=0 := by
  have he : (2 : Bit) • v=0 := by rw [show (2 : Bit)=0 from rfl, zero_smul]
  simpa only [two_smul] using he

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
noncomputable def char (u x : Cube ι) : ℝ := sign (dotProduct u x)
def size (ι : Type*) [Fintype ι] [DecidableEq ι] : ℝ := Fintype.card (Cube ι)

@[simp] theorem char_zero_right (u : Cube ι) : char u 0=1 := by simp [char]
@[simp] theorem char_zero_left (x : Cube ι) : char 0 x=1 := by simp [char]
theorem char_comm (u x : Cube ι) : char u x=char x u := by
  unfold char
  congr 1
  exact dotProduct_comm _ _
theorem char_add_right (u x y : Cube ι) : char u (x+y)=char u x*char u y := by
  simp only [char, dotProduct_add, sign_add]
theorem char_add_left (u v x : Cube ι) : char (u+v) x=char u x*char v x := by
  simp only [char, add_dotProduct, sign_add]
theorem char_sq (u x : Cube ι) : (char u x)^2=1 := sign_sq _

theorem char_sum (u : Cube ι) : (∑ x, char u x)=if u=0 then size ι else 0 := by
  classical
  by_cases hu : u=0
  · simp [hu, size]
  · rw [if_neg hu]
    obtain ⟨i,hi⟩ : ∃ i, u i ≠ 0 := by
      by_contra hh
      apply hu
      funext i
      exact not_not.mp (fun h => hh ⟨i,h⟩)
    have hui : u i=1 := (bit_cases (u i)).resolve_left hi
    let e : Cube ι := Pi.single i 1
    have hce : char u e = -1 := by
      simp only [char, e, dotProduct_single_one, hui, sign_one]
    have hs := Equiv.sum_comp (Equiv.addRight e) (fun x => char u x)
    change (∑ x, char u (x+e)) = ∑ x, char u x at hs
    simp_rw [char_add_right, hce, mul_neg_one] at hs
    rw [Finset.sum_neg_distrib] at hs
    linarith

theorem add_zero_iff (x y : Cube ι) : x+y=0 ↔ x=y := by
  constructor
  · intro h
    have he := congrArg (fun z => z+y) h
    simpa only [add_assoc, twice, add_zero, zero_add] using he
  · rintro rfl
    exact twice x

theorem char_orthogonal (x y : Cube ι) :
    (∑ u, char u x*char u y)=if x=y then size ι else 0 := by
  calc
    _ = ∑ u, char (x+y) u := by
      apply Finset.sum_congr rfl
      intro u _
      rw [← char_add_right, char_comm]
    _ = _ := by rw [char_sum]; simp only [add_zero_iff]

noncomputable def walsh (f : Cube ι → ℝ) (u : Cube ι) : ℝ :=
  ∑ x, f x*char u x

/-- Unnormalized Walsh inversion with a concrete binary character system. -/
theorem inversion (f : Cube ι → ℝ) (x : Cube ι) :
    (∑ u, walsh f u*char u x)=size ι*f x := by
  classical
  simp only [walsh, Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    (∑ y, ∑ u, f y*char u y*char u x) =
        ∑ y, f y*(∑ u, char u y*char u x) := by
      simp_rw [Finset.mul_sum, mul_assoc]
    _ = ∑ y, f y*(if y=x then size ι else 0) := by simp_rw [char_orthogonal]
    _ = size ι*f x := by simp; ring

theorem bilinear_parseval (f g : Cube ι → ℝ) :
    (∑ u, walsh f u*walsh g u)=size ι*(∑ x, f x*g x) := by
  calc
    _ = ∑ u, ∑ x, walsh f u*(g x*char u x) := by simp only [walsh, Finset.mul_sum]
    _ = ∑ x, g x*(∑ u, walsh f u*char u x) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      ring
    _ = ∑ x, g x*(size ι*f x) := by simp_rw [inversion]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring

theorem parseval (f : Cube ι → ℝ) :
    (∑ u, (walsh f u)^2)=size ι*(∑ x, (f x)^2) := by
  simpa only [pow_two] using bilinear_parseval f f

theorem size_pos : 0 < size ι := by
  unfold size
  exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Cube ι))

theorem walsh_injective : Function.Injective (walsh (ι := ι)) := by
  intro f g hfg
  funext x
  have hf := inversion f x
  have hg := inversion g x
  rw [hfg] at hf
  have hn := size_pos (ι := ι)
  nlinarith

theorem walsh_translate (f : Cube ι → ℝ) (a u : Cube ι) :
    walsh (fun x => f (x+a)) u = char u a*walsh f u := by
  have hs := Equiv.sum_comp (Equiv.addRight a) (fun x => f (x+a)*char u x)
  change (∑ x, f ((x+a)+a)*char u (x+a))=walsh (fun x => f (x+a)) u at hs
  simp_rw [add_assoc, twice, add_zero, char_add_right] at hs
  rw [← hs, walsh, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

def FlatSpectrum (B : ℝ) (f : Cube ι → ℝ) : Prop :=
  ∀ u, (walsh f u)^2=B^2

/-- Flat Walsh spectrum implies balanced nonzero autocorrelations. -/
theorem flat_autocorrelation (B : ℝ) (f : Cube ι → ℝ)
    (hB : B^2=size ι) (hf : FlatSpectrum B f) (a : Cube ι) (ha : a≠0) :
    (∑ x, f x*f (x+a))=0 := by
  have hp := bilinear_parseval f (fun x => f (x+a))
  simp_rw [walsh_translate] at hp
  have he : (∑ u, walsh f u*(char u a*walsh f u))=0 := by
    calc
      _ = ∑ u, (walsh f u)^2*char u a := by
        apply Finset.sum_congr rfl
        intro u _
        ring
      _ = size ι*(∑ u, char a u) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u _
        rw [hf, hB, char_comm]
      _ = 0 := by rw [char_sum, if_neg ha, mul_zero]
  rw [he] at hp
  have hn := size_pos (ι := ι)
  nlinarith


variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def VectorialBent (B : ℝ) (F : Cube ι → Cube κ) : Prop :=
  ∀ mu : Cube κ, mu≠0 → FlatSpectrum B (fun x => char mu (F x))

theorem derivative_character_sum (B : ℝ) (F : Cube ι → Cube κ)
    (hB : B^2=size ι) (hF : VectorialBent B F)
    (a : Cube ι) (ha : a≠0) (mu : Cube κ) :
    (∑ x, char mu (F x+F (x+a)))=if mu=0 then size ι else 0 := by
  classical
  by_cases hmu : mu=0
  · simp [hmu, size]
  · rw [if_neg hmu]
    simpa only [char_add_right] using
      flat_autocorrelation B (fun x => char mu (F x)) hB (hF mu hmu) a ha

/-- Exact differential balance derived from concrete Walsh bentness. -/
theorem derivative_count (B : ℝ) (F : Cube ι → Cube κ)
    (hB : B^2=size ι) (hF : VectorialBent B F)
    (a : Cube ι) (ha : a≠0) (v : Cube κ) :
    (∑ x, if F x+F (x+a)=v then (1 : ℝ) else 0)=size ι/size κ := by
  classical
  have he : size κ*(∑ x, if F x+F (x+a)=v then (1 : ℝ) else 0)=size ι := by
    calc
      _ = ∑ x, (if F x+F (x+a)=v then size κ else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        split_ifs <;> simp
      _ = ∑ x, ∑ mu, char mu (F x+F (x+a))*char mu v := by
        simp only [char_orthogonal]
      _ = ∑ mu, (∑ x, char mu (F x+F (x+a)))*char mu v := by
        rw [Finset.sum_comm]
        simp only [Finset.sum_mul]
      _ = size ι := by
        simp_rw [derivative_character_sum B F hB hF a ha]
        simp
  apply (eq_div_iff (ne_of_gt (size_pos (ι := κ)))).mpr
  nlinarith

theorem sign_abs (x : Bit) : |sign x|=1 := by
  rcases bit_cases x with rfl | rfl <;> norm_num
theorem char_abs (u x : Cube ι) : |char u x|=1 := sign_abs _

theorem sign_injective : Function.Injective sign := by
  intro x y he
  rcases bit_cases x with rfl | rfl <;> rcases bit_cases y with rfl | rfl <;>
    norm_num at *

theorem walsh_disagreement_bound (f g : Cube ι → Bit) (u : Cube ι) :
    |walsh (fun x => sign (f x)) u-walsh (fun x => sign (g x)) u| ≤
      2*((Finset.univ.filter (fun x => f x≠g x)).card : ℝ) := by
  classical
  have he : walsh (fun x => sign (f x)) u-walsh (fun x => sign (g x)) u =
      ∑ x, (sign (f x)-sign (g x))*char u x := by
    simp only [walsh, sub_mul, Finset.sum_sub_distrib]
  rw [he]
  calc
    _ ≤ ∑ x, |(sign (f x)-sign (g x))*char u x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, (if f x≠g x then (2 : ℝ) else 0) := by
      apply Finset.sum_le_sum
      intro x _
      by_cases hx : f x=g x
      · simp [hx]
      · rw [if_pos hx, abs_mul, char_abs, mul_one]
        have hb := abs_sub_le (sign (f x)) 0 (sign (g x))
        simp only [sub_zero, zero_sub, abs_neg, sign_abs] at hb
        linarith
    _ = _ := by rw [← Finset.sum_filter]; simp; ring

/-- Two bent Boolean functions agreeing off fewer than B points are identical. -/
theorem bent_erasure_unique (B : ℝ) (f g : Cube ι → Bit)
    (hf : FlatSpectrum B (fun x => sign (f x)))
    (hg : FlatSpectrum B (fun x => sign (g x)))
    (hd : ((Finset.univ.filter (fun x => f x≠g x)).card : ℝ)<B) : f=g := by
  classical
  have hw : walsh (fun x => sign (f x))=walsh (fun x => sign (g x)) := by
    funext u
    have hb := walsh_disagreement_bound f g u
    have hb' : |walsh (fun x => sign (f x)) u-walsh (fun x => sign (g x)) u|<2*B := by
      linarith
    have hpos := le_abs_self (walsh (fun x => sign (f x)) u-walsh (fun x => sign (g x)) u)
    have hneg := neg_le_abs (walsh (fun x => sign (f x)) u-walsh (fun x => sign (g x)) u)
    rcases (sq_eq_sq_iff_eq_or_eq_neg.mp (hf u)) with hh | hh <;>
      rcases (sq_eq_sq_iff_eq_or_eq_neg.mp (hg u)) with hh' | hh' <;> linarith
  have hs := walsh_injective hw
  funext x
  exact sign_injective (congrFun hs x)


noncomputable def productWalsh (f : Cube ι × Cube κ → ℝ) (w : Cube ι) (mu : Cube κ) : ℝ :=
  walsh (fun x => walsh (fun y => f (x,y)) mu) w

theorem productWalsh_expansion (f : Cube ι × Cube κ → ℝ) (w : Cube ι) (mu : Cube κ) :
    productWalsh f w mu=∑ x, ∑ y, f (x,y)*char w x*char mu y := by
  simp only [productWalsh, walsh, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem product_parseval (f : Cube ι × Cube κ → ℝ) :
    (∑ w, ∑ mu, (productWalsh f w mu)^2)=
      size ι*size κ*(∑ x, ∑ y, (f (x,y))^2) := by
  rw [Finset.sum_comm]
  simp only [productWalsh, parseval]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp_rw [parseval]
  rw [← Finset.mul_sum]
  ring

theorem product_inversion (f : Cube ι × Cube κ → ℝ) (x : Cube ι) (y : Cube κ) :
    (∑ w, ∑ mu, productWalsh f w mu*char w x*char mu y)=size ι*size κ*f (x,y) := by
  rw [Finset.sum_comm]
  calc
    (∑ mu, ∑ w, productWalsh f w mu*char w x*char mu y) =
        ∑ mu, (∑ w, productWalsh f w mu*char w x)*char mu y := by simp only [Finset.sum_mul]
    _ = ∑ mu, (size ι*walsh (fun y => f (x,y)) mu)*char mu y := by
      simp only [productWalsh, inversion]
    _ = size ι*(∑ mu, walsh (fun y => f (x,y)) mu*char mu y) := by
      simp only [Finset.mul_sum, mul_assoc]
    _ = _ := by rw [inversion]; ring

/-! The exact incidence-Gram operator estimate used by the bent spectral proof. -/
variable {R S : Type*} [Fintype R] [Fintype S] [DecidableEq R]

def inner {X : Type*} [Fintype X] (f g : X → ℝ) : ℝ := ∑ x, f x*g x
def sqnorm {X : Type*} [Fintype X] (f : X → ℝ) : ℝ := ∑ x, (f x)^2
def mv (C : R → S → ℝ) (f : S → ℝ) (p : R) : ℝ := ∑ z, C p z*f z

theorem adjoint_identity (C : R → S → ℝ) (f : S → ℝ) (u : R → ℝ) :
    inner f (mv (fun z p => C p z) u)=inner (mv C f) u := by
  simp only [inner, mv, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro z _
  ring

theorem gram_action (C : R → S → ℝ) (a b : ℝ)
    (hgram : ∀ p q, (∑ z, C p z*C q z)=a+(if p=q then b else 0))
    (u : R → ℝ) (hu : (∑ p, u p)=0) :
    mv C (mv (fun z p => C p z) u)=fun p => b*u p := by
  classical
  funext p
  unfold mv
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ q, ∑ z, C p z*(C q z*u q)) = ∑ q, (∑ z, C p z*C q z)*u q := by
      simp only [Finset.sum_mul, mul_assoc]
    _ = ∑ q, (a+(if p=q then b else 0))*u q := by simp_rw [hgram]
    _ = b*u p := by
      simp only [add_mul, Finset.sum_add_distrib]
      rw [← Finset.mul_sum, hu, mul_zero, zero_add]
      simp

/-- A rank-one-plus-scalar Gram identity gives the sharp centered operator norm. -/
theorem gram_bound_of_centered_image (C : R → S → ℝ) (a b : ℝ)
    (hb : 0 ≤ b)
    (hgram : ∀ p q, (∑ z, C p z*C q z)=a+(if p=q then b else 0))
    (f : S → ℝ) (hcenter : (∑ p, mv C f p)=0) : sqnorm (mv C f) ≤ b*sqnorm f := by
  let u := mv C f
  let v := mv (fun z p => C p z) u
  have hu : (∑ p, u p)=0 := hcenter
  have hv : mv C v=fun p => b*u p := gram_action C a b hgram u hu
  have hfv : inner f v=sqnorm u := by
    rw [show v=mv (fun z p => C p z) u from rfl, adjoint_identity]
    simp only [inner, sqnorm, u, pow_two]
  have hvv : sqnorm v=b*sqnorm u := by
    calc
      sqnorm v = inner v v := by simp only [sqnorm, inner, pow_two]
      _ = inner (mv C v) u := adjoint_identity C v u
      _ = inner (fun p => b*u p) u := by rw [hv]
      _ = b*sqnorm u := by simp only [inner, sqnorm, pow_two, Finset.mul_sum, mul_assoc]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f v
  change (inner f v)^2 ≤ sqnorm f*sqnorm v at hcs
  rw [hfv, hvv] at hcs
  have hu0 : 0 ≤ sqnorm u := Finset.sum_nonneg fun p _ => sq_nonneg _
  have hf0 : 0 ≤ sqnorm f := Finset.sum_nonneg fun z _ => sq_nonneg _
  change sqnorm u ≤ b*sqnorm f
  nlinarith [mul_nonneg hb hf0]

theorem centered_gram_bound (C : R → S → ℝ) (a b lam : ℝ)
    (hb : 0 ≤ b)
    (hgram : ∀ p q, (∑ z, C p z*C q z)=a+(if p=q then b else 0))
    (hcol : ∀ z, (∑ p, C p z)=lam)
    (f : S → ℝ) (hf : (∑ z, f z)=0) : sqnorm (mv C f) ≤ b*sqnorm f := by
  apply gram_bound_of_centered_image C a b hb hgram f
  unfold mv
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, hcol]
  rw [← Finset.mul_sum, hf, mul_zero]

/-! Concrete incidence identities from the Walsh definition of vectorial bentness. -/
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

abbrev der (F : Cube ι → Cube κ) (a p : Cube ι) : Cube κ := F p+F (p+a)
noncomputable def inc (F : Cube ι → Cube κ) (p : Cube ι) (z : Cube ι × Cube κ) : ℝ :=
  if z.1=0 then 0 else if der F z.1 p=z.2 then 1 else 0

theorem inc_colsum (B : ℝ) (F : Cube ι → Cube κ)
    (hB : B^2=size ι) (hF : VectorialBent B F) (z : Cube ι × Cube κ) :
    (∑ p, inc F p z)=if z.1=0 then 0 else size ι/size κ := by
  classical
  by_cases hz : z.1=0
  · simp [inc, hz]
  · simp only [inc, hz, if_false]
    exact derivative_count B F hB hF z.1 hz z.2

theorem sum_drop_zero (g : Cube ι → ℝ) :
    (∑ a, if a=0 then 0 else g a)=(∑ a, g a)-g 0 := by
  classical
  have he : (∑ a, if a=0 then 0 else g a)+(∑ a, if a=0 then g a else 0)=∑ a, g a := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at he
  linarith

theorem der_cross_equiv (F : Cube ι → Cube κ) (a p q : Cube ι) :
    der F a p=der F a q ↔ der F (p+q) (p+a)=der F (p+q) p := by
  have he1 : p+(p+q)=q := by rw [← add_assoc, twice, zero_add]
  have he2 : (p+a)+(p+q)=q+a := by
    calc
      _ = (p+p)+(q+a) := by abel
      _ = _ := by rw [twice, zero_add]
  simp only [der, he1, he2]
  have he : (F p+F (p+a))+(F q+F (q+a))=(F (p+a)+F (q+a))+(F p+F q) := by abel
  calc
    (F p+F (p+a)=F q+F (q+a)) ↔ (F p+F (p+a))+(F q+F (q+a))=0 :=
      (add_zero_iff _ _).symm
    _ ↔ (F (p+a)+F (q+a))+(F p+F q)=0 := by rw [he]
    _ ↔ _ := add_zero_iff _ _

theorem sum_translate (p : Cube ι) (g : Cube ι → ℝ) : (∑ a, g (p+a))=∑ x, g x :=
  Equiv.sum_comp (Equiv.addLeft p) g

theorem cross_count (B : ℝ) (F : Cube ι → Cube κ)
    (hB : B^2=size ι) (hF : VectorialBent B F) (p q : Cube ι) (hpq : p≠q) :
    (∑ a, if der F a p=der F a q then (1 : ℝ) else 0)=size ι/size κ := by
  have ha : p+q≠0 := fun he => hpq ((add_zero_iff p q).mp he)
  have hcount : (∑ x, if der F (p+q) x=der F (p+q) p then (1 : ℝ) else 0)=size ι/size κ := by
    simpa only [der] using derivative_count B F hB hF (p+q) ha (der F (p+q) p)
  calc
    _ = ∑ a, if der F (p+q) (p+a)=der F (p+q) p then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases he : der F a p=der F a q
      · rw [if_pos he, if_pos ((der_cross_equiv F a p q).mp he)]
      · rw [if_neg he, if_neg (fun hh => he ((der_cross_equiv F a p q).mpr hh))]
    _ = ∑ x, if der F (p+q) x=der F (p+q) p then (1 : ℝ) else 0 :=
      sum_translate p (fun x => if der F (p+q) x=der F (p+q) p then (1 : ℝ) else 0)
    _ = _ := hcount

theorem inc_output_gram (F : Cube ι → Cube κ) (p q a : Cube ι) :
    (∑ v, inc F p (a,v)*inc F q (a,v)) =
      if a=0 then 0 else if der F a p=der F a q then 1 else 0 := by
  classical
  by_cases ha : a=0
  · simp [inc, ha]
  · simp only [inc, ha, if_false, ite_mul, one_mul, zero_mul]
    simp [eq_comm]

/-- The exact Gram matrix is derived from balanced derivatives, not postulated. -/
theorem inc_gram (B : ℝ) (F : Cube ι → Cube κ)
    (hB : B^2=size ι) (hF : VectorialBent B F) (p q : Cube ι) :
    (∑ z, inc F p z*inc F q z) =
      (size ι/size κ-1)+(if p=q then size ι-size ι/size κ else 0) := by
  classical
  rw [Fintype.sum_prod_type]
  simp_rw [inc_output_gram]
  rw [sum_drop_zero]
  have hzero : der F 0 p=der F 0 q := by simp [der, twice]
  rw [if_pos hzero]
  by_cases hpq : p=q
  · subst q
    simp only [if_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    change size ι-1=size ι/size κ-1+(size ι-size ι/size κ)
    ring
  · rw [if_neg hpq, cross_count B F hB hF p q hpq, add_zero]


/-- The zero-character spectral bound for the actual bent-graph incidence matrix. -/
theorem inc_centered_bound (B : ℝ) (F : Cube ι → Cube κ)
    (hB : B^2=size ι) (hF : VectorialBent B F)
    (f : Cube ι × Cube κ → ℝ) (hvert : ∀ v, f (0,v)=0)
    (hf : (∑ z, f z)=0) :
    sqnorm (mv (inc F) f) ≤ (size ι-size ι/size κ)*sqnorm f := by
  have hM : 1 ≤ size κ := by
    unfold size
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Cube κ))
  have hnonneg : 0 ≤ size ι-size ι/size κ := by
    apply sub_nonneg.mpr
    apply (div_le_iff₀ (size_pos (ι := κ))).mpr
    nlinarith [size_pos (ι := ι)]
  apply gram_bound_of_centered_image (inc F) (size ι/size κ-1)
    (size ι-size ι/size κ) hnonneg (inc_gram B F hB hF) f
  unfold mv
  rw [Finset.sum_comm]
  calc
    (∑ z, ∑ p, inc F p z*f z) = ∑ z, (∑ p, inc F p z)*f z := by simp only [Finset.sum_mul]
    _ = ∑ z, (size ι/size κ)*f z := by
      apply Finset.sum_congr rfl
      rintro ⟨a,v⟩ _
      rw [inc_colsum B F hB hF]
      by_cases ha : a=0
      · subst a
        simp [hvert]
      · simp [ha]
    _ = 0 := by rw [← Finset.mul_sum, hf, mul_zero]

/-! Fourier identities for the concrete graph of a vectorial Boolean function. -/
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
abbrev Ambient (ι κ : Type*) := Cube ι × Cube κ

noncomputable def graph (F : Cube ι → Cube κ) (z : Ambient ι κ) : ℝ :=
  if F z.1=z.2 then 1 else 0
noncomputable def pchar (xi z : Ambient ι κ) : ℝ := char xi.1 z.1*char xi.2 z.2
noncomputable def transform (f : Ambient ι κ → ℝ) (xi : Ambient ι κ) : ℝ :=
  productWalsh f xi.1 xi.2

theorem pchar_add (xi z z' : Ambient ι κ) : pchar xi (z+z')=pchar xi z*pchar xi z' := by
  simp only [pchar, Prod.fst_add, Prod.snd_add, char_add_right]
  ring
theorem pchar_abs (xi z : Ambient ι κ) : |pchar xi z|=1 := by
  simp only [pchar, abs_mul, char_abs, one_mul]

theorem transform_expansion (f : Ambient ι κ → ℝ) (xi : Ambient ι κ) :
    transform f xi=∑ z, f z*pchar xi z := by
  rw [Fintype.sum_prod_type]
  simp only [transform, productWalsh_expansion, pchar, mul_assoc]

theorem transform_inversion (f : Ambient ι κ → ℝ) (z : Ambient ι κ) :
    (∑ xi, transform f xi*pchar xi z)=size ι*size κ*f z := by
  rw [Fintype.sum_prod_type]
  simp only [transform, pchar, ← mul_assoc]
  exact product_inversion f z.1 z.2

theorem transform_parseval (f : Ambient ι κ → ℝ) :
    (∑ xi, (transform f xi)^2)=size ι*size κ*(∑ z, (f z)^2) := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  exact product_parseval f

/-- The graph Fourier coefficients are exactly the component Walsh coefficients. -/
theorem graph_transform (F : Cube ι → Cube κ) (w : Cube ι) (mu : Cube κ) :
    transform (graph F) (w,mu)=walsh (fun x => char mu (F x)) w := by
  classical
  simp only [transform, productWalsh_expansion, graph, ite_mul, one_mul, zero_mul]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  unfold walsh
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem graph_zero_slice (F : Cube ι → Cube κ) (w : Cube ι) :
    transform (graph F) (w,0)=if w=0 then size ι else 0 := by
  rw [graph_transform]
  simp only [walsh, char_zero_left, one_mul]
  exact char_sum w

theorem graph_nonzero_slice (B : ℝ) (hB : 0 ≤ B) (F : Cube ι → Cube κ)
    (hF : VectorialBent B F) (w : Cube ι) (mu : Cube κ) (hmu : mu≠0) :
    |transform (graph F) (w,mu)|=B := by
  rw [graph_transform]
  have he := hF mu hmu w
  have ha := abs_nonneg (walsh (fun x => char mu (F x)) w)
  have hs := sq_abs (walsh (fun x => char mu (F x)) w)
  nlinarith

/-! Exact Fourier expansion of the concrete four-point propagation kernel. -/

theorem triple_rotate {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (h : X → Y → Z → ℝ) :
    (∑ x, ∑ y, ∑ z, h x y z)=∑ y, ∑ z, ∑ x, h x y z := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.sum_comm]

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem twisted_convolution (A g : Ambient ι κ → ℝ) (b : Ambient ι κ) :
    size ι*size κ*(∑ z, ∑ w, g z*g w*A (b+z+w)) =
      ∑ xi, transform A xi*pchar xi b*(transform g xi)^2 := by
  have hs (xi : Ambient ι κ) : (transform g xi)^2 =
      ∑ z, ∑ w, (g z*pchar xi z)*(g w*pchar xi w) := by
    rw [transform_expansion, pow_two]
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  symm
  calc
    _ = ∑ xi, ∑ z, ∑ w, (g z*g w)*(transform A xi*pchar xi (b+z+w)) := by
      simp_rw [hs, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro xi _
      apply Finset.sum_congr rfl
      intro z _
      apply Finset.sum_congr rfl
      intro w _
      rw [pchar_add, pchar_add]
      ring
    _ = ∑ z, ∑ w, (g z*g w)*(∑ xi, transform A xi*pchar xi (b+z+w)) := by
      rw [triple_rotate]
      simp only [Finset.mul_sum]
    _ = ∑ z, ∑ w, (g z*g w)*(size ι*size κ*A (b+z+w)) := by
      simp_rw [transform_inversion]
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      apply Finset.sum_congr rfl
      intro w _
      ring

noncomputable def kernel (F : Cube ι → Cube κ) (C : Cube ι → Ambient ι κ → ℝ)
    (t : Cube κ) (z w : Ambient ι κ) : ℝ :=
  ∑ p, C p z*C p w*graph F ((p,F p)+(0,t)+z+w)

noncomputable def kernelQuadratic (K : Ambient ι κ → Ambient ι κ → ℝ)
    (f : Ambient ι κ → ℝ) : ℝ := ∑ z, ∑ w, f z*K z w*f w

noncomputable def localTransform (C : Cube ι → Ambient ι κ → ℝ)
    (f : Ambient ι κ → ℝ) (xi : Ambient ι κ) (p : Cube ι) : ℝ :=
  transform (fun z => f z*C p z) xi

/-- The exact spectral expansion, before any inequalities or bentness assumptions. -/
theorem kernel_fourier_identity (F : Cube ι → Cube κ)
    (C : Cube ι → Ambient ι κ → ℝ) (t : Cube κ) (f : Ambient ι κ → ℝ) :
    size ι*size κ*kernelQuadratic (kernel F C t) f =
      ∑ xi, transform (graph F) xi*pchar xi (0,t)*
        (∑ p, pchar xi (p,F p)*(localTransform C f xi p)^2) := by
  have hq : kernelQuadratic (kernel F C t) f =
      ∑ p, ∑ z, ∑ w, (f z*C p z)*(f w*C p w)*graph F ((p,F p)+(0,t)+z+w) := by
    unfold kernelQuadratic kernel
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [triple_rotate]
    rw [triple_rotate]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro z _
    apply Finset.sum_congr rfl
    intro w _
    ring
  rw [hq, Finset.mul_sum]
  simp_rw [twisted_convolution]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro xi _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [pchar_add]
  dsimp [localTransform]
  ring

/-! Exact total and zero-output-slice energies for the actual bent incidence. -/
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem inc_sq (F : Cube ι → Cube κ) (p : Cube ι) (z : Ambient ι κ) :
    (inc F p z)^2=inc F p z := by
  unfold inc
  split_ifs <;> norm_num

theorem local_mass (B : ℝ) (F : Cube ι → Cube κ)
    (hB : B^2=size ι) (hF : VectorialBent B F)
    (f : Ambient ι κ → ℝ) (hvert : ∀ v, f (0,v)=0) :
    (∑ p, ∑ z, (f z*inc F p z)^2)=(size ι/size κ)*(∑ z, (f z)^2) := by
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  rintro ⟨a,v⟩ _
  simp_rw [mul_pow, inc_sq]
  rw [← Finset.mul_sum, inc_colsum B F hB hF]
  by_cases ha : a=0
  · subst a
    simp [hvert]
  · simp [ha, mul_comm]

theorem total_energy (B : ℝ) (F : Cube ι → Cube κ)
    (hB : B^2=size ι) (hF : VectorialBent B F)
    (f : Ambient ι κ → ℝ) (hvert : ∀ v, f (0,v)=0) :
    (∑ xi, ∑ p, (localTransform (inc F) f xi p)^2)=
      size ι*size κ*(size ι/size κ)*(∑ z, (f z)^2) := by
  rw [Finset.sum_comm]
  simp only [localTransform, transform_parseval]
  rw [← Finset.mul_sum, local_mass B F hB hF f hvert]
  ring

theorem slice_transform (F : Cube ι → Cube κ) (f : Ambient ι κ → ℝ)
    (w p : Cube ι) :
    localTransform (inc F) f (w,0) p =
      walsh (fun a => ∑ v, f (a,v)*inc F p (a,v)) w := by
  simp only [localTransform, transform_expansion, Fintype.sum_prod_type,
    pchar, char_zero_left, mul_one, walsh, Finset.sum_mul]

theorem row_slice_sq (F : Cube ι → Cube κ) (f : Ambient ι κ → ℝ)
    (p a : Cube ι) :
    (∑ v, f (a,v)*inc F p (a,v))^2=∑ v, (f (a,v)*inc F p (a,v))^2 := by
  classical
  by_cases ha : a=0
  · simp [inc, ha]
  · simp only [inc, ha, if_false, mul_ite, mul_one, mul_zero, ite_pow,
      zero_pow (by decide : (2:ℕ)≠0)]
    simp

/-- The zero-output-character slice must be subtracted, not estimated away. -/
theorem zero_slice_energy (B : ℝ) (F : Cube ι → Cube κ)
    (hB : B^2=size ι) (hF : VectorialBent B F)
    (f : Ambient ι κ → ℝ) (hvert : ∀ v, f (0,v)=0) :
    (∑ w, ∑ p, (localTransform (inc F) f (w,0) p)^2)=
      size ι*(size ι/size κ)*(∑ z, (f z)^2) := by
  rw [Finset.sum_comm]
  simp_rw [slice_transform, parseval, row_slice_sq]
  have hp (p : Cube ι) : (∑ a : Cube ι, ∑ v : Cube κ, (f (a,v)*inc F p (a,v))^2)=
      ∑ z : Ambient ι κ, (f z*inc F p z)^2 := by
    rw [Fintype.sum_prod_type]
  simp_rw [hp]
  rw [← Finset.mul_sum, local_mass B F hB hF f hvert]
  ring

/-! The sharp concrete bent propagation kernelQuadratic bound, derived from Walsh flatness. -/
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

noncomputable def contribution (F : Cube ι → Cube κ) (t : Cube κ)
    (f : Ambient ι κ → ℝ) (xi : Ambient ι κ) : ℝ :=
  transform (graph F) xi*pchar xi (0,t)*
    (∑ p, pchar xi (p,F p)*(localTransform (inc F) f xi p)^2)

theorem contribution_bound (B : ℝ) (hB : 0 ≤ B) (F : Cube ι → Cube κ)
    (hF : VectorialBent B F) (t : Cube κ) (f : Ambient ι κ → ℝ)
    (w : Cube ι) (mu : Cube κ) (hmu : mu≠0) :
    contribution F t f (w,mu) ≤ B*(∑ p, (localTransform (inc F) f (w,mu) p)^2) := by
  unfold contribution
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p _
  have hab : |transform (graph F) (w,mu)*pchar (w,mu) (0,t)*pchar (w,mu) (p,F p)|=B := by
    rw [abs_mul, abs_mul, graph_nonzero_slice B hB F hF w mu hmu,
      pchar_abs, pchar_abs, mul_one, mul_one]
  have hle := le_abs_self (transform (graph F) (w,mu)*pchar (w,mu) (0,t)*pchar (w,mu) (p,F p))
  rw [hab] at hle
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hle
    (sq_nonneg (localTransform (inc F) f (w,mu) p))

theorem zero_contribution (F : Cube ι → Cube κ) (t : Cube κ)
    (f : Ambient ι κ → ℝ) :
    (∑ w, contribution F t f (w,0))=size ι*sqnorm (mv (inc F) f) := by
  classical
  have hz (p : Cube ι) : localTransform (inc F) f (0,0) p=mv (inc F) f p := by
    simp only [localTransform, transform_expansion, pchar, char_zero_left,
      one_mul, mul_one, mv, mul_comm]
  simp only [contribution, graph_zero_slice, pchar, char_zero_right,
    char_zero_left, mul_one, ite_mul, zero_mul]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [hz, sqnorm, char_zero_left, one_mul]

theorem sum_split_output (g : Ambient ι κ → ℝ) :
    (∑ xi, g xi)=(∑ w, g (w,0))+(∑ w, ∑ mu, if mu=0 then 0 else g (w,mu)) := by
  rw [Fintype.sum_prod_type, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w _
  rw [sum_drop_zero]
  ring

/-- No spectral certificate is assumed: the coefficient comes from the actual graph. -/
theorem bent_quadratic_bound (B : ℝ) (hBnonneg : 0 ≤ B)
    (F : Cube ι → Cube κ) (hB : B^2=size ι) (hF : VectorialBent B F)
    (t : Cube κ) (f : Ambient ι κ → ℝ)
    (hvert : ∀ v, f (0,v)=0) (hf : (∑ z, f z)=0) :
    kernelQuadratic (kernel F (inc F) t) f ≤
      (size ι/size κ)*(1+B)*(1-1/size κ)*(∑ z, (f z)^2) := by
  let E (xi : Ambient ι κ) := ∑ p, (localTransform (inc F) f xi p)^2
  have he : (∑ w, ∑ mu, if mu=0 then 0 else E (w,mu)) =
      (size ι*size κ*(size ι/size κ)-size ι*(size ι/size κ))*(∑ z, (f z)^2) := by
    have hs := sum_split_output E
    have ht := total_energy B F hB hF f hvert
    have hz := zero_slice_energy B F hB hF f hvert
    change (∑ xi, E xi)=_ at ht
    change (∑ w, E (w,0))=_ at hz
    rw [ht, hz] at hs
    nlinarith
  have hbound : size ι*size κ*kernelQuadratic (kernel F (inc F) t) f ≤
      size ι*sqnorm (mv (inc F) f)+B*
      ((size ι*size κ*(size ι/size κ)-size ι*(size ι/size κ))*(∑ z, (f z)^2)) := by
    rw [kernel_fourier_identity]
    change (∑ xi, contribution F t f xi) ≤ _
    rw [sum_split_output, zero_contribution]
    apply add_le_add_right _ _
    rw [← he, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro w _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro mu _
    by_cases hmu : mu=0
    · simp [hmu]
    · simp only [hmu, if_false]
      exact contribution_bound B hBnonneg F hF t f w mu hmu
  have hc := inc_centered_bound B F hB hF f hvert hf
  have hcm := mul_le_mul_of_nonneg_left hc (le_of_lt (size_pos (ι := ι)))
  have hM0 : size κ ≠ 0 := ne_of_gt size_pos
  have hid : size ι*((size ι-size ι/size κ)*(∑ z, (f z)^2))+
      B*((size ι*size κ*(size ι/size κ)-size ι*(size ι/size κ))*(∑ z, (f z)^2)) =
      size ι*size κ*((size ι/size κ)*(1+B)*(1-1/size κ)*(∑ z, (f z)^2)) := by
    field_simp [hM0]
  have hmain : size ι*size κ*kernelQuadratic (kernel F (inc F) t) f ≤
      size ι*size κ*((size ι/size κ)*(1+B)*(1-1/size κ)*(∑ z, (f z)^2)) := by
    calc
      _ ≤ size ι*sqnorm (mv (inc F) f)+B*
          ((size ι*size κ*(size ι/size κ)-size ι*(size ι/size κ))*(∑ z, (f z)^2)) := hbound
      _ ≤ size ι*((size ι-size ι/size κ)*sqnorm f)+B*
          ((size ι*size κ*(size ι/size κ)-size ι*(size ι/size κ))*(∑ z, (f z)^2)) :=
        add_le_add_left hcm _
      _ = _ := by simpa only [sqnorm] using hid
  exact (mul_le_mul_iff_right₀ (mul_pos (size_pos (ι := ι)) (size_pos (ι := κ)))).mp hmain

/-! Constructive row-factorization of the four-point kernel. -/

section General
variable {V : Type*} [Fintype V] [AddCommGroup V]
noncomputable def pairCount (A : V → ℝ) (z : V) : ℝ := ∑ g, A g*A (g+z)
noncomputable def rawKernel (A : V → ℝ) (tau z w : V) : ℝ :=
  ∑ g, (A g*A (g+z))*(A (g+w)*A (g+z+w+tau))

theorem translated_pair (A : V → ℝ) (g z tau : V) :
    (∑ w, A (g+w)*A (g+z+w+tau))=pairCount A (z+tau) := by
  have he (w : V) : g+z+w+tau=(g+w)+(z+tau) := by abel
  simp_rw [he]
  exact Equiv.sum_comp (Equiv.addLeft g) (fun b => A b*A (b+(z+tau)))

/-- Every row is a product of two pair counts, even after arbitrary deletions. -/
theorem raw_row (A : V → ℝ) (tau z : V) :
    (∑ w, rawKernel A tau z w)=pairCount A z*pairCount A (z+tau) := by
  unfold rawKernel
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, translated_pair]
  rw [← Finset.sum_mul]
  rfl

theorem raw_symmetric (A : V → ℝ) (tau z w : V) :
    rawKernel A tau z w=rawKernel A tau w z := by
  unfold rawKernel
  apply Finset.sum_congr rfl
  intro g _
  have he : g+z+w+tau=g+w+z+tau := by abel
  rw [he]
  ring

theorem raw_nonneg (A : V → ℝ) (hA : ∀ g, 0 ≤ A g) (tau z w : V) :
    0 ≤ rawKernel A tau z w := by
  apply Finset.sum_nonneg
  intro g _
  exact mul_nonneg (mul_nonneg (hA _) (hA _)) (mul_nonneg (hA _) (hA _))
end General

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem derivative_graph (F : Cube ι → Cube κ) (p : Cube ι) (z : Ambient ι κ) :
    (der F z.1 p=z.2) ↔ F (p+z.1)=F p+z.2 := by
  constructor
  · intro h
    change F p+F (p+z.1)=z.2 at h
    calc
      F (p+z.1) = F p+(F p+F (p+z.1)) := by rw [← add_assoc, twice, zero_add]
      _ = _ := by rw [h]
  · intro h
    change F p+F (p+z.1)=z.2
    rw [h, ← add_assoc, twice, zero_add]

theorem inc_graph (F : Cube ι → Cube κ) (p : Cube ι) (z : Ambient ι κ)
    (hz : z.1≠0) : inc F p z=graph F ((p,F p)+z) := by
  simp only [inc, hz, if_false, graph, Prod.fst_add, Prod.snd_add]
  simp only [derivative_graph]

theorem raw_graph_expansion (F : Cube ι → Cube κ) (tau z w : Ambient ι κ) :
    rawKernel (graph F) tau z w=
      ∑ p, graph F ((p,F p)+z)*graph F ((p,F p)+w)*
        graph F ((p,F p)+z+w+tau) := by
  classical
  unfold rawKernel
  rw [Fintype.sum_prod_type]
  simp only [graph, ite_mul, one_mul, zero_mul]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem raw_graph_kernel (F : Cube ι → Cube κ) (t : Cube κ) (z w : Ambient ι κ)
    (hz : z.1≠0) (hw : w.1≠0) :
    rawKernel (graph F) (0,t) z w=kernel F (inc F) t z w := by
  rw [raw_graph_expansion]
  unfold kernel
  apply Finset.sum_congr rfl
  intro p _
  rw [inc_graph F p z hz, inc_graph F p w hw]
  have he : (p,F p)+z+w+(0,t)=(p,F p)+(0,t)+z+w := by abel
  rw [he]

theorem raw_quadratic_eq (F : Cube ι → Cube κ) (t : Cube κ)
    (f : Ambient ι κ → ℝ) (hvert : ∀ v, f (0,v)=0) :
    kernelQuadratic (rawKernel (graph F) (0,t)) f=kernelQuadratic (kernel F (inc F) t) f := by
  unfold kernelQuadratic
  apply Finset.sum_congr rfl
  rintro ⟨a,u⟩ _
  apply Finset.sum_congr rfl
  rintro ⟨b,v⟩ _
  by_cases ha : a=0
  · subst a
    simp [hvert]
  · by_cases hb : b=0
    · subst b
      simp [hvert]
    · rw [raw_graph_kernel F t (a,u) (b,v) ha hb]


variable {X : Type*} [Fintype X]

def quadratic (K : X -> X -> Real) (f : X -> Real) : Real :=
  ∑ i, ∑ j, K i j * f i * f j

def normSq (f : X -> Real) : Real := ∑ i, (f i)^2

theorem invariant_quadratic_eq (K : X -> X -> Real) (rho : Real)
    (hrow : ∀ i, ∑ j, K i j = rho)
    (f : X -> Real) (hinv : ∀ i j, K i j ≠ 0 -> f i = f j) :
    quadratic K f = rho * normSq f := by
  calc
    quadratic K f = ∑ i, ∑ j, K i j * (f i)^2 := by
      unfold quadratic
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      by_cases hK : K i j = 0
      · simp [hK]
      · rw [hinv i j hK]
        ring
    _ = ∑ i, (∑ j, K i j) * (f i)^2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_mul]
    _ = rho * normSq f := by
      simp_rw [hrow]
      rw [normSq, Finset.mul_sum]

theorem constant_of_regular_spectral_gap [Nonempty X]
    (K : X -> X -> Real) (alpha rho : Real)
    (hrow : ∀ i, ∑ j, K i j = rho)
    (hbound : ∀ f : X -> Real, (∑ i, f i) = 0 ->
      quadratic K f ≤ alpha * normSq f)
    (hgap : alpha < rho)
    (d : X -> Real) (hinv : ∀ i j, K i j ≠ 0 -> d i = d j) :
    ∀ i j, d i = d j := by
  let c : Real := (∑ i, d i) / (Fintype.card X : Real)
  let f : X -> Real := fun i => d i - c
  have hcard : (Fintype.card X : Real) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card X ≠ 0)
  have hsum : (∑ i, f i) = 0 := by
    simp only [f, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    dsimp [c]
    field_simp
    ring
  have hfinv : ∀ i j, K i j ≠ 0 -> f i = f j := by
    intro i j hij
    simp only [f, hinv i j hij]
  have hq := invariant_quadratic_eq K rho hrow f hfinv
  have hb := hbound f hsum
  rw [hq] at hb
  have hn : 0 ≤ normSq f := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hz : normSq f = 0 := by nlinarith
  intro i j
  have hi : (f i)^2 ≤ normSq f :=
    Finset.single_le_sum (fun x _ => sq_nonneg (f x)) (Finset.mem_univ i)
  have hj : (f j)^2 ≤ normSq f :=
    Finset.single_le_sum (fun x _ => sq_nonneg (f x)) (Finset.mem_univ j)
  rw [hz] at hi hj
  have hfi : f i = 0 := by nlinarith [sq_nonneg (f i)]
  have hfj : f j = 0 := by nlinarith [sq_nonneg (f j)]
  dsimp [f] at hfi hfj
  linarith


variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

abbrev Nonvertical (ι κ : Type*) := {z : Ambient ι κ // z.1 ≠ 0}

noncomputable def extendNonvertical (f : Nonvertical ι κ -> Real) : Ambient ι κ -> Real :=
  fun z => if hz : z.1 ≠ 0 then f ⟨z, hz⟩ else 0

theorem sum_extendNonvertical (f : Nonvertical ι κ -> Real) :
    (∑ z, extendNonvertical f z) = ∑ z, f z := by
  classical
  calc
    _ = ∑ z ∈ Finset.univ.filter (fun z : Ambient ι κ => z.1 ≠ 0),
        extendNonvertical f z := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro z _
      by_cases hz : z.1 = 0 <;> simp [extendNonvertical, hz]
    _ = ∑ z : Nonvertical ι κ, extendNonvertical f z :=
      Finset.sum_subtype _ (by simp) _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro z _
      simp [extendNonvertical, z.property]

theorem normSq_extendNonvertical (f : Nonvertical ι κ -> Real) :
    normSq (extendNonvertical f) = normSq f := by
  classical
  unfold normSq
  calc
    _ = ∑ z ∈ Finset.univ.filter (fun z : Ambient ι κ => z.1 ≠ 0),
        (extendNonvertical f z)^2 := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro z _
      by_cases hz : z.1 = 0 <;> simp [extendNonvertical, hz]
    _ = ∑ z : Nonvertical ι κ, (extendNonvertical f z)^2 :=
      Finset.sum_subtype _ (by simp) _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro z _
      simp [extendNonvertical, z.property]

theorem pairCount_graph (F : Cube ι -> Cube κ) (z : Ambient ι κ) (hz : z.1 ≠ 0) :
    pairCount (graph F) z = ∑ p, inc F p z := by
  classical
  unfold pairCount
  rw [Fintype.sum_prod_type]
  simp only [graph, ite_mul, one_mul, zero_mul]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  apply Finset.sum_congr rfl
  intro p _
  exact (inc_graph F p z hz).symm



theorem sum_subtype_of_zero {A : Type*} [Fintype A] (P : A -> Prop)
    [DecidablePred P] (g : A -> Real) (hzero : ∀ x, ¬ P x -> g x = 0) :
    (∑ x, g x) = ∑ x : Subtype P, g x := by
  classical
  calc
    _ = ∑ x ∈ Finset.univ.filter P, g x := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : P x
      · simp [hx]
      · simp [hx, hzero x hx]
    _ = _ := Finset.sum_subtype _ (by simp) _

noncomputable def bentKernel (F : Cube ι -> Cube κ) (t : Cube κ)
    (z w : Nonvertical ι κ) : Real :=
  rawKernel (graph F) (0, t) z w

theorem rawKernel_vertical_right (F : Cube ι -> Cube κ) (t : Cube κ) (ht : t ≠ 0)
    (z : Ambient ι κ) (v : Cube κ) :
    rawKernel (graph F) (0, t) z (0, v) = 0 := by
  rw [raw_graph_expansion]
  apply Finset.sum_eq_zero
  intro p _
  simp only [graph, Prod.fst_add, Prod.snd_add]
  split_ifs with h1 h2 h3 <;> simp_all

theorem quadratic_extendNonvertical (F : Cube ι -> Cube κ) (t : Cube κ)
    (ht : t ≠ 0) (f : Nonvertical ι κ -> Real) :
    quadratic (bentKernel F t) f =
      kernelQuadratic
        (rawKernel (graph F) (0, t)) (extendNonvertical f) := by
  classical
  symm
  unfold kernelQuadratic quadratic bentKernel
  rw [sum_subtype_of_zero (fun z : Ambient ι κ => z.1 ≠ 0)]
  · apply Finset.sum_congr rfl
    intro z _
    rw [sum_subtype_of_zero (fun w : Ambient ι κ => w.1 ≠ 0)]
    · apply Finset.sum_congr rfl
      intro w _
      unfold extendNonvertical
      rw [dif_pos z.property, dif_pos w.property]
      ring
    · intro w hw
      have hw0 : w.1 = 0 := not_ne_iff.mp hw
      rcases w with ⟨a, v⟩
      simp only at hw0
      subst a
      simp [extendNonvertical, rawKernel_vertical_right F t ht]
  · intro z hz
    have hz0 : z.1 = 0 := not_ne_iff.mp hz
    simp [extendNonvertical, hz0]




theorem bentKernel_row (B : Real) (F : Cube ι -> Cube κ)
    (hB : B^2 = size ι) (hF : VectorialBent B F)
    (t : Cube κ) (ht : t ≠ 0) (z : Nonvertical ι κ) :
    (∑ w, bentKernel F t z w) = (size ι / size κ)^2 := by
  classical
  unfold bentKernel
  rw [← sum_subtype_of_zero (fun w : Ambient ι κ => w.1 ≠ 0)]
  · rw [raw_row, pairCount_graph F z z.property]
    have hzt : ((z : Ambient ι κ) + (0, t)).1 ≠ 0 := by
      simpa using z.property
    rw [pairCount_graph F ((z : Ambient ι κ) + (0, t)) hzt]
    rw [inc_colsum B F hB hF, inc_colsum B F hB hF]
    simp [z.property]
    ring
  · intro w hw
    have hw0 : w.1 = 0 := not_ne_iff.mp hw
    rcases w with ⟨a, v⟩
    simp only at hw0
    subst a
    exact rawKernel_vertical_right F t ht z v

theorem bentKernel_bound (B : Real) (hBnonneg : 0 ≤ B)
    (F : Cube ι -> Cube κ) (hB : B^2 = size ι) (hF : VectorialBent B F)
    (t : Cube κ) (ht : t ≠ 0) (f : Nonvertical ι κ -> Real)
    (hf : (∑ z, f z) = 0) :
    quadratic (bentKernel F t) f ≤
      (size ι / size κ) * (1 + B) * (1 - 1 / size κ) * normSq f := by
  have hvert : ∀ v, extendNonvertical f (0, v) = 0 := by
    intro v
    simp [extendNonvertical]
  have hsum : (∑ z, extendNonvertical f z) = 0 := by
    rw [sum_extendNonvertical]
    exact hf
  calc
    quadratic (bentKernel F t) f =
        kernelQuadratic
          (rawKernel (graph F) (0, t)) (extendNonvertical f) :=
      quadratic_extendNonvertical F t ht f
    _ = kernelQuadratic
          (kernel F (inc F) t)
          (extendNonvertical f) :=
      raw_quadratic_eq F t (extendNonvertical f) hvert
    _ ≤ (size ι / size κ) * (1 + B) * (1 - 1 / size κ) *
          (∑ z, (extendNonvertical f z)^2) :=
      bent_quadratic_bound
        B hBnonneg F hB hF t (extendNonvertical f) hvert hsum
    _ = _ := by
      rw [← normSq, normSq_extendNonvertical]

theorem bent_strict_gap (B : Real) (hBpos : 0 < B)
    (hB : B^2 = size ι) (hM : size κ ≤ B) :
    (size ι / size κ) * (1 + B) * (1 - 1 / size κ) <
      (size ι / size κ)^2 := by
  have hMpos : 0 < size κ := size_pos
  have hM0 : size κ ≠ 0 := ne_of_gt hMpos
  rw [← hB]
  field_simp [hM0]
  nlinarith

theorem bentKernel_invariant_constant [Nonempty (Nonvertical ι κ)]
    (B : Real) (hBpos : 0 < B) (F : Cube ι -> Cube κ)
    (hB : B^2 = size ι) (hF : VectorialBent B F)
    (hM : size κ ≤ B) (t : Cube κ) (ht : t ≠ 0)
    (d : Nonvertical ι κ -> Real)
    (hinv : ∀ z w, bentKernel F t z w ≠ 0 -> d z = d w) :
    ∀ z w, d z = d w := by
  apply constant_of_regular_spectral_gap
    (bentKernel F t)
    ((size ι / size κ) * (1 + B) * (1 - 1 / size κ))
    ((size ι / size κ)^2)
  · exact bentKernel_row B F hB hF t ht
  · exact bentKernel_bound B (le_of_lt hBpos) F hB hF t ht
  · exact bent_strict_gap B hBpos hB hM
  · exact hinv




def derivative {A B : Type*} [Add A] (f : A -> B) (a x : A) [Add B] : B :=
  f x + f (x + a)

def secondDerivative {A B : Type*} [Add A] (f : A -> B) (a b x : A) [Add B] : B :=
  f x + f (x + a) + f (x + b) + f (x + a + b)

theorem secondDerivative_eq (A : Type*) [AddCommGroup A]
    (B : Type*) [AddCommGroup B] (f : A -> B) (a b x : A) :
    secondDerivative f a b x = derivative f a x + derivative f a (x + b) := by
  simp only [secondDerivative, derivative]
  rw [add_right_comm x a b]
  abel

theorem eq_of_add_eq_zero {A : Type*} [AddCommGroup A]
    (htwo : ∀ x : A, x + x = 0) {x y : A} (h : x + y = 0) : x = y := by
  have h' : x + y + y = y := by rw [h, zero_add]
  rwa [add_assoc, htwo y, add_zero] at h'

theorem fiber_derivative
    {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (htwoA : ∀ x : A, x + x = 0) (htwoB : ∀ x : B, x + x = 0)
    (htwoC : ∀ x : C, x + x = 0)
    (F : A -> B) (phi : A -> C)
    (hphi : ∀ a b x, secondDerivative F a b x = 0 ->
      secondDerivative phi a b x = 0)
    (a x y : A) (hxy : derivative F a x = derivative F a y) :
    derivative phi a x = derivative phi a y := by
  have hy : x + (x + y) = y := by
    rw [← add_assoc, htwoA, zero_add]
  have hF : secondDerivative F a (x + y) x = 0 := by
    rw [secondDerivative_eq, hy, hxy, htwoB]
  have hp := hphi a (x + y) x hF
  rw [secondDerivative_eq, hy] at hp
  exact eq_of_add_eq_zero htwoC hp

theorem derivative_surjective (B : Real) (F : Cube ι -> Cube κ)
    (hB : B^2 = size ι) (hF : VectorialBent B F)
    (a : Cube ι) (ha : a ≠ 0) (u : Cube κ) :
    ∃ x, derivative F a x = u := by
  classical
  by_contra h
  push Not at h
  change ∀ x, der F a x ≠ u at h
  have hs := inc_colsum B F hB hF (a, u)
  rw [if_neg ha] at hs
  have hz : (∑ x, inc F x (a, u)) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    simp [inc, ha, h x]
  have hp : 0 < size ι / size κ := div_pos size_pos size_pos
  linarith

noncomputable def derivativeBase (B : Real) (F : Cube ι -> Cube κ)
    (hB : B^2 = size ι) (hF : VectorialBent B F)
    (z : Nonvertical ι κ) : Cube ι :=
  Classical.choose (derivative_surjective B F hB hF z.val.1 z.property z.val.2)

theorem derivativeBase_spec (B : Real) (F : Cube ι -> Cube κ)
    (hB : B^2 = size ι) (hF : VectorialBent B F)
    (z : Nonvertical ι κ) :
    derivative F z.val.1 (derivativeBase B F hB hF z) = z.val.2 :=
  Classical.choose_spec (derivative_surjective B F hB hF z.val.1 z.property z.val.2)

noncomputable def differenceValue (B : Real) (F : Cube ι -> Cube κ)
    (hB : B^2 = size ι) (hF : VectorialBent B F)
    (phi : Cube ι -> Bit) (z : Nonvertical ι κ) : Bit :=
  derivative phi z.val.1 (derivativeBase B F hB hF z)

theorem differenceValue_eq (B : Real) (F : Cube ι -> Cube κ)
    (hB : B^2 = size ι) (hF : VectorialBent B F)
    (phi : Cube ι -> Bit)
    (hphi : ∀ a b x, secondDerivative F a b x = 0 ->
      secondDerivative phi a b x = 0)
    (z : Nonvertical ι κ) (x : Cube ι)
    (hx : derivative F z.val.1 x = z.val.2) :
    differenceValue B F hB hF phi z = derivative phi z.val.1 x := by
  unfold differenceValue
  apply Eq.symm
  apply fiber_derivative
    (fun x : Cube ι => twice x)
    (fun x : Cube κ => twice x)
    (fun x : Bit => by fin_cases x <;> decide)
    F phi hphi
  rw [hx, derivativeBase_spec B F hB hF z]




def outputShift (z : Nonvertical ι κ) (t : Cube κ) : Nonvertical ι κ :=
  ⟨z.val + (0, t), by simpa using z.property⟩

noncomputable def deltaValue (B : Real) (F : Cube ι -> Cube κ)
    (hB : B^2 = size ι) (hF : VectorialBent B F)
    (phi : Cube ι -> Bit) (t : Cube κ) (z : Nonvertical ι κ) : Bit :=
  differenceValue B F hB hF phi (outputShift z t) +
    differenceValue B F hB hF phi z

theorem graph_ne_zero_iff (F : Cube ι -> Cube κ) (z : Ambient ι κ) :
    graph F z ≠ 0 ↔ F z.1 = z.2 := by
  simp [graph]

theorem rawKernel_witness (F : Cube ι -> Cube κ) (tau z w : Ambient ι κ)
    (hK : rawKernel (graph F) tau z w ≠ 0) :
    ∃ p, graph F ((p, F p) + z) ≠ 0 ∧
      graph F ((p, F p) + w) ≠ 0 ∧
      graph F ((p, F p) + z + w + tau) ≠ 0 := by
  classical
  by_contra h
  apply hK
  rw [raw_graph_expansion]
  apply Finset.sum_eq_zero
  intro p _
  by_cases h1 : graph F ((p, F p) + z) = 0
  · simp [h1]
  by_cases h2 : graph F ((p, F p) + w) = 0
  · simp [h2]
  by_cases h3 : graph F ((p, F p) + z + w + tau) = 0
  · simp [h3]
  exact (h ⟨p, h1, h2, h3⟩).elim




theorem deltaValue_invariant
    (B : Real) (F : Cube ι -> Cube κ)
    (hB : B^2 = size ι) (hF : VectorialBent B F)
    (phi : Cube ι -> Bit)
    (hphi : ∀ a b x, secondDerivative F a b x = 0 ->
      secondDerivative phi a b x = 0)
    (t : Cube κ) (z w : Nonvertical ι κ)
    (hK : bentKernel F t z w ≠ 0) :
    deltaValue B F hB hF phi t z = deltaValue B F hB hF phi t w := by
  obtain ⟨p, hz, hw, hq⟩ :=
    rawKernel_witness F (0, t) z w hK
  have ez := (graph_ne_zero_iff F ((p, F p) + z.val)).mp hz
  have ew := (graph_ne_zero_iff F ((p, F p) + w.val)).mp hw
  have eq := (graph_ne_zero_iff F ((p, F p) + z.val + w.val + (0, t))).mp hq
  have ez' : F (p + z.val.1) = F p + z.val.2 := by
    simpa only [Prod.fst_add, Prod.snd_add] using ez
  have ew' : F (p + w.val.1) = F p + w.val.2 := by
    simpa only [Prod.fst_add, Prod.snd_add] using ew
  have eq' : F (p + z.val.1 + w.val.1) =
      F p + z.val.2 + w.val.2 + t := by
    simpa only [Prod.fst_add, Prod.snd_add, add_zero] using eq
  have hz0 : derivative F z.val.1 p = z.val.2 := by
    unfold derivative
    rw [ez', ← add_assoc, twice, zero_add]
  have hw0 : derivative F w.val.1 p = w.val.2 := by
    unfold derivative
    rw [ew', ← add_assoc, twice, zero_add]
  have hzt : derivative F z.val.1 (p + w.val.1) = z.val.2 + t := by
    unfold derivative
    rw [ew']
    have ha : p + w.val.1 + z.val.1 = p + z.val.1 + w.val.1 := by abel
    rw [ha, eq']
    calc
      (F p + w.val.2) + (F p + z.val.2 + w.val.2 + t) =
          (F p + F p) + (w.val.2 + w.val.2) + (z.val.2 + t) := by abel
      _ = z.val.2 + t := by
        rw [twice,
          twice, zero_add, zero_add]
  have hwt : derivative F w.val.1 (p + z.val.1) = w.val.2 + t := by
    unfold derivative
    rw [ez', eq']
    calc
      (F p + z.val.2) + (F p + z.val.2 + w.val.2 + t) =
          (F p + F p) + (z.val.2 + z.val.2) + (w.val.2 + t) := by abel
      _ = w.val.2 + t := by
        rw [twice,
          twice, zero_add, zero_add]
  have H0z := differenceValue_eq B F hB hF phi hphi z p hz0
  have H0w := differenceValue_eq B F hB hF phi hphi w p hw0
  have Htz := differenceValue_eq B F hB hF phi hphi
    (outputShift z t) (p + w.val.1) (by simpa [outputShift] using hzt)
  have Htw := differenceValue_eq B F hB hF phi hphi
    (outputShift w t) (p + z.val.1) (by simpa [outputShift] using hwt)
  unfold deltaValue
  rw [Htz, H0z, Htw, H0w]
  simp only [derivative, outputShift, Prod.fst_add, add_zero]
  abel




noncomputable def deltaSign (B : Real) (F : Cube ι -> Cube κ)
    (hB : B^2 = size ι) (hF : VectorialBent B F)
    (phi : Cube ι -> Bit) (t : Cube κ) (z : Nonvertical ι κ) : Real :=
  sign (deltaValue B F hB hF phi t z)

theorem deltaValue_constant [Nonempty (Nonvertical ι κ)]
    (B : Real) (hBpos : 0 < B) (F : Cube ι -> Cube κ)
    (hB : B^2 = size ι) (hF : VectorialBent B F)
    (hM : size κ ≤ B) (phi : Cube ι -> Bit)
    (hphi : ∀ a b x, secondDerivative F a b x = 0 ->
      secondDerivative phi a b x = 0)
    (t : Cube κ) (ht : t ≠ 0) :
    ∀ z w, deltaValue B F hB hF phi t z =
      deltaValue B F hB hF phi t w := by
  intro z w
  apply sign_injective
  exact bentKernel_invariant_constant B hBpos F hB hF hM t ht
    (deltaSign B F hB hF phi t)
    (fun z w hK => congrArg sign
      (deltaValue_invariant B F hB hF phi hphi t z w hK)) z w

noncomputable def nonverticalAnchor [Nonempty (Nonvertical ι κ)] :
    Nonvertical ι κ :=
  Classical.choice inferInstance

noncomputable def outputLinear [Nonempty (Nonvertical ι κ)]
    (B : Real) (F : Cube ι -> Cube κ)
    (hB : B^2 = size ι) (hF : VectorialBent B F)
    (phi : Cube ι -> Bit) (t : Cube κ) : Bit :=
  deltaValue B F hB hF phi t nonverticalAnchor

theorem deltaValue_eq_outputLinear [Nonempty (Nonvertical ι κ)]
    (B : Real) (hBpos : 0 < B) (F : Cube ι -> Cube κ)
    (hB : B^2 = size ι) (hF : VectorialBent B F)
    (hM : size κ ≤ B) (phi : Cube ι -> Bit)
    (hphi : ∀ a b x, secondDerivative F a b x = 0 ->
      secondDerivative phi a b x = 0)
    (t : Cube κ) (z : Nonvertical ι κ) :
    deltaValue B F hB hF phi t z =
      outputLinear B F hB hF phi t := by
  by_cases ht : t = 0
  · subst t
    have hz : outputShift z (0 : Cube κ) = z := by
      apply Subtype.ext
      simp [outputShift]
    have ha : outputShift (nonverticalAnchor (ι := ι) (κ := κ)) (0 : Cube κ) =
        nonverticalAnchor := by
      apply Subtype.ext
      simp [outputShift]
    unfold outputLinear deltaValue
    rw [hz, ha, twice,
      twice]
  · exact deltaValue_constant B hBpos F hB hF hM phi hphi t ht z nonverticalAnchor

theorem outputLinear_add [Nonempty (Nonvertical ι κ)]
    (B : Real) (hBpos : 0 < B) (F : Cube ι -> Cube κ)
    (hB : B^2 = size ι) (hF : VectorialBent B F)
    (hM : size κ ≤ B) (phi : Cube ι -> Bit)
    (hphi : ∀ a b x, secondDerivative F a b x = 0 ->
      secondDerivative phi a b x = 0)
    (s t : Cube κ) :
    outputLinear B F hB hF phi (s + t) =
      outputLinear B F hB hF phi s + outputLinear B F hB hF phi t := by
  let z := nonverticalAnchor (ι := ι) (κ := κ)
  have hst := deltaValue_eq_outputLinear B hBpos F hB hF hM phi hphi (s + t) z
  have hs := deltaValue_eq_outputLinear B hBpos F hB hF hM phi hphi s z
  have ht := deltaValue_eq_outputLinear B hBpos F hB hF hM phi hphi t (outputShift z s)
  unfold deltaValue at hst hs ht
  have hshift : outputShift (outputShift z s) t = outputShift z (s + t) := by
    apply Subtype.ext
    simp [outputShift, add_assoc]
  rw [hshift] at ht
  rw [← hst, ← hs, ← ht]
  ring_nf
  rw [show (2 : Bit) = 0 from rfl, mul_zero, add_zero]


def IsAffine {A B : Type*} [Add A] [Add B] [Zero A] (f : A -> B) : Prop :=
  ∀ x y, f (x + y) = f x + f y + f 0

theorem affine_of_constant_derivatives
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (htwo : ∀ x : B, x + x = 0) (f : A -> B)
    (h : ∀ a x, derivative f a x = derivative f a 0) :
    IsAffine f := by
  intro x y
  have hy := h y x
  unfold derivative at hy
  simp only [zero_add] at hy
  calc
    f (x + y) = f (x + y) + (f x + f x) := by rw [htwo, add_zero]
    _ = (f x + f (x + y)) + f x := by abel
    _ = (f 0 + f y) + f x := by rw [hy]
    _ = f x + f y + f 0 := by abel

theorem corrected_derivative_eq [Nonempty (Nonvertical ι κ)]
    (B : Real) (hBpos : 0 < B) (F : Cube ι -> Cube κ)
    (hB : B^2 = size ι) (hF : VectorialBent B F)
    (hM : size κ ≤ B) (phi : Cube ι -> Bit)
    (hphi : ∀ a b x, secondDerivative F a b x = 0 ->
      secondDerivative phi a b x = 0)
    (a : Cube ι) (ha : a ≠ 0) (x : Cube ι) :
    derivative
      (fun y => phi y + outputLinear B F hB hF phi (F y)) a x =
      differenceValue B F hB hF phi ⟨(a, 0), ha⟩ := by
  let u := derivative F a x
  let z0 : Nonvertical ι κ := ⟨(a, 0), ha⟩
  let zu : Nonvertical ι κ := ⟨(a, u), ha⟩
  have Hu := differenceValue_eq B F hB hF phi hphi zu x (by rfl)
  have hd := deltaValue_eq_outputLinear B hBpos F hB hF hM phi hphi u z0
  have hz : outputShift z0 u = zu := by
    apply Subtype.ext
    simp [outputShift, z0, zu]
  unfold deltaValue at hd
  rw [hz] at hd
  have hadd := outputLinear_add B hBpos F hB hF hM phi hphi (F x) (F (x + a))
  calc
    derivative (fun y => phi y + outputLinear B F hB hF phi (F y)) a x =
        derivative phi a x +
          (outputLinear B F hB hF phi (F x) +
            outputLinear B F hB hF phi (F (x + a))) := by
      unfold derivative
      simp only
      abel
    _ = differenceValue B F hB hF phi zu +
          outputLinear B F hB hF phi u := by
      rw [Hu, ← hadd]
      rfl
    _ = differenceValue B F hB hF phi z0 := by
      rw [← hd]
      ring_nf
      rw [show (2 : Bit) = 0 from rfl, mul_zero, zero_add]
    _ = _ := by rfl

theorem vanishing_flat_dual_rigidity [Nonempty (Nonvertical ι κ)]
    (B : Real) (hBpos : 0 < B) (F : Cube ι -> Cube κ)
    (hB : B^2 = size ι) (hF : VectorialBent B F)
    (hM : size κ ≤ B) (phi : Cube ι -> Bit)
    (hphi : ∀ a b x, secondDerivative F a b x = 0 ->
      secondDerivative phi a b x = 0) :
    ∃ ell : Cube κ -> Bit,
      (∀ s t, ell (s + t) = ell s + ell t) ∧
      IsAffine (fun x => phi x + ell (F x)) := by
  let ell := outputLinear B F hB hF phi
  refine ⟨ell, outputLinear_add B hBpos F hB hF hM phi hphi, ?_⟩
  apply affine_of_constant_derivatives
    (fun x : Bit => by fin_cases x <;> decide)
  intro a x
  by_cases ha : a = 0
  · subst a
    simp [derivative, twice]
  · rw [corrected_derivative_eq B hBpos F hB hF hM phi hphi a ha x,
      corrected_derivative_eq B hBpos F hB hF hM phi hphi a ha 0]





def IsAdditive {A B : Type*} [Add A] [Add B] (f : A -> B) : Prop :=
  ∀ x y, f (x + y) = f x + f y

theorem vectorial_dual_rigidity [Nonempty (Nonvertical ι κ)]
    {lambda : Type*} [Fintype lambda] [DecidableEq lambda]
    (B : Real) (hBpos : 0 < B) (F : Cube ι -> Cube κ)
    (hB : B^2 = size ι) (hF : VectorialBent B F)
    (hM : size κ ≤ B) (phi : Cube ι -> Cube lambda)
    (hphi : ∀ a b x, secondDerivative F a b x = 0 ->
      secondDerivative phi a b x = 0) :
    ∃ L : Cube κ -> Cube lambda, ∃ A : Cube ι -> Cube lambda,
      IsAdditive L ∧ IsAffine A ∧ ∀ x, phi x = A x + L (F x) := by
  have hc : ∀ j : lambda, ∃ ell : Cube κ -> Bit,
      (∀ s t, ell (s + t) = ell s + ell t) ∧
      IsAffine (fun x => phi x j + ell (F x)) := by
    intro j
    apply vanishing_flat_dual_rigidity B hBpos F hB hF hM (fun x => phi x j)
    intro a b x hx
    have hv := congrFun (hphi a b x hx) j
    simpa only [secondDerivative, Pi.add_apply, Pi.zero_apply] using hv
  choose ell hell haff using hc
  let L : Cube κ -> Cube lambda := fun u j => ell j u
  let A : Cube ι -> Cube lambda := fun x j => phi x j + ell j (F x)
  refine ⟨L, A, ?_, ?_, ?_⟩
  · intro u v
    funext j
    exact hell j u v
  · intro x y
    funext j
    exact haff j x y
  · intro x
    funext j
    dsimp [A, L]
    ring_nf
    rw [show (2 : Bit) = 0 from rfl, mul_zero, add_zero]




noncomputable def additiveHom {J : Type*} [Fintype J] [DecidableEq J]
    (ell : Cube J -> Bit) (h : IsAdditive ell) : Cube J →+ Bit where
  toFun := ell
  map_zero' := by
    have hz := h 0 0
    simp only [zero_add] at hz
    rcases bit_cases (ell 0) with he | he <;> simp_all
  map_add' := h

theorem cube_eq_sum_single {J : Type*} [Fintype J] [DecidableEq J]
    (u : Cube J) : u = ∑ j, Pi.single j (u j) := by
  funext j
  simp

theorem additive_eq_dotProduct {J : Type*} [Fintype J] [DecidableEq J]
    (ell : Cube J -> Bit) (h : IsAdditive ell) (u : Cube J) :
    ell u = dotProduct (fun j => ell (Pi.single j 1)) u := by
  let e := additiveHom ell h
  rw [cube_eq_sum_single u]
  change e (∑ j, Pi.single j (u j)) = _
  rw [map_sum]
  unfold dotProduct
  apply Finset.sum_congr rfl
  intro j _
  rcases bit_cases (u j) with hj | hj
  · simp [hj, e]
  · simp [hj]
    rfl

def imbalance {J : Type*} [Fintype J] [DecidableEq J] (f : Cube J -> Bit) : Real :=
  ∑ x, sign (f x)

theorem affine_add_origin_additive {J : Type*} [Fintype J] [DecidableEq J]
    (a : Cube J -> Bit) (ha : IsAffine a) :
    IsAdditive (fun x => a x + a 0) := by
  intro x y
  change a (x + y) + a 0 = (a x + a 0) + (a y + a 0)
  rw [ha]
  ring_nf

theorem affine_eq_dotProduct_add {J : Type*} [Fintype J] [DecidableEq J]
    (a : Cube J -> Bit) (ha : IsAffine a) (x : Cube J) :
    a x = dotProduct
      (fun j => (a (Pi.single j 1) + a 0)) x + a 0 := by
  have h := additive_eq_dotProduct (fun x => a x + a 0)
    (affine_add_origin_additive a ha) x
  calc
    a x = (a x + a 0) + a 0 := by
      ring_nf
      rw [show (2 : Bit) = 0 from rfl, mul_zero, add_zero]
    _ = _ := by rw [h]

theorem bent_component_plus_affine_imbalance_ne_zero
    (B : Real) (hBpos : 0 < B) (F : Cube ι -> Cube κ)
    (hF : VectorialBent B F)
    (ell : Cube κ -> Bit) (hell : IsAdditive ell) (hnell : ell ≠ 0)
    (a : Cube ι -> Bit) (ha : IsAffine a) :
    imbalance (fun x => a x + ell (F x)) ≠ 0 := by
  let mu : Cube κ := fun j => ell (Pi.single j 1)
  let w : Cube ι := fun j => a (Pi.single j 1) + a 0
  have hell' : ∀ u, ell u = dotProduct mu u :=
    additive_eq_dotProduct ell hell
  have hmu : mu ≠ 0 := by
    intro hzero
    apply hnell
    funext u
    rw [hell' u, hzero]
    simp [dotProduct]
  have hflat := hF mu hmu w
  have hwalsh : walsh (fun x => char mu (F x)) w ≠ 0 := by
    intro hz
    rw [hz] at hflat
    norm_num at hflat
    nlinarith
  have heq : imbalance (fun x => a x + ell (F x)) =
      sign (a 0) * walsh (fun x => char mu (F x)) w := by
    unfold imbalance walsh
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    simp only
    rw [affine_eq_dotProduct_add a ha x, hell' (F x), sign_add, sign_add]
    unfold char
    ring
  rw [heq]
  exact mul_ne_zero (by
    unfold sign
    split_ifs <;> norm_num) hwalsh

theorem coordinate_imbalance_zero
    {J : Type*} [Fintype J] [DecidableEq J]
    (sigma : Equiv (Cube J) (Cube J)) (j : J) :
    imbalance (fun x => sigma x j) = 0 := by
  let e : Cube J := Pi.single j 1
  have he : e ≠ 0 := by
    intro hz
    have := congrFun hz j
    simp [e] at this
  calc
    imbalance (fun x => sigma x j) = ∑ x, sign (sigma x j) := rfl
    _ = ∑ y : Cube J, sign (y j) := Equiv.sum_comp sigma (fun y : Cube J => sign (y j))
    _ = ∑ y : Cube J, char e y := by
      apply Finset.sum_congr rfl
      intro y _
      unfold char
      simpa [e] using congrArg sign (single_one_dotProduct j y).symm
    _ = 0 := by rw [char_sum, if_neg he]




theorem additive_zero {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (f : A -> B) (hf : IsAdditive f) : f 0 = 0 := by
  have h := hf 0 0
  simp only [zero_add] at h
  apply add_left_cancel (a := f 0)
  simpa using h.symm

theorem affine_derivative_constant
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (htwo : ∀ z : B, z + z = 0)
    (f : A -> B) (hf : IsAffine f) (a x y : A) :
    derivative f a x = derivative f a y := by
  unfold derivative
  rw [hf x a, hf y a]
  calc
    f x + (f x + f a + f 0) = (f x + f x) + (f a + f 0) := by abel
    _ = f a + f 0 := by rw [htwo, zero_add]
    _ = (f y + f y) + (f a + f 0) := by rw [htwo, zero_add]
    _ = f y + (f y + f a + f 0) := by abel

theorem permutation_output_part_zero
    (B : Real) (hBpos : 0 < B) (F : Cube ι -> Cube κ)
    (hF : VectorialBent B F)
    (sigma : Equiv (Cube ι) (Cube ι))
    (L : Cube κ -> Cube ι) (A : Cube ι -> Cube ι)
    (hL : IsAdditive L) (hA : IsAffine A)
    (hrep : ∀ x, sigma x = A x + L (F x)) :
    L = 0 := by
  by_contra hL0
  have hu : ∃ u, L u ≠ 0 := by
    by_contra h
    push Not at h
    apply hL0
    funext u
    exact h u
  obtain ⟨u, hu⟩ := hu
  have hj : ∃ j, L u j ≠ 0 := by
    by_contra h
    push Not at h
    apply hu
    funext j
    exact h j
  obtain ⟨j, hj⟩ := hj
  let ell : Cube κ -> Bit := fun v => L v j
  let a : Cube ι -> Bit := fun x => A x j
  have hell : IsAdditive ell := by
    intro x y
    exact congrFun (hL x y) j
  have ha : IsAffine a := by
    intro x y
    exact congrFun (hA x y) j
  have hnell : ell ≠ 0 := by
    intro he
    exact hj (congrFun he u)
  have hn := bent_component_plus_affine_imbalance_ne_zero
    B hBpos F hF ell hell hnell a ha
  have hb := coordinate_imbalance_zero sigma j
  have heq : (fun x => sigma x j) = (fun x => a x + ell (F x)) := by
    funext x
    exact congrFun (hrep x) j
  rw [heq] at hb
  exact hn hb

theorem additive_output_affine_zero [Nonempty (Nonvertical ι κ)]
    (B : Real) (F : Cube ι -> Cube κ)
    (hB : B^2 = size ι) (hF : VectorialBent B F)
    (L : Cube κ -> Cube κ) (hL : IsAdditive L)
    (hA : IsAffine (fun x => L (F x))) :
    L = 0 := by
  by_contra hL0
  have hu : ∃ u, L u ≠ 0 := by
    by_contra h
    push Not at h
    apply hL0
    funext u
    exact h u
  obtain ⟨u, hu⟩ := hu
  let z := nonverticalAnchor (ι := ι) (κ := κ)
  have h0 := derivative_surjective B F hB hF z.val.1 z.property 0
  have h1 := derivative_surjective B F hB hF z.val.1 z.property u
  obtain ⟨x0, hx0⟩ := h0
  obtain ⟨x1, hx1⟩ := h1
  have hc := affine_derivative_constant
    (fun x : Cube κ => twice x)
    (fun x => L (F x)) hA z.val.1 x0 x1
  have hd (x : Cube ι) :
      derivative (fun y => L (F y)) z.val.1 x =
        L (derivative F z.val.1 x) := by
    unfold derivative
    rw [hL]
  rw [hd, hd, hx0, hx1, additive_zero L hL] at hc
  exact hu hc.symm




def VanishingFlatEquiv (F G : Cube ι -> Cube κ)
    (sigma : Equiv (Cube ι) (Cube ι)) : Prop :=
  ∀ x1 x2 x3 x4,
    (x1 + x2 + x3 + x4 = 0 ∧ F x1 + F x2 + F x3 + F x4 = 0) ↔
    (sigma x1 + sigma x2 + sigma x3 + sigma x4 = 0 ∧
      G (sigma x1) + G (sigma x2) + G (sigma x3) + G (sigma x4) = 0)

def EAEquivalent (F G : Cube ι -> Cube κ) : Prop :=
  ∃ sigma : Equiv (Cube ι) (Cube ι), IsAffine sigma ∧
    ∃ D : Equiv (Cube κ) (Cube κ), IsAdditive D ∧
      ∃ C : Cube ι -> Cube κ, IsAffine C ∧
        ∀ x, G (sigma x) = C x + D (F x)

theorem parallelogram_sum (x a b : Cube ι) :
    x + (x + a) + (x + b) + (x + a + b) = 0 := by
  funext j
  change x j + (x j + a j) + (x j + b j) + (x j + a j + b j) = 0
  ring_nf
  rw [show (4 : Bit) = 0 from rfl, show (2 : Bit) = 0 from rfl]
  simp

theorem dual_maps_of_vanishingFlatEquiv
    (F G : Cube ι -> Cube κ) (sigma : Equiv (Cube ι) (Cube ι))
    (h : VanishingFlatEquiv F G sigma) :
    (∀ a b x, secondDerivative F a b x = 0 ->
      secondDerivative sigma a b x = 0) ∧
    (∀ a b x, secondDerivative F a b x = 0 ->
      secondDerivative (fun y => G (sigma y)) a b x = 0) := by
  constructor <;> intro a b x hx
  · have hs := (h x (x + a) (x + b) (x + a + b)).mp
      ⟨parallelogram_sum x a b, hx⟩
    exact hs.1
  · have hs := (h x (x + a) (x + b) (x + a + b)).mp
      ⟨parallelogram_sum x a b, hx⟩
    exact hs.2

theorem vanishingFlatEquiv_symm
    (F G : Cube ι -> Cube κ) (sigma : Equiv (Cube ι) (Cube ι))
    (h : VanishingFlatEquiv F G sigma) :
    VanishingFlatEquiv G F sigma.symm := by
  intro y1 y2 y3 y4
  have hs := h (sigma.symm y1) (sigma.symm y2) (sigma.symm y3) (sigma.symm y4)
  simpa using hs.symm

theorem cube_add_self {J : Type*} [Fintype J] [DecidableEq J]
    (x : Cube J) : x + x = 0 :=
  twice x

theorem affine_add
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (f g : A -> B) (hf : IsAffine f) (hg : IsAffine g) :
    IsAffine (fun x => f x + g x) := by
  intro x y
  change f (x + y) + g (x + y) =
    (f x + g x) + (f y + g y) + (f 0 + g 0)
  rw [hf, hg]
  abel

theorem affine_comp
    {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (htwo : ∀ z : C, z + z = 0)
    (f : A -> B) (g : B -> C) (hf : IsAffine f) (hg : IsAffine g) :
    IsAffine (fun x => g (f x)) := by
  intro x y
  change g (f (x + y)) = g (f x) + g (f y) + g (f 0)
  rw [hf, hg, hg]
  calc
    (g (f x) + g (f y) + g 0) + g (f 0) + g 0 =
        g (f x) + g (f y) + g (f 0) + (g 0 + g 0) := by abel
    _ = g (f x) + g (f y) + g (f 0) := by rw [htwo, add_zero]

theorem additive_comp
    {A B C : Type*} [Add A] [Add B] [Add C]
    (f : A -> B) (g : B -> C) (hf : IsAdditive f) (hg : IsAdditive g) :
    IsAdditive (fun x => g (f x)) := by
  intro x y
  change g (f (x + y)) = g (f x) + g (f y)
  rw [hf, hg]

theorem additive_add
    {A B : Type*} [AddCommSemigroup A] [AddCommSemigroup B]
    (f g : A -> B) (hf : IsAdditive f) (hg : IsAdditive g) :
    IsAdditive (fun x => f x + g x) := by
  intro x y
  change f (x + y) + g (x + y) = (f x + g x) + (f y + g y)
  rw [hf, hg]
  ac_rfl

theorem nonempty_nonvertical [Nonempty ι] : Nonempty (Nonvertical ι κ) := by
  classical
  let i : ι := Classical.choice inferInstance
  let a : Cube ι := Pi.single i 1
  have ha : a ≠ 0 := by
    intro h
    have hi := congrFun h i
    simp [a] at hi
  exact ⟨⟨(a, 0), ha⟩⟩
theorem problem_3_65_hard [Nonempty (Nonvertical ι κ)]
    (B : Real) (hBpos : 0 < B) (F G : Cube ι -> Cube κ)
    (hB : B^2 = size ι) (hF : VectorialBent B F)
    (hG : VectorialBent B G) (hM : size κ ≤ B)
    (sigma : Equiv (Cube ι) (Cube ι))
    (hflat : VanishingFlatEquiv F G sigma) :
    EAEquivalent F G := by
  have hmaps := dual_maps_of_vanishingFlatEquiv F G sigma hflat
  obtain ⟨L, A, hL, hA, hsigma⟩ :=
    vectorial_dual_rigidity B hBpos F hB hF hM sigma hmaps.1
  have hLzero := permutation_output_part_zero
    B hBpos F hF sigma L A hL hA hsigma
  have hsigmaA : ∀ x, sigma x = A x := by
    intro x
    rw [hsigma x, hLzero]
    simp
  have hsigmaAffine : IsAffine sigma := by
    intro x y
    rw [hsigmaA, hsigmaA, hsigmaA, hsigmaA]
    exact hA x y
  obtain ⟨D, C, hD, hC, hGC⟩ :=
    vectorial_dual_rigidity B hBpos F hB hF hM
      (fun x => G (sigma x)) hmaps.2
  have hflat' := vanishingFlatEquiv_symm F G sigma hflat
  have hmaps' := dual_maps_of_vanishingFlatEquiv G F sigma.symm hflat'
  obtain ⟨D', C', hD', hC', hFC⟩ :=
    vectorial_dual_rigidity B hBpos G hB hG hM
      (fun y => F (sigma.symm y)) hmaps'.2
  let E : Cube κ -> Cube κ := fun u => u + D' (D u)
  let R : Cube ι -> Cube κ := fun x => C' (sigma x) + D' (C x)
  have hE : IsAdditive E := by
    apply additive_add id (fun u => D' (D u))
    · intro u v
      rfl
    · exact additive_comp D D' hD hD'
  have hR : IsAffine R := by
    apply affine_add
    · exact affine_comp cube_add_self sigma C' hsigmaAffine hC'
    · exact affine_comp cube_add_self C D' hC (by
        intro u v
        rw [hD', additive_zero D' hD']
        exact (add_zero _).symm)
  have hEF : ∀ x, E (F x) = R x := by
    intro x
    have hx := hFC (sigma x)
    simp only [Equiv.symm_apply_apply] at hx
    rw [hGC x, hD'] at hx
    dsimp [E, R]
    calc
      F x + D' (D (F x)) =
          (C' (sigma x) + (D' (C x) + D' (D (F x)))) +
            D' (D (F x)) := congrArg (fun u => u + D' (D (F x))) hx
      _ = C' (sigma x) + D' (C x) +
          (D' (D (F x)) + D' (D (F x))) := by abel
      _ = C' (sigma x) + D' (C x) := by
        rw [cube_add_self, add_zero]
  have hEAff : IsAffine (fun x => E (F x)) := by
    intro x y
    change E (F (x + y)) = E (F x) + E (F y) + E (F 0)
    rw [hEF (x + y), hEF x, hEF y, hEF 0]
    exact hR x y
  have hEzero := additive_output_affine_zero B F hB hF E hE hEAff
  have hleft : ∀ u, D' (D u) = u := by
    intro u
    have hu := congrFun hEzero u
    dsimp [E] at hu
    calc
      D' (D u) = D' (D u) + (u + u) := by rw [cube_add_self, add_zero]
      _ = (u + D' (D u)) + u := by abel
      _ = u := by rw [hu, zero_add]
  have hDinj : Function.Injective D := by
    intro u v huv
    rw [← hleft u, ← hleft v, huv]
  let De : Equiv (Cube κ) (Cube κ) :=
    Equiv.ofBijective D (Finite.injective_iff_bijective.mp hDinj)
  refine ⟨sigma, hsigmaAffine, De, ?_, C, hC, ?_⟩
  · exact hD
  · exact hGC

theorem cube_add_eq_zero_iff_eq {J : Type*} [Fintype J] [DecidableEq J]
    (x y : Cube J) : x + y = 0 ↔ x = y := by
  constructor
  · intro h
    calc
      x = x + (y + y) := by rw [cube_add_self, add_zero]
      _ = (x + y) + y := by abel
      _ = y := by rw [h, zero_add]
  · intro h
    rw [h, cube_add_self]

theorem affine_four_sum
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (f : Cube I -> Cube J) (hf : IsAffine f)
    (x1 x2 x3 x4 : Cube I) :
    f x1 + f x2 + f x3 + f x4 =
      f (x1 + x2 + x3 + x4) + f 0 := by
  have hs : x1 + x2 + x3 + x4 = (x1 + x2) + (x3 + x4) := by abel
  calc
    f x1 + f x2 + f x3 + f x4 =
        f x1 + f x2 + f x3 + f x4 +
          ((f 0 + f 0) + (f 0 + f 0)) := by
      rw [cube_add_self]
      simp
    _ = ((f x1 + f x2 + f 0) + (f x3 + f x4 + f 0) + f 0) + f 0 := by
      abel
    _ = f ((x1 + x2) + (x3 + x4)) + f 0 := by
      rw [← hf x1 x2, ← hf x3 x4, ← hf (x1 + x2) (x3 + x4)]
    _ = f (x1 + x2 + x3 + x4) + f 0 := by rw [hs]

theorem additive_four_sum
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (f : Cube I -> Cube J) (hf : IsAdditive f)
    (x1 x2 x3 x4 : Cube I) :
    f x1 + f x2 + f x3 + f x4 = f (x1 + x2 + x3 + x4) := by
  have hs : x1 + x2 + x3 + x4 = (x1 + x2) + (x3 + x4) := by abel
  rw [hs, hf, hf, hf]
  abel

theorem affine_four_sum_zero
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (f : Cube I -> Cube J) (hf : IsAffine f)
    (x1 x2 x3 x4 : Cube I)
    (h : x1 + x2 + x3 + x4 = 0) :
    f x1 + f x2 + f x3 + f x4 = 0 := by
  rw [affine_four_sum f hf, h, cube_add_self]

theorem affine_equiv_four_sum_zero_iff
    {I : Type*} [Fintype I] [DecidableEq I]
    (sigma : Equiv (Cube I) (Cube I)) (hsigma : IsAffine sigma)
    (x1 x2 x3 x4 : Cube I) :
    sigma x1 + sigma x2 + sigma x3 + sigma x4 = 0 ↔
      x1 + x2 + x3 + x4 = 0 := by
  rw [affine_four_sum sigma hsigma]
  constructor
  · intro h
    apply sigma.injective
    exact (cube_add_eq_zero_iff_eq _ _).mp h
  · intro h
    apply (cube_add_eq_zero_iff_eq _ _).mpr
    rw [h]

theorem eaEquivalent_vanishingFlat
    (F G : Cube ι -> Cube κ) (hEA : EAEquivalent F G) :
    ∃ sigma : Equiv (Cube ι) (Cube ι), VanishingFlatEquiv F G sigma := by
  obtain ⟨sigma, hsigma, D, hD, C, hC, hGC⟩ := hEA
  refine ⟨sigma, ?_⟩
  intro x1 x2 x3 x4
  have hsigma0 := affine_equiv_four_sum_zero_iff sigma hsigma x1 x2 x3 x4
  have hout :
      G (sigma x1) + G (sigma x2) + G (sigma x3) + G (sigma x4) =
        (C x1 + C x2 + C x3 + C x4) +
          (D (F x1) + D (F x2) + D (F x3) + D (F x4)) := by
    rw [hGC, hGC, hGC, hGC]
    abel
  constructor
  · rintro ⟨hx, hFx⟩
    refine ⟨hsigma0.mpr hx, ?_⟩
    rw [hout, affine_four_sum_zero C hC x1 x2 x3 x4 hx,
      additive_four_sum D hD, hFx, additive_zero D hD]
    simp
  · rintro ⟨hsx, hGx⟩
    have hx := hsigma0.mp hsx
    refine ⟨hx, ?_⟩
    have hCsum := affine_four_sum_zero C hC x1 x2 x3 x4 hx
    rw [hout, hCsum, zero_add, additive_four_sum D hD] at hGx
    apply D.injective
    rw [hGx, additive_zero D hD]

theorem problem_3_65 [Nonempty ι]
    (B : Real) (hBpos : 0 < B) (F G : Cube ι -> Cube κ)
    (hB : B^2 = size ι) (hF : VectorialBent B F)
    (hG : VectorialBent B G) (hM : size κ ≤ B) :
    (∃ sigma : Equiv (Cube ι) (Cube ι),
      VanishingFlatEquiv F G sigma) ↔ EAEquivalent F G := by
  letI : Nonempty (Nonvertical ι κ) := nonempty_nonvertical
  constructor
  · rintro ⟨sigma, hflat⟩
    exact problem_3_65_hard B hBpos F G hB hF hG hM sigma hflat
  · exact eaEquivalent_vanishingFlat F G

end Mathproof.Polujan365
