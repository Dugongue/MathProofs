import Mathlib
namespace VanishingSubdesign
abbrev Point := Fin 6 → ZMod 2
abbrev Output := Fin 2 → ZMod 2
def Bent (F : Point → Output) : Prop :=
  ∀ c : Output, c ≠ 0 → ∀ a : Point,
    (∑ x : Point, (-1 : ℤ) ^ ((∑ i, c i * F x i) + (∑ i, a i * x i)).val) ^ 2 = 64
def Flat (F : Point → Output) (b : Finset Point) : Prop :=
  b.card = 4 ∧ ∑ x ∈ b, x = 0 ∧ ∑ x ∈ b, F x = 0
def PairDesign (D : Finset (Finset Point)) : Prop :=
  (∀ b ∈ D, b.card = 4) ∧ ∀ x y : Point, x ≠ y →
    (D.filter fun b => x ∈ b ∧ y ∈ b).card = 3

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def translate (x : Point) (b : Finset Point) : Finset Point := b.image (x + ·)
lemma add_self (x : Point) : x + x = 0 := by exact CharTwo.add_self_eq_zero x
lemma translate_twice (x : Point) (b : Finset Point) : translate x (translate x b) = b := by
  simp only [translate, Finset.image_image, Function.comp_def, ← add_assoc, add_self, zero_add, Finset.image_id']
lemma mem_translate (x y : Point) (b : Finset Point) :
    y ∈ translate x b ↔ x + y ∈ b := by
  constructor
  · intro h
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp h
    simpa [← add_assoc, add_self] using hz
  · intro h
    apply Finset.mem_image.mpr
    exact ⟨x + y, h, by simp [← add_assoc, add_self]⟩
lemma translate_injective (x : Point) : Function.Injective (translate x) := by
  intro a b h
  simpa only [translate_twice] using congrArg (translate x) h
lemma translate_card (x : Point) (b : Finset Point) : (translate x b).card = b.card := by
  exact Finset.card_image_of_injective _ (add_right_injective x)
lemma translate_stable {p : Finset Point}
    (hc : ∀ a ∈ p, ∀ b ∈ p, a + b ∈ p) {x : Point} (hx : x ∈ p) :
    translate x p = p := by
  ext y
  rw [mem_translate]
  constructor
  · intro h
    simpa [← add_assoc, add_self] using hc x hx (x+y) h
  · exact hc x hx y

def development (P : Finset (Finset Point)) : Finset (Finset Point) :=
  Finset.univ.biUnion fun x => P.image (translate x)
lemma mem_development (P : Finset (Finset Point)) (b : Finset Point) :
    b ∈ development P ↔ ∃ x p, p ∈ P ∧ translate x p = b := by
  simp [development]
lemma pair_count (P : Finset (Finset Point))
    (hz : ∀ p ∈ P, (0 : Point) ∈ p)
    (hc : ∀ p ∈ P, ∀ a ∈ p, ∀ b ∈ p, a + b ∈ p) (x y : Point) :
    ((development P).filter fun b => x ∈ b ∧ y ∈ b).card =
    (P.filter fun p => x + y ∈ p).card := by
  symm
  apply Finset.card_bij (fun p _ => translate x p)
  · intro p hp
    obtain ⟨hp, hxy⟩ := Finset.mem_filter.mp hp
    apply Finset.mem_filter.mpr
    refine ⟨(mem_development P _).mpr ⟨x,p,hp,rfl⟩, ?_, ?_⟩
    · simpa [mem_translate, add_self] using hz p hp
    · exact (mem_translate x y p).mpr hxy
  · intro p hp q hq he
    exact translate_injective x he
  · intro b hb
    obtain ⟨hb,hx,hy⟩ := Finset.mem_filter.mp hb
    obtain ⟨t,p,hp,rfl⟩ := (mem_development P b).mp hb
    have htx : t + x ∈ p := (mem_translate t x p).mp hx
    have he : translate x p = translate t p := by
      apply (translate_injective t)
      rw [translate_twice]
      have ht : translate t (translate x p) = translate (t+x) p := by
        simp only [translate, Finset.image_image, Function.comp_def, add_assoc]
      rw [ht]
      exact translate_stable (hc p hp) htx
    refine ⟨p, Finset.mem_filter.mpr ⟨hp, ?_⟩, he⟩
    exact (mem_translate x y p).mp (he.symm ▸ hy)

def pointEquiv : Point ≃ Fin 64 := finFunctionFinEquiv
def outputEquiv : Output ≃ Fin 4 := finFunctionFinEquiv
def values : Fin 64 → Fin 4 := ![0,0,0,0,0,0,0,0,0,1,2,3,0,1,2,3,0,2,0,2,3,1,3,1,0,3,2,1,3,0,1,2,0,0,3,3,2,2,1,1,0,1,1,0,2,3,3,2,0,2,3,1,1,3,2,0,0,3,1,2,1,2,0,3]
def F (x : Point) : Output := outputEquiv.symm (values (pointEquiv x))
def direction : Fin 63 → Finset (Fin 64) := ![{0,1,2,3},{0,1,4,5},{0,1,32,33},{0,2,4,6},{0,2,5,7},{0,3,4,7},{0,3,5,6},{0,6,56,62},{0,7,51,52},{0,8,16,24},{0,8,32,40},{0,8,48,56},{0,9,18,27},{0,9,36,45},{0,9,54,63},{0,10,20,30},{0,10,35,41},{0,10,55,61},{0,11,22,29},{0,11,39,44},{0,11,49,58},{0,12,19,31},{0,12,38,42},{0,12,53,57},{0,13,17,28},{0,13,21,24},{0,13,34,47},{0,14,23,25},{0,14,37,43},{0,14,50,60},{0,15,21,26},{0,15,33,46},{0,15,52,59},{0,16,32,48},{0,16,40,56},{0,17,34,51},{0,17,47,62},{0,18,36,54},{0,18,45,63},{0,19,38,53},{0,19,42,57},{0,20,35,55},{0,20,41,61},{0,21,46,59},{0,22,39,49},{0,22,44,58},{0,23,37,50},{0,23,43,60},{0,24,40,48},{0,25,37,60},{0,25,43,50},{0,26,33,59},{0,26,46,52},{0,27,36,63},{0,27,45,54},{0,28,34,62},{0,28,47,51},{0,29,39,58},{0,29,44,49},{0,30,35,61},{0,30,41,55},{0,31,38,57},{0,31,42,53}]
def plane (i : Fin 63) : Finset Point := (direction i).image pointEquiv.symm
def planes : Finset (Finset Point) := Finset.univ.image plane

theorem planes_zero : ∀ p ∈ planes, (0 : Point) ∈ p := by
  have h : ∀ i : Fin 63, (0 : Point) ∈ plane i := by decide +kernel
  intro p hp
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
  exact h i

theorem planes_closed : ∀ p ∈ planes, ∀ a ∈ p, ∀ b ∈ p, a+b ∈ p := by
  have h : ∀ i : Fin 63, ∀ a ∈ plane i, ∀ b ∈ plane i, a+b ∈ plane i := by
    decide +kernel
  intro p hp
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
  exact h i

theorem planes_degree : ∀ u : Point, u ≠ 0 → (planes.filter fun p => u ∈ p).card = 3 := by
  have h : ∀ j : Fin 64, pointEquiv.symm j ≠ 0 →
      (planes.filter fun p => pointEquiv.symm j ∈ p).card = 3 := by decide +kernel
  intro u hu
  simpa using h (pointEquiv u) (by simpa using hu)

theorem planes_flat : ∀ p ∈ planes, ∀ t : Point, Flat F (translate t p) := by
  have h : ∀ (i : Fin 63) (j : Fin 64),
      Flat F (translate (pointEquiv.symm j) (plane i)) := by
    unfold Flat
    decide +kernel
  intro p hp t
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
  simpa using h i (pointEquiv t)

theorem F_bent : Bent F := by
  have h : ∀ (c : Fin 4), outputEquiv.symm c ≠ 0 → ∀ a : Fin 64,
      (∑ x : Fin 64, (-1 : ℤ) ^
        ((∑ i, outputEquiv.symm c i * F (pointEquiv.symm x) i) +
          (∑ i, pointEquiv.symm a i * pointEquiv.symm x i)).val) ^ 2 = 64 := by
    decide +kernel
  intro c hc a
  have hh := h (outputEquiv c) (by simpa using hc) (pointEquiv a)
  rw [← Equiv.sum_comp pointEquiv.symm
    (fun x : Point => (-1 : ℤ) ^ ((∑ i, c i * F x i) + (∑ i, a i * x i)).val)]
  simpa only [Equiv.symm_apply_apply] using hh

theorem design : PairDesign (development planes) := by
  constructor
  · intro b hb
    obtain ⟨x,p,hp,rfl⟩ := (mem_development planes b).mp hb
    exact (planes_flat p hp x).1
  · intro x y hxy
    rw [pair_count planes planes_zero planes_closed]
    apply planes_degree
    intro he
    apply hxy
    have h := congrArg (x + ·) he
    simpa [← add_assoc, add_self] using h.symm

theorem inclusion : ∀ b ∈ development planes, Flat F b := by
  intro b hb
  obtain ⟨x,p,hp,rfl⟩ := (mem_development planes b).mp hb
  exact planes_flat p hp x

lemma rebase (P : Finset (Finset Point))
    (hc : ∀ p ∈ P, ∀ a ∈ p, ∀ b ∈ p, a+b ∈ p)
    {b : Finset Point} (hb : b ∈ development P) {x : Point} (hx : x ∈ b) :
    translate x b ∈ P := by
  obtain ⟨t,p,hp,rfl⟩ := (mem_development P b).mp hb
  have htx : x+t ∈ p := by simpa [add_comm] using (mem_translate t x p).mp hx
  have he : translate x (translate t p) = translate (x+t) p := by
    simp only [translate, Finset.image_image, Function.comp_def, add_assoc]
  rw [he, translate_stable (hc p hp) htx]
  exact hp

def block (s : Finset (Fin 64)) : Finset Point := s.image pointEquiv.symm
def A : Finset Point := block {0,1,2,3}
def B : Finset Point := block {0,1,4,5}
def C : Finset Point := block {2,3,4,5}

lemma A_mem : A ∈ development planes := by
  apply (mem_development planes A).mpr
  refine ⟨0,A,?_,?_⟩
  · decide +kernel
  · simp only [translate, zero_add, Finset.image_id']
lemma B_mem : B ∈ development planes := by
  apply (mem_development planes B).mpr
  refine ⟨0,B,?_,?_⟩
  · decide +kernel
  · simp only [translate, zero_add, Finset.image_id']
lemma C_not_mem : C ∉ development planes := by
  intro h
  have hc : pointEquiv.symm 2 ∈ C := by decide +kernel
  have hn : translate (pointEquiv.symm 2) C ∉ planes := by decide +kernel
  exact hn (rebase planes planes_closed h hc)
lemma C_flat : Flat F C := by unfold Flat; decide +kernel

lemma obstruction (g : Point → ZMod 2) (hA : ∑ x ∈ A, g x = 0)
    (hB : ∑ x ∈ B, g x = 0) : ∑ x ∈ C, g x = 0 := by
  simp [A, B, C, block] at *
  linear_combination (norm := ring_nf) hA + hB
  simp only [show (2 : ZMod 2) = 0 by decide, mul_zero, neg_zero, sub_self]

theorem unrealizable_subdesign : ∃ (F : Point → Output) (D : Finset (Finset Point)),
  Bent F ∧ PairDesign D ∧ (∀ b ∈ D, Flat F b) ∧
  ¬ ∃ g : Point → ZMod 2, ∀ b : Finset Point,
    (Flat F b ∧ ∑ x ∈ b, g x = 0) ↔ b ∈ D := by
  refine ⟨F, development planes, F_bent, design, inclusion, ?_⟩
  rintro ⟨g,h⟩
  have hA := ((h A).mpr A_mem).2
  have hB := ((h B).mpr B_mem).2
  exact C_not_mem ((h C).mp ⟨C_flat, obstruction g hA hB⟩)

#print axioms unrealizable_subdesign
end VanishingSubdesign
