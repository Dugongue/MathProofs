import Mathlib
namespace BentMetric
abbrev Bit := ZMod 2
abbrev Point := Fin 4 → Bit
abbrev Word := Fin 16 → Bit
abbrev Param := Fin 6 → Bit
def point : Fin 16 → Point := (finFunctionFinEquiv : Point ≃ Fin 16).symm
def encode (f : Word) (c : Param) : Word := fun i =>
  c 0 + (∑ j : Fin 4, c ⟨j.val + 1, by omega⟩ * point i j) + c 5 * f i
def Code (f : Word) : Set Word := Set.range (encode f)
def Bent (f : Word) : Prop := ∀ a : Point,
  (∑ i : Fin 16, (-1 : ℤ) ^ (f i + ∑ j, a j * point i j).val) ^ 2 = 16
noncomputable def distanceTo (A : Set Word) (x : Word) : ℕ :=
  sInf ((fun y => hammingDist x y) '' A)
noncomputable def radius (A : Set Word) : ℕ := by
  classical
  exact Finset.univ.sup (distanceTo A)
def metricComplement (A : Set Word) : Set Word := {x | distanceTo A x = radius A}
end BentMetric

namespace BentMetric
set_option maxRecDepth 100000
set_option maxHeartbeats 0

lemma distance_upper {A : Set Word} {a x : Word} (ha : a ∈ A) :
    distanceTo A x ≤ hammingDist x a := by
  exact csInf_le' ⟨a, ha, rfl⟩
lemma distance_lower {A : Set Word} (hne : A.Nonempty) {x : Word} {r : ℕ}
    (h : ∀ a ∈ A, r ≤ hammingDist x a) : r ≤ distanceTo A x := by
  apply le_csInf (hne.image (fun y => hammingDist x y))
  rintro _ ⟨a,ha,rfl⟩
  exact h a ha
lemma radius_upper {A : Set Word} {r : ℕ}
    (h : ∀ x, ∃ a ∈ A, hammingDist x a ≤ r) : radius A ≤ r := by
  classical
  apply Finset.sup_le
  intro x _
  obtain ⟨a,ha,hd⟩ := h x
  exact (distance_upper ha).trans hd
lemma distance_le_radius (A : Set Word) (x : Word) : distanceTo A x ≤ radius A := by
  classical
  exact Finset.le_sup (f := distanceTo A) (Finset.mem_univ x)

/-- A sufficient certificate for equality with the double metric complement. -/
theorem regular_of_certificate (A B : Set Word) (r : ℕ)
    (ha : A.Nonempty) (hb : B.Nonempty)
    (sep : ∀ a ∈ A, ∀ b ∈ B, r ≤ hammingDist a b)
    (ca : ∀ x, ∃ a ∈ A, hammingDist x a ≤ r)
    (cb : ∀ x, ∃ b ∈ B, hammingDist x b ≤ r)
    (strict : ∀ x ∉ A, ∃ b ∈ B, hammingDist x b < r) :
    metricComplement (metricComplement A) = A := by
  have er : radius A = r := by
    apply le_antisymm (radius_upper ca)
    obtain ⟨b,hb⟩ := hb
    exact (distance_lower ha (fun a ha => by simpa [hammingDist_comm] using sep a ha b hb)).trans
      (distance_le_radius A b)
  have bm : B ⊆ metricComplement A := by
    intro b hb
    change distanceTo A b = radius A
    rw [er]
    exact le_antisymm ((distance_le_radius A b).trans_eq er)
      (distance_lower ha (fun a ha => by simpa [hammingDist_comm] using sep a ha b hb))
  have hm : (metricComplement A).Nonempty := hb.mono bm
  have sm (a : Word) (ha : a ∈ A) (b : Word) (hb : b ∈ metricComplement A) :
      r ≤ hammingDist a b := by
    have he : distanceTo A b = r := hb.trans er
    rw [hammingDist_comm, ← he]
    exact distance_upper ha
  have cm : ∀ x, ∃ b ∈ metricComplement A, hammingDist x b ≤ r := by
    intro x
    obtain ⟨b,hb,hd⟩ := cb x
    exact ⟨b,bm hb,hd⟩
  have em : radius (metricComplement A) = r := by
    apply le_antisymm (radius_upper cm)
    obtain ⟨a,ha⟩ := ha
    exact (distance_lower hm (sm a ha)).trans (distance_le_radius _ a)
  ext x
  constructor
  · intro hx
    by_contra hn
    obtain ⟨b,hb,hd⟩ := strict x hn
    have he : distanceTo (metricComplement A) x = r := hx.trans em
    have hu := distance_upper (x := x) (bm hb)
    omega
  · intro hx
    change distanceTo (metricComplement A) x = radius (metricComplement A)
    rw [em]
    exact le_antisymm ((distance_le_radius _ x).trans_eq em) (distance_lower hm (sm x hx))

lemma encode_add (f : Word) (a b : Param) : encode f (a+b) = encode f a + encode f b := by
  ext i
  simp only [encode, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ring
lemma encode_zero (f : Word) : encode f 0 = 0 := by
  ext i
  simp [encode]
lemma hamming_translate (x y z : Word) : hammingDist (x+z) (y+z) = hammingDist x y := by
  exact hammingDist_comp (fun i t => t+z i) (fun i => add_left_injective (z i))
lemma word_twice (x : Word) : x+x=0 := CharTwo.add_self_eq_zero x

def q : Word := fun i => point i 0 * point i 1 + point i 2 * point i 3
def g : Word := fun i => point i 0 * point i 1 + point i 0 * point i 3 + point i 1 * point i 2

def coeff (w : Word) : Param := ![w 0, w 1+w 0, w 2+w 0, w 4+w 0,
  w 8+w 0, w 3+w 1+w 2+w 0]
def free : Fin 10 → Fin 16 := ![5,6,7,9,10,11,12,13,14,15]
def embed (s : Fin 10 → Bit) : Word := ![0,0,0,0,0,s 0,s 1,s 2,0,s 3,s 4,s 5,s 6,s 7,s 8,s 9]
def syndrome (w : Word) : Fin 10 → Bit := fun j => (w+encode q (coeff w)) (free j)
lemma point_table : point = ![![0,0,0,0],![1,0,0,0],![0,1,0,0],![1,1,0,0],![0,0,1,0],![1,0,1,0],![0,1,1,0],![1,1,1,0],![0,0,0,1],![1,0,0,1],![0,1,0,1],![1,1,0,1],![0,0,1,1],![1,0,1,1],![0,1,1,1],![1,1,1,1]] := by decide +kernel
lemma decompose (w : Word) : w = encode q (coeff w) + embed (syndrome w) := by
  ext i
  fin_cases i <;> simp [syndrome, embed, free, encode, coeff, q, point_table, Fin.sum_univ_succ] <;>
    ring_nf <;> simp [show (2 : Bit) = 0 by decide, show (4 : Bit) = 0 by decide, show (6 : Bit) = 0 by decide, show (8 : Bit) = 0 by decide, show (10 : Bit) = 0 by decide, show (14 : Bit) = 0 by decide]
lemma embed_zero : embed 0 = 0 := by decide +kernel
lemma syndrome_ne_zero {w : Word} (h : w ∉ Code q) : syndrome w ≠ 0 := by
  intro he
  apply h
  refine ⟨coeff w, ?_⟩
  simpa [he, embed_zero] using (decompose w).symm

def paramEquiv : Param ≃ Fin 64 := finFunctionFinEquiv
def syndromeEquiv : (Fin 10 → Bit) ≃ Fin 1024 := finFunctionFinEquiv
def wordEquiv : Word ≃ Fin 65536 := finFunctionFinEquiv
def friend : Fin 6 → Word := fun j => wordEquiv.symm (![13984,14944,22208,23648,39616,40096] j)
def nearCodeRows : Fin 32 → Fin 32 → Fin 64 := ![
  ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,24],
  ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,24,0,0,0,0,0,0,0,24,0,0,0,24,0,24,24,24],
  ![0,0,0,0,0,0,0,47,0,0,0,0,0,0,0,47,0,0,0,0,0,0,0,47,0,0,0,31,0,0,0,24],
  ![0,0,0,0,0,0,0,47,0,0,0,0,0,27,0,24,0,0,0,0,0,0,29,24,55,55,55,24,55,24,24,24],
  ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,0,0,0,0,0,0,0,0,0,0,0,6,0,0,42,6],
  ![0,0,0,0,0,0,0,0,0,0,0,0,0,2,42,2,0,50,0,50,0,50,29,24,0,50,0,6,0,2,24,24],
  ![0,0,0,0,0,0,0,8,0,0,0,0,0,0,20,8,0,0,36,36,0,0,29,8,0,0,36,6,0,0,20,6],
  ![0,0,0,0,32,32,29,8,0,0,0,0,32,2,20,2,0,12,29,12,29,12,29,29,16,12,16,6,16,2,29,24],
  ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,0,44,0,0,0,6,0,44,0,6],
  ![0,0,0,0,0,0,0,0,0,0,52,52,0,27,52,24,0,0,0,0,0,44,4,4,0,0,52,6,0,24,4,24],
  ![0,0,0,0,0,0,0,8,0,34,0,34,0,27,0,8,0,0,0,0,0,18,0,8,0,34,0,6,0,18,0,6],
  ![0,0,0,0,32,27,32,8,0,27,10,10,27,27,10,27,0,0,0,0,32,18,4,4,16,16,10,6,16,27,4,24],
  ![0,0,0,0,0,0,0,8,0,0,0,6,0,0,42,6,0,0,0,6,0,44,0,6,0,6,6,6,23,6,6,6],
  ![0,0,0,15,32,32,32,8,0,0,52,6,32,2,32,63,0,50,0,6,32,32,4,63,16,6,6,6,16,63,63,63],
  ![0,0,0,8,32,8,8,8,0,34,0,6,32,8,8,8,0,0,36,6,32,8,8,8,16,6,6,6,16,6,6,6],
  ![32,32,32,8,32,32,32,8,16,16,10,6,32,27,32,8,16,12,16,6,32,32,29,8,16,16,16,6,16,16,16,63],
  ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,31,48,48,48,24],
  ![0,0,0,40,0,0,0,40,0,0,0,40,0,2,0,2,0,0,0,40,0,0,4,4,0,0,0,24,48,2,4,24],
  ![0,0,0,0,0,0,0,8,0,34,0,31,0,34,0,8,0,0,36,31,0,0,36,8,0,31,31,31,14,14,14,31],
  ![0,0,0,22,0,0,0,8,0,34,0,22,0,2,0,2,0,0,36,22,0,0,4,4,16,16,16,31,14,2,4,24],
  ![0,0,0,0,0,0,0,8,0,0,0,0,0,2,42,2,0,0,36,36,0,11,36,8,0,0,36,6,48,2,36,63],
  ![0,0,0,40,0,2,0,2,0,2,19,2,2,2,2,2,0,50,36,36,0,2,4,63,16,2,16,63,2,2,63,63],
  ![0,0,36,8,0,8,8,8,0,34,36,8,0,2,8,8,36,36,36,36,36,8,36,8,16,16,36,31,14,2,36,8],
  ![0,0,36,8,32,2,8,8,16,2,16,2,2,2,2,2,16,12,36,36,16,2,29,8,16,16,16,16,16,2,16,63],
  ![0,0,0,0,0,0,0,8,0,34,0,34,0,34,13,8,0,0,0,0,0,44,4,4,0,34,0,6,48,34,4,63],
  ![0,0,0,40,0,0,4,4,0,34,52,34,0,2,4,63,0,21,4,4,4,4,4,4,16,16,4,63,4,63,4,63],
  ![0,34,0,8,0,8,8,8,34,34,34,34,34,34,8,8,0,34,36,8,0,8,4,8,16,34,16,31,14,34,4,8],
  ![0,34,0,8,32,8,4,8,16,34,10,34,16,27,4,8,16,16,4,4,4,4,4,4,16,16,16,16,16,16,4,63],
  ![0,0,0,8,0,8,8,8,0,34,0,6,0,2,8,8,0,0,36,6,0,8,4,8,16,6,6,6,16,63,63,63],
  ![0,0,0,8,32,2,4,8,16,2,16,63,2,2,63,63,16,16,4,63,4,63,4,63,16,16,16,63,16,63,63,63],
  ![0,8,8,8,8,8,8,8,16,34,8,8,8,8,8,8,16,8,36,8,8,8,8,8,16,16,16,6,16,8,8,8],
  ![16,8,8,8,32,8,8,8,16,16,16,8,16,2,8,8,16,16,16,8,16,8,4,8,16,16,16,16,16,16,16,63]
]
def nearCode (s : Fin 1024) : Fin 64 :=
  nearCodeRows ⟨s.val / 32, by omega⟩ ⟨s.val % 32, Nat.mod_lt _ (by decide)⟩
def nearFriendRows : Fin 32 → Fin 32 → Fin 6 := ![
  ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,2,0,0,0,0,0,0,2,0],
  ![0,0,0,0,0,0,2,4,0,0,0,0,0,0,4,0,0,0,2,2,2,4,2,2,0,0,2,0,4,0,2,0],
  ![0,0,0,0,0,0,0,0,0,0,1,1,0,0,2,0,0,0,0,0,0,0,2,0,0,0,1,0,0,0,2,0],
  ![0,1,0,1,0,1,3,1,0,1,1,1,0,0,4,1,0,3,3,3,2,5,2,3,0,0,1,1,0,0,2,0],
  ![0,0,0,1,0,0,0,3,0,0,0,1,0,0,0,0,0,0,0,1,0,0,3,3,0,0,0,0,0,0,0,0],
  ![0,0,0,1,0,0,2,5,1,1,1,1,1,0,1,1,0,0,2,1,3,0,2,3,2,0,2,1,4,0,2,0],
  ![0,0,0,1,0,0,0,0,0,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  ![0,1,0,1,0,0,0,1,1,1,1,1,0,0,1,1,0,0,0,1,0,0,0,0,0,0,1,1,0,0,0,0],
  ![0,0,0,1,0,0,0,1,0,0,0,1,1,1,1,1,0,0,0,1,0,0,2,1,0,0,0,0,2,0,2,1],
  ![0,0,0,3,0,0,2,4,0,0,0,0,1,0,1,1,0,0,3,3,3,0,2,3,0,0,0,0,5,0,2,0],
  ![0,0,0,3,0,0,0,0,0,0,2,1,2,0,2,1,1,3,2,3,1,0,2,2,2,0,2,2,2,0,2,2],
  ![0,2,0,3,0,0,0,3,0,0,0,1,0,0,2,1,1,3,3,3,1,3,2,3,0,0,2,3,2,0,2,2],
  ![0,1,1,1,0,3,1,1,0,4,4,1,2,5,1,1,0,4,4,1,0,0,4,3,0,0,0,0,0,0,2,0],
  ![0,3,1,1,0,0,1,4,2,4,1,1,1,4,1,1,0,0,5,3,0,0,4,0,0,0,2,0,4,0,1,0],
  ![0,1,3,1,0,0,0,0,0,0,5,1,0,0,2,0,2,4,2,3,0,0,2,0,0,0,2,0,0,0,2,0],
  ![0,1,0,1,0,0,0,0,0,1,1,1,0,0,1,1,0,3,3,3,0,0,0,0,0,0,1,1,0,0,1,0],
  ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,1,0,2,2,2,0,1,0,0,0,0,0,0],
  ![0,0,0,0,0,0,2,0,1,1,3,0,1,0,4,0,0,1,3,1,3,5,2,2,1,1,3,1,1,1,3,0],
  ![0,0,0,0,1,3,1,0,0,0,4,0,3,0,4,0,0,4,0,0,1,5,1,2,0,0,0,0,0,0,2,0],
  ![0,2,0,0,4,5,4,4,2,1,4,1,4,4,4,4,0,5,0,3,5,5,4,5,0,1,3,1,4,5,4,4],
  ![0,0,0,3,0,0,0,0,1,2,3,3,2,0,0,0,0,2,0,1,0,0,0,2,2,2,0,2,0,0,0,0],
  ![1,2,1,1,2,0,2,2,1,1,1,1,1,0,2,0,1,1,1,1,3,3,2,1,1,1,2,1,3,0,0,0],
  ![0,0,0,0,3,0,0,0,1,0,1,1,3,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  ![2,2,0,1,2,2,2,1,1,1,1,1,3,0,4,1,0,2,0,1,3,5,0,1,0,0,0,1,0,0,0,0],
  ![0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,1,0,1,0,0,0,1,0,0,0,0,0,0,0,0],
  ![0,0,0,0,0,0,0,0,1,0,0,0,1,0,1,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0],
  ![0,0,0,0,1,0,0,0,0,0,0,0,1,0,2,0,1,1,0,1,1,1,1,1,0,0,0,0,1,0,2,2],
  ![0,0,0,0,0,0,0,0,0,0,0,0,1,0,4,3,0,3,0,3,1,5,0,3,0,0,0,3,1,2,2,2],
  ![0,3,1,1,0,0,0,0,2,2,4,3,2,2,2,0,0,5,0,1,0,0,0,0,0,2,0,0,0,0,0,0],
  ![1,3,1,1,0,0,1,0,1,3,1,0,1,0,1,0,0,3,1,1,0,0,0,0,0,0,0,0,0,0,0,0],
  ![0,0,0,0,0,0,0,0,0,0,4,0,2,0,2,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,2,0],
  ![0,2,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,2,0,2,0,4,0,0,0,0,0,0,0,0,0,0]
]
def nearFriend (s : Fin 1024) : Fin 6 :=
  nearFriendRows ⟨s.val / 32, by omega⟩ ⟨s.val % 32, Nat.mod_lt _ (by decide)⟩
def nearDeepCodeRows : Fin 32 → Fin 32 → Fin 64 := ![
  ![0,0,6,20,0,0,6,36,0,0,8,29,0,0,36,36,0,0,8,20,0,0,0,34,0,0,8,0,0,0,0,0],
  ![2,16,24,29,12,16,16,34,12,29,29,29,12,0,0,29,2,32,27,27,10,31,0,27,32,32,32,29,36,0,0,0],
  ![0,0,6,42,0,0,6,0,0,0,0,0,0,0,0,0,0,0,42,42,0,0,0,0,0,0,50,0,0,0,0,0],
  ![2,0,24,0,50,42,44,0,50,0,0,0,50,0,0,0,2,0,0,0,52,0,0,0,0,0,0,0,0,0,0,0],
  ![0,0,24,0,0,0,31,32,0,0,47,0,0,0,0,0,0,0,47,55,0,0,32,32,0,0,47,0,0,0,0,0],
  ![24,55,24,0,55,55,16,36,0,0,0,0,47,0,0,0,27,0,32,0,8,0,16,32,32,0,32,0,36,0,32,0],
  ![0,0,24,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  ![24,0,24,0,0,0,24,0,0,0,0,0,0,0,0,0,0,0,24,0,0,0,0,0,0,0,0,0,0,0,0,0],
  ![6,16,6,16,6,16,6,32,8,32,8,32,8,32,32,32,8,32,8,16,34,0,0,16,8,32,8,8,0,0,0,32],
  ![16,16,63,0,16,16,55,34,32,32,8,29,8,16,8,32,27,32,0,0,47,16,0,0,32,32,8,32,34,32,0,32],
  ![6,23,6,0,6,0,6,6,44,0,0,0,0,0,0,32,6,0,0,0,63,0,0,0,0,0,0,0,0,0,0,0],
  ![63,24,63,0,6,16,6,0,32,32,63,0,50,0,0,0,6,0,0,0,6,0,0,0,32,32,0,0,0,0,0,0],
  ![18,10,27,0,34,29,27,27,18,8,32,0,36,16,27,32,27,63,16,16,34,0,16,32,0,0,8,0,0,0,0,0],
  ![27,36,34,0,16,16,27,34,29,8,0,0,8,8,0,0,27,27,8,0,27,0,16,10,27,32,32,32,36,0,18,0],
  ![44,52,50,0,0,0,6,0,44,0,63,0,0,0,0,0,42,63,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  ![24,0,24,0,0,0,6,52,44,0,0,0,0,0,0,0,27,0,0,0,0,0,52,52,0,0,0,0,0,0,44,0],
  ![2,14,8,36,16,16,31,36,8,36,8,36,36,36,36,36,2,16,8,16,34,34,34,34,8,36,8,8,0,0,8,36],
  ![2,16,63,16,16,16,16,16,8,36,34,29,8,16,0,36,2,36,34,16,8,0,16,34,36,36,34,36,8,36,34,36],
  ![2,48,63,36,2,4,2,36,11,0,0,36,63,0,0,36,2,24,2,42,63,0,2,34,0,0,8,0,0,0,0,0],
  ![2,63,63,63,0,0,0,0,4,0,0,0,0,0,0,0,2,0,2,0,0,0,0,0,2,36,34,0,0,0,0,0],
  ![14,14,31,16,31,0,31,31,22,8,16,16,36,0,31,36,34,8,8,16,34,0,31,34,8,8,8,8,0,0,0,0],
  ![31,63,34,0,16,16,16,16,0,0,0,0,8,0,16,36,31,31,31,0,8,8,16,14,31,36,32,0,8,0,22,0],
  ![48,48,24,48,63,0,31,0,40,0,0,0,63,0,63,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  ![63,63,24,0,16,63,16,0,0,0,0,0,63,0,0,0,2,63,2,0,8,0,40,48,0,0,40,0,0,0,40,0],
  ![8,16,8,16,16,16,6,16,8,8,8,8,8,16,8,36,8,16,8,16,34,16,8,16,8,8,8,8,8,0,8,8],
  ![16,16,63,16,16,16,16,16,8,16,8,4,8,16,8,16,2,16,8,16,16,16,8,16,8,32,8,8,8,16,8,8],
  ![63,16,63,63,63,16,6,6,8,0,8,4,8,0,0,36,63,16,8,16,63,63,63,16,8,0,8,8,63,0,0,0],
  ![63,16,63,63,16,16,63,16,63,4,63,4,8,16,0,48,2,0,63,0,63,0,63,0,2,32,8,0,8,40,0,0],
  ![34,36,34,16,34,16,31,16,36,8,32,16,36,36,36,36,34,32,8,16,34,34,34,34,8,8,8,8,34,0,8,0],
  ![34,36,34,34,16,16,34,16,8,36,34,4,8,16,8,4,27,36,34,16,34,16,34,10,8,32,8,4,34,0,8,0],
  ![34,48,63,4,34,0,6,0,44,0,32,4,36,0,0,0,34,63,8,13,34,0,34,0,0,0,8,0,0,0,0,0],
  ![63,63,63,4,16,16,63,4,4,4,4,4,21,0,0,4,2,2,63,2,34,6,34,52,0,0,4,4,0,0,40,0]
]
def nearDeepCode (s : Fin 1024) : Fin 64 :=
  nearDeepCodeRows ⟨s.val / 32, by omega⟩ ⟨s.val % 32, Nat.mod_lt _ (by decide)⟩

theorem bent_pair : Bent q ∧ Bent g ∧ Bent (q+g) := by
  have h : ∀ a : Fin 16,
      (∑ i : Fin 16, (-1 : ℤ) ^ (q i + ∑ j, point a j * point i j).val)^2=16 ∧
      (∑ i : Fin 16, (-1 : ℤ) ^ (g i + ∑ j, point a j * point i j).val)^2=16 ∧
      (∑ i : Fin 16, (-1 : ℤ) ^ ((q+g) i + ∑ j, point a j * point i j).val)^2=16 := by decide +kernel
  have hp (a : Point) : point (finFunctionFinEquiv a) = a := Equiv.symm_apply_apply _ _
  exact ⟨fun a => by simpa only [hp] using (h (finFunctionFinEquiv a)).1,
    fun a => by simpa only [hp] using (h (finFunctionFinEquiv a)).2.1,
    fun a => by simpa only [hp] using (h (finFunctionFinEquiv a)).2.2⟩

theorem deep_separation : ∀ (j : Fin 6) (c : Param), 6 ≤ hammingDist (encode q c) (friend j) := by
  have h : ∀ (j : Fin 6) (k : Fin 64),
      6 ≤ hammingDist (encode q (paramEquiv.symm k)) (friend j) := by decide +kernel
  intro j c
  simpa using h j (paramEquiv c)

theorem cover_code : ∀ s : Fin 1024,
    hammingDist (embed (syndromeEquiv.symm s)) (encode q (paramEquiv.symm (nearCode s))) ≤ 6 := by
  decide +kernel

theorem cover_deep : ∀ s : Fin 1024,
    hammingDist (embed (syndromeEquiv.symm s))
      (friend (nearFriend s) + encode q (paramEquiv.symm (nearDeepCode s))) ≤
        if s=0 then 6 else 5 := by
  decide +kernel


def deepSet : Set Word := {w | ∃ j : Fin 6, ∃ c : Param, w = friend j + encode q c}

lemma code_nonempty : (Code q).Nonempty := ⟨encode q 0, 0, rfl⟩
lemma deep_nonempty : deepSet.Nonempty := ⟨friend 0 + encode q 0, 0, 0, rfl⟩

lemma separation : ∀ a ∈ Code q, ∀ b ∈ deepSet, 6 ≤ hammingDist a b := by
  rintro _ ⟨a,rfl⟩ _ ⟨j,b,rfl⟩
  rw [← hamming_translate (encode q a) (friend j + encode q b) (encode q b)]
  rw [← encode_add, add_assoc, word_twice, add_zero]
  exact deep_separation j (a+b)

lemma shifted_distance (w v : Word) :
    hammingDist w (encode q (coeff w)+v) = hammingDist (embed (syndrome w)) v := by
  calc
    _ = hammingDist (encode q (coeff w)+embed (syndrome w)) (encode q (coeff w)+v) :=
      congrArg (fun x => hammingDist x (encode q (coeff w)+v)) (decompose w)
    _ = _ := by
      rw [add_comm (encode q (coeff w)) (embed (syndrome w)),
        add_comm (encode q (coeff w)) v, hamming_translate]

lemma code_cover : ∀ w : Word, ∃ a ∈ Code q, hammingDist w a ≤ 6 := by
  intro w
  let s := syndromeEquiv (syndrome w)
  let a := paramEquiv.symm (nearCode s)
  refine ⟨encode q (coeff w+a), ⟨coeff w+a,rfl⟩, ?_⟩
  rw [encode_add, shifted_distance]
  simpa [s,a] using cover_code s

lemma syndrome_index_zero (s : Fin 10 → Bit) : syndromeEquiv s=0 ↔ s=0 := by
  have hz : syndromeEquiv 0=0 := by decide +kernel
  constructor
  · intro h
    exact syndromeEquiv.injective (h.trans hz.symm)
  · rintro rfl
    exact hz

lemma deep_cover : ∀ w : Word, ∃ b ∈ deepSet,
    hammingDist w b ≤ if syndrome w=0 then 6 else 5 := by
  intro w
  let s := syndromeEquiv (syndrome w)
  let a := paramEquiv.symm (nearDeepCode s)
  let j := nearFriend s
  refine ⟨encode q (coeff w)+(friend j+encode q a), ?_, ?_⟩
  · refine ⟨j,coeff w+a,?_⟩
    rw [encode_add]
    abel
  · rw [shifted_distance]
    simpa [s,a,j,syndrome_index_zero] using cover_deep s

lemma deep_cover_all : ∀ w : Word, ∃ b ∈ deepSet, hammingDist w b ≤ 6 := by
  intro w
  obtain ⟨b,hb,hd⟩ := deep_cover w
  refine ⟨b,hb,hd.trans ?_⟩
  split_ifs <;> omega
lemma deep_cover_strict : ∀ w ∉ Code q, ∃ b ∈ deepSet, hammingDist w b < 6 := by
  intro w hw
  obtain ⟨b,hb,hd⟩ := deep_cover w
  rw [if_neg (syndrome_ne_zero hw)] at hd
  exact ⟨b,hb,by omega⟩

theorem q_metric_regular : metricComplement (metricComplement (Code q)) = Code q :=
  regular_of_certificate (Code q) deepSet 6 code_nonempty deep_nonempty
    separation code_cover deep_cover_all deep_cover_strict

end BentMetric
theorem BentMetric.metric_regular_bent_code : ∃ f g : BentMetric.Word,
  BentMetric.Bent f ∧ BentMetric.Bent g ∧ BentMetric.Bent (f + g) ∧
  BentMetric.metricComplement (BentMetric.metricComplement (BentMetric.Code f)) =
    BentMetric.Code f := by
  exact ⟨BentMetric.q, BentMetric.g, BentMetric.bent_pair.1, BentMetric.bent_pair.2.1,
    BentMetric.bent_pair.2.2, BentMetric.q_metric_regular⟩

#print axioms BentMetric.metric_regular_bent_code
