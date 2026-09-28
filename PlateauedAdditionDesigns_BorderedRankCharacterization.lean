import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.FieldTheory.Finiteness
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum


/-!
# Bordered-rank characterization of plateaued addition designs

A self-contained answer to Open Problem 4 of Hyun, Kwon, Wang and Wu,
"Designs, linear codes, plateaued functions, and their interconnections"
(arXiv:2605.24355v1), replacing Theorem 3(iii)'s rank-plus-Reed--Muller test.

For every simple design with the paper's nondegenerate parameters (n=m-r even,
n>=4), the canonical bordered incidence matrix has binary rank m+2 if and only
if the design is the Walsh-support addition design of an r-plateaued Boolean
function with no nonzero linear structures. The theorem covers every r>=1,
and also r=0. It does not assume a Reed--Muller code embedding or a block count.

All ingredients are proved here: normalized/bordered rank, triple symmetric
difference closure, design double counting, binary character orthogonality,
Walsh reconstruction, exact support identification, and the converse. Thus
the plateaued-realization equivalence is not imported from the paper.

The final section gives a simple 2-(64,28,24) design with 128 blocks and original
incidence rank 9, but without TSDP or the required plateaued realization. This
shows that the UNBORDERED incidence-rank threshold alone fails already for r=1.

Main declarations: PlateauedDesign.open_problem_4,
PlateauedDesign.polynomial_parameters, SumFreeCounterexample.counterexample,
and SumFreeCounterexample.not_plateaued_addition_design.
Only Mathlib is imported. No dimension-six MUB nonexistence claim is made.
-/
namespace BinaryDesignRank

abbrev F₂ := ZMod 2

@[simp] theorem two_eq_zero : (2 : F₂) = 0 := rfl
@[simp] theorem four_eq_zero : (4 : F₂) = 0 := by decide

def normalizedColumn {P B : Type*} (M : P → B → F₂)
    (p₀ : P) (b₀ b : B) (p : P) : F₂ :=
  M p b + M p b₀ + M p₀ b + M p₀ b₀

def TripleSymmetricDifference {P B : Type*} (M : P → B → F₂) : Prop :=
  ∀ a b c, ∃ d ε, ∀ p, M p a + M p b + M p c = M p d + ε

theorem rank_saturation {P B : Type*} [Fintype P] [Fintype B]
    (v : B → P → F₂) (b₀ : B) (hzero : v b₀ = 0)
    (hinj : Function.Injective v) (m : ℕ) (hcard : Fintype.card B = 2^m) :
    Module.finrank F₂ (Submodule.span F₂ (Set.range v)) = m ↔
      ∀ a b, ∃ c, v c = v a + v b := by
  classical
  let W := Submodule.span F₂ (Set.range v)
  let f : B → W := fun b => ⟨v b, Submodule.subset_span ⟨b, rfl⟩⟩
  have hf : Function.Injective f := fun a b h => hinj (congrArg Subtype.val h)
  have hcW : Fintype.card W = 2 ^ Module.finrank F₂ W := by
    simpa [F₂] using (Module.card_eq_pow_finrank (K := F₂) (V := W))
  constructor
  · intro hr
    have hsize : Fintype.card B = Fintype.card W := by rw [hcW, hr, hcard]
    have hs := ((Fintype.bijective_iff_injective_and_card f).2 ⟨hf, hsize⟩).2
    intro a b
    obtain ⟨c, hc⟩ := hs (f a + f b)
    exact ⟨c, congrArg Subtype.val hc⟩
  · intro hadd
    let S : Submodule F₂ (P → F₂) :=
      { carrier := Set.range v
        zero_mem' := ⟨b₀, hzero⟩
        add_mem' := by
          rintro x y ⟨a, rfl⟩ ⟨b, rfl⟩
          exact hadd a b
        smul_mem' := by
          intro c x hx
          fin_cases c
          · change (0 : F₂) • x ∈ Set.range v
            simpa only [zero_smul] using (show (0 : P → F₂) ∈ Set.range v from ⟨b₀, hzero⟩)
          · change (1 : F₂) • x ∈ Set.range v
            simpa only [one_smul] using hx }
    have hWS : W = S := by
      apply le_antisymm
      · exact Submodule.span_le.mpr (fun x hx => hx)
      · rintro x ⟨b, rfl⟩
        exact Submodule.subset_span ⟨b, rfl⟩
    have hs : Function.Surjective f := by
      intro x
      have hx : x.val ∈ S := hWS ▸ x.property
      obtain ⟨b, hb⟩ := hx
      exact ⟨b, Subtype.ext hb⟩
    have hsize := Fintype.card_of_bijective ⟨hf, hs⟩
    have hp : 2 ^ Module.finrank F₂ W = 2 ^ m := by
      rw [← hcW, ← hsize, hcard]
    exact Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ)) hp

theorem normalization_zero {P B : Type*} (M : P → B → F₂) (p₀ : P) (b₀ : B) :
    normalizedColumn M p₀ b₀ b₀ = 0 := by
  funext p
  simp only [normalizedColumn, Pi.zero_apply]
  ring_nf
  simp only [two_eq_zero, four_eq_zero, mul_zero, add_zero, zero_add]

theorem normalization_injective {P B : Type*} (M : P → B → F₂) (p₀ : P) (b₀ : B)
    (hsep : ∀ a b ε, (∀ p, M p a = M p b + ε) → a = b) :
    Function.Injective (normalizedColumn M p₀ b₀) := by
  intro a b h
  apply hsep a b (M p₀ a + M p₀ b)
  intro p
  have hp := congrFun h p
  simp only [normalizedColumn] at hp
  calc
    M p a = (M p a + M p b₀ + M p₀ a + M p₀ b₀) +
        M p b₀ + M p₀ a + M p₀ b₀ := by ring_nf; simp only [two_eq_zero, four_eq_zero, mul_zero, add_zero, zero_add]
    _ = (M p b + M p b₀ + M p₀ b + M p₀ b₀) +
        M p b₀ + M p₀ a + M p₀ b₀ := by rw [hp]
    _ = M p b + (M p₀ a + M p₀ b) := by ring_nf; simp only [two_eq_zero, four_eq_zero, mul_zero, add_zero, zero_add]

theorem normalization_closure {P B : Type*} (M : P → B → F₂) (p₀ : P) (b₀ : B) :
    (∀ a b, ∃ c, normalizedColumn M p₀ b₀ c =
      normalizedColumn M p₀ b₀ a + normalizedColumn M p₀ b₀ b) ↔
    TripleSymmetricDifference M := by
  constructor
  · intro hadd a b c
    obtain ⟨e, he⟩ := hadd a b
    obtain ⟨d, hd⟩ := hadd e c
    have hh : normalizedColumn M p₀ b₀ d =
        normalizedColumn M p₀ b₀ a + normalizedColumn M p₀ b₀ b +
          normalizedColumn M p₀ b₀ c := by rw [hd, he]
    refine ⟨d, M p₀ a + M p₀ b + M p₀ c + M p₀ d, ?_⟩
    intro p
    have hp := congrFun hh p
    simp only [normalizedColumn, Pi.add_apply] at hp
    calc
      M p a + M p b + M p c =
          ((M p a + M p b₀ + M p₀ a + M p₀ b₀) +
           (M p b + M p b₀ + M p₀ b + M p₀ b₀) +
           (M p c + M p b₀ + M p₀ c + M p₀ b₀)) +
           M p b₀ + M p₀ b₀ + M p₀ a + M p₀ b + M p₀ c := by ring_nf; simp only [two_eq_zero, four_eq_zero, mul_zero, add_zero, zero_add]
      _ = (M p d + M p b₀ + M p₀ d + M p₀ b₀) +
           M p b₀ + M p₀ b₀ + M p₀ a + M p₀ b + M p₀ c := by rw [← hp]
      _ = M p d + (M p₀ a + M p₀ b + M p₀ c + M p₀ d) := by ring_nf; simp only [two_eq_zero, four_eq_zero, mul_zero, add_zero, zero_add]
  · intro ht a b
    obtain ⟨c, ε, hc⟩ := ht a b b₀
    refine ⟨c, ?_⟩
    funext p
    have hp := hc p
    have h₀ := hc p₀
    simp only [normalizedColumn, Pi.add_apply]
    calc
      M p c + M p b₀ + M p₀ c + M p₀ b₀ =
          (M p c + ε) + (M p₀ c + ε) + M p b₀ + M p₀ b₀ := by ring_nf; simp only [two_eq_zero, four_eq_zero, mul_zero, add_zero, zero_add]
      _ = (M p a + M p b + M p b₀) +
          (M p₀ a + M p₀ b + M p₀ b₀) + M p b₀ + M p₀ b₀ := by rw [← hp, ← h₀]
      _ = (M p a + M p b₀ + M p₀ a + M p₀ b₀) +
          (M p b + M p b₀ + M p₀ b + M p₀ b₀) := by ring

/-- Exact numerical TSDP criterion for every complement-free simple block family. -/
theorem normalized_rank_iff {P B : Type*} [Fintype P] [Fintype B]
    (M : P → B → F₂) (p₀ : P) (b₀ : B) (m : ℕ)
    (hcard : Fintype.card B = 2^m)
    (hsep : ∀ a b ε, (∀ p, M p a = M p b + ε) → a = b) :
    Module.finrank F₂ (Submodule.span F₂ (Set.range (normalizedColumn M p₀ b₀))) = m ↔
      TripleSymmetricDifference M := by
  exact (rank_saturation _ b₀ (normalization_zero M p₀ b₀)
    (normalization_injective M p₀ b₀ hsep) m hcard).trans
      (normalization_closure M p₀ b₀)

end BinaryDesignRank

namespace BinaryDesignRank

/-- The canonical bordered incidence matrix, with one all-one row and column. -/
def bordered {P B : Type*} (M : P → B → F₂) : Matrix (Option P) (Option B) F₂
  | some p, some b => M p b
  | some _, none => 1
  | none, some _ => 1
  | none, none => 0

set_option maxHeartbeats 1000000 in
/-- Bordering increases normalized binary rank by exactly two. -/
theorem bordered_rank {P B : Type*} [Fintype P] [Fintype B]
    (M : P → B → F₂) (p₀ : P) (b₀ : B) :
    Matrix.rank (bordered M) =
      Module.finrank F₂ (Submodule.span F₂ (Set.range (normalizedColumn M p₀ b₀))) + 2 := by
  classical
  let E : (P → F₂) →ₗ[F₂] (Option P → F₂) :=
    { toFun := fun f => fun p => match p with | none => 0 | some p => f p
      map_add' := by intro f g; funext p; cases p <;> rfl
      map_smul' := by intro c f; funext p; cases p <;> simp }
  have hE : Function.Injective E := by
    intro f g h
    funext p
    exact congrFun h (some p)
  let S := Submodule.span F₂ (Set.range (normalizedColumn M p₀ b₀))
  let U := S.map E
  let v : Option P → F₂ := fun p => match p with | none => 0 | some _ => 1
  let w : Option P → F₂ := fun p => match p with | none => 1 | some p => M p b₀
  let W := Submodule.span F₂ (Set.range (Matrix.col (bordered M)))
  have hzero : ∀ f ∈ S, f p₀ = 0 := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b,rfl⟩ := hx
      simp only [normalizedColumn]
      ring_nf
      simp only [two_eq_zero, mul_zero, add_zero]
    | zero => rfl
    | add x y hx hy ihx ihy => simp [ihx, ihy]
    | smul c x hx ih => simp [ih]
  have hU (f : Option P → F₂) (hf : f ∈ U) : f none = 0 ∧ f (some p₀) = 0 := by
    obtain ⟨g,hg,rfl⟩ := hf
    exact ⟨rfl,hzero g hg⟩
  have hv : v ∉ U := by
    intro h
    have hh := (hU v h).2
    exact one_ne_zero hh
  have hw : w ∉ U ⊔ Submodule.span F₂ {v} := by
    intro h
    obtain ⟨a,ha,b,hb,hab⟩ := Submodule.mem_sup.mp h
    obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hb
    have hh := congrFun hab none
    have hzeroa := (hU a ha).1
    change a none + c * 0 = 1 at hh
    rw [hzeroa, mul_zero, add_zero] at hh
    exact zero_ne_one hh
  have hcol (b : B) : Matrix.col (bordered M) (some b) =
      E (normalizedColumn M p₀ b₀ b) + (M p₀ b + M p₀ b₀) • v + w := by
    funext p
    cases p with
    | none => simp [bordered, Matrix.col, E, v, w]
    | some p =>
      simp only [Matrix.col, Matrix.transpose_apply, bordered, E, LinearMap.coe_mk, AddHom.coe_mk,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul, normalizedColumn, v, w, mul_one]
      ring_nf
      simp only [two_eq_zero, mul_zero, add_zero, zero_add]
  have hvW : v ∈ W := Submodule.subset_span ⟨none,by funext p; cases p <;> rfl⟩
  have hwW : w ∈ W := Submodule.subset_span ⟨some b₀,by funext p; cases p <;> rfl⟩
  have hUW : U ≤ W := by
    rintro f ⟨g,hg,rfl⟩
    induction hg using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b,rfl⟩ := hx
      have hc : Matrix.col (bordered M) (some b) ∈ W := Submodule.subset_span ⟨some b,rfl⟩
      have hr : E (normalizedColumn M p₀ b₀ b) =
          Matrix.col (bordered M) (some b) + (M p₀ b + M p₀ b₀) • v + w := by
        rw [hcol]
        ext p
        simp only [Pi.add_apply]
        ring_nf
        simp only [two_eq_zero, mul_zero, add_zero, zero_add]
      rw [hr]
      exact W.add_mem (W.add_mem hc (W.smul_mem _ hvW)) hwW
    | zero => simpa using W.zero_mem
    | add x y hx hy ihx ihy => simpa using W.add_mem ihx ihy
    | smul c x hx ih => simpa using W.smul_mem c ih
  have hW : W = (U ⊔ Submodule.span F₂ {v}) ⊔ Submodule.span F₂ {w} := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro f ⟨b,rfl⟩
      cases b with
      | none =>
        have hn : Matrix.col (bordered M) none = v := by funext p; cases p <;> rfl
        rw [hn]
        exact Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton v)))
      | some b =>
        rw [hcol]
        apply Submodule.add_mem
        · apply Submodule.add_mem
          · exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_map.mpr
              ⟨_,Submodule.subset_span ⟨b,rfl⟩,rfl⟩))
          · exact Submodule.smul_mem _ _
              (Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton v))))
        · exact Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton w))
    · exact sup_le (sup_le hUW (Submodule.span_le.mpr (by simpa using hvW)))
        (Submodule.span_le.mpr (by simpa using hwW))
  have hdim : Module.finrank F₂ U = Module.finrank F₂ S :=
    (Submodule.equivMapOfInjective E hE S).finrank_eq.symm
  rw [Matrix.rank_eq_finrank_span_cols]
  change Module.finrank F₂ W = Module.finrank F₂ S + 2
  rw [hW, Submodule.finrank_sup_span_singleton hw,
    Submodule.finrank_sup_span_singleton hv, hdim]

/-- A single bordered-rank test replaces rank plus Reed--Muller containment. -/
theorem bordered_rank_iff {P B : Type*} [Fintype P] [Fintype B]
    (M : P → B → F₂) (p₀ : P) (b₀ : B) (m : ℕ)
    (hcard : Fintype.card B = 2^m)
    (hsep : ∀ a b ε, (∀ p, M p a = M p b + ε) → a = b) :
    Matrix.rank (bordered M) = m + 2 ↔ TripleSymmetricDifference M := by
  rw [bordered_rank M p₀ b₀, Nat.add_right_cancel_iff]
  exact normalized_rank_iff M p₀ b₀ m hcard hsep

/-- Uniform blocks of size other than half the point count cannot be complements. -/
theorem uniform_separation {P B : Type*} [Fintype P]
    (M : P → B → F₂) (k : ℕ)
    (hsimple : Function.Injective (fun b p => M p b))
    (hsize : ∀ b, (Finset.univ.filter (fun p : P => M p b = 1)).card = k)
    (hk : 2 * k ≠ Fintype.card P) :
    ∀ a b ε, (∀ p, M p a = M p b + ε) → a = b := by
  classical
  intro a b ε h
  have he_all : ∀ x : F₂, x = 0 ∨ x = 1 := by decide +kernel
  have he := he_all ε
  rcases he with rfl | rfl
  · apply hsimple
    funext p
    simpa using h p
  · have hc : Finset.univ.filter (fun p : P => M p a = 1) =
        Finset.univ.filter (fun p : P => ¬ M p b = 1) := by
      apply Finset.filter_congr
      intro p hp
      rw [h p]
      generalize M p b = x
      revert x
      decide +kernel
    have hcount := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset P)) (fun p => M p b = 1)
    rw [← hc, hsize a, hsize b, Finset.card_univ] at hcount
    exact (hk (by omega)).elim

/-- TSDP only needs to be checked on pairwise distinct blocks, as in the paper. -/
theorem tsdp_iff_distinct {P B : Type*} (M : P → B → F₂) :
    TripleSymmetricDifference M ↔
      ∀ a b c, a ≠ b → a ≠ c → b ≠ c →
        ∃ d ε, ∀ p, M p a + M p b + M p c = M p d + ε := by
  constructor
  · intro h a b c hab hac hbc
    exact h a b c
  · intro h a b c
    by_cases hab : a = b
    · subst b
      refine ⟨c,0,fun p => ?_⟩
      simp [CharTwo.add_self_eq_zero]
    by_cases hac : a = c
    · subst c
      refine ⟨b,0,fun p => ?_⟩
      ring_nf
      simp [two_eq_zero]
    by_cases hbc : b = c
    · subst c
      refine ⟨a,0,fun p => ?_⟩
      ring_nf
      simp [two_eq_zero]
    exact h a b c hab hac hbc

/-- The rank test for simple uniform designs, without a code-embedding assumption. -/
theorem uniform_bordered_rank_iff {P B : Type*} [Fintype P] [Fintype B]
    (M : P → B → F₂) (p₀ : P) (b₀ : B) (m k : ℕ)
    (hcard : Fintype.card B = 2^m)
    (hsimple : Function.Injective (fun b p => M p b))
    (hsize : ∀ b, (Finset.univ.filter (fun p : P => M p b = 1)).card = k)
    (hk : 2 * k ≠ Fintype.card P) :
    Matrix.rank (bordered M) = m + 2 ↔
      ∀ a b c, a ≠ b → a ≠ c → b ≠ c →
        ∃ d ε, ∀ p, M p a + M p b + M p c = M p d + ε := by
  exact (bordered_rank_iff M p₀ b₀ m hcard
    (uniform_separation M k hsimple hsize hk)).trans (tsdp_iff_distinct M)

end BinaryDesignRank

namespace PlateauedDesign
open scoped BigOperators
abbrev Bit := ZMod 2
abbrev Cube (ι : Type*) := ι → Bit

theorem bit_cases (x : Bit) : x=0 ∨ x=1 :=
  (by decide : ∀ x : ZMod 2, x=0 ∨ x=1) x

def sign (x : Bit) : ℤ := if x=0 then 1 else -1

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
noncomputable def char (u x : Cube ι) : ℤ := sign (dotProduct u x)
def size (ι : Type*) [Fintype ι] [DecidableEq ι] : ℤ := Fintype.card (Cube ι)

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

noncomputable def walsh (f : Cube ι → ℤ) (u : Cube ι) : ℤ :=
  ∑ x, f x*char u x

/-- Unnormalized Walsh inversion with a concrete binary character system. -/
theorem inversion (f : Cube ι → ℤ) (x : Cube ι) :
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

theorem bilinear_parseval (f g : Cube ι → ℤ) :
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

theorem parseval (f : Cube ι → ℤ) :
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

theorem walsh_translate (f : Cube ι → ℤ) (a u : Cube ι) :
    walsh (fun x => f (x+a)) u = char u a*walsh f u := by
  have hs := Equiv.sum_comp (Equiv.addRight a) (fun x => f (x+a)*char u x)
  change (∑ x, f ((x+a)+a)*char u (x+a))=walsh (fun x => f (x+a)) u at hs
  simp_rw [add_assoc, twice, add_zero, char_add_right] at hs
  rw [← hs, walsh, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring


theorem sign_injective : Function.Injective sign := by
  exact (by decide : ∀ a b : Bit, sign a = sign b → a=b)

/-- The actual Walsh-support addition-design realization, including absence of
nonzero linear structures. No external reconstruction theorem is assumed. -/
def Realization {P B : Type*} (M : P → B → Bit) (m : ℕ) (A : ℤ) : Prop :=
  ∃ f : Cube (Fin m) → Bit, ∃ β : B ≃ Cube (Fin m),
    ∃ φ : P ≃ {u : Cube (Fin m) // walsh (fun x => sign (f x)) u ≠ 0},
    ∃ g : P → Bit,
    (∀ u, walsh (fun x => sign (f x)) u = 0 ∨
      walsh (fun x => sign (f x)) u = A ∨
      walsh (fun x => sign (f x)) u = -A) ∧
    (∀ p, walsh (fun x => sign (f x)) (φ p).val = A * sign (g p)) ∧
    (∀ p b, M p b = dotProduct (φ p).val (β b) + f (β b) + g p) ∧
    (∀ a c, (∀ x, f (x+a) = f x+c) → a=0)

theorem linearize {P B : Type*} [Fintype P] [Fintype B]
    (M : P → B → Bit) (p₀ : P) (b₀ : B) (m : ℕ)
    (hcard : Fintype.card B = 2^m)
    (hsep : ∀ a b ε, (∀ p, M p a = M p b+ε) → a=b)
    (hr : Module.finrank Bit (Submodule.span Bit
      (Set.range (BinaryDesignRank.normalizedColumn M p₀ b₀))) = m) :
    ∃ β : B ≃ Cube (Fin m), ∃ φ : P → Cube (Fin m),
      ∃ f : Cube (Fin m) → Bit, ∃ g : P → Bit,
        ∀ p b, M p b = dotProduct (φ p) (β b) + f (β b) + g p := by
  classical
  let W := Submodule.span Bit (Set.range (BinaryDesignRank.normalizedColumn M p₀ b₀))
  let j : B → W := fun b => ⟨_, Submodule.subset_span ⟨b,rfl⟩⟩
  have hj : Function.Injective j := fun a b h =>
    BinaryDesignRank.normalization_injective M p₀ b₀ hsep (congrArg Subtype.val h)
  have hcW : Fintype.card W = 2^m := by
    rw [Module.card_eq_pow_finrank (K := Bit), hr]
    simp [Bit]
  let e := (Module.finBasisOfFinrankEq Bit W hr).equivFun
  let β : B ≃ Cube (Fin m) := (Equiv.ofBijective j
    ((Fintype.bijective_iff_injective_and_card j).2 ⟨hj,hcard.trans hcW.symm⟩)).trans e.toEquiv
  let ℓ (p : P) : Module.Dual Bit (Cube (Fin m)) :=
    (LinearMap.proj p).comp (W.subtype.comp e.symm.toLinearMap)
  let φ (p : P) := (dotProductEquiv Bit (Fin m)).symm (ℓ p)
  refine ⟨β,φ,(fun x => M p₀ (β.symm x)),(fun p => M p b₀+M p₀ b₀),?_⟩
  intro p b
  have hd : dotProduct (φ p) (β b) = BinaryDesignRank.normalizedColumn M p₀ b₀ b p := by
    have h := LinearEquiv.apply_symm_apply (dotProductEquiv Bit (Fin m)) (ℓ p)
    have hh := congrArg (fun z : Module.Dual Bit (Cube (Fin m)) => z (β b)) h
    change dotProduct (φ p) (β b) = ℓ p (β b) at hh
    exact hh.trans (by simp [ℓ, β, j])
  simp only [hd, β.symm_apply_apply]
  simp only [BinaryDesignRank.normalizedColumn]
  ring_nf
  simp [BinaryDesignRank.two_eq_zero, show (3 : Bit)=1 from rfl]

theorem spectrum_from_columns {P : Type*} [Fintype P]
    (φ : P → Cube ι) (g : P → Bit) (f : Cube ι → Bit) (C : ℤ)
    (h : ∀ x, ∑ p, sign (g p)*char (φ p) x = C*sign (f x)) (u : Cube ι) :
    C * walsh (fun x => sign (f x)) u =
      size ι * ∑ p, if φ p=u then sign (g p) else 0 := by
  classical
  calc
    _ = ∑ x, (C*sign (f x))*char u x := by simp [walsh, Finset.mul_sum, mul_assoc]
    _ = ∑ x, (∑ p, sign (g p)*char (φ p) x)*char u x := by simp_rw [← h]
    _ = ∑ p, sign (g p)*(∑ x, char (φ p) x*char u x) := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      simp [Finset.mul_sum, mul_assoc]
    _ = ∑ p, sign (g p)*(if φ p=u then size ι else 0) := by
      simp_rw [char_comm (φ _), char_comm u, char_orthogonal]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      split_ifs <;> ring

theorem reconstruct {P B : Type*} [Fintype P] [Fintype B]
    (M : P → B → Bit) (m : ℕ) (C A : ℤ)
    (hC : C ≠ 0) (hA : A ≠ 0) (hCA : C*A = size (Fin m))
    (hsimple : Function.Injective (fun b p => M p b))
    (hrow : ∀ p q ε, (∀ b, M p b = M q b+ε) → p=q)
    (hsum : ∀ b, ∑ p, sign (M p b) = C)
    (β : B ≃ Cube (Fin m)) (φ : P → Cube (Fin m))
    (f : Cube (Fin m) → Bit) (g : P → Bit)
    (hrep : ∀ p b, M p b = dotProduct (φ p) (β b)+f (β b)+g p) :
    Realization M m A := by
  classical
  have hi : Function.Injective φ := by
    intro p q hpq
    apply hrow p q (g p+g q)
    intro b
    rw [hrep, hrep, hpq]
    ring_nf
    simp [BinaryDesignRank.two_eq_zero, show (3 : Bit)=1 from rfl]
  have hc : ∀ x, ∑ p, sign (g p)*char (φ p) x = C*sign (f x) := by
    intro x
    have hh := hsum (β.symm x)
    simp only [hrep, β.apply_symm_apply, sign_add] at hh
    calc
      _ = (∑ p, sign (dotProduct (φ p) x)*sign (f x)*sign (g p))*sign (f x) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro p _
        have hf := sign_sq (f x)
        unfold char
        calc
          _ = sign (g p)*sign (dotProduct (φ p) x)*(sign (f x))^2 := by rw [hf]; ring
          _ = _ := by ring
      _ = _ := by rw [hh]
  have hon : ∀ p, walsh (fun x => sign (f x)) (φ p) = A*sign (g p) := by
    intro p
    have hh := spectrum_from_columns φ g f C hc (φ p)
    simp only [hi.eq_iff] at hh
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at hh
    rw [← hCA] at hh
    apply mul_left_cancel₀ hC
    simpa only [mul_assoc] using hh
  have hoff : ∀ u, u ∉ Set.range φ → walsh (fun x => sign (f x)) u = 0 := by
    intro u hu
    have hh := spectrum_from_columns φ g f C hc u
    have hz : ∀ p, φ p ≠ u := fun p hp => hu ⟨p,hp⟩
    simp only [hz, if_false, Finset.sum_const_zero, mul_zero] at hh
    exact (mul_eq_zero.mp hh).resolve_left hC
  have hn : ∀ p, walsh (fun x => sign (f x)) (φ p) ≠ 0 := by
    intro p
    rw [hon]
    exact mul_ne_zero hA (by have hh := sign_sq (g p); intro hz; simp [hz] at hh)
  let ψ : P → {u : Cube (Fin m) // walsh (fun x => sign (f x)) u ≠ 0} :=
    fun p => ⟨φ p,hn p⟩
  have hψ : Function.Bijective ψ := by
    constructor
    · intro p q h; exact hi (congrArg Subtype.val h)
    · intro u
      have hu : u.val ∈ Set.range φ := by
        by_contra hh
        exact u.property (hoff u.val hh)
      obtain ⟨p,hp⟩ := hu
      exact ⟨p,Subtype.ext hp⟩
  refine ⟨f,β,Equiv.ofBijective ψ hψ,g,?_,hon,hrep,?_⟩
  · intro u
    by_cases hu : u ∈ Set.range φ
    · obtain ⟨p,rfl⟩ := hu
      rcases bit_cases (g p) with hp | hp
      · exact Or.inr (Or.inl (by rw [hon,hp,sign_zero,mul_one]))
      · exact Or.inr (Or.inr (by rw [hon,hp,sign_one,mul_neg_one]))
    · exact Or.inl (hoff u hu)
  · intro a c hlin
    have hs : ∀ p, dotProduct (φ p) a = c := by
      intro p
      have hh := walsh_translate (fun x => sign (f x)) a (φ p)
      have he : walsh (fun x => sign (f (x+a))) (φ p) =
          sign c * walsh (fun x => sign (f x)) (φ p) := by
        simp only [hlin, sign_add, walsh, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring
      rw [he] at hh
      exact sign_injective ((mul_right_cancel₀ (hn p) hh).symm)
    have he : β.symm a = β.symm 0 := by
      apply hsimple
      funext p
      simp only [hrep,β.apply_symm_apply,dotProduct_zero,zero_add,hs]
      have hf := hlin 0
      simp only [zero_add] at hf
      rw [hf]
      ring_nf
      simp [BinaryDesignRank.two_eq_zero, show (3 : Bit)=1 from rfl]
    exact β.symm.injective he

theorem realization_tsdp {P B : Type*} (M : P → B → Bit) (m : ℕ) (A : ℤ)
    (h : Realization M m A) : BinaryDesignRank.TripleSymmetricDifference M := by
  obtain ⟨f,β,φ,g,_,_,hrep,_⟩ := h
  intro a b c
  let d := β.symm (β a+β b+β c)
  refine ⟨d,f (β a)+f (β b)+f (β c)+f (β d),?_⟩
  intro p
  simp only [hrep]
  have hd : β d=β a+β b+β c := β.apply_symm_apply _
  rw [hd]
  simp only [dotProduct_add]
  ring_nf
  simp [BinaryDesignRank.two_eq_zero, show (3 : Bit)=1 from rfl]

def indicator (x : Bit) : ℤ := if x=1 then 1 else 0

theorem indicator_sq (x : Bit) : indicator x*indicator x=indicator x := by
  unfold indicator
  split_ifs <;> norm_num

theorem sign_indicator (x : Bit) : sign x = 1-2*indicator x := by
  exact (by decide : ∀ x : Bit, sign x = 1-2*indicator x) x

theorem indicator_product (x y : Bit) :
    indicator x*indicator y = if x=1 ∧ y=1 then 1 else 0 := by
  exact (by decide : ∀ x y : Bit,
    indicator x*indicator y = if x=1 ∧ y=1 then 1 else 0) x y

theorem replication {P B : Type*} [Fintype P] [Fintype B]
    (M : P → B → Bit) (k lam : ℤ)
    (hsize : ∀ b, ∑ p, indicator (M p b) = k)
    (hpair : ∀ p q, p ≠ q → ∑ b, indicator (M p b)*indicator (M q b) = lam)
    (p : P) :
    (∑ b, indicator (M p b))*(k-1) = (Fintype.card P-1 : ℤ)*lam := by
  classical
  have he : (∑ b, indicator (M p b))*k =
      ∑ q, ∑ b, indicator (M p b)*indicator (M q b) := by
    rw [Finset.sum_comm, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b _
    rw [← Finset.mul_sum, hsize]
  have hp : ∀ q, (∑ b, indicator (M p b)*indicator (M q b)) =
      lam + if q=p then (∑ b, indicator (M p b))-lam else 0 := by
    intro q
    by_cases hq : q=p
    · subst q; simp [indicator_sq]
    · rw [hpair p q (Ne.symm hq), if_neg hq, add_zero]
  simp only [hp, Finset.sum_add_distrib] at he
  simp at he
  nlinarith [he]

theorem design_row_separation {P B : Type*} [Fintype P] [Fintype B]
    (M : P → B → Bit) (k lam : ℤ)
    (hk : k < Fintype.card P) (hlam : 0 < lam)
    (hsize : ∀ b, ∑ p, indicator (M p b) = k)
    (hpair : ∀ p q, p ≠ q → ∑ b, indicator (M p b)*indicator (M q b) = lam) :
    ∀ p q ε, (∀ b, M p b = M q b+ε) → p=q := by
  intro p q ε he
  by_contra hpq
  have hh := hpair p q hpq
  rcases bit_cases ε with hε | hε
  · simp only [hε,add_zero] at he
    have hd : (∑ b, indicator (M p b))=lam := by
      simpa only [he,indicator_sq] using hh
    have hr := replication M k lam hsize hpair p
    rw [hd] at hr
    nlinarith
  · have hz : ∀ b, indicator (M p b)*indicator (M q b)=0 := by
      intro b
      rw [he,hε]
      exact (by decide : ∀ x : Bit, indicator (x+1)*indicator x=0) _
    simp only [hz,Finset.sum_const_zero] at hh
    omega

theorem design_block_count {P B : Type*} [Fintype P] [Fintype B]
    (M : P → B → Bit) (k lam : ℤ)
    (hsize : ∀ b, ∑ p, indicator (M p b) = k)
    (hpair : ∀ p q, p ≠ q → ∑ b, indicator (M p b)*indicator (M q b) = lam) :
    (Fintype.card B : ℤ)*k*(k-1) = (Fintype.card P : ℤ)*(Fintype.card P-1)*lam := by
  have hh := Finset.sum_congr (s₁ := (Finset.univ : Finset P)) rfl
    (fun p _ => replication M k lam hsize hpair p)
  rw [← Finset.sum_mul, Finset.sum_comm] at hh
  simp only [hsize, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hh
  nlinarith [hh]

theorem complete_characterization {P B : Type*} [Fintype P] [Fintype B]
    (M : P → B → Bit) (p₀ : P) (b₀ : B) (m k : ℕ) (lam A : ℤ)
    (hcard : Fintype.card B=2^m)
    (hsimple : Function.Injective (fun b p => M p b))
    (hsize : ∀ b, (Finset.univ.filter (fun p : P => M p b=1)).card=k)
    (hpair : ∀ p q, p ≠ q →
      ((Finset.univ.filter (fun b : B => M p b=1 ∧ M q b=1)).card : ℤ)=lam)
    (hk : 2*k < Fintype.card P) (hlam : 0<lam) (hA : 0<A)
    (hCA : ((Fintype.card P : ℤ)-2*k)*A = size (Fin m)) :
    Matrix.rank (BinaryDesignRank.bordered M)=m+2 ↔ Realization M m A := by
  classical
  have hsz : ∀ b, ∑ p, indicator (M p b)=(k : ℤ) := by
    intro b
    simpa [indicator] using congrArg (fun n : ℕ => (n : ℤ)) (hsize b)
  have hpa : ∀ p q, p ≠ q → ∑ b, indicator (M p b)*indicator (M q b)=lam := by
    intro p q hpq
    simpa [indicator_product] using hpair p q hpq
  have hk' : (k : ℤ) < Fintype.card P := by exact_mod_cast (show k < Fintype.card P by omega)
  have hC : (Fintype.card P : ℤ)-2*k ≠ 0 := by
    have : (2 : ℤ)*k < Fintype.card P := by exact_mod_cast hk
    omega
  have hsep := BinaryDesignRank.uniform_separation M k hsimple hsize (by omega)
  constructor
  · intro hr
    have hn : Module.finrank Bit (Submodule.span Bit
        (Set.range (BinaryDesignRank.normalizedColumn M p₀ b₀)))=m := by
      rw [BinaryDesignRank.bordered_rank M p₀ b₀] at hr
      exact Nat.add_right_cancel hr
    obtain ⟨β,φ,f,g,hrep⟩ := linearize M p₀ b₀ m hcard hsep hn
    apply reconstruct M m ((Fintype.card P : ℤ)-2*k) A hC (ne_of_gt hA) hCA hsimple
      (design_row_separation M k lam hk' hlam hsz hpa) _ β φ f g hrep
    intro b
    simp only [sign_indicator, Finset.sum_sub_distrib, ← Finset.mul_sum, hsz]
    simp
  · intro h
    exact (BinaryDesignRank.bordered_rank_iff M p₀ b₀ m hcard hsep).2
      (realization_tsdp M m A h)

/-- Polynomial form of the design parameters; the number of blocks is derived,
not supplied as a separate hypothesis. -/
theorem polynomial_parameters {P B : Type*} [Fintype P] [Fintype B]
    (M : P → B → Bit) (p₀ : P) (b₀ : B) (m q s : ℕ)
    (hq : 2 ≤ q) (hs : 0 < s) (hpow : 4*s*q^2=2^m)
    (hv : Fintype.card P=4*q^2)
    (hsimple : Function.Injective (fun b p => M p b))
    (hsize : ∀ b, (Finset.univ.filter (fun p : P => M p b=1)).card=q*(2*q-1))
    (hpair : ∀ p q', p ≠ q' →
      (Finset.univ.filter (fun b : B => M p b=1 ∧ M q' b=1)).card=s*q*(q-1)) :
    Matrix.rank (BinaryDesignRank.bordered M)=m+2 ↔ Realization M m (2*s*q) := by
  classical
  have hqZ : (2 : ℤ) ≤ q := by exact_mod_cast hq
  have hsZ : (0 : ℤ) < s := by exact_mod_cast hs
  have hkcast : ((q*(2*q-1) : ℕ) : ℤ) = (q : ℤ)*(2*q-1) := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega)]
    push_cast
    rfl
  have hlcast : ((s*q*(q-1) : ℕ) : ℤ) = (s : ℤ)*q*(q-1) := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega)]
    push_cast
    rfl
  have hvZ : (Fintype.card P : ℤ) = 4*(q : ℤ)^2 := by exact_mod_cast hv
  have hsz : ∀ b, ∑ p, indicator (M p b)=(q : ℤ)*(2*q-1) := by
    intro b
    rw [← hkcast]
    simpa [indicator] using congrArg (fun n : ℕ => (n : ℤ)) (hsize b)
  have hpa : ∀ p q', p ≠ q' →
      ∑ b, indicator (M p b)*indicator (M q' b)=(s : ℤ)*q*(q-1) := by
    intro p q' hpq
    rw [← hlcast]
    simpa [indicator_product] using congrArg (fun n : ℕ => (n : ℤ)) (hpair p q' hpq)
  have hc := design_block_count M _ _ hsz hpa
  rw [hvZ] at hc
  have hkpos : 0 < (q : ℤ)*(2*q-1) := by nlinarith
  have hk1 : 0 < (q : ℤ)*(2*q-1)-1 := by nlinarith
  have hbc : (Fintype.card B : ℤ)=4*(s : ℤ)*q^2 := by
    have he : ((Fintype.card B : ℤ)-4*(s : ℤ)*q^2)*
        ((q : ℤ)*(2*q-1))*((q : ℤ)*(2*q-1)-1)=0 := by
      calc
        _ = (Fintype.card B : ℤ)*(q*(2*q-1))*(q*(2*q-1)-1) -
            (4*(q : ℤ)^2)*(4*q^2-1)*(s*q*(q-1)) := by ring
        _ = 0 := sub_eq_zero.mpr hc
    have hz := (mul_eq_zero.mp he).resolve_right (ne_of_gt hk1)
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right (ne_of_gt hkpos))
  have hcard : Fintype.card B=2^m := by
    have hh : Fintype.card B=4*s*q^2 := by exact_mod_cast hbc
    exact hh.trans hpow
  apply complete_characterization M p₀ b₀ m (q*(2*q-1)) (s*q*(q-1)) (2*s*q)
    hcard hsimple hsize
  · intro p q' hpq
    rw [hpair p q' hpq,hlcast]
  · rw [hv]
    have hh : (2 : ℤ)*((q*(2*q-1) : ℕ) : ℤ) < 4*(q : ℤ)^2 := by rw [hkcast]; nlinarith
    exact_mod_cast hh
  · exact mul_pos (mul_pos hsZ (by omega)) (by omega)
  · positivity
  · rw [hvZ,hkcast]
    have hn : size (Fin m)=(2 : ℤ)^m := by simp [size, Cube, Bit, Fintype.card_fun]
    rw [hn]
    have hp : (4 : ℤ)*s*q^2=2^m := by exact_mod_cast hpow
    rw [← hp]
    ring

/-- The paper's full nondegenerate parameter range: n=2*t+4, m=n+r.
The factored block and pair parameters equal
2^(n-1)-2^(n/2-1) and 2^(m-2)-2^((m+r)/2-1), respectively.
The r=0 case is included as well as every r>=1 asked about in Open Problem 4. -/
theorem open_problem_4 {P B : Type*} [Fintype P] [Fintype B]
    (M : P → B → Bit) (p₀ : P) (b₀ : B) (t r : ℕ)
    (hv : Fintype.card P=2^(2*t+4))
    (hsimple : Function.Injective (fun b p => M p b))
    (hsize : ∀ b, (Finset.univ.filter (fun p : P => M p b=1)).card=
      2^(t+1)*(2^(t+2)-1))
    (hpair : ∀ p q, p ≠ q →
      (Finset.univ.filter (fun b : B => M p b=1 ∧ M q b=1)).card=
        2^r*2^(t+1)*(2^(t+1)-1)) :
    Matrix.rank (BinaryDesignRank.bordered M)=2*t+r+6 ↔
      Realization M (2*t+r+4) ((2 : ℤ)^(t+r+2)) := by
  have hp : 4*2^r*(2^(t+1))^2=2^(2*t+r+4) := by
    rw [← pow_mul]
    rw [show (4 : ℕ)=2^2 from rfl, ← pow_add, ← pow_add]
    congr 1
    omega
  have hv' : Fintype.card P=4*(2^(t+1))^2 := by
    rw [hv,← pow_mul,show (4 : ℕ)=2^2 from rfl,← pow_add]
    congr 1
    omega
  have hk : 2*2^(t+1)=2^(t+2) := by
    rw [show t+2=(t+1)+1 by omega,pow_succ]
    omega
  have hq : 2 ≤ 2^(t+1) := by
    have hh : 0 < (2 : ℕ)^t := pow_pos (by decide) _
    rw [pow_succ]
    omega
  have ha : (2 : ℤ)*(2^r : ℕ)*(2^(t+1) : ℕ)=2^(t+r+2) := by
    push_cast
    rw [mul_assoc,← pow_add,mul_comm,← pow_succ]
    congr 1
    omega
  have hh := polynomial_parameters M p₀ b₀ (2*t+r+4) (2^(t+1)) (2^r)
    hq (pow_pos (by decide) _) hp hv' hsimple (by simpa only [hk] using hsize) hpair
  convert hh using 1 <;> first | omega | rw [ha]

end PlateauedDesign

/-! An explicit simple 2-(64,28,24) design of binary rank 9 without TSDP.
This file checks a fixed symbolic construction, not a numerical search. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open scoped Matrix

namespace SumFreeCounterexample
abbrev F := ZMod 2
abbrev P := Fin 8 × Fin 8
abbrev B := Fin 8 × Fin 16

def bits {n : ℕ} (v : Fin (2^n)) (i : Fin n) : F :=
  if v.val.testBit i.val then 1 else 0
def dot {n : ℕ} (a b : Fin n → F) : F := ∑ i, a i * b i
def piTable : Fin 8 → Fin 32 := ![1,2,4,8,15,17,18,20]
def pi (y : Fin 8) : Fin 5 → F := bits (piTable y)
def xcoord (j : B) : Fin 5 → F :=
  let u : Fin 4 → F := bits (n := 4) j.2
  match j.1.val with
  | 0 => ![0,u 0,u 1,u 2,u 3]
  | 1 => ![u 0,0,u 1,u 2,u 3]
  | 2 => ![u 0,u 1,0,u 2,u 3]
  | 3 => ![u 0,u 1,u 2,0,u 3]
  | 4 => ![u 0+u 1+u 2,u 0,u 1,u 2,u 3]
  | 5 => ![u 3,u 0,u 1,u 2,u 3]
  | 6 => ![u 0,u 3,u 1,u 2,u 3]
  | _ => ![u 0,u 1,u 3,u 2,u 3]

def M (p : P) (j : B) : F :=
  dot (pi p.1) (xcoord j) + dot (bits (n := 3) p.2) (bits (n := 3) p.1 + bits (n := 3) j.1)
def sign (a : F) : ℤ := if a = 0 then 1 else -1

theorem sign_add (a b : F) : sign (a+b) = sign a * sign b := by
  revert a b
  decide +kernel

def frame : Matrix P (Fin 9) F := fun p =>
  ![pi p.1 0,pi p.1 1,pi p.1 2,pi p.1 3,pi p.1 4,
    bits (n := 3) p.2 0,bits (n := 3) p.2 1,bits (n := 3) p.2 2,dot (bits (n := 3) p.2) (bits (n := 3) p.1)]
def coeff : Matrix (Fin 9) B F := fun i j =>
  ![xcoord j 0,xcoord j 1,xcoord j 2,xcoord j 3,xcoord j 4,
    bits (n := 3) j.1 0,bits (n := 3) j.1 1,bits (n := 3) j.1 2,1] i

theorem factor : (M : Matrix P B F) =
    (frame : Matrix P (Fin 9) F) * (coeff : Matrix (Fin 9) B F) := by
  ext p j
  simp only [M, frame, coeff, dot, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Pi.add_apply, Fin.sum_univ_zero, add_zero]
  norm_num [Fin.succ]
  ring!

def rows : Fin 9 → P := ![(0,0),(1,0),(2,0),(3,0),(5,0),(0,1),(0,2),(0,4),(1,1)]
def cols : Fin 9 → B := ![(0,0),(0,1),(0,2),(0,4),(0,8),(1,0),(2,0),(4,0),(1,1)]
def minorInverse : Matrix (Fin 9) (Fin 9) F :=
  !![1,0,1,1,1,0,1,1,1;
     0,1,0,0,0,0,0,0,0;
     0,0,1,0,0,0,0,0,0;
     0,0,0,1,0,0,0,0,0;
     1,0,0,0,1,0,0,0,0;
     0,0,0,0,0,1,0,0,0;
     1,0,0,0,0,0,1,0,0;
     1,0,0,0,0,0,0,1,0;
     1,0,0,0,0,0,0,0,0]

theorem minor_certificate : Matrix.submatrix M rows cols * minorInverse = 1 := by
  decide +kernel

theorem exact_rank : Matrix.rank M = 9 := by
  apply Nat.le_antisymm
  · rw [factor]
    exact (Matrix.rank_mul_le_left _ _).trans (by simpa using Matrix.rank_le_card_width frame)
  · have h := Matrix.rank_mul_le_left (Matrix.submatrix M rows cols) minorInverse
    rw [minor_certificate, Matrix.rank_one, Fintype.card_fin] at h
    exact h.trans (Matrix.rank_submatrix_le M rows cols)

private theorem separation_certificate : ∀ j k : B,
    (∀ i : Fin 9, M (rows i) j = M (rows i) k) → j = k := by
  decide +kernel

theorem simple : Function.Injective (fun j p => M p j) := by
  intro j k h
  exact separation_certificate j k (fun i => congrFun h (rows i))

def testRows : Fin 10 → P :=
  ![(0,0),(1,0),(2,0),(3,0),(5,0),(0,1),(0,2),(0,4),(1,1),(4,0)]

theorem triple_certificate : ∀ j : B, ∀ e : F, ∃ i : Fin 10,
    M (testRows i) (0,1) + M (testRows i) (0,0) + M (testRows i) (1,0) ≠
      M (testRows i) j + e := by
  decide +kernel

def TSDP : Prop := ∀ a b c : B, ∃ d e, ∀ p : P,
  M p a + M p b + M p c = M p d + e

theorem not_tsdp : ¬ TSDP := by
  intro h
  obtain ⟨j,e,hj⟩ := h (0,1) (0,0) (1,0)
  obtain ⟨i,hi⟩ := triple_certificate j e
  exact hi (hj (testRows i))

theorem block_size : ∀ j : B, (Finset.univ.filter (fun p : P => M p j = 1)).card = 28 := by
  decide +kernel

theorem signed_row_sum : ∀ p : P, (∑ j : B, sign (M p j)) = 16 := by
  decide +kernel

theorem cap_character : ∀ y y' z : Fin 8, y ≠ y' →
    (∑ w : Fin 16, sign (dot (pi y + pi y') (xcoord (z,w)))) = 0 := by
  decide +kernel

theorem cube_character : ∀ b b' y : Fin 8, b ≠ b' →
    (∑ z : Fin 8, sign (dot (bits (n := 3) b) (bits (n := 3) y + bits (n := 3) z) +
      dot (bits (n := 3) b') (bits (n := 3) y + bits (n := 3) z))) = 0 := by
  decide +kernel

theorem sign_product (p q : P) (j : B) :
    sign (M p j) * sign (M q j) =
      sign (dot (pi p.1 + pi q.1) (xcoord j)) *
        sign (dot (bits (n := 3) p.2) (bits (n := 3) p.1 + bits (n := 3) j.1) +
          dot (bits q.2) (bits q.1 + bits (n := 3) j.1)) := by
  rw [← sign_add, ← sign_add]
  congr 1
  simp only [M, dot, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ring

theorem signed_row_product (p q : P) (hpq : p ≠ q) :
    (∑ j : B, sign (M p j) * sign (M q j)) = 0 := by
  obtain ⟨y,b⟩ := p
  obtain ⟨y',b'⟩ := q
  simp_rw [sign_product]
  rw [Fintype.sum_prod_type]
  simp only
  have hfactor (z : Fin 8) :
      (∑ w : Fin 16, sign (dot (pi y + pi y') (xcoord (z,w))) *
        sign (dot (bits (n := 3) b) (bits (n := 3) y + bits (n := 3) z) + dot (bits (n := 3) b') (bits (n := 3) y' + bits (n := 3) z))) =
      (∑ w : Fin 16, sign (dot (pi y + pi y') (xcoord (z,w)))) *
        sign (dot (bits (n := 3) b) (bits (n := 3) y + bits (n := 3) z) + dot (bits (n := 3) b') (bits (n := 3) y' + bits (n := 3) z)) :=
    (Finset.sum_mul _ _ _).symm
  simp_rw [hfactor]
  by_cases hy : y = y'
  · subst y'
    have hb : b ≠ b' := by
      intro h
      exact hpq (by rw [h])
    have hi (z : Fin 8) :
        (∑ w : Fin 16, sign (dot (pi y + pi y) (xcoord (z,w)))) = 16 := by
      simp [CharTwo.add_self_eq_zero, dot, sign]
    simp_rw [hi]
    rw [← Finset.mul_sum, cube_character b b' y hb, mul_zero]
  · simp_rw [cap_character y y' _ hy]
    simp

theorem pair_count (p q : P) (hpq : p ≠ q) :
    (Finset.univ.filter (fun j : B => M p j = 1 ∧ M q j = 1)).card = 24 := by
  have hid (j : B) :
      (4 : ℤ) * (if M p j = 1 ∧ M q j = 1 then 1 else 0) =
        1 - sign (M p j) - sign (M q j) + sign (M p j) * sign (M q j) := by
    generalize M p j = a
    generalize M q j = b
    revert a b
    decide +kernel
  have hs := Finset.sum_congr (s₁ := (Finset.univ : Finset B)) rfl (fun j _ => hid j)
  rw [← Finset.mul_sum] at hs
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hs
  rw [signed_row_sum, signed_row_sum, signed_row_product p q hpq] at hs
  have hc : (∑ j : B, if M p j = 1 ∧ M q j = 1 then (1 : ℤ) else 0) =
      ((Finset.univ.filter (fun j : B => M p j = 1 ∧ M q j = 1)).card : ℤ) := by
    simp
  rw [hc] at hs
  norm_num at hs
  omega

/-- Every hypothesis of the r=1 incidence-rank assertion holds, but TSDP fails. -/
theorem counterexample :
    Fintype.card P = 64 ∧ Fintype.card B = 128 ∧
    Function.Injective (fun j p => M p j) ∧
    (∀ j : B, (Finset.univ.filter (fun p : P => M p j = 1)).card = 28) ∧
    (∀ p q : P, p ≠ q →
      (Finset.univ.filter (fun j : B => M p j = 1 ∧ M q j = 1)).card = 24) ∧
    Matrix.rank M = 9 ∧ ¬ TSDP := by
  exact ⟨by decide, by decide, simple, block_size, pair_count, exact_rank, not_tsdp⟩

end SumFreeCounterexample
namespace SumFreeCounterexample
/-- Despite the paper's original incidence-rank threshold m+2=9, this design
has no realization by the required 1-plateaued addition construction. -/
theorem not_plateaued_addition_design : ¬ PlateauedDesign.Realization M 7 16 := by
  intro h
  exact not_tsdp (PlateauedDesign.realization_tsdp M 7 16 h)
end SumFreeCounterexample
