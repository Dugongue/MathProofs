import EvenP18RecoverOrder
import Mathlib.Data.List.NodupEquivFin

namespace EvenTI.P22Site.Keys
open scoped Polynomial
open Polynomial UniqueFactorizationMonoid
open Lax13Proofs.Imp
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem17Primary47ExternalArchive (Archived)

set_option autoImplicit false
set_option maxHeartbeats 500000

section Lookup
variable {A : Type} [DecidableEq A] {m n : ℕ}

private theorem lookup_exists (x : Fin m → A) (y : Fin n → A)
    (cover : ∀ i, ∃ j, y j = x i) (i : Fin m) :
    ((List.finRange n).find? (fun j => decide (y j = x i))).isSome := by
  obtain ⟨j,hj⟩ := cover i
  apply List.find?_isSome.mpr
  exact ⟨j,List.mem_finRange j,decide_eq_true hj⟩

/-- A bounded literal-key scan. The proof of coverage is erased; the
computed value is the first matching index in the actual finite key array. -/
def lookup (x : Fin m → A) (y : Fin n → A)
    (cover : ∀ i, ∃ j, y j = x i) (i : Fin m) : Fin n :=
  ((List.finRange n).find? (fun j => decide (y j = x i))).get (lookup_exists x y cover i)

theorem lookup_spec (x : Fin m → A) (y : Fin n → A)
    (cover : ∀ i, ∃ j, y j = x i) (i : Fin m) : y (lookup x y cover i) = x i := by
  have hi := Option.some_get (lookup_exists x y cover i)
  have hp := List.find?_some (p:=fun j : Fin n => decide (y j = x i)) hi.symm
  exact of_decide_eq_true hp

/-- Unique literal keys give a constructive permutation, using bounded
forward and reverse searches rather than a transporter oracle. -/
def keyEquiv (x : Fin m → A) (y : Fin n → A)
    (hx : Function.Injective x) (hy : Function.Injective y)
    (xy : ∀ i, ∃ j, y j = x i) (yx : ∀ j, ∃ i, x i = y j) : Fin m ≃ Fin n where
  toFun := lookup x y xy
  invFun := lookup y x yx
  left_inv i := hx ((lookup_spec y x yx _).trans (lookup_spec x y xy i))
  right_inv j := hy ((lookup_spec x y xy _).trans (lookup_spec y x yx j))

theorem keyEquiv_spec (x : Fin m → A) (y : Fin n → A)
    (hx : Function.Injective x) (hy : Function.Injective y)
    (xy : ∀ i, ∃ j, y j = x i) (yx : ∀ j, ∃ i, x i = y j) (i : Fin m) :
    y (keyEquiv x y hx hy xy yx i) = x i := lookup_spec x y xy i
end Lookup

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

def rowKey (F : FieldPresentation K) (s : Env) (words : String) (cap i : ℕ) :
    Fin cap × Fin F.e → ℕ :=
  fun jk => (s.arrs words).getD (F.e*(i*cap+jk.1.val)+jk.2.val) 0

private theorem row_address_lt {cap : ℕ} {L : List K[X]} (i : Fin L.length) (j : Fin cap) :
    i.val*cap+j.val < L.length*cap := by
  calc
    _ < i.val*cap+cap := Nat.add_lt_add_left j.isLt _
    _ = (i.val+1)*cap := by rw [Nat.add_mul,one_mul]
    _ ≤ L.length*cap := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt i.isLt)

/-- Read a coefficient key directly from actual archived coordinate bytes. -/
theorem rowKey_decode (F : FieldPresentation K) {s : Env} {words mult : String}
    {cap : ℕ} {f : K[X]} {L : List K[X]}
    (h : Archived F words mult cap f L s) (i : Fin L.length)
    (j : Fin cap) (digit : Fin F.e) :
    rowKey F s words cap i.val (j,digit) =
      (F.coordinate ((L.get i).coeff (cap-1-j.val)) digit).val := by
  obtain ⟨v,hv,hc⟩ := h.data
  have ha := hv (i.val*cap+j.val) (row_address_lt i j) digit
  rw [hc i.val i.isLt j.val j.isLt] at ha
  simpa only [rowKey,Nat.zero_add,List.get_eq_getElem] using ha

private theorem factor_degree_lt (F : FieldPresentation K) {s : Env} {words mult : String}
    {cap : ℕ} {f : K[X]} {L : List K[X]}
    (h : Archived F words mult cap f L s) (hf : f ≠ 0) (hc : f.natDegree < cap)
    (i : Fin L.length) : (L.get i).natDegree < cap := by
  have hi : L.get i ∈ (L : Multiset K[X]) := List.get_mem L i
  rw [h.list,Multiset.mem_dedup] at hi
  exact (natDegree_le_of_dvd (dvd_of_mem_normalizedFactors hi) hf).trans_lt hc

/-- Byte equality is exactly polynomial equality, including every leading
zero slot. No same-order assumption between the two physical archives is used. -/
theorem rowKey_eq_iff (F : FieldPresentation K) {s : Env} {a am b bm : String}
    {cap : ℕ} {f : K[X]} {L M : List K[X]}
    (ha : Archived F a am cap f L s) (hb : Archived F b bm cap f M s)
    (hf : f ≠ 0) (hc : f.natDegree < cap) (i : Fin L.length) (j : Fin M.length) :
    rowKey F s a cap i.val = rowKey F s b cap j.val ↔ L.get i = M.get j := by
  constructor
  · intro h
    apply Polynomial.ext
    intro t
    by_cases ht : t < cap
    · let k : Fin cap := ⟨cap-1-t,by omega⟩
      have hk : cap-1-k.val = t := by dsimp [k]; omega
      apply F.coordinate.injective
      funext digit
      apply Fin.ext
      have he := congrFun h (k,digit)
      rw [rowKey_decode F ha i k digit,rowKey_decode F hb j k digit,hk] at he
      exact he
    · rw [coeff_eq_zero_of_natDegree_lt (by have hd := factor_degree_lt F ha hf hc i; omega),
        coeff_eq_zero_of_natDegree_lt (by have hd := factor_degree_lt F hb hf hc j; omega)]
  · intro h
    funext jk
    rcases jk with ⟨k,digit⟩
    rw [rowKey_decode F ha i k digit,rowKey_decode F hb j k digit,h]

theorem archive_nodup (F : FieldPresentation K) {s : Env} {a am : String}
    {cap : ℕ} {f : K[X]} {L : List K[X]} (ha : Archived F a am cap f L s) : L.Nodup := by
  apply Multiset.coe_nodup.mp
  rw [ha.list]
  exact Multiset.nodup_dedup _

theorem rowKey_injective (F : FieldPresentation K) {s : Env} {a am : String}
    {cap : ℕ} {f : K[X]} {L : List K[X]}
    (ha : Archived F a am cap f L s) (hf : f ≠ 0) (hc : f.natDegree < cap) :
    Function.Injective (fun i : Fin L.length => rowKey F s a cap i.val) := by
  intro i j he
  exact (archive_nodup F ha).get_inj_iff.mp ((rowKey_eq_iff F ha ha hf hc i j).mp he)

/-- The actual two archived tables determine a unique literal-key matching. -/
def archiveEquiv (F : FieldPresentation K) {s : Env} {a am b bm : String}
    {cap : ℕ} {f : K[X]} {L M : List K[X]}
    (ha : Archived F a am cap f L s) (hb : Archived F b bm cap f M s)
    (hf : f ≠ 0) (hc : f.natDegree < cap) : Fin L.length ≃ Fin M.length := by
  have hp : L.Perm M := Multiset.coe_eq_coe.mp (ha.list.trans hb.list.symm)
  refine keyEquiv (fun i : Fin L.length => rowKey F s a cap i.val)
    (fun j : Fin M.length => rowKey F s b cap j.val)
    (rowKey_injective F ha hf hc) (rowKey_injective F hb hf hc) ?_ ?_
  · intro i
    obtain ⟨j,hj⟩ := List.mem_iff_get.mp (hp.mem_iff.mp (List.get_mem L i))
    exact ⟨j,(rowKey_eq_iff F hb ha hf hc j i).mpr hj⟩
  · intro j
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp (hp.mem_iff.mpr (List.get_mem M j))
    exact ⟨i,(rowKey_eq_iff F ha hb hf hc i j).mpr hi⟩

#print axioms rowKey_eq_iff
#print axioms rowKey_injective
#print axioms archiveEquiv
end EvenTI.P22Site.Keys
