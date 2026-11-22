import EvenP6PrimaryFactors
import EvenP6PrimaryBlocks
import Primary48RawArchive

/-! Match archived factors by polynomial and multiplicity. All geometric inputs
to primary row reduction depend on the polynomial, even if coefficient storage
or factor ordering differs between the archive and the reference routine. -/
namespace EvenTI.P18Recover

open scoped Matrix Polynomial
open Matrix Polynomial UniqueFactorizationMonoid
open EvenTI.Contract EvenTI.PrimaryProducer
open Mathproof.P15FactorRef20261007 (toPoly)
open Mathproof.Problem17Primary47ExternalArchive (Archived)
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Lax13Proofs.Imp (Env)

set_option autoImplicit false

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {n : ℕ}

noncomputable def archiveRows (f : K[X]) (L : List K[X]) : List (K[X] × ℕ) :=
  L.map fun p => (p, (normalizedFactors f).count p)

theorem archiveRows_perm_anchorFactors (D : FieldEncoding K) (A : Matrix (Fin n) (Fin n) K)
    {L : List K[X]} (h : (L : Multiset K[X]) = (normalizedFactors A.charpoly).dedup) :
    (archiveRows A.charpoly L).Perm
      ((anchorFactors D A).map (fun row => (toPoly row.1, row.2))) := by
  apply Multiset.coe_eq_coe.mp
  rw [anchorFactors_spec]
  change (L : Multiset K[X]).map _ = _
  rw [h]

/-- A row of the physical archive supplies the polynomial and multiplicity of
a reference row, without a requirement to match their positions. -/
theorem archivedRow_reference (F : FieldPresentation K) (D : FieldEncoding K)
    (A : Matrix (Fin n) (Fin n) K) {words mult : String} {W : ℕ} {L : List K[X]}
    {σ : Env} (h : Archived F words mult W A.charpoly L σ) (i : Fin L.length) :
    ∃ row ∈ anchorFactors D A,
      toPoly row.1 = L.get i ∧ row.2 = (σ.arrs mult).getD i.val 0 := by
  have hh : (L.get i, (normalizedFactors A.charpoly).count (L.get i)) ∈
      archiveRows A.charpoly L := List.mem_map.mpr ⟨L.get i,L.get_mem i,rfl⟩
  have hm := (archiveRows_perm_anchorFactors D A h.list).mem_iff.mp hh
  obtain ⟨row,hr,he⟩ := List.mem_map.mp hm
  exact ⟨row,hr,congrArg Prod.fst he,(congrArg Prod.snd he).trans (h.multiplicity i.val i.isLt).symm⟩

theorem primaryRows_of_polynomial_eq (A : Matrix (Fin n) (Fin n) K)
    {p q : List K} (e : ℕ) (h : toPoly p = toPoly q) :
    primaryRows A p e = primaryRows A q e := by
  unfold primaryRows
  rw [matrixHorner_spec, matrixHorner_spec, h]

theorem primaryLabels_of_polynomial_eq (A : Matrix (Fin n) (Fin n) K)
    {p q : List K} (e : ℕ) (h : toPoly p = toPoly q) :
    primaryLabels A p e = primaryLabels A q e := by
  unfold primaryLabels
  rw [primaryRows_of_polynomial_eq A e h]

theorem primaryBasis_of_polynomial_eq (A : Matrix (Fin n) (Fin n) K)
    {p q : List K} (e : ℕ) (h : toPoly p = toPoly q) :
    primaryBasis A p e = primaryBasis A q e := by
  unfold primaryBasis
  rw [matrixHorner_spec, matrixHorner_spec, h]

#print axioms archiveRows_perm_anchorFactors
#print axioms archivedRow_reference
#print axioms primaryRows_of_polynomial_eq
#print axioms primaryLabels_of_polynomial_eq
#print axioms primaryBasis_of_polynomial_eq
end EvenTI.P18Recover



/-! A populated archive has one physical row ordering. Recover it from the
coefficient words instead of imposing a reference factorizer's ordering. -/
namespace EvenTI.P18Recover

open scoped Polynomial
open Polynomial UniqueFactorizationMonoid
open Lax13Proofs.Imp
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem17Primary47ExternalArchive (Archived)
open Mathproof.Problem17Primary48RawArchive (Output Retained)

set_option autoImplicit false

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- A fixed array of literal coefficient words has at most one archived
factor list at the specified size. The argument compares only entries of
the live archive and uses the degree capacity to recover all higher zeros. -/
theorem archived_order_unique (F : FieldPresentation K) {words mult : String} {W : ℕ}
    {f : K[X]} {L M : List K[X]} {s : Env}
    (ha : Archived F words mult W f L s)
    (hb : Archived F words mult W f M s) (hLen : L.length=M.length)
    (hf : f ≠ 0) (hW : f.natDegree < W) : L=M := by
  obtain ⟨a,da,ca⟩ := ha.data
  obtain ⟨b,db,cb⟩ := hb.data
  apply List.ext_getElem hLen
  intro i hi hj
  apply Polynomial.ext
  intro t
  have degL : L[i].natDegree < W := by
    have h : L[i] ∈ (L : Multiset K[X]) := List.getElem_mem _
    rw [ha.list,Multiset.mem_dedup] at h
    exact (natDegree_le_of_dvd (dvd_of_mem_normalizedFactors h) hf).trans_lt hW
  have degM : M[i].natDegree < W := by
    have h : M[i] ∈ (M : Multiset K[X]) := List.getElem_mem _
    rw [hb.list,Multiset.mem_dedup] at h
    exact (natDegree_le_of_dvd (dvd_of_mem_normalizedFactors h) hf).trans_lt hW
  by_cases ht : t<W
  · let j := W-1-t
    have hj' : j<W := by dsimp [j]; omega
    have hIndex (l : ℕ) (hl : i<l) : i*W+j < l*W := by
      calc
        _ < i*W+W := Nat.add_lt_add_left hj' _
        _ = (i+1)*W := by rw [Nat.add_mul,one_mul]
        _ ≤ _ := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hl)
    have heVal : a (i*W+j) = b (i*W+j) := by
      apply F.coordinate.injective
      funext k
      apply Fin.ext
      exact (da (i*W+j) (hIndex _ hi) k).symm.trans (db (i*W+j) (hIndex _ hj) k)
    have ht' : W-1-j=t := by dsimp [j]; omega
    rw [ca i hi j hj',cb i hj j hj',ht'] at heVal
    exact heVal
  · rw [coeff_eq_zero_of_natDegree_lt (by omega : L[i].natDegree < t),
      coeff_eq_zero_of_natDegree_lt (by omega : M[i].natDegree < t)]

theorem retained_order_unique (F : FieldPresentation K) {O : Output} {N : ℕ} {s : Env}
    {f : K[X]} {L M : List K[X]}
    (ha : s.vars O.size=L.length ∧ Archived F O.words O.mult (N+N) f L s)
    (hb : s.vars O.size=M.length ∧ Archived F O.words O.mult (N+N) f M s)
    (hf : f ≠ 0) (hW : f.natDegree < N+N) :
    L=M :=
  archived_order_unique F ha.2 hb.2 (ha.1.symm.trans hb.1) hf hW

#print axioms archived_order_unique
#print axioms retained_order_unique
end EvenTI.P18Recover

