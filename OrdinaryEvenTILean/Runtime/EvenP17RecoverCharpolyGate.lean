import EvenP6AlignPair
import Comparator46PolySetup

set_option autoImplicit false
set_option maxHeartbeats 1450000

namespace EvenTI.P17Recover

open scoped Polynomial
open Matrix Polynomial UniqueFactorizationMonoid
open EvenTI.Contract EvenTI.PrimaryProducer EvenTI.PrimaryAlignment
open Mathproof.P15FactorRef20261007

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

private theorem count_of_equal_tables (L R : Multiset K[X])
    (h : L.dedup.map (fun p => (p,L.count p))=R.dedup.map (fun p => (p,R.count p)))
    (p : K[X]) (hp : p ∈ L) : L.count p=R.count p := by
  have hd : p ∈ L.dedup := by simpa using hp
  have hm : (p,L.count p) ∈ L.dedup.map (fun q => (q,L.count q)) := Multiset.mem_map.mpr ⟨p,hd,rfl⟩
  rw [h] at hm
  obtain ⟨q,_,he⟩ := Multiset.mem_map.mp hm
  have hq := congrArg Prod.fst he
  change q=p at hq
  subst q
  exact (congrArg Prod.snd he).symm

/-- Complete ordered factor tables agree exactly when their characteristic
polynomials agree. Matching may compare coefficient banks before factoring
and then form only the source factor table. -/
theorem anchorFactors_eq_iff_charpoly (D : FieldEncoding K) {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) K) :
    anchorFactors D A=anchorFactors D B ↔ A.charpoly=B.charpoly := by
  constructor
  · intro he
    let L := normalizedFactors A.charpoly
    let R := normalizedFactors B.charpoly
    have h : L.dedup.map (fun p => (p,L.count p))=R.dedup.map (fun p => (p,R.count p)) := by
      have ha := anchorFactors_spec D A
      rw [he] at ha
      exact ha.symm.trans (anchorFactors_spec D B)
    have hf : L=R := by
      apply Multiset.ext.mpr
      intro p
      by_cases hp : p ∈ L
      · exact count_of_equal_tables L R h p hp
      · by_cases hq : p ∈ R
        · exact (count_of_equal_tables R L h.symm p hq).symm
        · exact (Multiset.count_eq_zero.mpr hp).trans (Multiset.count_eq_zero.mpr hq).symm
    have hprod (P : K[X]) (hm : P.Monic) : (normalizedFactors P).prod=P := by
      rw [prod_normalizedFactors_eq hm.ne_zero, (Polynomial.normalize_eq_self_iff_monic hm.ne_zero).mpr hm]
    exact (hprod _ A.charpoly_monic).symm.trans ((congrArg Multiset.prod hf).trans (hprod _ B.charpoly_monic))
  · intro h
    unfold anchorFactors
    apply congrArg (factorCoefficients D)
    apply List.ext_getElem (by simp)
    intro j ha hb
    have hA := congrArg (fun p : K[X] => p.coeff j) (anchorCoefficients_spec A)
    have hB := congrArg (fun p : K[X] => p.coeff j) (anchorCoefficients_spec B)
    simp only [coeff_toPoly,List.getD_eq_getElem _ _ ha] at hA
    simp only [coeff_toPoly,List.getD_eq_getElem _ _ hb] at hB
    rw [hA,hB,h]

noncomputable def prepareAnchorPairByCharpoly (D : FieldEncoding K) (budget : ℕ)
    (A B : NumberedAnchor K) : Option (PreparedMode K) :=
  if hw : B.width=A.width then
    let B' := B.matrix.submatrix (finCongr hw).symm (finCongr hw).symm
    if A.matrix.charpoly=B'.charpoly then
      ((anchorFactors D A.matrix).mapM (prepareModeBlock D budget A.matrix B')).map (PreparedMode.mk A.width)
    else none
  else none

theorem prepareAnchorPairByCharpoly_eq (D : FieldEncoding K) (budget : ℕ)
    (A B : NumberedAnchor K) : prepareAnchorPairByCharpoly D budget A B=prepareAnchorPair D budget A B := by
  by_cases h : B.width=A.width
  · let B' := B.matrix.submatrix (finCongr h).symm (finCongr h).symm
    have he := anchorFactors_eq_iff_charpoly D A.matrix B'
    let R := ((anchorFactors D A.matrix).mapM (prepareModeBlock D budget A.matrix B')).map
      (PreparedMode.mk A.width)
    simp only [prepareAnchorPairByCharpoly,prepareAnchorPair,dif_pos h]
    change (if A.matrix.charpoly=B'.charpoly then R else none) =
      (if anchorFactors D A.matrix=anchorFactors D B' then R else none)
    by_cases hP : A.matrix.charpoly=B'.charpoly
    · rw [if_pos hP,if_pos (he.mpr hP)]
    · have hC : anchorFactors D A.matrix≠anchorFactors D B' := fun hc => hP (he.mp hc)
      rw [if_neg hP,if_neg hC]
  · simp [prepareAnchorPairByCharpoly,prepareAnchorPair,h]

#print axioms anchorFactors_eq_iff_charpoly
#print axioms prepareAnchorPairByCharpoly_eq
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots)
open Mathproof.P15RecogIMPDot20261007 (qN)
open Mathproof.Problem17CharpolyExec (CoeffSlots)
open Mathproof.Problem17Comparator46PolyMatch (fromBanks fromBanks_run firstBank secondBank flag)

/-- Compare the two live characteristic-polynomial banks to execute the
original factor-table equality test without constructing a target factor table. -/
theorem anchorFactorCheck_run (D : FieldEncoding K) (F : FieldPresentation K)
    {B S n a b w : ℕ} {s : Env} (A C : Matrix (Fin n) (Fin n) K)
    (hS : Slots F canonical qN.WS S B s) (ha : a+w ≤ S) (hb : b+w ≤ S)
    (hA : CoeffSlots F s w a A.charpoly) (hC : CoeffSlots F s w b C.charpoly)
    (hw : n < w) (hB : 1 < B)
    (hfr : s.vars firstBank=a) (hsr : s.vars secondBank=b)
    (hwr : s.vars Mathproof.Problem17Comparator46PolyMatch.width=w) :
    ∃ t, Run B fromBanks s t (20*(w*F.e)+30) ∧ Slots F canonical qN.WS S B t ∧
      t.vars flag ≤ 1 ∧ (t.vars flag=1 ↔ anchorFactors D A=anchorFactors D C) ∧
      t.arrs=s.arrs ∧ t.inp=s.inp ∧ t.out=s.out := by
  have h₁ : A.charpoly.natDegree < w := by simpa [Matrix.charpoly_natDegree_eq_dim] using hw
  have h₂ : C.charpoly.natDegree < w := by simpa [Matrix.charpoly_natDegree_eq_dim] using hw
  obtain ⟨t,ht,hs,hbits,hEq,hA',hI',hO'⟩ := fromBanks_run F hS ha hb hA hC h₁ h₂ hB hfr hsr hwr
  exact ⟨t,ht,hs,hbits,hEq.trans (anchorFactors_eq_iff_charpoly D A C).symm,hA',hI',hO'⟩

#print axioms anchorFactorCheck_run
end EvenTI.P17Recover
