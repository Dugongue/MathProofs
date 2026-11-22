import EvenP22PadPack
import EvenP20SweepPrepared
import EvenP6PrimaryFrame
import EvenP17TransposeSlots
import EvenP15ReciprocalCall
import EvenP21PadSite
import EvenP21SiteMode
import Mathproof.Meta.Problem18FieldPresentation20260930

/-! Assemble the saved primary basis, transpose it into the inverse input, and
retain the original transpose bank for the dual order-four occurrence. -/

set_option autoImplicit false
set_option maxHeartbeats 1150000

namespace EvenTI.P22Pad

open scoped BigOperators Polynomial Matrix
open Matrix Polynomial Module UniqueFactorizationMonoid
open EvenTI.Contract EvenTI.PrimaryAlignment EvenTI.PrimaryProducer EvenTI.P20Sweep
open Mathproof.P15FactorRef20261007 Mathproof.P15FactorIMP20261007
open Mathproof.Problem17Comparator46Primary
open Lax13Proofs.Imp
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (val)
open Mathproof.P15RecogIMPDot20261007 (qN)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- Complete disjoint primary factors in archive order give exactly the
primary direct sum, regardless of the order used in another factorizer. -/
theorem archivePrimary_internal {n : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (L : List (Polynomial K))
    (hL : (L : Multiset (Polynomial K))=(normalizedFactors A.charpoly).dedup) :
    DirectSum.IsInternal (fun i : Fin L.length =>
      ((aeval A (factorAt A L i.val)).mulVecLin).ker) := by
  classical
  let M := normalizedFactors A.charpoly
  let g := fun f : Polynomial K => f ^ M.count f
  have hp (i : Fin L.length) : factorAt A L i.val=g (L.get i) := by
    unfold factorAt
    rw [List.getElem?_eq_getElem i.isLt] <;> rfl
  have mem (i : Fin L.length) : L.get i ∈ M := by
    rw [← Multiset.mem_dedup,show M.dedup=(L : Multiset (Polynomial K)) from hL.symm]
    exact Multiset.mem_coe.mpr (List.get_mem _ _)
  have nd : L.Nodup := by
    change (L : Multiset (Polynomial K)).Nodup
    rw [hL]
    exact Multiset.nodup_dedup _
  have hPair : Pairwise (fun i j : Fin L.length => IsCoprime
      (factorAt A L i.val) (factorAt A L j.val)) := by
    intro i j hij
    rw [hp,hp]
    exact (coprime_monic_irreducibles (nf_monic (mem i)) (nf_monic (mem j))
      (irreducible_of_normalized_factor _ (mem i)) (irreducible_of_normalized_factor _ (mem j))
      (fun h => hij (nd.injective_get h))).pow
  have hMonic : M.prod.Monic := by
    simpa only [id_eq,Multiset.map_id'] using
      (monic_multiset_prod_of_monic M id (fun f hf => nf_monic hf))
  have hEqual : M.prod=A.charpoly :=
    eq_of_monic_of_associated hMonic A.charpoly_monic (prod_normalizedFactors A.charpoly_monic.ne_zero)
  have hProd : (∏ i : Fin L.length, factorAt A L i.val)=A.charpoly := by
    calc
      _ = (L.map g).prod := by
        simp_rw [hp]
        rw [← List.prod_ofFn]
        change (List.ofFn (g ∘ L.get)).prod = _
        rw [← List.map_ofFn,List.ofFn_get]
      _ = (M.dedup.map g).prod := by
        rw [← Multiset.prod_coe,← Multiset.map_coe,hL]
      _ = M.prod := by
        rw [← Multiset.toFinset_val]
        exact (Finset.prod_multiset_count M).symm
      _ = _ := hEqual
  rw [show (fun i : Fin L.length => ((aeval A (factorAt A L i.val)).mulVecLin).ker) =
    (fun i : Fin L.length => part A.mulVecLin (factorAt A L i.val)) from
    funext fun _ => congrArg LinearMap.ker (matrixEvalToLin A _)]
  apply primary_internal _ _ hPair
  rw [hProd,← matrixEvalToLin,Matrix.aeval_self_charpoly,Matrix.mulVecLin_zero]

/-- The archived columns yield a square invertible primary frame in the
same order as their saved widths. Each block range is the actual primary
subspace of its archived factor. -/
theorem archiveBasis_exists (F : FieldPresentation K) {n off base lane : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (L : List (Polynomial K)) (s : Env)
    (hL : (L : Multiset (Polynomial K))=(normalizedFactors A.charpoly).dedup)
    (hArchive : ∀ i : Fin L.length,
      SavedChart F A (factorAt A L i.val) (off+i.val) (rowBasis base lane (off+i.val))
        (rowChart base lane (off+i.val)) s) :
    ∃ (width : Fin L.length → ℕ)
      (C : ∀ i : Fin L.length, Matrix (Fin n) (Fin (width i)) K)
      (hSum : (∑ i, width i)=n),
      IsUnit (concatenateFrame C hSum) ∧
      (∀ i, (s.arrs savedWidths)[off+i.val]?=some (width i)) ∧
      (∀ i r c, val F canonical qN.WS s (rowBasis base lane (off+i.val)+(c.val*n+r.val))=C i r c) ∧
      ∀ i, (C i).mulVecLin.range=((aeval A (factorAt A L i.val)).mulVecLin).ker := by
  classical
  unfold SavedChart at hArchive
  choose width xs hw hs hLin hSpan hWords hChart using hArchive
  let C (i : Fin L.length) : Matrix (Fin n) (Fin (width i)) K := fun r c => xs i c r
  have hRange (i : Fin L.length) : (C i).mulVecLin.range =
      ((aeval A (factorAt A L i.val)).mulVecLin).ker := by
    rw [Matrix.range_mulVecLin]
    exact hSpan i
  have hI : DirectSum.IsInternal (fun i => (C i).mulVecLin.range) := by
    simpa only [hRange] using archivePrimary_internal A L hL
  have hC (i : Fin L.length) : Function.Injective (C i).mulVec :=
    Matrix.mulVec_injective_iff.mpr (hLin i)
  let hSum := complete_columns_width C hI hC
  exact ⟨width,C,hSum,concatenateFrame_isUnit C hSum hI hC,hs,fun i r c => hWords i c r,hRange⟩

#print axioms archivePrimary_internal
#print axioms archiveBasis_exists
end EvenTI.P22Pad

set_option autoImplicit false
set_option maxRecDepth 24000
set_option maxHeartbeats 1000000

namespace EvenTI.P22Pad

open EvenTI.P20Sweep EvenTI.P17Execution EvenTI.P15Execution
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val val_setVar NoVar)
open Mathproof.P15RecogIMPDot20261007 (qN dL dT dU dZ)
open Mathproof.P15RecogIMPGrid20261007 (gRows gCols gOut Written)
open Mathproof.P15RecogIMPProgram20261007 (rOs)
open Mathproof.P15DecideIMPEGens20261007 (ev_var)
open Mathproof.Problem18P34AssemblyMatrixGatherSetup20261003
  (commands commands_run install installed_slots installed_scalar)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

private def transposeBindings : List (String × Expr) :=
  [(dL,.lit 1),(gRows,.var savedAmbientSize),(gCols,.var savedAmbientSize),
   (gOut,.var inverseInputWord),(transposeSourceSlot,.var frameTemp),
   (transposeOneSlot,.var rOs)]

noncomputable def transposePackedFrame (F : FieldPresentation K) : Com :=
  .seq (commands transposeBindings) (transposeSlots F)

private theorem transposeIndependent : ∀ p ∈ transposeBindings, ∀ r ∈ transposeBindings, NoVar p.1 r.2 := by
  intro p hp r hr
  simp only [transposeBindings,List.mem_cons,List.not_mem_nil,or_false] at hp hr
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl <;> rcases hr with rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp [NoVar,dL,gRows,gCols,gOut,transposeSourceSlot,transposeOneSlot,savedAmbientSize,
      inverseInputWord,frameTemp,rOs]

/-- Physically transpose the archived column vectors into the square,
row-major input window consumed by the inverse routine. -/
theorem transposePackedFrame_run (F : FieldPresentation K) {B S n src dst Z : ℕ} {s : Env}
    (hs : Slots F canonical qN.WS S B s)
    (hN : s.vars savedAmbientSize=n) (hSrc : s.vars frameTemp=src)
    (hDst : s.vars inverseInputWord=dst)
    (hZ : s.vars dZ=Z) (hOne : s.vars rOs=Z+1)
    (hT : s.vars dT=Z+2) (hU : s.vars dU=Z+3)
    (hz : val F canonical qN.WS s Z=0) (ho : val F canonical qN.WS s (Z+1)=1)
    (hApart : src+n*n≤dst) (hFit : dst+n*n≤Z) (hSpace : Z+4≤S)
    (hn : n+1<B) :
    ∃ t, Run B (transposePackedFrame F) s t (13+transposeSlotsCost F n n) ∧
      Slots F canonical qN.WS S B t ∧
      (∀ i j : Fin n, val F canonical qN.WS t (dst+(i.val*n+j.val))=
        val F canonical qN.WS s (src+(j.val*n+i.val))) ∧
      (∀ k<S, (k<dst ∨ dst+n*n≤k) → k≠Z+2 → k≠Z+3 →
        val F canonical qN.WS t k=val F canonical qN.WS s k) ∧
      Frame (transposePackedFrame F) s t := by
  have hsb := hs.slots_word
  let vals := [(dL,1),(gRows,n),(gCols,n),(gOut,dst),(transposeSourceSlot,src),(transposeOneSlot,Z+1)]
  let u := install vals s
  have e1 : (Expr.lit 1).evalB B s=some 1 := evalB_lit (by omega)
  have en := ev_var hN (show n<B by omega)
  have ed := ev_var hDst (show dst<B by omega)
  have es := ev_var hSrc (show src<B by omega)
  have eo := ev_var hOne (show Z+1<B by omega)
  have r₀ : Run B (commands transposeBindings) s u 13 :=
    commands_run transposeBindings [1,n,n,dst,src,Z+1] s rfl
      (List.Forall₂.cons e1 (List.Forall₂.cons en (List.Forall₂.cons en (List.Forall₂.cons ed (List.Forall₂.cons es (List.Forall₂.cons eo List.Forall₂.nil)))))) transposeIndependent
  have hu : Slots F canonical qN.WS S B u := by
    apply installed_slots F vals s hs
    intro p hp
    simp only [vals,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl <;> dsimp only <;> decide
  have uval (k : ℕ) : val F canonical qN.WS u k=val F canonical qN.WS s k := by
    simp only [u,vals,install]
    rw [val_setVar F canonical (by decide),val_setVar F canonical (by decide),
      val_setVar F canonical (by decide),val_setVar F canonical (by decide),
      val_setVar F canonical (by decide),val_setVar F canonical (by decide)]
  have uKeep (r : String) (hr : r=dZ ∨ r=dT ∨ r=dU) : u.vars r=s.vars r := by
    apply installed_scalar vals s r
    intro p hp
    simp only [vals,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hr with rfl|rfl|rfl <;> rcases hp with rfl|rfl|rfl|rfl|rfl|rfl <;> dsimp only <;> decide
  have uZ : u.vars dZ=Z := (uKeep dZ (Or.inl rfl)).trans hZ
  have uT : u.vars dT=Z+2 := (uKeep dT (Or.inr (Or.inl rfl))).trans hT
  have uU : u.vars dU=Z+3 := (uKeep dU (Or.inr (Or.inr rfl))).trans hU
  have uL : u.vars dL=1 := rfl
  have uR : u.vars gRows=n := rfl
  have uC : u.vars gCols=n := rfl
  have uOut : u.vars gOut=dst := rfl
  have uSrc : u.vars transposeSourceSlot=src := rfl
  have uOne : u.vars transposeOneSlot=Z+1 := rfl
  have noZ : ¬ Written dst n n (Z+2) (Z+3) Z := by unfold Written; omega
  have noO : ¬ Written dst n n (Z+2) (Z+3) (Z+1) := by unfold Written; omega
  obtain ⟨t,rt,ht,hAt,hKeep,_,_,_⟩ := transposeSlots_run F (z:=Z) (tt:=Z+2) (uu:=Z+3) (one:=Z+1) hu hApart (by omega)
    hn hn (by omega) (by omega) (by omega) (by omega)
    (Or.inl (by omega)) (Or.inl (by omega)) (by omega) noZ ((uval _).trans hz)
    (by omega) noO ((uval _).trans ho) uL uT uU uZ uR uC uOut uSrc uOne
  have rr : Run B (transposePackedFrame F) s t (13+transposeSlotsCost F n n) := r₀.seq rt
  refine ⟨t,rr,ht,?_,?_,Frame.of_run rr⟩
  · intro i j
    exact (hAt _ i.isLt _ j.isLt).trans (uval _)
  · intro k hk hOut hk₀ hk₁
    exact (hKeep k hk (by unfold Written; omega)).trans (uval _)

#print axioms transposePackedFrame_run
end EvenTI.P22Pad

set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 1350000

namespace EvenTI.P22Pad

open scoped BigOperators
open EvenTI.P20Sweep EvenTI.P17Execution EvenTI.P15Execution EvenTI.PrimaryAlignment
open EvenTI.P21Pad (inverseAddress)
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val)
open Mathproof.P15RecogIMPDot20261007 (qN)
open Mathproof.P15RecogIMPGrid20261007 (out_lt)
open UniqueFactorizationMonoid

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

theorem columnStart_eq_finSum (width : ℕ → ℕ) (i : ℕ) :
    columnStart width i=∑ j : Fin i, width j.val := by
  induction i with
  | zero => simp [columnStart]
  | succ i ih =>
    rw [columnStart,Fin.sum_univ_castSucc,ih] <;> rfl

/-- Packer columns and native source rows advance over the same widths from
the same archived order. -/
theorem columnStart_eq_siteRowPrefix (width : ℕ → ℕ) (i : ℕ) :
    columnStart width i=EvenTI.P21Site.Mode.rowPrefix width i := by
  induction i with
  | zero => simp [columnStart]
  | succ i ih => rw [columnStart,EvenTI.P21Site.Mode.prefix_succ,ih]

def extendWidths {m : ℕ} (width : Fin m → ℕ) (i : ℕ) : ℕ :=
  if h : i < m then width ⟨i,h⟩ else 0

theorem columnStart_extend_widths {m : ℕ} (width : Fin m → ℕ) :
    columnStart (extendWidths width) m=∑ i, width i := by
  simp [columnStart_eq_finSum,extendWidths]

theorem blockOrder_val_eq_columnStart {m n : ℕ} {width : Fin m → ℕ}
    (h : (∑ i, width i)=n) (i : Fin m) (j : Fin (width i)) :
    (blockOrder h ⟨i,j⟩).val=columnStart (extendWidths width) i.val+j.val := by
  change (finSigmaFinEquiv (n:=width) ⟨i,j⟩).val = _
  rw [finSigmaFinEquiv_apply,columnStart_eq_finSum]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  have hk : k.val < m := k.isLt.trans i.isLt
  rw [extendWidths,dif_pos hk]
  exact congrArg width (Fin.ext rfl)

private noncomputable def padFrameSample : FieldPresentation (ZMod 2) :=
  Classical.choice (Mathproof.Problem18FieldPresentation20260930.exists_fieldPresentation (ZMod 2))

private theorem transpose_preserves_width_words (F : FieldPresentation K) :
    savedWidths ∉ Mathproof.Problem18IMPFieldLayout20261001.arrayWrites (transposePackedFrame F) := by
  change savedWidths ∉ Mathproof.Problem18IMPFieldLayout20261001.arrayWrites (transposePackedFrame padFrameSample)
  decide

noncomputable def installArchivedFrame (F : FieldPresentation K) : Com :=
  .seq packArchiveColumns (transposePackedFrame F)

noncomputable def installArchivedFrameCost (F : FieldPresentation K) (n m : ℕ) : ℕ :=
  packArchiveColumnsCost F n m+(13+transposeSlotsCost F n n)

/-- The exact raw basis bank produced by a complete archive sweep is copied
and transposed into the inverse's matrix input. This also exposes the original
column-major bank as the row-major dual transpose and preserves all source basis words. -/
theorem installArchivedFrame_run (F : FieldPresentation K)
    {B S n off base lane src input Z : ℕ} {s : Env}
    (A : Matrix (Fin n) (Fin n) K) (L : List (Polynomial K))
    (hL : (L : Multiset (Polynomial K))=(normalizedFactors A.charpoly).dedup)
    (hArchive : ∀ i < L.length,
      SavedChart F A (factorAt A L i) (off+i) (rowBasis base lane (off+i))
        (rowChart base lane (off+i)) s)
    (hs : Slots F canonical qN.WS S B s)
    (p : ArchivePorts s n off L.length base (2*lane) src Z)
    (hInput : s.vars inverseInputWord=input)
    (hn : n+1 < B) (hm : L.length < B)
    (hi : ∀ i < L.length, off+i < B) (hStride : 2*lane < B)
    (hBefore : ∀ i < L.length, rowBasis base lane (off+i)+n*n ≤ src)
    (hApart : src+n*n ≤ input) (hFit : input+n*n ≤ Z) (hZ : Z+4 ≤ S) (hB : S+10 < B)
    (hz : val F canonical qN.WS s Z=0) (ho : val F canonical qN.WS s (Z+1)=1) :
    ∃ (t : Env) (width : Fin L.length → ℕ)
      (C : ∀ i : Fin L.length, Matrix (Fin n) (Fin (width i)) K)
      (hSum : (∑ i, width i)=n),
      Run B (installArchivedFrame F) s t (installArchivedFrameCost F n L.length) ∧
      Slots F canonical qN.WS S B t ∧ IsUnit (concatenateFrame C hSum) ∧
      (∀ r c, val F canonical qN.WS t (input+inverseAddress r c)=concatenateFrame C hSum r c) ∧
      (∀ r c, val F canonical qN.WS t (src+inverseAddress c r)=concatenateFrame C hSum r c) ∧
      (∀ i, (t.arrs savedWidths)[off+i.val]?=some (width i)) ∧
      (∀ i, (C i).mulVecLin.range=
        ((Polynomial.aeval A (factorAt A L i.val)).mulVecLin).ker) ∧
      (∀ k < S, (k < src ∨ src+n*n ≤ k) → (k < input ∨ input+n*n ≤ k) →
        k≠Z+2 → k≠Z+3 → val F canonical qN.WS t k=val F canonical qN.WS s k) ∧
      Frame (installArchivedFrame F) s t := by
  obtain ⟨width,C,hSum,hUnit,hWidths,hWords,hRange⟩ :=
    archiveBasis_exists F A L s hL (fun i => hArchive i.val i.isLt)
  let w := extendWidths width
  have hSum' : columnStart w L.length=n := (columnStart_extend_widths width).trans hSum
  have hw : ∀ i < L.length,(s.arrs savedWidths)[off+i]?=some (w i) := by
    intro i hi
    simpa [w,extendWidths,hi] using hWidths ⟨i,hi⟩
  have hSource : ∀ i < L.length, base+(off+i)*(2*lane)+w i*n ≤ src := by
    intro i hi
    have hwle : w i ≤ n := by
      have hl : w i ≤ columnStart w (i+1) := Nat.le_add_left _ _
      refine hl.trans ?_
      rw [← hSum']
      apply columnStart_mono w
      omega
    exact (Nat.add_le_add_left (Nat.mul_le_mul_right n hwle) _).trans (hBefore i hi)
  have hSrcZ : src+n*n ≤ Z := by omega
  obtain ⟨u,c,ru,huCost,hu,pu,_,hWidthKeep,hCopy,hKeep,fu⟩ :=
    packArchiveColumns_run F w hs p hw hSum' (by omega) hm hi hStride hSource hSrcZ hZ hB hz ho
  have uInput : u.vars inverseInputWord=input := (fu.vars _ (by decide)).trans hInput
  have uZero : val F canonical qN.WS u Z=0 :=
    (hKeep _ (by omega) (Or.inr hSrcZ) (by omega) (by omega)).trans hz
  have uOne : val F canonical qN.WS u (Z+1)=1 :=
    (hKeep _ (by omega) (Or.inr (by omega)) (by omega) (by omega)).trans ho
  obtain ⟨t,rt,ht,hTrans,hPreserve,ft⟩ :=
    transposePackedFrame_run F hu pu.size pu.dest uInput pu.zero pu.one pu.tmp₀ pu.tmp₁
      uZero uOne hApart hFit hZ hn
  have hPacked : ∀ r c, val F canonical qN.WS u (src+inverseAddress c r)=concatenateFrame C hSum r c := by
    intro r c
    obtain ⟨⟨i,j⟩,rfl⟩ := (blockOrder hSum).surjective c
    have hj : j.val*n+r.val < w i.val*n := by
      have h := out_lt (o0:=0) j.isLt r.isLt
      simpa [w,extendWidths,i.isLt] using h
    unfold inverseAddress
    rw [blockOrder_val_eq_columnStart]
    have he : src+((columnStart w i.val+j.val)*n+r.val) =
        src+columnStart w i.val*n+(j.val*n+r.val) := by ring
    rw [he,hCopy i.val i.isLt _ hj]
    change val F canonical qN.WS s (rowBasis base lane (off+i.val)+(j.val*n+r.val))=_
    exact (hWords i r j).trans (by rw [concatenateFrame,Equiv.symm_apply_apply])
  have rr : Run B (installArchivedFrame F) s t (installArchivedFrameCost F n L.length) :=
    (ru.seq rt).mono (Nat.add_le_add_right huCost _)
  refine ⟨t,width,C,hSum,rr,ht,hUnit,?_,?_,?_,hRange,?_,Frame.of_run rr⟩
  · intro r c
    exact (hTrans r c).trans (hPacked r c)
  · intro r c
    have hk : src+inverseAddress c r < input := by
      exact (out_lt (o0:=src) c.isLt r.isLt).trans_le hApart
    exact (hPreserve _ (by omega) (Or.inl hk) (by omega) (by omega)).trans (hPacked r c)
  · intro i
    rw [ft.arrs savedWidths (transpose_preserves_width_words F),hWidthKeep]
    exact hWidths i
  · intro k hk h₁ h₂ h₃ h₄
    exact (hPreserve k hk h₂ h₃ h₄).trans (hKeep k hk h₁ h₃ h₄)

#print axioms columnStart_eq_siteRowPrefix
#print axioms blockOrder_val_eq_columnStart
#print axioms installArchivedFrame_run
end EvenTI.P22Pad
