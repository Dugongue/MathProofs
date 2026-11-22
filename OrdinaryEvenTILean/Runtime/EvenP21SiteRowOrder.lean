import EvenP6LiveCellsNative
import EvenP6NativePrefix
import EvenP20ScalarNativeCRTMeaning

namespace EvenTI.P21Site.RowOrder
open scoped BigOperators
open EvenTI.LiveAlgebra EvenTI.PrimaryAlignment EvenTI.CellPreparation EvenTI.CellProducer

set_option autoImplicit false
set_option maxHeartbeats 300000

variable {K : Type} [Field K]

def physicalBlockOffset (m : PreparedMode K) (i : Fin m.blocks.length) : ℕ :=
  ∑ j : Fin i.val, (m.blocks.get (Fin.castLE i.isLt.le j)).width

/-- Native origin expansion preserves the primary block's contiguous physical
coordinate interval, including repeated blocks with many scalar origins. -/
theorem numberedModeSlots_interval (m : PreparedMode K)
    (h : (∑ i : Fin m.blocks.length, (m.blocks.get i).width) = m.n)
    (v : Fin (modeWidth m)) (k : numberedCoordinate m v) :
    (numberedModeSlots m h ⟨v,k⟩).val = 
      physicalBlockOffset m (EvenTI.LiveAlgebra.numberedOrigin m v).1+
        (blockWordSlots (m.blocks.get (EvenTI.LiveAlgebra.numberedOrigin m v).1) ((EvenTI.LiveAlgebra.numberedOrigin m v).2,k)).val := by
  rw [numberedModeSlots_apply]
  change (finSigmaFinEquiv (n:=fun i : Fin m.blocks.length => (m.blocks.get i).width)
    ⟨(EvenTI.LiveAlgebra.numberedOrigin m v).1,
      blockWordSlots (m.blocks.get (EvenTI.LiveAlgebra.numberedOrigin m v).1) ((EvenTI.LiveAlgebra.numberedOrigin m v).2,k)⟩).val = _
  rw [finSigmaFinEquiv_apply]
  rfl

/-- Reading a literal inverse-chart row recovers the same primary block as
reading its flat width interval. No equality of anchor and native cell labels occurs. -/
theorem numbered_inverse_primaryBlock (m : PreparedMode K)
    (h : (∑ i : Fin m.blocks.length, (m.blocks.get i).width) = m.n) (q : Fin m.n) :
    (EvenTI.LiveAlgebra.numberedOrigin m ((numberedModeSlots m h).symm q).1).1 = 
      ((blockOrder h).symm q).1 := by
  let a := (numberedModeSlots m h).symm q
  have he : blockOrder h (modeWordSlots m ⟨EvenTI.LiveAlgebra.numberedOrigin m a.1,a.2⟩) = q :=
    (numberedModeSlots m h).apply_symm_apply q
  have hh := congrArg (fun z => ((blockOrder h).symm z).1) he
  rw [Equiv.symm_apply_apply] at hh
  exact hh

/-- A physical row belongs to the interval of precisely its native primary block. -/
theorem numbered_inverse_interval (m : PreparedMode K)
    (h : (∑ i : Fin m.blocks.length, (m.blocks.get i).width) = m.n) (q : Fin m.n) :
    let a := (numberedModeSlots m h).symm q
    let i := (EvenTI.LiveAlgebra.numberedOrigin m a.1).1
    physicalBlockOffset m i  ≤  q.val ∧ q.val < physicalBlockOffset m i+(m.blocks.get i).width := by
  dsimp only
  let a := (numberedModeSlots m h).symm q
  have he := numberedModeSlots_interval m h a.1 a.2
  rw [show numberedModeSlots m h ⟨a.1,a.2⟩ = q from
    (numberedModeSlots m h).apply_symm_apply q] at he
  have hk := (blockWordSlots (m.blocks.get (EvenTI.LiveAlgebra.numberedOrigin m a.1).1)
    ((EvenTI.LiveAlgebra.numberedOrigin m a.1).2,a.2)).isLt
  change physicalBlockOffset m (EvenTI.LiveAlgebra.numberedOrigin m a.1).1 ≤ q.val ∧
    q.val < physicalBlockOffset m (EvenTI.LiveAlgebra.numberedOrigin m a.1).1+(m.blocks.get (EvenTI.LiveAlgebra.numberedOrigin m a.1).1).width
  omega

/-- The final numeric width cast used by actual recoverTrialSites changes no
physical row number, so the same interval identity holds in literal raw widths. -/
theorem cast_numberedModeSlots_interval (m : PreparedMode K)
    (h : (∑ i : Fin m.blocks.length, (m.blocks.get i).width) = m.n)
    {n : ℕ} (hw : m.n = n) (v : Fin (modeWidth m)) (k : numberedCoordinate m v) :
    (((numberedModeSlots m h).trans (finCongr hw)) ⟨v,k⟩).val = 
      physicalBlockOffset m (EvenTI.LiveAlgebra.numberedOrigin m v).1+
        (blockWordSlots (m.blocks.get (EvenTI.LiveAlgebra.numberedOrigin m v).1) ((EvenTI.LiveAlgebra.numberedOrigin m v).2,k)).val :=
  numberedModeSlots_interval m h v k

def nativeBlockOffset (m : PreparedMode K) (i : Fin m.blocks.length) : ℕ :=
  ∑ j : Fin i.val, blockOriginCount (m.blocks.get (Fin.castLE i.isLt.le j))

def nativeModeOffset {c : ℕ} (m : Fin c → PreparedMode K) (p : Fin c) : ℕ :=
  ∑ j : Fin p.val, modeWidth (m (Fin.castLE p.isLt.le j))

private theorem freeOrigin_local_zero (m : PreparedMode K) (o : ModeOrigin m)
    (hf : originIsFixed m o = false) : o.2.val = 0 := by
  have hj := o.2.isLt
  cases hb : (m.blocks.get o.1).compare with
  | inl T =>
    have hc : blockOriginCount (m.blocks.get o.1) = 1 := by simp only [blockOriginCount,hb]
    have hSmall := lt_of_lt_of_le hj (le_of_eq hc)
    omega
  | inr units => simp only [originIsFixed,hb,Bool.true_eq_false] at hf

private theorem sharedSlot_origin_val {c : ℕ} (m : Fin c → PreparedMode K) (p : Fin c)
    (v : Fin (modeWidth (m p))) :
    (sharedSlot (width:=fun p => modeWidth (m p)) p v).val = nativeModeOffset m p+
      nativeBlockOffset (m p) (EvenTI.LiveAlgebra.numberedOrigin (m p) v).1+
      (EvenTI.LiveAlgebra.numberedOrigin (m p) v).2.val := by
  let o := EvenTI.LiveAlgebra.numberedOrigin (m p) v
  have hv : modeOriginOrder (m p) o = v := (modeOriginOrder (m p)).apply_symm_apply v
  calc
    _  =  (sharedSlot (width:=fun p => modeWidth (m p)) p (modeOriginOrder (m p) o)).val := congrArg (fun z => (sharedSlot (width:=fun p => modeWidth (m p)) p z).val) hv.symm
    _  =  _ := by
      dsimp only [o]
      unfold sharedSlot modeOriginOrder nativeModeOffset nativeBlockOffset
      rw [finSigmaFinEquiv_apply,finSigmaFinEquiv_apply]
      ac_rfl

variable [Fintype K] [DecidableEq K]

/-- Every native field origin occurs in a physical row. Zero-dimensional
origins would make the verified field model identify zero and one. -/
theorem numberedCoordinate_nonempty (m : PreparedMode K)
    [∀ i : Fin m.blocks.length, Fact ((m.blocks.get i).HasFieldModel)]
    (v : Fin (modeWidth m)) : Nonempty (numberedCoordinate m v) := by
  letI : WordTable.Laws (numberedTable m v) := numberedWordLaws m v
  letI : WordFieldCertificate (numberedTable m v) := numberedFieldCertificate m v
  by_contra hn
  have hz : (numberedTable m v).one = 0 := by
    funext k
    exact False.elim (hn ⟨k⟩)
  have ho := wordDecode_one (numberedTable m v)
  rw [hz,map_zero] at ho
  exact zero_ne_one ho

#print axioms numberedCoordinate_nonempty
/-- The literal signed site of every numbered row is constant throughout a
primary physical block: free/simple gets its one shared positive address,
while every repeated origin receives the common pin address. -/
theorem physical_row_site (w : TrialWords K) (m : Fin w.modeCount → PreparedMode K)
    (r : Fin (w.sites+2)) (v : Fin (CodeWidth w m (w.mode r))) (t d : ℕ) :
    (EvenTI.P20Scalar.sharedBlockPhysicalSlot w.mode (branchIsFree w m) t d r v).val = 
      if originIsFixed (m (w.mode r)) (EvenTI.LiveAlgebra.numberedOrigin (m (w.mode r)) v) then 0 else
        2*(nativeModeOffset m (w.mode r)+
          nativeBlockOffset (m (w.mode r)) (EvenTI.LiveAlgebra.numberedOrigin (m (w.mode r)) v).1)+1 := by
  rw [EvenTI.P20Scalar.sharedBlockPhysicalSlot_val]
  unfold branchIsFree
  cases hf : originIsFixed (m (w.mode r)) (EvenTI.LiveAlgebra.numberedOrigin (m (w.mode r)) v) with
  | false =>
    have hj := freeOrigin_local_zero (m (w.mode r)) (EvenTI.LiveAlgebra.numberedOrigin (m (w.mode r)) v) hf
    rw [sharedSlot_origin_val m (w.mode r) v,hj]
    simp
  | true => simp

#print axioms physical_row_site
/-- Within-primary changes of inverse-frame basis preserve the exact supported
block test, allowing bare archived primary bases in place of Krylov gauges. -/
theorem primary_support_leftUnit {r n p : ℕ}
    (H : (Matrix (Fin r) (Fin r) K)ˣ) (R : Matrix (Fin r) (Fin n) K)
    (P : Matrix (Fin n) (Fin p) K) :
    (H.val*R)*P = 0 ↔ R*P = 0 := by
  constructor
  · intro h
    have he := congrArg (fun A : Matrix (Fin r) (Fin p) K => H.inv*A) h
    simpa only [← Matrix.mul_assoc,H.inv_val,Matrix.one_mul,Matrix.mul_zero] using he
  · intro h
    rw [Matrix.mul_assoc,h,Matrix.mul_zero]

#print axioms primary_support_leftUnit
#print axioms numberedModeSlots_interval
#print axioms numbered_inverse_primaryBlock
#print axioms numbered_inverse_interval
#print axioms cast_numberedModeSlots_interval
end EvenTI.P21Site.RowOrder

namespace EvenTI.P21Site.Prepare
open EvenTI.LiveAlgebra EvenTI.PrimaryAlignment EvenTI.CellPreparation EvenTI.CellProducer
open Matrix EvenTI.Contract

set_option autoImplicit false
set_option maxHeartbeats 350000

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

def isRepeated {n : ℕ} (b : ModeBlock K n) : Bool :=
  match b.compare with
  | .inl _ => false
  | .inr _ => true

/-- The archived multiplicity is exactly the branch used by the native
constructor; it is not a heuristic classification of a primary space. -/
theorem prepareModeBlock_tags (D : FieldEncoding K) (budget : ℕ)
    {n : ℕ} (A B : Matrix (Fin n) (Fin n) K) (row : List K × ℕ)
    (b : ModeBlock K n) (h : prepareModeBlock D budget A B row = some b) :
    b.factor = row ∧ b.width = EvenTI.PrimaryAlignment.blockWidth A row.1 row.2 ∧
      isRepeated b = decide (row.2 ≠ 1) := by
  rcases row with ⟨p,e⟩
  unfold prepareModeBlock at h
  dsimp only at h
  split at h
  · rename_i hw
    split at h
    · rename_i he
      cases ht : prepareSimpleWordTable (EvenTI.PrimaryProducer.restrictedAnchor A p e) with
      | none => simp only [ht,Option.map_none,reduceCtorEq] at h
      | some T =>
        simp only [ht,Option.map_some] at h
        obtain rfl := Option.some.inj h
        refine ⟨rfl,rfl,?_⟩
        simp only [isRepeated,he,ne_eq,not_true_eq_false,decide_false]
    · rename_i he
      obtain rfl := Option.some.inj h
      refine ⟨rfl,rfl,?_⟩
      simp only [isRepeated,he,ne_eq,not_false_eq_true,decide_true]
  · contradiction

theorem nativeBlock_fixed (m : PreparedMode K) (i : Fin m.blocks.length)
    (j : Fin (blockOriginCount (m.blocks.get i))) :
    originIsFixed m (EvenTI.LiveAlgebra.numberedOrigin m (modeOriginOrder m ⟨i,j⟩))  = 
      isRepeated (m.blocks.get i) := by
  unfold EvenTI.LiveAlgebra.numberedOrigin
  rw [Equiv.symm_apply_apply]
  unfold originIsFixed isRepeated
  cases (m.blocks.get i).compare <;> rfl

/-- The chronological native prefix advance is computed directly from the
same literal multiplicity and kernel width as the actual native constructor. -/
theorem prepareModeBlock_originCount (D : FieldEncoding K) (budget : ℕ)
    {n : ℕ} (A B : Matrix (Fin n) (Fin n) K) (row : List K × ℕ)
    (b : ModeBlock K n) (h : prepareModeBlock D budget A B row = some b) :
    blockOriginCount b = if row.2 = 1 then 1 else b.width := by
  have ht := (prepareModeBlock_tags D budget A B row b h).2.2
  have hc : blockOriginCount b = if isRepeated b then b.width else 1 := by
    unfold blockOriginCount isRepeated
    cases b.compare <;> rfl
  rw [hc,ht]
  by_cases he : row.2 = 1 <;> simp [he]

#print axioms prepareModeBlock_originCount
#print axioms prepareModeBlock_tags
#print axioms nativeBlock_fixed
end EvenTI.P21Site.Prepare
