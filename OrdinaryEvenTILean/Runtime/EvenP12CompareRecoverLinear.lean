import EvenP12CompareRecoverUnary

namespace EvenTI.P12Compare

open scoped BigOperators Matrix
open Mathproof.P15NetworkDefs20261007

set_option linter.unusedSectionVars false

variable {M m n : ℕ} [NeZero M]

/-- Numeric extraction from one installed Smith row. Only B and U are read,
and the right-hand side is the portion preceding the symbolic coordinate. -/
def coordinateEquation (B : Matrix (Fin (m+1)) (Fin n) (ZMod M))
    (U : Matrix (Fin (m+1)) (Fin (m+1)) (ZMod M))
    (b : Fin m → ZMod M) (r : Fin (m+1)) : UnaryEquation :=
  ⟨(U r (Fin.last m)).val, M - (∑ j : Fin m, U r j.castSucc * b j : ZMod M).val,
    Nat.gcd (rowEntryZ B r).val M⟩

def coordinateEquations (B : Matrix (Fin (m+1)) (Fin n) (ZMod M))
    (U : Matrix (Fin (m+1)) (Fin (m+1)) (ZMod M))
    (b : Fin m → ZMod M) : List UnaryEquation :=
  List.ofFn (coordinateEquation B U b)

theorem coordinateEquations_length (B : Matrix (Fin (m+1)) (Fin n) (ZMod M))
    (U : Matrix (Fin (m+1)) (Fin (m+1)) (ZMod M)) (b : Fin m → ZMod M) :
    (coordinateEquations B U b).length = m+1 := by simp [coordinateEquations]

private theorem coordinateEquations_divide (B : Matrix (Fin (m+1)) (Fin n) (ZMod M))
    (U : Matrix (Fin (m+1)) (Fin (m+1)) (ZMod M)) (b : Fin m → ZMod M) :
    ∀ e ∈ coordinateEquations B U b, e.modulus ∣ M := by
  intro e he
  obtain ⟨r,rfl⟩ := List.mem_ofFn.mp he
  exact Nat.gcd_dvd_right _ _

/-- Recover one extendible coordinate from the same installed B and U
matrices used by the physical Smith consistency test. -/
def valueFromBanks (B : Matrix (Fin (m+1)) (Fin n) (ZMod M))
    (U : Matrix (Fin (m+1)) (Fin (m+1)) (ZMod M)) (b : Fin m → ZMod M) : Option (ZMod M) :=
  (solveUnaryList (coordinateEquations B U b)).map (fun w => (w.1 : ZMod M))

theorem valueFromBanks_candidate_iff
    (A : Matrix (Fin m) (Fin n) (ZMod M)) (b : Fin m → ZMod M) (i : Fin n)
    {st : ZDiag.State M (m+1) n} (h : ZDiag.Valid (appendCoordinate A i) st)
    (hD : IsMonoDiag st.B) (s : ZMod M) :
    (∀ e ∈ coordinateEquations st.B st.U b, e.Satisfied s.val) ↔
      ∃ x, A.mulVec x = b ∧ x i = s := by
  rw [appendCoordinate_certificate A b i h hD s]
  constructor
  · intro he r
    have hr := he (coordinateEquation st.B st.U b r) (List.mem_ofFn.mpr ⟨r,rfl⟩)
    simpa only [add_comm (st.U r (Fin.last m) * s) (∑ j : Fin m, st.U r j.castSucc * b j)] using
      (unaryDvd_iff (st.U r (Fin.last m)) s
      (∑ j : Fin m, st.U r j.castSucc * b j) (Nat.gcd_dvd_right _ _)).mpr
      (by simpa only [coordinateEquation,UnaryEquation.Satisfied] using hr)
  · intro he e hym
    obtain ⟨r,rfl⟩ := List.mem_ofFn.mp hym
    simpa only [coordinateEquation,UnaryEquation.Satisfied] using (unaryDvd_iff (st.U r (Fin.last m)) s
      (∑ j : Fin m, st.U r j.castSucc * b j) (Nat.gcd_dvd_right _ _)).mp
      (by simpa only [mul_comm (st.U r (Fin.last m)) s,add_comm] using he r)

theorem valueFromBanks_sound
    (A : Matrix (Fin m) (Fin n) (ZMod M)) (b : Fin m → ZMod M) (i : Fin n)
    {st : ZDiag.State M (m+1) n} (h : ZDiag.Valid (appendCoordinate A i) st)
    (hD : IsMonoDiag st.B) {s : ZMod M} (hs : valueFromBanks st.B st.U b = some s) :
    ∃ x, A.mulVec x = b ∧ x i = s := by
  obtain ⟨w,hw,rfl⟩ := Option.map_eq_some_iff.mp hs
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hdiv := coordinateEquations_divide st.B st.U b
  have hp (e) (he : e ∈ coordinateEquations st.B st.U b) : 0 < e.modulus :=
    Nat.pos_of_dvd_of_pos (hdiv e he) hM
  have hr := solveUnaryList_bounds _ hM hdiv hw
  have hwM : w.1 < M := hr.2.2.trans_le (Nat.le_of_dvd hM hr.2.1)
  apply (valueFromBanks_candidate_iff A b i h hD _).mp
  rw [ZMod.val_natCast,Nat.mod_eq_of_lt hwM]
  exact (solveUnaryList_correct _ hp w.1).mp ⟨w,hw,Nat.ModEq.refl _⟩

theorem valueFromBanks_complete
    (A : Matrix (Fin m) (Fin n) (ZMod M)) (b : Fin m → ZMod M) (i : Fin n)
    {st : ZDiag.State M (m+1) n} (h : ZDiag.Valid (appendCoordinate A i) st)
    (hD : IsMonoDiag st.B) {x : Fin n → ZMod M} (hx : A.mulVec x = b) :
    (valueFromBanks st.B st.U b).isSome = true := by
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hp (e) (he : e ∈ coordinateEquations st.B st.U b) : 0 < e.modulus :=
    Nat.pos_of_dvd_of_pos (coordinateEquations_divide st.B st.U b e he) hM
  have hr := (valueFromBanks_candidate_iff A b i h hD (x i)).mpr ⟨x,hx,rfl⟩
  obtain ⟨w,hw,_⟩ := (solveUnaryList_correct _ hp (x i).val).mpr hr
  rw [valueFromBanks,hw]
  rfl

def recoverCoordinate (A : Matrix (Fin m) (Fin n) (ZMod M))
    (b : Fin m → ZMod M) (i : Fin n) : Option (ZMod M) :=
  let st := ZDiag.zmodDiag (appendCoordinate A i)
  valueFromBanks st.B st.U b

theorem recoverCoordinate_sound
    (A : Matrix (Fin m) (Fin n) (ZMod M)) (b : Fin m → ZMod M) (i : Fin n)
    {s : ZMod M} (hs : recoverCoordinate A b i = some s) :
    ∃ x, A.mulVec x = b ∧ x i = s := by
  obtain ⟨hU₁,hU₂,hV₁,hV₂,hB,hD⟩ := ZDiag.zmodDiag_spec (appendCoordinate A i)
  exact valueFromBanks_sound A b i ⟨hB,hU₁,hU₂,hV₁,hV₂⟩ hD hs

theorem recoverCoordinate_complete
    (A : Matrix (Fin m) (Fin n) (ZMod M)) (b : Fin m → ZMod M) (i : Fin n)
    {x : Fin n → ZMod M} (hx : A.mulVec x = b) :
    (recoverCoordinate A b i).isSome = true := by
  obtain ⟨hU₁,hU₂,hV₁,hV₂,hB,hD⟩ := ZDiag.zmodDiag_spec (appendCoordinate A i)
  exact valueFromBanks_complete A b i ⟨hB,hU₁,hU₂,hV₁,hV₂⟩ hD hx

private theorem appendCoordinate_solution
    (A : Matrix (Fin m) (Fin n) (ZMod M)) (b : Fin m → ZMod M) (i : Fin n)
    (x : Fin n → ZMod M) (h : A.mulVec x = b) :
    (appendCoordinate A i).mulVec x = appendCoordinateRhs b (x i) := by
  funext j
  refine Fin.lastCases ?_ (fun r => ?_) j
  · simp [appendCoordinate,appendCoordinateRhs,Matrix.mulVec,dotProduct,ite_mul]
  · simpa [appendCoordinate,appendCoordinateRhs,Matrix.mulVec,dotProduct] using congrFun h r

private theorem unappendCoordinate_solution
    (A : Matrix (Fin m) (Fin n) (ZMod M)) (b : Fin m → ZMod M) (i : Fin n)
    (x : Fin n → ZMod M) (s : ZMod M)
    (h : (appendCoordinate A i).mulVec x = appendCoordinateRhs b s) :
    A.mulVec x = b ∧ x i = s := by
  refine ⟨funext fun r => ?_,?_⟩
  · simpa [appendCoordinate,appendCoordinateRhs,Matrix.mulVec,dotProduct]
      using congrFun h r.castSucc
  · simpa [appendCoordinate,appendCoordinateRhs,Matrix.mulVec,dotProduct,ite_mul]
      using congrFun h (Fin.last m)

/-- Each iteration fixes one new coordinate and uses one Smith invocation.
The input of that invocation has one appended row with a symbolic RHS. -/
def fixCoordinates (M n : ℕ) [NeZero M] :
    (is : List (Fin n)) → (w : Fin n → ZMod M) → {m : ℕ} →
    Matrix (Fin m) (Fin n) (ZMod M) → (Fin m → ZMod M) → Option (Fin n → ZMod M)
  | [], w, _, _, _ => some w
  | i :: is, w, _, A, b => do
    let s ← recoverCoordinate A b i
    fixCoordinates M n is (Function.update w i s) (appendCoordinate A i)
      (appendCoordinateRhs b s)

private theorem fixCoordinates_complete (is : List (Fin n)) (hn : is.Nodup) (w : Fin n → ZMod M)
    (A : Matrix (Fin m) (Fin n) (ZMod M)) (b : Fin m → ZMod M)
    (h : ∃ x, A.mulVec x = b) :
    ∃ u, fixCoordinates M n is w A b = some u ∧
      ∃ y, A.mulVec y = b ∧ (∀ i ∈ is, u i = y i) ∧ (∀ i ∉ is, u i = w i) := by
  induction is generalizing m w with
  | nil =>
    obtain ⟨y,hy⟩ := h
    exact ⟨w,rfl,y,hy,by simp,by simp⟩
  | cons i is ih =>
    have hnodup := List.nodup_cons.mp hn
    obtain ⟨x,hx⟩ := h
    obtain ⟨s,hs⟩ := Option.isSome_iff_exists.mp (recoverCoordinate_complete A b i hx)
    obtain ⟨x',hx',hix'⟩ := recoverCoordinate_sound A b i hs
    have hxapp : (appendCoordinate A i).mulVec x' = appendCoordinateRhs b s := by
      rw [← hix']
      exact appendCoordinate_solution A b i x' hx'
    obtain ⟨u,hu,y,hy,hmem,hout⟩ := ih hnodup.2 (Function.update w i s)
      (appendCoordinate A i) (appendCoordinateRhs b s) ⟨x',hxapp⟩
    obtain ⟨hy',hiy⟩ := unappendCoordinate_solution A b i y s hy
    refine ⟨u,by simp [fixCoordinates,hs,hu],y,hy',?_,?_⟩
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact (hout j hnodup.1).trans (by simpa using hiy.symm)
      · exact hmem j hj
    · intro j hj
      have hn₁ : j ≠ i := fun h => hj (h ▸ List.mem_cons_self)
      have hn₂ : j ∉ is := fun h => hj (List.mem_cons_of_mem _ h)
      rw [hout j hn₂,Function.update_of_ne hn₁]

/-- Finite recovery of a coherent solution by coordinate fixing. The last
matrix-vector product also covers zero-column and malformed instances. -/
def recoverLinear (A : Matrix (Fin m) (Fin n) (ZMod M))
    (b : Fin m → ZMod M) : Option (Fin n → ZMod M) := do
  let u ← fixCoordinates M n (List.finRange n) 0 A b
  if A.mulVec u = b then some u else none

theorem recoverLinear_sound
    (A : Matrix (Fin m) (Fin n) (ZMod M)) (b : Fin m → ZMod M)
    {x : Fin n → ZMod M} (h : recoverLinear A b = some x) : A.mulVec x = b := by
  unfold recoverLinear at h
  obtain ⟨y,_,hy⟩ := Option.bind_eq_some_iff.mp h
  split at hy
  · obtain rfl := Option.some.inj hy
    assumption
  · contradiction

theorem recoverLinear_complete
    (A : Matrix (Fin m) (Fin n) (ZMod M)) (b : Fin m → ZMod M)
    (h : ∃ x, A.mulVec x = b) : (recoverLinear A b).isSome = true := by
  obtain ⟨u,hu,y,hy,hmem,_⟩ :=
    fixCoordinates_complete (List.finRange n) (List.nodup_finRange n) 0 A b h
  have huy : u = y := funext fun i => hmem i (List.mem_finRange _)
  unfold recoverLinear
  rw [hu]
  change (if A.mulVec u = b then some u else none).isSome = true
  rw [if_pos (show A.mulVec u = b by simpa only [huy] using hy)]
  rfl

#print axioms valueFromBanks_sound
/-- Installed Smith states can vary. The returned coordinate is the least
canonical representative among all extendible coordinates. -/
theorem valueFromBanks_min
    (A : Matrix (Fin m) (Fin n) (ZMod M)) (b : Fin m → ZMod M) (i : Fin n)
    {st : ZDiag.State M (m+1) n} (h : ZDiag.Valid (appendCoordinate A i) st)
    (hD : IsMonoDiag st.B) {s t : ZMod M} (hs : valueFromBanks st.B st.U b = some s)
    (ht : ∃ x, A.mulVec x = b ∧ x i = t) : s.val ≤ t.val := by
  obtain ⟨w,hw,rfl⟩ := Option.map_eq_some_iff.mp hs
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hdiv := coordinateEquations_divide st.B st.U b
  have hp (e) (he : e ∈ coordinateEquations st.B st.U b) : 0 < e.modulus :=
    Nat.pos_of_dvd_of_pos (hdiv e he) hM
  have hr := solveUnaryList_bounds _ hM hdiv hw
  have hwM : w.1 < M := hr.2.2.trans_le (Nat.le_of_dvd hM hr.2.1)
  have ht' := (valueFromBanks_candidate_iff A b i h hD t).mpr ht
  obtain ⟨v,hv,hMod⟩ := (solveUnaryList_correct _ hp t.val).mpr ht'
  have he : v = w := Option.some.inj (hv.symm.trans hw)
  subst v
  change t.val % w.2 = w.1 % w.2 at hMod
  rw [Nat.mod_eq_of_lt hr.2.2] at hMod
  rw [ZMod.val_natCast,Nat.mod_eq_of_lt hwM,← hMod]
  exact Nat.mod_le _ _

theorem valueFromBanks_eq
    (A : Matrix (Fin m) (Fin n) (ZMod M)) (b : Fin m → ZMod M) (i : Fin n)
    {st₁ st₂ : ZDiag.State M (m+1) n}
    (h₁ : ZDiag.Valid (appendCoordinate A i) st₁) (hD₁ : IsMonoDiag st₁.B)
    (h₂ : ZDiag.Valid (appendCoordinate A i) st₂) (hD₂ : IsMonoDiag st₂.B) :
    valueFromBanks st₁.B st₁.U b = valueFromBanks st₂.B st₂.U b := by
  cases hs₁ : valueFromBanks st₁.B st₁.U b with
  | none =>
    cases hs₂ : valueFromBanks st₂.B st₂.U b with
    | none => rfl
    | some t =>
      obtain ⟨x,hx,_⟩ := valueFromBanks_sound A b i h₂ hD₂ hs₂
      have hf := valueFromBanks_complete A b i h₁ hD₁ hx
      simp [hs₁] at hf
  | some s =>
    have hx := valueFromBanks_sound A b i h₁ hD₁ hs₁
    obtain ⟨x,hx',hxs⟩ := hx
    obtain ⟨t,ht⟩ := Option.isSome_iff_exists.mp (valueFromBanks_complete A b i h₂ hD₂ hx')
    rw [ht]
    apply congrArg some
    apply ZMod.val_injective
    apply Nat.le_antisymm
    · exact valueFromBanks_min A b i h₁ hD₁ hs₁ (valueFromBanks_sound A b i h₂ hD₂ ht)
    · exact valueFromBanks_min A b i h₂ hD₂ ht ⟨x,hx',hxs⟩

#print axioms valueFromBanks_complete
#print axioms valueFromBanks_eq
#print axioms recoverLinear_sound
#print axioms recoverLinear_complete

end EvenTI.P12Compare
