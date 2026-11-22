import EvenP12CompareRawLayout
import EvenP10WordsHeader
import Mathproof.Meta.Problem18IMPFieldIO20261001
import Mathproof.Meta.Problem18RAMLax51ProofsRamToTMPolytime20261001

namespace EvenTI.P12ComparePrep

open EvenTI.Action EvenTI.Contract EvenTI.P10Words
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Compile
open Mathproof.Problem18IMPFieldIO20261001
open Mathproof.Problem18IMPFieldAddition20261001 (pointState writeValues writeValues_length writeValues_inside)
open Lax51.TuringPolytime
set_option autoImplicit false

variable {K : Type} [Field K] [Fintype K]

theorem encode_decodeDigit (F : FieldEncoding K) {w : Nat} (hw : w < Fintype.card K) :
    (F (decodeDigit F w)).val = w := by
  simp [decodeDigit,hw]

/-- A valid raw tensor block is an exact canonical encoding after decoding. -/
theorem tensorWords_decodeTensor (F : FieldEncoding K) (n d : Nat) (xs : List Nat)
    (hlen : xs.length = n^d) (hDigit : ∀ v ∈ xs, v < Fintype.card K) :
    tensorWords F (decodeTensor F n d xs) = xs := by
  let T : Tensor K d n := fun x => decodeDigit F (xs.getD (inputCoordOrder n d x).val 0)
  have h : tensorWords F T = xs := by
    rw [tensorWords_eq_inputCoordOrder]
    apply List.ext_getElem (by simpa using hlen.symm)
    intro i hi hi'
    simp only [List.getElem_ofFn, T, Equiv.apply_symm_apply]
    rw [List.getD_eq_getElem _ _ hi']
    exact encode_decodeDigit F (hDigit _ (List.getElem_mem hi'))
  rw [← h,decodeTensor_encode]

/-- Every accepted raw pair is equal, byte for byte, to the comparison codec
of its decoded cells. This lets array loading feed both original cut kernels. -/
theorem decodePair_reencode (F : FieldEncoding K) (xs : List Nat) {p : ParsedPair K}
    (hp : decodePair F xs = some p) : comparisonInput F p.source p.target = xs := by
  match xs, hp with
  | d :: n :: ws, hp =>
    rw [decodePair_cons_cons] at hp
    split_ifs at hp with hv
    obtain rfl := Option.some.inj hp
    simp only [denseValid,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at hv
    obtain ⟨_,hLen⟩ := hv.1
    have hDigit := hv.2
    unfold comparisonInput
    rw [tensorWords_decodeTensor F _ _ _ (by simp [hLen]; omega)
          (fun v hv => hDigit v (List.mem_of_mem_take hv)),
      tensorWords_decodeTensor F _ _ _ (by simp [hLen]; omega)
          (fun v hv => hDigit v (List.mem_of_mem_drop hv))]
    simp only [List.append_assoc,List.take_append_drop,List.cons_append,List.nil_append]

theorem denseValid_eq_isSome (F : FieldEncoding K) (xs : List Nat) :
    denseValid (Fintype.card K) 2 xs = (decodePair F xs).isSome := by
  match xs with
  | [] | [_] => rfl
  | d :: n :: ws =>
    rw [decodePair_cons_cons]
    cases denseValid (Fintype.card K) 2 (d :: n :: ws) <;> rfl

theorem pairValid_time (F : FieldEncoding K) :
    TuringPolytime (denseValidWords (Fintype.card K) 2) :=
  Lax51Proofs.RamToTM.ramPolytime_to_turingPolytime (denseValidWords_ramPolytime _ _ (by decide))

/-- The raw comparison bank is kept at its exact length. No extra separator
or sentinel is stored in this bank. -/
def rawPairIO : Names := ⟨"even.compare.raw","even.compare.raw.base",
  "even.compare.raw.cursor","even.compare.raw.len","even.compare.raw.word"⟩

def rawPairLoad : Com := readBlock rawPairIO

theorem rawPairIO_valid : rawPairIO.Valid := by simp [rawPairIO,Names.Valid]

private theorem paid_exact_array (r : Names) (σ : Env) (xs tail : List Nat)
    (hb : σ.vars r.base = 0) (hlen : (σ.arrs r.array).length = xs.length) :
    (readState r σ xs tail xs.length).arrs r.array = xs := by
  have hArray : (readState r σ xs tail xs.length).arrs r.array =
      writeValues (σ.arrs r.array) (σ.vars r.base) (fun j => xs.getD j 0) xs.length := by
    simp [readState,pointState,Names.point]
  have hLen : ((readState r σ xs tail xs.length).arrs r.array).length = xs.length := by
    rw [hArray,writeValues_length,hlen]
  apply List.ext_getElem hLen
  intro j hj hj'
  have hd : ((readState r σ xs tail xs.length).arrs r.array).getD j 0 = xs.getD j 0 := by
    rw [hArray,hb]
    simpa only [Nat.zero_add] using writeValues_inside (σ.arrs r.array) 0 xs.length j
      (fun k => xs.getD k 0) (by rw [hlen]; omega) hj'
  simpa only [List.getD_eq_getElem _ _ hj,List.getD_eq_getElem _ _ hj'] using hd

theorem rawPairLoad_run (xs tail : List Nat) {B : Nat} {σ : Env}
    (hInput : σ.inp = xs++tail) (hBase : σ.vars rawPairIO.base = 0)
    (hLength : σ.vars rawPairIO.limit = xs.length)
    (hArray : (σ.arrs rawPairIO.array).length = xs.length)
    (hSize : xs.length < B) (hWords : ∀ v ∈ xs, v < B) :
    ∃ τ, Run B rawPairLoad σ τ (20*(xs.length+1)) ∧ τ.arrs rawPairIO.array = xs ∧
      (∀ bank, bank ≠ rawPairIO.array → τ.arrs bank = σ.arrs bank) ∧
      (∀ r, r ≠ rawPairIO.index → r ≠ rawPairIO.value → τ.vars r = σ.vars r) ∧
      τ.inp = tail ∧ τ.out = σ.out := by
  refine ⟨readState rawPairIO σ xs tail xs.length,
    readBlock_run rawPairIO rawPairIO_valid σ xs tail hInput hSize hLength (by simp [hBase,hArray])
      (by rwa [hArray]) hWords,paid_exact_array rawPairIO σ xs tail hBase hArray,?_,?_,?_,?_⟩
  · intro bank hbank
    simp [readState,pointState,Names.point,hbank]
  · intro x hx hw
    exact readState_vars rawPairIO σ xs tail xs.length x hx hw
  · simp [readState]
  · rfl

theorem rawPairLoad_decoded_run (F : FieldEncoding K) (xs tail : List Nat) {p : ParsedPair K}
    {B : Nat} {σ : Env} (hp : decodePair F xs = some p)
    (hInput : σ.inp = xs++tail) (hBase : σ.vars rawPairIO.base = 0)
    (hLength : σ.vars rawPairIO.limit = xs.length)
    (hArray : (σ.arrs rawPairIO.array).length = xs.length)
    (hSize : xs.length < B) (hWords : ∀ v ∈ xs, v < B) :
    ∃ τ, Run B rawPairLoad σ τ (20*(xs.length+1)) ∧
      τ.arrs rawPairIO.array = comparisonInput F p.source p.target ∧
      (∀ bank, bank ≠ rawPairIO.array → τ.arrs bank = σ.arrs bank) ∧
      (∀ r, r ≠ rawPairIO.index → r ≠ rawPairIO.value → τ.vars r = σ.vars r) ∧
      τ.inp = tail ∧ τ.out = σ.out := by
  rw [decodePair_reencode F xs hp]
  exact rawPairLoad_run xs tail hInput hBase hLength hArray hSize hWords

#print axioms decodePair_reencode
#print axioms pairValid_time
#print axioms rawPairLoad_decoded_run
end EvenTI.P12ComparePrep
