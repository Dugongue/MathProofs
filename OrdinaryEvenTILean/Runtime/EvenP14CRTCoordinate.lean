import EvenP14CRTProbe
import EvenP12CompareLiveCRTFrame

set_option autoImplicit false
set_option maxHeartbeats 2200000

namespace EvenTI.P14Recovery

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.IMPAuto20261004
open Mathproof.Problem18IMPFieldLayout20261001 (arrayWrites scalarWrites)
open Mathproof.P15GSSSmithSetup20261007 (rowsR)
open Mathproof.P15GSSSmithBanks20261007 (inputColsR)
open Mathproof.P15GSSSmithMix20261007 (matrixR)
open Mathproof.P15GSSSmithCoefficients20261007 (modR)
open Mathproof.P15GSSSmithSweep20261007 (Canonical)
open Mathproof.P15GSSSmithArray20261007 (decode)
open EvenTI.P12Compare

def recoverStoredCoordinate : Com := .seq prepareSmithProbe smithRecoverAndCommit

/-- Read a fixed-height logical system from its preserving bank, place the
probe row, run the charged Smith and CRT calls, and write the selected
coordinate. The caller provides no diagonal form, row table, or probe row. -/
theorem recoverStoredCoordinate_run {M B m n : Nat} [NeZero M]
    (A : Matrix (Fin m) (Fin n) (ZMod M)) (b : Fin m → ZMod M) (i : Fin n) {s : Env}
    (hW : 4*M*M+4*M+10<B)
    (hSizes : (m+1)+n+(m+1)*n+(m+1)*(m+1)+4<B)
    (hRows : s.vars rowsR=m+1) (hCols : s.vars inputColsR=n)
    (hSlot : s.vars coordinateSlot=i.val) (hMod : s.vars modR=M)
    (hSource : (m+1)*n≤(s.arrs constraintMatrix).length)
    (hMatrix : (m+1)*n+(m+1)*(m+1)+n≤(s.arrs matrixR).length)
    (hc : Canonical M (s.arrs constraintMatrix)) (hm : Canonical M (s.arrs matrixR))
    (hA : ∀ r : Fin m, ∀ j : Fin n, decode M (s.arrs constraintMatrix) (r.val*n+j.val)=A r j)
    (hProbe : ∀ j : Fin n,(s.arrs constraintMatrix).getD (m*n+j.val) 0=0)
    (hB : s.arrs crtRhsBank = List.ofFn (fun j => (b j).val))
    (hC₁ : (s.arrs coefficientBank).length=m+1)
    (hC₂ : (s.arrs targetBank).length=m+1)
    (hC₃ : (s.arrs modulusBank).length=m+1)
    (hDest : i.val < (s.arrs coordinateBank).length) :
    ∃ t, Run B recoverStoredCoordinate s t
          (20*((m+1)*n)+30+smithRecoverAndCommitCost M m n) ∧
      Frame recoverStoredCoordinate s t ∧ Canonical M (t.arrs matrixR) ∧
      match recoverCoordinate A b i with
      | some v => t.vars crtActive=1 ∧ t.arrs coordinateBank=(s.arrs coordinateBank).set i.val v.val
      | none => t.vars crtActive=0 ∧ t.arrs coordinateBank=s.arrs coordinateBank := by
  obtain ⟨u,ru,huCanon,huMat,f⟩ := prepareSmithProbe_run A i (s:=s) (B:=B) (by omega) (by omega)
    hRows hCols hSlot hMod (by omega) (by omega) (by omega) hSource (by omega)
    hc hm hA hProbe
  have hf (k : String) (hk : k ≠ Mathproof.Problem18PairBoundaryCopy20261004.cntReg ∧ k ≠ Mathproof.Problem18PairBoundaryCopy20261004.idxReg ∧
      k ≠ Mathproof.Problem18PairBoundaryCopy20261004.sbReg ∧ k ≠ Mathproof.Problem18PairBoundaryCopy20261004.dbReg) : u.vars k = s.vars k := by
    apply f.vars
    rcases hk with ⟨h₁,h₂,h₃,h₄⟩
    simp [prepareSmithProbe,reloadSmithConstraints,storeProbe,
      Mathproof.Problem18PairBoundaryCopy20261004.copyBlock,
      Mathproof.Problem18PairBoundaryCopy20261004.segCopy,
      Mathproof.Problem18PairBoundaryCopy20261004.segBody,scalarWrites,h₁,h₂,h₃,h₄]
  have hArr (k : String) (hk : k ≠ matrixR) : u.arrs k = s.arrs k := by
    apply f.arrs
    simp [prepareSmithProbe,reloadSmithConstraints,storeProbe,
      Mathproof.Problem18PairBoundaryCopy20261004.copyBlock,
      Mathproof.Problem18PairBoundaryCopy20261004.segCopy,
      Mathproof.Problem18PairBoundaryCopy20261004.segBody,arrayWrites,hk]
  have huDest : u.arrs coordinateBank=s.arrs coordinateBank := hArr _ (by decide)
  have hUMatrix := (f.len matrixR).symm ▸ hMatrix
  have hUMod := (hf _ (by decide)).trans hMod
  have hURows := (hf _ (by decide)).trans hRows
  have hUCols := (hf _ (by decide)).trans hCols
  obtain ⟨t,rt,_,hout⟩ := smithRecoverAndCommit_run A b i hW hSizes
    hUMatrix huCanon hUMod hURows hUCols
    huMat ((hArr _ (by decide)).trans hB)
    (by rw [hArr _ (by decide)]; exact hC₁)
    (by rw [hArr _ (by decide)]; exact hC₂)
    (by rw [hArr _ (by decide)]; exact hC₃)
    ((hf _ (by decide)).trans hSlot) (by rwa [huDest])
  have htCan := (smithRecoverAndCommit_state A i hW hSizes hUMatrix huCanon hUMod hURows hUCols huMat rt).1
  refine ⟨t,ru.seq rt,Frame.of_run (ru.seq rt),htCan,?_⟩
  cases h : recoverCoordinate A b i <;> simpa only [h,huDest] using hout

#print axioms recoverStoredCoordinate_run
end EvenTI.P14Recovery
