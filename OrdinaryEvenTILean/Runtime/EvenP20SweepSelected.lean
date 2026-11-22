import EvenP20SweepModes
import EvenP20RecoverModePorts

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace EvenTI.P20Sweep

open scoped Polynomial
open UniqueFactorizationMonoid
open EvenTI.Contract EvenTI.P17Recover EvenTI.P18Recover EvenTI.P19Recover EvenTI.P20Recover
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val)
open Mathproof.P15RecogIMPDot20261007 (qN)
open Mathproof.P15DecideIMPLayout20261007 (MatBlock)
open Mathproof.P15FactorIMP20261007 (rC)
open Mathproof.Problem17Primary46FactorCursor (cursor tableBase tableWidth)
open Mathproof.Problem17Primary48RawArchive (Output Retained)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

noncomputable def recoverSelectedMode (D : FieldEncoding K) (F : FieldPresentation K)
    (right : Bool) (O : Output) (addr : String) : Com :=
  .seq (initModeWithPrimaryPorts D F right O) (recoverArchiveFactors O addr)

/-- The caller's chart and archive bases and capacities at the mode handoff. -/
structure ModeSweepMetadata (F : FieldPresentation K) (n B : ℕ) (O : Output)
    (addr : String) (U : SweepLayout) (u : Env) : Prop where
  address : u.vars addr=U.D
  table : u.vars tableBase=U.D
  tableWidthEq : u.vars tableWidth=U.N+U.N
  residueWidth : u.vars rC=U.N+U.N
  fieldWorkspace : u.vars qN.WS=F.e+1
  regFit : ∀ r ∈ primaryPortNames, u.vars r < B
  charts : ChartLayoutRegisters u n U.AB U.OB U.QR U.QA U.QO U.QL U.QW U.QY U.Z U.QD
  bank : DurableBank u n U.OB U.QD U.offset U.base U.lane
  words : F.e*(U.N*(U.N+U.N))≤(u.arrs O.words).length
  wordsFit : (u.arrs O.words).length < B
  widths : U.offset+U.N≤(u.arrs savedWidths).length

/-- Join the real selected-mode initializer to the real factor sweep. The
archive order and number of factors are obtained from the live initializer;
only the unchanging caller metadata is supplied at the handoff. -/
theorem recoverSelectedMode_run (D : FieldEncoding K) (F : FieldPresentation K)
    {B n C : ℕ} (right : Bool) (O : Output) (addr : String)
    (A : Matrix (Fin n) (Fin n) K) (U : SweepLayout) {s u : Env}
    (init : Run B (initModeWithPrimaryPorts D F right O) s u C)
    (archive : Retained F U.N O A.charpoly u)
    (slots : Slots F canonical qN.WS U.Sn B u)
    (ports : PrimaryPorts u n n U.SB U.TB U.RB U.PB U.AM U.OB U.Z)
    (anchor : MatBlock F u U.AB A) (powers : ∀ j ≤ n, MatBlock F u (U.SB+j*(n*n)) (A^j))
    (zero : val F canonical qN.WS u U.Z=0) (one : val F canonical qN.WS u (U.Z+1)=1)
    (metadata : ModeSweepMetadata F n B O addr U u) (prior : DurablePrefix F U s u)
    (names : SweepNames O addr) (bounds : ∀ m ≤ U.N, SweepBounds F n m B U) :
    ∃ (t : Env) (L : List (Polynomial K)), L.length ≤ U.N ∧
      (L : Multiset (Polynomial K))=(normalizedFactors A.charpoly).dedup ∧
      Run B (recoverSelectedMode D F right O addr) s t (C+((maxModeRowTime F U.N n+8)*U.N+6)) ∧
      PreparedMode F A L O addr U B t ∧ t.vars cursor=L.length ∧ DurablePrefix F U s t ∧
      ∀ i < L.length, SavedChart F A (factorAt A L i) (U.offset+i)
        (rowBasis U.base U.lane (U.offset+i)) (rowChart U.base U.lane (U.offset+i)) t := by
  obtain ⟨L,hL,hCount,hArc⟩ := archive
  have hWidths := (Nat.add_le_add_left hL U.offset).trans metadata.widths
  have ready : PreparedMode F A L O addr U B u :=
    ⟨hArc,hCount,metadata.address,metadata.table,metadata.tableWidthEq,
      metadata.residueWidth,metadata.fieldWorkspace,slots,ports,metadata.regFit,
      anchor,powers,metadata.charts,metadata.bank,zero,one,metadata.words,
      metadata.wordsFit,hWidths⟩
  obtain ⟨t,r,rt,hCursor,hPrefix,hRows⟩ := recoverPreparedMode_run F names (bounds L.length hL) ready
  have paid : Run B (recoverSelectedMode D F right O addr) s t _ :=
    init.seq (r.mono (Nat.add_le_add_right (Nat.mul_le_mul_left _ hL) 6))
  exact ⟨t,L,hL,hArc.list,paid,rt,hCursor,prior.trans F hPrefix,hRows⟩

#print axioms recoverSelectedMode_run
end EvenTI.P20Sweep



