import EvenP20SweepCell
import EvenP20RecoverOrderedCall
import EvenP18RecoverOrder

set_option autoImplicit false
set_option maxRecDepth 150000
set_option maxHeartbeats 7500000

namespace EvenTI.P20Sweep

open scoped Polynomial
open Polynomial UniqueFactorizationMonoid
open EvenTI.P18Recover EvenTI.P19Recover EvenTI.P20Recover
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical scalarWrites arrayWrites)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val val_setVar)
open Mathproof.P15RecogIMPDot20261007 (qN dZ dT dU)
open Mathproof.P15RecogIMPProgram20261007 (rOs)
open Mathproof.P15DecideIMPLayout20261007 (MatBlock)
open Mathproof.P15DecideIMPKerBasis20261007 (XBs)
open Mathproof.P15FactorIMP20261007 (rC)
open Mathproof.Problem17Primary46FactorCursor (cursor tableBase tableWidth)
open Mathproof.Problem17Primary46Kernel (Geometry)
open Mathproof.Problem17Primary47ExternalArchive (Archived)
open Mathproof.Problem17Primary48RawArchive (Output Distinct Retained)
open Mathproof.Problem17Primary46Reload (key)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

structure SweepLayout where
  N : ℕ
  D : ℕ
  SB : ℕ
  TB : ℕ
  RB : ℕ
  PB : ℕ
  AM : ℕ
  OB : ℕ
  Z : ℕ
  Sn : ℕ
  AB : ℕ
  QR : ℕ
  QA : ℕ
  QO : ℕ
  QL : ℕ
  QW : ℕ
  QY : ℕ
  QD : ℕ
  offset : ℕ
  base : ℕ
  lane : ℕ

structure PreparedMode {n : ℕ} (F : FieldPresentation K) (A : Matrix (Fin n) (Fin n) K)
    (L : List K[X]) (O : Output) (address : String) (U : SweepLayout) (B : ℕ) (s : Env) : Prop where
  installed : Archived F O.words O.mult (U.N+U.N) A.charpoly L s
  count : s.vars O.size=L.length
  address : s.vars address=U.D
  table : s.vars tableBase=U.D
  tableW : s.vars tableWidth=U.N+U.N
  residueW : s.vars rC=U.N+U.N
  ws : s.vars qN.WS=F.e+1
  slots : Slots F canonical qN.WS U.Sn B s
  ports : PrimaryPorts s n n U.SB U.TB U.RB U.PB U.AM U.OB U.Z
  regFit : ∀ r ∈ primaryPortNames, s.vars r < B
  anchor : MatBlock F s U.AB A
  powers : ∀ j ≤ n, MatBlock F s (U.SB+j*(n*n)) (A^j)
  layout : ChartLayoutRegisters s n U.AB U.OB U.QR U.QA U.QO U.QL U.QW U.QY U.Z U.QD
  bank : DurableBank s n U.OB U.QD U.offset U.base U.lane
  zero : val F canonical qN.WS s U.Z=0
  one : val F canonical qN.WS s (U.Z+1)=1
  words : F.e*(U.N*(U.N+U.N))≤(s.arrs O.words).length
  wordsFit : (s.arrs O.words).length < B
  widthFit : U.offset+L.length≤(s.arrs savedWidths).length

structure SweepBounds (F : FieldPresentation K) (n m B : ℕ) (U : SweepLayout) : Prop where
  cap : m ≤ U.N
  nonzero : 0 < U.N
  coefficients : n < U.N+U.N
  length : m < B
  ambientB : n < B
  rowB : U.offset+m < B
  strideB : 2*U.lane < B
  matrixLane : n*n ≤ U.lane
  workspace : U.Sn+10 < B
  constants : U.Z+4 ≤ U.Sn
  chartLow : U.base ≤ U.Z
  arena : rowBasis U.base U.lane (U.offset+m) ≤ U.Z
  anchorTop : U.AB+n*n ≤ U.D
  powersTop : U.SB+(n+1)*(n*n) ≤ U.D
  inputLow : ∀ w ≤ n, (n+1)*XBs n n ≤ U.AB ∧ (n+1)*XBs n n ≤ U.SB ∧
    (w+1+1)*XBs n (w+1) ≤ U.AB ∧ (w+1+1)*XBs n (w+1) ≤ U.SB
  tableTop : U.D+U.N*(U.N+U.N) ≤ U.base
  inputFirst : U.D ≤ U.TB ∧ U.D ≤ U.QR ∧ U.D ≤ U.OB ∧ U.D ≤ U.QD
  outputs : U.OB+n*n+n ≤ U.base ∧ U.QD+n*n ≤ U.base ∧ U.QY+n ≤ U.base
  geom : ∀ i < m, Geometry n n (U.N+U.N) U.SB (U.D+i*(U.N+U.N)) U.TB U.RB U.PB U.AM U.OB U.Z U.Sn B
  chart : ∀ w ≤ n, ChartBankLayout w n U.AB U.OB U.QR U.QA U.QO U.QL U.QW U.QY U.Z U.QD U.Sn B
  layoutFit : ∀ p ∈ chartLayoutEntries n U.AB U.OB U.QR U.QA U.QO U.QL U.QW U.QY U.Z U.QD, p.2 < B


structure SweepNames (O : Output) (address : String) : Prop where
  distinct : Distinct O
  cursorFresh : cursor≠O.size
  addressFresh : address ≠ Mathproof.Problem17Primary48Install.cnt ∧
    address ≠ Mathproof.Problem17Primary48Install.src
  sizeArchive : O.size ∉ scalarWrites (archivedFactorChart O address)
  addressArchive : address ∉ scalarWrites (archivedFactorChart O address)
  sizeStore : O.size ∉ scalarWrites framedStoreChartRow
  addressStore : address ∉ scalarWrites framedStoreChartRow
  addressCursor : address≠cursor
  wordsStore : O.words ∉ arrayWrites framedStoreChartRow
  multStore : O.mult ∉ arrayWrites framedStoreChartRow

noncomputable def factorAt {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (L : List K[X]) (i : ℕ) : K[X] :=
  let f := L[i]?.getD 1
  f ^ (normalizedFactors A.charpoly).count f

noncomputable def archiveTime (F : FieldPresentation K) (N n m w : ℕ) : ℕ :=
  39+(((Mathproof.Problem17Primary48Install.cost F N +
    (12+Mathproof.Problem17Primary46Kernel.cost F n n m))+
    (33+(8+chartBankCost F w n)))+39)

noncomputable def durableTime (F : FieldPresentation K) (N n e w : ℕ) : ℕ :=
  archiveTime F N n e w+(39+((16+publishChartCost F w n)+39))

noncomputable def maxModeRowTime (F : FieldPresentation K) (N n : ℕ) : ℕ :=
  (Finset.range (n+1)).sup fun e => (Finset.range (n+1)).sup fun w => durableTime F N n e w

private theorem durableTime_le_max (F : FieldPresentation K) {N n e w : ℕ}
    (he : e ≤ n) (hw : w ≤ n) : durableTime F N n e w ≤ maxModeRowTime F N n := by
  apply le_trans (Finset.le_sup (f := fun u => durableTime F N n e u) (Finset.mem_range.mpr (by omega : w < n+1)))
  exact Finset.le_sup (s := Finset.range (n+1))
    (f := fun a => (Finset.range (n+1)).sup (fun b => durableTime F N n a b))
    (Finset.mem_range.mpr (by omega : e < n+1))

private theorem auxiliaryNoWrite : ∀ r ∈ [tableBase,tableWidth,rC,qN.WS,
    savedAmbientSize,savedBasisSource,savedChartSource,savedOffset,savedBank,savedLane,savedStride],
    r ∉ scalarWrites framedStoreChartRow := by decide

private theorem chartKeyNoWrite : ∀ r ∈ chartLayoutNames,
    key chartLayoutTag r ∉ scalarWrites framedStoreChartRow := by decide

private theorem primaryKeyNotCursor : ∀ r ∈ primaryPortNames, r≠cursor := by decide

private theorem auxNotCursor : ∀ r ∈ [tableBase,tableWidth,rC,qN.WS,
    savedAmbientSize,savedBasisSource,savedChartSource,savedOffset,savedBank,savedLane,savedStride],
    r≠cursor := by decide

private theorem chartKeyNotCursor : ∀ r ∈ chartLayoutNames, key chartLayoutTag r≠cursor := by decide

/-- A factor iteration changes its cursor without corrupting the installed mode. -/
theorem preparedMode_setCursor (F : FieldPresentation K) {n B : ℕ} {A : Matrix (Fin n) (Fin n) K}
    {L : List K[X]} {O : Output} {address : String} {U : SweepLayout} {s : Env}
    (names : SweepNames O address) (h : PreparedMode F A L O address U B s) (i : ℕ) :
    PreparedMode F A L O address U B (s.setVar cursor i) := by
  let t := s.setVar cursor i
  have kept (r : String) (hr : r≠cursor) : t.vars r=s.vars r := by simp [t,vars_setVar,hr]
  have v (k : ℕ) : val F canonical qN.WS t k=val F canonical qN.WS s k :=
    val_setVar F canonical (by decide) s i k
  have archive : Archived F O.words O.mult (U.N+U.N) A.charpoly L t := by
    obtain ⟨vv,hv,hc⟩ := h.installed.data
    exact ⟨h.installed.list,⟨vv,fun a ha b => hv a ha b,hc⟩,h.installed.multLen,h.installed.multiplicity⟩

  refine ⟨archive,(kept _ names.cursorFresh.symm).trans h.count,(kept _ names.addressCursor).trans h.address,
    (kept _ (by decide)).trans h.table,(kept _ (by decide)).trans h.tableW,
    (kept _ (by decide)).trans h.residueW,(kept _ (by decide)).trans h.ws,
    Slots.setVar F canonical h.slots (by decide) (by decide) _,
    primaryPorts_of_eq h.ports (fun r hr => kept r (primaryKeyNotCursor r hr)),
    fun r hr => by rw [kept _ (primaryKeyNotCursor r hr)]; exact h.regFit _ hr,
    fun a b => (v _).trans (h.anchor a b),fun j hj a b => (v _).trans (h.powers j hj a b),?_,?_ ,
    (v _).trans h.zero,(v _).trans h.one,h.words,h.wordsFit,h.widthFit⟩
  · intro p hp
    have hm : p.1 ∈ chartLayoutNames := by
      rw [← chartLayoutEntries_names n U.AB U.OB U.QR U.QA U.QO U.QL U.QW U.QY U.Z U.QD]
      exact List.mem_map_of_mem hp
    exact (kept _ (chartKeyNotCursor _ hm)).trans (h.layout _ hp)
  · exact ⟨(kept _ (by decide)).trans h.bank.ambient,(kept _ (by decide)).trans h.bank.basisSource,
      (kept _ (by decide)).trans h.bank.chartSource,(kept _ (by decide)).trans h.bank.offsetReg,
      (kept _ (by decide)).trans h.bank.bankReg,(kept _ (by decide)).trans h.bank.laneReg,
      (kept _ (by decide)).trans h.bank.strideReg⟩

private theorem primaryPoints {s t : Env} {n d SB TB RB PB AM OB Z : ℕ}
    (h : PrimaryPorts s n d SB TB RB PB AM OB Z)
    (g : PrimaryPorts t n d SB TB RB PB AM OB Z) :
    ∀ r ∈ primaryPortNames, t.vars r=s.vars r := by
  intro r hr
  simp only [primaryPortNames,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact g.dot.trans h.dot.symm
  · exact g.rows.trans h.rows.symm
  · exact g.cols.trans h.cols.symm
  · exact g.output.trans h.output.symm
  · exact g.size.trans h.size.symm
  · exact g.sizeSq.trans h.sizeSq.symm
  · exact g.powers.trans h.powers.symm
  · exact g.query.trans h.query.symm
  · exact g.powered.trans h.powered.symm
  · exact g.work.trans h.work.symm
  · exact g.kerRows.trans h.kerRows.symm
  · exact g.kerCols.trans h.kerCols.symm
  · exact g.kerInput.trans h.kerInput.symm
  · exact g.kerWork.trans h.kerWork.symm
  · exact g.kerOutput.trans h.kerOutput.symm
  · exact g.zero.trans h.zero.symm
  · exact g.one.trans h.one.symm
  · exact g.temp1.trans h.temp1.symm
  · exact g.temp2.trans h.temp2.symm

/-- Run and publish one native factor and preserve the mode and earlier rows. -/
theorem recoverPreparedRow_run (F : FieldPresentation K) {n B : ℕ}
    {A : Matrix (Fin n) (Fin n) K} {L : List K[X]} {O : Output} {address : String}
    {U : SweepLayout} {s : Env} {i : ℕ} (name : SweepNames O address)
    (C : SweepBounds F n L.length B U) (h : PreparedMode F A L O address U B s)
    (hi : i < L.length) (ic : s.vars cursor=i) :
    ∃ t, Run B (recoverArchiveRow O address) s t (maxModeRowTime F U.N n) ∧
      PreparedMode F A L O address U B t ∧ t.vars cursor=i ∧ t.vars O.size=L.length ∧
      SavedChart F A (factorAt A L i) (U.offset+i) (rowBasis U.base U.lane (U.offset+i))
        (rowChart U.base U.lane (U.offset+i)) t ∧
      (∀ j < i, (t.arrs savedWidths)[U.offset+j]?=(s.arrs savedWidths)[U.offset+j]?) ∧
      (∀ j < i, ∀ k < n*n, val F canonical qN.WS t (rowBasis U.base U.lane (U.offset+j)+k)=
        val F canonical qN.WS s (rowBasis U.base U.lane (U.offset+j)+k)) ∧
      (∀ j < i, ∀ k < n*n, val F canonical qN.WS t (rowChart U.base U.lane (U.offset+j)+k)=
        val F canonical qN.WS s (rowChart U.base U.lane (U.offset+j)+k)) ∧
      (∀ k, U.base ≤ k → k < rowBasis U.base U.lane U.offset →
        val F canonical qN.WS t k=val F canonical qN.WS s k) ∧
      (∀ q < U.offset, (t.arrs savedWidths)[q]?=(s.arrs savedWidths)[q]?) := by
  let row := U.offset+i
  let X := rowBasis U.base U.lane row
  let R := rowChart U.base U.lane row
  have ar : Retained F U.N O A.charpoly s := ⟨L,C.cap,h.count,h.installed⟩
  have hg := C.geom i hi
  have boundTable := C.tableTop
  have boundArena := C.chartLow
  have hRZ : R+U.lane ≤ U.Z :=
    (rowChart_end_le_next _ _ (show U.offset+i < U.offset+L.length by omega)).trans C.arena
  have hRX : R=X+U.lane := rfl
  have hXZ : X ≤ U.Z := by omega
  have hBaseX : U.base ≤ X := Nat.le_add_right _ _
  have hConst := C.constants
  have hWord := C.workspace
  obtain ⟨u,M,j,w,xs,hj,hMl,hMa,hw,r,hu,hcu,hind,hspan,hbasis,hchart,hstable,keep,archiveFrame⟩ :=
    archivedFactorChartOrdered_run F O address A ar name.distinct h.address name.addressFresh
      name.sizeArchive name.addressArchive h.residueW h.slots C.nonzero (by omega)
      h.words h.wordsFit ic (by rwa [h.count]) h.table h.tableW h.ws hg h.ports
      h.regFit C.powersTop (by omega) h.powers h.zero h.one h.anchor
      (C.inputLow n le_rfl).1 C.anchorTop h.layout C.layoutFit C.chart
  have ord : M=L := retained_order_unique F ⟨hMl,hMa⟩ ⟨h.count,h.installed⟩ A.charpoly_monic.ne_zero
    (by simpa using C.coefficients)
  subst M
  have hget : L[i]?.getD 1=L.get j := by
    rw [← hj]
    simp [List.getElem?_eq_getElem j.isLt]
  have hsPow : Submodule.span K (Set.range xs)=LinearMap.ker (aeval A (factorAt A L i)).mulVecLin := by
    unfold factorAt
    rwa [hget]
  let e := (normalizedFactors A.charpoly).count (L.get j)
  have hMem : L.get j ∈ normalizedFactors A.charpoly := by
    have ht : L.get j ∈ (L : Multiset K[X]) := L.get_mem j
    rwa [h.installed.list,Multiset.mem_dedup] at ht
  have he : e ≤ n := by
    simpa [e] using
      Problem17Factor46.count_le_degree (Mathproof.P15FactorIMP20261007.nf_monic hMem)
        (irreducible_of_normalized_factor (L.get j) hMem) A.charpoly_monic.ne_zero
  have cports := hstable.ports
  have regU (r : String) (hr : r ∈ primaryPortNames) : u.vars r<B := by
    rw [primaryPoints h.ports cports r hr]
    exact h.regFit r hr
  obtain ⟨o1,o2,o3⟩ := C.outputs
  obtain ⟨lA,lS,lAw,lSw⟩ := C.inputLow w hw
  have fromWidth := Nat.mul_le_mul_right n hw
  have fromSquare := Nat.mul_le_mul hw hw
  have hanchorTop := C.anchorTop
  have hzMem (k : ℕ) (hk : k=U.Z ∨ k=U.Z+1) :
      val F canonical qN.WS u k=val F canonical qN.WS s k := by
    apply keep k (by omega) (Or.inr (by omega)) (by omega) (Or.inr (by omega))
      (by omega) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)) (by omega) (by omega)
  have hRowFit := C.rowB
  have hCountFit := C.length
  obtain ⟨t,rt,ht,hct,chart,after,other,hControls,storeFrame,fr⟩ :=
    recoverArchiveRow_commit F r hu h.bank regU (hstable.cursor.trans ic) hcu
      cports.zero cports.one cports.temp1 cports.temp2 hw hind hsPow hbasis hchart
      C.matrixLane C.ambientB (by omega) (by omega) C.strideB
      (by have := h.widthFit; omega) (by omega) o2 hRZ hConst hWord
      ((hzMem _ (Or.inl rfl)).trans h.zero) ((hzMem _ (Or.inr rfl)).trans h.one)
  have hrt : Run B (recoverArchiveRow O address) s t (maxModeRowTime F U.N n) :=
    rt.mono (durableTime_le_max F he hw)

  have kept (k : ℕ) (hk : k < U.Sn) (hc : k < X ∨ R+U.lane ≤ k)
      (hD : k < U.D ∨ U.D+U.N*(U.N+U.N) ≤ k)
      (hL : (n+1)*XBs n n ≤ k) (hM : k < U.TB ∨ U.OB+n*n ≤ k)
      (hLw : (w+1+1)*XBs n (w+1) ≤ k) (hSol : k < U.QR ∨ U.QY+w ≤ k)
      (hKer : k < U.OB+w*n ∨ U.OB+w*n+n ≤ k) (hC : k < U.QD ∨ U.QD+w*w ≤ k)
      (ht₂ : k≠U.Z+2) (ht₃ : k≠U.Z+3) :
      val F canonical qN.WS t k=val F canonical qN.WS s k := by
    change rowChart U.base U.lane (U.offset+i)+U.lane≤U.Z at hRZ
    exact (after k hk hc ht₂ ht₃).trans (keep k hk hD hL hM hLw hSol hKer hC ht₂ ht₃)
  have hInput : U.AB+n*n ≤ U.D := C.anchorTop
  have pInput := C.powersTop
  obtain ⟨hTB,hQR,hOB,hQD⟩ := C.inputFirst
  have preserveInput (k : ℕ) (hi : k < U.D) (hlo : (n+1)*XBs n n ≤ k)
      (hlw : (w+1+1)*XBs n (w+1) ≤ k) :
      val F canonical qN.WS t k=val F canonical qN.WS s k :=
    kept k (by omega) (Or.inl (by omega)) (Or.inl hi) hlo (Or.inl (by omega)) hlw
      (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (by omega) (by omega)
  have hModeAnchor : MatBlock F t U.AB A := by
    intro a b
    have idx := Mathproof.Problem18IMPMatrixMemory20261001.index_lt a b
    exact (preserveInput _ (by omega) (by omega) (by omega)).trans (h.anchor a b)
  have hModePowers (j : ℕ) (hj : j ≤ n) : MatBlock F t (U.SB+j*(n*n)) (A^j) := by
    intro a b
    have idx := Mathproof.Problem18IMPMatrixMemory20261001.index_lt a b
    have jmul := Nat.mul_le_mul_right (n*n) hj
    rw [Nat.add_mul,one_mul] at pInput
    exact (preserveInput _ (by omega) (by omega) (by omega)).trans (h.powers j hj a b)
  have hFinConst (k : ℕ) (hk : k=U.Z ∨ k=U.Z+1) :
      val F canonical qN.WS t k=val F canonical qN.WS s k := by
    change rowChart U.base U.lane (U.offset+i)+U.lane≤U.Z at hRZ
    exact (after k (by omega) (Or.inr (by omega)) (by omega) (by omega)).trans (hzMem k hk)
  have hWords : t.arrs O.words=s.arrs O.words := (storeFrame.arrs _ name.wordsStore).trans hstable.words
  have hMult : t.arrs O.mult=s.arrs O.mult := (storeFrame.arrs _ name.multStore).trans hstable.mult
  have hArchived : Archived F O.words O.mult (U.N+U.N) A.charpoly L t := by
    obtain ⟨vals,valsEq,coeff⟩ := h.installed.data
    refine ⟨h.installed.list,⟨vals,?_,coeff⟩,?_,?_⟩
    · intro a ha b
      have heq := valsEq a ha b
      rw [hWords]
      exact heq
    · rw [hMult]
      exact h.installed.multLen
    · intro j hj
      rw [hMult]
      exact h.installed.multiplicity j hj
  have hsKeep (r : String) (hr : r ∈ [tableBase,tableWidth,rC,qN.WS,
      savedAmbientSize,savedBasisSource,savedChartSource,savedOffset,savedBank,savedLane,savedStride]) :
      t.vars r=u.vars r := storeFrame.vars r (auxiliaryNoWrite r hr)
  have hRegArch (r : String) (hr : r ∈ [savedAmbientSize,savedBasisSource,savedChartSource,
      savedOffset,savedBank,savedLane,savedStride]) : u.vars r=s.vars r :=
    archiveFrame.vars r (by
      change r ∉ scalarWrites (archivedFactorChart ⟨"","",""⟩ "")
      exact chartSaveRegisters r hr)
  have installed : PreparedMode F A L O address U B t := by
    refine ⟨hArchived,?_,?_,(hsKeep _ (by decide)).trans hstable.tableBase,
      (hsKeep _ (by decide)).trans hstable.tableWidth,(hsKeep _ (by decide)).trans hstable.resWidth,
      (hsKeep _ (by decide)).trans hstable.workspace,ht,primaryPorts_of_eq cports hControls,
      ?_,hModeAnchor,hModePowers,?_,?_,(hFinConst _ (Or.inl rfl)).trans h.zero,
      (hFinConst _ (Or.inr rfl)).trans h.one,?_,?_,?_⟩
    · exact (storeFrame.vars _ name.sizeStore).trans (hstable.size.trans h.count)
    · exact (storeFrame.vars _ name.addressStore).trans (hstable.address.trans h.address)
    · intro r hr
      rw [hControls _ hr,primaryPoints h.ports cports r hr]
      exact h.regFit r hr
    · intro p hp
      have hm : p.1 ∈ chartLayoutNames := by
        rw [← chartLayoutEntries_names n U.AB U.OB U.QR U.QA U.QO U.QL U.QW U.QY U.Z U.QD]
        exact List.mem_map_of_mem hp
      exact (storeFrame.vars _ (chartKeyNoWrite _ hm)).trans (hstable.layout _ hp)
    · exact ⟨(hsKeep _ (by decide)).trans ((hRegArch _ (by decide)).trans h.bank.ambient),
        (hsKeep _ (by decide)).trans ((hRegArch _ (by decide)).trans h.bank.basisSource),
        (hsKeep _ (by decide)).trans ((hRegArch _ (by decide)).trans h.bank.chartSource),
        (hsKeep _ (by decide)).trans ((hRegArch _ (by decide)).trans h.bank.offsetReg),
        (hsKeep _ (by decide)).trans ((hRegArch _ (by decide)).trans h.bank.bankReg),
        (hsKeep _ (by decide)).trans ((hRegArch _ (by decide)).trans h.bank.laneReg),
        (hsKeep _ (by decide)).trans ((hRegArch _ (by decide)).trans h.bank.strideReg)⟩
    · rw [hWords]
      exact h.words
    · rw [hWords]
      exact h.wordsFit
    · rw [fr.len]
      exact h.widthFit
  have preserveDurable (k : ℕ) (hk : U.base ≤ k) (hpre : k < X) :
      val F canonical qN.WS t k=val F canonical qN.WS s k :=
    kept k (by omega) (Or.inl hpre) (Or.inr (by omega)) (by omega)
      (Or.inr (by omega)) (by omega) (Or.inr (by omega)) (Or.inr (by omega))
      (Or.inr (by omega)) (by omega) (by omega)
  refine ⟨t,hrt,installed,hct,installed.count,chart,?_,?_,?_,?_,?_⟩
  · intro j hj
    exact other _ (by omega)
  · intro j hj k hk
    have hprev := rowChart_end_le_next U.base U.lane (show U.offset+j < row by omega)
    let Y := rowBasis U.base U.lane (U.offset+j)
    change rowChart U.base U.lane (U.offset+j)+U.lane ≤ X at hprev
    have hChartEq : rowChart U.base U.lane (U.offset+j)=Y+U.lane := rfl
    have hBefore : Y+k < X := by have := C.matrixLane; omega
    have hAfter : U.base ≤ Y+k := (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)
    exact preserveDurable _ hAfter hBefore
  · intro j hj k hk
    let Y := rowChart U.base U.lane (U.offset+j)
    have hprev : Y+U.lane ≤ X := rowChart_end_le_next U.base U.lane (show U.offset+j < row by omega)
    have hBefore : Y+k < X := by have := C.matrixLane; omega
    have hAfter : U.base ≤ Y+k :=
      (Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))
    exact preserveDurable _ hAfter hBefore
  · intro k hk hpre
    have hm := Nat.mul_le_mul_right (2*U.lane) (Nat.le_add_right U.offset i)
    apply preserveDurable k hk
    change k < U.base+(U.offset+i)*(2*U.lane)
    unfold rowBasis at hpre
    omega
  · intro j hj
    exact other j (by omega)


def DurablePrefix (F : FieldPresentation K) (U : SweepLayout) (s t : Env) : Prop :=
  (∀ k, U.base ≤ k → k < rowBasis U.base U.lane U.offset →
    val F canonical qN.WS t k=val F canonical qN.WS s k) ∧
  (∀ q < U.offset, (t.arrs savedWidths)[q]?=(s.arrs savedWidths)[q]?)

theorem DurablePrefix.trans (F : FieldPresentation K) {U : SweepLayout} {s u t : Env}
    (a : DurablePrefix F U s u) (b : DurablePrefix F U u t) : DurablePrefix F U s t :=
  ⟨fun k h₁ h₂ => (b.1 k h₁ h₂).trans (a.1 k h₁ h₂),fun q h => (b.2 q h).trans (a.2 q h)⟩

theorem DurablePrefix.setVar (F : FieldPresentation K) {U : SweepLayout} {s t : Env} {r : String}
    (h : DurablePrefix F U s t) (hr : r≠qN.WS) (v : ℕ) : DurablePrefix F U s (t.setVar r v) :=
  ⟨fun k h₁ h₂ => (val_setVar F canonical hr t v k).trans (h.1 k h₁ h₂),h.2⟩

/-- Execute every factor in literal archive order and retain earlier modes. -/
theorem recoverPreparedMode_run (F : FieldPresentation K) {n B : ℕ}
    {A : Matrix (Fin n) (Fin n) K} {L : List K[X]} {O : Output} {address : String}
    {U : SweepLayout} {s : Env} (name : SweepNames O address)
    (C : SweepBounds F n L.length B U) (h : PreparedMode F A L O address U B s) :
    ∃ t, Run B (recoverArchiveFactors O address) s t ((maxModeRowTime F U.N n+8)*L.length+6) ∧
      PreparedMode F A L O address U B t ∧ t.vars cursor=L.length ∧ DurablePrefix F U s t ∧
      ∀ i < L.length, SavedChart F A (factorAt A L i) (U.offset+i)
        (rowBasis U.base U.lane (U.offset+i)) (rowChart U.base U.lane (U.offset+i)) t := by
  have f : DurablePrefix F U s s := ⟨fun _ _ _ => rfl,fun _ _ => rfl⟩
  let Ready : Env → Prop := fun u => PreparedMode F A L O address U B u ∧ DurablePrefix F U s u
  have hReady (u : Env) (i : ℕ) (hu : Ready u) : Ready (u.setVar cursor i) :=
    ⟨preparedMode_setCursor F name hu.1 i, hu.2.setVar F (by decide) i⟩
  obtain ⟨t,hr,hEnd,hC,hRows⟩ := recoverArchiveFactors_of_replayed_rows F O address
    name.cursorFresh A (factorAt A L) Ready h.count C.length ⟨h,f⟩ hReady (by
      intro i hi u hU hc _
      obtain ⟨v,r,hv,hCursor,hCount,hSaved,hw,hX,hR,hKeep,hW⟩ :=
        recoverPreparedRow_run F name C hU.1 hi hc
      exact ⟨v,r,⟨hv,hU.2.trans F ⟨hKeep,hW⟩⟩,hCursor,hCount,hSaved,hw,hX,hR⟩)
  exact ⟨t,hr,hEnd.1,hC,hEnd.2,hRows⟩

#print axioms recoverPreparedMode_run
end EvenTI.P20Sweep










