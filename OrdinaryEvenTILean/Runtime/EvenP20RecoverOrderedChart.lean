import EvenP19RecoverArchiveChart
import Mathproof.Meta.Problem18RecursiveSlotInstall20261002

/-! Install one archived factor table into the shared canonical slot layout. -/
namespace EvenTI.P20Recover
open scoped Polynomial
open Polynomial
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 Mathproof.Problem18ClaudeIMPSlots20261001
open Mathproof.Problem18IMPFieldPresentation20261001
open Mathproof.P15RecogIMPDot20261007 (qN)
open Mathproof.P15DecideIMPEGens20261007 (ev_var ev_mul)
open Mathproof.P15FactorIMP20261007 (rC)
open Mathproof.Problem18PairLargeBank20261004 (Vals)
open Mathproof.Problem17Primary46FactorCursor (Bank)
open Mathproof.Problem17Primary48RawArchive (Output Distinct Retained)
open Mathproof.Problem17Primary47ExternalArchive (Archived)
open Mathproof.Problem17Primary48Install (cnt src dst idx)

set_option autoImplicit false
set_option maxHeartbeats 5500000
set_option maxRecDepth 30000
set_option backward.isDefEq.respectTransparency false

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

theorem installArchiveWitness_run (F : FieldPresentation K) {B Sn N D : ℕ} {σ : Env} {f : K[X]}
    (O : Output) (address : String) (d : Distinct O)
    (hAddr : σ.vars address=D) (hFresh : address ≠ cnt ∧ address ≠ src)
    (hWidth : σ.vars rC=N+N) (hS : Slots F canonical qN.WS Sn B σ)
    (h : Retained F N O f σ)
    (hSizeFresh : O.size ∉ scalarWrites (Mathproof.Problem17Primary48Install.program O address))
    (hN : 0 < N) (hFit : D+N*(N+N) ≤ Sn) (hWord : Sn+10 < B)
    (hCap : F.e*(N*(N+N)) ≤ (σ.arrs O.words).length)
    (hCapB : (σ.arrs O.words).length < B) :
    ∃ τ L, Run B (Mathproof.Problem17Primary48Install.program O address) σ τ (Mathproof.Problem17Primary48Install.cost F N) ∧
      Slots F canonical qN.WS Sn B τ ∧ L.length ≤ N ∧ τ.vars O.size=L.length ∧
      σ.vars O.size=L.length ∧ Archived F O.words O.mult (N+N) f L σ ∧ Bank F O.mult D (N+N) f L τ ∧
      (∀ s < Sn, (s < D ∨ D+N*(N+N) ≤ s) →
        val F canonical qN.WS τ s=val F canonical qN.WS σ s) ∧
      Frame (Mathproof.Problem17Primary48Install.program O address) σ τ := by
  obtain ⟨L,hLen,hCount,hArchive⟩ := h
  obtain ⟨v,hData,hCoeff⟩ := hArchive.data
  let W := L.length*(N+N)
  have hLe : W ≤ N*(N+N) := Nat.mul_le_mul_right (N+N) hLen
  have hW : D+W ≤ Sn := by omega
  have hAr : W*F.e ≤ (σ.arrs O.words).length := by
    rw [Nat.mul_comm W F.e]
    exact (Nat.mul_le_mul_left F.e hLe).trans hCap
  have hD : D < Sn := by have hh := Nat.mul_pos hN (show 0 < N+N by omega); omega
  have hSmall : L.length < B := hLen.trans_lt (by
    have hh := Nat.le_mul_of_pos_right N (show 0 < N+N by omega)
    omega)
  have hnB : N+N < B := by have hh := Nat.le_mul_of_pos_left (N+N) hN; omega
  have hWlt : W < B := by omega
  have hwlt : W*F.e < B := hAr.trans_lt hCapB
  let ρ := σ.setVar cnt (W*F.e)
  let η := ρ.setVar src 0
  let pre := η.setVar dst (η.vars qN.WS+D*F.e)
  have r₁ : Run B (.assign cnt (.mul (.mul (.var O.size) (.var rC)) (.var canonical.e))) σ ρ 6 :=
    Run.assign (ev_mul (ev_mul (ev_var hCount hSmall) (ev_var hWidth hnB) hWlt)
      (ev_var hS.base.degree (e_lt F canonical hS.base)) hwlt)
  have r₂ : Run B (.assign src (.lit 0)) ρ η 2 := Run.assign (evalB_lit (by omega))
  have s₁ := hS.setVar F canonical (by decide : cnt ∉ regNames canonical)
    (by decide : cnt ≠ qN.WS) (W*F.e)
  have s₂ := s₁.setVar F canonical (by decide : src ∉ regNames canonical)
    (by decide : src ≠ qN.WS) 0
  have hDst : η.vars address=D := by simp [η,ρ,vars_setVar,hFresh.1,hFresh.2,hAddr]
  have r₃ : Run B (.assign dst (addr canonical qN.WS (.var address))) η pre 6 :=
    Run.assign (evalB_addr F canonical s₂ (ev_var hDst (by omega)) hD)
  have s₃ := s₂.setVar F canonical (by decide : dst ∉ regNames canonical)
    (by decide : dst ≠ qN.WS) (η.vars qN.WS+D*F.e)
  have wPre : pre.vars qN.WS=σ.vars qN.WS := by
    simp [pre,η,ρ,vars_setVar,show qN.WS ≠ dst by decide,show qN.WS ≠ src by decide,show qN.WS ≠ cnt by decide]
  have hVal (j : ℕ) : val F canonical qN.WS pre j=val F canonical qN.WS σ j := by
    unfold val slice
    rw [wPre,show pre.arrs=σ.arrs from rfl]
  have canon (i : ℕ) (hi : i < W) :
      Canonical F (fun t => (pre.arrs O.words).getD (0+i*F.e+t.val) 0) := by
    intro t
    change (σ.arrs O.words).getD (0+i*F.e+t.val) 0 < F.p
    rw [Nat.mul_comm i F.e,hData i hi t]
    exact (F.coordinate (v i) t).isLt
  obtain ⟨τ,r₄,s₄,hCopy,mem,hArr,_,_,_⟩ :=
    Mathproof.Problem18RecursiveSlotInstall20261002.run F canonical qN.WS O.words idx cnt src dst
      Sn B D W 0 pre s₃ hW d.wordsMem (by decide) (by decide) (by decide) (by decide) (by decide)
      (by simp [pre,η,ρ,vars_setVar,show cnt ≠ dst by decide,show cnt ≠ src by decide])
      (by simp [pre,η,vars_setVar,show src ≠ dst by decide])
      (by simp [pre,vars_setVar,show qN.WS ≠ dst by decide])
      (by simpa [pre,η,ρ] using hAr) (by omega) canon
  have read (i : ℕ) (hi : i < W) : val F canonical qN.WS τ (D+i)=v i := by
    rw [hCopy i hi]
    have he : (fun t : Fin F.e => (pre.arrs O.words).getD (0+i*F.e+t.val) 0) =
        fun t : Fin F.e => (F.coordinate (v i) t).val := by
      funext t
      change (σ.arrs O.words).getD (0+i*F.e+t.val) 0 = _
      rw [Nat.mul_comm i F.e,hData i hi t]
    rw [he]
    exact decode_coordinates F (v i)
  have hMeta : τ.arrs O.mult=σ.arrs O.mult := hArr _ d.multMem
  have hcc := Nat.mul_le_mul_left 16 (Nat.mul_le_mul_right F.e hLe)
  have r : Run B (Mathproof.Problem17Primary48Install.program O address) σ τ (Mathproof.Problem17Primary48Install.cost F N) :=
    (r₁.seq (r₂.seq (r₃.seq r₄))).mono (by unfold Mathproof.Problem17Primary48Install.cost; omega)
  refine ⟨τ,L,r,s₄,hLen,((Frame.of_run r).vars _ hSizeFresh).trans hCount,hCount,hArchive,⟨hArchive.list,?_,by rw [hMeta]; exact hArchive.multLen,?_⟩,
    ?_,Frame.of_run r⟩
  · intro i hi j hj
    have hh := Nat.mul_le_mul_right (N+N) (Nat.succ_le_of_lt hi)
    rw [Nat.succ_mul] at hh
    simpa only [Nat.add_assoc] using (read (i*(N+N)+j) (by dsimp [W]; omega)).trans (hCoeff i hi j hj)
  · intro i hi; rw [hMeta]; exact hArchive.multiplicity i hi
  · intro i hi hb
    exact (mem i hi (hb.imp id (fun hz => by omega))).trans (hVal i)


#print axioms installArchiveWitness_run
end EvenTI.P20Recover

namespace EvenTI.P20Recover

open scoped Polynomial
open Polynomial UniqueFactorizationMonoid EvenTI.P18Recover EvenTI.P19Recover
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical scalarWrites arrayWrites)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val val_setVar)
open Mathproof.P15RecogIMPDot20261007 (qN dL dZ dT dU)
open Mathproof.P15DecideIMPEGens20261007 (ev_add ev_mul ev_var)
open Mathproof.P15DecideIMPSolve20261007 (svM svL svC)
open Mathproof.P15RecogIMPGrid20261007 (gRows gCols gOut)
open Mathproof.P15RecogIMPProgram20261007 (rOs)
open Mathproof.P15DecideIMPLayout20261007 (MatBlock)
open Mathproof.P15DecideIMPMatPow20261007 (mpN mpNN mpE mpP mpR mpT)
open Mathproof.P15DecideIMPRowKer20261007 (tNR tD tRB)
open Mathproof.P15DecideIMPKerBasis20261007 (kAM kOUT kK XBs)
open Mathproof.P15GBFPolynomialGrid20261007 (pePB peCap)
open Mathproof.P15GBFAffine20261007 (afSB)
open Mathproof.P15FactorIMP20261007 (rC)
open Mathproof.Problem17Primary46FactorCursor (cursor tableBase tableWidth load load_run)
open Mathproof.Problem17Primary46Kernel (Geometry Controls)
open Mathproof.Problem17Primary48RawArchive (Output Distinct Retained)
open Mathproof.Problem17Primary47ExternalArchive (Archived)

set_option autoImplicit false
set_option maxHeartbeats 4500000
set_option maxRecDepth 50000

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

private theorem archivedRow_bounds {n : ℕ} (A : Matrix (Fin n) (Fin n) K) {p : K[X]} (hp : p ∈ normalizedFactors A.charpoly) :
    p.natDegree ≤ n ∧ (normalizedFactors A.charpoly).count p ≤ n := by
  have h₁ := natDegree_le_of_dvd (dvd_of_mem_normalizedFactors hp) A.charpoly_monic.ne_zero
  have h₂ := Problem17Factor46.count_le_degree
    (Mathproof.P15FactorIMP20261007.nf_monic hp) (irreducible_of_normalized_factor p hp)
    A.charpoly_monic.ne_zero
  simpa using And.intro h₁ h₂

/-- The literal factor archive can be in any order. The program computes the
primary basis for the row it actually reads, including repeated factors. -/
theorem archivedPrimaryOrdered_run (F : FieldPresentation K) (O : Output) (address : String)
    {n N D SB TB RB PB AM OB Z Sn B i : ℕ} {σ : Env} (S : Matrix (Fin n) (Fin n) K)
    (hA : Retained F N O S.charpoly σ) (distinct : Distinct O)
    (hAddr : σ.vars address=D)
    (hFresh : address ≠ Mathproof.Problem17Primary48Install.cnt ∧
      address ≠ Mathproof.Problem17Primary48Install.src)
    (sizeFresh : O.size ∉ scalarWrites (Mathproof.Problem17Primary48Install.program O address))
    (hWidth : σ.vars rC=N+N) (hS : Slots F canonical qN.WS Sn B σ)
    (hn : 0 < N) (hFit : D+N*(N+N) ≤ Sn)
    (hCap : F.e*(N*(N+N)) ≤ (σ.arrs O.words).length)
    (hCapB : (σ.arrs O.words).length < B)
    (hCursor : σ.vars cursor=i) (hi : i < σ.vars O.size)
    (hBase : σ.vars tableBase=D) (hTableWidth : σ.vars tableWidth=N+N)
    (hWS : σ.vars qN.WS = F.e+1)
    (G : Geometry n n (N+N) SB (D+i*(N+N)) TB RB PB AM OB Z Sn B)
    (C : PrimaryPorts σ n n SB TB RB PB AM OB Z)
    (hPowersFirst : SB+(n+1)*(n*n) ≤ D) (hConstAfter : D+N*(N+N) ≤ Z)
    (hp : ∀ j ≤ n, MatBlock F σ (SB+j*(n*n)) (S^j))
    (hz : val F canonical qN.WS σ Z = 0) (ho : val F canonical qN.WS σ (Z+1) = 1) :
    ∃ (τ : Env) (L : List K[X]) (j : Fin L.length),
      j.val = i ∧ σ.vars O.size=L.length ∧ Archived F O.words O.mult (N+N) S.charpoly L σ ∧
      Run B (archivedPrimary O address) σ τ
        (Mathproof.Problem17Primary48Install.cost F N +
          (12 + Mathproof.Problem17Primary46Kernel.cost F n n
            ((normalizedFactors S.charpoly).count (L.get j)))) ∧
      Slots F canonical qN.WS Sn B τ ∧
      τ.vars kK = Module.finrank K
        (LinearMap.ker (aeval S ((L.get j) ^ (normalizedFactors S.charpoly).count (L.get j))).mulVecLin) ∧
      (∃ xs : Fin (τ.vars kK) → Fin n → K,
        (∀ a b, val F canonical qN.WS τ (OB+(a.val*n+b.val)) = xs a b) ∧
        LinearIndependent K xs ∧
        Submodule.span K (Set.range xs) =
          LinearMap.ker (aeval S ((L.get j) ^ (normalizedFactors S.charpoly).count (L.get j))).mulVecLin) ∧
      MatBlock F τ RB (aeval S ((L.get j) ^ (normalizedFactors S.charpoly).count (L.get j))) ∧
      (∀ k < Sn, (k < D ∨ D+N*(N+N) ≤ k) → (n+1)*XBs n n ≤ k →
        (k < TB ∨ OB+n*n ≤ k) → k ≠ Z+2 → k ≠ Z+3 →
        val F canonical qN.WS τ k=val F canonical qN.WS σ k) ∧
      Frame (archivedPrimary O address) σ τ := by
  have hWord : Sn+10 < B := by have := G.words; omega
  obtain ⟨u,L,rI,sI,hLen,hCount,hSize,hArchive,hBank,memI,frI⟩ :=
    installArchiveWitness_run F O address distinct hAddr hFresh hWidth hS hA
      sizeFresh hn hFit hWord hCap hCapB
  have hii : i < L.length := by simpa only [← hCount, frI.vars _ sizeFresh] using hi
  have hMem : L[i] ∈ normalizedFactors S.charpoly := by
    have hh : L[i] ∈ (L : Multiset K[X]) := List.getElem_mem _
    rwa [hBank.list, Multiset.mem_dedup] at hh
  obtain ⟨hDegree,hMult⟩ := archivedRow_bounds S hMem
  have hMultWord : (normalizedFactors S.charpoly).count L[i] + 2 < B := by
    have := G.words
    omega
  have hTableFit : D+L.length*(N+N) ≤ Sn :=
    (Nat.add_le_add_left (Nat.mul_le_mul_right (N+N) hLen) D).trans hFit
  have hIreg (x : String)
      (hh : x ∉ scalarWrites (Mathproof.Problem17Primary48Install.program ⟨"", "", ""⟩ "")) :
      u.vars x=σ.vars x := frI.vars _ (by
        change x ∉ scalarWrites (Mathproof.Problem17Primary48Install.program ⟨"", "", ""⟩ "")
        exact hh)
  obtain ⟨v,rL,sL,addrRow,capRow,expRow,coeffRow,frL⟩ :=
    load_run F hBank sI (by omega) hTableFit hWord
      ((hIreg _ (by decide)).trans hBase) ((hIreg _ (by decide)).trans hTableWidth)
      hii ((hIreg _ (by decide)).trans hCursor) hMultWord
  have vreg (x : String)
      (hI : x ∉ scalarWrites (Mathproof.Problem17Primary48Install.program ⟨"", "", ""⟩ ""))
      (hL : x ∉ scalarWrites (load "")) :
      v.vars x=σ.vars x := (frL.vars _ (by change x ∉ scalarWrites (load ""); exact hL)).trans (hIreg _ hI)
  have cm : Controls n n ((normalizedFactors S.charpoly).count L[i])
      (N+N) SB (D+i*(N+N)) TB RB PB AM OB Z F.e v :=
    ⟨(vreg _ (by decide) (by decide)).trans C.dot,
      (vreg _ (by decide) (by decide)).trans C.rows,
      (vreg _ (by decide) (by decide)).trans C.cols,
      (vreg _ (by decide) (by decide)).trans C.output,
      (vreg _ (by decide) (by decide)).trans C.size,
      (vreg _ (by decide) (by decide)).trans C.sizeSq,addrRow,capRow,
      (vreg _ (by decide) (by decide)).trans C.powers,expRow,
      (vreg _ (by decide) (by decide)).trans C.query,
      (vreg _ (by decide) (by decide)).trans C.powered,
      (vreg _ (by decide) (by decide)).trans C.work,
      (vreg _ (by decide) (by decide)).trans C.kerRows,
      (vreg _ (by decide) (by decide)).trans C.kerCols,
      (vreg _ (by decide) (by decide)).trans C.kerInput,
      (vreg _ (by decide) (by decide)).trans C.kerWork,
      (vreg _ (by decide) (by decide)).trans C.kerOutput,
      (vreg _ (by decide) (by decide)).trans C.zero,
      (vreg _ (by decide) (by decide)).trans C.one,
      (vreg _ (by decide) (by decide)).trans C.temp1,
      (vreg _ (by decide) (by decide)).trans C.temp2,
      (vreg _ (by decide) (by decide)).trans hWS⟩
  have loadMem (s : ℕ) : val F canonical qN.WS v s = val F canonical qN.WS u s := by
    unfold val Mathproof.Problem18IMPFieldPresentation20261001.slice
    rw [frL.vars _ (by change qN.WS ∉ scalarWrites (load ""); decide),
      frL.arrs _ (by change canonical.mem ∉ arrayWrites (load ""); decide)]
  have hpv (j : ℕ) (hj : j ≤ n) : MatBlock F v (SB+j*(n*n)) (S^j) := by
    intro a b
    have hab : a.val*n+b.val < n*n := calc
      _ < a.val*n+n := Nat.add_lt_add_left b.isLt _
      _ = (a.val+1)*n := by rw [Nat.add_mul,one_mul]
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt a.isLt)
    have hh : j*(n*n)+a.val*n+b.val < (n+1)*(n*n) := calc
      _ = j*(n*n)+(a.val*n+b.val) := Nat.add_assoc _ _ _
      _ < j*(n*n)+(n*n) := Nat.add_lt_add_left hab _
      _ = (j+1)*(n*n) := by rw [Nat.add_mul,one_mul]
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.succ_le_succ hj)
    rw [loadMem,memI _ (by omega) (Or.inl (by omega))]
    exact hp j hj a b
  have hZv : val F canonical qN.WS v Z=0 := by
    rw [loadMem,memI _ (by have := G.kernel.z_s; omega) (Or.inr hConstAfter),hz]
  have hOv : val F canonical qN.WS v (Z+1)=1 := by
    rw [loadMem,memI _ (by have := G.kernel.z_s; omega) (Or.inr (by omega)),ho]
  obtain ⟨τ,rK,sK,dim,basis,mat,memK,_,_,_⟩ := Mathproof.Problem17Primary46Kernel.run
    F G cm S L[i] hDegree hMultWord sL (fun t ht => coeffRow t (ht.trans_le G.cap)) hpv hZv hOv
  have run : Run B (archivedPrimary O address) σ τ _ := rI.seq (rL.seq rK)
  refine ⟨τ,L,⟨i,hii⟩,rfl,hSize,hArchive,run,sK,dim,basis,mat,?_,Frame.of_run run⟩
  intro k hk hTable hLo hArea h₁ h₂
  exact (memK k hk hLo hArea h₁ h₂).trans
    ((loadMem k).trans (memI k hk hTable))


#print axioms archivedPrimaryOrdered_run
end EvenTI.P20Recover

namespace EvenTI.P20Recover

open scoped BigOperators Polynomial Matrix
open Matrix Polynomial UniqueFactorizationMonoid EvenTI.P18Recover EvenTI.P19Recover
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical scalarWrites)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val)
open Mathproof.P15RecogIMPDot20261007 (qN)
open Mathproof.P15DecideIMPLayout20261007 (MatBlock)
open Mathproof.P15DecideIMPKerBasis20261007 (kK XBs)
open Mathproof.P15FactorIMP20261007 (rC)
open Mathproof.Problem17Primary46FactorCursor (cursor tableBase tableWidth)
open Mathproof.Problem17Primary46Kernel (Geometry)
open Mathproof.Problem17Primary48RawArchive (Output Distinct Retained)
open Mathproof.Problem17Primary47ExternalArchive (Archived)
open Mathproof.Problem17Primary46Reload (key)

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 120000

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

private theorem layout_key_fresh : ∀ r ∈ chartLayoutNames,
    key chartLayoutTag r ∉ scalarWrites (archivedPrimary ⟨"","",""⟩ "") := by decide

theorem archivedCompleteChartOrdered_run (F : FieldPresentation K) (O : Output) (address : String)
    {n N D SB TB RB PB AM OB Z Sn B i : ℕ} {σ : Env} (S : Matrix (Fin n) (Fin n) K)
    (hA : Retained F N O S.charpoly σ) (distinct : Distinct O)
    (hAddr : σ.vars address=D)
    (hFresh : address ≠ Mathproof.Problem17Primary48Install.cnt ∧
      address ≠ Mathproof.Problem17Primary48Install.src)
    (sizeFresh : O.size ∉ scalarWrites (Mathproof.Problem17Primary48Install.program O address))
    (hWidth : σ.vars rC=N+N) (hS : Slots F canonical qN.WS Sn B σ)
    (hn : 0 < N) (hFit : D+N*(N+N) ≤ Sn)
    (hCap : F.e*(N*(N+N)) ≤ (σ.arrs O.words).length) (hCapB : (σ.arrs O.words).length < B)
    (hCursor : σ.vars cursor=i) (hi : i < σ.vars O.size)
    (hBase : σ.vars tableBase=D) (hTableWidth : σ.vars tableWidth=N+N)
    (hWS : σ.vars qN.WS = F.e+1)
    (G : Geometry n n (N+N) SB (D+i*(N+N)) TB RB PB AM OB Z Sn B)
    (C : PrimaryPorts σ n n SB TB RB PB AM OB Z)
    (hPowersFirst : SB+(n+1)*(n*n) ≤ D) (hConstAfter : D+N*(N+N) ≤ Z)
    (hp : ∀ j ≤ n, MatBlock F σ (SB+j*(n*n)) (S^j))
    (hz : val F canonical qN.WS σ Z = 0) (ho : val F canonical qN.WS σ (Z+1) = 1)
    {AB QR QA QO QL QW QY QD : ℕ}
    (hMat : MatBlock F σ AB S) (hMatLow : (n+1)*XBs n n ≤ AB) (hMatHigh : AB+n*n≤D)
    (hLayout : ChartLayoutRegisters σ n AB OB QR QA QO QL QW QY Z QD)
    (hFitChart : ∀ p ∈ chartLayoutEntries n AB OB QR QA QO QL QW QY Z QD, p.2<B)
    (hForWidth : ∀ w ≤ n, ChartBankLayout w n AB OB QR QA QO QL QW QY Z QD Sn B) :
    ∃ (τ : Env) (L : List K[X]) (j : Fin L.length) (w : ℕ) (xs : Fin w → Fin n → K),
      j.val=i ∧ σ.vars O.size=L.length ∧
      Archived F O.words O.mult (N+N) S.charpoly L σ ∧ w≤n ∧
      Run B (archivedCompleteChart O address) σ τ
        ((Mathproof.Problem17Primary48Install.cost F N +
          (12+Mathproof.Problem17Primary46Kernel.cost F n n
             ((normalizedFactors S.charpoly).count (L.get j))))+
          (33+(8+chartBankCost F w n))) ∧
      Slots F canonical qN.WS Sn B τ ∧ τ.vars chartCursor=w ∧
      LinearIndependent K xs ∧
      Submodule.span K (Set.range xs) =
        LinearMap.ker (aeval S ((L.get j)^((normalizedFactors S.charpoly).count (L.get j)))).mulVecLin ∧
      (∀ (a : Fin w) (b : Fin n), val F canonical qN.WS τ (OB+(a.val*n+b.val))=xs a b) ∧
      ChartPrefix F τ QD w S xs ∧
      (∀ k < Sn, (k < D ∨ D+N*(N+N) ≤ k) → (n+1)*XBs n n ≤ k →
        (k < TB ∨ OB+n*n ≤ k) → (w+1+1)*XBs n (w+1) ≤ k →
        (k < QR ∨ QY+w ≤ k) → (k < OB+w*n ∨ OB+w*n+n ≤ k) →
        (k < QD ∨ QD+w*w ≤ k) → k ≠ Z+2 → k ≠ Z+3 →
        val F canonical qN.WS τ k=val F canonical qN.WS σ k) ∧
      Frame (archivedCompleteChart O address) σ τ := by
  obtain ⟨u,L,j,hj,hSize,hArchive,r₁,s₁,dim,basis,_,mem₁,fr₁⟩ := archivedPrimaryOrdered_run F O address S
    hA distinct hAddr hFresh sizeFresh hWidth hS hn hFit hCap hCapB hCursor hi hBase hTableWidth
    hWS G C hPowersFirst hConstAfter hp hz ho
  let w := u.vars kK
  obtain ⟨xs,xvals,xInd,xSpan⟩ := basis
  have hBound : w≤n := by
    have h := xInd.fintype_card_le_finrank
    simpa only [Fintype.card_fin,Module.finrank_fin_fun,w] using h
  have readLayout : ChartLayoutRegisters u n AB OB QR QA QO QL QW QY Z QD := by
    intro p hp
    have mem : p.1 ∈ chartLayoutNames := by
      rw [← chartLayoutEntries_names n AB OB QR QA QO QL QW QY Z QD]
      exact List.mem_map_of_mem hp
    rw [fr₁.vars _ (by
      change key chartLayoutTag p.1 ∉ scalarWrites (archivedPrimary ⟨"","",""⟩ "")
      exact layout_key_fresh _ mem)]
    exact hLayout _ hp
  have knowWS : u.vars qN.WS=F.e+1 := by
    rw [fr₁.vars _ (by change qN.WS ∉ scalarWrites (archivedPrimary ⟨"","",""⟩ ""); decide)]
    exact hWS
  have hZ := G.kernel.z_s
  have hOB := G.kernel.out_z
  have hTB := G.coefficients
  have holdAnchor : MatBlock F u AB S := by
    intro a b
    have hIdx := Mathproof.Problem18IMPMatrixMemory20261001.index_lt a b
    have hLow : (n+1)*XBs n n≤AB+(a.val*n+b.val) := by omega
    have hHigh : AB+(a.val*n+b.val)<D := by omega
    exact (mem₁ _ (by omega) (Or.inl hHigh) hLow (Or.inl (by omega))
      (by omega) (by omega)).trans (hMat a b)
  have holdConst (k : ℕ) (hk : k=Z ∨ k=Z+1) :
      val F canonical qN.WS u k=val F canonical qN.WS σ k :=
    mem₁ k (by omega) (Or.inr (by omega)) (by omega) (Or.inr (by omega)) (by omega) (by omega)
  let chartGeometry := hForWidth w hBound
  obtain ⟨τ,r₂,s₂,hCur,chart,mem₂,_⟩ := reloadKernelChart_run (w:=w) F S
    ((L.get j)^((normalizedFactors S.charpoly).count (L.get j))) xs xInd xSpan
    s₁ readLayout hFitChart chartGeometry (rfl : u.vars kK=w) knowWS holdAnchor xvals
    ((holdConst Z (Or.inl rfl)).trans hz) ((holdConst (Z+1) (Or.inr rfl)).trans ho)
  have chartLo := chartGeometry.anchorLow
  have chartAnchor := chartGeometry.anchorHigh
  have chartRB := chartGeometry.solve.columns
  have chartAM := chartGeometry.solve.transpose
  have chartOUT := chartGeometry.solve.kernel.am_out
  have chartLB := chartGeometry.solve.out
  have chartW := chartGeometry.solve.labels
  have chartY := chartGeometry.solve.work
  have chartDest := chartGeometry.outLow
  have chartEnd := chartGeometry.outHigh
  have chartKeep (a : Fin w) (b : Fin n) :
      val F canonical qN.WS τ (OB+(a.val*n+b.val))=xs a b := by
    have hIdx := Mathproof.Problem18IMPMatrixMemory20261001.index_lt a b
    rw [Nat.succ_mul] at chartRB
    exact (mem₂ _ (by omega) (by omega) (Or.inl (by omega)) (Or.inl (by omega))
      (Or.inl (by omega)) (by omega) (by omega)).trans (xvals a b)
  have run : Run B (archivedCompleteChart O address) σ τ _ := r₁.seq r₂
  refine ⟨τ,L,j,w,xs,hj,hSize,hArchive,hBound,run,s₂,hCur,xInd,xSpan,chartKeep,chart,?_,Frame.of_run run⟩
  intro k hk ht hl ha hc hs hg hd hz₁ hz₂
  exact (mem₂ k hk hc hs hg hd hz₁ hz₂).trans (mem₁ k hk ht hl ha hz₁ hz₂)
#print axioms archivedCompleteChartOrdered_run
end EvenTI.P20Recover

