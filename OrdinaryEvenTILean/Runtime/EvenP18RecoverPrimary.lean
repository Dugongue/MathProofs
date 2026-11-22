import Primary48Install

/-! Install an actual selected-anchor factor archive and compute the primary
kernel for the factor selected by the caller's live cursor. -/
namespace EvenTI.P18Recover

open scoped Polynomial
open Polynomial UniqueFactorizationMonoid
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical scalarWrites arrayWrites)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val)
open Mathproof.P15RecogIMPDot20261007 (qN dL dZ dT dU)
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

set_option autoImplicit false
set_option maxHeartbeats 4500000
set_option maxRecDepth 23000

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

noncomputable def archivedPrimary (O : Output) (address : String) : Com :=
  .seq (Mathproof.Problem17Primary48Install.program O address)
    (.seq (load O.mult) Mathproof.Problem17Primary46Kernel.program)

/-- Register controls for the powered annihilator and its kernel, apart from
the three controls read from the factor row itself. -/
structure PrimaryPorts (σ : Env) (n d SB TB RB PB AM OB Z : ℕ) : Prop where
  dot : σ.vars dL = d+1
  rows : σ.vars gRows = n
  cols : σ.vars gCols = n
  output : σ.vars gOut = PB
  size : σ.vars mpN = n
  sizeSq : σ.vars mpNN = n*n
  powers : σ.vars afSB = SB
  query : σ.vars mpP = PB
  powered : σ.vars mpR = RB
  work : σ.vars mpT = TB
  kerRows : σ.vars tNR = n
  kerCols : σ.vars tD = n
  kerInput : σ.vars tRB = RB
  kerWork : σ.vars kAM = AM
  kerOutput : σ.vars kOUT = OB
  zero : σ.vars dZ = Z
  one : σ.vars rOs = Z+1
  temp1 : σ.vars dT = Z+2
  temp2 : σ.vars dU = Z+3

private theorem archivedRow_bounds {n : ℕ} (A : Matrix (Fin n) (Fin n) K) {p : K[X]} (hp : p ∈ normalizedFactors A.charpoly) :
    p.natDegree ≤ n ∧ (normalizedFactors A.charpoly).count p ≤ n := by
  have h₁ := natDegree_le_of_dvd (dvd_of_mem_normalizedFactors hp) A.charpoly_monic.ne_zero
  have h₂ := Problem17Factor46.count_le_degree
    (Mathproof.P15FactorIMP20261007.nf_monic hp) (irreducible_of_normalized_factor p hp)
    A.charpoly_monic.ne_zero
  simpa using And.intro h₁ h₂

/-- The literal factor archive can be in any order. The program computes the
primary basis for the row it actually reads, including repeated factors. -/
theorem archivedPrimary_run (F : FieldPresentation K) (O : Output) (address : String)
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
      j.val = i ∧ (L : Multiset K[X]) = (normalizedFactors S.charpoly).dedup ∧
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
      Frame (archivedPrimary O address) σ τ := by
  have hWord : Sn+10 < B := by have := G.words; omega
  obtain ⟨u,L,rI,sI,hLen,hCount,hBank,memI,frI⟩ :=
    Mathproof.Problem17Primary48Install.run F O address distinct hAddr hFresh hWidth hS hA
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
  obtain ⟨τ,rK,sK,dim,basis,mat,_,_,_,_⟩ := Mathproof.Problem17Primary46Kernel.run
    F G cm S L[i] hDegree hMultWord sL (fun t ht => coeffRow t (ht.trans_le G.cap)) hpv hZv hOv
  have run : Run B (archivedPrimary O address) σ τ _ := rI.seq (rL.seq rK)
  exact ⟨τ,L,⟨i,hii⟩,rfl,hBank.list,run,sK,dim,basis,mat,Frame.of_run run⟩

#print axioms archivedPrimary_run
end EvenTI.P18Recover

