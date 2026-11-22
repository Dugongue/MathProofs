import EvenP20ScalarNativeSites
import Mathproof.Meta.Problem18P34AssemblyMatrixMemory20261003

set_option autoImplicit false
set_option maxHeartbeats 650000
set_option maxRecDepth 20000

namespace EvenTI.P20Scalar

open scoped Matrix BigOperators
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open EvenTI.P18Scalar (stencilSitesBank stencilChartBank)
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001
open Mathproof.Problem18IMPFieldPresentation20261001
open Mathproof.Problem18ClaudeIMPSlots20261001
open Mathproof.P15RecogIMPDot20261007 (qN)
open Mathproof.P15DecideIMPLayout20261007 (MatBlock)
open Mathproof.P15AlgebraFrames20261007 (IsFieldFrame)
open Mathproof.Problem17Step17Project (CornerField)
open Mathproof.Problem17CornerBasis (restrict)
open Mathproof.Problem17Gauge48 (RestrictSafe)
open Mathproof.Problem17Repeat46 (WordFrame)
open Mathproof.Problem17Active47 (ids)
open Mathproof.Problem17Resume51
open Problem17CellCRT46 (source4 sourceCount source3 firstArray labelsAndAnchorsCost)
open Problem17CellCRT51Action (sourceActionList)

noncomputable def contiguousNativeSites {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (F : FieldPresentation K) : Com := .seq (contiguousLabels F) installNativeSites

/-- Existing all-native-cell restriction/embedding execution followed by
literal site-bank installation. Every incidence label comes with its actual
field embedding; no anchor-primary-factor label is substituted for it. -/
theorem contiguousNativeSites_run {K A : Type} [Field K] [Fintype K] [DecidableEq K] [CommRing A] [Algebra K A]
    (F : FieldPresentation K) {B Sn N c a H TB Z PB O b : ℕ} {σ : Env}
    (degree : Fin 4 → ℕ) (raw : ℕ → ℕ) (hRaw : ∀ i < a, raw i < c)
    {G : (t : Fin 4) → Fin (degree t) → Type} [∀ t i, Field (G t i)]
    (S : Subalgebra K A) (φ : A →ₐ[K] Matrix (Fin N) (Fin N) K)
    (hφ : Function.Injective φ) (e : Fin c → A) (he : IsFieldFrame S e)
    (ρ : ∀ t : Fin 4, (∀ i, G t i) →+* S)
    (Gm : Geometry N c H TB Z PB O Sn B (sourceTotal degree) degree
      (actionModeBase degree b (N*N)) (orderedOffsets degree))
    (C : Controls N TB Z PB O a σ)
    (hS : Slots F canonical qN.WS Sn B σ) (hW : WordFrame B σ)
    (hZ : val F canonical qN.WS σ Z = 0) (hOne : val F canonical qN.WS σ (Z+1) = 1)
    (hProj : ∀ j : Fin c, MatBlock F σ (PB+j.val*(N*N)) (φ (e j)))
    (hBank : ∀ i : Fin (sourceTotal degree),
      MatBlock F σ (b+i.val*(N*N)) (φ ((sourceActionList degree G (fun t x => ρ t x) i : S).val)))
    (hBase : σ.vars descBase = b)
    (hDegree : ∀ i : Fin 4, (σ.arrs modeDegree)[i.val]? = some (degree i))
    (hIds : ∀ k < a, (σ.arrs ids)[k]? = some (raw k))
    (hOffsetCap : 4 ≤ (σ.arrs modeOffset).length) (hBaseCap : 4 ≤ (σ.arrs modeBase).length)
    (hInc : 6*a < B) (hLabelCount : sourceTotal degree+a < B)
    (hCap : 4*a ≤ (σ.arrs source4).length)
    (hTernaryCap : 6*a ≤ (σ.arrs source3).length)
    (hAnchorCap : sourceTotal degree+a ≤ (σ.arrs firstArray).length)
    (hSitesCap : 4*a ≤ (σ.arrs stencilSitesBank).length)
 :
    ∃ τ, Run B (contiguousNativeSites F) σ τ
        ((124+((4+((labelCost F N H+8)*(4*a)+6))+
          (2+labelsAndAnchorsCost a (sourceTotal degree))))+(80*a+14)) ∧
      Slots F canonical qN.WS Sn B τ ∧
      (∀ k (hk : k < 4*a),
        let t := side k
        let j : Fin c := ⟨raw (k/4),hRaw _ (by omega)⟩
        ∃ (i : Fin (degree t)) (emb : G t i →+* CornerField S φ hφ e he j),
          (∀ x, restrict S φ hφ e he j (ρ t) x = emb (x i)) ∧
          (τ.arrs stencilSitesBank).getD k 0=(sourceLabel degree ⟨t,i⟩).val) ∧
      (∀ j : Fin c, MatBlock F τ (PB+j.val*(N*N)) (φ (e j))) ∧
      (∀ i : Fin (sourceTotal degree),
        MatBlock F τ (b+i.val*(N*N))
          (φ ((sourceActionList degree G (fun t x => ρ t x) i : S).val))) ∧
      τ.arrs stencilChartBank=σ.arrs stencilChartBank ∧
      Frame (contiguousNativeSites F) σ τ := by
  obtain ⟨u,ru,su,wu,cu,hCnt,du,specu,memu,ternu,firstu,proju,banku,fu⟩ :=
    contiguous_labels_run F degree raw hRaw S φ hφ e he ρ Gm C hS hW hZ hOne
      hProj hBank hBase hDegree hIds hOffsetCap hBaseCap hInc hLabelCount
      hCap hTernaryCap hAnchorCap
  have hFour : 4 < B := by have := Gm.word; omega
  have hSize : 4*a < B := by omega
  have hWords : ∀ k < 4*a, (u.arrs source4).getD k 0 < B := by
    intro k hk
    obtain ⟨i,emb,hEmbedding,hLabel⟩ := specu k hk
    rw [hLabel]
    exact (sourceLabel degree ⟨side k,i⟩).isLt.trans Gm.labelWord
  obtain ⟨τ,rτ,sτ,hCopy,hTail,hOther,hLength,fτ,hInp,hOut⟩ :=
    installNativeSites_run F su cu.active hFour hSize
      (by rw [fu.len]; exact hCap) (by rw [fu.len]; exact hSitesCap) hWords
  have hVal (s : ℕ) : val F canonical qN.WS τ s=val F canonical qN.WS u s := by
    unfold val Mathproof.Problem18IMPFieldPresentation20261001.slice
    rw [hOther canonical.mem (by decide),fτ.vars qN.WS (by
      apply not_mem_scalarWrites
      rfl)]
  have runAll : Run B (contiguousNativeSites F) σ τ _ := ru.seq rτ
  refine ⟨τ,runAll,sτ,?_,?_,?_,?_,Frame.of_run runAll⟩
  · intro k hk
    obtain ⟨i,emb,hEmbedding,hLabel⟩ := specu k hk
    exact ⟨i,emb,hEmbedding,(hCopy k hk).trans hLabel⟩
  · intro j x y
    exact (hVal _).trans (proju j x y)
  · intro i x y
    exact (hVal _).trans (banku i x y)
  · exact (hOther _ (by decide)).trans (fu.arrs _ (by
      apply not_mem_arrayWrites
      rfl))

#print axioms contiguousNativeSites_run
end EvenTI.P20Scalar