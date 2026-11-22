import EvenP22ScalarScanSiteInput
import EvenP22ScalarScanRemap

set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 1000000

namespace EvenTI.P21ScalarScan

open EvenTI.P21Site EvenTI.P21Site.Mode
open EvenTI.P19Scalar.PrefixStencil
open EvenTI.P20Scalar (positiveSiteCount)
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18IMPFieldLayout20261001 (arrayWrites scalarWrites)

def mappedModeSites (widths mult : String) : Com := .seq (modeSites widths mult) remapSelectedSites

def mappedModeSitesCost (w : ℕ → ℕ) (blocks : ℕ) : ℕ :=
  modeSitesCost w blocks+13*rowPrefix w blocks+6

structure MappedModeSitesInput (widths mult : String) (W blocks off base S : ℕ)
    (w e : ℕ → ℕ) (raw mapped : List ℕ) (s : Env) : Prop where
  native : ModeSitesInput widths mult W blocks off base S w e raw s
  address : ∀ k < rowPrefix w blocks, raw.getD k 0 < (s.arrs siteReindexWords).length
  mapLength : (s.arrs siteReindexWords).length < W
  mapWords : ∀ v ∈ s.arrs siteReindexWords, v < W
  length : raw.length=mapped.length
  mappedPrefix : ∀ k < rowPrefix w blocks, mapped.getD k 0=(s.arrs siteReindexWords).getD (raw.getD k 0) 0
  mappedTail : ∀ k, rowPrefix w blocks ≤ k → mapped.getD k 0=raw.getD k 0

/-- Compute archive-order site words then change their addresses into the
already committed incidence order before choosing a scalar reference. -/
theorem mappedModeSites_run {W blocks off base S : ℕ} {s : Env}
    (widths mult : String) (w e : ℕ → ℕ) (raw mapped : List ℕ)
    (h : MappedModeSitesInput widths mult W blocks off base S w e raw mapped s) :
    ∃ t, Run W (mappedModeSites widths mult) s t (mappedModeSitesCost w blocks) ∧
      Frame (mappedModeSites widths mult) s t ∧ t.arrs stencilSitesBank=mapped ∧
      t.vars positiveSiteCount=rowPrefix w blocks ∧
      t.vars globalStart=base+rowPrefix (nativeCount w e) blocks := by
  obtain ⟨u,r₀,f₀,uSites,count,global⟩ := modeSitesInput_run widths mult w e raw h.native
  have uMap : u.arrs siteReindexWords=s.arrs siteReindexWords :=
    f₀.arrs _ (by change siteReindexWords ∉ arrayWrites (modeSites "" ""); decide)
  obtain ⟨t,r₁,f₁,seg⟩ := remapSelectedSites_run count h.native.rowWord
    (by rw [uSites]; exact h.native.siteFit) (by rw [uSites,uMap]; exact h.address)
    (by rw [uMap]; exact h.mapLength) (by rw [uMap]; exact h.mapWords)
  have hMap : t.arrs stencilSitesBank=mapped := by
    apply List.ext_getElem ((f₁.len stencilSitesBank).trans ((congrArg List.length uSites).trans h.length))
    intro k hk hk'
    rw [←List.getD_eq_getElem _ 0 hk,←List.getD_eq_getElem _ 0 hk']
    by_cases hSmall : k < rowPrefix w blocks
    · simpa only [Nat.zero_add,uSites,uMap,h.mappedPrefix k hSmall] using seg.inside k hSmall
    · have big : rowPrefix w blocks ≤ k := by omega
      have outside := seg.outside k (.inr (by simpa only [Nat.zero_add] using big))
      rw [uSites] at outside
      exact outside.trans (h.mappedTail k big).symm
  have rr : Run W (mappedModeSites widths mult) s t (mappedModeSitesCost w blocks) :=
    (r₀.seq r₁).mono (by unfold mappedModeSitesCost; omega)
  exact ⟨t,rr,Frame.of_run rr,hMap,(f₁.vars _ (by decide)).trans count,(f₁.vars _ (by decide)).trans global⟩

#print axioms mappedModeSites_run
end EvenTI.P21ScalarScan
