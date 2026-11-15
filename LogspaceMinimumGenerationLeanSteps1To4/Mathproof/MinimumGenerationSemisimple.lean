import Mathlib.GroupTheory.Goursat
import Mathlib.GroupTheory.NoncommPiCoprod
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Group

/-!
# Algebraic certificates for the nonabelian semisimple lift

The component test reduces generation of a subgroup of a direct product of nonabelian simple
groups to its one- and two-coordinate projections.

The Schreier loops section adapts the orbit construction in the Apache-2.0
AxiomMath CFSG file CFSG.Certificates.SchreierStabilizerGenerators.
-/

namespace Mathproof.MinimumGenerationSemisimple

open Subgroup

section SimpleProduct

variable {S : Type*} [Group S]

private abbrev coordinate {n : ℕ} (i : Fin n) : S →* (Fin n → S) :=
  MonoidHom.mulSingle (fun _ : Fin n => S) i

private theorem coordinate_range_normal {n : ℕ} (i : Fin n) :
    (coordinate (S := S) i).range.Normal where
  conj_mem x hx y := by
    obtain ⟨a, rfl⟩ := hx
    refine ⟨y i * a * (y i)⁻¹, ?_⟩
    funext j
    by_cases hij : j = i
    · subst j
      simp [coordinate]
    · simp [coordinate, Pi.mulSingle_eq_of_ne hij]

private theorem range_eq_iSup_coordinate_ranges {n : ℕ} (f : (Fin n → S) →* S) :
    f.range = ⨆ i : Fin n, (f.comp (coordinate i)).range := by
  let h : Pairwise (fun (i j : Fin n) => ∀ a b : S,
      Commute (f.comp (coordinate i) a) (f.comp (coordinate j) b)) :=
    fun i j hij a b => by
      change Commute (f (Pi.mulSingle i a)) (f (Pi.mulSingle j b))
      exact (Pi.mulSingle_commute (f := fun _ : Fin n => S) hij a b).map f
  have he : f = MonoidHom.noncommPiCoprod (fun i => f.comp (coordinate i)) h := by
    apply MonoidHom.pi_ext
    intro i a
    simp [coordinate]
  rw [he, MonoidHom.noncommPiCoprod_range]
  congr 1
  funext i
  rw [← he]

/-- A surjective homomorphism from a finite power to its nonabelian simple factor
depends on just one input coordinate. -/
theorem factor_through_coordinate [IsSimpleGroup S] {n : ℕ} (f : (Fin n → S) →* S)
    (hf : Function.Surjective f) (hnc : ∃ a b : S, a * b ≠ b * a) :
    ∃ i : Fin n, ∀ x : Fin n → S, f x = f (coordinate i (x i)) := by
  classical
  have hnorm (i : Fin n) : ((f.comp (coordinate i)).range).Normal := by
    rw [MonoidHom.range_comp]
    exact (coordinate_range_normal (S := S) i).map f hf
  have hex : ∃ i : Fin n, (f.comp (coordinate i)).range = ⊤ := by
    by_contra! hn
    have hbot (i : Fin n) : (f.comp (coordinate i)).range = ⊥ :=
      (hnorm i).eq_bot_or_eq_top.resolve_right (hn i)
    have hr : f.range = ⊥ := by
      rw [range_eq_iSup_coordinate_ranges]
      simp [hbot]
    exact bot_ne_top (hr.symm.trans (MonoidHom.range_eq_top.mpr hf))
  obtain ⟨i, hi⟩ := hex
  have hother (j : Fin n) (hji : j ≠ i) :
      (f.comp (coordinate j)).range = ⊥ := by
    refine (hnorm j).eq_bot_or_eq_top.resolve_right ?_
    intro hj
    obtain ⟨a, b, hab⟩ := hnc
    obtain ⟨u, rfl⟩ := MonoidHom.range_eq_top.mp hi a
    obtain ⟨v, rfl⟩ := MonoidHom.range_eq_top.mp hj b
    apply hab
    change f (Pi.mulSingle i u) * f (Pi.mulSingle j v) =
      f (Pi.mulSingle j v) * f (Pi.mulSingle i u)
    exact ((Pi.mulSingle_commute (f := fun _ : Fin n => S) (Ne.symm hji) u v).map f).eq
  let g : (Fin n → S) →* S := (f.comp (coordinate i)).comp (Pi.evalMonoidHom (fun _ : Fin n => S) i)
  suffices f = g by
    exact ⟨i, fun x => DFunLike.congr_fun this x⟩
  apply MonoidHom.pi_ext
  intro j a
  by_cases hji : j = i
  · subst j
    simp [g, coordinate]
  · have hm : f.comp (coordinate j) a ∈ (f.comp (coordinate j)).range := ⟨a, rfl⟩
    rw [hother j hji, Subgroup.mem_bot] at hm
    simpa [g, coordinate, Pi.mulSingle_eq_of_ne (Ne.symm hji)] using hm

private def splitHead (n : ℕ) : (Fin (n + 1) → S) ≃* (Fin n → S) × S where
  toFun x := (Fin.tail x, x 0)
  invFun x := Fin.cons x.2 x.1
  left_inv x := Fin.cons_self_tail x
  right_inv x := by simp
  map_mul' x y := rfl

/-- Surjectivity of every individual and every pair projection forces the full finite product. -/
theorem eq_top_of_pair_surjective [IsSimpleGroup S] (hnc : ∃ a b : S, a * b ≠ b * a)
    {n : ℕ} (K : Subgroup (Fin n → S))
    (hone : ∀ i : Fin n, ∀ a : S, ∃ x ∈ K, x i = a)
    (hpair : ∀ i j : Fin n, i ≠ j → ∀ a b : S, ∃ x ∈ K, x i = a ∧ x j = b) :
    K = ⊤ := by
  induction n with
  | zero =>
    apply top_unique
    intro x _
    have hx : x = 1 := funext fun i => Fin.elim0 i
    rw [hx]
    exact K.one_mem
  | succ n ih =>
    let P := K.map (splitHead (S := S) n).toMonoidHom
    let tail : (Fin (n + 1) → S) →* (Fin n → S) :=
      (MonoidHom.fst _ _).comp (splitHead n).toMonoidHom
    have htail : K.map tail = ⊤ := by
      apply ih
      · intro i a
        obtain ⟨x, hx, hxi⟩ := hone i.succ a
        exact ⟨tail x, ⟨x, hx, rfl⟩, hxi⟩
      · intro i j hij a b
        obtain ⟨x, hx, hxi, hxj⟩ := hpair i.succ j.succ (fun h => hij (Fin.succ_inj.mp h)) a b
        exact ⟨tail x, ⟨x, hx, rfl⟩, hxi, hxj⟩
    have hfst : Function.Surjective (Prod.fst ∘ P.subtype) := by
      intro x
      obtain ⟨y, hy, hyx⟩ : x ∈ K.map tail := by rw [htail]; trivial
      exact ⟨⟨splitHead n y, ⟨y, hy, rfl⟩⟩, hyx⟩
    have hsnd : Function.Surjective (Prod.snd ∘ P.subtype) := by
      intro s
      obtain ⟨y, hy, hys⟩ := hone 0 s
      exact ⟨⟨splitHead n y, ⟨y, hy, rfl⟩⟩, hys⟩
    have hP : P = ⊤ := by
      rcases (Subgroup.normal_goursatSnd hsnd).eq_bot_or_eq_top with hbot | htop
      · have huniq : ∀ (u v : P), u.1.1 = v.1.1 → u.1.2 = v.1.2 := by
          intro u v h
          have hm : u.1.2 / v.1.2 ∈ P.goursatSnd := by
            apply Subgroup.mem_goursatSnd.mpr
            have hd := P.div_mem u.2 v.2
            change (u.1.1 / v.1.1, u.1.2 / v.1.2) ∈ P at hd
            rw [h, div_self'] at hd
            exact hd
          rw [hbot, Subgroup.mem_bot, div_eq_one] at hm
          exact hm
        obtain ⟨f, hf⟩ := MonoidHom.exists_range_eq_graph (f := P.subtype) hfst huniq
        have he : P = f.graph := (Subgroup.range_subtype P).symm.trans hf
        have hfs : Function.Surjective f := by
          intro s
          obtain ⟨⟨⟨u,v⟩, huv⟩, rfl⟩ := hsnd s
          exact ⟨u, MonoidHom.mem_graph.mp (he ▸ huv)⟩
        obtain ⟨i, hi⟩ := factor_through_coordinate f hfs hnc
        obtain ⟨s, hs⟩ := exists_ne (1 : S)
        obtain ⟨x, hx, hxi, hx0⟩ := hpair i.succ 0 (Fin.succ_ne_zero i) 1 s
        have hxp : splitHead n x ∈ f.graph := he ▸ (show splitHead n x ∈ P from ⟨x, hx, rfl⟩)
        have hfx : f (Fin.tail x) = x 0 := MonoidHom.mem_graph.mp hxp
        have hfi := hi (Fin.tail x)
        change f (Fin.tail x) = f (coordinate i (x i.succ)) at hfi
        rw [hxi, map_one, map_one, hfx, hx0] at hfi
        exact (hs hfi).elim
      · apply top_unique
        rintro ⟨x, y⟩ _
        obtain ⟨⟨⟨x', y'⟩, hy'⟩, hx⟩ := hfst x
        change x' = x at hx
        subst x'
        have ht : (1, y / y') ∈ P := by
          apply Subgroup.mem_goursatSnd.mp
          rw [htop]
          trivial
        simpa using P.mul_mem ht hy'
    apply top_unique
    intro x _
    have hm : splitHead n x ∈ P := by rw [hP]; trivial
    obtain ⟨y, hy, hyx⟩ := hm
    exact (splitHead n).injective hyx ▸ hy

end SimpleProduct


section TwoFactors

variable {G H : Type*} [Group G] [Group H]

private theorem eq_top_of_full_snd_kernel (K : Subgroup (G × H))
    (hfst : Function.Surjective (Prod.fst ∘ K.subtype)) (h : K.goursatSnd = ⊤) :
    K = ⊤ := by
  apply top_unique
  rintro ⟨a, b⟩ _
  obtain ⟨⟨⟨u, v⟩, hv⟩, hu⟩ := hfst a
  change u = a at hu
  subst u
  have ht : (1, b / v) ∈ K := by
    apply Subgroup.mem_goursatSnd.mp
    rw [h]
    trivial
  simpa [div_eq_mul_inv, mul_assoc] using K.mul_mem ht hv

private theorem eq_top_of_full_fst_kernel (K : Subgroup (G × H))
    (hsnd : Function.Surjective (Prod.snd ∘ K.subtype)) (h : K.goursatFst = ⊤) :
    K = ⊤ := by
  apply top_unique
  rintro ⟨a, b⟩ _
  obtain ⟨⟨⟨u, v⟩, hv⟩, hu⟩ := hsnd b
  change v = b at hu
  subst v
  have ht : (a / u, 1) ∈ K := by
    apply Subgroup.mem_goursatFst.mp
    rw [h]
    trivial
  simpa [div_eq_mul_inv, mul_assoc] using K.mul_mem ht hv

/-- A subdirect subgroup of two simple groups is the full product or a diagonal graph. -/
theorem subdirect_pair_eq_top_or_graph [IsSimpleGroup G] [IsSimpleGroup H]
    (K : Subgroup (G × H))
    (hfst : Function.Surjective (Prod.fst ∘ K.subtype))
    (hsnd : Function.Surjective (Prod.snd ∘ K.subtype)) :
    K = ⊤ ∨ ∃ e : G ≃* H, K = e.toMonoidHom.graph := by
  rcases (Subgroup.normal_goursatFst hfst).eq_bot_or_eq_top with h₁ | h₁
  · rcases (Subgroup.normal_goursatSnd hsnd).eq_bot_or_eq_top with h₂ | h₂
    · right
      apply Subgroup.exists_mulEquiv_eq_graph
      · refine ⟨?_, hfst⟩
        intro u v h
        change u.1.1 = v.1.1 at h
        apply Subtype.ext
        apply Prod.ext h
        have hm : u.1.2 / v.1.2 ∈ K.goursatSnd := by
          apply Subgroup.mem_goursatSnd.mpr
          have hd := K.div_mem u.2 v.2
          change (u.1.1 / v.1.1, u.1.2 / v.1.2) ∈ K at hd
          rw [h, div_self'] at hd
          exact hd
        simpa only [h₂, Subgroup.mem_bot, div_eq_one] using hm
      · refine ⟨?_, hsnd⟩
        intro u v h
        change u.1.2 = v.1.2 at h
        apply Subtype.ext
        refine Prod.ext ?_ h
        have hm : u.1.1 / v.1.1 ∈ K.goursatFst := by
          apply Subgroup.mem_goursatFst.mpr
          have hd := K.div_mem u.2 v.2
          change (u.1.1 / v.1.1, u.1.2 / v.1.2) ∈ K at hd
          rw [h, div_self'] at hd
          exact hd
        simpa only [h₁, Subgroup.mem_bot, div_eq_one] using hm
    · exact Or.inl (eq_top_of_full_snd_kernel K hfst h₂)
  · exact Or.inl (eq_top_of_full_fst_kernel K hsnd h₁)

end TwoFactors

section Schreier

variable {G X : Type*} [Group G] [MulAction G X]

/-- The Schreier loop of a generator edge relative to a path to each orbit vertex. -/
def schreierEdge (b : X) (path : MulAction.orbit G b → G)
    (x : MulAction.orbit G b) (g : G) : G :=
  (path (g • x))⁻¹ * g * path x

theorem schreierEdge_mul (b : X) (path : MulAction.orbit G b → G)
    (x : MulAction.orbit G b) (g h : G) :
    schreierEdge b path x (g * h) = schreierEdge b path (h • x) g *
      schreierEdge b path x h := by
  simp only [schreierEdge, mul_smul]
  group

private theorem schreierEdge_mem_stabilizer (b : X) (path : MulAction.orbit G b → G)
    (validPath : ∀ x, path x • b = x.val) (x : MulAction.orbit G b) (g : G) :
    schreierEdge b path x g ∈ MulAction.stabilizer G b := by
  apply MulAction.mem_stabilizer_iff.mpr
  simp only [schreierEdge, mul_smul, validPath]
  change (path (g • x))⁻¹ • (g • x : MulAction.orbit G b).val = b
  rw [← validPath (g • x), inv_smul_smul]

/-- Signed edge loops using any paths whose basepoint path is the empty word generate
the stabilizer. This applies both to a single orbit and to the orbit of an ordered pair. -/
theorem closure_signed_edges_eq_stabilizer (b : X) (S : Set G)
    (hS : closure S = ⊤) (path : MulAction.orbit G b → G)
    (validPath : ∀ x, path x • b = x.val)
    (rootPath : path ⟨b, MulAction.mem_orbit_self b⟩ = 1) :
    closure {u | ∃ (x : MulAction.orbit G b) (g : G),
        (g ∈ S ∨ g⁻¹ ∈ S) ∧ u = schreierEdge b path x g}
      = MulAction.stabilizer G b := by
  let E : Set G := {u | ∃ (x : MulAction.orbit G b) (g : G),
    (g ∈ S ∨ g⁻¹ ∈ S) ∧ u = schreierEdge b path x g}
  change closure E = MulAction.stabilizer G b
  apply le_antisymm
  · apply (Subgroup.closure_le _).2
    rintro _ ⟨x, g, _, rfl⟩
    exact schreierEdge_mem_stabilizer b path validPath x g
  · intro g hg
    have hg' : g ∈ closure S := by rw [hS]; trivial
    have hall (w : G) (hw : w ∈ closure S) (x : MulAction.orbit G b) :
        schreierEdge b path x w ∈ closure E := by
      refine Subgroup.closure_induction_left
        (p := fun w _ => ∀ x, schreierEdge b path x w ∈ closure E)
        ?_ ?_ ?_ hw x
      · intro y
        simp [schreierEdge]
      · intro a ha u _ hu y
        rw [schreierEdge_mul]
        exact (closure E).mul_mem (subset_closure ⟨u • y, a, Or.inl ha, rfl⟩) (hu y)
      · intro a ha u _ hu y
        rw [schreierEdge_mul]
        exact (closure E).mul_mem
          (subset_closure ⟨u • y, a⁻¹, Or.inr (by simpa using ha), rfl⟩) (hu y)
    let root : MulAction.orbit G b := ⟨b, MulAction.mem_orbit_self b⟩
    have hfix : g • root = root := Subtype.ext (MulAction.mem_stabilizer_iff.mp hg)
    have hone : path root = 1 := rootPath
    simpa only [schreierEdge, hfix, hone, inv_one, one_mul, mul_one] using hall g hg' root

end Schreier

section Factorization

variable {G Q T : Type*} [Group G] [Group Q] [Group T]

/-- Trivial action on a quotient kernel is exactly the stabilizer factorization test. -/
theorem exists_factor_iff_kernel_le (π : G →* Q) (hπ : Function.Surjective π)
    (ρ : G →* T) :
    (∃ θ : Q →* T, θ.comp π = ρ) ↔ π.ker ≤ ρ.ker := by
  constructor
  · rintro ⟨θ, hθ⟩ a ha
    change ρ a = 1
    rw [← hθ]
    change θ (π a) = 1
    rw [MonoidHom.mem_ker.mp ha, map_one]
  · intro h
    let e := QuotientGroup.quotientKerEquivOfSurjective π hπ
    refine ⟨(QuotientGroup.lift π.ker ρ h).comp e.symm.toMonoidHom, ?_⟩
    ext x
    have he : e (QuotientGroup.mk' π.ker x) = π x := rfl
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [← he, MulEquiv.symm_apply_apply]
    rfl

/-- A centerless diagonal is preserved by two inner actions exactly when their
conjugating elements correspond under the diagonal isomorphism. -/
theorem inner_actions_preserve_graph_iff (f : G ≃* T)
    (hcenter : Subgroup.center T = ⊥) (a : G) (b : T) :
    (∀ x : G, b * f x * b⁻¹ = f (a * x * a⁻¹)) ↔ b = f a := by
  constructor
  · intro h
    have hc : (f a)⁻¹ * b ∈ Subgroup.center T := by
      apply Subgroup.mem_center_iff.mpr
      intro z
      obtain ⟨x, rfl⟩ := f.surjective z
      have hx : b * f x = f a * f x * (f a)⁻¹ * b := by
        calc
          _ = (b * f x * b⁻¹) * b := by group
          _ = _ := by rw [h x, map_mul, map_mul, map_inv]
      calc
        _ = (f a)⁻¹ * (f a * f x * (f a)⁻¹ * b) := by group
        _ = _ := by rw [← hx]; group
    rw [hcenter, Subgroup.mem_bot, inv_mul_eq_one] at hc
    exact hc.symm
  · rintro rfl x
    rw [map_mul, map_mul, map_inv]

end Factorization

section CandidateGeneration

variable {G Q S : Type*} [Group G] [Group Q] [Group S]

/-- The candidate subgroup's intersection with the quotient kernel in direct-product coordinates. -/
def kernelCoordinates {n : ℕ} (π : G →* Q) (H : Subgroup G)
    (e : π.ker ≃* (Fin n → S)) : Subgroup (Fin n → S) :=
  (H.comap π.ker.subtype).map e.toMonoidHom

/-- A candidate generating the quotient generates the whole group when its kernel intersection
passes the nonabelian simple one- and two-coordinate tests. -/
theorem candidate_eq_top_of_pair_surjective [IsSimpleGroup S] {n : ℕ} (π : G →* Q)
    (H : Subgroup G) (e : π.ker ≃* (Fin n → S)) (hnc : ∃ a b : S, a * b ≠ b * a)
    (hq : ∀ q : Q, ∃ x ∈ H, π x = q)
    (hone : ∀ i : Fin n, ∀ a : S, ∃ x ∈ kernelCoordinates π H e, x i = a)
    (hpair : ∀ i j : Fin n, i ≠ j → ∀ a b : S,
      ∃ x ∈ kernelCoordinates π H e, x i = a ∧ x j = b) : H = ⊤ := by
  have hK := eq_top_of_pair_surjective hnc (kernelCoordinates π H e) hone hpair
  have hker : π.ker ≤ H := by
    intro a ha
    have hm : e ⟨a, ha⟩ ∈ kernelCoordinates π H e := by
      rw [hK]
      exact Subgroup.mem_top _
    obtain ⟨b, hb, he⟩ := hm
    have hba : b = ⟨a, ha⟩ := e.injective he
    change b.val ∈ H at hb
    rwa [hba] at hb
  apply top_unique
  intro x _
  obtain ⟨y, hy, hyx⟩ := hq (π x)
  have hdiv : x / y ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_div, hyx, div_self']
  simpa [div_eq_mul_inv, mul_assoc] using H.mul_mem (hker hdiv) hy

end CandidateGeneration

section ExactCandidateTests

variable {G Q S : Type*} [Group G] [Group Q] [Group S] [IsSimpleGroup S]

/-- A subdirect subgroup of a simple power has full pair projections when no pair is a
diagonal graph. The supplied inequalities are the witnesses of failure of the graph test. -/
theorem pair_surjective_of_no_diagonal {n : ℕ} (K : Subgroup (Fin n → S))
    (hone : ∀ i : Fin n, ∀ a : S, ∃ x ∈ K, x i = a)
    (hno : ∀ i j : Fin n, i ≠ j → ∀ f : S ≃* S,
      ∃ x ∈ K, f (x i) ≠ x j) :
    ∀ i j : Fin n, i ≠ j → ∀ a b : S, ∃ x ∈ K, x i = a ∧ x j = b := by
  intro i j hij a b
  let eval (k : Fin n) := Pi.evalMonoidHom (fun _ : Fin n => S) k
  let p := (eval i).prod (eval j)
  let L := K.map p
  have hf : Function.Surjective (Prod.fst ∘ L.subtype) := by
    intro u
    obtain ⟨x, hx, he⟩ := hone i u
    exact ⟨⟨p x, ⟨x, hx, rfl⟩⟩, he⟩
  have hs : Function.Surjective (Prod.snd ∘ L.subtype) := by
    intro u
    obtain ⟨x, hx, he⟩ := hone j u
    exact ⟨⟨p x, ⟨x, hx, rfl⟩⟩, he⟩
  rcases subdirect_pair_eq_top_or_graph L hf hs with hL | ⟨e, he⟩
  · have hp : (a, b) ∈ L := by rw [hL]; trivial
    obtain ⟨x, hx, hpx⟩ := hp
    exact ⟨x, hx, congrArg Prod.fst hpx, congrArg Prod.snd hpx⟩
  · obtain ⟨x, hx, hne⟩ := hno i j hij e
    have hm : p x ∈ L := ⟨x, hx, rfl⟩
    rw [he] at hm
    exact (hne (MonoidHom.mem_graph.mp hm)).elim

/-- The exact full-component and no-diagonal candidate test suffices for generation,
provided the candidate also generates the quotient. -/
theorem candidate_eq_top_of_no_diagonal {n : ℕ} (π : G →* Q)
    (H : Subgroup G) (e : π.ker ≃* (Fin n → S)) (hnc : ∃ a b : S, a * b ≠ b * a)
    (hq : ∀ q : Q, ∃ x ∈ H, π x = q)
    (hone : ∀ i : Fin n, ∀ a : S, ∃ x ∈ kernelCoordinates π H e, x i = a)
    (hno : ∀ i j : Fin n, i ≠ j → ∀ f : S ≃* S,
      ∃ x ∈ kernelCoordinates π H e, f (x i) ≠ x j) : H = ⊤ :=
  candidate_eq_top_of_pair_surjective π H e hnc hq hone
    (pair_surjective_of_no_diagonal _ hone hno)

end ExactCandidateTests

section SchreierFactorization

variable {G X Q T : Type*} [Group G] [MulAction G X] [Group Q] [Group T]

/-- The Schreier edge loops, considered as elements of the stabilizer subgroup. -/
def stabilizerEdges (b : X) (S : Set G) (path : MulAction.orbit G b → G)
    (validPath : ∀ x, path x • b = x.val) : Set (MulAction.stabilizer G b) :=
  {u | ∃ (x : MulAction.orbit G b) (g : G), (g ∈ S ∨ g⁻¹ ∈ S) ∧
    u = ⟨schreierEdge b path x g, schreierEdge_mem_stabilizer b path validPath x g⟩}

theorem closure_stabilizerEdges (b : X) (S : Set G) (hS : closure S = ⊤)
    (path : MulAction.orbit G b → G) (validPath : ∀ x, path x • b = x.val)
    (rootPath : path ⟨b, MulAction.mem_orbit_self b⟩ = 1) :
    closure (stabilizerEdges b S path validPath) = ⊤ := by
  let H := MulAction.stabilizer G b
  have hmap : (⊤ : Subgroup H).map H.subtype = H := by
    ext x
    constructor
    · rintro ⟨y, _, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩
  have himage : H.subtype '' stabilizerEdges b S path validPath =
      {u | ∃ (x : MulAction.orbit G b) (g : G),
        (g ∈ S ∨ g⁻¹ ∈ S) ∧ u = schreierEdge b path x g} := by
    ext u
    constructor
    · rintro ⟨v, ⟨x, g, hg, rfl⟩, rfl⟩
      exact ⟨x, g, hg, rfl⟩
    · rintro ⟨x, g, hg, rfl⟩
      exact ⟨⟨_, schreierEdge_mem_stabilizer b path validPath x g⟩,
        ⟨x, g, hg, rfl⟩, rfl⟩
  apply Subgroup.map_subtype_inj.mp
  change (closure (stabilizerEdges b S path validPath)).map H.subtype =
    (⊤ : Subgroup H).map H.subtype
  rw [MonoidHom.map_closure, hmap, himage]
  exact closure_signed_edges_eq_stabilizer b S hS path validPath rootPath

/-- An action factors through the quotient of the stabilizer exactly when a quotient action
agrees on the signed Schreier edge loops. -/
theorem stabilizer_kernel_le_iff_exists_edge_factor
    (b : X) (S : Set G) (hS : closure S = ⊤)
    (path : MulAction.orbit G b → G) (validPath : ∀ x, path x • b = x.val)
    (rootPath : path ⟨b, MulAction.mem_orbit_self b⟩ = 1)
    (π : MulAction.stabilizer G b →* Q) (hπ : Function.Surjective π)
    (ρ : MulAction.stabilizer G b →* T) :
    π.ker ≤ ρ.ker ↔ ∃ θ : Q →* T,
      Set.EqOn (θ.comp π) ρ (stabilizerEdges b S path validPath) := by
  rw [← exists_factor_iff_kernel_le π hπ ρ]
  constructor
  · rintro ⟨θ, hθ⟩
    exact ⟨θ, fun a _ => DFunLike.congr_fun hθ a⟩
  · rintro ⟨θ, hθ⟩
    exact ⟨θ, MonoidHom.eq_of_eqOn_dense
      (closure_stabilizerEdges b S hS path validPath rootPath) hθ⟩

end SchreierFactorization

section FiniteOrbitSelection

variable {A B : Type*} [LinearOrder A] [DecidableEq B]

/-- Scan predicate selecting the first available candidate in every orbit, represented by
a complete invariant of candidate equivalence. -/
def leastOrbitRepresentatives (candidates : Finset A) (key : A → B)
    (forbidden : Finset B) : Finset A :=
  candidates.filter fun a => key a ∉ forbidden ∧
    ∀ b ∈ candidates, key b = key a → a ≤ b

theorem leastOrbitRepresentatives_subset (candidates : Finset A) (key : A → B)
    (forbidden : Finset B) :
    leastOrbitRepresentatives candidates key forbidden ⊆ candidates :=
  Finset.filter_subset _ _

theorem leastOrbitRepresentatives_injOn (candidates : Finset A) (key : A → B)
    (forbidden : Finset B) :
    Set.InjOn key (leastOrbitRepresentatives candidates key forbidden) := by
  intro a ha b hb hab
  obtain ⟨has, _, hamin⟩ := Finset.mem_filter.mp ha
  obtain ⟨hbs, _, hbmin⟩ := Finset.mem_filter.mp hb
  exact le_antisymm (hamin b hbs hab.symm) (hbmin a has hab)

theorem leastOrbitRepresentatives_image (candidates : Finset A) (key : A → B)
    (forbidden : Finset B) :
    (leastOrbitRepresentatives candidates key forbidden).image key =
      candidates.image key \ forbidden := by
  ext z
  constructor
  · intro hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨has, haf, _⟩ := Finset.mem_filter.mp ha
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨a, has, rfl⟩, haf⟩
  · intro hz
    obtain ⟨hzi, hzf⟩ := Finset.mem_sdiff.mp hz
    obtain ⟨a, ha, haz⟩ := Finset.mem_image.mp hzi
    let fiber := candidates.filter fun b => key b = z
    have hf : fiber.Nonempty := ⟨a, Finset.mem_filter.mpr ⟨ha, haz⟩⟩
    let rep := fiber.min' hf
    obtain ⟨hr, hrz⟩ := Finset.mem_filter.mp (Finset.min'_mem fiber hf)
    apply Finset.mem_image.mpr
    refine ⟨rep, Finset.mem_filter.mpr ⟨hr, ?_, ?_⟩, hrz⟩
    · rwa [hrz]
    · intro b hb hbkey
      exact Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hb, hbkey.trans hrz⟩)

theorem enough_leastOrbitRepresentatives (candidates : Finset A) (key : A → B)
    (forbidden : Finset B) {k : ℕ} (h : k + forbidden.card ≤ (candidates.image key).card) :
    k ≤ (leastOrbitRepresentatives candidates key forbidden).card := by
  have him := leastOrbitRepresentatives_image candidates key forbidden
  have hinj := leastOrbitRepresentatives_injOn candidates key forbidden
  have hcard := Finset.card_le_card_sdiff_add_card (s := candidates.image key) (t := forbidden)
  rw [← him, Finset.card_image_of_injOn hinj] at hcard
  exact Nat.le_of_add_le_add_right (h.trans hcard)

end FiniteOrbitSelection

end Mathproof.MinimumGenerationSemisimple
