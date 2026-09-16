import Mathlib

/-!
A counterexample to Conjecture 2.9 of Caishi Fang,
"Accelerations for Graph Isomorphism", arXiv:1706.09230 (2017).

Collapse tomography records the vertex-degree and edge-degree multisets of
successive induced breadth-first layers. The ten-vertex example has the same
tomography at every vertex, but no automorphism sends vertex 0 to vertex 2.

The classical Tutte 12-cage also refutes this conjecture: it is bipartite
and distance-regular, so every root has edgeless distance layers of sizes
3, 6, 12, 24, 48, 32 and hence identical collapse tomography, but it is
not vertex-transitive. This observation is contextual; the formal proof
below certifies the ten-vertex example.
References: R. F. Bailey, "The metric dimension of small distance-regular
and strongly regular graphs" (2013), Section 4.2 and Table 3;
Y. Alizadeh et al., "Wiener Dimension: Fundamental Properties and
(5,0)-Nanotubical Fullerenes", MATCH 72 (2014), proof of Theorem 4.2.

All finite certificates use kernel reduction, not native_decide.
-/

namespace GraphTomography

def layerNeighbors {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Finset (Fin n)) (v : Fin n) : Finset (Fin n) :=
  s.filter (G.Adj v)

def layerProperty {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Finset (Fin n)) : Multiset ℕ × Multiset ℕ :=
  (s.val.map (fun v => (layerNeighbors G s v).card),
   ((s ×ˢ s).filter (fun uv => uv.1 < uv.2 ∧ G.Adj uv.1 uv.2)).val.map
     (fun uv => (layerNeighbors G s uv.1).card +
       (layerNeighbors G s uv.2).card -
       (layerNeighbors G s uv.1 ∩ layerNeighbors G s uv.2).card))

def nextLayer {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (seen front : Finset (Fin n)) : Finset (Fin n) :=
  (Finset.univ.filter (fun v => ∃ u ∈ front, G.Adj u v)) \ (seen ∪ front)

def collectLayers {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ℕ → Finset (Fin n) → Finset (Fin n) → List (Multiset ℕ × Multiset ℕ)
  | 0, _, _ => []
  | fuel + 1, seen, front =>
    if front = ∅ then [] else
      layerProperty G front ::
        collectLayers G fuel (seen ∪ front) (nextLayer G seen front)

def tomography {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (root : Fin n) : List (Multiset ℕ × Multiset ℕ) :=
  collectLayers G n {root} (Finset.univ.filter (G.Adj root))

def VertexTransitive {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ u v, ∃ f : G ≃g G, f u = v

def neighbors : Fin 10 → Finset (Fin 10) :=
  ![{7, 8, 9}, {7, 8, 9}, {5, 6, 9}, {5, 6, 7}, {5, 6, 8},
    {2, 3, 4}, {2, 3, 4}, {0, 1, 3}, {0, 1, 4}, {0, 1, 2}]

def exampleGraph : SimpleGraph (Fin 10) where
  Adj u v := v ∈ neighbors u
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

instance : DecidableRel exampleGraph.Adj :=
  fun u v => inferInstanceAs (Decidable (v ∈ neighbors u))

def commonTomography : List (Multiset ℕ × Multiset ℕ) :=
  [({0, 0, 0}, 0), ({0, 0, 0, 0}, 0), ({0, 0}, 0)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem tomography_eq : ∀ v : Fin 10,
    tomography exampleGraph v = commonTomography := by
  decide

theorem zero_one_twins : ∀ v : Fin 10,
    exampleGraph.Adj 0 v ↔ exampleGraph.Adj 1 v := by
  decide

theorem two_has_no_twin : ∀ w : Fin 10, w ≠ 2 →
    ¬ (∀ v, exampleGraph.Adj 2 v ↔ exampleGraph.Adj w v) := by
  decide

theorem no_automorphism_zero_to_two (f : exampleGraph ≃g exampleGraph) :
    f 0 ≠ 2 := by
  intro h
  have hne : f 1 ≠ 2 := by
    intro h1
    have : (1 : Fin 10) = 0 := f.injective (h1.trans h.symm)
    exact (by decide : (1 : Fin 10) ≠ 0) this
  apply two_has_no_twin (f 1) hne
  intro v
  obtain ⟨w, rfl⟩ := f.surjective v
  rw [← h]
  exact (f.map_adj_iff).trans ((zero_one_twins w).trans f.map_adj_iff.symm)

theorem not_vertexTransitive : ¬ VertexTransitive exampleGraph := by
  intro h
  obtain ⟨f, hf⟩ := h 0 2
  exact no_automorphism_zero_to_two f hf

/-- An explicit existential refutation of the stated conjecture. -/
theorem counterexample :
    (∀ u v : Fin 10, tomography exampleGraph u = tomography exampleGraph v) ∧
      ¬ VertexTransitive exampleGraph := by
  exact ⟨fun u v => (tomography_eq u).trans (tomography_eq v).symm,
    not_vertexTransitive⟩

#print axioms counterexample

end GraphTomography
