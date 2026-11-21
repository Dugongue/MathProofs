namespace DirectionalGap

abbrev Profile := Bool → Bool → Bool → Prop

def gap (p : Profile) : Prop :=
  p true false false ∧ ¬ p false false false

def shiftedDiagonal (p : Bool → Prop) : Profile :=
  fun x y z => ∃ t, p t ∧ x = !t ∧ y = t ∧ z = t

def shiftedDualDiagonal (p : Bool → Prop) : Profile :=
  fun x y z => ∃ t, p t ∧ x = t ∧ y = !t ∧ z = !t

theorem diagonal_reads_positive (p : Bool → Prop) :
    gap (shiftedDiagonal p) ↔ p false := by
  simp [gap, shiftedDiagonal]

theorem diagonal_reads_negative (p : Bool → Prop) :
    gap (shiftedDualDiagonal p) ↔ p true := by
  simp [gap, shiftedDualDiagonal]

theorem padded_reads_absence (p : Bool → Prop)
    (nonempty : p false ∨ p true) :
    gap (fun x _ _ => p x) ↔ ¬ p false := by
  constructor
  · exact And.right
  · intro missing
    exact ⟨nonempty.resolve_left missing, missing⟩

theorem promise_guard {ordinary signed localFailure : Prop}
    (impliesOrdinary : signed → ordinary)
    (agreement : ordinary → (localFailure ↔ ¬ signed)) :
    (¬ ordinary ∨ (ordinary ∧ localFailure)) ↔ ¬ signed := by
  constructor
  · rintro (h | ⟨ho, hf⟩)
    · exact fun hs => h (impliesOrdinary hs)
    · exact (agreement ho).mp hf
  · intro hn
    classical
    by_cases ho : ordinary
    · exact Or.inr ⟨ho, (agreement ho).mpr hn⟩
    · exact Or.inl ho

end DirectionalGap
