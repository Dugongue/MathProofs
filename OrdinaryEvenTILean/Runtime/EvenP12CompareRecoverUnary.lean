import EvenP12CompareSmithCoordinate

namespace EvenTI.P12Compare

open scoped BigOperators Matrix

/-- A single linear congruence in the coordinate being installed. -/
structure UnaryEquation where
  coefficient : ℕ
  value : ℕ
  modulus : ℕ

def UnaryEquation.Satisfied (e : UnaryEquation) (x : ℕ) : Prop :=
  e.coefficient*x ≡ e.value [MOD e.modulus]

private def bezoutResidue (a b d : ℕ) : ℕ :=
  (((b / Nat.gcd a d : ℕ) : ZMod d) * (Nat.gcdA a d : ZMod d)).val

private theorem bezoutResidue_solves (a b d : ℕ) (hd : 0 < d) (hb : Nat.gcd a d ∣ b) :
    a * bezoutResidue a b d ≡ b [MOD d] := by
  letI : NeZero d := ⟨hd.ne'⟩
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  have hg := congrArg (fun z : ℤ => (z : ZMod d)) (Nat.gcd_eq_gcd_ab a d)
  push_cast at hg
  rw [ZMod.natCast_self,zero_mul,add_zero] at hg
  rw [Nat.cast_mul]
  unfold bezoutResidue
  rw [ZMod.natCast_zmod_val]
  calc (a : ZMod d) * ((b / Nat.gcd a d : ℕ) * (Nat.gcdA a d : ZMod d)) =
      (b / Nat.gcd a d : ℕ) * ((a : ZMod d) * (Nat.gcdA a d : ZMod d)) := by ring
    _ = b := by rw [← hg, ← Nat.cast_mul, Nat.div_mul_cancel hb]

/-- Normalize an equation to one canonical residue class. -/
def normalizeUnary (e : UnaryEquation) : Option (ℕ × ℕ) :=
  if Nat.gcd e.coefficient e.modulus ∣ e.value then
    let l := e.modulus / Nat.gcd e.coefficient e.modulus
    some (bezoutResidue e.coefficient e.value e.modulus % l, l)
  else none

theorem normalizeUnary_correct (e : UnaryEquation) (hd : 0 < e.modulus) (x : ℕ) :
    (∃ w, normalizeUnary e = some w ∧ x ≡ w.1 [MOD w.2]) ↔ e.Satisfied x := by
  rcases e with ⟨a,b,d⟩
  let g := Nat.gcd a d
  let r := bezoutResidue a b d
  let l := d / g
  have hda : g ∣ a := Nat.gcd_dvd_left _ _
  have hdd : g ∣ d := Nat.gcd_dvd_right _ _
  unfold normalizeUnary UnaryEquation.Satisfied
  change (∃ w, (if g ∣ b then some (r % l,l) else none) = some w ∧
    x ≡ w.1 [MOD w.2]) ↔ a*x ≡ b [MOD d]
  by_cases hg : g ∣ b
  · rw [if_pos hg]
    have hr : a*r ≡ b [MOD d] := bezoutResidue_solves a b d hd hg
    constructor
    · rintro ⟨w,hw,hx⟩
      have hwe : w = (r%l,l) := (Option.some.inj hw).symm
      subst w
      have hxr : x ≡ r [MOD l] := hx.trans (Nat.mod_modEq r l)
      have hscaled := (hxr.mul_left' g).mul_left (a/g)
      have hgl : g*l = d := Nat.mul_div_cancel' hdd
      have hga : a/g*g = a := Nat.div_mul_cancel hda
      have hab : a*x ≡ a*r [MOD d] := by
        simpa only [hgl,← Nat.mul_assoc,hga] using hscaled
      exact hab.trans hr
    · intro hx
      have hxr : x ≡ r [MOD l] := by
        simpa [l,g,Nat.gcd_comm] using (hx.trans hr.symm).cancel_left_div_gcd hd
      exact ⟨(r%l,l),rfl,hxr.trans (Nat.mod_modEq r l).symm⟩
  · rw [if_neg hg]
    refine ⟨by simp,?_⟩
    intro h
    exact False.elim (hg ((h.dvd_iff hdd).mp (dvd_mul_of_dvd_left hda x)))

private theorem normalizeUnary_bounds (e : UnaryEquation) {M : ℕ}
    (hM : 0 < M) (hdM : e.modulus ∣ M) {w : ℕ × ℕ} (hw : normalizeUnary e = some w) :
    0 < w.2 ∧ w.2 ∣ M ∧ w.1 < w.2 := by
  unfold normalizeUnary at hw
  split at hw
  · have he := Option.some.inj hw
    subst w
    have hd : 0 < e.modulus := Nat.pos_of_dvd_of_pos hdM hM
    have hl := Nat.div_gcd_pos_of_pos_right e.coefficient hd
    refine ⟨hl,?_,Nat.mod_lt _ hl⟩
    exact (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right _ _)).trans hdM
  · contradiction

private theorem mergeUnary_bounds {a d b e M : ℕ} {w : ℕ × ℕ} (hd : 0 < d) (he : 0 < e)
    (hdM : d ∣ M) (heM : e ∣ M) (hw : mergeUnary a d b e = some w) :
    0 < w.2 ∧ w.2 ∣ M ∧ w.1 < w.2 := by
  unfold mergeUnary at hw
  split at hw
  · rename_i h
    have hwe := Option.some.inj hw
    subst w
    exact ⟨Nat.lcm_pos hd he,Nat.lcm_dvd hdM heM,
      Nat.chineseRemainder'_lt_lcm h hd.ne' he.ne'⟩
  · contradiction

/-- Scan the installed Smith rows, maintaining one residue class of all
coordinates that extend to a solution of the current prefix. -/
def solveUnaryList : List UnaryEquation → Option (ℕ × ℕ)
  | [] => some (0,1)
  | e::es => do
    let w ← normalizeUnary e
    let v ← solveUnaryList es
    mergeUnary w.1 w.2 v.1 v.2

theorem solveUnaryList_correct (es : List UnaryEquation)
    (h : ∀ e ∈ es, 0 < e.modulus) (x : ℕ) :
    (∃ w, solveUnaryList es = some w ∧ x ≡ w.1 [MOD w.2]) ↔
      ∀ e ∈ es, e.Satisfied x := by
  induction es with
  | nil => simp [solveUnaryList,Nat.ModEq,Nat.mod_one]
  | cons e es ih =>
    have he := normalizeUnary_correct e (h e List.mem_cons_self) x
    have hs := ih (fun e hme => h e (List.mem_cons_of_mem _ hme))
    constructor
    · rintro ⟨w,hw,hx⟩
      change (normalizeUnary e).bind (fun v =>
        (solveUnaryList es).bind (fun u => mergeUnary v.1 v.2 u.1 u.2)) = some w at hw
      obtain ⟨v,hv,hw⟩ := Option.bind_eq_some_iff.mp hw
      obtain ⟨u,hu,hw⟩ := Option.bind_eq_some_iff.mp hw
      obtain ⟨h₁,h₂⟩ := (mergeUnary_correct v.1 v.2 u.1 u.2 x).mp ⟨w,hw,hx⟩
      intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact he.mp ⟨v,hv,h₁⟩
      · exact (hs.mp ⟨u,hu,h₂⟩) j hj
    · intro hx
      obtain ⟨v,hv,h₁⟩ := he.mpr (hx e List.mem_cons_self)
      obtain ⟨u,hu,h₂⟩ := hs.mpr (fun j hj => hx j (List.mem_cons_of_mem _ hj))
      obtain ⟨w,hw,hfinal⟩ := (mergeUnary_correct v.1 v.2 u.1 u.2 x).mpr ⟨h₁,h₂⟩
      exact ⟨w,by simp [solveUnaryList,hv,hu,hw],hfinal⟩

theorem solveUnaryList_bounds (es : List UnaryEquation) {M : ℕ}
    (hM : 0 < M) (h : ∀ e ∈ es, e.modulus ∣ M)
    {w : ℕ × ℕ} (hw : solveUnaryList es = some w) :
    0 < w.2 ∧ w.2 ∣ M ∧ w.1 < w.2 := by
  induction es generalizing w with
  | nil => simp only [solveUnaryList,Option.some.injEq] at hw; subst w; simp
  | cons e es ih =>
    change (normalizeUnary e).bind (fun v =>
      (solveUnaryList es).bind (fun u => mergeUnary v.1 v.2 u.1 u.2)) = some w at hw
    obtain ⟨v,hv,hw⟩ := Option.bind_eq_some_iff.mp hw
    obtain ⟨u,hu,hw⟩ := Option.bind_eq_some_iff.mp hw
    obtain ⟨hvp,hvd,_⟩ := normalizeUnary_bounds e hM (h e List.mem_cons_self) hv
    obtain ⟨hup,hud,_⟩ := ih (fun j hj => h j (List.mem_cons_of_mem _ hj)) hu
    exact mergeUnary_bounds hvp hup hvd hud hw

#print axioms normalizeUnary_correct
#print axioms solveUnaryList_correct
#print axioms solveUnaryList_bounds

end EvenTI.P12Compare
