import Mathlib

/-! # P15 FACTOR reference: computable list polynomials (campaign p15-lean-20261007)

The field is an abstract record `FOps α` of computable operations; `Agree O` states that they are
the operations of a `Field α` instance (for a presented field, transport the field structure along
the presentation equivalence, e.g. with `Equiv.field`, and prove `Agree` from the presentation lemmas).

Polynomials are little-endian coefficient lists, `toPoly [a₀, a₁, …] = a₀ + a₁ X + …`.  A list is
*normalized* (`Norm`) when its last entry is nonzero; normalized lists are canonical representatives
(`norm_inj`).  Cost notes are in field operations, `n` = list lengths. -/

namespace Mathproof.P15FactorRef20261007

open Polynomial

set_option linter.unusedSectionVars false

/-- Computable field operations. `key` is an injective code used for sorting, `card = |α|`,
`elt` enumerates the field (only its validity/injectivity matter, and only for the failure bound). -/
structure FOps (α : Type) where
  zero : α
  one : α
  add : α → α → α
  neg : α → α
  mul : α → α → α
  inv : α → α
  beq : α → α → Bool
  key : α → ℕ
  card : ℕ
  /-- enumeration of the field by digits `0 … card-1` (used to draw random residues) -/
  elt : ℕ → α

/-- The operations are those of a field. -/
structure Agree {α : Type} [Field α] [Fintype α] [DecidableEq α] (O : FOps α) : Prop where
  zero : O.zero = 0
  one : O.one = 1
  add : ∀ a b, O.add a b = a + b
  neg : ∀ a, O.neg a = -a
  mul : ∀ a b, O.mul a b = a * b
  inv : ∀ a, O.inv a = a⁻¹
  beq : ∀ a b, O.beq a b = decide (a = b)
  key : Function.Injective O.key
  card : O.card = Fintype.card α

variable {α : Type} (O : FOps α)

/-! ## Computable operations -/

/-- Drop trailing zeros. Cost: `n` comparisons. -/
def trim : List α → List α
  | [] => []
  | a :: l => match trim l with
    | [] => if O.beq a O.zero then [] else [a]
    | b :: t => a :: b :: t

/-- Cost: `min n m` additions. -/
def addL : List α → List α → List α
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => O.add a b :: addL p q

def negL (p : List α) : List α := p.map O.neg

def subL (p q : List α) : List α := addL O p (negL O q)

def smulL (c : α) (p : List α) : List α := p.map (O.mul c)

/-- Schoolbook product. Cost: `O(n m)`. -/
def mulL : List α → List α → List α
  | [], _ => []
  | a :: p, q => addL O (smulL O a q) (O.zero :: mulL p q)

/-- `X^k * p`. -/
def shiftL (k : ℕ) (p : List α) : List α := List.replicate k O.zero ++ p

/-- Last coefficient (leading coefficient of a normalized list). -/
def lastL (p : List α) : α := p.getLast?.getD O.zero

/-- Monic normalization `p / lc p`. Cost: `n + 1`. -/
def monicL (p : List α) : List α := smulL O (O.inv (lastL O p)) p

/-- Division with remainder by a monic normalized `q`; `fuel ≥ length p` suffices.
Cost: `≤ length p` steps of `O(length q)`. -/
def divModAux (q : List α) : ℕ → List α → List α → List α × List α
  | 0, quot, rem => (quot, rem)
  | fuel + 1, quot, rem =>
    if rem.length < q.length then (quot, rem) else
      let c := lastL O rem
      let k := rem.length - q.length
      divModAux q fuel (addL O quot (shiftL O k [c])) (trim O (subL O rem (shiftL O k (smulL O c q))))

def divModL (q p : List α) : List α × List α := divModAux O q (p.length) [] (trim O p)

/-- `p mod q` for monic `q`. -/
def modL (p q : List α) : List α := (divModL O q p).2

/-- Monic gcd by Euclid; `fuel ≥ length b + 1` suffices. Cost: `≤ length b` divisions. -/
def gcdAux : ℕ → List α → List α → List α
  | 0, a, _ => monicL O a
  | fuel + 1, a, b => if b.isEmpty then monicL O a else gcdAux fuel b (modL O a (monicL O b))

def gcdL (a b : List α) : List α := gcdAux O (b.length + 1) (trim O a) (trim O b)


/-! ## Semantics -/

section semantics

variable {α : Type} [Field α]

/-- The polynomial of a coefficient list. -/
noncomputable def toPoly : List α → α[X]
  | [] => 0
  | a :: l => C a + X * toPoly l

@[simp] theorem toPoly_nil : toPoly ([] : List α) = 0 := rfl
@[simp] theorem toPoly_cons (a : α) (l : List α) : toPoly (a :: l) = C a + X * toPoly l := rfl

theorem coeff_toPoly (l : List α) (i : ℕ) : (toPoly l).coeff i = l.getD i 0 := by
  induction l generalizing i with
  | nil => simp
  | cons a l ih =>
    cases i with
    | zero => simp
    | succ i => simp [coeff_X_mul, ih]

/-- Normalized: the last coefficient is nonzero. -/
def Norm (l : List α) : Prop := ∀ x, l.getLast? = some x → x ≠ 0

theorem norm_nil : Norm ([] : List α) := by intro x h; simp at h

theorem norm_tail {a : α} {l : List α} (h : Norm (a :: l)) : Norm l := by
  intro x hx
  apply h x
  cases l with
  | nil => simp at hx
  | cons b t => rw [List.getLast?_cons_cons]; exact hx

theorem degree_toPoly_lt (l : List α) : (toPoly l).degree < l.length := by
  rw [degree_lt_iff_coeff_zero]
  intro m hm
  rw [coeff_toPoly, List.getD_eq_default _ _ hm]

theorem natDegree_toPoly_le (l : List α) : (toPoly l).natDegree ≤ l.length - 1 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [coeff_toPoly, List.getD_eq_default _ _ (by omega)]

theorem getLast_mem_getD {l : List α} (hl : l ≠ []) :
    l.getD (l.length - 1) 0 = l.getLast hl := by
  rw [List.getD_eq_getElem _ _ (by have := List.length_pos_of_ne_nil hl; omega),
    List.getLast_eq_getElem]

theorem norm_props {l : List α} (hn : Norm l) (hl : l ≠ []) :
    toPoly l ≠ 0 ∧ (toPoly l).natDegree = l.length - 1 ∧ (toPoly l).leadingCoeff = l.getLast hl := by
  have hlast : l.getLast hl ≠ 0 := hn _ (List.getLast?_eq_some_getLast hl)
  have hc : (toPoly l).coeff (l.length - 1) = l.getLast hl := by
    rw [coeff_toPoly, getLast_mem_getD hl]
  have hne : toPoly l ≠ 0 := by
    intro h0; rw [h0, coeff_zero] at hc; exact hlast hc.symm
  have hdeg : (toPoly l).natDegree = l.length - 1 :=
    le_antisymm (natDegree_toPoly_le l) (le_natDegree_of_ne_zero (by rw [hc]; exact hlast))
  exact ⟨hne, hdeg, by rw [leadingCoeff, hdeg, hc]⟩

theorem norm_toPoly_eq_zero {l : List α} (hn : Norm l) : toPoly l = 0 ↔ l = [] := by
  constructor
  · intro h; by_contra hl; exact (norm_props hn hl).1 h
  · rintro rfl; rfl

theorem norm_length_eq {l : List α} (hn : Norm l) (hl : l ≠ []) :
    l.length = (toPoly l).natDegree + 1 := by
  have := (norm_props hn hl).2.1
  have := List.length_pos_of_ne_nil hl
  omega

theorem norm_inj {l l' : List α} (hn : Norm l) (hn' : Norm l') (h : toPoly l = toPoly l') :
    l = l' := by
  have hlen : l.length = l'.length := by
    by_cases hl : l = []
    · subst hl
      have : l' = [] := (norm_toPoly_eq_zero hn').mp (by rw [← h]; rfl)
      rw [this]
    · have hl' : l' ≠ [] := fun h' => hl ((norm_toPoly_eq_zero hn).mp (by rw [h, h']; rfl))
      rw [norm_length_eq hn hl, norm_length_eq hn' hl', h]
  apply List.ext_getElem hlen
  intro i h1 h2
  have := congrArg (fun p => p.coeff i) h
  simp only [coeff_toPoly] at this
  rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this

end semantics

/-! ## Correctness of the list operations -/

section correct

variable {α : Type} [Field α] [Fintype α] [DecidableEq α] {O : FOps α} (hO : Agree O)
include hO

theorem trim_spec (l : List α) : toPoly (trim O l) = toPoly l ∧ Norm (trim O l) := by
  induction l with
  | nil => exact ⟨rfl, norm_nil⟩
  | cons a l ih =>
    obtain ⟨ih1, ih2⟩ := ih
    simp only [trim]
    split
    · rename_i h
      rw [h] at ih1 ih2
      by_cases ha : a = 0
      · rw [if_pos (by rw [hO.beq, hO.zero]; simp [ha])]
        refine ⟨?_, norm_nil⟩
        simp [ha, ← ih1]
      · rw [if_neg (by rw [hO.beq, hO.zero]; simp [ha])]
        refine ⟨by simp [← ih1], ?_⟩
        intro x hx; simp at hx; rw [← hx]; exact ha
    · rename_i b t h
      rw [h] at ih1 ih2
      refine ⟨by simp [← ih1], ?_⟩
      intro x hx
      apply ih2 x
      rw [List.getLast?_cons_cons] at hx
      exact hx

theorem toPoly_trim (l : List α) : toPoly (trim O l) = toPoly l := (trim_spec hO l).1
theorem norm_trim (l : List α) : Norm (trim O l) := (trim_spec hO l).2

theorem trim_of_norm {l : List α} (hn : Norm l) : trim O l = l :=
  norm_inj (norm_trim hO l) hn (toPoly_trim hO l)

theorem toPoly_addL (p q : List α) : toPoly (addL O p q) = toPoly p + toPoly q := by
  induction p generalizing q with
  | nil => simp [addL]
  | cons a p ih =>
    cases q with
    | nil => simp [addL]
    | cons b q => simp only [addL, toPoly_cons, ih, hO.add, C_add]; ring

theorem toPoly_negL (p : List α) : toPoly (negL O p) = - toPoly p := by
  induction p with
  | nil => simp [negL]
  | cons a p ih =>
    simp only [negL, List.map_cons, toPoly_cons, hO.neg, C_neg] at ih ⊢
    rw [ih]; ring

theorem toPoly_subL (p q : List α) : toPoly (subL O p q) = toPoly p - toPoly q := by
  rw [subL, toPoly_addL hO, toPoly_negL hO]; ring

theorem toPoly_smulL (c : α) (p : List α) : toPoly (smulL O c p) = C c * toPoly p := by
  induction p with
  | nil => simp [smulL]
  | cons a p ih =>
    simp only [smulL, List.map_cons, toPoly_cons, hO.mul, C_mul] at ih ⊢
    rw [ih]; ring

theorem toPoly_mulL (p q : List α) : toPoly (mulL O p q) = toPoly p * toPoly q := by
  induction p with
  | nil => simp [mulL]
  | cons a p ih =>
    simp only [mulL, toPoly_addL hO, toPoly_smulL hO, toPoly_cons, ih, hO.zero, C_0]
    ring

theorem toPoly_shiftL (k : ℕ) (p : List α) : toPoly (shiftL O k p) = X ^ k * toPoly p := by
  induction k with
  | zero => simp [shiftL]
  | succ k ih =>
    simp only [shiftL, List.replicate_succ, List.cons_append, toPoly_cons, hO.zero, C_0,
      zero_add] at ih ⊢
    rw [ih]; ring

theorem length_shiftL (k : ℕ) (p : List α) : (shiftL O k p).length = k + p.length := by
  simp [shiftL]

theorem lastL_eq {p : List α} (hp : p ≠ []) : lastL O p = p.getLast hp := by
  rw [lastL, List.getLast?_eq_some_getLast hp]; rfl

end correct


/-! ## Monic normalization, division, gcd -/

section divgcd

variable {α : Type} [Field α] [Fintype α] [DecidableEq α] {O : FOps α} (hO : Agree O)
include hO

theorem length_trim_le (l : List α) : (trim O l).length ≤ l.length := by
  induction l with
  | nil => simp [trim]
  | cons a l ih =>
    simp only [trim]
    split
    · split_ifs <;> simp
    · rename_i b t h; rw [h] at ih; simp at ih ⊢; omega

theorem norm_smulL {c : α} (hc : c ≠ 0) {p : List α} (hp : Norm p) : Norm (smulL O c p) := by
  intro x hx
  simp only [smulL, List.getLast?_map, Option.map_eq_some_iff] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [hO.mul]
  exact mul_ne_zero hc (hp y hy)

theorem lastL_smulL (c : α) {p : List α} (hp : p ≠ []) :
    lastL O (smulL O c p) = c * lastL O p := by
  have hp' : smulL O c p ≠ [] := by simp [smulL, hp]
  rw [lastL_eq hO hp', lastL_eq hO hp]
  simp [smulL, List.getLast_map, hO.mul]

theorem monicL_spec {p : List α} (hp : Norm p) (hne : p ≠ []) :
    toPoly (monicL O p) = C (lastL O p)⁻¹ * toPoly p ∧ Norm (monicL O p) ∧
      monicL O p ≠ [] ∧ lastL O (monicL O p) = 1 := by
  have hl : lastL O p ≠ 0 := by rw [lastL_eq hO hne]; exact hp _ (List.getLast?_eq_some_getLast hne)
  refine ⟨by rw [monicL, toPoly_smulL hO, hO.inv], norm_smulL hO (by rw [hO.inv]; exact inv_ne_zero hl) hp,
    by simp [monicL, smulL, hne], ?_⟩
  rw [monicL, lastL_smulL hO _ hne, hO.inv, inv_mul_cancel₀ hl]

theorem monic_of_lastL {p : List α} (hp : Norm p) (hne : p ≠ []) (h1 : lastL O p = 1) :
    (toPoly p).Monic := by
  rw [Monic, (norm_props hp hne).2.2, ← lastL_eq hO hne, h1]

theorem toPoly_monicL {p : List α} (hp : Norm p) : toPoly (monicL O p) = normalize (toPoly p) := by
  by_cases hne : p = []
  · subst hne; simp [monicL, smulL]
  obtain ⟨h1, h2, h3, h4⟩ := monicL_spec hO hp hne
  have hP : toPoly p ≠ 0 := (norm_props hp hne).1
  have hl : lastL O p ≠ 0 := by rw [lastL_eq hO hne]; exact hp _ (List.getLast?_eq_some_getLast hne)
  apply eq_of_monic_of_associated (monic_of_lastL hO h2 h3 h4) (monic_normalize hP)
  rw [h1]
  exact (associated_unit_mul_left _ _ (isUnit_C.mpr (Ne.isUnit (inv_ne_zero hl)))).trans
    (normalize_associated _).symm

theorem norm_monicL {p : List α} (hp : Norm p) : Norm (monicL O p) := by
  by_cases hne : p = []
  · subst hne; simp [monicL, smulL]; exact norm_nil
  exact (monicL_spec hO hp hne).2.1

omit hO in
theorem length_monicL (p : List α) : (monicL O p).length = p.length := by simp [monicL, smulL]

/-- One division step strictly shortens the remainder. -/
theorem divStep_lt {q rem : List α} (hq : Norm q) (hq1 : lastL O q = 1) (hqne : q ≠ [])
    (hr : Norm rem) (hlen : q.length ≤ rem.length) :
    (trim O (subL O rem (shiftL O (rem.length - q.length) (smulL O (lastL O rem) q)))).length
      < rem.length := by
  have hrne : rem ≠ [] := by
    intro h; rw [h, List.length_nil] at hlen; have := List.length_pos_of_ne_nil hqne; omega
  set k := rem.length - q.length
  set c := lastL O rem
  have hc : c ≠ 0 := by
    show lastL O rem ≠ 0
    rw [lastL_eq hO hrne]; exact hr _ (List.getLast?_eq_some_getLast hrne)
  set R := toPoly rem
  set S := X ^ k * (C c * toPoly q)
  obtain ⟨hR0, hRdeg, hRlc⟩ := norm_props hr hrne
  obtain ⟨hQ0, hQdeg, hQlc⟩ := norm_props hq hqne
  have hQlc' : (toPoly q).leadingCoeff = 1 := by rw [hQlc, ← lastL_eq hO hqne, hq1]
  have hSdeg : S.degree = R.degree := by
    rw [degree_eq_natDegree hR0, hRdeg, degree_mul, degree_mul, degree_C hc, degree_X_pow,
      degree_eq_natDegree hQ0, hQdeg, zero_add]
    have := List.length_pos_of_ne_nil hqne
    norm_cast; omega
  have hSlc : S.leadingCoeff = R.leadingCoeff := by
    rw [leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_C, leadingCoeff_X_pow, hQlc', hRlc,
      ← lastL_eq hO hrne]; ring
  have hlt : (R - S).degree < R.degree := degree_sub_lt_left hSdeg.symm hR0 hSlc.symm
  set rem' := trim O (subL O rem (shiftL O k (smulL O c q)))
  have hrem' : toPoly rem' = R - S := by
    rw [toPoly_trim hO, toPoly_subL hO, toPoly_shiftL hO, toPoly_smulL hO]
  by_cases h0 : rem' = []
  · rw [h0]; simp; exact List.length_pos_of_ne_nil hrne
  · have hn' := norm_trim hO (subL O rem (shiftL O k (smulL O c q)))
    rw [norm_length_eq hn' h0, hrem']
    have hRS0 : R - S ≠ 0 := by rw [← hrem']; exact (norm_props hn' h0).1
    have := natDegree_lt_natDegree hRS0 hlt
    have := List.length_pos_of_ne_nil hrne
    have hRd : R.natDegree = rem.length - 1 := hRdeg
    omega

theorem divModAux_spec {q : List α} (hq : Norm q) (hq1 : lastL O q = 1) (hqne : q ≠ []) :
    ∀ (fuel : ℕ) (quot rem : List α), Norm rem → rem.length ≤ fuel →
      toPoly quot * toPoly q + toPoly rem =
        toPoly (divModAux O q fuel quot rem).1 * toPoly q + toPoly (divModAux O q fuel quot rem).2 ∧
      Norm (divModAux O q fuel quot rem).2 ∧ (divModAux O q fuel quot rem).2.length < q.length := by
  intro fuel
  induction fuel with
  | zero =>
    intro quot rem hr hlen
    have : rem = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    exact ⟨rfl, hr, List.length_pos_of_ne_nil hqne⟩
  | succ fuel ih =>
    intro quot rem hr hlen
    simp only [divModAux]
    split_ifs with h
    · exact ⟨rfl, hr, h⟩
    · push Not at h
      have hlt := divStep_lt hO hq hq1 hqne hr h
      obtain ⟨e1, e2, e3⟩ := ih (addL O quot (shiftL O (rem.length - q.length) [lastL O rem]))
        (trim O (subL O rem (shiftL O (rem.length - q.length) (smulL O (lastL O rem) q))))
        (norm_trim hO _) (by omega)
      refine ⟨?_, e2, e3⟩
      rw [← e1, toPoly_addL hO, toPoly_shiftL hO, toPoly_trim hO, toPoly_subL hO,
        toPoly_shiftL hO, toPoly_smulL hO]
      simp only [toPoly_cons, toPoly_nil, mul_zero, add_zero]
      ring

theorem divModL_spec {q : List α} (hq : Norm q) (hq1 : lastL O q = 1) (hqne : q ≠ [])
    (p : List α) :
    toPoly (divModL O q p).1 = toPoly p /ₘ toPoly q ∧ toPoly (divModL O q p).2 = toPoly p %ₘ toPoly q ∧
      Norm (divModL O q p).2 := by
  rw [show divModL O q p = divModAux O q p.length [] (trim O p) from rfl]
  obtain ⟨e1, e2, e3⟩ := divModAux_spec hO hq hq1 hqne p.length [] (trim O p) (norm_trim hO p)
    (length_trim_le hO p)
  rw [toPoly_nil, zero_mul, zero_add, toPoly_trim hO] at e1
  have hmon := monic_of_lastL hO hq hqne hq1
  have hdeg : (toPoly (divModL O q p).2).degree < (toPoly q).degree := by
    rw [degree_eq_natDegree (norm_props hq hqne).1, (norm_props hq hqne).2.1]
    refine lt_of_lt_of_le (degree_toPoly_lt _) ?_
    have := List.length_pos_of_ne_nil hqne
    norm_cast; rw [show divModL O q p = divModAux O q p.length [] (trim O p) from rfl]; omega
  obtain ⟨u1, u2⟩ := div_modByMonic_unique (f := toPoly p)
    (toPoly (divModAux O q p.length [] (trim O p)).1) (toPoly (divModAux O q p.length [] (trim O p)).2)
    hmon ⟨by rw [e1]; ring, hdeg⟩
  exact ⟨u1.symm, u2.symm, e2⟩

theorem modL_spec {q : List α} (hq : Norm q) (hq1 : lastL O q = 1) (hqne : q ≠ []) (p : List α) :
    toPoly (modL O p q) = toPoly p %ₘ toPoly q ∧ Norm (modL O p q) :=
  ⟨(divModL_spec hO hq hq1 hqne p).2.1, (divModL_spec hO hq hq1 hqne p).2.2⟩

omit hO in
/-- Euclid's step for the normalized gcd. -/
theorem gcd_modByMonic (A B : α[X]) :
    gcd B (A %ₘ normalize B) = gcd A B := by
  rw [modByMonic_eq_sub_mul_div]
  have hB : B ∣ normalize B := (normalize_associated B).symm.dvd
  apply dvd_antisymm_of_normalize_eq (normalize_gcd _ _) (normalize_gcd _ _)
  · apply dvd_gcd
    · have h1 : gcd B (A - normalize B * (A /ₘ normalize B)) ∣ normalize B * (A /ₘ normalize B) :=
        dvd_mul_of_dvd_left ((gcd_dvd_left _ _).trans hB) _
      have := dvd_add (gcd_dvd_right B (A - normalize B * (A /ₘ normalize B))) h1
      rwa [sub_add_cancel] at this
    · exact gcd_dvd_left _ _
  · exact dvd_gcd (gcd_dvd_right _ _)
      (dvd_sub (gcd_dvd_left _ _) (dvd_mul_of_dvd_left ((gcd_dvd_right _ _).trans hB) _))

theorem gcdAux_spec : ∀ (fuel : ℕ) (a b : List α), Norm a → Norm b → b.length < fuel →
    toPoly (gcdAux O fuel a b) = gcd (toPoly a) (toPoly b) ∧ Norm (gcdAux O fuel a b) := by
  intro fuel
  induction fuel with
  | zero => intro a b _ _ h; omega
  | succ fuel ih =>
    intro a b ha hb hlen
    simp only [gcdAux]
    split_ifs with hbe
    · have : b = [] := List.isEmpty_iff.mp hbe
      subst this
      exact ⟨by rw [toPoly_monicL hO ha, toPoly_nil, gcd_zero_right], norm_monicL hO ha⟩
    · have hbne : b ≠ [] := fun h => hbe (List.isEmpty_iff.mpr h)
      obtain ⟨m1, m2, m3, m4⟩ := monicL_spec hO hb hbne
      obtain ⟨r1, r2⟩ := modL_spec hO m2 m4 m3 a
      have hrlen : (modL O a (monicL O b)).length < b.length := by
        have := (divModAux_spec hO m2 m4 m3 a.length [] (trim O a) (norm_trim hO a)
          (length_trim_le hO a)).2.2
        rw [length_monicL] at this; exact this
      obtain ⟨g1, g2⟩ := ih b _ hb r2 (by omega)
      refine ⟨?_, g2⟩
      rw [g1, r1, toPoly_monicL hO hb, gcd_modByMonic]

theorem gcdL_spec (a b : List α) :
    toPoly (gcdL O a b) = gcd (toPoly a) (toPoly b) ∧ Norm (gcdL O a b) := by
  have := gcdAux_spec hO (b.length + 1) (trim O a) (trim O b) (norm_trim hO a) (norm_trim hO b)
    (by have := length_trim_le hO b; omega)
  rw [toPoly_trim hO, toPoly_trim hO] at this
  exact this

end divgcd


/-! ## Modular powering and the derivative -/

/-- `b^e mod m` by square-and-multiply; `e < 2^fuel` suffices (use `fuel = Nat.size e`).
Cost: `≤ 2·fuel` products and reductions mod `m`. -/
def powModAux (m : List α) : ℕ → List α → ℕ → List α
  | 0, _, _ => modL O [O.one] m
  | fuel + 1, b, e =>
    if e = 0 then modL O [O.one] m else
      let r := powModAux m fuel (modL O (mulL O b b) m) (e / 2)
      if e % 2 = 1 then modL O (mulL O r b) m else r

def powModL (b : List α) (e : ℕ) (m : List α) : List α := powModAux O m (Nat.size e) b e

/-- `k • a` by repeated addition. Cost: `k` additions. -/
def natMul : ℕ → α → α
  | 0, _ => O.zero
  | k + 1, a => O.add (natMul k a) a

def derivAux : ℕ → List α → List α
  | _, [] => []
  | k, a :: l => natMul O k a :: derivAux (k + 1) l

/-- Formal derivative. Cost: `O(n²)` additions (`O(n)` with a better `natMul`). -/
def derivL : List α → List α
  | [] => []
  | _ :: l => derivAux O 1 l

section powderiv

variable {α : Type} [Field α] [Fintype α] [DecidableEq α] {O : FOps α} (hO : Agree O)
include hO

omit hO in
theorem mod_pow_congr {M : α[X]} (hM : M.Monic) (x : α[X]) (k : ℕ) :
    (x %ₘ M) ^ k %ₘ M = x ^ k %ₘ M := by
  apply modByMonic_eq_of_dvd_sub hM
  refine dvd_trans ?_ (sub_dvd_pow_sub_pow _ _ k)
  rw [modByMonic_eq_sub_mul_div, sub_sub_cancel_left, dvd_neg]
  exact dvd_mul_right _ _

omit hO in
theorem mod_mul_congr {M : α[X]} (hM : M.Monic) (x y : α[X]) :
    (x %ₘ M * y) %ₘ M = (x * y) %ₘ M := by
  apply modByMonic_eq_of_dvd_sub hM
  rw [← sub_mul, modByMonic_eq_sub_mul_div, sub_sub_cancel_left]
  exact dvd_mul_of_dvd_left (by rw [dvd_neg]; exact dvd_mul_right _ _) _

theorem toPoly_one : toPoly [O.one] = (1 : α[X]) := by simp [hO.one]

theorem powModAux_spec {m : List α} (hm : Norm m) (hm1 : lastL O m = 1) (hmne : m ≠ []) :
    ∀ (fuel : ℕ) (b : List α) (e : ℕ), e < 2 ^ fuel →
      toPoly (powModAux O m fuel b e) = toPoly b ^ e %ₘ toPoly m ∧ Norm (powModAux O m fuel b e) := by
  have hM := monic_of_lastL hO hm hmne hm1
  intro fuel
  induction fuel with
  | zero =>
    intro b e he
    have : e = 0 := by simpa using he
    subst this
    simp only [powModAux]
    obtain ⟨h1, h2⟩ := modL_spec hO hm hm1 hmne [O.one]
    exact ⟨by rw [h1, toPoly_one hO, pow_zero], h2⟩
  | succ fuel ih =>
    intro b e he
    simp only [powModAux]
    split_ifs with h0 h1
    · subst h0
      obtain ⟨h1, h2⟩ := modL_spec hO hm hm1 hmne [O.one]
      exact ⟨by rw [h1, toPoly_one hO, pow_zero], h2⟩
    · obtain ⟨r1, r2⟩ := ih (modL O (mulL O b b) m) (e / 2) (by rw [pow_succ] at he; omega)
      obtain ⟨s1, s2⟩ := modL_spec hO hm hm1 hmne
        (mulL O (powModAux O m fuel (modL O (mulL O b b) m) (e / 2)) b)
      refine ⟨?_, s2⟩
      rw [s1, toPoly_mulL hO, r1, (modL_spec hO hm hm1 hmne _).1, toPoly_mulL hO,
        mod_pow_congr hM, mod_mul_congr hM]
      congr 1
      rw [← sq, ← pow_mul, ← pow_succ]
      congr 1; omega
    · obtain ⟨r1, r2⟩ := ih (modL O (mulL O b b) m) (e / 2) (by rw [pow_succ] at he; omega)
      refine ⟨?_, r2⟩
      rw [r1, (modL_spec hO hm hm1 hmne _).1, toPoly_mulL hO, mod_pow_congr hM, ← sq, ← pow_mul]
      congr 2; omega

theorem powModL_spec {m : List α} (hm : Norm m) (hm1 : lastL O m = 1) (hmne : m ≠ [])
    (b : List α) (e : ℕ) :
    toPoly (powModL O b e m) = toPoly b ^ e %ₘ toPoly m ∧ Norm (powModL O b e m) :=
  powModAux_spec hO hm hm1 hmne _ b e (Nat.lt_size_self e)

theorem natMul_eq (k : ℕ) (a : α) : natMul O k a = (k : α) * a := by
  induction k with
  | zero => simp [natMul, hO.zero]
  | succ k ih => simp only [natMul, ih, hO.add]; push_cast; ring

theorem toPoly_derivAux (k : ℕ) (l : List α) :
    toPoly (derivAux O k l) = C (k : α) * toPoly l + X * derivative (toPoly l) := by
  induction l generalizing k with
  | nil => simp [derivAux]
  | cons a l ih =>
    simp only [derivAux, toPoly_cons, ih, natMul_eq hO, derivative_add, derivative_C,
      derivative_mul, derivative_X, C_mul]
    push_cast
    simp only [C_add, C_1]
    ring

theorem toPoly_derivL (l : List α) : toPoly (derivL O l) = derivative (toPoly l) := by
  cases l with
  | nil => simp [derivL]
  | cons a l =>
    simp only [derivL, toPoly_derivAux hO, toPoly_cons, derivative_add, derivative_C,
      derivative_mul, derivative_X]
    push_cast; simp

end powderiv

end Mathproof.P15FactorRef20261007
