import Mathlib.Data.List.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Data.List.FinRange

/-! RECOG lane (P15, 2026-10-07): generic computable linear algebra over an abstract arithmetic
record `Ops α` (no axioms), and its naturality under operation-preserving maps.

The algorithms (all plain structural recursion / folds, polynomial in the sizes):
* `reduceBy`, `insertVec`, `rref`, `rank`: incremental reduced row echelon form;
* `freeCol`, `kerVec`: a nonzero kernel vector from a rank-deficient RREF;
* `dot`, `lincomb`, matrix product / power / trace products, zero tests.

Correctness is proved once over a genuine field (`P15RecogLinAlg20261007`), and transported to
any representation via `Ops.IsHom` (this file). -/

set_option linter.unusedSectionVars false

namespace Mathproof.P15RecogOps20261007

/-- An arithmetic record: the operations an algorithm may use. -/
structure Ops (α : Type) where
  zero : α
  one : α
  add : α → α → α
  neg : α → α
  mul : α → α → α
  inv : α → α
  isZero : α → Bool

/-- `f` commutes with all operations and with the zero test. -/
structure Ops.IsHom {α β : Type} (A : Ops α) (B : Ops β) (f : α → β) : Prop where
  zero : f A.zero = B.zero
  one : f A.one = B.one
  add : ∀ x y, f (A.add x y) = B.add (f x) (f y)
  neg : ∀ x, f (A.neg x) = B.neg (f x)
  mul : ∀ x y, f (A.mul x y) = B.mul (f x) (f y)
  inv : ∀ x, f (A.inv x) = B.inv (f x)
  isZero : ∀ x, A.isZero x = B.isZero (f x)

/-- The operations of a field with decidable equality. -/
def Ops.ofField (K : Type) [Field K] [DecidableEq K] : Ops K :=
  ⟨0, 1, (· + ·), (- ·), (· * ·), (·⁻¹), fun x => decide (x = 0)⟩

section Algorithms

variable {α : Type} (A : Ops α) {ι : Type} [DecidableEq ι]

/-- `v - c w`. -/
def axpy (v : ι → α) (c : α) (w : ι → α) : ι → α :=
  fun i => A.add (v i) (A.neg (A.mul c (w i)))

def smul (c : α) (v : ι → α) : ι → α := fun i => A.mul c (v i)

def firstNZ (idx : List ι) (v : ι → α) : Option ι := idx.find? (fun i => !A.isZero (v i))

def isZeroVec (idx : List ι) (v : ι → α) : Bool := idx.all (fun i => A.isZero (v i))

/-- Reduce `v` by a pivoted basis (pairs `(pivot, vector)`). -/
def reduceBy (bs : List (ι × (ι → α))) (v : ι → α) : ι → α :=
  bs.foldl (fun v pb => axpy A v (v pb.1) pb.2) v

/-- Insert one vector into a reduced row echelon basis. -/
def insertVec (idx : List ι) (bs : List (ι × (ι → α))) (v : ι → α) : List (ι × (ι → α)) :=
  match firstNZ A idx (reduceBy A bs v) with
  | none => bs
  | some p =>
    let r := reduceBy A bs v
    let w := smul A (A.inv (r p)) r
    bs.map (fun pb => (pb.1, axpy A pb.2 (pb.2 p) w)) ++ [(p, w)]

/-- Reduced row echelon basis of the span of `vs`. -/
def rref (idx : List ι) (vs : List (ι → α)) : List (ι × (ι → α)) :=
  vs.foldl (insertVec A idx) []

def rank (idx : List ι) (vs : List (ι → α)) : ℕ := (rref A idx vs).length

/-- A non-pivot coordinate. -/
def freeCol (idx : List ι) (bs : List (ι × (ι → α))) : Option ι :=
  idx.find? (fun i => !(bs.any (fun pb => decide (pb.1 = i))))

/-- The kernel vector attached to a free column `f`: `x_f = 1`, `x_{piv} = -b_f`, else `0`. -/
def kerVec (bs : List (ι × (ι → α))) (f : ι) : ι → α := fun i =>
  if i = f then A.one else
    match bs.find? (fun pb => decide (pb.1 = i)) with
    | some pb => A.neg (pb.2 f)
    | none => A.zero

def dot (idx : List ι) (v w : ι → α) : α :=
  idx.foldr (fun i acc => A.add (A.mul (v i) (w i)) acc) A.zero

/-- `Σ_a x_a B_a`. -/
def lincomb {κ : Type} (idxK : List κ) (x : κ → α) (B : κ → ι → α) : ι → α := fun i =>
  idxK.foldr (fun a acc => A.add (A.mul (x a) (B a i)) acc) A.zero

/-- Matrix product on `Fin n → Fin n → α`. -/
def matMul {n : ℕ} (X Y : Fin n → Fin n → α) : Fin n → Fin n → α :=
  fun i j => dot A (List.finRange n) (X i) (fun k => Y k j)

def matOne {n : ℕ} : Fin n → Fin n → α := fun i j => if i = j then A.one else A.zero

def matPow {n : ℕ} (X : Fin n → Fin n → α) : ℕ → Fin n → Fin n → α
  | 0 => matOne A
  | k + 1 => matMul A (matPow X k) X

/-- `Tr(XY) = Σ_{i,j} X_ij Y_ji`. -/
def traceMul {n : ℕ} (X Y : Fin n → Fin n → α) : α :=
  dot A (List.finRange n) (fun i => dot A (List.finRange n) (X i) (fun j => Y j i)) (fun _ => A.one)

end Algorithms

/-! ### Naturality -/

section Naturality

variable {α β : Type} {A : Ops α} {B : Ops β} {f : α → β} (hf : A.IsHom B f)
  {ι : Type} [DecidableEq ι]
include hf

def mapB (f : α → β) (bs : List (ι × (ι → α))) : List (ι × (ι → β)) :=
  bs.map (fun pb => (pb.1, f ∘ pb.2))

theorem axpy_hom (v : ι → α) (c : α) (w : ι → α) :
    f ∘ axpy A v c w = axpy B (f ∘ v) (f c) (f ∘ w) := by
  funext i; simp [axpy, hf.add, hf.neg, hf.mul]

theorem smul_hom (c : α) (v : ι → α) : f ∘ smul A c v = smul B (f c) (f ∘ v) := by
  funext i; simp [smul, hf.mul]

theorem firstNZ_hom (idx : List ι) (v : ι → α) : firstNZ A idx v = firstNZ B idx (f ∘ v) := by
  simp [firstNZ, hf.isZero]

theorem isZeroVec_hom (idx : List ι) (v : ι → α) : isZeroVec A idx v = isZeroVec B idx (f ∘ v) := by
  simp [isZeroVec, hf.isZero]

theorem reduceBy_hom (bs : List (ι × (ι → α))) (v : ι → α) :
    f ∘ reduceBy A bs v = reduceBy B (mapB f bs) (f ∘ v) := by
  induction bs generalizing v with
  | nil => rfl
  | cons pb bs ih =>
    simp only [reduceBy, List.foldl_cons, mapB, List.map_cons] at ih ⊢
    rw [ih, axpy_hom hf]
    rfl

theorem insertVec_hom (idx : List ι) (bs : List (ι × (ι → α))) (v : ι → α) :
    mapB f (insertVec A idx bs v) = insertVec B idx (mapB f bs) (f ∘ v) := by
  unfold insertVec
  rw [firstNZ_hom hf, reduceBy_hom hf]
  cases firstNZ B idx (reduceBy B (mapB f bs) (f ∘ v)) with
  | none => rfl
  | some p =>
    simp only [mapB, List.map_append, List.map_map, List.map_cons, List.map_nil]
    congr 1
    · apply List.map_congr_left
      intro pb _
      have hr : f (reduceBy A bs v p) = reduceBy B (mapB f bs) (f ∘ v) p :=
        congrFun (reduceBy_hom hf bs v) p
      simp only [Function.comp_apply, Prod.mk.injEq, true_and]
      rw [axpy_hom hf, smul_hom hf, hf.inv, hr, reduceBy_hom hf]
      rfl
    · have hr : f (reduceBy A bs v p) = reduceBy B (mapB f bs) (f ∘ v) p :=
        congrFun (reduceBy_hom hf bs v) p
      simp only [Prod.mk.injEq, true_and, List.cons.injEq, and_true]
      rw [smul_hom hf, hf.inv, hr, reduceBy_hom hf]
      rfl

theorem rref_hom (idx : List ι) (vs : List (ι → α)) :
    mapB f (rref A idx vs) = rref B idx (vs.map (f ∘ ·)) := by
  unfold rref
  suffices H : ∀ bs : List (ι × (ι → α)),
      mapB f (vs.foldl (insertVec A idx) bs) = (vs.map (f ∘ ·)).foldl (insertVec B idx) (mapB f bs)
    from H []
  induction vs with
  | nil => intro bs; rfl
  | cons v vs ih =>
    intro bs
    simp only [List.foldl_cons, List.map_cons]
    rw [ih, insertVec_hom hf]

theorem rank_hom (idx : List ι) (vs : List (ι → α)) :
    rank A idx vs = rank B idx (vs.map (f ∘ ·)) := by
  unfold rank
  rw [← rref_hom hf, mapB, List.length_map]

theorem freeCol_hom (idx : List ι) (bs : List (ι × (ι → α))) :
    freeCol idx bs = freeCol idx (mapB f bs) := by
  simp [freeCol, mapB, Function.comp_def]

theorem kerVec_hom (bs : List (ι × (ι → α))) (c : ι) :
    f ∘ kerVec A bs c = kerVec B (mapB f bs) c := by
  funext i
  simp only [Function.comp_apply, kerVec, mapB]
  by_cases hi : i = c
  · simp [hi, hf.one]
  · simp only [hi, if_false, List.find?_map]
    cases h : bs.find? (fun pb => decide (pb.1 = i)) with
    | none =>
      have : bs.find? ((fun pb : ι × (ι → β) => decide (pb.1 = i)) ∘
          (fun pb : ι × (ι → α) => (pb.1, f ∘ pb.2))) = none := by
        simpa [Function.comp_def] using h
      simp [this, hf.zero]
    | some pb =>
      have : bs.find? ((fun pb : ι × (ι → β) => decide (pb.1 = i)) ∘
          (fun pb : ι × (ι → α) => (pb.1, f ∘ pb.2))) = some pb := by
        simpa [Function.comp_def] using h
      simp [this, hf.neg]

theorem dot_hom (idx : List ι) (v w : ι → α) : f (dot A idx v w) = dot B idx (f ∘ v) (f ∘ w) := by
  induction idx with
  | nil => simp [dot, hf.zero]
  | cons i idx ih =>
    simp only [dot, List.foldr_cons] at ih ⊢
    rw [hf.add, hf.mul, ih]; rfl

theorem lincomb_hom {κ : Type} (idxK : List κ) (x : κ → α) (Bv : κ → ι → α) :
    f ∘ lincomb A idxK x Bv = lincomb B idxK (f ∘ x) (fun a => f ∘ Bv a) := by
  funext i
  simp only [Function.comp_apply, lincomb]
  induction idxK with
  | nil => simp [hf.zero]
  | cons a idxK ih =>
    simp only [List.foldr_cons]
    rw [hf.add, hf.mul, ih]

theorem matMul_hom {n : ℕ} (X Y : Fin n → Fin n → α) :
    (fun i j => f (matMul A X Y i j)) = matMul B (fun i j => f (X i j)) (fun i j => f (Y i j)) := by
  funext i j
  simp only [matMul]
  rw [dot_hom hf]; rfl

theorem matPow_hom {n : ℕ} (X : Fin n → Fin n → α) (k : ℕ) :
    (fun i j => f (matPow A X k i j)) = matPow B (fun i j => f (X i j)) k := by
  induction k with
  | zero =>
    funext i j
    simp only [matPow, matOne]
    split_ifs <;> simp [hf.one, hf.zero]
  | succ k ih =>
    simp only [matPow]
    rw [matMul_hom hf, ih]

theorem traceMul_hom {n : ℕ} (X Y : Fin n → Fin n → α) :
    f (traceMul A X Y) = traceMul B (fun i j => f (X i j)) (fun i j => f (Y i j)) := by
  simp only [traceMul]
  rw [dot_hom hf]
  congr 1
  · funext i; simp only [Function.comp_apply]; rw [dot_hom hf]; rfl
  · funext i; simp [hf.one]

end Naturality

end Mathproof.P15RecogOps20261007
