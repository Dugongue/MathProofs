import Mathproof.MinimumGenerationRankFormulaAddress

namespace Mathproof.MinimumGeneration.RankBerkowitz.Formula

/-- A digit representation and its word operations. Child operands are
sampled through their individual bits. -/
structure BitOperations (R Addr : Type*) [CommRing R] where
  encode : R → Addr → Bool
  zero : Addr → Bool
  one : Addr → Bool
  add : (Addr → Bool) → (Addr → Bool) → Addr → Bool
  mul : (Addr → Bool) → (Addr → Bool) → Addr → Bool
  sub : (Addr → Bool) → (Addr → Bool) → Addr → Bool
  zero_exact : zero = encode 0
  one_exact : one = encode 1
  add_exact : ∀ x y, add (encode x) (encode y) = encode (x+y)
  mul_exact : ∀ x y, mul (encode x) (encode y) = encode (x*y)
  sub_exact : ∀ x y, sub (encode x) (encode y) = encode (x-y)

namespace BitOperations

variable {R Addr : Type*} [CommRing R] (C : BitOperations R Addr)

def nodeBits (read : Nat → Nat → Addr → Bool) (child : Bool → Addr → Bool) :
    Option Node → Addr → Bool
  | some .zero => C.zero
  | some .one => C.one
  | some (.input i j) => read i j
  | some .add => C.add (child false) (child true)
  | some .mul => C.mul (child false) (child true)
  | some .sub => C.sub (child false) (child true)
  | none => fun _ => false

/-- Evaluate one bit directly by a gate locator. The function recurses on a
bounded address path and its arithmetic callbacks get only bit accessors. -/
def evalAt (lookup : Locator) (read : Nat → Nat → Addr → Bool) : Nat → List Bool → Addr → Bool
  | 0, path => C.nodeBits read (fun _ _ => false) (lookup path)
  | depth+1, path =>
    C.nodeBits read (fun side digit => evalAt lookup read depth (path ++ [side]) digit)
      (lookup path)

theorem evalAt_exact (lookup : Locator) (read : Nat → Nat → Addr → Bool)
    (value : Nat → Nat → R) (hRead : ∀ i j, read i j = C.encode (value i j))
    (e : Expr) (fuel : Nat) (root : List Bool)
    (hGate : ∀ path, lookup (root ++ path) = e.nodeAt path) (hFuel : e.depth ≤ fuel) :
    C.evalAt lookup read fuel root = C.encode (e.eval value) := by
  have hRoot : lookup root = e.nodeAt [] := by simpa only [List.append_nil] using hGate []
  induction e generalizing fuel root with
  | zero => cases fuel <;> simp [evalAt,nodeBits,hRoot,Expr.nodeAt,Expr.eval,C.zero_exact]
  | one => cases fuel <;> simp [evalAt,nodeBits,hRoot,Expr.nodeAt,Expr.eval,C.one_exact]
  | input i j => cases fuel <;> simp [evalAt,nodeBits,hRoot,Expr.nodeAt,Expr.eval,hRead]
  | add l r il ir | mul l r il ir | sub l r il ir =>
    cases fuel with
    | zero => have := hFuel; simp [Expr.depth] at this
    | succ f =>
      have hMax : max l.depth r.depth ≤ f := Nat.le_of_succ_le_succ hFuel
      have hl : C.evalAt lookup read f (root ++ [false]) = C.encode (l.eval value) := by
        apply il
        · intro path
          rw [List.append_assoc,hGate]
          rfl
        · exact (Nat.le_max_left _ _).trans hMax
        · exact hGate [false]
      have hr : C.evalAt lookup read f (root ++ [true]) = C.encode (r.eval value) := by
        apply ir
        · intro path
          rw [List.append_assoc,hGate]
          rfl
        · exact (Nat.le_max_right _ _).trans hMax
        · exact hGate [true]
      simp [evalAt,nodeBits,hRoot,Expr.nodeAt,Expr.eval,hl,hr,
        C.add_exact,C.mul_exact,C.sub_exact]

def coefficientBudget (n : Nat) : Nat :=
  factorDepth n+n.size*((n+1).size+1)

def coefficientBit {n : Nat} (d : Fin (n+1)) (read : Nat → Nat → Addr → Bool) : Addr → Bool :=
  C.evalAt (coefficientNode n d) read (coefficientBudget n) []

/-- The addressed bit evaluator returns the exact characteristic coefficient.
This identifies the operation used by one weighted grid probe. -/
theorem coefficientBit_exact {n : Nat} (A : Matrix (Fin n) (Fin n) R)
    (d : Fin (n+1)) (read : Nat → Nat → Addr → Bool)
    (hRead : ∀ i j, read i j = C.encode (Berkowitz.matrixSource A i j)) :
    C.coefficientBit d read = C.encode (A.charpoly.coeff d.val) := by
  have he := C.evalAt_exact (coefficientNode n d) read (Berkowitz.matrixSource A) hRead
    (coefficientTerm n d) (coefficientBudget n) []
    (by intro path; exact coefficientNode_exact n d path) (coefficientTerm_depth n d)
  rw [coefficientTerm_eval] at he
  exact he
end BitOperations
end Mathproof.MinimumGeneration.RankBerkowitz.Formula
