import Mathproof.MinimumGenerationRankCoefficientFormula

namespace Mathproof.MinimumGeneration.RankBerkowitz.Formula

inductive Node
  | zero
  | one
  | input (row column : Nat)
  | add
  | mul
  | sub

/-- Meaning of a root-to-node path in the coefficient formula. -/
def Expr.nodeAt : Expr → List Bool → Option Node
  | .zero, [] => some .zero
  | .one, [] => some .one
  | .input i j, [] => some (.input i j)
  | .add _ _, [] => some .add
  | .mul _ _, [] => some .mul
  | .sub _ _, [] => some .sub
  | .add l r, b::bs | .mul l r, b::bs | .sub l r, b::bs =>
    if b then r.nodeAt bs else l.nodeAt bs
  | _, _::_ => none

abbrev Locator := List Bool → Option Node

def leaf (tag : Node) : Locator
  | [] => some tag
  | _::_ => none

def branch (tag : Node) (left right : Locator) : Locator
  | [] => some tag
  | b::bs => if b then right bs else left bs

def intervalNode (term : Nat → Locator) : Nat → Nat → List Bool → Option Node
  | 0, start, path => term start path
  | _+1, _, [] => some .add
  | h+1, start, false::path => intervalNode term h start path
  | h+1, start, true::path => intervalNode term h (start+2^h) path

private theorem intervalNode_eq {term : Nat → Locator} {tree : Nat → Expr}
    (ht : ∀ i path, term i path = (tree i).nodeAt path) (h start : Nat) (path : List Bool) :
    intervalNode term h start path = (intervalSum tree h start).nodeAt path := by
  induction h generalizing start path with
  | zero => exact ht _ _
  | succ h ih =>
    cases path with
    | nil => rfl
    | cons b bs => cases b <;> simp [intervalNode, intervalSum, branch, Expr.nodeAt, ih]

def sumNode {n : Nat} (term : Fin n → Locator) : Locator :=
  intervalNode (fun i => if hi : i < n then term ⟨i,hi⟩ else leaf .zero) n.size 0

private theorem sumNode_eq {n : Nat} {term : Fin n → Locator} {tree : Fin n → Expr}
    (h : ∀ i path, term i path = (tree i).nodeAt path) (path : List Bool) :
    sumNode term path = (finiteSum tree).nodeAt path := by
  apply intervalNode_eq
  intro i path
  by_cases hi : i < n
  · simp [hi,h]
  · cases path <;> simp [hi,leaf,Expr.nodeAt]

def deltaNode {n : Nat} (i j : Fin n) : Locator :=
  leaf (if i=j then .one else .zero)

private theorem deltaNode_eq {n : Nat} (i j : Fin n) (path : List Bool) :
    deltaNode i j path = (delta i j).nodeAt path := by
  by_cases h : i=j <;> cases path <;> simp [deltaNode,delta,h,leaf,Expr.nodeAt]

/-- Navigate a product entry using cursor arithmetic and the chosen
path. This operation traverses no sibling subformula. -/
def productNode {n : Nat} (factor : Nat → Fin n → Fin n → Locator) :
    Nat → Nat → Nat → Fin n → Fin n → List Bool → Option Node
  | 0, s, e, i, j, path =>
    if e=0 then deltaNode i j path else if e=1 then factor s i j path else leaf .zero path
  | h+1, s, e, i, j, path =>
    if e=0 then deltaNode i j path else if e=1 then factor s i j path
    else sumNode (fun k p =>
      match p with
      | [] => some .mul
      | false::ps => productNode factor h s (e/2) i k ps
      | true::ps => productNode factor h (s+e/2) (e-e/2) k j ps) path

theorem productNode_eq {n : Nat}
    {factor : Nat → Fin n → Fin n → Locator} {tree : Nat → Fin n → Fin n → Expr}
    (hFactor : ∀ s i j path, factor s i j path = (tree s i j).nodeAt path)
    (h s e : Nat) (i j : Fin n) (path : List Bool) :
    productNode factor h s e i j path = (productEntry tree h s e i j).nodeAt path := by
  induction h generalizing s e i j path with
  | zero =>
    by_cases hz : e=0
    · simp [productNode,productEntry,hz,deltaNode_eq]
    by_cases ho : e=1
    · simp [productNode,productEntry,ho,hFactor]
    cases path <;> simp [productNode,productEntry,hz,ho,leaf,Expr.nodeAt]
  | succ h ih =>
    by_cases hz : e=0
    · simp [productNode,productEntry,hz,deltaNode_eq]
    by_cases ho : e=1
    · simp [productNode,productEntry,ho,hFactor]
    simp only [productNode,productEntry,hz,ho,if_false]
    apply sumNode_eq
    intro k path
    cases path with
    | nil => rfl
    | cons b bs => cases b <;> simp [branch,Expr.nodeAt,ih]

def powerNode {n : Nat} (off e : Nat) (i j : Fin n) : Locator :=
  productNode (fun _ a b => leaf (.input (a.val+off) (b.val+off))) e.size 0 e i j

theorem powerNode_eq {n : Nat} (off e : Nat) (i j : Fin n) (path : List Bool) :
    powerNode off e i j path = (powerTerm off e i j).nodeAt path := by
  apply productNode_eq
  intro s r c p
  cases p <;> rfl

def momentNode (off n e : Nat) : Locator :=
  sumNode fun i : Fin n =>
    sumNode fun j : Fin n =>
      branch .mul (leaf (.input off (i.val+off+1)))
        (branch .mul (fun p => powerNode (off+1) e i j p) (leaf (.input (j.val+off+1) off)))

theorem momentNode_eq (off n e : Nat) (path : List Bool) :
    momentNode off n e path = (momentTerm off n e).nodeAt path := by
  apply sumNode_eq
  intro i p
  apply sumNode_eq
  intro j q
  cases q with
  | nil => rfl
  | cons b bs =>
    cases b
    · cases bs <;> rfl
    · cases bs with
      | nil => rfl
      | cons c cs =>
        cases c
        · exact powerNode_eq _ _ _ _ _
        · cases cs <;> rfl

def factorNode {w : Nat} (n off stage : Nat) (d k : Fin w) : Locator :=
  if stage<n then
    let anchor := off+stage
    let tail := n-stage-1
    branch .sub (branch .sub (leaf (if k.val+1=d.val then .one else .zero))
      (leaf (if k.val=d.val then .input anchor anchor else .zero)))
      (if d.val<k.val ∧ k.val≤tail then (fun p => momentNode anchor tail (k.val-(d.val+1)) p)
       else leaf .zero)
  else deltaNode d k

theorem factorNode_eq {w : Nat} (n off stage : Nat) (d k : Fin w) (path : List Bool) :
    factorNode n off stage d k path = (factorTerm n off stage d k).nodeAt path := by
  by_cases hs : stage<n
  · simp only [factorNode,factorTerm,hs,if_true]
    cases path with
    | nil => rfl
    | cons b bs =>
      cases b
      · cases bs with
        | nil => rfl
        | cons c cs =>
          cases c <;> cases cs <;> split_ifs <;> rfl
      · simp only [branch,Expr.nodeAt,if_true]
        split_ifs
        · exact momentNode_eq _ _ _ _
        · cases bs <;> rfl
  · simp [factorNode,factorTerm,hs,deltaNode_eq]

def coefficientNode (n : Nat) (d : Fin (n+1)) : Locator :=
  productNode (factorNode n 0) n.size 0 n d 0

/-- Every local address returns exactly the corresponding coefficient-formula
node without constructing the arithmetic formula. -/
theorem coefficientNode_exact (n : Nat) (d : Fin (n+1)) (path : List Bool) :
    coefficientNode n d path = (coefficientTerm n d).nodeAt path :=
  productNode_eq (factorNode_eq n 0) _ _ _ _ _ _

private theorem nodeAt_length {e : Expr} (path : List Bool) (v : Node)
    (h : e.nodeAt path = some v) : path.length ≤ e.depth := by
  induction e generalizing path with
  | zero | one | input => cases path <;> simp_all [Expr.nodeAt,Expr.depth]
  | add l r il ir | mul l r il ir | sub l r il ir =>
    cases path with
    | nil => simp
    | cons b bs =>
      cases b
      · have hl := il bs (by simpa only [Expr.nodeAt, if_false, Bool.false_eq_true] using h)
        exact Nat.succ_le_succ (hl.trans (Nat.le_max_left _ _))
      · have hr := ir bs (by simpa only [Expr.nodeAt, if_true] using h)
        exact Nat.succ_le_succ (hr.trans (Nat.le_max_right _ _))

theorem coefficientNode_path_bound (n : Nat) (d : Fin (n+1)) (path : List Bool)
    (v : Node) (h : coefficientNode n d path = some v) :
    path.length ≤ factorDepth n+n.size*((n+1).size+1) :=
  (nodeAt_length path v ((coefficientNode_exact n d path).symm.trans h)).trans
    (coefficientTerm_depth n d)
end Mathproof.MinimumGeneration.RankBerkowitz.Formula
