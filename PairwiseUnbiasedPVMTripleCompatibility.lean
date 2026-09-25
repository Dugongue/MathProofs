import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue

/-!
# Compatibility of triples of pairwise mutually unbiased projective measurements

Let `P`, `Q`, and `R` be arbitrary-rank projective measurements with `n > 0`
outcomes on a finite-dimensional complex space. If every ordered pair satisfies
the operator mutual-unbiasedness equations, this file constructs an explicit
positive normalized parent whose marginals dominate `(1 + x) / 3` times the
corresponding projections, where `x` is the unique positive root of
`n^2 * x^3 - 3 * n * x - 2 = 0`. For `n = 4`, `x = cos (pi / 9)`.

This proves the pairwise-unbiased special case of Conjecture 10(3,4) in
Sebastien Designolle and Mate Farkas, "k-fold unbiased measurements and maximal
incompatibility", arXiv:2609.20728v1 (2026). It does not prove that conjecture
for arbitrary triples of PVMs.

For ordinary rank-one MUB triples in every fixed dimension `n >= 3`, the same
explicit parent works at a strictly larger visibility. A single positive
increment is proved to work uniformly over all such triples in that fixed
dimension. This strengthens the `(1 + x) / 3` benchmark for this rank-one MUB
subclass, but gives no numerical increment and no increment uniform in `n`.
The one-anchor obstruction used for strictness is the argument in Appendix B,
proof of Theorem 4, of the cited paper.

The file imports only Mathlib. Every definition, algebraic moment identity,
positivity certificate, basis-to-projector bridge, and compactness argument
needed by the exported theorems is included below.
-/

open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.style.haveILetI false

namespace MUMSpectral

abbrev Mat (D : ℕ) := Matrix (Fin D) (Fin D) ℂ

structure PVM (n D : ℕ) where
  proj : Fin n → Mat D
  isProj : ∀ a, IsStarProjection (proj a)
  orthogonal : ∀ a b, a ≠ b → proj a * proj b = 0
  complete : ∑ a, proj a = 1

def Unbiased {n D : ℕ} (P Q : PVM n D) : Prop :=
  (∀ a b, P.proj a * Q.proj b * P.proj a = (n : ℝ)⁻¹ • P.proj a) ∧
  (∀ a b, Q.proj b * P.proj a * Q.proj b = (n : ℝ)⁻¹ • Q.proj b)

theorem PVM.proj_nonneg {n D : ℕ} (P : PVM n D) (a : Fin n) : 0 ≤ P.proj a :=
  (P.isProj a).nonneg

theorem PVM.sum_proj_mul {n D : ℕ} (P : PVM n D) (X : Mat D) :
    ∑ a, P.proj a * X = X := by
  rw [← Finset.sum_mul, P.complete, one_mul]

theorem PVM.sum_mul_proj {n D : ℕ} (P : PVM n D) (X : Mat D) :
    ∑ a, X * P.proj a = X := by
  rw [← Finset.mul_sum, P.complete, mul_one]

theorem Unbiased.symm {n D : ℕ} {P Q : PVM n D} (h : Unbiased P Q) :
    Unbiased Q P := ⟨fun b a => h.2 a b, fun b a => h.1 a b⟩

end MUMSpectral

namespace MUMPowerReduction
variable {A : Type*} [Ring A] [Algebra ℝ A]
variable (p q r : A) (t : ℝ)
variable (hp : p*p=p) (hq : q*q=q) (hr : r*r=r)
variable (hpq : p*q*p=t • p) (hpr : p*r*p=t • p)
variable (hqp : q*p*q=t • q) (hqr : q*r*q=t • q)
variable (hrp : r*p*r=t • r) (hrq : r*q*r=t • r)

private theorem hpptail (x : A) (ha : p*p=p) : p*(p*x)=p*x := by
  rw [← mul_assoc, ha]

private theorem hqqtail (x : A) (ha : q*q=q) : q*(q*x)=q*x := by
  rw [← mul_assoc, ha]

private theorem hrrtail (x : A) (ha : r*r=r) : r*(r*x)=r*x := by
  rw [← mul_assoc, ha]

private theorem hpqptail (x : A) (ha : p*q*p=t • p) :
    p*(q*(p*x))=t • (p*x) := by
  rw [← mul_assoc, ← mul_assoc, ha, smul_mul_assoc]

private theorem hprptail (x : A) (ha : p*r*p=t • p) :
    p*(r*(p*x))=t • (p*x) := by
  rw [← mul_assoc, ← mul_assoc, ha, smul_mul_assoc]

private theorem hqpqtail (x : A) (ha : q*p*q=t • q) :
    q*(p*(q*x))=t • (q*x) := by
  rw [← mul_assoc, ← mul_assoc, ha, smul_mul_assoc]

private theorem hqrqtail (x : A) (ha : q*r*q=t • q) :
    q*(r*(q*x))=t • (q*x) := by
  rw [← mul_assoc, ← mul_assoc, ha, smul_mul_assoc]

private theorem hrprtail (x : A) (ha : r*p*r=t • r) :
    r*(p*(r*x))=t • (r*x) := by
  rw [← mul_assoc, ← mul_assoc, ha, smul_mul_assoc]

private theorem hrqrtail (x : A) (ha : r*q*r=t • r) :
    r*(q*(r*x))=t • (r*x) := by
  rw [← mul_assoc, ← mul_assoc, ha, smul_mul_assoc]

include hp hq hr hpq hpr hqp hqr hrp hrq

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8000 in
theorem power_1 : (p+q+r)^1 =
    (1 : ℝ) • (p) +
    (1 : ℝ) • (q) +
    (1 : ℝ) • (r) := by
  simp only [pow_succ,
    pow_zero,
    mul_one,
    one_mul,
    add_mul,
    mul_add,
    mul_assoc,
    smul_mul_assoc,
    mul_smul_comm,
    smul_smul,
    hp,
    hq,
    hr,
    hpptail p _ hp,
    hqqtail q _ hq,
    hrrtail r _ hr,
    hpqptail p q t _ hpq,
    show p*(q*p)=t • p by simpa only [mul_assoc] using hpq,
    hprptail p r t _ hpr,
    show p*(r*p)=t • p by simpa only [mul_assoc] using hpr,
    hqpqtail p q t _ hqp,
    show q*(p*q)=t • q by simpa only [mul_assoc] using hqp,
    hqrqtail q r t _ hqr,
    show q*(r*q)=t • q by simpa only [mul_assoc] using hqr,
    hrprtail p r t _ hrp,
    show r*(p*r)=t • r by simpa only [mul_assoc] using hrp,
    hrqrtail q r t _ hrq,
    show r*(q*r)=t • r by simpa only [mul_assoc] using hrq]
  module

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8000 in
theorem power_2 : (p+q+r)^2 =
    (1 : ℝ) • (p) +
    (1 : ℝ) • (q) +
    (1 : ℝ) • (r) +
    (1 : ℝ) • (p*q) +
    (1 : ℝ) • (p*r) +
    (1 : ℝ) • (q*p) +
    (1 : ℝ) • (q*r) +
    (1 : ℝ) • (r*p) +
    (1 : ℝ) • (r*q) := by
  simp only [pow_succ,
    pow_zero,
    mul_one,
    one_mul,
    add_mul,
    mul_add,
    mul_assoc,
    smul_mul_assoc,
    mul_smul_comm,
    smul_smul,
    hp,
    hq,
    hr,
    hpptail p _ hp,
    hqqtail q _ hq,
    hrrtail r _ hr,
    hpqptail p q t _ hpq,
    show p*(q*p)=t • p by simpa only [mul_assoc] using hpq,
    hprptail p r t _ hpr,
    show p*(r*p)=t • p by simpa only [mul_assoc] using hpr,
    hqpqtail p q t _ hqp,
    show q*(p*q)=t • q by simpa only [mul_assoc] using hqp,
    hqrqtail q r t _ hqr,
    show q*(r*q)=t • q by simpa only [mul_assoc] using hqr,
    hrprtail p r t _ hrp,
    show r*(p*r)=t • r by simpa only [mul_assoc] using hrp,
    hrqrtail q r t _ hrq,
    show r*(q*r)=t • r by simpa only [mul_assoc] using hrq]
  module

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8000 in
theorem power_3 : (p+q+r)^3 =
    (1+2*t^1 : ℝ) • (p) +
    (1+2*t^1 : ℝ) • (q) +
    (1+2*t^1 : ℝ) • (r) +
    (2 : ℝ) • (p*q) +
    (2 : ℝ) • (p*r) +
    (2 : ℝ) • (q*p) +
    (2 : ℝ) • (q*r) +
    (2 : ℝ) • (r*p) +
    (2 : ℝ) • (r*q) +
    (1 : ℝ) • (p*q*r) +
    (1 : ℝ) • (p*r*q) +
    (1 : ℝ) • (q*p*r) +
    (1 : ℝ) • (q*r*p) +
    (1 : ℝ) • (r*p*q) +
    (1 : ℝ) • (r*q*p) := by
  simp only [pow_succ,
    pow_zero,
    mul_one,
    one_mul,
    add_mul,
    mul_add,
    mul_assoc,
    smul_mul_assoc,
    mul_smul_comm,
    smul_smul,
    hp,
    hq,
    hr,
    hpptail p _ hp,
    hqqtail q _ hq,
    hrrtail r _ hr,
    hpqptail p q t _ hpq,
    show p*(q*p)=t • p by simpa only [mul_assoc] using hpq,
    hprptail p r t _ hpr,
    show p*(r*p)=t • p by simpa only [mul_assoc] using hpr,
    hqpqtail p q t _ hqp,
    show q*(p*q)=t • q by simpa only [mul_assoc] using hqp,
    hqrqtail q r t _ hqr,
    show q*(r*q)=t • q by simpa only [mul_assoc] using hqr,
    hrprtail p r t _ hrp,
    show r*(p*r)=t • r by simpa only [mul_assoc] using hrp,
    hrqrtail q r t _ hrq,
    show r*(q*r)=t • r by simpa only [mul_assoc] using hrq]
  module

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8000 in
theorem power_4 : (p+q+r)^4 =
    (1+6*t^1 : ℝ) • (p) +
    (1+6*t^1 : ℝ) • (q) +
    (1+6*t^1 : ℝ) • (r) +
    (3+3*t^1 : ℝ) • (p*q) +
    (3+3*t^1 : ℝ) • (p*r) +
    (3+3*t^1 : ℝ) • (q*p) +
    (3+3*t^1 : ℝ) • (q*r) +
    (3+3*t^1 : ℝ) • (r*p) +
    (3+3*t^1 : ℝ) • (r*q) +
    (3 : ℝ) • (p*q*r) +
    (3 : ℝ) • (p*r*q) +
    (3 : ℝ) • (q*p*r) +
    (3 : ℝ) • (q*r*p) +
    (3 : ℝ) • (r*p*q) +
    (3 : ℝ) • (r*q*p) +
    (1 : ℝ) • (p*q*r*p) +
    (1 : ℝ) • (p*r*q*p) +
    (1 : ℝ) • (q*p*r*q) +
    (1 : ℝ) • (q*r*p*q) +
    (1 : ℝ) • (r*p*q*r) +
    (1 : ℝ) • (r*q*p*r) := by
  simp only [pow_succ,
    pow_zero,
    mul_one,
    one_mul,
    add_mul,
    mul_add,
    mul_assoc,
    smul_mul_assoc,
    mul_smul_comm,
    smul_smul,
    hp,
    hq,
    hr,
    hpptail p _ hp,
    hqqtail q _ hq,
    hrrtail r _ hr,
    hpqptail p q t _ hpq,
    show p*(q*p)=t • p by simpa only [mul_assoc] using hpq,
    hprptail p r t _ hpr,
    show p*(r*p)=t • p by simpa only [mul_assoc] using hpr,
    hqpqtail p q t _ hqp,
    show q*(p*q)=t • q by simpa only [mul_assoc] using hqp,
    hqrqtail q r t _ hqr,
    show q*(r*q)=t • q by simpa only [mul_assoc] using hqr,
    hrprtail p r t _ hrp,
    show r*(p*r)=t • r by simpa only [mul_assoc] using hrp,
    hrqrtail q r t _ hrq,
    show r*(q*r)=t • r by simpa only [mul_assoc] using hrq]
  module

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8000 in
theorem power_5 : (p+q+r)^5 =
    (1+12*t^1+6*t^2 : ℝ) • (p) +
    (1+12*t^1+6*t^2 : ℝ) • (q) +
    (1+12*t^1+6*t^2 : ℝ) • (r) +
    (4+12*t^1 : ℝ) • (p*q) +
    (4+12*t^1 : ℝ) • (p*r) +
    (4+12*t^1 : ℝ) • (q*p) +
    (4+12*t^1 : ℝ) • (q*r) +
    (4+12*t^1 : ℝ) • (r*p) +
    (4+12*t^1 : ℝ) • (r*q) +
    (6+4*t^1 : ℝ) • (p*q*r) +
    (6+4*t^1 : ℝ) • (p*r*q) +
    (6+4*t^1 : ℝ) • (q*p*r) +
    (6+4*t^1 : ℝ) • (q*r*p) +
    (6+4*t^1 : ℝ) • (r*p*q) +
    (6+4*t^1 : ℝ) • (r*q*p) +
    (4 : ℝ) • (p*q*r*p) +
    (4 : ℝ) • (p*r*q*p) +
    (4 : ℝ) • (q*p*r*q) +
    (4 : ℝ) • (q*r*p*q) +
    (4 : ℝ) • (r*p*q*r) +
    (4 : ℝ) • (r*q*p*r) +
    (1 : ℝ) • (p*q*r*p*q) +
    (1 : ℝ) • (p*r*q*p*r) +
    (1 : ℝ) • (q*p*r*q*p) +
    (1 : ℝ) • (q*r*p*q*r) +
    (1 : ℝ) • (r*p*q*r*p) +
    (1 : ℝ) • (r*q*p*r*q) := by
  simp only [pow_succ,
    pow_zero,
    mul_one,
    one_mul,
    add_mul,
    mul_add,
    mul_assoc,
    smul_mul_assoc,
    mul_smul_comm,
    smul_smul,
    hp,
    hq,
    hr,
    hpptail p _ hp,
    hqqtail q _ hq,
    hrrtail r _ hr,
    hpqptail p q t _ hpq,
    show p*(q*p)=t • p by simpa only [mul_assoc] using hpq,
    hprptail p r t _ hpr,
    show p*(r*p)=t • p by simpa only [mul_assoc] using hpr,
    hqpqtail p q t _ hqp,
    show q*(p*q)=t • q by simpa only [mul_assoc] using hqp,
    hqrqtail q r t _ hqr,
    show q*(r*q)=t • q by simpa only [mul_assoc] using hqr,
    hrprtail p r t _ hrp,
    show r*(p*r)=t • r by simpa only [mul_assoc] using hrp,
    hrqrtail q r t _ hrq,
    show r*(q*r)=t • r by simpa only [mul_assoc] using hrq]
  module

end MUMPowerReduction

section
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator ComplexOrder
open Matrix MUMSpectral

namespace MUMCompatibility
noncomputable section

def selected {n D : ℕ} (P Q R : PVM n D) (a b c : Fin n) : Mat D :=
  P.proj a + Q.proj b + R.proj c

def polyQ (n : ℕ) (x : ℝ) {D : ℕ} (S : Mat D) : Mat D :=
  S^2 + (x-2) • S + (x^2-x+1-3/(n:ℝ)) • (1 : Mat D)

def rawParent (n : ℕ) (x : ℝ) {D : ℕ} (S : Mat D) : Mat D :=
  S * (polyQ n x S)^2

def denom (n : ℕ) (x : ℝ) : ℝ := ((n:ℝ)+2)*x^2+6*x+1+2/(n:ℝ)
def scale (n : ℕ) (x : ℝ) : ℝ := 1/(9*denom n x)
def coeffU (n : ℕ) (x : ℝ) : ℝ := 3*((n:ℝ)+6)*x^2+30*x+3+8/(n:ℝ)
def coeffV (n : ℕ) (x : ℝ) : ℝ := 6*x^2+24*x/(n:ℝ)+6/(n:ℝ)+8/(n:ℝ)^2
def coeffC (n : ℕ) (x : ℝ) : ℝ := 6*x^2+24*x/(n:ℝ)+4/(n:ℝ)+8/(n:ℝ)^2

def rootEquation (n : ℕ) (x : ℝ) : Prop := (n:ℝ)^2*x^3-3*(n:ℝ)*x-2=0

def parent {n D : ℕ} (P Q R : PVM n D) (x : ℝ) (a b c : Fin n) : Mat D :=
  scale n x • rawParent n x (selected P Q R a b c)

def cycleZ {n D : ℕ} (P Q R : PVM n D) (a : Fin n) : Mat D :=
  ∑ b, ∑ c, (Q.proj b*R.proj c*P.proj a*Q.proj b*R.proj c +
    R.proj c*Q.proj b*P.proj a*R.proj c*Q.proj b)

def amplitudeH {n D : ℕ} (P Q R : PVM n D) (a b c : Fin n) : Mat D :=
  P.proj a*(Q.proj b*R.proj c+R.proj c*Q.proj b)-(2/(n:ℝ)^2) • P.proj a

def IsParent {n D : ℕ} (P Q R : PVM n D) (eta : ℝ)
    (G : Fin n → Fin n → Fin n → Mat D) : Prop :=
  (∀ a b c, (G a b c).PosSemidef) ∧
  (∑ a, ∑ b, ∑ c, G a b c) = 1 ∧
  (∀ a, ((∑ b, ∑ c, G a b c)-eta • P.proj a).PosSemidef) ∧
  (∀ b, ((∑ a, ∑ c, G a b c)-eta • Q.proj b).PosSemidef) ∧
  (∀ c, ((∑ a, ∑ b, G a b c)-eta • R.proj c).PosSemidef)

def ParentAt {n D : ℕ} (P Q R : PVM n D) (eta : ℝ) : Prop :=
  ∃ G, IsParent P Q R eta G

end
end MUMCompatibility
end

section
open scoped BigOperators
namespace MUMCompatibility
open MUMSpectral
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000
private theorem sum_insert {n D : ℕ} (P:PVM n D) (U V:Mat D) :
    (∑ a,U*P.proj a*V)=U*V := by
  rw [← Finset.sum_mul,← Finset.mul_sum,P.complete,mul_one]
private theorem idem_tail {D:ℕ} (p x:Mat D) (h:p*p=p) : p*(p*x)=p*x := by
  rw [←mul_assoc,h]
private theorem mum_tail {D:ℕ} (p q x:Mat D) (t:ℝ) (h:p*q*p=t•p) :
    p*(q*(p*x))=t•(p*x) := by
  rw [←mul_assoc,←mul_assoc,h,smul_mul_assoc]
variable {n D:ℕ} (hn:0<n) (P Q R:PVM n D)
variable (hPQ:Unbiased P Q) (hPR:Unbiased P R) (hQR:Unbiased Q R) (a:Fin n)
include hn hPQ hPR hQR a

theorem conditional_word_p : (∑ b:Fin n,∑ c:Fin n,P.proj a)=((n:ℝ)^2:ℝ)•P.proj a := by
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  have hp := (P.isProj a).isIdempotentElem.eq
  try simp only [mul_assoc, hp, fun b => (Q.isProj b).isIdempotentElem.eq, fun c => (R.isProj c).isIdempotentElem.eq, fun b => (show P.proj a*(Q.proj b*P.proj a)=(n:ℝ)⁻¹•P.proj a by simpa only [mul_assoc] using hPQ.1 a b), fun b => mum_tail (P.proj a) (Q.proj b) _ (n:ℝ)⁻¹ (hPQ.1 a b), fun b => (show Q.proj b*(P.proj a*Q.proj b)=(n:ℝ)⁻¹•Q.proj b by simpa only [mul_assoc] using hPQ.2 a b), fun b => mum_tail (Q.proj b) (P.proj a) _ (n:ℝ)⁻¹ (hPQ.2 a b), fun c => (show P.proj a*(R.proj c*P.proj a)=(n:ℝ)⁻¹•P.proj a by simpa only [mul_assoc] using hPR.1 a c), fun c => mum_tail (P.proj a) (R.proj c) _ (n:ℝ)⁻¹ (hPR.1 a c), fun c => (show R.proj c*(P.proj a*R.proj c)=(n:ℝ)⁻¹•R.proj c by simpa only [mul_assoc] using hPR.2 a c), fun c => mum_tail (R.proj c) (P.proj a) _ (n:ℝ)⁻¹ (hPR.2 a c), fun b c => (show Q.proj b*(R.proj c*Q.proj b)=(n:ℝ)⁻¹•Q.proj b by simpa only [mul_assoc] using hQR.1 b c), fun b c => mum_tail (Q.proj b) (R.proj c) _ (n:ℝ)⁻¹ (hQR.1 b c), fun b c => (show R.proj c*(Q.proj b*R.proj c)=(n:ℝ)⁻¹•R.proj c by simpa only [mul_assoc] using hQR.2 b c), fun b c => mum_tail (R.proj c) (Q.proj b) _ (n:ℝ)⁻¹ (hQR.2 b c), smul_mul_assoc, mul_smul_comm, smul_smul, mul_one, one_mul]
  all_goals try simp only [← Finset.sum_mul,← Finset.mul_sum,Q.complete,R.complete,mul_one,one_mul,
    ← Finset.smul_sum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,← Nat.cast_smul_eq_nsmul ℝ,
    smul_smul,pow_two,inv_mul_cancel₀ hn0,mul_inv_cancel₀ hn0,one_smul]
  all_goals module
theorem conditional_word_q : (∑ b:Fin n,∑ c:Fin n,Q.proj b)=((n:ℝ):ℝ)•(1:Mat D) := by
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  have hp := (P.isProj a).isIdempotentElem.eq
  have he : (∑ b:Fin n,Q.proj b)=(1 : Mat D) := by
    simpa only [mul_assoc,one_mul,mul_one] using sum_insert Q ((1 : Mat D)) ((1 : Mat D))
  rw [Finset.sum_comm]
  simp_rw [he]
  try simp only [mul_assoc, hp, fun b => (Q.isProj b).isIdempotentElem.eq, fun c => (R.isProj c).isIdempotentElem.eq, fun c => (show P.proj a*(R.proj c*P.proj a)=(n:ℝ)⁻¹•P.proj a by simpa only [mul_assoc] using hPR.1 a c), fun c => mum_tail (P.proj a) (R.proj c) _ (n:ℝ)⁻¹ (hPR.1 a c), fun c => (show R.proj c*(P.proj a*R.proj c)=(n:ℝ)⁻¹•R.proj c by simpa only [mul_assoc] using hPR.2 a c), fun c => mum_tail (R.proj c) (P.proj a) _ (n:ℝ)⁻¹ (hPR.2 a c), smul_mul_assoc, mul_smul_comm, smul_smul, mul_one, one_mul]
  all_goals try simp only [← Finset.sum_mul,← Finset.mul_sum,Q.complete,R.complete,mul_one,one_mul,
    ← Finset.smul_sum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,← Nat.cast_smul_eq_nsmul ℝ,
    smul_smul,pow_two,inv_mul_cancel₀ hn0,mul_inv_cancel₀ hn0,one_smul]
  all_goals module
theorem conditional_word_r : (∑ b:Fin n,∑ c:Fin n,R.proj c)=((n:ℝ):ℝ)•(1:Mat D) := by
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  have hp := (P.isProj a).isIdempotentElem.eq
  have he : (∑ c:Fin n,R.proj c)=(1 : Mat D) := by
    simpa only [mul_assoc,one_mul,mul_one] using sum_insert R ((1 : Mat D)) ((1 : Mat D))
  simp_rw [he]
  try simp only [mul_assoc, hp, fun b => (Q.isProj b).isIdempotentElem.eq, fun c => (R.isProj c).isIdempotentElem.eq, fun b => (show P.proj a*(Q.proj b*P.proj a)=(n:ℝ)⁻¹•P.proj a by simpa only [mul_assoc] using hPQ.1 a b), fun b => mum_tail (P.proj a) (Q.proj b) _ (n:ℝ)⁻¹ (hPQ.1 a b), fun b => (show Q.proj b*(P.proj a*Q.proj b)=(n:ℝ)⁻¹•Q.proj b by simpa only [mul_assoc] using hPQ.2 a b), fun b => mum_tail (Q.proj b) (P.proj a) _ (n:ℝ)⁻¹ (hPQ.2 a b), smul_mul_assoc, mul_smul_comm, smul_smul, mul_one, one_mul]
  all_goals try simp only [← Finset.sum_mul,← Finset.mul_sum,Q.complete,R.complete,mul_one,one_mul,
    ← Finset.smul_sum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,← Nat.cast_smul_eq_nsmul ℝ,
    smul_smul,pow_two,inv_mul_cancel₀ hn0,mul_inv_cancel₀ hn0,one_smul]
  all_goals module
theorem conditional_word_pq : (∑ b:Fin n,∑ c:Fin n,P.proj a * Q.proj b)=((n:ℝ):ℝ)•P.proj a := by
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  have hp := (P.isProj a).isIdempotentElem.eq
  have he : (∑ b:Fin n,P.proj a * Q.proj b)=P.proj a := by
    simpa only [mul_assoc,one_mul,mul_one] using sum_insert Q (P.proj a) ((1 : Mat D))
  rw [Finset.sum_comm]
  simp_rw [he]
  try simp only [mul_assoc, hp, fun b => (Q.isProj b).isIdempotentElem.eq, fun c => (R.isProj c).isIdempotentElem.eq, fun c => (show P.proj a*(R.proj c*P.proj a)=(n:ℝ)⁻¹•P.proj a by simpa only [mul_assoc] using hPR.1 a c), fun c => mum_tail (P.proj a) (R.proj c) _ (n:ℝ)⁻¹ (hPR.1 a c), fun c => (show R.proj c*(P.proj a*R.proj c)=(n:ℝ)⁻¹•R.proj c by simpa only [mul_assoc] using hPR.2 a c), fun c => mum_tail (R.proj c) (P.proj a) _ (n:ℝ)⁻¹ (hPR.2 a c), smul_mul_assoc, mul_smul_comm, smul_smul, mul_one, one_mul]
  all_goals try simp only [← Finset.sum_mul,← Finset.mul_sum,Q.complete,R.complete,mul_one,one_mul,
    ← Finset.smul_sum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,← Nat.cast_smul_eq_nsmul ℝ,
    smul_smul,pow_two,inv_mul_cancel₀ hn0,mul_inv_cancel₀ hn0,one_smul]
  all_goals module
theorem conditional_word_pr : (∑ b:Fin n,∑ c:Fin n,P.proj a * R.proj c)=((n:ℝ):ℝ)•P.proj a := by
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  have hp := (P.isProj a).isIdempotentElem.eq
  have he : (∑ c:Fin n,P.proj a * R.proj c)=P.proj a := by
    simpa only [mul_assoc,one_mul,mul_one] using sum_insert R (P.proj a) ((1 : Mat D))
  simp_rw [he]
  try simp only [mul_assoc, hp, fun b => (Q.isProj b).isIdempotentElem.eq, fun c => (R.isProj c).isIdempotentElem.eq, fun b => (show P.proj a*(Q.proj b*P.proj a)=(n:ℝ)⁻¹•P.proj a by simpa only [mul_assoc] using hPQ.1 a b), fun b => mum_tail (P.proj a) (Q.proj b) _ (n:ℝ)⁻¹ (hPQ.1 a b), fun b => (show Q.proj b*(P.proj a*Q.proj b)=(n:ℝ)⁻¹•Q.proj b by simpa only [mul_assoc] using hPQ.2 a b), fun b => mum_tail (Q.proj b) (P.proj a) _ (n:ℝ)⁻¹ (hPQ.2 a b), smul_mul_assoc, mul_smul_comm, smul_smul, mul_one, one_mul]
  all_goals try simp only [← Finset.sum_mul,← Finset.mul_sum,Q.complete,R.complete,mul_one,one_mul,
    ← Finset.smul_sum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,← Nat.cast_smul_eq_nsmul ℝ,
    smul_smul,pow_two,inv_mul_cancel₀ hn0,mul_inv_cancel₀ hn0,one_smul]
  all_goals module
theorem conditional_word_qp : (∑ b:Fin n,∑ c:Fin n,Q.proj b * P.proj a)=((n:ℝ):ℝ)•P.proj a := by
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  have hp := (P.isProj a).isIdempotentElem.eq
  have he : (∑ b:Fin n,Q.proj b * P.proj a)=P.proj a := by
    simpa only [mul_assoc,one_mul,mul_one] using sum_insert Q ((1 : Mat D)) (P.proj a)
  rw [Finset.sum_comm]
  simp_rw [he]
  try simp only [mul_assoc, hp, fun b => (Q.isProj b).isIdempotentElem.eq, fun c => (R.isProj c).isIdempotentElem.eq, fun c => (show P.proj a*(R.proj c*P.proj a)=(n:ℝ)⁻¹•P.proj a by simpa only [mul_assoc] using hPR.1 a c), fun c => mum_tail (P.proj a) (R.proj c) _ (n:ℝ)⁻¹ (hPR.1 a c), fun c => (show R.proj c*(P.proj a*R.proj c)=(n:ℝ)⁻¹•R.proj c by simpa only [mul_assoc] using hPR.2 a c), fun c => mum_tail (R.proj c) (P.proj a) _ (n:ℝ)⁻¹ (hPR.2 a c), smul_mul_assoc, mul_smul_comm, smul_smul, mul_one, one_mul]
  all_goals try simp only [← Finset.sum_mul,← Finset.mul_sum,Q.complete,R.complete,mul_one,one_mul,
    ← Finset.smul_sum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,← Nat.cast_smul_eq_nsmul ℝ,
    smul_smul,pow_two,inv_mul_cancel₀ hn0,mul_inv_cancel₀ hn0,one_smul]
  all_goals module
theorem conditional_word_qr : (∑ b:Fin n,∑ c:Fin n,Q.proj b * R.proj c)=(1:ℝ)•(1:Mat D) := by
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  have hp := (P.isProj a).isIdempotentElem.eq
  have he (c:Fin n) : (∑ b:Fin n,Q.proj b * R.proj c)=R.proj c := by
    simpa only [mul_assoc,one_mul,mul_one] using sum_insert Q ((1 : Mat D)) (R.proj c)
  rw [Finset.sum_comm]
  simp_rw [he]
  try simp only [mul_assoc, hp, fun b => (Q.isProj b).isIdempotentElem.eq, fun c => (R.isProj c).isIdempotentElem.eq, fun c => (show P.proj a*(R.proj c*P.proj a)=(n:ℝ)⁻¹•P.proj a by simpa only [mul_assoc] using hPR.1 a c), fun c => mum_tail (P.proj a) (R.proj c) _ (n:ℝ)⁻¹ (hPR.1 a c), fun c => (show R.proj c*(P.proj a*R.proj c)=(n:ℝ)⁻¹•R.proj c by simpa only [mul_assoc] using hPR.2 a c), fun c => mum_tail (R.proj c) (P.proj a) _ (n:ℝ)⁻¹ (hPR.2 a c), smul_mul_assoc, mul_smul_comm, smul_smul, mul_one, one_mul]
  all_goals try simp only [← Finset.sum_mul,← Finset.mul_sum,Q.complete,R.complete,mul_one,one_mul,
    ← Finset.smul_sum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,← Nat.cast_smul_eq_nsmul ℝ,
    smul_smul,pow_two,inv_mul_cancel₀ hn0,mul_inv_cancel₀ hn0,one_smul]
  all_goals module
theorem conditional_word_rp : (∑ b:Fin n,∑ c:Fin n,R.proj c * P.proj a)=((n:ℝ):ℝ)•P.proj a := by
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  have hp := (P.isProj a).isIdempotentElem.eq
  have he : (∑ c:Fin n,R.proj c * P.proj a)=P.proj a := by
    simpa only [mul_assoc,one_mul,mul_one] using sum_insert R ((1 : Mat D)) (P.proj a)
  simp_rw [he]
  try simp only [mul_assoc, hp, fun b => (Q.isProj b).isIdempotentElem.eq, fun c => (R.isProj c).isIdempotentElem.eq, fun b => (show P.proj a*(Q.proj b*P.proj a)=(n:ℝ)⁻¹•P.proj a by simpa only [mul_assoc] using hPQ.1 a b), fun b => mum_tail (P.proj a) (Q.proj b) _ (n:ℝ)⁻¹ (hPQ.1 a b), fun b => (show Q.proj b*(P.proj a*Q.proj b)=(n:ℝ)⁻¹•Q.proj b by simpa only [mul_assoc] using hPQ.2 a b), fun b => mum_tail (Q.proj b) (P.proj a) _ (n:ℝ)⁻¹ (hPQ.2 a b), smul_mul_assoc, mul_smul_comm, smul_smul, mul_one, one_mul]
  all_goals try simp only [← Finset.sum_mul,← Finset.mul_sum,Q.complete,R.complete,mul_one,one_mul,
    ← Finset.smul_sum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,← Nat.cast_smul_eq_nsmul ℝ,
    smul_smul,pow_two,inv_mul_cancel₀ hn0,mul_inv_cancel₀ hn0,one_smul]
  all_goals module
theorem conditional_word_rq : (∑ b:Fin n,∑ c:Fin n,R.proj c * Q.proj b)=(1:ℝ)•(1:Mat D) := by
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  have hp := (P.isProj a).isIdempotentElem.eq
  have he (c:Fin n) : (∑ b:Fin n,R.proj c * Q.proj b)=R.proj c := by
    simpa only [mul_assoc,one_mul,mul_one] using sum_insert Q (R.proj c) ((1 : Mat D))
  rw [Finset.sum_comm]
  simp_rw [he]
  try simp only [mul_assoc, hp, fun b => (Q.isProj b).isIdempotentElem.eq, fun c => (R.isProj c).isIdempotentElem.eq, fun c => (show P.proj a*(R.proj c*P.proj a)=(n:ℝ)⁻¹•P.proj a by simpa only [mul_assoc] using hPR.1 a c), fun c => mum_tail (P.proj a) (R.proj c) _ (n:ℝ)⁻¹ (hPR.1 a c), fun c => (show R.proj c*(P.proj a*R.proj c)=(n:ℝ)⁻¹•R.proj c by simpa only [mul_assoc] using hPR.2 a c), fun c => mum_tail (R.proj c) (P.proj a) _ (n:ℝ)⁻¹ (hPR.2 a c), smul_mul_assoc, mul_smul_comm, smul_smul, mul_one, one_mul]
  all_goals try simp only [← Finset.sum_mul,← Finset.mul_sum,Q.complete,R.complete,mul_one,one_mul,
    ← Finset.smul_sum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,← Nat.cast_smul_eq_nsmul ℝ,
    smul_smul,pow_two,inv_mul_cancel₀ hn0,mul_inv_cancel₀ hn0,one_smul]
  all_goals module
theorem conditional_word_pqr : (∑ b:Fin n,∑ c:Fin n,P.proj a * Q.proj b * R.proj c)=(1:ℝ)•P.proj a := by
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  have hp := (P.isProj a).isIdempotentElem.eq
  have he (c:Fin n) : (∑ b:Fin n,P.proj a * Q.proj b * R.proj c)=P.proj a * R.proj c := by
    simpa only [mul_assoc,one_mul,mul_one] using sum_insert Q (P.proj a) (R.proj c)
  rw [Finset.sum_comm]
  simp_rw [he]
  try simp only [mul_assoc, hp, fun b => (Q.isProj b).isIdempotentElem.eq, fun c => (R.isProj c).isIdempotentElem.eq, fun c => (show P.proj a*(R.proj c*P.proj a)=(n:ℝ)⁻¹•P.proj a by simpa only [mul_assoc] using hPR.1 a c), fun c => mum_tail (P.proj a) (R.proj c) _ (n:ℝ)⁻¹ (hPR.1 a c), fun c => (show R.proj c*(P.proj a*R.proj c)=(n:ℝ)⁻¹•R.proj c by simpa only [mul_assoc] using hPR.2 a c), fun c => mum_tail (R.proj c) (P.proj a) _ (n:ℝ)⁻¹ (hPR.2 a c), smul_mul_assoc, mul_smul_comm, smul_smul, mul_one, one_mul]
  all_goals try simp only [← Finset.sum_mul,← Finset.mul_sum,Q.complete,R.complete,mul_one,one_mul,
    ← Finset.smul_sum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,← Nat.cast_smul_eq_nsmul ℝ,
    smul_smul,pow_two,inv_mul_cancel₀ hn0,mul_inv_cancel₀ hn0,one_smul]
  all_goals module
theorem conditional_word_prq : (∑ b:Fin n,∑ c:Fin n,P.proj a * R.proj c * Q.proj b)=(1:ℝ)•P.proj a := by
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  have hp := (P.isProj a).isIdempotentElem.eq
  have he (c:Fin n) : (∑ b:Fin n,P.proj a * R.proj c * Q.proj b)=P.proj a * R.proj c := by
    simpa only [mul_assoc,one_mul,mul_one] using sum_insert Q (P.proj a * R.proj c) ((1 : Mat D))
  rw [Finset.sum_comm]
  simp_rw [he]
  try simp only [mul_assoc, hp, fun b => (Q.isProj b).isIdempotentElem.eq, fun c => (R.isProj c).isIdempotentElem.eq, fun c => (show P.proj a*(R.proj c*P.proj a)=(n:ℝ)⁻¹•P.proj a by simpa only [mul_assoc] using hPR.1 a c), fun c => mum_tail (P.proj a) (R.proj c) _ (n:ℝ)⁻¹ (hPR.1 a c), fun c => (show R.proj c*(P.proj a*R.proj c)=(n:ℝ)⁻¹•R.proj c by simpa only [mul_assoc] using hPR.2 a c), fun c => mum_tail (R.proj c) (P.proj a) _ (n:ℝ)⁻¹ (hPR.2 a c), smul_mul_assoc, mul_smul_comm, smul_smul, mul_one, one_mul]
  all_goals try simp only [← Finset.sum_mul,← Finset.mul_sum,Q.complete,R.complete,mul_one,one_mul,
    ← Finset.smul_sum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,← Nat.cast_smul_eq_nsmul ℝ,
    smul_smul,pow_two,inv_mul_cancel₀ hn0,mul_inv_cancel₀ hn0,one_smul]
  all_goals module
theorem conditional_word_qpr : (∑ b:Fin n,∑ c:Fin n,Q.proj b * P.proj a * R.proj c)=(1:ℝ)•P.proj a := by
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  have hp := (P.isProj a).isIdempotentElem.eq
  have he (c:Fin n) : (∑ b:Fin n,Q.proj b * P.proj a * R.proj c)=P.proj a * R.proj c := by
    simpa only [mul_assoc,one_mul,mul_one] using sum_insert Q ((1 : Mat D)) (P.proj a * R.proj c)
  rw [Finset.sum_comm]
  simp_rw [he]
  try simp only [mul_assoc, hp, fun b => (Q.isProj b).isIdempotentElem.eq, fun c => (R.isProj c).isIdempotentElem.eq, fun c => (show P.proj a*(R.proj c*P.proj a)=(n:ℝ)⁻¹•P.proj a by simpa only [mul_assoc] using hPR.1 a c), fun c => mum_tail (P.proj a) (R.proj c) _ (n:ℝ)⁻¹ (hPR.1 a c), fun c => (show R.proj c*(P.proj a*R.proj c)=(n:ℝ)⁻¹•R.proj c by simpa only [mul_assoc] using hPR.2 a c), fun c => mum_tail (R.proj c) (P.proj a) _ (n:ℝ)⁻¹ (hPR.2 a c), smul_mul_assoc, mul_smul_comm, smul_smul, mul_one, one_mul]
  all_goals try simp only [← Finset.sum_mul,← Finset.mul_sum,Q.complete,R.complete,mul_one,one_mul,
    ← Finset.smul_sum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,← Nat.cast_smul_eq_nsmul ℝ,
    smul_smul,pow_two,inv_mul_cancel₀ hn0,mul_inv_cancel₀ hn0,one_smul]
  all_goals module
theorem conditional_word_qrp : (∑ b:Fin n,∑ c:Fin n,Q.proj b * R.proj c * P.proj a)=(1:ℝ)•P.proj a := by
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  have hp := (P.isProj a).isIdempotentElem.eq
  have he (c:Fin n) : (∑ b:Fin n,Q.proj b * R.proj c * P.proj a)=R.proj c * P.proj a := by
    simpa only [mul_assoc,one_mul,mul_one] using sum_insert Q ((1 : Mat D)) (R.proj c * P.proj a)
  rw [Finset.sum_comm]
  simp_rw [he]
  try simp only [mul_assoc, hp, fun b => (Q.isProj b).isIdempotentElem.eq, fun c => (R.isProj c).isIdempotentElem.eq, fun c => (show P.proj a*(R.proj c*P.proj a)=(n:ℝ)⁻¹•P.proj a by simpa only [mul_assoc] using hPR.1 a c), fun c => mum_tail (P.proj a) (R.proj c) _ (n:ℝ)⁻¹ (hPR.1 a c), fun c => (show R.proj c*(P.proj a*R.proj c)=(n:ℝ)⁻¹•R.proj c by simpa only [mul_assoc] using hPR.2 a c), fun c => mum_tail (R.proj c) (P.proj a) _ (n:ℝ)⁻¹ (hPR.2 a c), smul_mul_assoc, mul_smul_comm, smul_smul, mul_one, one_mul]
  all_goals try simp only [← Finset.sum_mul,← Finset.mul_sum,Q.complete,R.complete,mul_one,one_mul,
    ← Finset.smul_sum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,← Nat.cast_smul_eq_nsmul ℝ,
    smul_smul,pow_two,inv_mul_cancel₀ hn0,mul_inv_cancel₀ hn0,one_smul]
  all_goals module
theorem conditional_word_rpq : (∑ b:Fin n,∑ c:Fin n,R.proj c * P.proj a * Q.proj b)=(1:ℝ)•P.proj a := by
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  have hp := (P.isProj a).isIdempotentElem.eq
  have he (c:Fin n) : (∑ b:Fin n,R.proj c * P.proj a * Q.proj b)=R.proj c * P.proj a := by
    simpa only [mul_assoc,one_mul,mul_one] using sum_insert Q (R.proj c * P.proj a) ((1 : Mat D))
  rw [Finset.sum_comm]
  simp_rw [he]
  try simp only [mul_assoc, hp, fun b => (Q.isProj b).isIdempotentElem.eq, fun c => (R.isProj c).isIdempotentElem.eq, fun c => (show P.proj a*(R.proj c*P.proj a)=(n:ℝ)⁻¹•P.proj a by simpa only [mul_assoc] using hPR.1 a c), fun c => mum_tail (P.proj a) (R.proj c) _ (n:ℝ)⁻¹ (hPR.1 a c), fun c => (show R.proj c*(P.proj a*R.proj c)=(n:ℝ)⁻¹•R.proj c by simpa only [mul_assoc] using hPR.2 a c), fun c => mum_tail (R.proj c) (P.proj a) _ (n:ℝ)⁻¹ (hPR.2 a c), smul_mul_assoc, mul_smul_comm, smul_smul, mul_one, one_mul]
  all_goals try simp only [← Finset.sum_mul,← Finset.mul_sum,Q.complete,R.complete,mul_one,one_mul,
    ← Finset.smul_sum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,← Nat.cast_smul_eq_nsmul ℝ,
    smul_smul,pow_two,inv_mul_cancel₀ hn0,mul_inv_cancel₀ hn0,one_smul]
  all_goals module
theorem conditional_word_rqp : (∑ b:Fin n,∑ c:Fin n,R.proj c * Q.proj b * P.proj a)=(1:ℝ)•P.proj a := by
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  have hp := (P.isProj a).isIdempotentElem.eq
  have he (c:Fin n) : (∑ b:Fin n,R.proj c * Q.proj b * P.proj a)=R.proj c * P.proj a := by
    simpa only [mul_assoc,one_mul,mul_one] using sum_insert Q (R.proj c) (P.proj a)
  rw [Finset.sum_comm]
  simp_rw [he]
  try simp only [mul_assoc, hp, fun b => (Q.isProj b).isIdempotentElem.eq, fun c => (R.isProj c).isIdempotentElem.eq, fun c => (show P.proj a*(R.proj c*P.proj a)=(n:ℝ)⁻¹•P.proj a by simpa only [mul_assoc] using hPR.1 a c), fun c => mum_tail (P.proj a) (R.proj c) _ (n:ℝ)⁻¹ (hPR.1 a c), fun c => (show R.proj c*(P.proj a*R.proj c)=(n:ℝ)⁻¹•R.proj c by simpa only [mul_assoc] using hPR.2 a c), fun c => mum_tail (R.proj c) (P.proj a) _ (n:ℝ)⁻¹ (hPR.2 a c), smul_mul_assoc, mul_smul_comm, smul_smul, mul_one, one_mul]
  all_goals try simp only [← Finset.sum_mul,← Finset.mul_sum,Q.complete,R.complete,mul_one,one_mul,
    ← Finset.smul_sum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,← Nat.cast_smul_eq_nsmul ℝ,
    smul_smul,pow_two,inv_mul_cancel₀ hn0,mul_inv_cancel₀ hn0,one_smul]
  all_goals module
theorem conditional_word_pqrp : (∑ b:Fin n,∑ c:Fin n,P.proj a * Q.proj b * R.proj c * P.proj a)=(1:ℝ)•P.proj a := by
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  have hp := (P.isProj a).isIdempotentElem.eq
  have he (c:Fin n) : (∑ b:Fin n,P.proj a * Q.proj b * R.proj c * P.proj a)=P.proj a * R.proj c * P.proj a := by
    simpa only [mul_assoc,one_mul,mul_one] using sum_insert Q (P.proj a) (R.proj c * P.proj a)
  rw [Finset.sum_comm]
  simp_rw [he]
  try simp only [mul_assoc, hp, fun b => (Q.isProj b).isIdempotentElem.eq, fun c => (R.isProj c).isIdempotentElem.eq, fun c => (show P.proj a*(R.proj c*P.proj a)=(n:ℝ)⁻¹•P.proj a by simpa only [mul_assoc] using hPR.1 a c), fun c => mum_tail (P.proj a) (R.proj c) _ (n:ℝ)⁻¹ (hPR.1 a c), fun c => (show R.proj c*(P.proj a*R.proj c)=(n:ℝ)⁻¹•R.proj c by simpa only [mul_assoc] using hPR.2 a c), fun c => mum_tail (R.proj c) (P.proj a) _ (n:ℝ)⁻¹ (hPR.2 a c), smul_mul_assoc, mul_smul_comm, smul_smul, mul_one, one_mul]
  all_goals try simp only [← Finset.sum_mul,← Finset.mul_sum,Q.complete,R.complete,mul_one,one_mul,
    ← Finset.smul_sum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,← Nat.cast_smul_eq_nsmul ℝ,
    smul_smul,pow_two,inv_mul_cancel₀ hn0,mul_inv_cancel₀ hn0,one_smul]
  all_goals module
theorem conditional_word_prqp : (∑ b:Fin n,∑ c:Fin n,P.proj a * R.proj c * Q.proj b * P.proj a)=(1:ℝ)•P.proj a := by
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  have hp := (P.isProj a).isIdempotentElem.eq
  have he (c:Fin n) : (∑ b:Fin n,P.proj a * R.proj c * Q.proj b * P.proj a)=P.proj a * R.proj c * P.proj a := by
    simpa only [mul_assoc,one_mul,mul_one] using sum_insert Q (P.proj a * R.proj c) (P.proj a)
  rw [Finset.sum_comm]
  simp_rw [he]
  try simp only [mul_assoc, hp, fun b => (Q.isProj b).isIdempotentElem.eq, fun c => (R.isProj c).isIdempotentElem.eq, fun c => (show P.proj a*(R.proj c*P.proj a)=(n:ℝ)⁻¹•P.proj a by simpa only [mul_assoc] using hPR.1 a c), fun c => mum_tail (P.proj a) (R.proj c) _ (n:ℝ)⁻¹ (hPR.1 a c), fun c => (show R.proj c*(P.proj a*R.proj c)=(n:ℝ)⁻¹•R.proj c by simpa only [mul_assoc] using hPR.2 a c), fun c => mum_tail (R.proj c) (P.proj a) _ (n:ℝ)⁻¹ (hPR.2 a c), smul_mul_assoc, mul_smul_comm, smul_smul, mul_one, one_mul]
  all_goals try simp only [← Finset.sum_mul,← Finset.mul_sum,Q.complete,R.complete,mul_one,one_mul,
    ← Finset.smul_sum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,← Nat.cast_smul_eq_nsmul ℝ,
    smul_smul,pow_two,inv_mul_cancel₀ hn0,mul_inv_cancel₀ hn0,one_smul]
  all_goals module
theorem conditional_word_qprq : (∑ b:Fin n,∑ c:Fin n,Q.proj b * P.proj a * R.proj c * Q.proj b)=((n:ℝ)⁻¹:ℝ)•(1:Mat D) := by
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  have hp := (P.isProj a).isIdempotentElem.eq
  have he (b:Fin n) : (∑ c:Fin n,Q.proj b * P.proj a * R.proj c * Q.proj b)=Q.proj b * P.proj a * Q.proj b := by
    simpa only [mul_assoc,one_mul,mul_one] using sum_insert R (Q.proj b * P.proj a) (Q.proj b)
  simp_rw [he]
  try simp only [mul_assoc, hp, fun b => (Q.isProj b).isIdempotentElem.eq, fun c => (R.isProj c).isIdempotentElem.eq, fun b => (show P.proj a*(Q.proj b*P.proj a)=(n:ℝ)⁻¹•P.proj a by simpa only [mul_assoc] using hPQ.1 a b), fun b => mum_tail (P.proj a) (Q.proj b) _ (n:ℝ)⁻¹ (hPQ.1 a b), fun b => (show Q.proj b*(P.proj a*Q.proj b)=(n:ℝ)⁻¹•Q.proj b by simpa only [mul_assoc] using hPQ.2 a b), fun b => mum_tail (Q.proj b) (P.proj a) _ (n:ℝ)⁻¹ (hPQ.2 a b), smul_mul_assoc, mul_smul_comm, smul_smul, mul_one, one_mul]
  all_goals try simp only [← Finset.sum_mul,← Finset.mul_sum,Q.complete,R.complete,mul_one,one_mul,
    ← Finset.smul_sum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,← Nat.cast_smul_eq_nsmul ℝ,
    smul_smul,pow_two,inv_mul_cancel₀ hn0,mul_inv_cancel₀ hn0,one_smul]
  all_goals module
theorem conditional_word_qrpq : (∑ b:Fin n,∑ c:Fin n,Q.proj b * R.proj c * P.proj a * Q.proj b)=((n:ℝ)⁻¹:ℝ)•(1:Mat D) := by
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  have hp := (P.isProj a).isIdempotentElem.eq
  have he (b:Fin n) : (∑ c:Fin n,Q.proj b * R.proj c * P.proj a * Q.proj b)=Q.proj b * P.proj a * Q.proj b := by
    simpa only [mul_assoc,one_mul,mul_one] using sum_insert R (Q.proj b) (P.proj a * Q.proj b)
  simp_rw [he]
  try simp only [mul_assoc, hp, fun b => (Q.isProj b).isIdempotentElem.eq, fun c => (R.isProj c).isIdempotentElem.eq, fun b => (show P.proj a*(Q.proj b*P.proj a)=(n:ℝ)⁻¹•P.proj a by simpa only [mul_assoc] using hPQ.1 a b), fun b => mum_tail (P.proj a) (Q.proj b) _ (n:ℝ)⁻¹ (hPQ.1 a b), fun b => (show Q.proj b*(P.proj a*Q.proj b)=(n:ℝ)⁻¹•Q.proj b by simpa only [mul_assoc] using hPQ.2 a b), fun b => mum_tail (Q.proj b) (P.proj a) _ (n:ℝ)⁻¹ (hPQ.2 a b), smul_mul_assoc, mul_smul_comm, smul_smul, mul_one, one_mul]
  all_goals try simp only [← Finset.sum_mul,← Finset.mul_sum,Q.complete,R.complete,mul_one,one_mul,
    ← Finset.smul_sum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,← Nat.cast_smul_eq_nsmul ℝ,
    smul_smul,pow_two,inv_mul_cancel₀ hn0,mul_inv_cancel₀ hn0,one_smul]
  all_goals module
theorem conditional_word_rpqr : (∑ b:Fin n,∑ c:Fin n,R.proj c * P.proj a * Q.proj b * R.proj c)=((n:ℝ)⁻¹:ℝ)•(1:Mat D) := by
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  have hp := (P.isProj a).isIdempotentElem.eq
  have he (c:Fin n) : (∑ b:Fin n,R.proj c * P.proj a * Q.proj b * R.proj c)=R.proj c * P.proj a * R.proj c := by
    simpa only [mul_assoc,one_mul,mul_one] using sum_insert Q (R.proj c * P.proj a) (R.proj c)
  rw [Finset.sum_comm]
  simp_rw [he]
  try simp only [mul_assoc, hp, fun b => (Q.isProj b).isIdempotentElem.eq, fun c => (R.isProj c).isIdempotentElem.eq, fun c => (show P.proj a*(R.proj c*P.proj a)=(n:ℝ)⁻¹•P.proj a by simpa only [mul_assoc] using hPR.1 a c), fun c => mum_tail (P.proj a) (R.proj c) _ (n:ℝ)⁻¹ (hPR.1 a c), fun c => (show R.proj c*(P.proj a*R.proj c)=(n:ℝ)⁻¹•R.proj c by simpa only [mul_assoc] using hPR.2 a c), fun c => mum_tail (R.proj c) (P.proj a) _ (n:ℝ)⁻¹ (hPR.2 a c), smul_mul_assoc, mul_smul_comm, smul_smul, mul_one, one_mul]
  all_goals try simp only [← Finset.sum_mul,← Finset.mul_sum,Q.complete,R.complete,mul_one,one_mul,
    ← Finset.smul_sum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,← Nat.cast_smul_eq_nsmul ℝ,
    smul_smul,pow_two,inv_mul_cancel₀ hn0,mul_inv_cancel₀ hn0,one_smul]
  all_goals module
theorem conditional_word_rqpr : (∑ b:Fin n,∑ c:Fin n,R.proj c * Q.proj b * P.proj a * R.proj c)=((n:ℝ)⁻¹:ℝ)•(1:Mat D) := by
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  have hp := (P.isProj a).isIdempotentElem.eq
  have he (c:Fin n) : (∑ b:Fin n,R.proj c * Q.proj b * P.proj a * R.proj c)=R.proj c * P.proj a * R.proj c := by
    simpa only [mul_assoc,one_mul,mul_one] using sum_insert Q (R.proj c) (P.proj a * R.proj c)
  rw [Finset.sum_comm]
  simp_rw [he]
  try simp only [mul_assoc, hp, fun b => (Q.isProj b).isIdempotentElem.eq, fun c => (R.isProj c).isIdempotentElem.eq, fun c => (show P.proj a*(R.proj c*P.proj a)=(n:ℝ)⁻¹•P.proj a by simpa only [mul_assoc] using hPR.1 a c), fun c => mum_tail (P.proj a) (R.proj c) _ (n:ℝ)⁻¹ (hPR.1 a c), fun c => (show R.proj c*(P.proj a*R.proj c)=(n:ℝ)⁻¹•R.proj c by simpa only [mul_assoc] using hPR.2 a c), fun c => mum_tail (R.proj c) (P.proj a) _ (n:ℝ)⁻¹ (hPR.2 a c), smul_mul_assoc, mul_smul_comm, smul_smul, mul_one, one_mul]
  all_goals try simp only [← Finset.sum_mul,← Finset.mul_sum,Q.complete,R.complete,mul_one,one_mul,
    ← Finset.smul_sum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,← Nat.cast_smul_eq_nsmul ℝ,
    smul_smul,pow_two,inv_mul_cancel₀ hn0,mul_inv_cancel₀ hn0,one_smul]
  all_goals module
theorem conditional_word_pqrpq : (∑ b:Fin n,∑ c:Fin n,P.proj a * Q.proj b * R.proj c * P.proj a * Q.proj b)=((n:ℝ)⁻¹:ℝ)•P.proj a := by
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  have hp := (P.isProj a).isIdempotentElem.eq
  have he (b:Fin n) : (∑ c:Fin n,P.proj a * Q.proj b * R.proj c * P.proj a * Q.proj b)=P.proj a * Q.proj b * P.proj a * Q.proj b := by
    simpa only [mul_assoc,one_mul,mul_one] using sum_insert R (P.proj a * Q.proj b) (P.proj a * Q.proj b)
  simp_rw [he]
  try simp only [mul_assoc, hp, fun b => (Q.isProj b).isIdempotentElem.eq, fun c => (R.isProj c).isIdempotentElem.eq, fun b => (show P.proj a*(Q.proj b*P.proj a)=(n:ℝ)⁻¹•P.proj a by simpa only [mul_assoc] using hPQ.1 a b), fun b => mum_tail (P.proj a) (Q.proj b) _ (n:ℝ)⁻¹ (hPQ.1 a b), fun b => (show Q.proj b*(P.proj a*Q.proj b)=(n:ℝ)⁻¹•Q.proj b by simpa only [mul_assoc] using hPQ.2 a b), fun b => mum_tail (Q.proj b) (P.proj a) _ (n:ℝ)⁻¹ (hPQ.2 a b), smul_mul_assoc, mul_smul_comm, smul_smul, mul_one, one_mul]
  all_goals try simp only [← Finset.sum_mul,← Finset.mul_sum,Q.complete,R.complete,mul_one,one_mul,
    ← Finset.smul_sum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,← Nat.cast_smul_eq_nsmul ℝ,
    smul_smul,pow_two,inv_mul_cancel₀ hn0,mul_inv_cancel₀ hn0,one_smul]
  all_goals module
theorem conditional_word_prqpr : (∑ b:Fin n,∑ c:Fin n,P.proj a * R.proj c * Q.proj b * P.proj a * R.proj c)=((n:ℝ)⁻¹:ℝ)•P.proj a := by
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  have hp := (P.isProj a).isIdempotentElem.eq
  have he (c:Fin n) : (∑ b:Fin n,P.proj a * R.proj c * Q.proj b * P.proj a * R.proj c)=P.proj a * R.proj c * P.proj a * R.proj c := by
    simpa only [mul_assoc,one_mul,mul_one] using sum_insert Q (P.proj a * R.proj c) (P.proj a * R.proj c)
  rw [Finset.sum_comm]
  simp_rw [he]
  try simp only [mul_assoc, hp, fun b => (Q.isProj b).isIdempotentElem.eq, fun c => (R.isProj c).isIdempotentElem.eq, fun c => (show P.proj a*(R.proj c*P.proj a)=(n:ℝ)⁻¹•P.proj a by simpa only [mul_assoc] using hPR.1 a c), fun c => mum_tail (P.proj a) (R.proj c) _ (n:ℝ)⁻¹ (hPR.1 a c), fun c => (show R.proj c*(P.proj a*R.proj c)=(n:ℝ)⁻¹•R.proj c by simpa only [mul_assoc] using hPR.2 a c), fun c => mum_tail (R.proj c) (P.proj a) _ (n:ℝ)⁻¹ (hPR.2 a c), smul_mul_assoc, mul_smul_comm, smul_smul, mul_one, one_mul]
  all_goals try simp only [← Finset.sum_mul,← Finset.mul_sum,Q.complete,R.complete,mul_one,one_mul,
    ← Finset.smul_sum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,← Nat.cast_smul_eq_nsmul ℝ,
    smul_smul,pow_two,inv_mul_cancel₀ hn0,mul_inv_cancel₀ hn0,one_smul]
  all_goals module
theorem conditional_word_qprqp : (∑ b:Fin n,∑ c:Fin n,Q.proj b * P.proj a * R.proj c * Q.proj b * P.proj a)=((n:ℝ)⁻¹:ℝ)•P.proj a := by
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  have hp := (P.isProj a).isIdempotentElem.eq
  have he (b:Fin n) : (∑ c:Fin n,Q.proj b * P.proj a * R.proj c * Q.proj b * P.proj a)=Q.proj b * P.proj a * Q.proj b * P.proj a := by
    simpa only [mul_assoc,one_mul,mul_one] using sum_insert R (Q.proj b * P.proj a) (Q.proj b * P.proj a)
  simp_rw [he]
  try simp only [mul_assoc, hp, fun b => (Q.isProj b).isIdempotentElem.eq, fun c => (R.isProj c).isIdempotentElem.eq, fun b => (show P.proj a*(Q.proj b*P.proj a)=(n:ℝ)⁻¹•P.proj a by simpa only [mul_assoc] using hPQ.1 a b), fun b => mum_tail (P.proj a) (Q.proj b) _ (n:ℝ)⁻¹ (hPQ.1 a b), fun b => (show Q.proj b*(P.proj a*Q.proj b)=(n:ℝ)⁻¹•Q.proj b by simpa only [mul_assoc] using hPQ.2 a b), fun b => mum_tail (Q.proj b) (P.proj a) _ (n:ℝ)⁻¹ (hPQ.2 a b), smul_mul_assoc, mul_smul_comm, smul_smul, mul_one, one_mul]
  all_goals try simp only [← Finset.sum_mul,← Finset.mul_sum,Q.complete,R.complete,mul_one,one_mul,
    ← Finset.smul_sum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,← Nat.cast_smul_eq_nsmul ℝ,
    smul_smul,pow_two,inv_mul_cancel₀ hn0,mul_inv_cancel₀ hn0,one_smul]
  all_goals module
theorem conditional_word_rpqrp : (∑ b:Fin n,∑ c:Fin n,R.proj c * P.proj a * Q.proj b * R.proj c * P.proj a)=((n:ℝ)⁻¹:ℝ)•P.proj a := by
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  have hp := (P.isProj a).isIdempotentElem.eq
  have he (c:Fin n) : (∑ b:Fin n,R.proj c * P.proj a * Q.proj b * R.proj c * P.proj a)=R.proj c * P.proj a * R.proj c * P.proj a := by
    simpa only [mul_assoc,one_mul,mul_one] using sum_insert Q (R.proj c * P.proj a) (R.proj c * P.proj a)
  rw [Finset.sum_comm]
  simp_rw [he]
  try simp only [mul_assoc, hp, fun b => (Q.isProj b).isIdempotentElem.eq, fun c => (R.isProj c).isIdempotentElem.eq, fun c => (show P.proj a*(R.proj c*P.proj a)=(n:ℝ)⁻¹•P.proj a by simpa only [mul_assoc] using hPR.1 a c), fun c => mum_tail (P.proj a) (R.proj c) _ (n:ℝ)⁻¹ (hPR.1 a c), fun c => (show R.proj c*(P.proj a*R.proj c)=(n:ℝ)⁻¹•R.proj c by simpa only [mul_assoc] using hPR.2 a c), fun c => mum_tail (R.proj c) (P.proj a) _ (n:ℝ)⁻¹ (hPR.2 a c), smul_mul_assoc, mul_smul_comm, smul_smul, mul_one, one_mul]
  all_goals try simp only [← Finset.sum_mul,← Finset.mul_sum,Q.complete,R.complete,mul_one,one_mul,
    ← Finset.smul_sum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,← Nat.cast_smul_eq_nsmul ℝ,
    smul_smul,pow_two,inv_mul_cancel₀ hn0,mul_inv_cancel₀ hn0,one_smul]
  all_goals module
end MUMCompatibility
end

section
open scoped BigOperators
namespace MUMCompatibility
open MUMSpectral
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
variable {n D:ℕ} (hn:0<n) (P Q R:PVM n D)
variable (hPQ:Unbiased P Q) (hPR:Unbiased P R) (hQR:Unbiased Q R) (a:Fin n)
include hn hPQ hPR hQR

theorem conditional_moment_1 : (∑ b,∑ c,(selected P Q R a b c)^1) =
    ((n:ℝ)^2) • P.proj a + (2*(n:ℝ)) • (1:Mat D) := by
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  have ha : ((1)*((n:ℝ)^2)) = (n:ℝ)^2 := by field_simp; all_goals ring
  have hi : ((1)*((n:ℝ)) + (1)*((n:ℝ))) = 2*(n:ℝ) := by field_simp; all_goals ring
  have he (b c:Fin n) := MUMPowerReduction.power_1 (P.proj a) (Q.proj b) (R.proj c) (n:ℝ)⁻¹
    (P.isProj a).isIdempotentElem.eq (Q.isProj b).isIdempotentElem.eq (R.isProj c).isIdempotentElem.eq
    (hPQ.1 a b) (hPR.1 a c) (hPQ.2 a b) (hQR.1 b c) (hPR.2 a c) (hQR.2 b c)
  unfold selected
  simp_rw [he]
  simp only [Finset.sum_add_distrib, ← Finset.smul_sum]
  rw [conditional_word_p hn P Q R hPQ hPR hQR a, conditional_word_q hn P Q R hPQ hPR hQR a, conditional_word_r hn P Q R hPQ hPR hQR a]
  calc
    _ = ((1)*((n:ℝ)^2)) • P.proj a + ((1)*((n:ℝ)) + (1)*((n:ℝ))) • (1:Mat D) := by
      module
    _ = _ := by rw [ha,hi]

theorem conditional_moment_2 : (∑ b,∑ c,(selected P Q R a b c)^2) =
    ((n:ℝ)^2+4*n) • P.proj a + (2*(n:ℝ)+2) • (1:Mat D) := by
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  have ha : ((1)*((n:ℝ)^2) + (1)*((n:ℝ)) + (1)*((n:ℝ)) + (1)*((n:ℝ)) + (1)*((n:ℝ))) = (n:ℝ)^2+4*n := by field_simp; all_goals ring
  have hi : ((1)*((n:ℝ)) + (1)*((n:ℝ)) + (1)*(1) + (1)*(1)) = 2*(n:ℝ)+2 := by field_simp; all_goals ring
  have he (b c:Fin n) := MUMPowerReduction.power_2 (P.proj a) (Q.proj b) (R.proj c) (n:ℝ)⁻¹
    (P.isProj a).isIdempotentElem.eq (Q.isProj b).isIdempotentElem.eq (R.isProj c).isIdempotentElem.eq
    (hPQ.1 a b) (hPR.1 a c) (hPQ.2 a b) (hQR.1 b c) (hPR.2 a c) (hQR.2 b c)
  unfold selected
  simp_rw [he]
  simp only [Finset.sum_add_distrib, ← Finset.smul_sum]
  rw [conditional_word_p hn P Q R hPQ hPR hQR a, conditional_word_q hn P Q R hPQ hPR hQR a, conditional_word_r hn P Q R hPQ hPR hQR a, conditional_word_pq hn P Q R hPQ hPR hQR a, conditional_word_pr hn P Q R hPQ hPR hQR a, conditional_word_qp hn P Q R hPQ hPR hQR a, conditional_word_qr hn P Q R hPQ hPR hQR a, conditional_word_rp hn P Q R hPQ hPR hQR a, conditional_word_rq hn P Q R hPQ hPR hQR a]
  calc
    _ = ((1)*((n:ℝ)^2) + (1)*((n:ℝ)) + (1)*((n:ℝ)) + (1)*((n:ℝ)) + (1)*((n:ℝ))) • P.proj a + ((1)*((n:ℝ)) + (1)*((n:ℝ)) + (1)*(1) + (1)*(1)) • (1:Mat D) := by
      module
    _ = _ := by rw [ha,hi]

theorem conditional_moment_3 : (∑ b,∑ c,(selected P Q R a b c)^3) =
    ((n:ℝ)^2+10*n+6) • P.proj a + (2*(n:ℝ)+8) • (1:Mat D) := by
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  have ha : ((1+2*((n:ℝ)⁻¹)^1)*((n:ℝ)^2) + (2)*((n:ℝ)) + (2)*((n:ℝ)) + (2)*((n:ℝ)) + (2)*((n:ℝ)) + (1)*(1) + (1)*(1) + (1)*(1) + (1)*(1) + (1)*(1) + (1)*(1)) = (n:ℝ)^2+10*n+6 := by field_simp; all_goals ring
  have hi : ((1+2*((n:ℝ)⁻¹)^1)*((n:ℝ)) + (1+2*((n:ℝ)⁻¹)^1)*((n:ℝ)) + (2)*(1) + (2)*(1)) = 2*(n:ℝ)+8 := by field_simp; all_goals ring
  have he (b c:Fin n) := MUMPowerReduction.power_3 (P.proj a) (Q.proj b) (R.proj c) (n:ℝ)⁻¹
    (P.isProj a).isIdempotentElem.eq (Q.isProj b).isIdempotentElem.eq (R.isProj c).isIdempotentElem.eq
    (hPQ.1 a b) (hPR.1 a c) (hPQ.2 a b) (hQR.1 b c) (hPR.2 a c) (hQR.2 b c)
  unfold selected
  simp_rw [he]
  simp only [Finset.sum_add_distrib, ← Finset.smul_sum]
  rw [conditional_word_p hn P Q R hPQ hPR hQR a, conditional_word_q hn P Q R hPQ hPR hQR a, conditional_word_r hn P Q R hPQ hPR hQR a, conditional_word_pq hn P Q R hPQ hPR hQR a, conditional_word_pr hn P Q R hPQ hPR hQR a, conditional_word_qp hn P Q R hPQ hPR hQR a, conditional_word_qr hn P Q R hPQ hPR hQR a, conditional_word_rp hn P Q R hPQ hPR hQR a, conditional_word_rq hn P Q R hPQ hPR hQR a, conditional_word_pqr hn P Q R hPQ hPR hQR a, conditional_word_prq hn P Q R hPQ hPR hQR a, conditional_word_qpr hn P Q R hPQ hPR hQR a, conditional_word_qrp hn P Q R hPQ hPR hQR a, conditional_word_rpq hn P Q R hPQ hPR hQR a, conditional_word_rqp hn P Q R hPQ hPR hQR a]
  calc
    _ = ((1+2*((n:ℝ)⁻¹)^1)*((n:ℝ)^2) + (2)*((n:ℝ)) + (2)*((n:ℝ)) + (2)*((n:ℝ)) + (2)*((n:ℝ)) + (1)*(1) + (1)*(1) + (1)*(1) + (1)*(1) + (1)*(1) + (1)*(1)) • P.proj a + ((1+2*((n:ℝ)⁻¹)^1)*((n:ℝ)) + (1+2*((n:ℝ)⁻¹)^1)*((n:ℝ)) + (2)*(1) + (2)*(1)) • (1:Mat D) := by
      module
    _ = _ := by rw [ha,hi]

theorem conditional_moment_4 : (∑ b,∑ c,(selected P Q R a b c)^4) =
    ((n:ℝ)^2+18*n+32) • P.proj a + (2*(n:ℝ)+18+10/n) • (1:Mat D) := by
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  have ha : ((1+6*((n:ℝ)⁻¹)^1)*((n:ℝ)^2) + (3+3*((n:ℝ)⁻¹)^1)*((n:ℝ)) + (3+3*((n:ℝ)⁻¹)^1)*((n:ℝ)) + (3+3*((n:ℝ)⁻¹)^1)*((n:ℝ)) + (3+3*((n:ℝ)⁻¹)^1)*((n:ℝ)) + (3)*(1) + (3)*(1) + (3)*(1) + (3)*(1) + (3)*(1) + (3)*(1) + (1)*(1) + (1)*(1)) = (n:ℝ)^2+18*n+32 := by field_simp; all_goals ring
  have hi : ((1+6*((n:ℝ)⁻¹)^1)*((n:ℝ)) + (1+6*((n:ℝ)⁻¹)^1)*((n:ℝ)) + (3+3*((n:ℝ)⁻¹)^1)*(1) + (3+3*((n:ℝ)⁻¹)^1)*(1) + (1)*((n:ℝ)⁻¹) + (1)*((n:ℝ)⁻¹) + (1)*((n:ℝ)⁻¹) + (1)*((n:ℝ)⁻¹)) = 2*(n:ℝ)+18+10/n := by field_simp; all_goals ring
  have he (b c:Fin n) := MUMPowerReduction.power_4 (P.proj a) (Q.proj b) (R.proj c) (n:ℝ)⁻¹
    (P.isProj a).isIdempotentElem.eq (Q.isProj b).isIdempotentElem.eq (R.isProj c).isIdempotentElem.eq
    (hPQ.1 a b) (hPR.1 a c) (hPQ.2 a b) (hQR.1 b c) (hPR.2 a c) (hQR.2 b c)
  unfold selected
  simp_rw [he]
  simp only [Finset.sum_add_distrib, ← Finset.smul_sum]
  rw [conditional_word_p hn P Q R hPQ hPR hQR a, conditional_word_q hn P Q R hPQ hPR hQR a, conditional_word_r hn P Q R hPQ hPR hQR a, conditional_word_pq hn P Q R hPQ hPR hQR a, conditional_word_pr hn P Q R hPQ hPR hQR a, conditional_word_qp hn P Q R hPQ hPR hQR a, conditional_word_qr hn P Q R hPQ hPR hQR a, conditional_word_rp hn P Q R hPQ hPR hQR a, conditional_word_rq hn P Q R hPQ hPR hQR a, conditional_word_pqr hn P Q R hPQ hPR hQR a, conditional_word_prq hn P Q R hPQ hPR hQR a, conditional_word_qpr hn P Q R hPQ hPR hQR a, conditional_word_qrp hn P Q R hPQ hPR hQR a, conditional_word_rpq hn P Q R hPQ hPR hQR a, conditional_word_rqp hn P Q R hPQ hPR hQR a, conditional_word_pqrp hn P Q R hPQ hPR hQR a, conditional_word_prqp hn P Q R hPQ hPR hQR a, conditional_word_qprq hn P Q R hPQ hPR hQR a, conditional_word_qrpq hn P Q R hPQ hPR hQR a, conditional_word_rpqr hn P Q R hPQ hPR hQR a, conditional_word_rqpr hn P Q R hPQ hPR hQR a]
  calc
    _ = ((1+6*((n:ℝ)⁻¹)^1)*((n:ℝ)^2) + (3+3*((n:ℝ)⁻¹)^1)*((n:ℝ)) + (3+3*((n:ℝ)⁻¹)^1)*((n:ℝ)) + (3+3*((n:ℝ)⁻¹)^1)*((n:ℝ)) + (3+3*((n:ℝ)⁻¹)^1)*((n:ℝ)) + (3)*(1) + (3)*(1) + (3)*(1) + (3)*(1) + (3)*(1) + (3)*(1) + (1)*(1) + (1)*(1)) • P.proj a + ((1+6*((n:ℝ)⁻¹)^1)*((n:ℝ)) + (1+6*((n:ℝ)⁻¹)^1)*((n:ℝ)) + (3+3*((n:ℝ)⁻¹)^1)*(1) + (3+3*((n:ℝ)⁻¹)^1)*(1) + (1)*((n:ℝ)⁻¹) + (1)*((n:ℝ)⁻¹) + (1)*((n:ℝ)⁻¹) + (1)*((n:ℝ)⁻¹)) • (1:Mat D) := by
      module
    _ = _ := by rw [ha,hi]

theorem conditional_moment_5 : (∑ b,∑ c,(selected P Q R a b c)^5) =
    ((n:ℝ)^2+28*n+98+28/n) • P.proj a + (2*(n:ℝ)+32+52/n) • (1:Mat D) + cycleZ P Q R a := by
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  have ha : ((1+12*((n:ℝ)⁻¹)^1+6*((n:ℝ)⁻¹)^2)*((n:ℝ)^2) + (4+12*((n:ℝ)⁻¹)^1)*((n:ℝ)) + (4+12*((n:ℝ)⁻¹)^1)*((n:ℝ)) + (4+12*((n:ℝ)⁻¹)^1)*((n:ℝ)) + (4+12*((n:ℝ)⁻¹)^1)*((n:ℝ)) + (6+4*((n:ℝ)⁻¹)^1)*(1) + (6+4*((n:ℝ)⁻¹)^1)*(1) + (6+4*((n:ℝ)⁻¹)^1)*(1) + (6+4*((n:ℝ)⁻¹)^1)*(1) + (6+4*((n:ℝ)⁻¹)^1)*(1) + (6+4*((n:ℝ)⁻¹)^1)*(1) + (4)*(1) + (4)*(1) + (1)*((n:ℝ)⁻¹) + (1)*((n:ℝ)⁻¹) + (1)*((n:ℝ)⁻¹) + (1)*((n:ℝ)⁻¹)) = (n:ℝ)^2+28*n+98+28/n := by field_simp; all_goals ring
  have hi : ((1+12*((n:ℝ)⁻¹)^1+6*((n:ℝ)⁻¹)^2)*((n:ℝ)) + (1+12*((n:ℝ)⁻¹)^1+6*((n:ℝ)⁻¹)^2)*((n:ℝ)) + (4+12*((n:ℝ)⁻¹)^1)*(1) + (4+12*((n:ℝ)⁻¹)^1)*(1) + (4)*((n:ℝ)⁻¹) + (4)*((n:ℝ)⁻¹) + (4)*((n:ℝ)⁻¹) + (4)*((n:ℝ)⁻¹)) = 2*(n:ℝ)+32+52/n := by field_simp; all_goals ring
  have he (b c:Fin n) := MUMPowerReduction.power_5 (P.proj a) (Q.proj b) (R.proj c) (n:ℝ)⁻¹
    (P.isProj a).isIdempotentElem.eq (Q.isProj b).isIdempotentElem.eq (R.isProj c).isIdempotentElem.eq
    (hPQ.1 a b) (hPR.1 a c) (hPQ.2 a b) (hQR.1 b c) (hPR.2 a c) (hQR.2 b c)
  unfold selected
  simp_rw [he]
  simp only [Finset.sum_add_distrib, ← Finset.smul_sum]
  rw [conditional_word_p hn P Q R hPQ hPR hQR a, conditional_word_q hn P Q R hPQ hPR hQR a, conditional_word_r hn P Q R hPQ hPR hQR a, conditional_word_pq hn P Q R hPQ hPR hQR a, conditional_word_pr hn P Q R hPQ hPR hQR a, conditional_word_qp hn P Q R hPQ hPR hQR a, conditional_word_qr hn P Q R hPQ hPR hQR a, conditional_word_rp hn P Q R hPQ hPR hQR a, conditional_word_rq hn P Q R hPQ hPR hQR a, conditional_word_pqr hn P Q R hPQ hPR hQR a, conditional_word_prq hn P Q R hPQ hPR hQR a, conditional_word_qpr hn P Q R hPQ hPR hQR a, conditional_word_qrp hn P Q R hPQ hPR hQR a, conditional_word_rpq hn P Q R hPQ hPR hQR a, conditional_word_rqp hn P Q R hPQ hPR hQR a, conditional_word_pqrp hn P Q R hPQ hPR hQR a, conditional_word_prqp hn P Q R hPQ hPR hQR a, conditional_word_qprq hn P Q R hPQ hPR hQR a, conditional_word_qrpq hn P Q R hPQ hPR hQR a, conditional_word_rpqr hn P Q R hPQ hPR hQR a, conditional_word_rqpr hn P Q R hPQ hPR hQR a, conditional_word_pqrpq hn P Q R hPQ hPR hQR a, conditional_word_prqpr hn P Q R hPQ hPR hQR a, conditional_word_qprqp hn P Q R hPQ hPR hQR a, conditional_word_rpqrp hn P Q R hPQ hPR hQR a]
  calc
    _ = ((1+12*((n:ℝ)⁻¹)^1+6*((n:ℝ)⁻¹)^2)*((n:ℝ)^2) + (4+12*((n:ℝ)⁻¹)^1)*((n:ℝ)) + (4+12*((n:ℝ)⁻¹)^1)*((n:ℝ)) + (4+12*((n:ℝ)⁻¹)^1)*((n:ℝ)) + (4+12*((n:ℝ)⁻¹)^1)*((n:ℝ)) + (6+4*((n:ℝ)⁻¹)^1)*(1) + (6+4*((n:ℝ)⁻¹)^1)*(1) + (6+4*((n:ℝ)⁻¹)^1)*(1) + (6+4*((n:ℝ)⁻¹)^1)*(1) + (6+4*((n:ℝ)⁻¹)^1)*(1) + (6+4*((n:ℝ)⁻¹)^1)*(1) + (4)*(1) + (4)*(1) + (1)*((n:ℝ)⁻¹) + (1)*((n:ℝ)⁻¹) + (1)*((n:ℝ)⁻¹) + (1)*((n:ℝ)⁻¹)) • P.proj a + ((1+12*((n:ℝ)⁻¹)^1+6*((n:ℝ)⁻¹)^2)*((n:ℝ)) + (1+12*((n:ℝ)⁻¹)^1+6*((n:ℝ)⁻¹)^2)*((n:ℝ)) + (4+12*((n:ℝ)⁻¹)^1)*(1) + (4+12*((n:ℝ)⁻¹)^1)*(1) + (4)*((n:ℝ)⁻¹) + (4)*((n:ℝ)⁻¹) + (4)*((n:ℝ)⁻¹) + (4)*((n:ℝ)⁻¹)) • (1:Mat D) + cycleZ P Q R a := by
      unfold cycleZ
      simp only [Finset.sum_add_distrib]
      module
    _ = _ := by rw [ha,hi]

end MUMCompatibility
end

section
open scoped BigOperators
namespace MUMCompatibility
open MUMSpectral
set_option maxHeartbeats 1000000

theorem cycleZ_sum {n D:ℕ} (P Q R:PVM n D) (hQR:Unbiased Q R) :
    (∑ a, cycleZ P Q R a) = (2/(n:ℝ)) • (1:Mat D) := by
  have he (b c:Fin n) :
      (∑ a, (Q.proj b*R.proj c*P.proj a*Q.proj b*R.proj c +
        R.proj c*Q.proj b*P.proj a*R.proj c*Q.proj b)) =
        (n:ℝ)⁻¹ • (Q.proj b*R.proj c+R.proj c*Q.proj b) := by
    simp only [Finset.sum_add_distrib, ←Finset.sum_mul, ←Finset.mul_sum,
      P.complete,mul_one]
    rw [hQR.1 b c,hQR.2 b c,smul_mul_assoc,smul_mul_assoc,smul_add]
  have hs : (∑ b,∑ c, (Q.proj b*R.proj c+R.proj c*Q.proj b)) = (2:ℝ) • (1:Mat D) := by
    simp only [Finset.sum_add_distrib, ←Finset.mul_sum, ←Finset.sum_mul,
      Q.complete,R.complete,mul_one,one_mul]
    module
  unfold cycleZ
  calc
    _ = ∑ b,∑ c,∑ a, (Q.proj b*R.proj c*P.proj a*Q.proj b*R.proj c +
        R.proj c*Q.proj b*P.proj a*R.proj c*Q.proj b) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.sum_comm]
    _ = (n:ℝ)⁻¹ • (∑ b,∑ c,(Q.proj b*R.proj c+R.proj c*Q.proj b)) := by
      simp_rw [he]
      simp only [Finset.smul_sum]
    _ = _ := by rw [hs,smul_smul]; congr 1; ring

end MUMCompatibility
end

section
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator ComplexOrder
open Matrix MUMSpectral
namespace MUMCompatibility

theorem denom_pos {n : ℕ} (hn : 0<n) {x : ℝ} (hx : 0<x) : 0 < denom n x := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  unfold denom
  positivity

theorem scale_pos {n : ℕ} (hn : 0<n) {x : ℝ} (hx : 0<x) : 0 < scale n x := by
  unfold scale
  exact div_pos (by norm_num) (mul_pos (by norm_num) (denom_pos hn hx))

theorem coeffC_pos {n : ℕ} (hn : 0<n) {x : ℝ} (hx : 0<x) : 0 < coeffC n x := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  unfold coeffC
  positivity

theorem root_cubic {n : ℕ} (hn : 0<n) {x : ℝ} (h : rootEquation n x) :
    x^3 = 3*x/(n:ℝ)+2/(n:ℝ)^2 := by
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  unfold rootEquation at h
  field_simp
  nlinarith [h]

theorem coeffV_split (n : ℕ) (x : ℝ) : coeffV n x = coeffC n x+2/(n:ℝ) := by
  unfold coeffV coeffC
  ring

theorem normalization_scalar (n : ℕ) (hn : 0<n) (x : ℝ) :
    coeffU n x+(n:ℝ)*coeffV n x+2/(n:ℝ)=9*denom n x := by
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  unfold coeffU coeffV denom
  field_simp
  ring

theorem marginal_scalar (n : ℕ) (hn : 0<n) (x : ℝ) (h : rootEquation n x) :
    coeffU n x+coeffC n x+4/(n:ℝ)^2=3*denom n x*(1+x) := by
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hx3 := root_cubic hn h
  unfold coeffU coeffC denom
  ring_nf
  simp only [hx3]
  field_simp
  ring

theorem scale_normalization (n : ℕ) (hn : 0<n) (x : ℝ) (hx : 0<x) :
    scale n x*(coeffU n x+(n:ℝ)*coeffV n x+2/(n:ℝ))=1 := by
  rw [normalization_scalar n hn x]
  unfold scale
  exact div_mul_cancel₀ 1 (ne_of_gt (mul_pos (by norm_num) (denom_pos hn hx)))

theorem positive_root_exists (n : ℕ) (hn : 0<n) :
    ∃ x : ℝ, 0<x ∧ x≤2 ∧ rootEquation n x := by
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  let f : ℝ → ℝ := fun x => (n:ℝ)^2*x^3-3*(n:ℝ)*x-2
  have hc : ContinuousOn f (Set.Icc 0 2) := by fun_prop
  have h0 : f 0 ≤ 0 := by dsimp [f]; norm_num
  have h2 : 0 ≤ f 2 := by
    dsimp [f]
    nlinarith [sq_nonneg ((n:ℝ)-1)]
  obtain ⟨x,hx,hfx⟩ := intermediate_value_Icc (by norm_num : (0:ℝ)≤2) hc ⟨h0,h2⟩
  refine ⟨x,?_,hx.2,hfx⟩
  have hne : x≠0 := by intro h; subst x; norm_num [f] at hfx
  exact lt_of_le_of_ne hx.1 (Ne.symm hne)

theorem positive_root_unique (n : ℕ) (hn : 0<n) (x y : ℝ)
    (hx : 0<x) (hy : 0<y) (hX : rootEquation n x) (hY : rootEquation n y) : x=y := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  unfold rootEquation at hX hY
  have hx2 : 3*(n:ℝ) < (n:ℝ)^2*x^2 := by
    by_contra h
    have hmul := mul_le_mul_of_nonneg_right (le_of_not_gt h) (le_of_lt hx)
    nlinarith [hmul, hX]
  have hfactor : (x-y)*((n:ℝ)^2*(x^2+x*y+y^2)-3*(n:ℝ))=0 := by nlinarith [hX,hY]
  have hpos : 0 < (n:ℝ)^2*(x^2+x*y+y^2)-3*(n:ℝ) := by
    nlinarith [mul_nonneg (sq_nonneg (n:ℝ)) (mul_nonneg (le_of_lt hx) (le_of_lt hy)),
      mul_nonneg (sq_nonneg (n:ℝ)) (sq_nonneg y)]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_right (ne_of_gt hpos))

theorem four_cos_root : 0 < Real.cos (Real.pi/9) ∧ rootEquation 4 (Real.cos (Real.pi/9)) := by
  constructor
  · apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [Real.pi_pos]
  · have h := Real.cos_three_mul (Real.pi/9)
    rw [show 3*(Real.pi/9)=Real.pi/3 by ring, Real.cos_pi_div_three] at h
    unfold rootEquation
    norm_num
    nlinarith [h]

end MUMCompatibility
end

section
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator ComplexOrder
open Matrix MUMSpectral
namespace MUMCompatibility

theorem rawParent_expand (n : ℕ) (x : ℝ) {D : ℕ} (S : Mat D) :
    rawParent n x S = S^5+(2*(x-2)) • S^4+
      ((x-2)^2+2*(x^2-x+1-3/(n:ℝ))) • S^3+
      (2*(x-2)*(x^2-x+1-3/(n:ℝ))) • S^2+
      (x^2-x+1-3/(n:ℝ))^2 • S := by
  unfold rawParent polyQ
  simp only [pow_succ, pow_zero, mul_one, one_mul, add_mul, mul_add,
    smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]
  module

theorem raw_projection_coefficient (n : ℕ) (hn : 0<n) (x : ℝ) (h : rootEquation n x) :
    ((n:ℝ)^2+28*n+98+28/n)+2*(x-2)*((n:ℝ)^2+18*n+32)+
      ((x-2)^2+2*(x^2-x+1-3/(n:ℝ)))*((n:ℝ)^2+10*n+6)+
      (2*(x-2)*(x^2-x+1-3/(n:ℝ)))*((n:ℝ)^2+4*n)+
      (x^2-x+1-3/(n:ℝ))^2*(n:ℝ)^2 = coeffU n x := by
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hx3 := root_cubic hn h
  have hx4 : x^4=x*(3*x/(n:ℝ)+2/(n:ℝ)^2) := by
    calc
      x^4=x*x^3 := by ring
      _ = _ := by rw [hx3]
  unfold coeffU
  ring_nf
  simp only [hx4,hx3]
  field_simp
  ring

theorem raw_identity_coefficient (n : ℕ) (hn : 0<n) (x : ℝ) (h : rootEquation n x) :
    (2*(n:ℝ)+32+52/n)+2*(x-2)*(2*(n:ℝ)+18+10/n)+
      ((x-2)^2+2*(x^2-x+1-3/(n:ℝ)))*(2*(n:ℝ)+8)+
      (2*(x-2)*(x^2-x+1-3/(n:ℝ)))*(2*(n:ℝ)+2)+
      (x^2-x+1-3/(n:ℝ))^2*(2*(n:ℝ)) = coeffV n x := by
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hx3 := root_cubic hn h
  have hx4 : x^4=x*(3*x/(n:ℝ)+2/(n:ℝ)^2) := by
    calc
      x^4=x*x^3 := by ring
      _ = _ := by rw [hx3]
  unfold coeffV
  ring_nf
  simp only [hx4,hx3]
  field_simp
  ring

end MUMCompatibility
end

section
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator ComplexOrder
open Matrix MUMSpectral
namespace MUMCompatibility
noncomputable section
set_option maxHeartbeats 2000000
variable {n D : ℕ}

theorem projection_complement_posSemidef (P : PVM n D) (a : Fin n) :
    (1 - P.proj a).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (P.isProj a).one_sub.nonneg

theorem selected_nonneg (P Q R : PVM n D) (a b c : Fin n) :
    0 ≤ selected P Q R a b c :=
  add_nonneg (add_nonneg (P.proj_nonneg a) (Q.proj_nonneg b)) (R.proj_nonneg c)

theorem polyQ_selfAdjoint (n : ℕ) (x : ℝ) (S : Mat D) (hS : IsSelfAdjoint S) :
    IsSelfAdjoint (polyQ n x S) := by
  unfold polyQ
  exact ((hS.pow 2).add ((IsSelfAdjoint.all _).smul hS)).add
    ((IsSelfAdjoint.all _).smul (IsSelfAdjoint.one _))

theorem polyQ_commute (n : ℕ) (x : ℝ) (S : Mat D) :
    S * polyQ n x S = polyQ n x S * S := by
  simp only [polyQ, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
  congr 2
  noncomm_ring

theorem rawParent_posSemidef (n : ℕ) (x : ℝ) (S : Mat D) (hS : 0 ≤ S) :
    (rawParent n x S).PosSemidef := by
  have hq := polyQ_selfAdjoint n x S (IsSelfAdjoint.of_nonneg hS)
  have hp := (Matrix.nonneg_iff_posSemidef.mp hS).conjTranspose_mul_mul_same (polyQ n x S)
  rw [← Matrix.star_eq_conjTranspose, hq.star_eq] at hp
  unfold rawParent
  rw [pow_two, ← mul_assoc, polyQ_commute]
  exact hp

theorem centered_square_expand (A X : Mat D) (z : ℝ)
    (hA : IsStarProjection A) (hX : IsSelfAdjoint X) :
    star (A*X-z • A)*(A*X-z • A) =
      X*A*X-z • (X*A+A*X)+(z^2) • A := by
  have hAA : A*A=A := hA.isIdempotentElem
  simp only [star_sub, star_mul, star_smul, star_trivial,
    hA.isSelfAdjoint.star_eq, hX.star_eq, mul_sub, sub_mul,
    smul_mul_assoc, mul_smul_comm, smul_smul, smul_add, pow_two]
  have h1 : X*A*(A*X)=X*A*X := by
    calc
      X*A*(A*X)=X*(A*A)*X := by noncomm_ring
      _=X*A*X := by rw [hAA]
  have h2 : X*A*A=X*A := by rw [mul_assoc, hAA]
  have h3 : A*(A*X)=A*X := by rw [← mul_assoc, hAA]
  rw [h1, h2, h3, hAA]
  module

theorem sum_anticommutator (Q R : PVM n D) :
    (∑ b, ∑ c, (Q.proj b*R.proj c+R.proj c*Q.proj b)) = (2:ℝ) • (1:Mat D) := by
  simp only [Finset.sum_add_distrib, PVM.sum_mul_proj, PVM.sum_proj_mul, Q.complete]
  module

theorem sum_anticommutator_sandwich (hn : 0<n) (P Q R : PVM n D)
    (hPQ : Unbiased P Q) (hPR : Unbiased P R) (hQR : Unbiased Q R) (a : Fin n) :
    (∑ b, ∑ c, (Q.proj b*R.proj c+R.proj c*Q.proj b)*P.proj a*
      (Q.proj b*R.proj c+R.proj c*Q.proj b)) = cycleZ P Q R a + (2/(n:ℝ)) • (1:Mat D) := by
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hterm (b c : Fin n) :
      (Q.proj b*R.proj c+R.proj c*Q.proj b)*P.proj a*(Q.proj b*R.proj c+R.proj c*Q.proj b) =
      (Q.proj b*R.proj c*P.proj a*Q.proj b*R.proj c+
       R.proj c*Q.proj b*P.proj a*R.proj c*Q.proj b) +
       ((n:ℝ)⁻¹)^2 • (Q.proj b+R.proj c) := by
    have h1 : Q.proj b*R.proj c*P.proj a*R.proj c*Q.proj b =
        ((n:ℝ)⁻¹)^2 • Q.proj b := by
      calc
        _ = Q.proj b*(R.proj c*P.proj a*R.proj c)*Q.proj b := by noncomm_ring
        _ = _ := by rw [hPR.2 a c]; simp only [mul_smul_comm, smul_mul_assoc, hQR.1 b c, smul_smul, pow_two]
    have h2 : R.proj c*Q.proj b*P.proj a*Q.proj b*R.proj c =
        ((n:ℝ)⁻¹)^2 • R.proj c := by
      calc
        _ = R.proj c*(Q.proj b*P.proj a*Q.proj b)*R.proj c := by noncomm_ring
        _ = _ := by rw [hPQ.2 a b]; simp only [mul_smul_comm, smul_mul_assoc, hQR.2 b c, smul_smul, pow_two]
    calc
      _ = (Q.proj b*R.proj c*P.proj a*Q.proj b*R.proj c+
       R.proj c*Q.proj b*P.proj a*R.proj c*Q.proj b) +
       (Q.proj b*R.proj c*P.proj a*R.proj c*Q.proj b+
        R.proj c*Q.proj b*P.proj a*Q.proj b*R.proj c) := by noncomm_ring
      _ = _ := by rw [h1,h2,smul_add]
  simp only [hterm, Finset.sum_add_distrib, ← Finset.smul_sum]
  simp only [cycleZ, Finset.sum_add_distrib]
  apply congrArg (fun M : Mat D =>
    (∑ b, ∑ c, Q.proj b*R.proj c*P.proj a*Q.proj b*R.proj c) +
    (∑ b, ∑ c, R.proj c*Q.proj b*P.proj a*R.proj c*Q.proj b) + M)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Finset.smul_sum, Q.complete, R.complete, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  have htwo : (1:Mat D)+1=(2:ℝ) • (1:Mat D) := by module
  rw [← smul_add, htwo, smul_smul, smul_smul]
  apply congrArg (fun r : ℝ => r • (1:Mat D))
  field_simp [hn0]
  <;> ring

theorem amplitude_squares_posSemidef (P Q R : PVM n D) (a : Fin n) :
    (∑ b, ∑ c, star (amplitudeH P Q R a b c)*amplitudeH P Q R a b c).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro b _
  apply Matrix.posSemidef_sum
  intro c _
  exact Matrix.posSemidef_conjTranspose_mul_self _

theorem amplitude_squares_identity (hn : 0<n) (P Q R : PVM n D)
    (hPQ : Unbiased P Q) (hPR : Unbiased P R) (hQR : Unbiased Q R) (a : Fin n) :
    (∑ b, ∑ c, star (amplitudeH P Q R a b c)*amplitudeH P Q R a b c) =
      cycleZ P Q R a + (2/(n:ℝ)) • (1:Mat D) - (4/(n:ℝ)^2) • P.proj a := by
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hn)
  let X (b c : Fin n) := Q.proj b*R.proj c+R.proj c*Q.proj b
  have hX (b c : Fin n) : IsSelfAdjoint (X b c) := by
    change star (X b c)=X b c
    simp only [X,star_add,star_mul,(Q.isProj b).isSelfAdjoint.star_eq,
      (R.isProj c).isSelfAdjoint.star_eq]
    abel
  have hsumX : (∑ b, ∑ c, X b c)=(2:ℝ) • (1:Mat D) := sum_anticommutator Q R
  have hlinear : (∑ b, ∑ c, (2/(n:ℝ)^2) • (X b c*P.proj a+P.proj a*X b c)) =
      (8/(n:ℝ)^2) • P.proj a := by
    simp only [← Finset.smul_sum, Finset.sum_add_distrib,
      ← Finset.sum_mul, ← Finset.mul_sum, hsumX, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    module
  have hconstant : (∑ _b : Fin n, ∑ _c : Fin n, ((2/(n:ℝ)^2)^2) • P.proj a) =
      (4/(n:ℝ)^2) • P.proj a := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,← Nat.cast_smul_eq_nsmul ℝ,smul_smul]
    apply congrArg (fun r : ℝ => r • P.proj a)
    field_simp [hn0]
    <;> ring
  calc
    _ = (∑ b, ∑ c, (X b c*P.proj a*X b c -
        (2/(n:ℝ)^2) • (X b c*P.proj a+P.proj a*X b c) +
        ((2/(n:ℝ)^2)^2) • P.proj a)) := by
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro c _
      exact centered_square_expand (P.proj a) (X b c) _ (P.isProj a) (hX b c)
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, hlinear, hconstant]
      rw [show (∑ b, ∑ c, X b c*P.proj a*X b c) =
        cycleZ P Q R a + (2/(n:ℝ)) • (1:Mat D) from
        sum_anticommutator_sandwich hn P Q R hPQ hPR hQR a]
      module

end
end MUMCompatibility
end

section
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator ComplexOrder
open Matrix MUMSpectral
namespace MUMCompatibility
noncomputable section
set_option maxHeartbeats 4000000
variable {n D : ℕ}

theorem raw_marginal (hn : 0<n) (P Q R : PVM n D)
    (hPQ : Unbiased P Q) (hPR : Unbiased P R) (hQR : Unbiased Q R)
    (x : ℝ) (hroot : rootEquation n x) (a : Fin n) :
    (∑ b, ∑ c, rawParent n x (selected P Q R a b c)) =
      cycleZ P Q R a + coeffU n x • P.proj a + coeffV n x • (1:Mat D) := by
  simp_rw [rawParent_expand]
  simp only [Finset.sum_add_distrib, ← Finset.smul_sum]
  rw [conditional_moment_5 hn P Q R hPQ hPR hQR a,
    conditional_moment_4 hn P Q R hPQ hPR hQR a,
    conditional_moment_3 hn P Q R hPQ hPR hQR a,
    conditional_moment_2 hn P Q R hPQ hPR hQR a,
    show (∑ b, ∑ c, selected P Q R a b c) =
      ((n:ℝ)^2) • P.proj a + (2*(n:ℝ)) • (1:Mat D) by
        simpa only [pow_one] using conditional_moment_1 hn P Q R hPQ hPR hQR a]
  have hA := raw_projection_coefficient n hn x hroot
  have hI := raw_identity_coefficient n hn x hroot
  rw [← hA, ← hI]
  module

theorem parent_normalized (hn : 0<n) (P Q R : PVM n D)
    (hPQ : Unbiased P Q) (hPR : Unbiased P R) (hQR : Unbiased Q R)
    (x : ℝ) (hx : 0<x) (hroot : rootEquation n x) :
    (∑ a, ∑ b, ∑ c, parent P Q R x a b c) = 1 := by
  simp only [parent, ← Finset.smul_sum]
  simp_rw [raw_marginal hn P Q R hPQ hPR hQR x hroot]
  simp only [Finset.sum_add_distrib, ← Finset.smul_sum, P.complete,
    cycleZ_sum P Q R hQR, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  calc
    _ = (scale n x*(coeffU n x+(n:ℝ)*coeffV n x+2/(n:ℝ))) • (1:Mat D) := by module
    _ = 1 := by rw [scale_normalization n hn x hx, one_smul]

theorem marginal_certificate (hn : 0<n) (P Q R : PVM n D)
    (hPQ : Unbiased P Q) (hPR : Unbiased P R) (hQR : Unbiased Q R)
    (x : ℝ) (hx : 0<x) (hroot : rootEquation n x) (a : Fin n) :
    (∑ b, ∑ c, parent P Q R x a b c) - ((1+x)/3) • P.proj a =
      scale n x • (∑ b, ∑ c, star (amplitudeH P Q R a b c)*amplitudeH P Q R a b c) +
      (scale n x*coeffC n x) • (1-P.proj a) := by
  simp only [parent, ← Finset.smul_sum]
  rw [raw_marginal hn P Q R hPQ hPR hQR x hroot,
    amplitude_squares_identity hn P Q R hPQ hPR hQR a, coeffV_split]
  have hscalar : scale n x*(coeffU n x+coeffC n x+4/(n:ℝ)^2)=(1+x)/3 := by
    rw [marginal_scalar n hn x hroot]
    unfold scale
    field_simp [ne_of_gt (denom_pos hn hx)]
    <;> ring
  rw [← hscalar]
  module

theorem first_marginal_posSemidef (hn : 0<n) (P Q R : PVM n D)
    (hPQ : Unbiased P Q) (hPR : Unbiased P R) (hQR : Unbiased Q R)
    (x : ℝ) (hx : 0<x) (hroot : rootEquation n x) (a : Fin n) :
    ((∑ b, ∑ c, parent P Q R x a b c)-((1+x)/3) • P.proj a).PosSemidef := by
  rw [marginal_certificate hn P Q R hPQ hPR hQR x hx hroot a]
  apply Matrix.nonneg_iff_posSemidef.mp
  exact add_nonneg
    (smul_nonneg (le_of_lt (scale_pos hn hx))
      (Matrix.nonneg_iff_posSemidef.mpr (amplitude_squares_posSemidef P Q R a)))
    (smul_nonneg (le_of_lt (mul_pos (scale_pos hn hx) (coeffC_pos hn hx)))
      (Matrix.nonneg_iff_posSemidef.mpr (projection_complement_posSemidef P a)))

theorem parent_swap12 (P Q R : PVM n D) (x : ℝ) (a b c : Fin n) :
    parent P Q R x a b c = parent Q P R x b a c := by
  unfold parent selected
  rw [add_comm (P.proj a) (Q.proj b)]

theorem parent_cycle (P Q R : PVM n D) (x : ℝ) (a b c : Fin n) :
    parent P Q R x a b c = parent R P Q x c a b := by
  unfold parent selected
  rw [add_comm (P.proj a+Q.proj b) (R.proj c), add_assoc]

theorem explicit_parent (hn : 0<n) (P Q R : PVM n D)
    (hPQ : Unbiased P Q) (hPR : Unbiased P R) (hQR : Unbiased Q R)
    (x : ℝ) (hx : 0<x) (hroot : rootEquation n x) :
    IsParent P Q R ((1+x)/3) (parent P Q R x) := by
  refine ⟨?_, parent_normalized hn P Q R hPQ hPR hQR x hx hroot,
    first_marginal_posSemidef hn P Q R hPQ hPR hQR x hx hroot, ?_, ?_⟩
  · intro a b c
    apply Matrix.nonneg_iff_posSemidef.mp
    exact smul_nonneg (le_of_lt (scale_pos hn hx))
      (Matrix.nonneg_iff_posSemidef.mpr
        (rawParent_posSemidef n x _ (selected_nonneg P Q R a b c)))
  · intro b
    simp_rw [parent_swap12 P Q R]
    exact first_marginal_posSemidef hn Q P R hPQ.symm hQR hPR x hx hroot b
  · intro c
    simp_rw [parent_cycle P Q R]
    exact first_marginal_posSemidef hn R P Q hPR.symm hQR.symm hPQ x hx hroot c

end
end MUMCompatibility
end

section
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator ComplexOrder
open Matrix MUMSpectral
namespace MUMCompatibility
noncomputable section
variable {n D : ℕ}

/-- Every positive root lies in the physical visibility range. -/
theorem positive_root_le_two (hn : 0 < n) {x : ℝ} (hx : 0 < x)
    (hroot : rootEquation n x) : x ≤ 2 := by
  obtain ⟨y, hy, hy2, hyroot⟩ := positive_root_exists n hn
  rw [positive_root_unique n hn x y hx hy hroot hyroot]
  exact hy2

theorem positive_root_lt_two (hn : 2 ≤ n) {x : ℝ} (hx : 0 < x)
    (hroot : rootEquation n x) : x < 2 := by
  have hn0 : 0 < n := by omega
  have hx2 := positive_root_le_two hn0 hx hroot
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  apply lt_of_le_of_ne hx2
  intro heq
  rw [heq] at hroot
  unfold rootEquation at hroot
  norm_num at hroot
  nlinarith [sq_nonneg ((n : ℝ) - 1)]

theorem positive_root_visibility (hn : 0 < n) {x : ℝ} (hx : 0 < x)
    (hroot : rootEquation n x) : 0 < (1+x)/3 ∧ (1+x)/3 ≤ 1 := by
  have hx2 := positive_root_le_two hn hx hroot
  constructor <;> linarith

theorem nontrivial_root_visibility (hn : 2 ≤ n) {x : ℝ} (hx : 0 < x)
    (hroot : rootEquation n x) : 0 < (1+x)/3 ∧ (1+x)/3 < 1 := by
  have hx2 := positive_root_lt_two hn hx hroot
  constructor <;> linarith

/-- The four-outcome complement coefficient is exactly one ninth. -/
theorem four_outcome_complement_coefficient {x : ℝ} (hx : 0 < x) :
    scale 4 x * coeffC 4 x = 1/9 := by
  have hC : coeffC 4 x = denom 4 x := by
    unfold coeffC denom
    norm_num
    <;> ring
  rw [hC]
  unfold scale
  field_simp [ne_of_gt (denom_pos (by decide : 0 < 4) hx)]
  <;> ring

theorem four_outcome_marginal_certificate (P Q R : PVM 4 D)
    (hPQ : Unbiased P Q) (hPR : Unbiased P R) (hQR : Unbiased Q R)
    (x : ℝ) (hx : 0 < x) (hroot : rootEquation 4 x) (a : Fin 4) :
    (∑ b, ∑ c, parent P Q R x a b c) - ((1+x)/3) • P.proj a =
      scale 4 x • (∑ b, ∑ c, star (amplitudeH P Q R a b c) * amplitudeH P Q R a b c) +
      (1/9 : ℝ) • (1-P.proj a) := by
  rw [marginal_certificate (by decide) P Q R hPQ hPR hQR x hx hroot a,
    four_outcome_complement_coefficient hx]

end
end MUMCompatibility
end

section
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator ComplexOrder
open Matrix MUMSpectral
namespace MUMCompatibility
noncomputable section
set_option maxHeartbeats 2000000
variable {D : ℕ}

theorem star_square_quadratic (K : Mat D) (v : Fin D → ℂ) :
    star v ⬝ᵥ ((star K*K)*ᵥv) = star (K*ᵥv) ⬝ᵥ (K*ᵥv) := by
  rw [Matrix.star_eq_conjTranspose, ← mulVec_mulVec, dotProduct_mulVec,
    vecMul_conjTranspose, star_star]

theorem weighted_sos_posDef {ι : Type*} [Fintype ι] (A : Mat D) (hA : IsStarProjection A)
    (H : ι → Mat D) (a c : ℝ) (ha : 0<a) (hc : 0<c)
    (hkernel : ∀ v : Fin D → ℂ, v≠0 → A*ᵥv=v → ∃ i, H i*ᵥv≠0) :
    (a • (∑ i, star (H i)*H i) + c • (1-A)).PosDef := by
  have hs : (∑ i, star (H i)*H i).PosSemidef := by
    apply Matrix.posSemidef_sum
    intro i _
    exact Matrix.posSemidef_conjTranspose_mul_self _
  have ht : (1-A).PosSemidef := Matrix.nonneg_iff_posSemidef.mp hA.one_sub.nonneg
  apply Matrix.PosDef.of_dotProduct_mulVec_pos ((hs.smul ha.le).add (ht.smul hc.le)).isHermitian
  intro v hv
  rw [add_mulVec, dotProduct_add, smul_mulVec, smul_mulVec, dotProduct_smul, dotProduct_smul]
  have hs0 := hs.dotProduct_mulVec_nonneg v
  have ht0 := ht.dotProduct_mulVec_nonneg v
  by_cases hAv : A*ᵥv=v
  · obtain ⟨i, hi⟩ := hkernel v hv hAv
    have hspos : 0 < star v ⬝ᵥ ((∑ i, star (H i)*H i)*ᵥv) := by
      rw [Matrix.sum_mulVec, dotProduct_sum]
      apply Finset.sum_pos'
      · intro j _
        exact (Matrix.posSemidef_conjTranspose_mul_self (H j)).dotProduct_mulVec_nonneg v
      · exact ⟨i, Finset.mem_univ _, by
          rw [star_square_quadratic]
          exact dotProduct_star_self_pos_iff.mpr hi⟩
    exact add_pos_of_pos_of_nonneg (smul_pos ha hspos) (smul_nonneg hc.le ht0)
  · have hcv : (1-A)*ᵥv≠0 := by
      intro hz
      rw [sub_mulVec, one_mulVec] at hz
      exact hAv (sub_eq_zero.mp hz).symm
    have hcomp : star (1-A)*(1-A)=1-A := by
      rw [hA.one_sub.isSelfAdjoint.star_eq]
      exact hA.one_sub.isIdempotentElem
    have htpos : 0 < star v ⬝ᵥ ((1-A)*ᵥv) := by
      rw [← hcomp, star_square_quadratic]
      exact dotProduct_star_self_pos_iff.mpr hcv
    exact add_pos_of_nonneg_of_pos (smul_nonneg ha.le hs0) (smul_pos hc htpos)

theorem posDef_exists_projection_gap (hD : 0<D) (A T : Mat D)
    (hA : IsStarProjection A) (hT : T.PosDef) :
    ∃ ε : ℝ, 0<ε ∧ (T-ε • A).PosSemidef := by
  letI : NeZero D := ⟨Nat.ne_of_gt hD⟩
  have ht := hT.isStrictlyPositive
  obtain ⟨ε,hε,hbound⟩ := (CFC.exists_pos_algebraMap_le_iff ht.isSelfAdjoint).mpr
    (fun x hx => ht.spectrum_pos hx)
  refine ⟨ε,hε,Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr ?_)⟩
  have hAle : A ≤ 1 := sub_nonneg.mp hA.one_sub.nonneg
  have hsmul : ε • A ≤ ε • (1:Mat D) := smul_le_smul_of_nonneg_left hAle hε.le
  exact hsmul.trans (by simpa only [Algebra.algebraMap_eq_smul_one] using hbound)

end
end MUMCompatibility
end

section
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator ComplexOrder
open Matrix MUMSpectral
namespace MUMCompatibility
noncomputable section
variable {D : ℕ}

theorem finite_posDef_projection_gap {ι : Type*} [Fintype ι] [Nonempty ι]
    (hD : 0<D) (A T : ι → Mat D) (hA : ∀ i, IsStarProjection (A i))
    (hT : ∀ i, (T i).PosDef) :
    ∃ ε : ℝ, 0<ε ∧ ∀ i, (T i-ε • A i).PosSemidef := by
  classical
  choose e he hbound using fun i => posDef_exists_projection_gap hD (A i) (T i) (hA i) (hT i)
  let s : Finset ℝ := Finset.univ.image e
  have hs : s.Nonempty := Finset.univ_nonempty.image e
  refine ⟨s.min' hs, ?_, ?_⟩
  · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.min'_mem s hs)
    rw [← hi]
    exact he i
  · intro i
    have hmin : s.min' hs ≤ e i := Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
    apply Matrix.nonneg_iff_posSemidef.mp
    exact (hbound i).nonneg.trans (sub_le_sub_left
      (smul_le_smul_of_nonneg_right hmin (hA i).nonneg) (T i))

end
end MUMCompatibility
end

section
open scoped BigOperators ComplexConjugate
open Matrix

namespace MUMAnchor

theorem integer_obstruction (n : ℕ) (hn : 3 ≤ n) (k : ℤ) :
    (n : ℤ) + ((n : ℤ) - 1) * k ≠ 0 := by
  intro h
  have hd : (n : ℤ) - 1 ∣ (n : ℤ) := ⟨-k, by nlinarith⟩
  have hd1 : (n : ℤ) - 1 ∣ 1 := by
    have hh := dvd_sub hd (dvd_refl ((n : ℤ) - 1))
    simpa only [sub_sub_cancel] using hh
  have hh := Int.le_of_dvd (by norm_num : (0 : ℤ) < 1) hd1
  omega

theorem flat_imaginary_sign {n : ℕ} (hn : 0 < n) (z : ℂ)
    (hre : z.re = 1 / (n : ℝ)) (hflat : ‖z‖ ^ 2 = 1 / (n : ℝ)) :
    ∃ k : ℤ, (k = 1 ∨ k = -1) ∧
      z.im = (k : ℝ) * (Real.sqrt ((n : ℝ) - 1) / n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : (Real.sqrt ((n : ℝ) - 1)) ^ 2 = (n : ℝ) - 1 :=
    Real.sq_sqrt (by linarith)
  have hz : z.re ^ 2 + z.im ^ 2 = 1 / (n : ℝ) := by
    calc
      _ = Complex.normSq z := by simp only [Complex.normSq_apply, pow_two]
      _ = ‖z‖^2 := Complex.normSq_eq_norm_sq z
      _ = _ := hflat
  have him : z.im ^ 2 = (Real.sqrt ((n : ℝ) - 1) / n) ^ 2 := by
    rw [hre] at hz
    rw [div_pow, hs]
    field_simp at hz ⊢
    nlinarith
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp him with h | h
  · exact ⟨1, Or.inl rfl, by simpa using h⟩
  · exact ⟨-1, Or.inr rfl, by simpa using h⟩

theorem unitary_flat_not_constant_real {n : ℕ} (hn : 3 ≤ n)
    (U : Matrix (Fin n) (Fin n) ℂ)
    (hunit : U * Uᴴ = 1)
    (hflat : ∀ i j, ‖U i j‖ ^ 2 = 1 / (n : ℝ)) :
    ¬ (∀ i j, (U i j).re = 1 / (n : ℝ)) := by
  classical
  intro hreal
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
  choose e hes he using fun i j => flat_imaginary_sign hn0 (U i j) (hreal i j) (hflat i j)
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  have hij : i ≠ j := by simp [i, j]
  let k : ℤ := ∑ l, e i l * e j l
  let t : ℝ := Real.sqrt ((n : ℝ) - 1) / n
  have ht : t^2 = ((n : ℝ)-1)/(n : ℝ)^2 := by
    dsimp [t]
    rw [div_pow, Real.sq_sqrt (by linarith)]
  have hsum : ∑ l, (U i l).im * (U j l).im = t^2 * (k : ℝ) := by
    simp only [he]
    dsimp [k, t]
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    ring
  have hortho := congrArg Complex.re (congrFun (congrFun hunit i) j)
  have ho : ∑ l, ((U i l).re * (U j l).re + (U i l).im * (U j l).im) = 0 := by
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.mul_re,
      Matrix.one_apply_ne hij] using hortho
  simp only [hreal, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, hsum] at ho
  rw [ht] at ho
  have hkR : (n : ℝ) + ((n : ℝ)-1)*(k : ℝ) = 0 := by
    field_simp at ho
    nlinarith
  have hk : (n : ℤ) + ((n : ℤ)-1)*k = 0 := by exact_mod_cast hkR
  exact integer_obstruction n hn k hk

theorem diagonal_phase_unitary {n : ℕ} (v : Fin n → ℂ) (hv : ∀ i, ‖v i‖=1) :
    Matrix.diagonal v * (Matrix.diagonal v)ᴴ = (1 : Matrix (Fin n) (Fin n) ℂ) := by
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i=j
  · subst j
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    change v i * conj (v i) = 1
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hv i]
    norm_num
  · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]

theorem diagonal_gauge_unitary {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U*Uᴴ=1) (r c : Fin n → ℂ)
    (hr : ∀ i, ‖r i‖=1) (hc : ∀ i, ‖c i‖=1) :
    let Z := Matrix.diagonal r * U * Matrix.diagonal c
    Z*Zᴴ=1 := by
  dsimp only
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  calc
    _ = Matrix.diagonal r * (U * (Matrix.diagonal c * (Matrix.diagonal c)ᴴ) * Uᴴ) *
        (Matrix.diagonal r)ᴴ := by noncomm_ring
    _ = _ := by rw [diagonal_phase_unitary c hc, Matrix.mul_one, hU,
      Matrix.mul_one, diagonal_phase_unitary r hr]

theorem one_anchor_bargmann {n : ℕ} (hn : 3 ≤ n)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (P Q R : OrthonormalBasis (Fin n) ℂ E)
    (hPQ : ∀ i j, ‖inner ℂ (P i) (Q j)‖^2 = 1/(n : ℝ))
    (hQR : ∀ i j, ‖inner ℂ (Q i) (R j)‖^2 = 1/(n : ℝ))
    (hRP : ∀ i j, ‖inner ℂ (R i) (P j)‖^2 = 1/(n : ℝ)) (a : Fin n) :
    ∃ b c, (inner ℂ (P a) (Q b) * inner ℂ (Q b) (R c) *
      inner ℂ (R c) (P a)).re ≠ 1/(n : ℝ)^2 := by
  classical
  by_contra h
  push_neg at h
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hs : (Real.sqrt (n : ℝ))^2 = n := Real.sq_sqrt (by positivity)
  let r : Fin n → ℂ := fun b => (Real.sqrt (n : ℝ) : ℂ) * inner ℂ (P a) (Q b)
  let c : Fin n → ℂ := fun c => (Real.sqrt (n : ℝ) : ℂ) * inner ℂ (R c) (P a)
  have hr (b : Fin n) : ‖r b‖=1 := by
    apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num)).mp
    dsimp [r]
    rw [norm_mul, mul_pow, hPQ, Complex.norm_real, Real.norm_eq_abs, sq_abs, hs]
    field_simp
  have hc (b : Fin n) : ‖c b‖=1 := by
    apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num)).mp
    dsimp [c]
    rw [norm_mul, mul_pow, hRP, Complex.norm_real, Real.norm_eq_abs, sq_abs, hs]
    field_simp
  let U := Q.toBasis.toMatrix R
  have hU : U*Uᴴ=1 := Q.toMatrix_orthonormalBasis_self_mul_conjTranspose R
  let Z := Matrix.diagonal r * U * Matrix.diagonal c
  have hZ : Z*Zᴴ=1 := diagonal_gauge_unitary U hU r c hr hc
  have hflat (i j : Fin n) : ‖Z i j‖^2=1/(n : ℝ) := by
    dsimp [Z]
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, norm_mul, hr i, hc j,
      one_mul, mul_one]
    simpa only [U, Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.repr_apply_apply] using hQR i j
  have hreal (i j : Fin n) : (Z i j).re=1/(n : ℝ) := by
    have hsC : (Real.sqrt (n : ℝ) : ℂ)*(Real.sqrt (n : ℝ) : ℂ)=(n : ℂ) := by
      exact_mod_cast (show Real.sqrt (n : ℝ)*Real.sqrt (n : ℝ)=(n : ℝ) by nlinarith [hs])
    have he : Z i j=(n : ℂ)*(inner ℂ (P a) (Q i)*inner ℂ (Q i) (R j)*
        inner ℂ (R j) (P a)) := by
      dsimp [Z, U, r, c]
      simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Module.Basis.toMatrix_apply,
        OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
      rw [← hsC]
      ring
    rw [he]
    simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero, h]
    field_simp
  exact unitary_flat_not_constant_real hn Z hZ hflat hreal

end MUMAnchor
end

section
open scoped BigOperators ComplexConjugate MatrixOrder Matrix.Norms.L2Operator
open Matrix MUMSpectral MUMCompatibility

namespace MUMAnchor
noncomputable section

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def basisKetBra (B : OrthonormalBasis (Fin n) ℂ E) (x y : E) : Mat n :=
  Matrix.vecMulVec (B.repr x) (star (B.repr y))

theorem repr_dot_inner (B : OrthonormalBasis (Fin n) ℂ E) (x y : E) :
    star (B.repr x) ⬝ᵥ B.repr y = inner ℂ x y := by
  simpa only [dotProduct, Pi.star_apply, PiLp.inner_apply, RCLike.inner_apply', starRingEnd_apply] using
    B.repr.inner_map_map x y

theorem basisKetBra_mul (B : OrthonormalBasis (Fin n) ℂ E) (x y z w : E) :
    basisKetBra B x y * basisKetBra B z w = inner ℂ y z • basisKetBra B x w := by
  rw [basisKetBra, basisKetBra, Matrix.vecMulVec_mul_vecMulVec, repr_dot_inner]
  ext i j
  simp only [basisKetBra, Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem basis_projector_sandwich (B : OrthonormalBasis (Fin n) ℂ E) (x y z : E) :
    basisKetBra B x x * basisKetBra B y y * basisKetBra B z z * basisKetBra B x x =
      (inner ℂ x y * inner ℂ y z * inner ℂ z x) • basisKetBra B x x := by
  rw [basisKetBra_mul, Matrix.smul_mul, basisKetBra_mul, smul_smul,
    Matrix.smul_mul, basisKetBra_mul, smul_smul]

theorem basisKetBra_self_isStarProjection (B : OrthonormalBasis (Fin n) ℂ E) (x : E)
    (hx : ‖x‖=1) : IsStarProjection (basisKetBra B x x) := by
  rw [isStarProjection_iff']
  constructor
  · rw [basisKetBra_mul, inner_self_eq_norm_sq_to_K, hx]
    norm_num
  · change (basisKetBra B x x)ᴴ=basisKetBra B x x
    simp [basisKetBra]

theorem basisKetBra_orthogonal (B P : OrthonormalBasis (Fin n) ℂ E)
    (a b : Fin n) (hab : a≠b) :
    basisKetBra B (P a) (P a) * basisKetBra B (P b) (P b)=0 := by
  rw [basisKetBra_mul, orthonormal_iff_ite.mp P.orthonormal a b]
  simp [hab]

theorem basisKetBra_complete (B P : OrthonormalBasis (Fin n) ℂ E) :
    (∑ a, basisKetBra B (P a) (P a))=(1 : Mat n) := by
  calc
    _ = B.toBasis.toMatrix P * (B.toBasis.toMatrix P)ᴴ := by
      ext i j
      simp [basisKetBra, Matrix.sum_apply, Matrix.vecMulVec_apply, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Module.Basis.toMatrix_apply,
        OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
    _ = 1 := B.toMatrix_orthonormalBasis_self_mul_conjTranspose P

theorem basisKetBra_unbiased (B P Q : OrthonormalBasis (Fin n) ℂ E)
    (hPQ : ∀ a b, ‖inner ℂ (P a) (Q b)‖^2=1/(n : ℝ)) (a b : Fin n) :
    basisKetBra B (P a) (P a) * basisKetBra B (Q b) (Q b) * basisKetBra B (P a) (P a) =
      (1/(n : ℝ)) • basisKetBra B (P a) (P a) := by
  rw [basisKetBra_mul, Matrix.smul_mul, basisKetBra_mul, smul_smul]
  have hh : inner ℂ (P a) (Q b) * inner ℂ (Q b) (P a)=(1/(n : ℝ) : ℂ) := by
    rw [← inner_conj_symm (Q b) (P a), Complex.mul_conj, Complex.normSq_eq_norm_sq, hPQ a b]
    push_cast
    rfl
  rw [hh]
  ext i j
  simp [Complex.real_smul]

def basisPVM (B P : OrthonormalBasis (Fin n) ℂ E) : PVM n n where
  proj a := basisKetBra B (P a) (P a)
  isProj a := basisKetBra_self_isStarProjection B (P a) (P.norm_eq_one a)
  orthogonal a b hab := basisKetBra_orthogonal B P a b hab
  complete := basisKetBra_complete B P

theorem basisPVM_unbiased (B P Q : OrthonormalBasis (Fin n) ℂ E)
    (hPQ : ∀ a b, ‖inner ℂ (P a) (Q b)‖^2=1/(n : ℝ)) :
    Unbiased (basisPVM B P) (basisPVM B Q) := by
  constructor
  · intro a b
    simpa [basisPVM, one_div] using basisKetBra_unbiased B P Q hPQ a b
  · intro a b
    have hQP : ∀ b a, ‖inner ℂ (Q b) (P a)‖^2=1/(n : ℝ) := by
      intro b a
      rw [norm_inner_symm]
      exact hPQ a b
    simpa [basisPVM, one_div] using basisKetBra_unbiased B Q P hQP b a

theorem amplitudeH_mul_anchor (B P Q R : OrthonormalBasis (Fin n) ℂ E)
    (a b c : Fin n) :
    amplitudeH (basisPVM B P) (basisPVM B Q) (basisPVM B R) a b c *
      (basisPVM B P).proj a =
    (2*(inner ℂ (P a) (Q b)*inner ℂ (Q b) (R c)*inner ℂ (R c) (P a)).re-
      2/(n : ℝ)^2) • (basisPVM B P).proj a := by
  have hc : inner ℂ (P a) (R c)*inner ℂ (R c) (Q b)*inner ℂ (Q b) (P a) =
      conj (inner ℂ (P a) (Q b)*inner ℂ (Q b) (R c)*inner ℂ (R c) (P a)) := by
    simp only [map_mul, inner_conj_symm]
    ring
  have hAA : (basisPVM B P).proj a * (basisPVM B P).proj a = (basisPVM B P).proj a :=
    ((basisPVM B P).isProj a).isIdempotentElem
  unfold amplitudeH
  rw [Matrix.sub_mul, Matrix.smul_mul, hAA, Matrix.mul_add, Matrix.add_mul]
  simp only [basisPVM, ← Matrix.mul_assoc]
  rw [basis_projector_sandwich, basis_projector_sandwich, hc, ← add_smul, Complex.add_conj]
  ext i j
  simp [basisPVM, Complex.real_smul]
  ring

theorem basis_amplitude_separates (hn : 3 ≤ n)
    (B P Q R : OrthonormalBasis (Fin n) ℂ E)
    (hPQ : ∀ i j, ‖inner ℂ (P i) (Q j)‖^2=1/(n : ℝ))
    (hQR : ∀ i j, ‖inner ℂ (Q i) (R j)‖^2=1/(n : ℝ))
    (hRP : ∀ i j, ‖inner ℂ (R i) (P j)‖^2=1/(n : ℝ))
    (a : Fin n) (v : Fin n → ℂ) (hv : v ≠ 0)
    (hAv : (basisPVM B P).proj a *ᵥ v = v) :
    ∃ b c, amplitudeH (basisPVM B P) (basisPVM B Q) (basisPVM B R) a b c *ᵥ v ≠ 0 := by
  obtain ⟨b,c,hphase⟩ := one_anchor_bargmann hn P Q R hPQ hQR hRP a
  refine ⟨b,c,?_⟩
  intro hz
  have hh := congrArg (fun M : Mat n => M *ᵥ v) (amplitudeH_mul_anchor B P Q R a b c)
  rw [← Matrix.mulVec_mulVec, hAv, hz, Matrix.smul_mulVec, hAv] at hh
  have hcoeff : 2*(inner ℂ (P a) (Q b)*inner ℂ (Q b) (R c)*
      inner ℂ (R c) (P a)).re-2/(n : ℝ)^2 ≠ 0 := by
    intro h0
    apply hphase
    linarith [show 2/(n : ℝ)^2 = 2*(1/(n : ℝ)^2) by ring]
  exact (smul_ne_zero hcoeff hv) hh.symm

end
end MUMAnchor
end

section
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator ComplexOrder
open Matrix MUMSpectral MUMCompatibility

namespace MUMAnchor
noncomputable section

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem first_marginal_posDef (hn : 3 ≤ n)
    (B P Q R : OrthonormalBasis (Fin n) ℂ E)
    (hPQ : ∀ i j, ‖inner ℂ (P i) (Q j)‖^2=1/(n : ℝ))
    (hQR : ∀ i j, ‖inner ℂ (Q i) (R j)‖^2=1/(n : ℝ))
    (hRP : ∀ i j, ‖inner ℂ (R i) (P j)‖^2=1/(n : ℝ))
    (x : ℝ) (hx : 0<x) (hroot : rootEquation n x) (a : Fin n) :
    ((∑ b, ∑ c, parent (basisPVM B P) (basisPVM B Q) (basisPVM B R) x a b c) -
      ((1+x)/3) • (basisPVM B P).proj a).PosDef := by
  have hn0 : 0<n := by omega
  rw [marginal_certificate hn0 _ _ _ (basisPVM_unbiased B P Q hPQ)
    (basisPVM_unbiased B R P hRP).symm (basisPVM_unbiased B Q R hQR) x hx hroot a]
  have hp := weighted_sos_posDef ((basisPVM B P).proj a) ((basisPVM B P).isProj a)
    (fun bc : Fin n × Fin n => amplitudeH (basisPVM B P) (basisPVM B Q) (basisPVM B R)
      a bc.1 bc.2) (scale n x) (scale n x*coeffC n x)
    (scale_pos hn0 hx) (mul_pos (scale_pos hn0 hx) (coeffC_pos hn0 hx))
    (by
      intro v hv hAv
      obtain ⟨b,c,hbc⟩ := basis_amplitude_separates hn B P Q R hPQ hQR hRP a v hv hAv
      exact ⟨(b,c),hbc⟩)
  simpa only [Fintype.sum_prod_type] using hp

theorem second_marginal_posDef (hn : 3 ≤ n)
    (B P Q R : OrthonormalBasis (Fin n) ℂ E)
    (hPQ : ∀ i j, ‖inner ℂ (P i) (Q j)‖^2=1/(n : ℝ))
    (hQR : ∀ i j, ‖inner ℂ (Q i) (R j)‖^2=1/(n : ℝ))
    (hRP : ∀ i j, ‖inner ℂ (R i) (P j)‖^2=1/(n : ℝ))
    (x : ℝ) (hx : 0<x) (hroot : rootEquation n x) (b : Fin n) :
    ((∑ a, ∑ c, parent (basisPVM B P) (basisPVM B Q) (basisPVM B R) x a b c) -
      ((1+x)/3) • (basisPVM B Q).proj b).PosDef := by
  simp_rw [parent_swap12 (basisPVM B P) (basisPVM B Q)]
  apply first_marginal_posDef hn B Q P R
  · intro i j; rw [norm_inner_symm]; exact hPQ j i
  · intro i j; rw [norm_inner_symm]; exact hRP j i
  · intro i j; rw [norm_inner_symm]; exact hQR j i
  · exact hx
  · exact hroot

theorem third_marginal_posDef (hn : 3 ≤ n)
    (B P Q R : OrthonormalBasis (Fin n) ℂ E)
    (hPQ : ∀ i j, ‖inner ℂ (P i) (Q j)‖^2=1/(n : ℝ))
    (hQR : ∀ i j, ‖inner ℂ (Q i) (R j)‖^2=1/(n : ℝ))
    (hRP : ∀ i j, ‖inner ℂ (R i) (P j)‖^2=1/(n : ℝ))
    (x : ℝ) (hx : 0<x) (hroot : rootEquation n x) (c : Fin n) :
    ((∑ a, ∑ b, parent (basisPVM B P) (basisPVM B Q) (basisPVM B R) x a b c) -
      ((1+x)/3) • (basisPVM B R).proj c).PosDef := by
  simp_rw [parent_cycle (basisPVM B P) (basisPVM B Q)]
  exact first_marginal_posDef hn B R P Q hRP hPQ hQR x hx hroot c

theorem strict_explicit_parent (hn : 3 ≤ n)
    (B P Q R : OrthonormalBasis (Fin n) ℂ E)
    (hPQ : ∀ i j, ‖inner ℂ (P i) (Q j)‖^2=1/(n : ℝ))
    (hQR : ∀ i j, ‖inner ℂ (Q i) (R j)‖^2=1/(n : ℝ))
    (hRP : ∀ i j, ‖inner ℂ (R i) (P j)‖^2=1/(n : ℝ))
    (x : ℝ) (hx : 0<x) (hroot : rootEquation n x) :
    ∃ ε : ℝ, 0<ε ∧ IsParent (basisPVM B P) (basisPVM B Q) (basisPVM B R)
      ((1+x)/3+ε) (parent (basisPVM B P) (basisPVM B Q) (basisPVM B R) x) := by
  classical
  have hn0 : 0<n := by omega
  letI : NeZero n := ⟨Nat.ne_of_gt hn0⟩
  let A : Fin n ⊕ (Fin n ⊕ Fin n) → Mat n :=
    Sum.elim (basisPVM B P).proj (Sum.elim (basisPVM B Q).proj (basisPVM B R).proj)
  let T : Fin n ⊕ (Fin n ⊕ Fin n) → Mat n := Sum.elim
    (fun a => (∑ b, ∑ c, parent (basisPVM B P) (basisPVM B Q) (basisPVM B R) x a b c)-
      ((1+x)/3) • (basisPVM B P).proj a)
    (Sum.elim
      (fun b => (∑ a, ∑ c, parent (basisPVM B P) (basisPVM B Q) (basisPVM B R) x a b c)-
        ((1+x)/3) • (basisPVM B Q).proj b)
      (fun c => (∑ a, ∑ b, parent (basisPVM B P) (basisPVM B Q) (basisPVM B R) x a b c)-
        ((1+x)/3) • (basisPVM B R).proj c))
  have hA : ∀ i, IsStarProjection (A i) := by
    intro i
    rcases i with a | b | c
    · exact (basisPVM B P).isProj a
    · exact (basisPVM B Q).isProj b
    · exact (basisPVM B R).isProj c
  have hT : ∀ i, (T i).PosDef := by
    intro i
    rcases i with a | b | c
    · exact first_marginal_posDef hn B P Q R hPQ hQR hRP x hx hroot a
    · exact second_marginal_posDef hn B P Q R hPQ hQR hRP x hx hroot b
    · exact third_marginal_posDef hn B P Q R hPQ hQR hRP x hx hroot c
  obtain ⟨ε,hε,hgap⟩ := finite_posDef_projection_gap hn0 A T hA hT
  have hp := explicit_parent hn0 (basisPVM B P) (basisPVM B Q) (basisPVM B R)
    (basisPVM_unbiased B P Q hPQ) (basisPVM_unbiased B R P hRP).symm
    (basisPVM_unbiased B Q R hQR) x hx hroot
  refine ⟨ε,hε,hp.1,hp.2.1,?_,?_,?_⟩
  · intro a
    have hh := hgap (Sum.inl a)
    dsimp [A,T] at hh
    convert hh using 1 <;> module
  · intro b
    have hh := hgap (Sum.inr (Sum.inl b))
    dsimp [A,T] at hh
    convert hh using 1 <;> module
  · intro c
    have hh := hgap (Sum.inr (Sum.inr c))
    dsimp [A,T] at hh
    convert hh using 1 <;> module

theorem strict_parentAt (hn : 3 ≤ n)
    (B P Q R : OrthonormalBasis (Fin n) ℂ E)
    (hPQ : ∀ i j, ‖inner ℂ (P i) (Q j)‖^2=1/(n : ℝ))
    (hQR : ∀ i j, ‖inner ℂ (Q i) (R j)‖^2=1/(n : ℝ))
    (hRP : ∀ i j, ‖inner ℂ (R i) (P j)‖^2=1/(n : ℝ))
    (x : ℝ) (hx : 0<x) (hroot : rootEquation n x) :
    ∃ ε : ℝ, 0<ε ∧ ParentAt (basisPVM B P) (basisPVM B Q) (basisPVM B R) ((1+x)/3+ε) := by
  obtain ⟨ε,hε,hp⟩ := strict_explicit_parent hn B P Q R hPQ hQR hRP x hx hroot
  exact ⟨ε,hε,_,hp⟩

end
end MUMAnchor
end

section
open scoped BigOperators ComplexConjugate
namespace MUMCompatibility
noncomputable section
abbrev Frames (n:ℕ) := Fin 3 → Fin n → EuclideanSpace ℂ (Fin n)

def IsMUBFrame {n:ℕ} (F:Frames n) : Prop :=
  (∀ k i j, inner ℂ (F k i) (F k j) = if i=j then 1 else 0) ∧
  (∀ k l, k≠l → ∀ i j, ‖inner ℂ (F k i) (F l j)‖^2 = 1/(n:ℝ))

theorem frame_orthonormal {n:ℕ} {F:Frames n} (h:IsMUBFrame F) (k:Fin 3) :
    Orthonormal ℂ (F k) := orthonormal_iff_ite.mpr (h.1 k)

def frameBasis {n:ℕ} {F:Frames n} (h:IsMUBFrame F) (k:Fin 3) :
    OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)) :=
  OrthonormalBasis.mk (frame_orthonormal h k)
    ((frame_orthonormal h k).linearIndependent.span_eq_top_of_card_eq_finrank'
      (by simp)).ge

@[simp] theorem frameBasis_apply {n:ℕ} {F:Frames n} (h:IsMUBFrame F) (k:Fin 3) (a:Fin n) :
    frameBasis h k a = F k a := by simp [frameBasis]

theorem isClosed_MUBFrame (n:ℕ) : IsClosed {F:Frames n | IsMUBFrame F} := by
  simp only [IsMUBFrame,Set.setOf_and,Set.setOf_forall]
  apply IsClosed.inter
  · exact isClosed_iInter fun k => isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_eq (by fun_prop) continuous_const
  · exact isClosed_iInter fun k => isClosed_iInter fun l => isClosed_iInter fun h =>
      isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_eq (by fun_prop) continuous_const

theorem isCompact_MUBFrame (n:ℕ) : IsCompact {F:Frames n | IsMUBFrame F} := by
  apply (isCompact_closedBall (0:Frames n) 1).of_isClosed_subset (isClosed_MUBFrame n)
  intro F hF
  rw [Metric.mem_closedBall,dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1)).mpr
  intro k
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1)).mpr
  intro i
  exact ((frame_orthonormal hF k).norm_eq_one i).le

end
end MUMCompatibility
end

section
open scoped BigOperators ComplexConjugate MatrixOrder Matrix.Norms.L2Operator ComplexOrder
open Matrix MUMSpectral
namespace MUMCompatibility
noncomputable section
set_option maxHeartbeats 2000000

def frameProj {n:ℕ} (F:Frames n) (k:Fin 3) (a:Fin n) : Mat n :=
  Matrix.vecMulVec (WithLp.ofLp (F k a)) (star (WithLp.ofLp (F k a)))

def frameSlack {n:ℕ} (F:Frames n) (x:ℝ) (a:Fin n) : Mat n :=
  (∑ b,∑ c, scale n x • rawParent n x (frameProj F 0 a+frameProj F 1 b+frameProj F 2 c)) -
    ((1+x)/3) • frameProj F 0 a

@[fun_prop] theorem continuous_frameProj {n:ℕ} (k:Fin 3) (a:Fin n) :
    Continuous (fun F:Frames n => frameProj F k a) := by
  unfold frameProj
  fun_prop

@[fun_prop] theorem continuous_frameSlack {n:ℕ} (x:ℝ) (a:Fin n) :
    Continuous (fun F:Frames n => frameSlack F x a) := by
  unfold frameSlack rawParent polyQ
  fun_prop (disch := aesop) [continuous_frameProj]

theorem frameProj_eq_basisPVM {n:ℕ} {F:Frames n} (h:IsMUBFrame F) (k:Fin 3) (a:Fin n) :
    frameProj F k a = (MUMAnchor.basisPVM (EuclideanSpace.basisFun (Fin n) ℂ) (frameBasis h k)).proj a := by
  simp [frameProj,MUMAnchor.basisPVM,MUMAnchor.basisKetBra]
  rfl

theorem frameSlack_eq_basis {n:ℕ} {F:Frames n} (h:IsMUBFrame F) (x:ℝ) (a:Fin n) :
    frameSlack F x a =
      (∑ b,∑ c, parent
        (MUMAnchor.basisPVM (EuclideanSpace.basisFun (Fin n) ℂ) (frameBasis h 0))
        (MUMAnchor.basisPVM (EuclideanSpace.basisFun (Fin n) ℂ) (frameBasis h 1))
        (MUMAnchor.basisPVM (EuclideanSpace.basisFun (Fin n) ℂ) (frameBasis h 2)) x a b c) -
       ((1+x)/3) • (MUMAnchor.basisPVM (EuclideanSpace.basisFun (Fin n) ℂ) (frameBasis h 0)).proj a := by
  simp only [frameSlack,parent,selected,frameProj_eq_basisPVM h]

theorem compact_positive_lower_bound {T:Type*} [TopologicalSpace T] {K:Set T}
    (hK:IsCompact K) {f:T→ℝ} (hf:ContinuousOn f K) (hp:∀t∈K,0<f t) :
    ∃ e:ℝ, 0<e ∧ ∀t∈K,e≤f t := by
  by_cases hne:K.Nonempty
  · obtain ⟨t,ht,hmin⟩ := hK.exists_isMinOn hne hf
    exact ⟨f t,hp t ht,hmin⟩
  · exact ⟨1,by norm_num,fun t ht => False.elim (hne ⟨t,ht⟩)⟩

theorem uniform_frame_quadratic_gap {n:ℕ} (x:ℝ)
    (hp:∀F:Frames n,IsMUBFrame F → ∀a,(frameSlack F x a).PosDef) :
    ∃e:ℝ,0<e ∧ ∀F:Frames n,IsMUBFrame F → ∀a (v:EuclideanSpace ℂ (Fin n)),
      ‖v‖=1 → e≤(star (WithLp.ofLp v) ⬝ᵥ (frameSlack F x a *ᵥ WithLp.ofLp v)).re := by
  let K:Set (Fin n × (Frames n × EuclideanSpace ℂ (Fin n))) :=
    Set.univ ×ˢ ({F:Frames n | IsMUBFrame F} ×ˢ Metric.sphere 0 1)
  have hK:IsCompact K := isCompact_univ.prod ((isCompact_MUBFrame n).prod (isCompact_sphere 0 1))
  let f: (Fin n × (Frames n × EuclideanSpace ℂ (Fin n))) → ℝ := fun t =>
    (star (WithLp.ofLp t.2.2) ⬝ᵥ (frameSlack t.2.1 x t.1 *ᵥ WithLp.ofLp t.2.2)).re
  have hf:Continuous f := by
    apply continuous_prod_of_discrete_left.mpr
    intro a
    dsimp [f]
    fun_prop (disch := aesop) [continuous_frameSlack]
  have hpos:∀t∈K,0<f t := by
    intro t ht
    have hv : WithLp.ofLp t.2.2 ≠ 0 := by
      intro hz
      have hvzero : t.2.2=0 := by exact WithLp.ofLp_injective 2 hz
      have hs:=ht.2.2
      simp [Metric.mem_sphere, hvzero] at hs
    exact RCLike.pos_iff.mp ((hp t.2.1 ht.2.1 t.1).dotProduct_mulVec_pos hv) |>.1
  obtain ⟨e,he,hle⟩ := compact_positive_lower_bound hK hf.continuousOn hpos
  refine ⟨e,he,?_⟩
  intro F hF a v hv
  exact hle ⟨a,F,v⟩ ⟨Set.mem_univ _,hF,by simpa [Metric.mem_sphere,dist_zero_right] using hv⟩

end
end MUMCompatibility
end

section
open scoped BigOperators ComplexConjugate MatrixOrder Matrix.Norms.L2Operator ComplexOrder
open Matrix MUMSpectral MUMAnchor
namespace MUMCompatibility
noncomputable section
set_option maxHeartbeats 2000000

variable {n:ℕ} {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def basesFrame (B P Q R:OrthonormalBasis (Fin n) ℂ E) : Frames n :=
  ![fun i => B.repr (P i), fun i => B.repr (Q i),fun i => B.repr (R i)]

theorem basesFrame_mub (B P Q R:OrthonormalBasis (Fin n) ℂ E)
    (hPQ : ∀ i j, ‖inner ℂ (P i) (Q j)‖^2=1/(n:ℝ))
    (hQR : ∀ i j, ‖inner ℂ (Q i) (R j)‖^2=1/(n:ℝ))
    (hRP : ∀ i j, ‖inner ℂ (R i) (P j)‖^2=1/(n:ℝ)) :
    IsMUBFrame (basesFrame B P Q R) := by
  constructor
  · intro k i j
    fin_cases k
    · change inner ℂ (B.repr (P i)) (B.repr (P j)) = _
      rw [B.repr.inner_map_map]
      exact orthonormal_iff_ite.mp P.orthonormal i j
    · change inner ℂ (B.repr (Q i)) (B.repr (Q j)) = _
      rw [B.repr.inner_map_map]
      exact orthonormal_iff_ite.mp Q.orthonormal i j
    · change inner ℂ (B.repr (R i)) (B.repr (R j)) = _
      rw [B.repr.inner_map_map]
      exact orthonormal_iff_ite.mp R.orthonormal i j
  · intro k l hkl i j
    simp only [one_div] at hPQ hQR hRP
    fin_cases k <;> fin_cases l
    all_goals try exact False.elim (hkl rfl)
    all_goals norm_num [basesFrame,B.repr.inner_map_map]
    all_goals first | exact hPQ i j | exact hQR i j | exact hRP i j |
      (rw [norm_inner_symm]; first | exact hPQ j i | exact hQR j i | exact hRP j i)

theorem basesFrame_slack (B P Q R:OrthonormalBasis (Fin n) ℂ E) (x:ℝ) (a:Fin n) :
    frameSlack (basesFrame B P Q R) x a =
      (∑ b,∑ c,parent (basisPVM B P) (basisPVM B Q) (basisPVM B R) x a b c) -
      ((1+x)/3) • (basisPVM B P).proj a := rfl

theorem uniform_basis_quadratic_gap (hn:3≤n) (x:ℝ) (hx:0<x) (hroot:rootEquation n x) :
    ∃e:ℝ,0<e ∧ ∀(B P Q R:OrthonormalBasis (Fin n) ℂ E),
      (∀ i j, ‖inner ℂ (P i) (Q j)‖^2=1/(n:ℝ)) →
      (∀ i j, ‖inner ℂ (Q i) (R j)‖^2=1/(n:ℝ)) →
      (∀ i j, ‖inner ℂ (R i) (P j)‖^2=1/(n:ℝ)) →
      ∀ a (v:EuclideanSpace ℂ (Fin n)), ‖v‖=1 →
        e≤(star (WithLp.ofLp v) ⬝ᵥ
          (((∑ b,∑ c,parent (basisPVM B P) (basisPVM B Q) (basisPVM B R) x a b c) -
          ((1+x)/3) • (basisPVM B P).proj a) *ᵥ WithLp.ofLp v)).re := by
  have hp:∀F:Frames n,IsMUBFrame F → ∀a,(frameSlack F x a).PosDef := by
    intro F hF a
    rw [frameSlack_eq_basis hF]
    apply first_marginal_posDef hn _ _ _ _ _ _ _ x hx hroot
    · simpa only [frameBasis_apply] using hF.2 0 1 (by decide)
    · simpa only [frameBasis_apply] using hF.2 1 2 (by decide)
    · simpa only [frameBasis_apply] using hF.2 2 0 (by decide)
  obtain ⟨e,he,hbound⟩ := uniform_frame_quadratic_gap x hp
  refine ⟨e,he,?_⟩
  intro B P Q R hPQ hQR hRP a v hv
  simpa only [basesFrame_slack] using
    hbound (basesFrame B P Q R) (basesFrame_mub B P Q R hPQ hQR hRP) a v hv

end
end MUMCompatibility
end

section
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator ComplexOrder
open Matrix MUMSpectral
namespace MUMCompatibility
noncomputable section

theorem sphere_lower_bound_posSemidef {n : ℕ} (T : Mat n) (hT : T.IsHermitian) (e : ℝ)
    (hbound : ∀ v : EuclideanSpace ℂ (Fin n), ‖v‖=1 →
      e ≤ (star (WithLp.ofLp v) ⬝ᵥ (T *ᵥ WithLp.ofLp v)).re) :
    (T-e • (1:Mat n)).PosSemidef := by
  have hM : (T-e • (1:Mat n)).IsHermitian :=
    hT.sub (Matrix.isHermitian_one.smul (IsSelfAdjoint.all e))
  apply hM.posSemidef_iff_eigenvalues_nonneg.mpr
  intro i
  have hv : ‖hM.eigenvectorBasis i‖=1 := hM.eigenvectorBasis.orthonormal.1 i
  have hb := hbound (hM.eigenvectorBasis i) hv
  have hu : star (WithLp.ofLp (hM.eigenvectorBasis i)) ⬝ᵥ
      WithLp.ofLp (hM.eigenvectorBasis i) = (1:ℂ) := by
    have hi : inner ℂ (hM.eigenvectorBasis i) (hM.eigenvectorBasis i) = (1:ℂ) := by
      rw [inner_self_eq_norm_sq_to_K, hv]
      norm_num
    simpa only [dotProduct, Pi.star_apply, PiLp.inner_apply, RCLike.inner_apply', starRingEnd_apply] using hi
  rw [hM.eigenvalues_eq]
  simp only [sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul,
    hu, RCLike.re_to_complex, Complex.sub_re, Complex.smul_re, Complex.one_re, smul_eq_mul, mul_one]
  exact sub_nonneg.mpr hb

end
end MUMCompatibility
end

section
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator ComplexOrder
open Matrix MUMSpectral MUMAnchor
namespace MUMCompatibility
noncomputable section
set_option maxHeartbeats 2000000

theorem uniform_basis_parent {n:ℕ} {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (hn:3≤n) (x:ℝ) (hx:0<x) (hroot:rootEquation n x) :
    ∃e:ℝ,0<e ∧ ∀(B P Q R:OrthonormalBasis (Fin n) ℂ E),
      (∀ i j, ‖inner ℂ (P i) (Q j)‖^2=1/(n:ℝ)) →
      (∀ i j, ‖inner ℂ (Q i) (R j)‖^2=1/(n:ℝ)) →
      (∀ i j, ‖inner ℂ (R i) (P j)‖^2=1/(n:ℝ)) →
      IsParent (basisPVM B P) (basisPVM B Q) (basisPVM B R) (((1+x)/3)+e)
        (parent (basisPVM B P) (basisPVM B Q) (basisPVM B R) x) := by
  obtain ⟨e,he,hbound⟩ := uniform_basis_quadratic_gap (E:=E) hn x hx hroot
  have hfirst : ∀(B P Q R:OrthonormalBasis (Fin n) ℂ E),
      (∀ i j, ‖inner ℂ (P i) (Q j)‖^2=1/(n:ℝ)) →
      (∀ i j, ‖inner ℂ (Q i) (R j)‖^2=1/(n:ℝ)) →
      (∀ i j, ‖inner ℂ (R i) (P j)‖^2=1/(n:ℝ)) → ∀a,
      ((∑ b,∑ c,parent (basisPVM B P) (basisPVM B Q) (basisPVM B R) x a b c)-
        (((1+x)/3)+e) • (basisPVM B P).proj a).PosSemidef := by
    intro B P Q R hPQ hQR hRP a
    have hpd := first_marginal_posDef hn B P Q R hPQ hQR hRP x hx hroot a
    have hgap := sphere_lower_bound_posSemidef _ hpd.isHermitian e
      (hbound B P Q R hPQ hQR hRP a)
    have hc := (projection_complement_posSemidef (basisPVM B P) a).smul he.le
    convert hgap.add hc using 1 <;> module
  refine ⟨e,he,?_⟩
  intro B P Q R hPQ hQR hRP
  have hbase := explicit_parent (by omega) (basisPVM B P) (basisPVM B Q) (basisPVM B R)
    (basisPVM_unbiased B P Q hPQ) (basisPVM_unbiased B R P hRP).symm
    (basisPVM_unbiased B Q R hQR) x hx hroot
  refine ⟨hbase.1,hbase.2.1,hfirst B P Q R hPQ hQR hRP,?_,?_⟩
  · intro b
    simp_rw [parent_swap12 (basisPVM B P) (basisPVM B Q)]
    apply hfirst B Q P R
    · intro i j; rw [norm_inner_symm]; exact hPQ j i
    · intro i j; rw [norm_inner_symm]; exact hRP j i
    · intro i j; rw [norm_inner_symm]; exact hQR j i
  · intro c
    simp_rw [parent_cycle (basisPVM B P) (basisPVM B Q)]
    exact hfirst B R P Q hRP hPQ hQR c

end
end MUMCompatibility
end

section
open MUMSpectral MUMCompatibility

theorem pairwise_mum_explicit_parent :
    ∀ (n D : ℕ), 0 < n → ∀ (P Q R : MUMSpectral.PVM n D),
    MUMSpectral.Unbiased P Q → MUMSpectral.Unbiased P R → MUMSpectral.Unbiased Q R →
    ∀ (x : ℝ), 0 < x → MUMCompatibility.rootEquation n x →
    MUMCompatibility.IsParent P Q R ((1+x)/3) (MUMCompatibility.parent P Q R x) := by
  intro n D hn P Q R hPQ hPR hQR x hx hroot
  exact explicit_parent hn P Q R hPQ hPR hQR x hx hroot

theorem pairwise_mum_compatibility_exists (n D : ℕ) (hn : 0<n)
    (P Q R : PVM n D) (hPQ : Unbiased P Q) (hPR : Unbiased P R) (hQR : Unbiased Q R) :
    ∃ x : ℝ, 0<x ∧ rootEquation n x ∧ ParentAt P Q R ((1+x)/3) := by
  obtain ⟨x,hx,_,hroot⟩ := positive_root_exists n hn
  exact ⟨x,hx,hroot,parent P Q R x,explicit_parent hn P Q R hPQ hPR hQR x hx hroot⟩

theorem pairwise_mum_positive_root_unique (n : ℕ) (hn : 0<n) :
    ∃! x : ℝ, 0<x ∧ rootEquation n x := by
  obtain ⟨x,hx,_,hroot⟩ := positive_root_exists n hn
  refine ⟨x,⟨hx,hroot⟩,?_⟩
  intro y hy
  exact positive_root_unique n hn y x hy.1 hx hy.2 hroot

theorem four_outcome_pairwise_mum_compatibility (D : ℕ) (P Q R : PVM 4 D)
    (hPQ : Unbiased P Q) (hPR : Unbiased P R) (hQR : Unbiased Q R) :
    IsParent P Q R ((1+Real.cos (Real.pi/9))/3)
      (parent P Q R (Real.cos (Real.pi/9))) := by
  exact explicit_parent (by decide) P Q R hPQ hPR hQR _ four_cos_root.1 four_cos_root.2

theorem mub_strict_compatibility {n : ℕ} (hn : 3≤n)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (B P Q R : OrthonormalBasis (Fin n) ℂ E)
    (hPQ : ∀ i j, ‖inner ℂ (P i) (Q j)‖^2=1/(n:ℝ))
    (hQR : ∀ i j, ‖inner ℂ (Q i) (R j)‖^2=1/(n:ℝ))
    (hRP : ∀ i j, ‖inner ℂ (R i) (P j)‖^2=1/(n:ℝ))
    (x : ℝ) (hx : 0<x) (hroot : rootEquation n x) :
    ∃ ε : ℝ, 0<ε ∧ IsParent (MUMAnchor.basisPVM B P) (MUMAnchor.basisPVM B Q)
      (MUMAnchor.basisPVM B R) ((1+x)/3+ε)
      (parent (MUMAnchor.basisPVM B P) (MUMAnchor.basisPVM B Q) (MUMAnchor.basisPVM B R) x) := by
  exact MUMAnchor.strict_explicit_parent hn B P Q R hPQ hQR hRP x hx hroot

theorem mub_uniform_strict_compatibility (n : ℕ) (hn : 3≤n)
    (x : ℝ) (hx : 0<x) (hroot : rootEquation n x) :
    ∃ ε : ℝ, 0<ε ∧
      ∀ B P Q R : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)),
      (∀ i j, ‖inner ℂ (P i) (Q j)‖^2=1/(n:ℝ)) →
      (∀ i j, ‖inner ℂ (Q i) (R j)‖^2=1/(n:ℝ)) →
      (∀ i j, ‖inner ℂ (R i) (P j)‖^2=1/(n:ℝ)) →
      IsParent (MUMAnchor.basisPVM B P) (MUMAnchor.basisPVM B Q) (MUMAnchor.basisPVM B R)
        ((1+x)/3+ε)
        (parent (MUMAnchor.basisPVM B P) (MUMAnchor.basisPVM B Q) (MUMAnchor.basisPVM B R) x) := by
  exact uniform_basis_parent hn x hx hroot

theorem mub_uniform_improvement_exists (n : ℕ) (hn : 3≤n) :
    ∃ x ε : ℝ, 0<x ∧ rootEquation n x ∧ 0<ε ∧
      ∀ B P Q R : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)),
      (∀ i j, ‖inner ℂ (P i) (Q j)‖^2=1/(n:ℝ)) →
      (∀ i j, ‖inner ℂ (Q i) (R j)‖^2=1/(n:ℝ)) →
      (∀ i j, ‖inner ℂ (R i) (P j)‖^2=1/(n:ℝ)) →
      IsParent (MUMAnchor.basisPVM B P) (MUMAnchor.basisPVM B Q) (MUMAnchor.basisPVM B R)
        ((1+x)/3+ε)
        (parent (MUMAnchor.basisPVM B P) (MUMAnchor.basisPVM B Q) (MUMAnchor.basisPVM B R) x) := by
  obtain ⟨x,hx,_,hroot⟩ := positive_root_exists n (by omega)
  obtain ⟨ε,hε,hparent⟩ := mub_uniform_strict_compatibility n hn x hx hroot
  exact ⟨x,ε,hx,hroot,hε,hparent⟩
end
