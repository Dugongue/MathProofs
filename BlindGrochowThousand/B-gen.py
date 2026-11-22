"""Generate 249 matrix determinant profile instances plus the general theorem.

The modular enumeration proposes statements. Lean separately checks every equality,
inequality and full finite profile in the emitted file with kernel reduction.
"""
from pathlib import Path
from math import gcd
from random import Random

ROOT = Path(__file__).resolve().parent
HEADER = r'''
import Mathlib

open Matrix

namespace OrbitQ

variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

/-- A matrix supported in one column, with that column equal to v. -/
def column (r : n) (v : n → K) : Matrix n n K :=
  fun i j => if j = r then v i else 0

/-- The simultaneous transporter for the anchored two-matrix tuples, with a
prescribed determinant. Nonzero determinant is equivalent to invertibility. -/
def rel (a : n → K) (r : n) (v : n → K) (z : K) : Prop :=
  ∃ X : Matrix n n K, X.det = z ∧
    X * diagonal a = diagonal a * X ∧
    X * column r (fun _ => 1) = column r (fun i => v i / v r) * X

/-- The whole attainable determinant range is one scalar power family.
This follows by recovering each diagonal entry from the anchored column
equations. Infinite fields and all finite characteristics are admitted. -/
theorem profile (a : n → K) (ha : Function.Injective a) (r : n)
    (v : n → K) (hv : v r ≠ 0) (z : K) :
    rel a r v z ↔ ∃ c : K, c ^ Fintype.card n * (∏ i, v i) = z := by
  constructor
  · rintro ⟨X, hz, hA, hC⟩
    have hoff (i j : n) (hij : i ≠ j) : X i j = 0 := by
      by_contra hne
      have he := congrArg (fun M : Matrix n n K => M i j) hA
      simp only [mul_diagonal, diagonal_mul] at he
      apply hij
      apply ha
      apply mul_left_cancel₀ hne
      exact (he.trans (mul_comm _ _)).symm
    have hdiag : X = diagonal (fun i => X i i) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp
      · simp [diagonal_apply_ne _ hij, hoff i j hij]
    have hcol (i : n) : X i i = v i / v r * X r r := by
      have he := congrArg (fun M : Matrix n n K => M i r) hC
      rw [hdiag] at he
      simpa [mul_diagonal, diagonal_mul, column] using he
    let c := X r r / v r
    have hs : (fun i => X i i) = fun i => c * v i := by
      funext i
      rw [hcol]
      simp only [c, div_eq_mul_inv]
      ring
    refine ⟨c, ?_⟩
    rw [hdiag, hs, Matrix.det_diagonal, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ] at hz
    exact hz
  · rintro ⟨c, hz⟩
    refine ⟨diagonal (fun i => c * v i), ?_, ?_, ?_⟩
    · simpa only [Matrix.det_diagonal, Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_univ] using hz
    · exact (Matrix.commute_diagonal _ _).eq
    · ext i j
      simp only [diagonal_mul, mul_diagonal]
      by_cases hj : j = r
      · subst j
        simp [column]
        field_simp [hv] <;> ring
      · simp [column, hj]

/-- Concrete anchored tuples use a translated consecutive spectrum and one
coordinate twist. The width is m + 1. -/
def twisted (p m shift : ℕ) (t z : ZMod p) [Fact (Nat.Prime p)] : Prop :=
  rel (fun i : Fin (m + 1) => (i.val : ZMod p) + shift) (0 : Fin (m + 1))
    (fun i => if i = 0 then t else 1) z

private theorem twisted_iff (p m shift : ℕ) (t : ZMod p) {z : ZMod p}
    [Fact (Nat.Prime p)] (hn : m + 1 ≤ p) (ht : t ≠ 0) :
    twisted p m shift t z ↔ ∃ c : ZMod p, c ^ (m + 1) * t = z := by
  unfold twisted
  rw [profile]
  · simp
  · intro i j h
    have he : (i.val : ZMod p) = (j.val : ZMod p) := add_right_cancel h
    apply Fin.ext
    have hi := ZMod.val_natCast_of_lt (i.isLt.trans_le hn)
    have hj := ZMod.val_natCast_of_lt (j.isLt.trans_le hn)
    exact hi.symm.trans ((congrArg ZMod.val he).trans hj)
  · simpa using ht
'''.lstrip()
PRIMES = [5, 7, 11, 13, 17, 19, 23, 29, 31, 37]


def fixtures():
    rng = Random(129875)
    groups = {}
    for p in PRIMES:
        local = []
        for n in range(2, min(9, p + 1)):
            if gcd(n, p - 1) in (1, p - 1):
                continue
            powers = {pow(c, n, p) for c in range(1,p)}
            for shift in range(p):
                local.append((p, n, shift, powers))
        rng.shuffle(local)
        groups[p] = local

    # Round-robin on primes before sorting for shared Lean field instances.
    chosen = []
    while len(chosen) < 249:
        for p in PRIMES:
            if groups[p] and len(chosen) < 249:
                chosen.append(groups[p].pop())
    for idx, (p, n, shift, powers) in enumerate(chosen):
        mode = idx % 3
        if mode == 0:
            t = rng.choice(sorted(powers - {1}))
        elif mode == 1:
            t = rng.choice(sorted(set(range(1,p)) - powers))
        else:
            t = rng.randrange(1, p)
        yield (p, n, shift, idx, mode, t)


def build():
    cases = sorted(fixtures())
    targets = ["OrbitQ.profile"]
    chunks = [HEADER]
    for p in PRIMES:
        if not any(row[0] == p for row in cases):
            continue
        chunks += [f"section Q{p}", f"local instance : Fact (Nat.Prime {p}) := ⟨by decide⟩", ""]
        for prime, n, shift, idx, mode, t in cases:
            if prime != p:
                continue
            m = n - 1
            tag = f"b{idx:03}"
            targets.append(f"OrbitQ.{tag}")
            base = f"twisted {p} {m} {shift} {t}"
            if mode == 0:
                stmt = f"{base} 1"
            elif mode == 1:
                stmt = f"{base} {t} ∧ ¬ {base} 1"
            else:
                image = ', '.join(str(x) for x in sorted({pow(c, n, p)*t % p for c in range(p)}))
                stmt = f"∀ z : ZMod {p}, {base} z ↔ z ∈ ([{image}] : List (ZMod {p}))"
            chunks += [f"theorem {tag} : {stmt} := by",
                       f"  simp only [twisted_iff {p} {m} {shift} {t} (by decide) (by decide)]",
                       "  decide", ""]
        chunks.append(f"end Q{p}\n")
    chunks.append("end OrbitQ\n")
    (ROOT / "B.lean").write_text("\n".join(chunks), encoding="utf-8",newline="\n")
    (ROOT / "B.targets").write_text("\n".join(targets)+"\n",encoding="utf-8",newline="\n")


if __name__ == "__main__":
    build()
