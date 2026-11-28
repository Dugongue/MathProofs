# The three-label LO promise CSP lower bound

The argument uses the finite-minion obstruction criterion from the cited preprint. The higher-label question remains open.

## 1. The method (useful to every lane)

Let H be a "universally hard source": PCSP(H, S) is NP-hard for every S without constant tuples. By BGKR Thm 2.1 this holds for H = CYCLE₃[L] with L ≡ 1 (mod 3), and by sandwiching for any cyclic H that receives such a tight cycle. Graph rows: BG gives every odd cycle (BGKR Thm 2.3 / Zhou), and FMW gives K₃.

Then:

> PCSP(A, B) is NP-hard whenever Pol(A, B) fails the H-loop condition ∃f ∀x : f(x∘c₁) = … = f(x∘c_r).

The reason: F_{Pol(A,B)}(H) is then constant-free, H → F, and Pol(A,B) → Pol(H, F) is a minion homomorphism (BBKO).

- For H = K₃ this is FMW + Siggers-freeness.
- For tight cycles it is new as a criterion. It is how R\* in R-P4-T2 becomes hard.
- Ordering: if H → H′, then the H-loop condition implies the H′-loop condition. So sources with no homomorphism from already-satisfied sources are the ones worth testing.

**Computation.**
1. Identify the vectors x∘c_k.
2. Encode "f is a polymorphism into B", either fully or on a sub-family of inputs; a subsystem being UNSAT is enough.
3. Run SAT.

The full system is feasible for |A|^{|H|} ≲ 10⁶. For larger systems, a sub-family works: the identified vectors, all vectors with ≤ 2 non-zero entries, and two rounds of completing third rows. That sub-family already suffices for (LO₂, LO₃) at L = 4 and for (R\*, NAE₃) at L = 4.
