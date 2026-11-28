# Odd solvability and Hilbert’s tenth problem over the rationals

The arithmetic equivalence is the input to the repaired PL embeddability construction.

## 1. Survivor S1 (proved here, unconditional apart from the input named): HTP(Q) ⇔ c:solodd(a) ⇔ c:solodd(b)

**Lemma 1 (Q reduces to Z_(2)).** Let g(t) = t² + t + 2. For P ∈ Z[w_1..w_n] of degree D:

  P has a root in Q^n ⇔ G(a,t) := g(t)^D · P(a/g(t)) has a root (a,t) ∈ Z_(2)^{n+1}.

*Proof.*
- (⇐) The discriminant of g is −7 < 0, so g has no rational root. Hence g(t) ≠ 0, and w = a/g(t) is a root.
- (⇒) Since −7 ≡ 1 (mod 8), g has two roots r_0 ≡ 0 and r_1 ≡ 1 (mod 2) in Z_2. Given w ∈ Q^n, let k = max(0, −min_i v_2(w_i)).
- Pick t ∈ Z with t ≡ r_0 (mod 2^k). Then v_2(t − r_1) = 0, so v_2(g(t)) = v_2(t − r_0) ≥ k.
- Therefore a := g(t)·w ∈ Z_(2)^n. ∎

Conversely, HTP(Z_(2)) ≤ HTP(Q), because Z_(2) is Diophantine in Q (J. Robinson). So HTP(Z_(2)) ≡ HTP(Q), with fixed sizes carried along.

**Theorem S1.**
- (i) SYM1 ≡_m HTP(Z_(2)).
- (ii) SKEW1 ≡_m HTP(Z_(2)).
- Hence, under BB, both are Σ⁰₁-complete for fixed (m,s), and [Sk20e] Conj. c:solodd (a) and (b) hold. In both reductions every a^{ij}_q can be made even, by doubling each equation, as Conj. t:ckmvwz / t:ckmvwzg require.

*Proof of (i), ≥ direction.* Let a target quadratic system over Z_(2) be Σ c_ij r_i r_j + Σ d_i r_i + e = 0. A general system reduces to this form, with fixed size. Introduce SYM1 variables u = x_0, v = x_1, u′ = x_3, y_i, y′_i, and the equations:
- x_0 x_1 = t (b = 1);
- x_1 x_0 − x_1 x_3 = 0;
- x_0 y_i − x_0 y′_i = 0;
- the homogenisation Σ c_ij y_i y′_j (using y_i y′_i for squares) + Σ d_i x_0 y_i + e x_0 x_3 = 0 (b = 0).

Every monomial is x_α x_β with α ≠ β. Soundness:
- From x_0 x_1 = t odd, x_0 and x_1 are odd and nonzero. Hence x_3 = x_0 and y′ = y.
- Then r := y/x_0 ∈ Z_(2)^s is a root.

Completeness: given a root r, let u be an odd common denominator. Put y = u r, x_0 = x_3 = u, x_1 = 1, t = u.

*Proof of (i), ≤ direction.* If (x, t) is a Z_(2)-solution with t a unit, write x = y/σ with σ odd. Then Σ a y y = σ² t b, and σ² t is odd. So SYM1 is the Z_(2)-problem ∃x ∃t (t s = 1 ∧ …).

*Proof of (ii), ≥ direction: a Plücker pivot.* SKEW1 asks for an integral decomposable bivector P = x∧y on a fixed affine slice. An integral P that is decomposable over Q equals X∧Y with X, Y integral: take a basis e, f of span(x,y) ∩ Z^n. Then e∧f is primitive, so P = λ e∧f with λ ∈ Z.

Use coordinates 0, 1, α_0..α_s, β_0..β_s and the linear equations, with RHS t·b:
- p_01 = t;
- p_{1α_i} = 0;
- p_{0β_i} = 0;
- p_{1β_i} − p_{0α_i} = 0;
- p_{0α_0} = t;
- Σ_{ij} c^{(q)}_ij p_{α_iβ_j} = 0. Here Σ_{ij} c_ij r_i r_j = 0, with r_0 = 1, is the homogenised target.

Soundness:
- Plücker gives p_01 p_ij = p_0i p_1j − p_0j p_1i. So, with w_i := p_{0α_i}, we get p_{α_iβ_j} = w_i w_j / t and w_0 = t.
- The last equation becomes Σ c_ij (w_i/t)(w_j/t) = 0, so r = w/t ∈ Z_(2)^s, since t is odd.

Completeness: given r, take an odd T with T r ∈ Z^s, and set t = T² and w = t r. Define
- p_0j = u_j and p_1j = v_j, with u_{α_i} = w_i, v_{α_i} = 0, u_{β_i} = 0, v_{β_i} = w_i;
- p_ij = (u_i v_j − u_j v_i)/t, which lies in {0, ±(T r_i)(T r_j)} ⊂ Z.

This P equals (e_0 − Σ (v_j/t) e_j) ∧ (t e_1 + Σ u_j e_j), so it is decomposable and integral. Hence P = X∧Y as above.

*Proof of (ii), ≤ direction.* SKEW1 is bilinear, so the denominators scale out as σσ′t.

So Theorem S1 turns the Moroz–Kogan sketch (part a) into a proof. Part (b) is new as stated, and both proofs are a page long. ∎
