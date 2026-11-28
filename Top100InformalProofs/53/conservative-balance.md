# Conservative balance implies small read-once formulas and the A3 operations

These are the two audited forward implications. The conditional complexity converse is a separate question.

## 1. Setting

- Template Γ: finitely many relations over a finite set D.
- Instance Φ: a conjunction of Γ-atoms on variables 1..n.
- F1 polynomial: P_Φ = Σ_{σ∈S} Π_v x_{v,σ(v)}, where S = Sol(Φ).
- Family: (P_{Φ_n}) for a p-bounded sequence of instances.
- Setting x_{v,a} = 0 imposes any unary list restriction under projection, so U_D (all unary relations) comes free.

**CB.** F = Γ ∪ U_D, with U_D the nonnegative rational unary weights. F is *balanced* (Cai–Chen–Lu, as in CDGJLMR §3) if every pps-definable function F ∈ F# and every split of its variables gives a flattening of block-rank 1. CDGJLMR Lemma 13: in the conservative case, weakly log-modular ⇒ balanced. The converse is immediate, since a 2×2 restriction by unaries is a submatrix of a flattening. So CB = weakly log-modular.

CB is decidable: CDGJLMR Lemma 48 reduces it to a finite language H ∪ Func₁(D,{1,2}), and balance is decidable by Cai–Chen–Lu.

## 2. Theorem V2.1 (proved): CB ⇒ VP

**Notation.** Fix Φ with solution set S ⊆ Dⁿ. For 0 ≤ i ≤ n and a ∈ T_i := π_{[i]}(S), put

G_i(a) = Σ_{s∈S, s|[i] = a} Π_{j=1}^{n} x_{j,s_j}.

Then G_0 = P_Φ, and G_n(s) = x^s is a monomial.

**Step 1 (balance holds formally).**
- G_i is the pps-function of Φ with a unary weight at every variable, summed over the variables after i. So with positive rational weights it lies in F#.
- Its support is T_i for formal and for positive weights alike. Each entry is a sum of *distinct* monomials with coefficient 1, so it is nonzero in every characteristic.
- A 2×2 minor inside a block is an integer polynomial that vanishes on the positive rational orthant, hence it is identically 0, hence 0 over every field.
- So the flattening G_i : T_{i−1} × D → K[x] has block-rank 1 over K[x].

**Step 2 (peeling).**
- Let β be a block of that flattening, with rows R_β ⊆ T_{i−1} and columns C_β ⊆ D.
- Block-rank 1 gives G_i(a′,c) = λ(a′)μ_β(c) on R_β × C_β, and G_i(a′,c) = 0 for c ∉ C_β, because a row's support lies inside its block.
- Summing over c gives G_{i−1}(a′) = λ(a′)M_β with M_β = Σ_{c∈C_β} μ_β(c). Hence
  - (★) G_i(a′,c) = G_{i−1}(a′) · μ_β(c) / M_β.
- Take μ_β(c) := G_i(r_β, c) for one fixed representative row r_β.

**Step 3 (recursion).**
- For a ∈ T_i with i < n, choose c* with (a,c*) ∈ T_{i+1}, and let β′ be the block of a at level i+1. By (★):
  - G_i(a) = G_{i+1}(a,c*) · M_{β′} / μ_{β′}(c*).
- Every μ is itself a value G_{i+1}(r_{β′}, c). So every quantity reduces to monomials G_n(t), through chains of length ≤ n.
- There are at most \|D\| blocks per level, because blocks have disjoint nonempty column sets. So there are at most n·\|D\|² anchor values G_i(r_β, c).
- Each anchor opens a chain of ≤ n memoised entries, so there are O(n²\|D\|²) entries, each costing O(\|D\|) operations.
- Result: a circuit with divisions of size O(n²\|D\|³) computing P_Φ = G_0(∅).

**Step 4 (division removal).**
- Every divisor is some μ = G_j(·), a nonzero polynomial of degree ≤ n. P_Φ is a polynomial of degree ≤ n.
- Over an infinite field, Strassen's division elimination gives a division-free circuit of size poly(n, \|D\|).
- Over F_q: by Schwartz–Zippel, an extension F_{q^k} with q^k > (size)·n contains a point where all divisors are nonzero. Simulate F_{q^k} arithmetic over F_q, at cost O(k²) per gate, and read off the F_q-component.
- So the family is in VP over every field. ∎

**Remarks.**
- Block structure, representatives and c* are combinatorial data of Φ. That is fine for nonuniform VP.
- The data is also poly-time computable: T_i membership is CSP extension, and CB implies a Mal'cev polymorphism, so Bulatov–Dalmau applies.
- The proof uses only instance-level balance in one variable order, which gives V2.1′.
- The circuit is essentially a product of ratios along one solution: P = x^t · Π_i M_{β_i}/μ_{β_i}(t_i).

**C++ check** (v2_balance.cpp, exact arithmetic mod 2⁶¹−1, random points, n ≤ 7, \|D\| = 4, rectangular block-bijection constraints plus random lists):
- On every balanced instance, the recursion that uses only monomials and ratios reproduces the brute-force P: 267/267 and 266/266.
- Unbalanced instances are detected (1 and 28) and skipped.

## 3. Proposition V2.2 (proved from citations): CB ⇒ conservative Mal'cev and conservative majority

- **Mal'cev.** Balanced implies strongly rectangular (Dyer–Richerby), which implies a Mal'cev polymorphism (Bulatov–Dalmau). It is a polymorphism of Γ ∪ U_D, so it preserves every subset and is therefore conservative.
- **Majority.** CB = weakly log-modular, which implies weakly log-supermodular (Definition 4 of CDGJLMR is the one-sided version).
- CDGJLMR Lemma 33 runs Takhanov's Theorem 32. Each of its three non-majority alternatives yields a binary pps-function violating the inequality: N(a,b,a,b) directly; the XOR-like ternary {aaa, abb, bab, bba} with a unary weight; or an odd cycle of N's.
- The same three constructions in the (Σ,·) semiring violate weak log-modularity: a 2×2 with 3 nonzero entries, or 4 nonzero entries that are not rank 1. So Feas(Γ ∪ U_D) has a majority polymorphism, conservative for the same reason. ∎
- Self-audit: Lemma 33 is stated for valued languages (min, +). Its counting translation is mechanical, since each gadget is a pps-formula with large unary weights, but I did not rewrite it line by line. Confidence 85%.

**Boolean (V2.3).**
- With all unary weights, Dyer–Goldberg–Jerrum's weighted Boolean #CSP dichotomy leaves only product type in FP. Pure affine dies under a non-constant unary.
- Cai–Chen–Lu gives FP ⟺ balanced.
- Product type with 0/1 relations means conjunctions of =, ≠ and constants, which is exactly BK09 Remark 1. This matches BK09 Thm 2.
