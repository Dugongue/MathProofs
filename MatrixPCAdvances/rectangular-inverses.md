# Exact degree of two-sided rectangular inverses

Let \(a>b\ge1\), let \(K\) have characteristic \(p>0\), and put \(q=p^{v_p(a-b)}\). The least ordinary Polynomial Calculus (PC) degree of \(UV=I_a,\ VU=I_b\), for independent variables \(U_{ij},V_{ji}\), is
\[
D_p(a,b)=\min(2q,b+2).
\]
The same equality holds over a finite field \(K=\mathbb F_Q\) of size \(Q>2\) after adjoining all equations \(x^Q-x=0\). Degree is the largest actual total degree of any proof line.

## Matching designs at the boundary

A degree-\(\ell\) matching design on a board assigns values to edge sets of at most \(\ell\) edges, vanishes on collisions, and satisfies both marginal identities
\[
\sum_{e\ \mathrm{in\ a\ specified\ row\ or\ column}}\psi(P\cup\{e\})=\psi(P)
\quad\text{for }|P|<\ell .
\]
Let the board have smaller side \(r\) and larger side \(m\), where \(q\mid m-r\). For \(2\ell\le r+1\) and \(\ell<q\), there is a normalized design, and every degree-\((\ell-1)\) design extends to degree \(\ell\) when \(\ell>0\).

Here is the boundary adjustment to Riis's construction. Orient the board as \([r]\times[m]\) and append \(m-r\) rows. In §§14.3–14.4, the sole use of \(2\ell\le r\) is the bound on a failed row prefix of a matching with at most \(\ell\) edges. If the prefix is indexed by \(t\), the defining failure gives \(t<h(P_{\le t})+|\operatorname{rows}(P_{\le t})|\le2\ell\). Thus \(t\le2\ell-1\le r\) still holds at the new boundary. The failed prefix, including a prefix ending at \(r\), lies entirely among old rows. All row rewrites therefore keep every surviving appended-row token in its old row, and column rewrites preserve the row of a surviving token. Strictly increasing renaming of appended rows continues to preserve failed prefixes, selected chains and all retained branches. It also preserves terminality. The signed marked path sum with appended-row history size \(k\) still carries the factor \(\binom{m-r}{k}\), for \(1\le k\le\ell<q\), and each factor vanishes in \(K\). The square designs restricted to the old rectangle therefore give the same terminal-coordinate basis and the same extension operation in §14.4. Degree zero requires only the value on the empty set, including when \(r=0\). [Riis, §§14.2–14.4](https://arxiv.org/html/2611.07280v1#S14.SS3)

## Lower bound through degree falls

Fix a cap \(d\le\min(2q-1,b+1)\). For \(d<2\), no nonzero axiom is usable. Otherwise grade by row in \(\mathbb Z^a\), with \(U_{ij}\) of weight \(+e_i\) and \(V_{ji}\) of weight \(-e_i\). For the finite-field statement use \((\mathbb Z/(Q-1))^a\) instead, where both \(+1\) and \(-1\) are nonzero. Every inverse equation is homogeneous for this grading. Field equations are homogeneous in the modular grading.

Fix a weight \(w\) having \(s\) nonzero rows. Pin these rows to distinct columns by any injection \(A\). In evaluating each monomial, record a cell as an edge if either variable for that cell occurs. Assign value zero to a colliding support or one conflicting with \(A\). On all other supports, delete the edges of \(A\) and apply any design \(\psi\) of degree \(L_s=\lfloor(d-s)/2\rfloor\) on the remaining board. Each mandatory row occurs in the monomial, and every other occupied row uses at least two variables counted with multiplicity, since a single exponent contribution has nonzero weight. Thus the residual support has at most \(L_s\) edges. Only weights with \(s\le d\) can occur. If \(s>b\), all supports collide, so take the tests to vanish identically. The residual board has smaller side \(b-s\), and \(2L_s\le b-s+1\), \(L_s<q\).

Test every weight component of every line against all these choices. Off-diagonal inverse axioms have colliding supports. Diagonal axioms have zero weight and give the corresponding matching marginal. The two terms of a finite-field equation have the same edge support. Hence every usable axiom vanishes under the tests, and linear combinations preserve the assertion.

For a multiplication by the variable for \(e=(i,j)\), take any test for the output component. The earlier component has degree at most \(d-1\), since nonzero multiplication by a variable raises actual degree by one. Write \(s\) for the earlier number of mandatory rows and \(B=\lfloor(d-1-s)/2\rfloor\). If \(s>d-1\), that earlier component is zero. The following pullbacks of tests suffice on supports of at most \(B\) residual edges.

- If row \(i\) stays mandatory, keep the pins and multiply by the constant 0 or 1 determined by the pin at \(i\). If the current design has surplus degree, restrict it to \(B\).
- If row \(i\) becomes mandatory, the output pin fixes its column. The pullback is zero unless it fixes \(j\). When it fixes \(j\), regard the output design as a design on the earlier board by setting \(e\) to 1 and all other edges meeting its endpoints to 0. This preserves all matching marginals. The current design has degree \(\lfloor(d-s-1)/2\rfloor=B\).
- If row \(i\) ceases to be mandatory, adjoin \(e\) to the earlier pins. If the output pins already use column \(j\), the pullback is zero. Otherwise condition the output design on \(e\) by \(\psi'(P)=\psi(P\cup\{e\})\) for residual supports on the smaller board. The marginal identities apply after insertion, so the conditioning loses one degree. The resulting degree is \(\lfloor(d-s+1)/2\rfloor-1=B\).

If the earlier mandatory set is too large to pin, every earlier support collides and multiplying by a variable preserves the collision. If the output set is too large, its test vanishes by definition. The case where row \(i\) stays nonmandatory is excluded by the nonzero weight of the multiplier in row \(i\). In each remaining case the boundary extension property extends the test from \(B\) to \(L_s\), so the earlier component annihilates the pullback. This proves the invariant through all PC steps. At weight zero a normalized design evaluates \(1\) to \(1\), ruling out a refutation in degree \(d\).

## Upper bounds

If \(2q\le b+2\), compare the sums of principal \(q\)-minors of \(UV\) and \(VU\), which agree by Cauchy–Binet. Replacing product entries by their identity values gives the constants \(\binom a q,\binom b q\) in degree \(2q\). Their difference is nonzero by the base-\(p\) digit at \(q\). This includes \(b=1,q=1\); when \(b\ge2\), \(2q\le b+2\) implies \(q\le b\). The descending-minor proof uses only \(UV=I_a\) and has degree \(b+2\). Both derivations also work when field axioms are present. [Earlier compound and descending-minor derivations](https://github.com/Dugongue/MathProofs/blob/main/GrochowEightFollowup/complexity.md)
