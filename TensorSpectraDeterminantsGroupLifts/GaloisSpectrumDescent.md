# Galois descent for the full tensor asymptotic spectrum

Fix an order \(d\ge 2\). Write \(\Delta_d(F)\) for the space of all normalized, additive and multiplicative real-valued spectral points on \(d\)-tensors over \(F\), monotone under ordinary local linear restriction. This uses the tensor direct sum and the modewise Kronecker product. Equip the spectrum with the topology of pointwise convergence. A field extension \(E/F\) induces a map \(\rho_{E/F}:\Delta_d(E)\to\Delta_d(F)\) by evaluating a point on scalar-extended tensors. For Galois \(E/F\), let \(\operatorname{Gal}(E/F)\) act by coefficient twists, with the inverse on twists if using a left action on spectral points.

**Theorem.** If \(E/F\) is normal algebraic, the restriction map induces a homeomorphism

\[
\Delta_d(E)/\operatorname{Aut}_F(E)\ \cong\ \Delta_d(F).
\]

For a finite Galois extension, two distinct orbits are distinguished downstairs by the transfer of at most \([E:F]\) powers of one tensor upstairs. For example, a real tensor spectral point extends to a complex point, and all its complex extensions form one orbit under complex conjugation. The theorem allows a one-point orbit. Purely inseparable extensions give one-point fibers, even if the field extension is infinite.

The question of maps between asymptotic spectra occurs in [Grochow–Qiao, Open Question 7.5](https://epubs.siam.org/eprint/VA7M2DT6DFQMVDVWIBBN/full), alongside their field-change Question 7.6. The argument combines the scalar-extension and Galois-orbit viewpoint in the MathProofs field-descent work, the restriction-semiring viewpoint in [Functorial tensor reductions](https://github.com/Dugongue/MathProofs/blob/main/FunctorialTensorReductions/PROOF.md), and the field-multiplication tensor used by [Chen–Ye](https://arxiv.org/abs/2409.04034). The extension of spectral points on a scalar-extended tensor family already follows from [Strassen, Theorem 3.10](https://eudml.org/doc/153001), as stated in [Christandl–Vrana–Zuiddam, Remark 1.3](https://arxiv.org/abs/1709.07851). We include the surjectivity argument to identify exactly the map whose fibers are computed. The orbit description and finite separation bound are the additions here. Their publication priority remains unverified.

## 1. Surjectivity and the constant-cost field simulation

Write \(S\le T\) when \(S\) is a restriction of \(T\) and write \(\langle c\rangle\) for the diagonal tensor of size \(c\). View tensors as multilinear forms on the duals of their coefficient spaces. If \(L/F\) is finite, take any \(F\)-linear functional \(\lambda:L\to F\) with \(\lambda(1)=1\) and let \(M\) be the tensor of \((x_1,\ldots,x_d)\mapsto\lambda(x_1\cdots x_d)\) on \(L^d\). In an \(F\)-basis of \(L\), expanding all but one mode shows that \(M\le\langle [L:F]^{d-1}\rangle\).

Suppose \(S_L\le T_L\), witnessed by \(L\)-linear maps on the respective input spaces of the forms. Restrict those maps to the input spaces over \(F\), and regard their outputs as vectors over \(F\) with an extra factor \(L\) in each mode. On those outputs, \(T\otimes M\) evaluates to \(\lambda\) of the value of \(T_L\). That value is \(S\) on the restricted inputs, so applying \(\lambda\) gives \(S\). Thus \(S\le T\otimes M\). The same single \(M\) suffices to simulate the tensor product of any number of copies of the \(L\)-linear witness. The new coefficient products are still evaluated by the same \(\lambda\) on \(L\).

For completeness, if \(S_E^{\otimes n}\le \langle c_n\rangle\otimes T_E^{\otimes n}\) with \(c_n^{1/n}\to1\), each individual witness is a finite system of polynomial equations with coefficients over \(F\). Whenever it is solvable over \(E\), the defining ideal is proper and it is also solvable over some finite algebraic extension \(L_n/F\), by the weak Nullstellensatz. Use the same \(L_n\)-witness \(k\) times before simulating it downstairs. For every \(\phi\in\Delta_d(F)\) this gives

\[
\phi(S)^{nk}\le [L_n:F]^{d-1} c_n^k\phi(T)^{nk}.
\]

Taking \(k\)-th roots and letting \(k\to\infty\) first yields \(\phi(S)^n\le c_n\phi(T)^n\). Then \(n\)-th roots give \(\phi(S)\le\phi(T)\). A zero tensor causes no exception, since \(\phi\) vanishes there and every nonzero tensor restricts to the unit. By Strassen duality, asymptotic restrictions between scalar-extended tensors therefore hold already over the base field. This argument works for arbitrary extensions.

Each spectral space is compact Hausdorff. It is a closed subset of a product of intervals, using \(0\le\phi(T)\le\operatorname{rank}(T)\) for each coordinate. Suppose \(\phi\in\Delta_d(F)\) is absent from the compact image of restriction. Finitely many evaluations give a vector \(v\) for \(\phi\) separated by positive Euclidean distance from the image in those coordinates. A real polynomial of the form \(r-\sum_i(x_i-v_i)^2\) for a sufficiently small \(r>0\) is positive at \(v\) and negative on the compact projected image. Approximate its coefficients by rationals while preserving the signs, clear denominators, and separate positive and negative monomials. The resulting polynomial is the difference of the evaluation functions of two actual tensors \(S,T\) formed from these finitely many coordinate tensors, diagonal tensors, direct sums and products. Then \(\phi(S)>\phi(T)\) and every spectral point over \(E\) puts \(S_E\) below \(T_E\). Duality over \(E\) and the simulation just proved contradict \(\phi(S)>\phi(T)\). Thus restriction is surjective.

## 2. Trace transfer recovers the finite Galois orbit

Now take finite Galois \(E/F\) with group \(G\), and a tensor \(X\) over \(E\) viewed as a multilinear form. Let \(\operatorname{tr}_{E/F}(X)\) be the \(F\)-tensor on the same input spaces regarded over \(F\), obtained by composing the form with the field trace. There is a tensor isomorphism over \(E\)

\[
\big(\operatorname{tr}_{E/F}(X)\big)_E\cong\bigoplus_{g\in G} gX.
\]

Indeed, \(E\otimes_F E\cong\prod_{g\in G}E\), where the second factor acts on each copy through its corresponding embedding. Extend each input space using this decomposition. The extended multilinear form vanishes on mixed blocks, because it is multilinear for the product algebra before applying trace and the distinct factor idempotents multiply to zero. On the \(g\)-block its coefficients are twisted by \(g\). The base-changed field trace adds the coordinates of the product algebra, including when the characteristic divides \(|G|\). This proves the displayed isomorphism.

If \(\psi,\eta\) have the same restriction to \(F\), apply the trace identity to each \(X^{\otimes j}\) with \(1\le j\le |G|\). For each \(X\) this gives

\[
\sum_{g\in G}\psi(gX)^j=\sum_{g\in G}\eta(gX)^j.
\]

Newton's identities for real numbers recover the multiset of \(|G|\) values from these power sums. In particular \(\eta(X)\) belongs to \(\{\psi(gX):g\in G\}\).

Suppose no single \(g\) gives \(\eta=\psi\circ g\). For each \(g\) choose a tensor distinguishing the two points there, giving a finite list \(X_i\). The vector of \(\eta\)-values on this list differs from the vector of \(\psi\circ g\)-values for every \(g\). Choose positive integers \(w_i\) with unequal dot products for all these pairs. For example, take \(w_i=N^{i-1}\) and avoid the finitely many roots of the resulting nonzero difference polynomials. Form the single tensor \(X=\bigoplus_i\langle w_i\rangle\otimes X_i\). Then \(\eta(X)\ne\psi(gX)\) for every \(g\), contradicting the multiset statement. This proves the orbit description and gives the finite separation bound. The opposite implication holds since twisting fixes tensors defined over \(F\).

## 3. Arbitrary algebraic Galois extensions

For algebraic Galois \(E/F\), restrict two points with equal base restrictions to every finite Galois intermediate field \(L\). At that level the finite theorem gives at least one twist matching the restrictions. Every such twist extends to \(E\), and the subset of \(\operatorname{Gal}(E/F)\) giving a match on \(L\) is a nonempty closed subset of the profinite group. Finitely many such conditions hold simultaneously by applying the finite theorem to the compositum. Compactness gives one group element matching on every finite Galois intermediate field. Every coefficient tuple is contained in one of those fields, so this group element matches the full points. Finally the continuous restriction map from the compact quotient to the Hausdorff base spectrum is a bijection, hence a homeomorphism.

## 4. Purely inseparable descent by charging only finitely many nilpotent factors

Suppose \(E/F\) is finite and purely inseparable, and take a nonzero \(F\)-linear functional \(\lambda:E\to F\). Define \(T_n\) over \(F\) by applying \(\lambda\) to the multilinear form \(X^{\otimes_E n}\), viewing its input spaces over \(F\). We show that for every \(\psi\in\Delta_d(E)\),

\[
\psi(X)=\lim_{n\to\infty}\psi((T_n)_E)^{1/n}.
\]

Put \(B=E\otimes_F E\), regarded as an algebra via the first coefficient field, and let \(J\) be the kernel of the multiplication map \(B\to E\). If \(p^a\) is an inseparability exponent, the generators \(1\otimes x-x\otimes1\) of \(J\) have \(p^a\)-th power zero. Finitely many generators suffice, so \(J^r=0\) for some fixed \(r\) and \(B/J=E\). The scalar extension \(\lambda_E:B\to E\) gives a nondegenerate product pairing because the pairing \(\lambda(xy)\) on the field \(E\) over \(F\) is nondegenerate. Choose nonzero \(s\in\operatorname{Ann}(J)\). Since \(as=\bar a s\) for any \(a\in B\) with residue \(\bar a\in E\), nondegeneracy gives \(\lambda_E(s)\ne0\). Rescale \(s\) to make that value one.

In the base change of the form defining \(T_n\), the input spaces have coefficients in \(B\). Before applying \(\lambda_E\), the coefficient array for a single \(X\) is \(X+\delta\), where we view the entries of \(X\) through the first coefficient embedding and \(\delta\) takes values in \(J\). For the lower bound, restrict the \(d\) inputs to their copies over \(E\), multiplying the entire first input by \(s\). Then every nilpotent coefficient term vanishes, and \(\lambda_E(s)=1\) gives the restriction \(X^{\otimes n}\le (T_n)_E\).

For the upper bound, expand the \(n\) products of coefficient arrays and use \(J^r=0\). At most \(r-1\) of the \(n\) positions may contribute a \(\delta\). Expand \(\delta=\sum_j D_j b_j\) in a fixed \(E\)-basis \((b_j)\) of \(J\). Each resulting term with \(h<r\) such positions, after local reordering, is \(X^{\otimes(n-h)}\) times \(h\) members of the fixed tensor list \((D_j)\), times the tensor of the form \(\lambda_E(b,a_1\cdots a_d)\) on \(B^d\), with \(b\) the selected product of basis elements of \(J\). The latter form has mode dimension \([E:F]\). There are polynomially many terms in \(n\), and every tensor factor outside \(X^{\otimes(n-h)}\) has bounded rank independent of \(n\). A sum in common mode spaces is a restriction of the direct sum, so additivity and monotonicity bound its spectral value by the sum of the values. For nonzero \(X\), use \(\psi(X)\ge1\) to conclude

\[
\psi(X)^n\le \psi((T_n)_E)\le O_{E,X,d}(n^{r-1})\psi(X)^n.
\]

The nth roots give the formula, with zero handled directly. The right side depends only on the restriction of \(\psi\) to \(F\). It follows that pure inseparability gives injectivity, which together with surjectivity and compactness gives a homeomorphism. An arbitrary algebraic purely inseparable extension follows by testing on the finite subextensions containing the coefficients of each tensor.

Finally, for normal algebraic \(E/F\), the subfield \(E_s\) of elements separable over \(F\) is Galois over \(F\), and \(E/E_s\) is purely inseparable. The automorphisms of \(E_s/F\) extend uniquely to \(E/F\) and their action commutes with spectral restriction. Combining the pure-inseparability step and the Galois step proves the theorem for normal algebraic extensions.

For any algebraic \(E/F\), choose a common algebraic closure \(\Omega\). Then \(\Delta_d(E)\to\Delta_d(F)\) identifies with the map from \(\Delta_d(\Omega)/\operatorname{Aut}_E(\Omega)\) to \(\Delta_d(\Omega)/\operatorname{Aut}_F(\Omega)\) induced by inclusion of the subgroups. This describes every algebraic-extension map in terms of one spectral space and its automorphism action. It leaves the size of a given orbit and the effects of the other reductions in Grochow–Qiao Question 7.5 as separate questions.
