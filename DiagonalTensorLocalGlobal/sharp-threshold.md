# Side four is sharp for the special-linear local–global principle

**Theorem.** Over every number field \(F\), geometrically diagonal tensors of side at most three that are special-linearly equivalent over every completion are special-linearly equivalent over \(F\). Side four admits a counterexample over every \(F\), even within a single ordinary orbit and with trivial norm coordinates.

More precisely, a degree-four étale algebra has a nontrivial parity factor in formula (1) of the [determinant calculation](determinants.md) exactly in the following cases.

- It is a biquadratic field with cyclic decomposition subgroups everywhere.
- It is a quartic field with dihedral normal closure, and no decomposition subgroup contains the regular Klein four group in the four-point action.

**Proof through side three.** Local ordinary isomorphisms give global ordinary isomorphism by rigidity in degree at most five. Then the determinant coordinates apply to their global transporter. [Degree-six diagonal classification](https://github.com/Dugongue/MathProofs/blob/main/DickeAndIsomorphismMethods/GEOMETRY.md).

An algebra with a scalar factor has a surjective norm. Quadratic and cyclic cubic fields satisfy Hasse's cyclic norm theorem. If \(E/F\) is a non-Galois cubic, let \(\Omega/F\) be its normal closure and \(K/F\) its quadratic resolvent. Then \(\Omega=EK\) and \(\Omega/K\) is cyclic. An element \(a\in F^\times\) that is everywhere locally a norm from \(E\) is everywhere locally a norm after base change to \(K\). By the cyclic norm theorem, \(a=N_{\Omega/K}z\) for some \(z\). Thus \(a^2=N_{\Omega/F}z\) is a norm from \(E/F\). Also \(a^3=N_{E/F}a\), so \(a\) itself is a norm.

For the sign factor, a cubic field has an unramified place whose Frobenius is a three-cycle by Chebotarev. The centralizer of that three-cycle consists of even permutations. Therefore the intersection of the local sign groups is trivial. A quadratic field has a global odd conjugation. A split algebra with at least two scalar factors has a global odd swap. The remaining mixed algebra is a scalar factor times a quadratic field, where conjugation on that quadratic factor is globally odd. In degree one the only possible sign is \(+1\). This exhausts the cases and makes both factors of the local obstruction trivial.

**The quartic classification.** Let \(G\le S_4\) act faithfully on the embeddings. The global automorphisms of the algebra are the permutations in the centralizer of \(G\). The local automorphisms are the centralizers of its decomposition subgroups. If \(G\) contains a three-cycle, Chebotarev supplies a place where its centralizer is the local automorphism group, and on four points that centralizer is all even.

We may therefore assume that \(G\) is a 2-group. If the action is intransitive, an independent flip of a two-point orbit or a swap of singleton orbits gives an odd global automorphism. The transitive possibilities are \(C_4,V_4,D_8\), where \(D_8\) has order eight. In the regular cyclic case the four-cycle is an odd global automorphism. In the regular Klein four case its centralizer is itself, all even, while every proper subgroup has an odd centralizing permutation. This gives the first quartic case.

For \(D_8=\langle r,s\rangle\) acting on square vertices, take \(r\) to be a four-cycle and \(s\) a reflection fixing two vertices. The full group's centralizer is \(\langle r^2\rangle\), all even. Its two proper noncyclic subgroups are \(\langle r^2,s\rangle\) and \(\langle r^2,rs\rangle\). The first centralizes \(s\), a transposition. The second is the regular Klein four group and has an all-even centralizer. Every cyclic subgroup has an odd centralizing permutation, as the centralizer of any permutation on four points of 2-power order contains an odd permutation. This proves the second case. The \(D_8\) closure of \(\mathbb Q(\sqrt[4]{17})\) from the side-six theorem is an explicit example. Both quartic cases occur over every number field by the locally cyclic realization theorem. [Frei–Loughran–Newton, Proposition 5.5](https://arxiv.org/pdf/1508.02518).

For an explicit tensor construction from either case, apply a basis transformation of determinant \(-1\) in each of the three slots. The normalized determinant coordinates are \((-1,1,1)\). Each local stabilizer can remove the sign, while the global stabilizer has sign \(+1\). This constructs the sharp obstruction with both norm coordinates equal to one.



**Complete quartic count.** The signed local genus has the following size for any choice of representative. There is only one ordinary orbit in the local genus by degree-four ordinary rigidity.

| Quartic algebra | Condition | Signed classes |
|---|---|---:|
| Biquadratic field | Every decomposition subgroup is cyclic | 8 |
| \(A_4\)-quartic field | No decomposition subgroup contains \(V_4\) | 4 |
| \(D_8\)-quartic field | No decomposition subgroup contains the regular \(V_4\) in the vertex action | 2 |
| Every other case | | 1 |

Kunyavskiĭ's quartic norm theorem gives a norm quotient of order two exactly in the two indicated \(V_4\) and \(A_4\) field cases, and order one in all other quartic field cases. For quartic product algebras either a scalar factor gives surjectivity or the algebra is a product of two quadratic fields, where the [two-field norm theorem](side-six-genera.md#two-field-calculation-for-the-dihedral-pair) applies. Combining with the sign calculation proves the table. The split algebra gives size one, and all the larger sizes occur over each number field by locally cyclic realizations of the three solvable groups. [Kunyavskiĭ's quartic norm theorem](https://www.mathnet.ru/php/archive.phtml?jrnid=znsl&option_lang=eng&paperid=1756&wshow=paper), [Oki, Theorem 1.2](https://arxiv.org/pdf/2508.10706), [Frei–Loughran–Newton, Proposition 5.5](https://arxiv.org/pdf/1508.02518).
