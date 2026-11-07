# Computational supplement: connected J-equivalence with unequal Loewy lengths

This strengthens the one-way counterexample in LOEWY.md. It uses a deterministic exact finite computation, not Lean verification, to identify one explicit central idempotent. The public counterexample does not depend on this supplement.

Work first over F2. Put R=F2[SL2(F4)], and let P={[[1,t],[0,1]]:t∈F4}. The group is isomorphic to A5, and P is its Klein-four Sylow 2-subgroup. Let

e = Σ_{g of odd order} g.

Under the A5 identification this is 1 plus the sum of all 3-cycles and all 5-cycles. The exact companion checker establishes:

- e²=e and e is central;
- dim(eR)=44 and dim((1−e)R)=16;
- the Jacobson radical I of R has dimension 35 and eI=I;
- the center of eR has dimension 4, and its image in R/I has dimension 1.

For completeness, the last image equals F2·e because it contains e and is one-dimensional. Its kernel lies in the nilpotent ideal I. Hence the center of eR is local with residue field F2. Therefore eR is connected. This remains true after extension to any characteristic-2 field: its center is obtained by scalar extension, its nilpotent ideal extends, and the residue field becomes that field. The augmentation of e is 1, so the connected block eR contains the trivial module and is the principal block.

Let π:R→B=F2[P] be coefficient projection: discard every group-basis coefficient outside P. This is a B-bimodule map, since for p,q∈P and g∈G one has pgq∈P if and only if g∈P. No averaging or division is involved. Since every nonidentity element of P has order 2, the displayed odd-order sum has only its identity term inside P. Thus

π(e)=1_B.

The map i:B→eR, i(b)=eb, is a B-bimodule map because e is central. For b∈B,

π(i(b))=π(eb)=π(e)b=b.

Consequently B is a direct summand of eR as B-bimodules. Write A=eR, M={}_B A_A and N={}_A A_B, where the B-actions come from b↦eb. Multiplication gives M⊗_A N≅{}_B A_B. The preceding split inclusion proves B≥_J A. The explicit coset-separability splitting in the main note proves A≥_J B, so A~_J B.

All maps and equalities extend to any characteristic-2 field. Over an algebraically closed such field the algebras meet Jonsson's connectedness convention and have Loewy lengths 5 and 3. The discrepancy therefore occurs within a single J-equivalence class, not only between comparable classes.

## Exact certificate scope

The checker verifies the entire multiplication table of the 60 group elements and all 3,600 products of their images in F2⊕Mat_2(F4)⊕Mat_4(F2). The image has dimension 25. The kernel I is nilpotent with successive dimensions 35,27,17,9,0, so it is the Jacobson radical. It verifies e²=e, every commutator [e,g], all products e·v for a radical basis, and the center kernel/image dimensions by exact binary Gaussian elimination. It also directly checks π(e)=1, independently of the odd-order argument.

These finite checks are reproducible with the Python standard library. They constitute an exact computational verification and supporting certificate, not a proof checked by the Lean kernel. The mathematical identification of the constructed group with A5 and the routine finite-dimensional algebra implications are informal arguments. The main one-way counterexample already follows from its explicit splitting and the published Loewy-length value without these computations.
