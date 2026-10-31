# Independent AI-Worker Audit of the Code-Equivalence Wrapper

**Status:** AI-assisted informal proof; separate AI-worker review and exact finite checks where supplied. No Lean certificate; independent human review and publication-priority assessment remain pending.

31 October 2026. Complete informal proof; no Lean verification.

RESULT
The parent's four-reference construction is correct for arbitrary full-row-rank input generator matrices, including zero columns and repeated projective classes. It gives a deterministic same-field many-one reduction from decision LCE to decision GCE, with length 5n+10 and dimension k+2. Every semilinear witness for the wrapped instance has trivial field automorphism and restricts to a linear monomial witness for the original instance. Consequently search LCE reduces directly to search GCE and, using the known search-to-decision theorem for LCE, also reduces in polynomial time to decision GCE.
This addresses the reverse-reduction gap explicitly left in Section VI of Mazumder, arXiv:2608.10967v1. Our bounded current-literature audit found no prior reverse construction. Priority is NOT fully established, and the conclusion must be distinguished from the already-solved July survey search-to-decision question.

## Exact Target And Source Scope
The relevant target is the reduction from search LCE to GCE, or search GCE, mentioned in the conclusion of the August 2026 paper. That paper already proves search LCE to decision LCE and search GCE to decision GCE. Its field-automorphism enumeration goes in the opposite direction, reducing GCE to LCE; it does not settle the reverse reduction addressed here.
Primary source:
https://arxiv.org/html/2608.10967v1
Section VI, Conclusion and Future Work, immediately after Algorithm 5 and its complexity analysis.

MODEL
The finite field F_q is supplied in the usual polynomial representation
    F_q = F_p[T]/(h(T)),
where h is an irreducible polynomial of degree s and q=p^s. Field elements and the common field presentation are input data, so field arithmetic takes polynomial time in log q. No field representation is constructed from q alone. In particular this theorem does not assume an algorithm for constructing an irreducible h from only its degree.
When s=1, LCE and GCE coincide, so use the identity reduction. Assume henceforth s>1 and put alpha = T modulo h. Its degree over F_p is exactly s. Therefore alpha is neither 0 nor 1, and the only Frobenius automorphism fixing alpha is the identity. Alpha need not generate the multiplicative group and no primitive-element or discrete-logarithm computation is used.
LCE on k by n full-row-rank matrices G,H means existence of A in GL(k,F_q) and an n by n monomial M with A G M=H. GCE additionally permits a common field automorphism, so its matrix equation is S sigma(G) M=H.

## Construction
Work in F_q^(k+2) = U direct-sum W, with U the first k coordinates and W the last two. Pad each data column g_i to (g_i,0,0). In W define four distinct projective lines represented by
    r_1=(1,0), r_2=(0,1), r_3=(1,1), r_4=(1,alpha).
Adjoin n+1 copies of r_1, n+2 copies of r_2, n+3 copies of r_3, and n+4 copies of r_4, with zeros in their first k coordinates. Denote the resulting matrix by E(G), and use exactly the same reference columns for E(H).
The total length is
    n+(n+1)+(n+2)+(n+3)+(n+4) = 5n+10.
The rank is k+2, since the original data span U and the first two references span W. The construction takes polynomial bit time and uses only the original field.

## Forward Direction
If A G M=H, then diag(A,I_2), the original monomial map on the data coordinates, and the identity on all reference coordinates witness linear equivalence of E(G),E(H). In particular the wrapped matrices are GCE-equivalent with trivial field automorphism. Within repeated reference groups any permutation may be used; the identity suffices.

## Reverse Direction And Witness Extraction
Suppose
    S sigma(E(G)) M' = E(H),
where S is invertible, M' is monomial, and sigma(x)=x^(p^j), 0<=j<s.
An invertible semilinear map preserves proportionality of nonzero columns in both directions, and therefore gives a bijection on distinct projective classes, preserving each class's number of columns. Every nonzero data class has multiplicity at most n. Every reference class has one of the four pairwise distinct multiplicities n+1,...,n+4. No reference line is a data line, because U and W intersect only in 0.
It follows that each reference projective line must be mapped to ITSELF, and that all nonzero data classes are mapped to data classes. Zero columns map to zero columns and cannot interact with any projective class.
Since sigma fixes the coordinate subspaces U,W setwise, the facts that the data span U and the references span W imply S(U)=U and S(W)=W. Thus S=diag(A,B), with A and B invertible.
Now sigma fixes r_1,r_2,r_3, since their entries lie in the prime field. Fixing the first two reference lines forces B to be diagonal, say diag(b_1,b_2). Fixing the third line forces b_1=b_2, so B=b I_2 for a nonzero scalar b. The fourth fixed reference line now says
    [1 : alpha^(p^j)] = [1 : alpha].
The first coordinate is 1 on both sides, so this projective equality forces alpha^(p^j)=alpha. Since alpha has full degree s, j=0. Thus sigma is the identity on the whole field.
Consequently the data-coordinate restriction of the wrapped monomial map, together with A, witnesses the original LCE. The wrapped permutation necessarily sends the data coordinate set to the data coordinate set: nonzero data lines are disjoint from reference lines, and zero columns also occur only among the data coordinates. Read the corresponding n by n monomial submatrix from M' and the k by k upper-left block from S. These satisfy the original literal matrix equation, with the same permutation convention as the input witness.
This proves equivalence of the decision instances and proves that EVERY wrapped semilinear witness is valid for extraction. There is no promise that an oracle chooses a special witness.

## Composition With Search-To-Decision
The preceding construction directly gives a many-one search reduction from search LCE to search GCE: one wrapped instance and deterministic extraction suffice. For a decision GCE oracle, apply an existing polynomial-time LCE search-to-decision algorithm, wrapping each of its decision LCE queries. Every resulting GCE query has length linear in the corresponding LCE query length, dimension increased by 2, and the same field. The total number of queries and all non-oracle work stay polynomial in n,k,log q. This uses an established complete algorithm as a theorem, rather than assuming an unknown recovery gadget.
The reduction works on inequivalent inputs as well: the decision wrapper preserves NO exactly, and a decision self-reduction can return NO. If a search oracle's contract is only on promised YES instances, state the resulting promise-search reduction accordingly; do not claim that such an oracle detects NO by itself.

## Independent Exact Controls
verify_reference_stabilizers.py exhaustively enumerates PGL(2,q) times the Frobenius group for q=4,8,9,16,25,27,32, using explicit irreducible polynomial representations. The projective canonical matrices are all matrices with first nonzero entry 1 and nonzero determinant. For every field the pointwise stabilizer of the four labeled reference lines is exactly projective identity with Frobenius exponent 0.
The total is 273,240 semilinear projective maps. Exact finite-field arithmetic is used; there is no floating-point tolerance. Output: REFERENCE-CHECKS.json, pass=true. These finite checks corroborate the independent universal proof above; they do not replace it or certify novelty.

## Adversarial Audit
## 1. Repeated or proportional data columns: their class multiplicities remain <=n, so none can imitate a reference label.
## 2. Zero columns: these are invariant under all invertible semilinear maps, occur only among data columns, and are safely retained.
## 3. Nonconcise/row-redundant input: reduce to a basis of each row space first; if ranks differ, reject. The frozen theorem is stated for full-row-rank generators, as in the source.
## 4. Mixing data and reference subspaces: forbidden by class labels, then excluded as a linear-algebraic consequence of their spanning the two coordinate summands. No unproved indecomposability condition is assumed.
## 5. Reference-line permutations: forbidden by four distinct multiplicities. Without labels, anharmonic permutations of four points could invalidate the field-rigidity conclusion.
## 6. Prime fields: handled by the identity reduction; no four-reference gadget is needed when there is no nontrivial field automorphism.
## 7. Proper-subfield alpha: inadequate, since a nontrivial Frobenius may fix it. The polynomial-presentation generator has full extension degree and eliminates this defect.
## 8. Scalar B: its value need not be recovered or fixed to 1. A nonzero scalar acts trivially on projective lines and does not obstruct data witness extraction.
## 9. Rank increase and length growth: exactly +2 and 5n+10, respectively; original full rank ensures the wrapped generator has the claimed rank.
## 10. No whole-field search: all construction constants are 0,1,alpha and use the supplied field presentation.

## Priority Check And Older Ambiguous Wording
A bounded literature search located Sendrier and Simos, How easy is code equivalence over F_q?, hal-00790861v2, whose Section 7 loosely describes polynomial reductions "between" linear and semilinear equivalence. Inspection of its actual Section 4.1 resolves the ambiguity: it enumerates the s field automorphisms and calls a LINEAR equivalence algorithm s times to solve SEMILINEAR equivalence. This is GCE to LCE, the easy direction already discussed in the August 2026 source. It does not present the reverse field-rigidity wrapper here.
Original author-hosted extended abstract:
https://publications.sba-research.org/publications/codeq3_wccfin.pdf
Long-version record and searchable author-paper mirror:
https://inria.hal.science/hal-00790861v2
https://www.researchgate.net/publication/281186344_How_easy_is_code_equivalence_over_Fq
The HAL document fetch was blocked by its access gate. The indexed long-version Section 4.1 text was inspected through the mirror. This limitation is recorded instead of silently treating the extended abstract as the long version.
Searches for search LCE/GCE reverse reductions, cross-ratio code-equivalence gadgets, and semilinear-to-linear rigidity found no prior matching construction. This is a bounded audit, not a proof of absolute priority. The correct present claim is a complete informal positive resolution of the explicitly stated Section VI gap, with novelty still requiring wider review.
