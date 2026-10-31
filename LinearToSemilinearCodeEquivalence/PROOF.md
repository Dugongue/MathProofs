# A Linear-Size Frobenius-Rigidity Wrapper for Code Equivalence

**Status:** AI-assisted informal proof; separate AI-worker review and exact finite checks where supplied. No Lean certificate; independent human review and publication-priority assessment remain pending.

31 October 2026. Complete informal proof, two independent audits, no Lean claim.

Theorem. Given full-row-rank k by n code generators over a presented finite field F_q, ordinary linear monomial equivalence reduces in polynomial bit time to generalized (semilinear monomial) code equivalence over the SAME field. For a nonprime field the output length is 5n+10 and its dimension is k+2. Every semilinear transporter of the output has identity field automorphism and restricts to an original linear monomial transporter. Combining this decision reduction with the established LCE search-to-decision theorem yields search LCE <= decision GCE. One call also reduces promise-search LCE to promise-search GCE, with direct witness restriction.

Target and source. Section VI of Mazumder, Search-to-Decision Reductions for the Linear and General Code Equivalence Problems, arXiv:2608.10967v1 (11 August 2026), explicitly leaves the reverse reduction from search LCE to GCE or search GCE unproved. It already solves the separate search-to-decision question within each variant, and those earlier closures are not claimed here.
https://arxiv.org/html/2608.10967v1#S6

Field model. Write F_q=F_p[T]/(h), with h irreducible of degree s supplied as part of the common field representation. For s=1, the two equivalence notions coincide and the identity map suffices. For s>1 choose alpha=T modulo h. It has full extension degree, so only the identity Frobenius fixes it. It need not be a multiplicatively primitive element; no discrete logarithm, primitive-element search, field construction or factoring oracle is used.

Construction. In F_q^(k+2)=U direct-sum W pad each data column g_i to (g_i,0,0). In the independent two-dimensional space W append the four distinct projective representatives

    e_1, e_2, e_1+e_2, e_1+alpha e_2

with multiplicities n+1,n+2,n+3,n+4 respectively. Call the resulting generator E(G), and use the same constants for E(H). The length is exactly 5n+10 and the row rank is k+2.

Proof. Linear equivalence of G,H extends by the identity on W and the reference columns, proving the forward direction. Conversely suppose an invertible row map S, a common Frobenius sigma and a monomial column map take E(G) to E(H). Nonzero projective-class multiplicities are preserved under invertible semilinear maps. Every data class has multiplicity at most n; the four reference classes have pairwise distinct multiplicities above n. Each reference line is therefore fixed individually, and data classes map to data classes. Zero columns are fixed as zero and do not enter the class argument.

The data span U and the references span W, so S=diag(A,B). The first three reference lines have prime-field coordinates and are fixed by sigma. Fixing their labels forces B to be a scalar matrix: fixing the two axes makes it diagonal, and fixing their sum makes its diagonal entries equal. On the fourth reference line the condition now says alpha^sigma=alpha. Full extension degree implies sigma is identity. Restriction to U and the original column coordinates gives the desired ordinary linear monomial equivalence. This excludes all possible block-mixing and field-automorphism false positives, without a genericity or irreducibility promise on the input code.

Search consequences. A search GCE output on the wrapped pair has trivial field automorphism by the proof, and its monomial action maps data positions to data positions. Its restriction is a valid LCE witness. If the oracle supplies only a monomial map and a Frobenius exponent, an invertible row map is recovered by Gaussian elimination if needed. With a decision GCE oracle, wrap every query of the known deterministic polynomial LCE search-to-decision reduction; all queries and work remain polynomial in n,k,log q. Decision NO instances are preserved exactly. A promise-search oracle does not itself certify NO; that contract remains separate.

Input edge cases. Reduce redundant generators to full row rank and handle unequal ranks or lengths directly. Rank-zero inputs are identical zero codes when lengths match. Nonzero ranks may have arbitrary zero or parallel columns; the multiplicity argument already includes them. Prime fields require no wrapper.

Independent evidence. AUDIT.md audits the proof and exhaustively checks 273,240 projective semilinear maps over seven finite fields. verify_wrapper.py separately enumerates every GL_3(F_4) row map and both Frobenius exponents on a complete wrapped small code. It finds exactly nine linear row automorphisms and no nonidentity-Frobenius ones, checking the full ambient block action. It also verifies a control with generalized equivalence but no linear equivalence before wrapping.

Prior work and priority. Cross-ratio rigidity, projective classes and multiplicity tags are classical ingredients. Sendrier-Simos 2013's actual reduction enumerates field automorphisms and uses a LINEAR solver to decide SEMILINEAR equivalence; despite loose wording about reductions 'between' the variants, this goes in the opposite direction. Mazumder August 2026 and Biasse-Micheli-Prada-Waitkevich September 2026 already settle LCE search-to-decision, and are credited for the algorithm used in our composition. Bounded literature searches found no prior matching reverse-rigidity wrapper. Publication priority remains unverified.

Detailed independent proof and older-source caveats:
AUDIT.md
https://arxiv.org/html/2609.31517v1
https://publications.sba-research.org/publications/codeq3_wccfin.pdf
