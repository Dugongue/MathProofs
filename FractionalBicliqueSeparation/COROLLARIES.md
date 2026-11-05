# COMPLETE STRICT-GAP CLASSIFICATION WHEN THE FRACTIONAL BICLIQUE COVER NUMBER IS TWO

Informal corollary of PROOF.txt. November 4, 2026.
No Lean verification or publication-priority claim.

THEOREM
Let A be a finite nonzero binary matrix with bc_f(A)=2. Delete zero rows and columns, and identify identical rows and identical columns, obtaining its reduced kernel K. Write D=[110;111;011] and delta=bp_f^infinity(D). Exactly one of the following cases holds:

(a) rank_R(A)=2. Then r_b(A)=2 and bp_f(A^(tensor k))=2^k for every k>=1. In particular bp_f^infinity(A)=bc_f(A)=2.

(b) rank_R(A)=3. Then K is D up to row and column permutations, and bp_f(A^(tensor k))=bp_f(D^(tensor k)) for every k>=1. Consequently bp_f^infinity(A)=delta>=1/2+sqrt(5/2)>2=bc_f(A).

There are no other possibilities. Thus, among matrices with EXACT fractional cover number two, strict asymptotic fractional cover/partition separation is equivalent to real rank three, integral binary rank three, or Domino reduced kernel. This is a complete classification of STRICTNESS within the stated class; the numerical exact value of delta remains undetermined.

1. FRACTIONAL COVER TWO FORCES AN ORDINARY TWO-RECTANGLE COVER

Define a finite edge-conflict graph H(A). Its vertices are the one entries (i,j) of A. Two distinct entries (i,j) and (i',j') are adjacent when they cannot belong to a single allowed rectangle, equivalently when at least one of A_{i,j'}, A_{i',j} is zero.

An independent set I of H(A) extends to an allowed rectangle: take the row projection R and column projection C of I. For any r in R and c in C, choose members (r,j),(i,c) in I. If they coincide then A_rc=1 already. If they differ, their nonadjacency implies A_rc=1. Thus R by C is entirely contained in A. Conversely every allowed rectangle is an independent set.

Suppose H(A) has an odd cycle of length 2s+1. A rectangle contains at most s vertices of this cycle, since its vertex set is independent. Sum the fractional-cover constraints for the 2s+1 cycle vertices. The left side is at least 2s+1, while each rectangle contributes at most s times its weight. Hence every fractional cover has cost at least (2s+1)/s>2, contradicting bc_f(A)=2.

Therefore H(A) is bipartite. Color it with two colors and extend each independent color class to an allowed rectangle as above. These two rectangles cover A. Both are needed, since a one-rectangle support would have fractional cover number one. Thus the ordinary biclique cover number is exactly two. No hypothesis about the numerical value of a fractional-LP solution has been substituted for this argument.

2. THE TWO-RECTANGLE NORMAL FORM

Write the support of A as the union of R_1 by C_1 and R_2 by C_2. After zero rows/columns are removed, each row belongs to one of three membership classes:

                      R_1 only, both, R_2 only,

and the columns have the analogous three classes. With this ordering the entry between membership types is one exactly when the two types share one of the labels 1,2. The resulting 3 by 3 type matrix is D. Thus A is a duplicate blow-up of a submatrix of D.

If all three row types and all three column types occur, they give three distinct row and column patterns, so the reduced kernel is exactly D up to permutations. Since det(D)=-1, the real rank is three.

If any row type or column type is missing, there are at most two distinct rows or at most two distinct columns. Partitioning the ones by those distinct row or column patterns uses at most two disjoint rectangles. Real rank is at most two. It cannot be one: a nonzero binary real-rank-one matrix has rectangular support, which would give bc_f(A)=1. Therefore real rank and integral binary rank are both two.

This proves the exhaustive alternative, not merely a sufficient condition for finding a Domino submatrix. The elementary normal form itself is not claimed as a first discovery.

3. INVARIANCE UNDER ZERO PADDING AND DUPLICATES

Let A be obtained from K by duplicating rows and columns and adding zero rows/columns. Extending each rectangle of a fractional partition of K to all copies gives an exact fractional partition of A with the same weights. Conversely, restricting a fractional partition of A to one representative of every nonzero row/column type gives one of K, discarding any empty restricted rectangles and never increasing cost. Hence bp_f(A)=bp_f(K).

The same statements apply to integral partitions and to ordinary or fractional covers. Moreover A^(tensor k) is a duplicate blow-up and zero padding of K^(tensor k), using the product row/column type maps. Thus bp_f(A^(tensor k))=bp_f(K^(tensor k)) for every k, not just in an asymptotic inequality.

4. THE NON-DOMINO CASE HAS EXACT POWER COST TWO TO THE k

In case (a), the two-rectangle partition gives bp_f(A^(tensor k))<=2^k. To prove the reverse inequality directly, H(A) has an edge because A does not have rectangular support. Choose its two conflicting one entries e_0,e_1. Tensor products indexed by the 2^k binary words form 2^k one entries of A^(tensor k). Two distinct words disagree at a coordinate. At that coordinate the chosen conflicting entries have a zero cross-entry in at least one direction, so the two tensor entries cannot share an allowed rectangle.

Therefore every rectangle contains at most one of these 2^k entries. Summing their fractional-cover constraints proves bc_f(A^(tensor k))>=2^k. Every fractional partition is a fractional cover, so bp_f(A^(tensor k))>=2^k. This proves equality and case (a).

In case (b), duplicate invariance reduces every power exactly to D's corresponding power. The theorem from PROOF.txt gives bp_f(D^(tensor k))>=(1/2+sqrt(5/2))^k, proving strictness and case (b).

5. COMPUTABILITY AND LIMITS

Given a matrix promised to have bc_f(A)=2, real rank and the reduced kernel are computable by elementary exact polynomial-time matrix operations. The conflict graph supplies a constructive two-rectangle cover as well. One can recognize the entire class without solving an exponential fractional LP: if the support is nonrectangular and H(A) is bipartite, its two-color cover gives bc_f(A)<=2 while a conflicting pair gives bc_f(A)>=2. Conversely Section 1 proves necessity.

Thus class membership and the strict-gap alternative are polynomial-time decidable. This does not compute bp_f(A^(tensor k)) in case (b), determine delta, or classify arbitrary matrices with larger fractional cover number.
