# A STRICT ASYMPTOTIC GAP BETWEEN FRACTIONAL BICLIQUE COVERS AND PARTITIONS

Informal proof, November 4, 2026. No Lean verification. Publication priority unestablished.

THEOREM
Let
                 D = [1 1 0; 1 1 1; 0 1 1].
For every positive integer k,

       bp_f(D^(tensor k)) >= (1/2 + sqrt(5/2))^k.              (T)

Consequently

       bc_f(D) = 2 < 1/2 + sqrt(5/2) <= bp_f^infinity(D),

where 1/2+sqrt(5/2) is approximately 2.08113883008419. Thus the roots of the fractional biclique partition numbers of the Domino do NOT converge to 2. Fractional biclique cover and asymptotic fractional biclique partition are strictly different parameters.

This rules out the convergence-to-2 possibility explicitly discussed by Ghosal--Karrenbauer, SEA 2025, Section 4, and proves the strict separation missing from the comparison chain in their Section 3. It does NOT determine the exact asymptotic fractional binary rank of D, and does NOT claim the already refuted integral binary-rank multiplicativity conjecture as our result.

1. DEFINITIONS AND THE EXACT LITERATURE TARGET

For a nonzero binary m by n matrix A, an allowed rectangle is a nonempty R by C contained entirely in its ones. Write J_{R,C}=1_R 1_C^T. A fractional biclique partition is a representation

                  A = sum_{R,C} lambda_{R,C} J_{R,C},
                  lambda_{R,C} >= 0.

Its cost is sum lambda; bp_f(A) is the minimum cost. This is entrywise EQUALITY, not Boolean OR, ordinary matrix rank, or a fractional covering inequality. The fractional biclique cover number bc_f uses >=1 on each one instead. Product decompositions give bp_f(A tensor B)<=bp_f(A)bp_f(B), so Fekete's lemma yields the limit bp_f^infinity(A)=lim_k bp_f(A^(tensor k))^(1/k).

Ghosal and Karrenbauer, Engineering Insights into Biclique Partitions and Fractional Binary Ranks of Matrices, SEA 2025, Section 4, explicitly discuss the unresolved possibility that these roots for D converge to 2. Section 3 observes that strictness was known for the other inequalities in their parameter chain, while a strict example for bc_f(A)<=bp_f^infinity(A) was not given. Their Theorem 2 records lower bound 2 and upper bound 2.372713 for the Domino. We answer the convergence-to-2 question negatively; the numerical upper bound is credited, not recomputed here.

Primary target:
https://drops.dagstuhl.de/storage/00lipics/lipics-vol338-sea2025/html/LIPIcs.SEA.2025.18/LIPIcs.SEA.2025.18.html
arXiv:2502.06730, DOI 10.4230/LIPIcs.SEA.2025.18.

2. A GENERAL TENSOR-STABLE WEIGHTED TRACE-NORM BOUND

For positive row weights p_1,...,p_m and column weights q_1,...,q_n, set

 W_p=diag(sqrt(p_i)), W_q=diag(sqrt(q_j)),
 M=W_p A W_q,
 beta_A(p,q)=max_{R by C allowed in A} sqrt(p(R)q(C)),
 p(R)=sum_{i in R}p_i, q(C)=sum_{j in C}q_j.

The nuclear norm ||M||_* is the sum of its singular values. Its triangle inequality and rank-one formula give

 ||M||_* <= sum lambda_{R,C} ||W_p J_{R,C} W_q||_*
         = sum lambda_{R,C} sqrt(p(R)q(C))
         <= beta_A(p,q) sum lambda_{R,C}.

Taking the minimum over exact fractional partitions yields

             bp_f(A) >= ||W_p A W_q||_* / beta_A(p,q).       (2.1)

The critical point is that this estimate remains tensor-stable on ALL rectangles of a tensor power, including non-product rectangles.

Indeed let R by C be any allowed rectangle in A^(tensor k). Let R_j and C_j be its projections to coordinate j. For each a in R_j and b in C_j, choose a row in R with j-coordinate a and a column in C with j-coordinate b. Their tensor entry is one, so A_ab=1. Therefore R_j by C_j is an allowed rectangle in A. Positivity and product weights give

 (p^tensor k)(R) <= product_j p(R_j),
 (q^tensor k)(C) <= product_j q(C_j).

Hence its weighted rank-one nuclear norm is at most beta_A(p,q)^k. Conversely a product of maximizing rectangles attains that value, so

       beta_{A^(tensor k)}(p^tensor k,q^tensor k)=beta_A(p,q)^k.

Also

 W_{p^tensor k} A^(tensor k) W_{q^tensor k}=(W_p A W_q)^(tensor k),
 ||M^(tensor k)||_* = ||M||_*^k.                              (2.2)

For completeness, the last identity follows from any singular-value decompositions: tensoring the orthogonal/unitary factors preserves them, and the new singular values are all products of the old singular values, including zeros. Their sum is the product of the sums. Applying (2.1) to the tensor power proves

 bp_f(A^(tensor k)) >= [||W_p A W_q||_*/beta_A(p,q)]^k.        (2.3)

This is a universal sufficient LOWER-BOUND THEOREM, not a conjectured compression or rounding principle. Its proof uses ordinary matrix norms only. Optimizing weights can improve the bound, but is unnecessary for its validity.

3. EXACT EVALUATION FOR THE DOMINO

Take equal row and column weights p=q=(1,t,1), t>0. Then

                 M_t = [1 sqrt(t) 0;
                        sqrt(t) t sqrt(t);
                        0 sqrt(t) 1].

The maximal allowed rectangles of D are the two 2 by 2 corner blocks, the middle-row star, and the middle-column star. Their weighted rank-one nuclear norms are respectively

                    1+t, 1+t, sqrt(t(2+t)), sqrt(t(2+t)).

There are no other maximal rectangles: a row set containing both outer rows has only the middle column available; a row set containing the middle row and just one outer row has the corresponding two columns; the remaining possibilities are contained in these or the middle-row star. Since (1+t)^2-t(2+t)=1, we obtain

                           beta_D(p,p)=1+t.                 (3.1)

The vector (1,0,-1) is an eigenvector of M_t with eigenvalue 1. On the symmetric two-dimensional subspace spanned by (1,0,1)/sqrt(2) and (0,1,0), the matrix is

                           [1 sqrt(2t); sqrt(2t) t].

Its determinant is -t<0, so its eigenvalues have opposite signs. They are

           lambda_+,lambda_-=(1+t +/- sqrt(1+6t+t^2))/2.

Since M_t is real symmetric, its singular values are the absolute values of these three eigenvalues. Thus

                     ||M_t||_* = 1+sqrt(1+6t+t^2).          (3.2)

Combining (2.3), (3.1), and (3.2), for EVERY k>=1,

 bp_f(D^(tensor k)) >= [(1+sqrt(1+6t+t^2))/(1+t)]^k.          (3.3)

This derivation controls arbitrary rectangles of D^(tensor k); it does not merely check the 4^k product-maximal rectangles or assume that every rectangle factors.

4. OPTIMIZATION AND THE STRICT ASYMPTOTIC GAP

Put z=1/(1+t), so 0<z<1. The ratio in (3.3) becomes

                   z+sqrt(1+4z-4z^2).

Writing u=2z-1 transforms this into

                   1/2 + u/2 + sqrt(2-u^2).

Cauchy--Schwarz bounds u/2+sqrt(2-u^2) by

                   sqrt((1/2)^2+1^2) sqrt(2)=sqrt(5/2).

Equality is attainable at u=sqrt(2/5), which lies in (-1,1). Equivalently

                   t=(7-2sqrt(10))/3 > 0.

Thus the maximum over these symmetric weights is exactly

                         c=1/2+sqrt(5/2)>2.

Substituting this t into (3.3) proves (T). Taking k-th roots and then the existing Fekete limit gives bp_f^infinity(D)>=c. No numerical fitting or exchange of uncontrolled limits is used.

To verify bc_f(D)=2 without relying on a reported LP optimum, cover D by its two 2 by 2 corner blocks with unit weights. Their union is all seven ones, so bc_f(D)<=2. Conversely the entries (0,0) and (2,2) cannot lie in one allowed rectangle, since its cross-entries (0,2) and (2,0) would be zeros. Summing the two fractional-cover constraints therefore gives total weight at least 2. Hence bc_f(D)=2, and

                        bc_f(D)<bp_f^infinity(D).

This is the previously missing strict separation in the source's comparison chain. It rules out the convergence-to-2 possibility. It leaves a nontrivial interval for the exact asymptotic fractional binary rank; the source's upper bound 2.372713 is compatible with our theorem.

A simple rational weighting already suffices for strictness: choose t=1/4. Then (3.3) gives

           bp_f(D^(tensor k)) >= [(4+sqrt(41))/5]^k,
           (4+sqrt(41))/5 approximately 2.08062484748657 >2.

This version uses the rational matrix diag(1,1/2,1) D diag(1,1/2,1) and is useful for exact finite checks. The optimized algebraic t improves the constant slightly.

5. CONSEQUENCES AND LIMITS

(a) The gap between fractional cover and exact fractional partition is exponential on tensor powers:

 bp_f(D^(tensor k))/bc_f(D^(tensor k)) >= (c/2)^k.

Here bc_f(D^(tensor k))=2^k can be proved directly. Product corner covers give the upper bound. The 2^k diagonal entries indexed by words in {0,2}^k form a fooling set: any two different words have a coordinate 0 versus 2, forcing a zero cross-entry. No allowed rectangle contains two of them, giving the lower bound. This avoids assuming general multiplicativity of fractional covers.

(b) There can be no universal conversion of a fractional cover of tensor powers into an exact fractional partition with only a subexponential multiplicative increase in cost. The displayed family is an explicit counterexample. This is an affirmative separation theorem, not an impossibility speculation about a particular search method.

(c) The result concerns fractional partitions. For the integral binary rank, det(D)=-1 and row partitions give r_b(D^(tensor k))=3^k. Ordinary real rank is multiplicative and is at most integral binary rank. Thus integral Domino rank is already understood and is NOT the remaining target.

(d) This proof does not establish a new algorithm for tensor isomorphism, a P-versus-NP or VP-versus-VNP separation, the exact value of bp_f^infinity(D), or a first-discovery claim. Matrix nuclear norms, weighted factorization bounds, and their Kronecker identities are standard machinery. The claim requiring a novelty audit is their explicit application yielding the strict asymptotic fractional cover/partition separation here.

6. VERIFICATION AND REUSE

The proof is self-contained given elementary singular-value decomposition and its trace-norm triangle inequality. It applies to all tensor exponents, independently of finite computation. controls.py enumerates all allowed rectangles of D and D tensor D under t=1/4 using exact rational weighted sums, and checks the claimed rectangle-norm maximum. A separate exact quadratic-field check validates a tensor-stable LP-dual witness, described in CONTROLS.json. Finite controls corroborate the derivation; they do not replace it.

Actual federated searches and selected source readings are recorded in RETRIEVAL.json. Broad library discovery is not checked-theorem reuse; no Lean compilation or axiom audit is claimed. Prior local binary-rank notes frequently concern rank over F2, which is a different parameter and was not substituted for biclique partition rank.

BACKGROUND AND CREDIT
Angikar Ghosal and Andreas Karrenbauer, Engineering Insights into Biclique Partitions and Fractional Binary Ranks of Matrices, SEA 2025, Sections 3-4 and Theorem 2, DOI 10.4230/LIPIcs.SEA.2025.18; arXiv:2502.06730.
https://drops.dagstuhl.de/storage/00lipics/lipics-vol338-sea2025/html/LIPIcs.SEA.2025.18/LIPIcs.SEA.2025.18.html

Valerie L. Watts, Fractional Biclique Covers and Partitions of Graphs, Electronic Journal of Combinatorics 13 (2006), R74, DOI 10.37236/1100. Background on fractional parameters and products.
https://www.combinatorics.org/ojs/index.php/eljc/article/view/v13i1r74

Hamza Fawzi and Pablo A. Parrilo, Lower bounds on nonnegative rank via nonnegative nuclear norms, arXiv:1210.6970; and Self-scaled bounds for atomic cone ranks, arXiv:1404.3240. Related prior norm/atomic methods are credited; we do not claim to invent nuclear-norm lower bounds.
https://arxiv.org/abs/1210.6970
https://arxiv.org/abs/1404.3240

The integral binary-rank multiplicativity counterexample of Yaroslav Shitov, July 2026, is credited separately in ALREADY-SOLVED-SHITOV.txt and SHITOV-CERTIFICATE.json. It is not counted as our closure.
