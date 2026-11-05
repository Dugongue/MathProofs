# LOGSPACE EXACT COUNTS FOR SKEW TABLEAUX WITH SMALL INNER DURFEE RANK

Informal sufficient theorem, November 4, 2026. No Lean verification or publication-priority claim.

STATUS. The unrestricted Question 5.15 of Gutierrez--Ikenmeyer--Panova, Counting in logarithmic space, arXiv:2607.15881, remains open in this work. This document proves a positive FL and hence #L theorem with an explicit restriction on the inner partition. Both partition lengths, both partition sizes, and the number of skew rows may grow. It is not a claimed resolution of the unrestricted question.

THEOREM. Fix a constant C. Given unary partitions mu subset lambda with total input length N, write d for the Durfee rank of mu. The total function which outputs f^(lambda/mu) if d! <= N^C, and zero otherwise, belongs to FL. Its values are nonnegative, so it also belongs to #L. In particular this applies to every fixed inner Durfee rank and, for suitable fixed constants, to d log(d+1) = O(log N). No condition is placed on the outer Durfee rank. Invalid partition inputs may be assigned zero.

Here FL means a deterministic logarithmic-workspace transducer with a write-only polynomial-length output. It does not mean storing the output integer in logarithmic space. All arithmetic below is on integers of polynomially bounded bit length. Standard logspace iterated multiplication, division, addition, subtraction, and composition with logspace bit generators are charged explicitly. The unrestricted determinant is never treated as an FL primitive.

1. A FACTORIAL ALTERNANT WITH ONLY d REPLACED COLUMNS

Let l be the length of lambda after removing trailing zeros, and let n = |lambda|-|mu|. Handle l=0 directly: the only valid case is empty/empty, with answer 1. Pad mu to length l. In increasing order define
 a_i = lambda_(l+1-i) + i-1,  i=1,...,l,
 b_j = mu_(l+1-j) + j-1,     j=1,...,l.
The a_i are distinct nonnegative integers, strictly increasing; the b_j are also strictly increasing. All are O(N). Write P_k(t)=t(t-1)...(t-k+1), with P_0=1. Aitken's formula gives
 f^(lambda/mu) = n! det[P_(b_j)(a_i)] / product_i a_i! .       (1)
This includes P_k(a)=0 for 0<=a<k. Reversing both the rows and columns of the usual decreasing-index formula introduces no sign.

Let V_(i,h)=P_h(a_i), h=0,...,l-1. As these polynomials are monic of successive degrees,
 Delta := det V = product_(i<j)(a_j-a_i) > 0.                 (2)
Exactly d of the b_j are at least l: in the original order this is precisely mu_j >= j. Thus the exponent set {b_j} removes d holes H={h_1<...<h_d} from {0,...,l-1} and adds d high exponents K={k_1<...<k_d}, all k_t>=l.

For each k in K let R_k(t) be the unique polynomial of degree less than l satisfying R_k(a_i)=P_k(a_i), and expand
 R_k(t) = sum_(h=0)^(l-1) c_(h,k) P_h(t).
Start with V and replace its column h_t by the evaluation column P_(k_t)(a_i). The determinant ratio is det[c_(h_s,k_t)]_(s,t=1)^d: all the unchanged identity columns can be removed from V^(-1) times the new matrix. Sorting the new exponent columns into increasing order has
 I = sum_(t=1)^d (l-1-h_t-(d-t))
inversions. Consequently
 det[P_(b_j)(a_i)] = (-1)^I Delta det[c_(h_s,k_t)].            (3)
For d=0 the empty determinant is 1. Equations (1)--(3) are exact, without a supplied flag, decomposition, or generic-position hypothesis.

2. EVERY REDUCED ENTRY IS EXPLICITLY FL

Put d_i=product_(j!=i)(a_i-a_j), which is nonzero and may be negative. Lagrange interpolation and Newton finite differences give
 c_(h,k) = (1/h!) sum_(s=0)^h (-1)^(h-s) binom(h,s)
                  sum_(i=1)^l P_k(a_i) product_(j!=i)(s-a_j)/d_i.  (4)
Indeed the inner sum is R_k(s), and the h-th forward difference at zero divided by h! is exactly the coefficient of P_h in a polynomial of degree less than l.

A single positive common denominator is
 D = Delta (l-1)! .
Since every d_i divides Delta as a signed integer and h! divides (l-1)!, all entries M_(h,k)=D c_(h,k) are integers. Explicitly
 M_(h,k) = ((l-1)!/h!) sum_(s=0)^h (-1)^(h-s) binom(h,s)
              sum_(i=1)^l (Delta/d_i) P_k(a_i) product_(j!=i)(s-a_j).   (5)
Thus the answer is the exact integer quotient
 f^(lambda/mu) = (-1)^I n! Delta det[M_(h_s,k_t)]
                       / ((product_i a_i!) D^d).             (6)
No individual rational Naruse summand is interpreted as a path count; the only final division is an exact division of fully assembled integers.

All products in (5) have polynomially many O(log N)-bit factors. Delta and D have O(N^2 log(N+1)) bits; each M entry has polynomial bit length. The signed sums have at most l(l+1) terms. Iterated multiplication and integer division are in DLOGTIME-uniform TC0 and hence FL, by Hesse--Allender--Barrington (2002), Corollary 6.3. Polynomially many signed summands are handled by separately adding positive and negative parts, followed by subtraction. Factorials and binomials are exact product quotients. The bits of every factor are generated with counters for i,j,s,h,k using O(log N) space. Standard FL composition supplies virtual inputs to the arithmetic transducers, so none of these large integers is stored on the work tape. The nesting depth of these constructions is fixed; it does not grow with d or l.

3. THE SMALL DETERMINANT AND COMPLEXITY ASSEMBLY

On the stated domain there are d! <= N^C permutations. A permutation can be represented by its Lehmer code using O(log(d!)+d) = O(log N) bits. Its values, inversion parity, and sign are recovered by rescanning that code. Equivalently one may enumerate rank codes 0,...,d!-1 and unrank with recomputation. For each code generate the d entry values and use FL iterated multiplication. Sum positive and negative permutation terms separately. There are polynomially many terms, every term has polynomial bit length, and their sum has polynomial bit length. This evaluates the reduced determinant in FL, with no determinant oracle. In (6) use signed exact division and the known nonnegative final answer. This proves FL membership.

Testing d! <= N^C itself uses logarithmic space: multiply successive factors with saturation at N^C+1, whose binary length is O(log N) for fixed C. Partition validity, containment, d, holes H, high exponents K and inversion count I are all obtained by bounded scans and counters. Empty and zero-dimensional cases were handled above. Therefore the promised-domain construction extends to the total function stated in the theorem.

Finally, any nonnegative FL function with polynomial output length belongs to #L. Fix a polynomial bit bound L(N) for its value. Guess an L(N)-bit integer z, most significant bit first. Maintain the three-valued comparison state against the corresponding output bit of the deterministic FL transducer, recomputed from the input and position each time. Accept exactly if z is smaller than the value. This creates exactly f accepting paths, uses O(log N) workspace, and runs in polynomial time. Signed intermediate quantities never become negative path multiplicities.

4. WHAT THIS DOES AND DOES NOT SETTLE

The result covers inner hooks of arbitrary size (d=1), arbitrary fixed Durfee rank, and a slowly growing rank up to the explicit factorial budget. For example mu may have unbounded row length and unbounded number of rows while d stays 1. The outer partition is unrestricted. This is a sufficient algorithmic theorem, not a necessary condition or a failed-route barrier.

It does not prove the full unrestricted #L assertion. For unrestricted d the final d-by-d determinant cannot be expanded in polynomially many permutations; replacing this step by generic determinant evaluation supplies GapL, which was already known and is weaker than the required #L conclusion. Neither total positivity nor a positive final value justifies making that replacement inside #L. The separate Naruse and many-path routes remain unassembled, as recorded in ROUTE.json. No claimed universal solution is hidden in a compression assumption.

PRIMARY SOURCES AND CREDIT
Gutiérrez, Ikenmeyer, Panova, Counting in logarithmic space, July 2026, Question 5.15:
https://arxiv.org/html/2607.15881#S5.Thmde15
https://arxiv.org/abs/2607.15881
Hesse, Allender, Barrington, Uniform constant-depth threshold circuits for division and iterated multiplication, JCSS 65 (2002), Corollary 6.3:
https://people.cs.rutgers.edu/~allender/papers/division.pdf
The factorial alternant/Aitken determinant, Vandermonde determinant, Lagrange interpolation, Newton differences, and low-column determinant reduction are classical. Okounkov--Olshanski's shifted Schur framework (Theorem 8.1 and Section 13) independently explains the Durfee/Giambelli reduction:
https://arxiv.org/abs/q-alg/9605042
This proof uses the elementary interpolation version rather than asserting unproved logspace evaluation of shifted complete functions. First-publication priority for the stated restricted FL theorem has not been established. Earlier exact Hermite/principal-Schur FL closure belongs to the prior public fengqiaoqu draft, independently audited in the sibling hermite-logspace packet; it is not claimed as our discovery here.
