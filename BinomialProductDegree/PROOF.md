# Polynomial-time degree computation for a product of rational binomials minus a monomial

**Provenance:** AI-assisted informal proof recorded by [Dugongue](https://github.com/Dugongue), first recorded 27 October 2026 and independently audited by another project worker on 31 October 2026. Independent human review, novelty assessment and Lean formalization are pending.

**Scope:** explicit rational coefficients and nonnegative binary exponents. This answers that precise discrete version of the displayed question; it is not a general DegSLP or arbitrary-coefficient-oracle claim.

## Status

The standard explicit-rational binary-input problem is completely solved at the informal mathematical level by the prime-bank algorithm below. This includes every explicit integer input. The proof covers all coefficients, arbitrary signs, zero factors, zero exponents, leading cancellations and exponentially large numerical exponents. No mathematical or bit-complexity gap was found in the October 27 argument. A separately written implementation passed 3,000 new exact full-input comparisons and very large binary-scale controls.

This is an unconditional polynomial-bit algorithm. It uses no PIT, factoring, counting oracle, ETH result, unknown representation or genericity premise. Novelty is not established, and no Lean/kernel verification occurred in this audit.

## Exact statement
Input: a finite list of rational pairs (alpha_i,beta_i), nonnegative integers e_i, a rational A and a nonnegative integer N. Rationals are supplied by signed binary numerators and nonzero binary denominators; all exponents are binary. Output the degree in binary of

    P(X)=product_i(alpha_i X^(e_i)+beta_i)-A X^N,

or a distinguished ZERO symbol when P is zero. Let B be the complete bit length of this input. There is a deterministic B^{O(1)} bit-time, polynomial-space algorithm for this problem.

## Original source and convention audit
Guillaume Lagarde's author-maintained page, updated September 23, 2026, explicitly displays precisely this polynomial family and asks for polynomial-time degree computation (or better hardness):
https://guillaume-lagarde.github.io/problems.html

The page discusses DegSLP using the discrete class coRP^PP and cites Koiran-Perifel (2007) and Kayal (2010). It does not explicitly say how scalar coefficients are encoded. The discrete complexity label alone does NOT logically force characteristic zero: finite-field encodings also admit Turing complexity statements. However, the cited Koiran-Perifel primary text explicitly uses only the constants -1,0,1 and therefore integer polynomial coefficients in characteristic zero. It also explicitly discusses usual Boolean Turing machines and binary encoding:
https://doi.org/10.1016/j.tcs.2007.08.008
https://fileserver-az.core.ac.uk/download/52328879.pdf

Thus explicit integers/rationals are the standard discrete characteristic-zero interpretation of the displayed problem. The theorem above is a complete affirmative answer under that convention. It should not be presented merely as a special positive-coefficient, bounded-exponent or generic-input subclass. Equally, the author page's silence must not be turned into a claim to solve all coefficient oracles, all characteristics or generic DegSLP.

Kayal's cited report is available at the source link below. Its Section 5 studies a binary degree threshold, finite-field coefficient computation and the coRP^PP algorithm. It does not justify assuming an arbitrary real/complex oracle encoding for the restricted displayed instance:
https://eccc.weizmann.ac.il/report/2010/073/

## Proof

### 1. Complete preprocessing and zero detection.
At exponent e_i=0 replace a factor by alpha_i+beta_i. For e_i>0, alpha_i=0 contributes a constant; beta_i=0 contributes a scalar times X^(e_i). A zero factor makes the product zero, leaving -A X^N, which is decided directly. Otherwise, after collecting scalars and monomials, write

    Q(X)=C X^b product_(i=1..t)(X^(e_i)+c_i),

where C!=0, c_i!=0, e_i>=1, b>=0. All data have polynomial bit size. If t=0, P is the difference of two monomials, and its degree or zero status is decided by comparing their coefficients and exponents.

For t>0 put D=b+sum e_i. The coefficients at both extreme degrees b and D are nonzero, with b<D, so subtracting a single monomial cannot make P zero. If A=0 or N<D, degree P=D; if A!=0 and N>D, degree P=N; if N=D and A!=C, degree P=D. Only A=C and N=D remains.

### 2. The exact valuation problem.
Set E=sum e_i and

    F(z)=product_i(1+c_i z^(e_i)).

This polynomial is nonconstant, has constant coefficient one and degree E. Reversal gives

    P(X)=C X^D (F(1/X)-1),
    degree P=D-nu, where nu=valuation_z(F-1), 1<=nu<=E.

The numerical E and nu may be exponential in B. The algorithm will not enumerate that interval.

### 3. Positive Euler normalization, with cancellation retained exactly.
For c<0, use the factor 1-(-c)z^e. For c>0, use

    1+c z^e=(1-c^2 z^(2e))/(1-c z^e).

Combine equal pairs (d,a) and delete zero multiplicities. This yields

    F(z)=product_(j=1..s)(1-a_j z^(d_j))^(m_j),

where a_j are positive rationals, d_j>=1, m_j are nonzero signed integers and s<=2t. The equality holds as rational functions and as formal power series at zero. The list is nonempty, since F is nonconstant. Let d0=min d_j, and let r be the number of records there. Their positive bases a_j are pairwise distinct.

### 4. Logarithmic derivative and valuation.
In characteristic zero,

    G(z)=-z F'(z)/F(z),
    Gamma_v=[z^v]G=sum_(d_j divides v) m_j*d_j*a_j^(v/d_j).

If F=1+u z^nu+..., u!=0, then G=-nu*u z^nu+..., so valuation G=nu. The Euler representation may have negative powers, but all denominators have constant coefficient one, and its formal derivative/geometric expansions are therefore valid. No numerical logarithm is computed.

### 5. Universal prime witness.
For each nonminimal record define q_j=d_j/gcd(d_j,d0)>1. For a prime p,

    d_j divides p*d0  iff q_j divides p  iff q_j=p.

Every nonminimal record therefore forbids at most one prime. Among the first s primes at least r avoid all s-r nonminimal records. At each such good prime,

    Gamma_(p*d0)=d0 * sum_(d_j=d0) m_j a_j^p.

A nonzero sum H(x)=sum_(i=1..r) gamma_i a_i^x with distinct positive bases and nonzero real coefficients has at most r-1 distinct real zeros. Divide by one exponential; differentiation leaves r-1 exponentials with distinct nonzero exponents; induction and Rolle's theorem prove the bound. Consequently the displayed r-term sum cannot vanish at all r good primes. Therefore

    nu<=p_s*d0.

This argument covers cancellation of the first moment and any subsequent moments; no noncancellation promise remains.

### 6. Elementary polynomial bound on p_s.
For even x, the central binomial coefficient is at least 2^x/(x+1). Legendre's formula shows that each prime contributes a prime power at most x to that coefficient, so it is at most x^{pi(x)}. Hence

    pi(x)>=(x-log_2(x+1))/log_2 x.

For x=16s^2, log_2 x<=2s+2 and log_2(x+1)<=2s+3, so the last expression is at least s. Thus p_s<=16s^2. The primes certify the bound but need not be generated by the algorithm.

### 7. The actual sparse dictionary and decoder.
Set K=16s^2 and M=min(E,K*d0). For every record (d_j,a_j,m_j), enumerate only

    k=1,...,floor(M/d_j),

adding m_j*d_j*a_j^k to the dictionary entry keyed by k*d_j. Since d_j>=d0, each record contributes at most K entries. There are at most sK=16s^3 contributions. Formula for Gamma shows that every omitted key below M has zero coefficient. The prime-witness and valuation lemmas show some retained key has a nonzero coefficient. Delete exact zero entries and take the least surviving key. It is nu, so return D-nu.

The dictionary covers all possible contributions below the proved bound, not just the prime witness indices. Therefore its minimum is the true first nonzero coefficient, rather than merely an upper bound on it. It is initialized and decoded explicitly.

### 8. Polynomial bit complexity.
Normalization creates s=O(B) records, with positive bases having total rational numerator/denominator bit height O(B), binary d_j of O(B) bits, and multiplicities of O(log B) bits. Only powers a_j^k with k<=K=O(B^2) are formed, so their heights are O(B^3). At any dictionary key, at most one power from each record contributes. A common-denominator bound keeps the exact sum's height polynomial in B, as do all intermediate partial sums. Multiplication by d_j adds only O(B) bits. Keys k*d_j also have O(B) bits.

There are O(B^3) updates. Binary integer arithmetic, rational gcd reduction, dictionary sorting, equality checks and final output arithmetic therefore all take B^{O(1)} bit time and polynomial memory. The routine never raises a coefficient to an input-sized numerical exponent or expands to numerical degree E. This completes the theorem.

## Adversarial audit findings
- The proof genuinely needs positive bases, but the exact signed Euler identity produces them from EVERY nonzero rational c_i; original coefficients need not be positive.
- q_j>1 follows from d_j>d0, so the good-prime count has no missing divisibility case.
- Equal (d,a) records must be merged before the exponential-zero lemma; the algorithm does so.
- A zero first Euler moment does not cause an early return. All surviving bank entries are compared.
- F cannot be identically one in the t>0 branch, since its leading coefficient is product c_i!=0 and degree E>0.
- The log-derivative equality of valuations uses characteristic zero, which is part of the exact rational theorem.
- All monomial, zero and exponent-zero branches were included in the independent implementation.
- A common real algebraic number-field extension from the previous session is valid with an explicitly supplied field presentation. It is not needed to settle this standard rational input problem and is not made an extra prerequisite.

## Independent executable controls
The mathematical argument was audited against a separately written implementation. The portable verify.py supplied here exercises degree.py against independent exact polynomial expansion. It passed 3,000 random complete rational inputs, compared against independent exact polynomial expansion, including leading-cancellation and zero branches. Four zero-first-moment scaled cases used exponents of bit lengths 11, 101, 1001 and 10001. A 1001-factor signed-unit identity with numerical degree 2^1000 returned the correct constant remainder without expanding its enormous empty interval. The reproducible receipt is CHECKS.json. Finite controls corroborate the implementation; the universal proof is above.

## Novelty/source search
Primary web queries targeted the displayed problem, DegSLP, product/binomial valuation, logarithmic derivatives and prime isolation. GitHub repository queries included Lagarde/binomial/degree, DegSLP, and positive/Euler/valuation. No matching prior polynomial-bit algorithm was identified. Two of these searches returned no repositories; the broad positive/Euler query was noisy (278 total, first 100 retrieved) and is not an exhaustive global code search. Search receipts are retained in the private research archive; this publication package contains no search caches. No authenticated GitHub code search or comprehensive citation review was performed.

The proper status is therefore: complete independently audited INFORMAL affirmative solution of the explicit-rational displayed degree problem, first proved in our October 27 work; bounded novelty search inconclusive; no Lean verification, no external peer review. This audit should not count the old algorithm as a second new discovery.

## Reproduce

Run `python verify.py` in this directory. It uses only the Python standard library and writes `CHECKS.json`. Import `degree` from `degree.py` for the reference algorithm; it returns `None` for the zero polynomial. Finite controls support implementation checks and do not establish novelty or replace the proof.

## Attribution

The motivating displayed question is credited to [Guillaume Lagarde](https://guillaume-lagarde.github.io/problems.html). The proof above is presented as MathProof project work with AI assistance. Its use of formal logarithmic derivatives, Rolle's theorem and elementary prime bounds is explicitly explained. No source code or manuscript passages from the cited works are redistributed.
