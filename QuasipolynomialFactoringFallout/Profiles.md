# Extension profiles and explicit witnesses over finite fields

For finite étale multiplication tensors, membership at any extension degree is polynomial-time. The binary threshold problem for the least degree is NP-complete. For compact tensors representing a power equation, computing the least degree is equivalent to multiplicative order. The assumed complete finite-field factoring algorithm gives explicit power witnesses with factorization degrees controlled by prime divisors of the exponent and extension degree.

## 1. Polynomial-time profiles and NP-complete minimum degree

A finite étale algebra over \(\mathbb F_q\) is a product of finite extensions. Its multiplication tensor treats the two inputs of the bilinear multiplication and the output as three ordinary modes. For unital associative algebras, multiplication-tensor isomorphism is equivalent to algebra isomorphism. Indeed if \(W(xy)=P(x)Q(y)\), evaluation at either argument equal to one shows \(a=P(1)\) and \(b=Q(1)\) are units. Then \(a^{-1}W(-)b^{-1}\) is an algebra isomorphism by associativity. Conversely any algebra isomorphism gives an ordinary witness. This holds after every field extension. [Exact associative isotopy](https://github.com/Dugongue/MathProofs/blob/main/AssociativeIsotopyDegeneration/PROOF.md)

**Theorem 1.** Given equal-dimensional finite étale algebras \(A,B\) over \(\mathbb F_q\) by structure constants, compute in deterministic polynomial bit time an exact representation of the scalar-extension isomorphism profile of their ordinary multiplication tensors. The representation is two arrays of \(n\) integers for side \(n\). Testing membership at a degree \(e\) given in binary takes polynomial time in \(n,\log q,\log e\). The threshold problem
\[
 \text{does there exist }1\le e\le M\text{ with }
        T_A\simeq_{\mathbb F_{q^e}}T_B?
 \tag{1}
\]
for binary \(M\) is NP-complete even over \(\mathbb F_2\). For every fixed \(0<\epsilon<1/2\), computing a feasible degree within a factor \(n^{1/2-\epsilon}\) of the least degree is NP-hard on this class.

*Profile algorithm.* Let \(a_d\) be the number of degree-\(d\) field factors of \(A\). Compute the matrix of the \(\mathbb F_q\)-linear endomorphism \(F:x\mapsto x^q\) by powering each basis vector, and set \(u_e=\dim\ker(F^e-I)\) for \(1\le e\le n\). A degree-\(d\) field factor contributes \(\gcd(d,e)\) to the fixed dimension. Thus
\[
 u_e=\sum_{d=1}^n a_d\gcd(d,e)
     =\sum_{t\mid e}\varphi(t)\sum_{d:t\mid d}a_d.
\]
The second equality uses \(\sum_{t\mid m}\varphi(t)=m\). Möbius inversion recovers \(\sum_{d:t\mid d}a_d\) for each \(t\), and descending subtraction recovers \(a_d\). Repeat for \(B\). At degree \(e\), a degree-\(d\) field factor becomes \(\gcd(d,e)\) factors of relative degree \(d/\gcd(d,e)\), by the orbits of the \(e\)-th Frobenius power on a \(d\)-cycle. Compare the resulting arrays. [Earlier finite-field profile theorems](https://github.com/Dugongue/MathProofs/blob/main/SimultaneousComputabilityAndGrochow/FiniteFieldProfiles.md)

This gives NP membership with \(e\) as the certificate. Validity of the input format can also be checked in polynomial time. Check commutativity, associativity and the unit equations. A verified finite-dimensional commutative unital algebra is étale precisely when \(x\mapsto x^q\) is injective, since some Frobenius power kills each nilpotent and a reduced finite algebra is a product of fields.

*Hardness construction.* Let \(G\) be a simple graph on \(v\) vertices, and assign distinct primes \(p_i\) to its vertices. Denote a cycle of length \(d\) by \([d]\). For an edge whose primes are \(a,b\), take the signed difference
\[
       ab[1]-b[a]-a[b]+[ab].
\]
Its positive and negative lists each have total length \(2ab\), and the difference of their fixed-point counts at the \(e\)-th power is
\[
         ab(1-\mathbf 1_{a\mid e})(1-\mathbf 1_{b\mid e}).
\]
Sum the positive lists over all edges and likewise the negative lists. If any edge is uncovered by the primes dividing \(e\), the total fixed-point difference is positive. If these primes cover every edge, then the primes dividing every multiple \(et\) also cover every edge, so the two \(e\)-th powers have equal fixed-point counts at all powers. These determine their cycle lists by Möbius inversion. Realizing each cycle as the corresponding field factor gives a pair with least accepting degree equal to the minimum product of the vertex primes of a cover. [Karp, Node Cover completeness](https://doi.org/10.1007/978-1-4684-2001-2_9)

Choose \(X=v^3\) for large \(v\). Partition \([X,2X]\) into \(O(v)\) integer intervals of width at most \(X/(10v)\). The prime number theorem gives \(\Omega(X/\log X)\) primes in the full interval, so one part has at least \(v\). A deterministic sieve finds it in polynomial time. If \(P\) is its lower endpoint, its primes lie between \(P\) and \(P(1+1/(10v))\). Any product of at most \(k\le v\) of them is less than \(2P^k\), while any product of at least \(k+1\) is at least \(P^{k+1}>2P^k\). Use \(M=2P^k\). Finite small sizes and empty graphs can be handled directly. The output side is \(2\sum_{ij\in E(G)}p_i p_j\), and the field factors have degree at most \((2X)^2\). Shoup's fixed-characteristic algorithm constructs the necessary irreducibles deterministically in polynomial time over \(\mathbb F_2\), so the multiplication tables can be written in polynomial time. [Shoup, deterministic irreducible construction](https://www.shoup.net/papers/detirred.pdf) · [Prime number theorem](https://arxiv.org/abs/2002.03255)

For approximation hardness use \(X=v^C\) with a sufficiently large fixed \(C\) depending on \(\epsilon\). The output side satisfies \(n\le 4v^2P^2(1+1/(10v))^2\). Hence \(2n^{1/2-\epsilon}<P\) for large \(v\). If a cover of size at most \(k\) exists, an approximation of the specified quality gives a feasible degree below \(P^{k+1}\). Otherwise every feasible degree is at least \(P^{k+1}\). This proves the hardness claim. \(\square\)

The degree in (1) is binary. An explicit field presentation and isomorphism matrices at degree \(e\) can have length proportional to \(e\log q\), while the existence query at that degree uses only \(\log e\) bits.

## 2. Compact power equations and multiplicative order

Let \(k=\mathbb F_q\) be explicitly presented, \(b\in k^\times\), and let \(N\ge2\) be given in binary. The preceding exact ordinary tensor compiler for \(x^N=b\) gives a pair of unital associative multiplication tensors of side \(O(\log N)\) with fixed formulas lifting a root to a tensor isomorphism. The pair accepts exactly the finite extension degrees containing a root. [Compact power-tensor construction](../OrdinaryTensorTransferFallout/Arithmetic.md)

**Theorem 2.** Write \(H=q-1\). For a supplied binary \(e\), existence of a root of \(x^N=b\) in \(\mathbb F_{q^e}\) is decidable unconditionally in deterministic time polynomial in \(\log q,\log N,\log e\). The full profile is one divisibility cone \(d\mid e\), with \(d\mid N\). Computing \(d\) for these compact inputs is polynomial-time Turing-equivalent to computing the multiplicative order of a given finite-field element. An integer factorization of \(N\) also suffices to compute \(d\) in polynomial bit time.

*Membership.* Put \(Q=q^e-1\) and \(g=\gcd(N,Q)\). Cyclicity gives the test \(b^{Q/g}=1\). Compute \(g\) by modular powering modulo \(N\). Then compute \(q^e\) modulo \(gH\), subtract one from its residue, divide by \(g\), and reduce modulo \(H\). This gives \(Q/g\bmod H\) and suffices for the power of \(b\). If \(H=1\) every test accepts. All other moduli have bit lengths polynomial in \(\log q,\log N\).

*Least degree.* At a prime \(\ell\mid H\), put \(u=v_\ell(H)\), \(a=v_\ell(N)\), and \(c=v_\ell(\operatorname{ord}(b))\). Primes with \(c=0\) impose no condition. Otherwise the test requires \(v_\ell(q^e-1)\ge a+c\). For odd \(\ell\), the left side is \(u+v_\ell(e)\), so the exponent required in \(d\) is \(\max(0,a+c-u)\). For \(\ell=2\) and odd \(q\), the valuation is \(u\) for odd \(e\) and \(u+v_2(q+1)+v_2(e)-1\) for even \(e\). For a positive gap \(a+c-u\) the required exponent is \(\max(1,a+c-u-v_2(q+1)+1)\). A nonpositive gap requires none. These identities follow by removing prime-to-\(\ell\) powers via the geometric sum and then applying the binomial expansion for odd \(\ell\) or factoring successive differences of squares for \(\ell=2\). Every required exponent is at most \(a\), since \(c\le u\). Given a factorization of \(N\), obtain all needed \(c\)'s by testing \(b^{H/\ell^j}=1\) for \(0\le j\le u\). The largest valid \(j\) is \(u-c\). This avoids factoring \(H\).

For the single order query, set \(h=\gcd(N,H)\), \(I=N/h\), and obtain the order \(C\) of \(b^{H/h}\). Its valuation is \(v_\ell(C)=\max(0,c-u+\min(a,u))\). Thus the odd part of \(d\) is
\[
 d_{\rm odd}=C_{\rm odd}\gcd\bigl(I,C_{\rm odd}^{\lceil\log_2(N+1)\rceil}\bigr).
\]
Positive valuations in \(C_{\rm odd}\) indicate exactly the active odd-prime gaps, and each active gap is \(v_\ell(C)+v_\ell(I)\). The gcd takes the full part of \(I\) supported on those primes without factoring either integer. For \(2\), if \(q\) is odd and \(v_2(C)>0\), use gap \(v_2(C)+v_2(I)\) in the previous formula. In every other case use no factor of two. The remaining arithmetic has polynomial bit complexity.

Conversely take \(N=q-1\) for \(q\ge3\). Every geometric root satisfies \(x^q=bx\), hence \(x^{q^e}=b^e x\). Every geometric root is defined over exactly the extensions with \(b^e=1\), so the least degree gives \(\operatorname{ord}(b)\). The case \(q=2\) has order one. \(\square\)

## 3. Output-sensitive witness construction under the factoring premise

Assume complete deterministic factorization of degree-\(t\) polynomials over a presented finite field of order \(U\) in \(t^{O(1+\log t)}(\log U)^{O(1)}\) bit time.

**Theorem 3.** For an accepting degree \(e\), given the integer factorization of \(N\) and an explicit presentation of \(\mathbb F_{q^e}\) over \(k\), a compact power-tensor witness can be produced using only binomial factorizations of degrees at most the largest prime factor of \(\gcd(N,q^e-1)\). Constructing the field as well uses factorization degrees at most the largest prime factor of \(e\), with temporary fields of at most that factor times the target field's bit dimension. At the least degree \(d\), the entire output uses factorization degrees at most the largest prime \(B\) dividing \(\gcd(N,q-1)\), and runs in
\[
          B^{O(1+\log B)}\operatorname{poly}(d,\log q,\log N)
\]
bit time, with no integer factorization supplied in this version. Take \(B=1\) if the gcd is one. The extension field and all three ordinary isomorphism matrices are explicit.

*Root extraction in a supplied field.* Put \(Q=q^e-1\), \(g=\gcd(N,Q)\). Find integers \(a,z\) with \(aN+zQ=g\). The equation \(X^N=b\) for units implies \(X^g=b^a\). Conversely \(aN/g\equiv1\pmod{Q/g}\) and \(b^{Q/g}=1\) on an accepting probe. Hence raising \(X^g=b^a\) to \(N/g\) gives \(X^N=b\).

Extract a \(g\)-th root a prime factor at a time from \(b^a\), choosing any linear factor of the current binomial \(X^\ell-c\). The choices remain compatible. In fact if \(c\) is an \(\ell h\)-th power and \(\ell h\mid Q\), any \(\ell\)-th root differs from a known \(h\)-th power by an \(\ell\)-th root of unity. Every such root of unity is an \(h\)-th power in the cyclic group of order \(Q\), since \(\ell h\mid Q\). So the remaining extraction stays feasible. All factors of \(g\) are read from the supplied factorization of \(N\). There are at most \(\log_2 N\) steps, and the lifted root gives the three isomorphism matrices. This uses no integer factorization of \(q^e-1\). The case \(g=1\) needs no binomial calls.

*Constructing the target field.* Iterate prime-degree extensions using the prime factors of \(e\). For a single step of degree \(\ell\) over a current field \(K\) of order \(U\), take first \(\ell=p=\operatorname{char}K\). Choose \(a\) of nonzero absolute trace by checking a prime-field basis. If \(x^p-x=a\), iterating the \(p\)-power map gives \(x^U-x=\operatorname{Tr}_{K/\mathbb F_p}a\ne0\). The \(U\)-Frobenius therefore translates the roots by a nonzero element of \(\mathbb F_p\), proving irreducibility of \(X^p-X-a\).

For \(\ell\ne p\), adjoin a nontrivial \(\ell\)-th root of unity using an irreducible factor of \(X^\ell-1\) other than \(X-1\). The resulting \(K'/K\) has degree \(r\mid\ell-1\). Starting with this root of unity as \(c\), repeatedly extract an \(\ell\)-th root in \(K'\) via \(X^\ell-c\) until its order reaches \(\ell^{v_\ell(|K'|-1)}\). Each earlier extraction is possible by cyclicity and increases its order by \(\ell\), regardless of which root is chosen. The final \(c\) is no longer an \(\ell\)-th power. Since \(K'\) contains all \(\ell\)-th roots of unity, its Frobenius permutes the roots of \(X^\ell-c\) via multiplication by one such root. This root of unity is nontrivial since there is no \(K'\)-root, so the permutation is an \(\ell\)-cycle. Adjoin a root and get a field \(L/K\) of degree \(r\ell\le\ell^2\).

The degree-\(\ell\) subfield of \(L\) is the fixed space of \(x\mapsto x^{U^\ell}\), found by linear algebra over \(K\). A basis vector outside \(K\) has degree \(\ell\) over \(K\). Compute its minimal polynomial by linear dependence among its powers. This constructs the desired field using factoring calls of degree at most \(\ell\) and a number of calls polynomial in the intermediate field bit lengths. At the least degree \(d\mid N\), all necessary integer factors come from the supplied factorization of \(N\). Before a step of degree \(\ell\), the cumulative bit dimension is at most \(d\log q/\ell\), so the largest intermediate bit dimension is at most \(B d\log q\). So far the construction gives the time bound with \(B\) the largest prime of \(N\). It suffices in fact to retain the factor
\[
 N_0=\gcd\bigl(N,H^{\lceil\log_2(N+1)\rceil}\bigr),\qquad H=q-1.
\]
Write \(N=N_0N_1\), so \(\gcd(N_1,H)=1\). Replace \(b\) by \(b'=b^{N_1^{-1}\bmod H}\) and solve \(X^{N_0}=b'\). Raising a solution to the original exponent gives \(b\). Theorem 2 shows that the two equations have the same accepting degrees, since \(b'\) has the order of \(b\) and only primes dividing \(H\) enter that theorem. Thus the constructed solution can be used in the original tensor lift. Trial division factors \(N_0\) in time polynomial in \(B,\log N\): stop when the remaining integer is one or the trial divisor squared exceeds it, in which case the remainder is prime. The case \(H=1\) directly has the root one. This proves the bound without an integer factorization supplied and with \(B\) drawn only from \(\gcd(N,q-1)\). For other accepting degrees, their integer prime factors can be supplied or found by trial division in time polynomial in the numerical degree \(e\), consistent with explicit output size. [Shoup, finite-field construction from factoring](https://www.shoup.net/papers/detirred.pdf)

If the factoring oracle requires a single polynomial basis over the prime field, the tower presentations above can be converted without any extra factoring calls. For a field \(L/\mathbb F_p\) of degree \(s\), compute each prime power \(r^a\parallel s\) by integer trial division, and choose
\[
       u_r\in\mathbb F_{p^{r^a}}\setminus\mathbb F_{p^{r^{a-1}}}
\]
using the two Frobenius fixed spaces inside \(L\). Then \(u=\sum_r u_r\) has degree \(s\). Indeed if a Frobenius power fixes \(u\), the differences of the corresponding images of the \(u_r\)'s sum to zero. The difference for \(r\) lies in the intersection of the degree-\(r^a\) subfield and the compositum of the other subfields, hence in \(\mathbb F_p\). Its trace in its degree-\(r^a\) subfield is zero by Frobenius invariance, so it vanishes for \(r\ne p\). The remaining difference also vanishes since all the differences sum to zero. The Frobenius exponent is therefore divisible by every \(r^a\), hence by \(s\). The minimal polynomial of \(u\) and the basis conversion come from linear algebra on its powers. When \(s=1\) the given field is already its prime field. The entire conversion is polynomial in the field bit dimension.

The one-degree membership tests and the minimum-degree classification are unconditional. The explicit arbitrary-characteristic witness bound uses the assumed complete finite-field factoring algorithm. These are written proofs.

Separate finite computations checked 493,950 prime-field power-profile instances and 1,600 cycle-list instances of the covering relation. Those checks are independent of the written proofs.

## 4. Exact subexponential optimization for finite étale tensors

**Proposition 4.** Given the two multiplication tensors of side \(n\) from Theorem 1, the least accepting degree and the complete list of minimal divisibility generators of the profile can both be computed in deterministic time
\[
   \exp\!\left(O\!\left(\sqrt{\frac{n}{\log(n+2)}}\right)\right)
   \operatorname{poly}(n,\log q).
\]
No finite-field factoring is needed.

*Proof.* Let \(M\) be the least common multiple of all cycle lengths from the two field-factor lists. Membership depends on \(e\) only through \(\gcd(e,M)\), since every cycle length \(d\) divides \(M\) and splits according to \(\gcd(e,d)\). The least positive accepting degree is consequently an accepting divisor of \(M\). The divisibility-minimal accepting divisors generate the profile, since extension of scalars preserves isomorphism and every accepted \(e\) has an accepting divisor \(\gcd(e,M)\).

For each prime \(\ell\mid M\), assign its maximal power \(\ell^{\alpha_\ell}\) in \(M\) to one cycle whose length is divisible by that power. For a single cycle, the assigned powers are pairwise coprime, so their product divides the cycle length. Their sum is at most their product when at least two powers are assigned, by repeatedly using \(a+b\le ab\) for integers \(a,b\ge2\). For one assigned power the bound by the cycle length holds directly. Summing over both lists gives
\[
       \sum_{\ell\mid M}\ell^{\alpha_\ell}\le 2n .
\]
If there are \(k\) distinct primes in \(M\), their sum is \(\Omega(k^2\log k)\) for large \(k\). Indeed, at \(x=k\log k/16\), the prime number theorem gives \(\pi(x)\le 2x/\log x\le k/4\) for large \(k\), so at least \(k/2\) of any \(k\) distinct primes exceed \(x\). The preceding sum bound yields \(k^2\log k=O(n)\), and hence \(k=O(\sqrt{n/\log(n+2)})\). For the last inference, split into \(k\le n^{1/4}\) and \(k>n^{1/4}\); in the second case \(\log k>\tfrac14\log n\).

Every maximal prime power divides a cycle length at most \(n\). Therefore primes \(\ell>n^{1/4}\) have \(\alpha_\ell\le3\), while the at most \(n^{1/4}\) smaller primes each have \(\alpha_\ell\le\log_2 n\). It follows that
\[
   \log\tau(M)=\sum_{\ell\mid M}\log(1+\alpha_\ell)
      \le k\log4+n^{1/4}\log(1+\log_2 n)
      =O\!\left(\sqrt{\frac{n}{\log(n+2)}}\right).
\]
Factor the cycle lengths, which are at most \(n\), by an integer sieve or trial division. Then enumerate all divisors of \(M\), testing each by Theorem 1. A pairwise divisibility comparison among accepted divisors gives the minimal generator list. Squaring the number of enumerated divisors leaves the stated exponential order. The case \(n=1\) is immediate. \(\square\) [Prime number theorem](https://arxiv.org/abs/2002.03255)
