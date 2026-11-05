# Central Rectangular Kronecker Asymptotics
Informal proof candidate, November 4, 2026.
No Lean certificate. Publication priority is not established.

THEOREM

For each positive integer m let

  lambda_m = (ceil(m^2/2), floor(m^2/2)),
  G_m = g((m^m),(m^m),lambda_m).

As m tends to infinity through the positive integers,

  G_m = (3 sqrt(3)/pi) (1 + 1_{m odd}) 4^m m^(-5) (1+o(1)).       (T)

Thus the even subsequence has leading constant 3 sqrt(3)/pi, and the
odd subsequence has leading constant 6 sqrt(3)/pi. This is an asymptotic
equivalence for the exact family in Panova's Open Problem 6.13; it is
not a statement only away from the center or only for one parity.

The proof first forms the adjacent coefficient difference exactly and then
analyzes its Fourier integral. It never subtracts two independently rounded
or insufficiently accurate local central limit estimates.

## 1. THE CLASSICAL RECTANGULAR IDENTITY

Let p_r(m) count partitions of r fitting in an m by m rectangle; set
p_{-1}(m)=0. The classical two-row rectangular Kronecker identity is

  g((m^m),(m^m),(m^2-r,r)) = p_r(m)-p_{r-1}(m),
                        0 <= r <= floor(m^2/2).                  (1)

This identity and the target question are stated in Panova, Complexity and
asymptotics of structure constants, Section 6.3. It is credited there to
Pak and Panova; it is not a new identity of this work.

For completeness its representation-theoretic reduction is short. The
permutation character on r-subsets decomposes multiplicity-freely into
the characters (m^2-j,j), 0 <= j <= r. Frobenius reciprocity and restriction
of the rectangular character therefore identify the sum of these Kronecker
multiplicities with

  sum_{alpha partition m^2-r, beta partition r} (c^rect_{alpha,beta})^2.

The rectangle represents det^m for GL_m. Such a Littlewood-Richardson
coefficient is one exactly when beta is the rotated rectangle-complement of
alpha, and zero otherwise: its multiplicity is the multiplicity of V_beta
in det^m tensor V_alpha^*, an irreducible representation. Consequently the
sum is p_r(m). Subtracting the analogous equality at r-1 gives (1).

Set r=floor(m^2/2). It remains to estimate D_m=p_r(m)-p_{r-1}(m).

## 2. A DENOMINATOR-FREE EXACT INTEGRAL

For an m-element subset {j_1<...<j_m} of {1,...,2m}, the integer

                    sum_l j_l - m(m+1)/2

is the area of a partition inside the rectangle. Indeed the nondecreasing
integers j_l-l lie between 0 and m; reverse them to obtain its row lengths.
This is a bijection, with the displayed area preserved.

Thus p_r(m) counts subsets with cardinality m and element sum
T_r=r+m(m+1)/2. Equivalently, if B_1,...,B_{2m} are independent fair
Bernoulli variables, then

  p_r(m) = 4^m Pr[sum B_j=m, sum j B_j=T_r].

Integer Fourier inversion gives the same count as the integral of

  exp(-i m s-i T_r t) product_{j=1}^{2m}(1+exp(i(s+j t)))

over s,t in [-pi,pi], divided by (2pi)^2. Expanding
1+exp(iu)=2 exp(iu/2) cos(u/2) cancels the entire s-phase. The t-phase
becomes exp(-i(r-m^2/2)t).

Write c=(2m+1)/2, j'=j-c, and put a=s+c t. Define

  F_m(a,t)=product_{j=1}^{2m} cos((a+j' t)/2).

For each fixed t this is 2pi-periodic in a: translating a by 2pi changes
the sign of 2m cosine factors, so leaves the product unchanged. The
shifted integration interval can therefore be returned to [-pi,pi].
The multiset of j' is symmetric about zero, so F_m is even in a and in t.

Let epsilon_m=m^2/2-floor(m^2/2), equal to 0 for even m and 1/2 for odd m.
Subtract the two integrals BEFORE any approximation. Their imaginary parts
integrate to zero, giving exactly

  D_m = 4^m/(2pi)^2 integral integral w_m(t) F_m(a,t) da dt,         (2)

where the integrals range over [-pi,pi]^2 and

  w_m(t)=cos(epsilon_m t)-cos((epsilon_m+1)t).

Put b_m=epsilon_m+1/2, hence b_m=1/2 or 1. In both cases

  w_m(t)=b_m t^2+O(t^4),       |w_m(t)| <= b_m t^2.                (3)

The second bound holds for all real t: use
2 sin((2epsilon_m+1)t/2) sin(t/2) and |sin x|<=|x|. No parity lattice
has been discarded; the parity dependence is precisely retained in w_m.

## 3. GLOBAL TAIL BOUNDS: THERE ARE NO OTHER CONTRIBUTING PEAKS

For real u, |cos u| <= exp(-sin^2(u)/2). Therefore

  |F_m(a,t)| <= exp(-S_m(a,t)/2),
  S_m(a,t)=sum_{j=1}^{2m} sin^2((a+j't)/2).

The finite geometric sum yields

  S_m(a,t)=m-C_m(t) cos a,
  C_m(t)=sin(mt)/(2 sin(t/2)),          C_m(0)=m.                  (4)

These identities are exact, including the half-integer values of j'.

First suppose |t|<=1/m and |a|<=pi. Each |j't|<=1, so
C_m(t) >= m cos(1). Also, using 1-cos x >= 2x^2/pi^2 for |x|<=pi,

  m-C_m(t) = (1/2) sum_j (1-cos(j't))
      >= (t^2/pi^2) sum_j (j')^2
       = m(4m^2-1)t^2/(6pi^2)
      >= m^3 t^2/(2pi^2).

Combining (4) with 1-cos a >= 2a^2/pi^2 gives

  S_m(a,t) >= m^3 t^2/(2pi^2) + 2m cos(1) a^2/pi^2.

In particular, with the absolute constant gamma=1/(4pi^2),

  |F_m(a,t)| <= exp(-gamma(m a^2+m^3 t^2)),   |t|<=1/m.          (5)

For the rest of the torus suppose m>=4. If 1/m<=|t|<=4/m, set x=m|t|.
On [1,4] one has |sin x|/x<=sin(1): the positive sinc is decreasing up
to pi, and beyond pi the bound 1/pi is enough. As |t|<=1,

  2 sin(|t|/2)/|t| >= 1-t^2/24 >= 23/24.

Consequently |C_m(t)|/m <= (24/23)sin(1) < 9/10. If instead
4/m<=|t|<=pi, use sin(|t|/2)>=|t|/pi to obtain

  |C_m(t)| <= pi/(2|t|) <= pi m/8 < 9m/10.

Thus S_m(a,t)>=m/10 throughout |t|>=1/m, uniformly in a. Hence

  |F_m(a,t)| <= exp(-m/20),               1/m<=|t|<=pi.           (6)

The contribution of this region to D_m/4^m is O(exp(-m/20)), by (2)
and the bounded weight. Multiplication by m^5 still sends it to zero.
In particular there is no unaccounted root-of-unity saddle of comparable
size, a common danger when analyzing a q-binomial as a rational product.

## 4. THE WEIGHTED GAUSSIAN LIMIT

On the remaining strip |t|<=1/m set

                       a=x/sqrt(m),   t=y/m^(3/2).

The Jacobian is m^(-2). For each fixed real x,y, eventually all cosine
arguments are small and positive. The Taylor expansion
log cos u=-u^2/2+O(u^4) gives

  log F_m(x/sqrt(m),y/m^(3/2))
    = -(1/8) sum_j (x/sqrt(m)+j'y/m^(3/2))^2 + O_{x,y}(1/m)
    = -x^2/4 -(4m^2-1)y^2/(48m^2) + O_{x,y}(1/m).

Here sum_j j'=0 and sum_j(j')^2=m(4m^2-1)/6; the fourth-power
sum is O_{x,y}(1/m). Therefore

  F_m(x/sqrt(m),y/m^(3/2)) -> exp(-x^2/4-y^2/12).                (7)

Equation (3) supplies

  m^3 w_m(y/m^(3/2))/b_m -> y^2,
  |m^3 w_m(y/m^(3/2))/b_m| <= y^2.                              (8)

The first convergence is valid along the full sequence because epsilon_m
takes only two values and the Taylor remainder is uniform over them.

Extend the rescaled strip integrand by zero outside
|x|<=pi sqrt(m), |y|<=sqrt(m). By (5), (8) its absolute value is at most

                           y^2 exp(-gamma(x^2+y^2)),

an integrable function on R^2. Thus dominated convergence applies to
the exact DIFFERENCE integral, with no subtractive error estimate needed.
Equations (2), (6)-(8) imply

  lim_{m->infinity} m^5 D_m/(b_m 4^m)
      = 1/(2pi)^2 integral_R integral_R
                       y^2 exp(-x^2/4-y^2/12) dx dy.

The two Gaussian integrals are

  integral exp(-x^2/4) dx = 2 sqrt(pi),
  integral y^2 exp(-y^2/12) dy = 12 sqrt(3pi).

Their product divided by (2pi)^2 is 6 sqrt(3)/pi. Consequently

  D_m = (6 sqrt(3)/pi) b_m 4^m m^(-5) (1+o(1)).                  (9)

As b_m=(1+1_{m odd})/2, (1) and (9) give (T). This completes the
informal argument for the full stated square-central family.

## 5. INDEPENDENT CONSTANT CHECK AND EXACT DIAGNOSTICS

For a uniform m-subset of {1,...,2m}, its element sum has variance
sigma_m^2=m^2(2m+1)/12 and the total number of subsets is binom(2m,m).
The Gaussian heuristic for the central adjacent difference is

  binom(2m,m) b_m/(sqrt(2pi) sigma_m^3).

Using Stirling and sigma_m^2~m^3/6 recovers exactly
(6 sqrt(3)/pi)b_m 4^m/m^5. This paragraph is only a constant check:
the rigorous difference and tail estimates were given in Sections 2-4.

The accompanying checks.py verifies the subset identity independently by
enumeration for m<=8, computes exact central q-binomial coefficients with
integer arithmetic at selected m through 241, and checks the displayed
tail inequalities on 16,605 deterministic grid points. At m=240 and 241,
the exact-to-leading-term ratios are approximately 0.991697 and 0.991731.
These computations corroborate the parity and constant; they are not the
universal asymptotic proof or a novelty certificate.

## 6. SOURCE SCOPE AND PRIORITY

Panova's Open Problem 6.13 asks for precisely the family in (T). The
off-center result cited immediately before it explicitly excludes the
central cancellation regime. Our proof addresses that regime directly.
It gives a leading constant and a relative error tending to zero; it
does not claim an explicit optimal remainder, a general Kronecker
coefficient algorithm, or a VP-versus-VNP separation.

Classical input and target:
Greta Panova, Complexity and asymptotics of structure constants,
arXiv:2305.02553, Section 6.3, identity and Open Problem 6.13.
https://arxiv.org/html/2305.02553

Related off-center asymptotics, credited rather than claimed here:
Stephen Melczer, Greta Panova and Robin Pemantle, Counting partitions
inside a rectangle, SIAM J. Discrete Math. 34 (2020), 2388-2410.
https://arxiv.org/abs/1805.08375
https://doi.org/10.1137/20M1315828

Prior work on q-binomial limit laws, subset sums and higher-order local
expansions may already imply or state (T). A bounded search cannot settle
publication priority. The present packet records the proof independently;
claims of first discovery await a dedicated literature and external audit.


APPENDIX: FIRST RELATIVE CORRECTION AND NEAR-CENTRAL WINDOW

FIRST RELATIVE CORRECTION TO THE CENTRAL ASYMPTOTIC
Informal extension of the main proof above, November 4, 2026.
Not Lean verified. Priority unestablished.

THEOREM

With exactly the notation of the main proof above,

  G_m = (3 sqrt(3)/pi)(1+1_{m odd}) 4^m/m^5
                        times (1-2/m+O(m^(-2))).                 (R)

The implied constant can be absolute and applies to both parities.

PROOF

Use the exact weighted integral and its global tail bounds from Sections
2 and 3 of the main proof above. Put a=x/sqrt(m), t=y/m^(3/2), b=b_m. In the rescaled
integral discard |x|+|y|>m^(1/16). Equation (5) bounds its contribution by
a Gaussian tail, smaller than every negative power of m. The already
discarded region |t|>1/m is exponentially small by (6).

On |x|+|y|<=m^(1/16), Taylor expansion with a uniform remainder gives

  log F_m(x/sqrt(m),y/m^(3/2))
   = -x^2/4-y^2/12 - Q(x,y)/m + E_m(x,y),

  Q(x,y)=x^4/96+x^2 y^2/48+y^4/480,
  |E_m(x,y)| <= C/m^2 [y^2+(|x|+|y|)^6+(|x|+|y|)^4].

To check this explicitly, the quadratic sum contributes the correction
y^2/(48m^2). The fourth-power sum in log cos(z/2)=-z^2/8-z^4/192+O(z^6)
has leading terms

  sum_j (a+j't)^4 = [2x^4+4x^2 y^2+(2/5)y^4]/m
                          +O((|x|+|y|)^4/m^3).

Here sum(j')^4=m(4m^2-1)(12m^2-7)/120, and
sum |a+j't|^6 <= C(|x|+|y|)^6/m^2. These establish the displayed bound.

On the chosen region Q/m and E_m are bounded and tend uniformly to zero.
The elementary exponential remainder estimate therefore gives

  F_m = exp(-x^2/4-y^2/12)
            times [1-Q/m+O(P(x,y)/m^2)],

for a fixed polynomial bound P in |x|,|y|, independently of m. For example
one can take a sufficiently large constant times
1+y^2+(|x|+|y|)^6+(|x|+|y|)^8. Each such error is integrable against
the displayed Gaussian, with an integral bounded independently of m.

The exact weight has

  m^3 w_m(y/m^(3/2))/b_m = y^2+O(y^4/m^3),

uniformly in the two possible parities. Thus it contributes no correction
of relative order 1/m. Divide the weighted integral by its leading Gaussian
moment. Its relative correction is -E[Q]/m, where X has density proportional
to exp(-x^2/4) and Y has density proportional to y^2 exp(-y^2/12),
independently. Their moments are

  E[X^2]=2, E[X^4]=12, E[Y^2]=18, E[Y^4]=540.

Hence

  E[Q] = 12/96+(2*18)/48+540/480 = 1/8+3/4+9/8 = 2.

The integrated remainder is O(m^(-2)). The omitted Gaussian tails are
smaller still. Combining with the exact normalization in the main proof above gives
(R), uniformly over both parity subsequences.

NEAR-CENTRAL CONSEQUENCE

There is also a direct uniform window extension of the leading term. If
r_m is an integer with 0<=r_m<=floor(m^2/2), put
h_m=m^2/2-r_m. Whenever h_m=o(m^(3/2)), the same proof gives

  g((m^m),(m^m),(m^2-r_m,r_m))
       ~ (6 sqrt(3)/pi)(h_m+1/2) 4^m/m^5.

Indeed replace the exact weight by cos(h_m t)-cos((h_m+1)t). Dividing
by h_m+1/2 still bounds its absolute value by t^2, while its rescaled
weight tends to y^2 because h_m/m^(3/2)->0. The same integrable bound
and dominated convergence apply. This extension is not needed to answer
the central source question and does not assert the two-term correction
uniformly for growing h_m.
