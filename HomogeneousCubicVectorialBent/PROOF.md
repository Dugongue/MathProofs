# A Homogeneous Cubic Vectorial Bent Function in Ten Variables

**Status:** AI-assisted informal proof; separate AI-worker review and exact finite checks where supplied. No Lean certificate; independent human review and publication-priority assessment remain pending.


Result and scope (31 October 2026)
There exists a binary homogeneous cubic vectorial bent function H: F_2^10 -> F_2^2. Every one of its three nonzero components is homogeneous of degree 3. Consequently nonquadratic homogeneous vectorial bent functions exist, answering the existential question in Alexandr Polujan's 2021 dissertation, Open Problem 4.31, affirmatively. This is an informal proof with independently audited exact finite certificates, not a Lean formalization. We have not established publication priority; no assertion that later literature has not already answered the question is intended.

Original question and exact hypotheses
Alexandr Polujan, Boolean and Vectorial Functions: A Design-Theoretic Point of View, 2021, printed p. 123, Open Problem 4.31: "Do non-quadratic homogeneous vectorial bent functions exist?"
Primary public copies:
https://d-nb.info/1239811446/34
https://files01.core.ac.uk/download/pdf/619981175.pdf
SHA-256: bf7ce72cc515ef9c7f8f10e905f9c55f71732352a83e4f17e7f11a3bc6801541
The question is on PDF page 141. Its preceding paragraph on printed p. 122 defines homogeneous vectorial maps coordinatewise. The general coordinatewise ANF and homogeneity definitions also occur on PDF page 22. The observations about dimensions 6 and 8 motivate the unrestricted existence question; they do not restrict the question's dimension. There is no requirement to be outside the completed Maiorana-McFarland class. All three components of our function meet the stronger property of being nonzero homogeneous cubics. The original dissertation is linked above; its pages are cited rather than redistributed here.

## 1. Encoding
All additions below are over F_2. Let K = F_2[t]/(t^5 + t^2 + 1), and let alpha be the class of t. Encode a K element by an integer in 0,...,31, whose five bits are its coefficients in the basis 1,t,t^2,t^3,t^4. The modulus is encoded by 37. The modulus has no roots in F_2 and has remainder 1 on division by the unique irreducible quadratic t^2+t+1, so it is irreducible of degree 5. Let Tr: K -> F_2 be the absolute trace.
Encode (x,y) in K^2 by x + 32 y, using XOR as vector addition. For a five-bit mask M, let y^M be the product of those y coordinates whose bits in M are 1. Put
    G_0 = {5,6,10,11,19,21,24,25,26,28},
    G_1 = {3,5,6,9,10,11,13,20,21,22,25,28},
    g_i(y) = sum_(M in G_i) y^M.
Every mask here has weight 2 or 3. Define
    F_0(x,y) = Tr(xy) + g_0(y),
    F_1(x,y) = Tr(alpha xy) + g_1(y),
and F=(F_0,F_1), encoded by F_0 + 2 F_1.

## 2. Analytic bentness of the seed
For each (a,b) in F_2^2 minus {(0,0)}, let k=a+b alpha. This k is nonzero. The corresponding component is
    f_(a,b)(x,y)=Tr(kxy)+a g_0(y)+b g_1(y).
Every additive character of K^2 has the form (-1)^(Tr(ux)+Tr(vy)). Indeed the trace pairing is nondegenerate: Tr(1)=1, and multiplication by any nonzero field element is bijective. Its Walsh coefficient at (u,v) is therefore
    sum_y (-1)^(a g_0(y)+b g_1(y)+Tr(vy)) sum_x (-1)^Tr((ky+u)x).
The inner sum is 32 if y=k^(-1)u, and zero otherwise. Every Walsh coefficient consequently equals 32 or -32. This proves all three seed components bent, without reliance on a spectral search.

## 3. The explicit change of coordinates
Let B be the binary 10 by 10 matrix with columns encoded by
    [476,281,675,391,383,210,668,844,790,932].
Its inverse has columns
    [393,95,877,940,664,971,235,524,191,21].
The identity of these two binary matrix products is a small direct certificate of invertibility. Let b_j be column j, with j=0,...,9. Their encoded F values are
    [2,0,1,1,3,2,1,3,0,1].
Define the binary linear output correction
    L(u)=sum_(j=0)^9 u_j F(b_j),
and the required map
    H(u)=F(Bu)+L(u).
WITNESS.json gives the seed masks and B; ALGEBRAIC-CERTIFICATE.json gives B, its inverse and the correction constants. Thus the map is specified without any black-box oracle, equivalence-class choice or existence assumption.

## 4. Homogeneity
The seed F has algebraic degree at most 3, so F composed with a linear map and then added to a linear function still has degree at most 3. We have H(0)=0 and H(e_j)=0 for every standard basis vector. Direct substitution into the explicit field formulas gives
    F(b_i+b_j)+F(b_i)+F(b_j)=0 in F_2^2
for all 45 pairs 0 <= i < j < 10; all 45 encoded residuals are recorded as zero in ALGEBRAIC-CERTIFICATE.json. The correction L has zero second difference, so H(e_i+e_j)=0 as well.
For a Boolean ANF, the constant coefficient is H(0), each linear coefficient is H(e_j)+H(0), and each quadratic coefficient is H(e_i+e_j)+H(e_i)+H(e_j)+H(0). Hence all ANF coefficients of degrees 0,1,2 vanish. Since no degree above 3 is possible, both coordinates of H consist exclusively of cubic monomials. Their complete monomial lists have respectively 67 and 66 terms, and their sum has 61 terms. ANF.json records all three exact lists, with zero-based variable masks. In particular none of the three components is zero and each has degree exactly 3.

## 5. Bentness after the coordinate change
Composing a Boolean bent function with an invertible binary linear map permutes its character-indexed Walsh coefficients. Adding a binary linear function also permutes those coefficients. For each nonzero output selector, H's selected component is obtained from the bent seed component by exactly these operations. Therefore every selected component is bent and H is a homogeneous cubic (10,2)-bent function. This completes the full unrestricted existential question.

## 6. Infinite family
For every positive integer q, define H^[q] on q disjoint ten-variable blocks by the componentwise sum of q copies of H. Each nonzero scalar component is a direct sum of q homogeneous cubic bent functions, so its Walsh transform factors into q factors of magnitude 32. The result is a homogeneous cubic (10q,2)-bent function. Thus existence holds in infinitely many input dimensions, as an immediate consequence of the finite witness.

## 7. Independent verification and proof origins
The discovery search used the existing vectorial Maiorana-McFarland template. For prescribed y-projections of ten prospective basis directions, the 50 unknown x-projection bits and 40 unknown quadratic/cubic seed coefficients obey 90 homogeneous binary linear constraints expressing the two output coordinates of the 45 vanishing second differences. Exact nullspace sampling found the displayed invertible basis at trial 52,976. This is a discovery method, not a universal guarantee or exhaustive classification.
The worker's verify.py reconstructs all 1,024 truth values, computes the full ANF by the subset transform, and computes every Walsh coefficient of all three components by an integer butterfly transform. It checks invertibility, homogeneous degree exactly 3 and Walsh magnitude exactly 32. A separate reviewing AI worker independently reconstructed every value using different field long division, directly computed subset-sum ANF coefficients, and directly summed all 3 x 1,024 x 1,024 character terms, with no butterfly transform. The independent report gives 528 Walsh values +32 and 496 values -32 for each component. This agrees with H(0)=0. The separate reviewing worker used the direct-sum verifier provided as verify_independent.py; its receipt is INDEPENDENT-CHECKS.json.
Truth table bytes SHA-256:
    17b135009c51e340728ffa4810eccfc07f5e626995d312775a58232fdae20f4c
The exact finite certificate supplements the analytic proof; no random oracle, unverified floating-point calculation or external solver is part of the conclusion.

## 8. Prior-work and novelty limits
The shared notes catalog returned 45 homogeneous/vectorial hits and 15 OP 4.31/bent hits. The September 2026 archive explicitly records OP 4.31 as unresolved and identifies (10,2) as the next constructive target. Its older classification and spread-law results concern quadratic functions and do not include this cubic witness. The live indexed declaration searches for homogeneous/vectorial and homogeneous/bent returned no matching declarations; this is a search receipt, not a proof that no synonymous result exists elsewhere. These were bounded searches of the project catalog, not an exhaustive priority certificate.
Focused public searches for binary homogeneous vectorial, homogeneous cubic vectorial bent and the precise OP 4.31 wording found the original thesis and neighbouring Boolean constructions, but no prior explicit closure. Fengrong Zhang, Enes Pasalic, Amar Bapic and Baocang Wang, Constructions of several special classes of cubic bent functions outside the completed Maiorana-McFarland class, Information and Computation 297 (2024), 105149, https://doi.org/10.1016/j.ic.2024.105149, solves a distinct Boolean homogeneous/nondecomposable problem. Odd-prime notions of homogeneous or ternary vectorial cubic bent functions are different definitions and are not evidence for or against binary ANF homogeneity. Publication priority remains unverified. We credit the established Maiorana-McFarland bentness construction and Polujan's question rather than claiming either underlying concept as new. The specific witness and simultaneous-homogenization search were produced during this session.
