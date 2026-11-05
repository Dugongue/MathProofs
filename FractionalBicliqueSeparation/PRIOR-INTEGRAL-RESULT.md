# ALREADY SOLVED: INTEGRAL BINARY-RANK MULTIPLICATIVITY IS FALSE

Credit: Yaroslav Shitov, July 25, 2026. NOT OUR DISCOVERY.

The author-uploaded preprint Factoring Kronecker squares of nonnegative matrices with GPT-5.6 Sol, Theorem 1, gives

 B=[11001;01100;00111;10010;11111], r_b(B)=5, r_b(B tensor B)<=24.

We independently checked the transcribed 24 rectangles in SHITOV-CERTIFICATE.json: they partition all 225 ones exactly, with no overlap or zero entries.

The lower bound is exact. B has real rank 4: lambda=(1,1,1,1,-2) annihilates it, and rows 0,1,2,3 / columns 0,1,2,4 have determinant -2. In a hypothetical binary factorization B=P Q of inner dimension 4, lambda P=0 because Q has full row rank. Every nonzero column of P must consequently have its bottom entry one and exactly two other ones. All columns of B sum to 3, so every Q column has exactly one one. Five distinct B columns cannot come from four unit Q columns. Thus r_b(B)>=5; partitioning by rows gives equality.

Primary source and full certificate:
https://www.researchgate.net/publication/410803878_Factoring_Kronecker_squares_of_nonnegative_matrices_with_GPT-56_Sol
DOI 10.13140/RG.2.2.26449.90723, Section 3 and page 4.

This credited result refutes Conjecture 1 of Ghosal--Karrenbauer SEA 2025. It is separate from our new informal fractional-asymptotic separation proof.
