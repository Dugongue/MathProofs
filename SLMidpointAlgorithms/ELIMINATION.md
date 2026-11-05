# Exact simultaneous completion for triangular tensor factors

Informal mathematics. This note proves the conditional elimination and shared-completion statements for up to two unfixed factors. It also gives a direct ordinary tensor isomorphism encoding of the eliminated one-factor relation by flagged quotients.

## 1. Tensor words and a shared system

Let F be a field, let V_1, V_2, V_3 be finite-dimensional F-vector spaces with ordered bases, and let X be their tensor product. A factor is an invertible matrix on one mode, acting on X as the identity on the other modes. An unfixed factor ranges either over upper unitriangular matrices or over lower unitriangular matrices in its designated mode. Such a factor is I + Z for Z in a fixed strictly triangular matrix space J. Inversion permutes I + J, because J is nilpotent and the finite geometric series gives its inverse.

Consider a word of these factors mapping A in X to B in X. Leave one factor unfixed and evaluate all other factors. Moving the evaluated products across the equality gives

    (I + Z) A' = B',    Z in J.

This is affine linear in all entries of Z. The equations include the entire tensor. In particular they require one common Z even when the same entries affect many slices.

For two unfixed factors the equation has the form

    P (I + Z_2) Q (I + Z_1) R A = B.

Here P, Q and R are the evaluated intervening products in their original order. Multiplying by the available inverses gives the equivalent equation

    Q (I + Z_1) R A = (I + Y_2) P^(-1) B,    Y_2 in J_2,

where I + Y_2 = (I + Z_2)^(-1). This is one jointly stacked affine linear system in the coordinates of Z_1 and Y_2. The argument works for two occurrences in the same mode, different modes, or different triangular directions. The system can have any rank. Every solution determines valid unitriangular factors, and every original solution appears in the system. Its solution space, when nonempty, is an affine space in the variables Z_1 and Y_2. Mapping Y_2 back to Z_2 need not preserve affine coordinates.

Write the system as M x = b. There are dim(X) equations and at most dim(J_1) + dim(J_2) unknowns. Explicit tensor coefficient construction and elimination cost polynomially many field operations. If the evaluated factors are instead supplied as variables, the same formulas construct the entries of M and b by a polynomial-size straight-line arithmetic circuit. Unitriangular inverses use their finite geometric series. For every specialization of those variables the resulting M x = b has exactly the stated common-completion meaning.

## 2. Conditional consistency over finite fields

Over F_q, the polynomial z(a) = 1 - a^(q-1) is the zero indicator. The polynomial a^(q-2)(1 - z(a)) agrees with inversion at nonzero a and vanishes at zero. This uses exponent zero for q = 2.

Consequently a fixed-size circuit can run full-pivot elimination on all specializations of M and b, including rank drops. At stage k list all entries a_j of the trailing submatrix in one fixed order. The mask

    m_j = (1 - z(a_j)) product_(i < j) z(a_i)

equals 1 exactly for the first nonzero candidate. The no-pivot mask is the product of all z(a_i). Use these masks to combine the candidate row and column permutations, including the identity for the no-pivot case. Exactly one mask equals 1, so the circuit applies one actual permutation. The masked inverse then gives the multipliers for clearing below the pivot. A no-pivot stage leaves the rows unchanged and cannot be followed by a successful pivot because the trailing matrix was zero. Keep track of the permutations of the unknowns and apply the same row operations to b.

The output test requires each transformed right-hand-side entry in a zero row to vanish. One can use the product of the corresponding masked zero indicators. The same circuit can give a solution whenever the test passes. Set free entries to zero, solve the pivot equations by masked back substitution, and undo the column permutations. The masks and tracked permutations are circuit values, so neither the circuit nor the selected decoder uses a list of rank profiles. The number of arithmetic gates is polynomial in the dimensions and log(q), using repeated squaring for the powers. For an explicitly presented finite field whose arithmetic has polynomial bit cost in its presentation length, this gives a polynomial-size bit implementation as well.

This proves conditional consistency and common completion in an arithmetic-circuit representation. Its remaining free inputs are the factors which were not eliminated. To decide whether some values of those inputs make the circuit accept requires a separate argument.

## 3. A division-free coefficient test over every field

For an m by n matrix M put D_m(t) = diag(t^1,...,t^m) and D_n(t) = diag(t^1,...,t^n). Define

    C_M(s,t) = det(I_n + s D_n(t) M^T D_m(t) M).

The degree in s of C_M is exactly rank(M) over every field, including characteristic two. The coefficient of s^k is the Cauchy–Binet sum

    sum_(|I|=|J|=k) t^(sum(I) + sum(J)) det(M[I,J])^2,

where I and J range over row and column sets. No coefficient of s^k for k above r = rank(M) can be nonzero.

At k = r every row basis pairs with every column basis to give a nonsingular minor, and these are the only nonzero minors of that size. For example, factor M = P Q with P of full column rank r and Q of full row rank r. A row basis of M is exactly a set I for which P[I,:] is invertible, and the analogous column condition is invertibility of Q[:,J]. The determinant of M[I,J] is then the product of those two nonzero determinants.

Among row bases there is a unique minimum weight basis with weight sum(I). Greedily take independent rows in index order. The j-th index chosen by greedy is at most the j-th index of any basis, because the rank of the prefix ending at the latter index is at least j. If the bases differ, one of the coordinate inequalities is strict. The same argument holds for column bases. Therefore the unique pair of minimum total weight among the nonzero r-minors contributes a nonzero square to its t-coefficient. No other pair can cancel it. For r = 0 the constant coefficient already gives the result.

The t-degree is at most (m+n) min(m,n). Computing the coefficient array is polynomial in m and n using addition and multiplication over F. For a self-contained procedure, work in the truncated polynomial ring with s-degree at most n and t-degree at most (m+n) min(m,n). The input matrix of the determinant is the identity modulo s. Gaussian elimination without pivoting keeps every successive pivot congruent to 1 modulo s, so its inverse in this ring is the finite geometric series in 1 minus that pivot. The product of the pivots gives the determinant coefficient array. Truncation is exact for the claimed output since the determinant satisfies both degree bounds. This computes the array by a fixed circuit even when the entries of M are themselves circuit inputs.

Apply this to M and to its augmentation [M | b]. Equality of the two degrees in s is equivalent to consistency. One can also encode equality by requiring for every k that the statement “some coefficient at s-degree at least k is nonzero” have the same truth value for both arrays. This is a polynomial-size Boolean combination of explicit coefficient zero tests over F, without assumptions on the specialized rank. The weighted determinant idea is related to Mulmuley's rank method. The proof above establishes the specific rectangular coefficient formula used here. [Mulmuley, 1987](https://doi.org/10.1007/BF02579205)

## 4. Eliminating one factor into ordinary TI

The one-factor elimination has a stronger representation when the remaining action is a product of independent linear maps on the other two modes. For definiteness eliminate a lower unitriangular factor on V_1, and write the input tensors as rows a_j and b_j in W = V_2 tensor V_3. Write A_j = span(a_1,...,a_j) and B_j = span(b_1,...,b_j), with A_0 = B_0 = 0. Let h = h_2 tensor h_3 act on W. The two statements below are equivalent.

1. There is a lower unitriangular l on V_1 with (l tensor h) A = B.
2. For every j, h(A_j) = B_j and the induced map W/A_(j-1) -> W/B_(j-1) sends a_j + A_(j-1) to b_j + B_(j-1).

Indeed, the j-th row equation is b_j = h(a_j) plus a linear combination of h(a_i) for i < j. The row equations through j give h(A_j) = B_j because the leading principal part of l is invertible. Conversely the quotient equality gives coefficients for row j from the span of the previous transformed rows. These choices can be made independently for the different rows of l. All slices of each row use those same coefficients. No row independence is required. For upper unitriangular l, reverse the row order.

For each input, compute its flag spaces, quotient spaces and the marked classes. Encode the quotient maps from W and the marked quotient vectors in a typed tensor system. An invertible map on W preserves the quotient-map component exactly when it takes the kernel to the target kernel, and then the induced map on each quotient is forced. Encode the canonical bilinear map V_2 x V_3 -> W. Its component forces the map on W to equal h_2 tensor h_3. Encode marked vectors by maps from a fixed scalar sort. If h_2 or h_3 are to range over a given unitriangular group, include the existing triangular-algebra controller on that mode. If neither restriction is needed, use unrestricted invertible maps on both modes. Unequal corresponding quotient dimensions reject immediately. Zero-dimensional sorts can be omitted, since their maps and marked vectors are forced.

The number of spaces and components and their dense dimensions are polynomial in the input dimensions, and all components have order at most three. The existing uniform typed-system packing and the ordinary-TI compiler give a same-field polynomial many-one reduction for this class. A quotient encoding can be reused with additional constraints on h_2 and h_3 whenever those constraints are already expressed by typed tensor components. [Fixed-component tensor-system compiler, Theorem 4.1](https://arxiv.org/html/2306.03135v2)

The two-factor arithmetic completion theorem retains a common solution across all slices without enumerating possible ranks. The quotient construction gives an ordinary-TI test for one triangular factor and independently controlled remaining modes. A four-layer reduction still needs an ordinary-TI encoding of the residual shared midpoint when the two opposite-direction halves remain simultaneously unfixed.
