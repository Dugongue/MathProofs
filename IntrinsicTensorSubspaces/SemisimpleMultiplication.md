# Determinant profiles for raw semisimple multiplication tensors

**Theorem.** Fix a finite field F. For raw three-mode tensors promised to be isotopic to the multiplication tensors of finite-dimensional semisimple associative F-algebras, the full determinant profile can be computed in Las Vegas polynomial bit time. The algorithm also decides whether the ordinary transporter set is empty under this promise. It requires neither supplied isotopies nor invariant projective points. For F of size three, this gives an exact randomized polynomial-time SL-TI algorithm on this family.

The algorithm handles products of noncommutative matrix algebras of arbitrary degrees and centers. It uses the safe degree extension descent from the preceding work and the constructive finite-field Wedderburn algorithm. The randomized time is expected polynomial and the output is always correct.

## Work over a large safe extension

Choose E over F of polynomial degree e as in the safe extension theorem so that the norm determinant profile upstairs, followed by the inverse e-th power map on F×, is the original determinant profile. Choose the degree also large enough that |E|>4N, where N is the mode dimension. Choosing another power of the same safe prime suffices. All three dimensions agree by the semisimple multiplication promise. Formats with unequal corresponding dimensions are rejected. The rest of the argument computes the norm profile over E without enumerating E. [Safe extension descent](https://github.com/Dugongue/MathProofs/blob/main/TensorSignSearchSpace/Extensions.md)

Write the input in bilinear form T:U×V→W. For x∈U and y∈V write L_x(v)=T(x,v) and R_y(u)=T(u,y). By the hidden algebra multiplication, each of det L_x and det R_y is a nonzero polynomial of degree N. Choose u and v uniformly and independently until both L_u and R_v are invertible. Each determinant test is exact and each trial succeeds with probability at least 1−N/|E|. Define the multiplication on W by

    a * b = T(R_v⁻¹a,L_u⁻¹b).

Under any hidden isotope coordinates, T is usual multiplication, and the chosen u and v identify with units there. In those coordinates the displayed product is a (uv)⁻¹ b, associative and unital with identity uv. The isomorphism to the hidden algebra is a↦(uv)⁻¹a. Thus (R_v,L_u,I) is an explicit transporter from the raw tensor to multiplication in a semisimple E-algebra. Apply this method to both inputs. Associativity and the claimed identity can also be checked directly on the output table.

## Obtain one reference transporter

Use the constructive algorithm of Eberly and Giesbrecht to obtain an explicit Wedderburn isomorphism for each algebra. Their algorithm accepts a matrix representation. The left regular representation is faithful because the algebra is unital, and a structure-constant table supplies generating matrices by left multiplication by its basis. The random finite-field operations and polynomial factoring give Las Vegas polynomial bit time. [Eberly and Giesbrecht, Efficient Decomposition of Associative Algebras over Finite Fields](https://www.sciencedirect.com/science/article/pii/S0747717199903085)

The simple factors have formats M_m(K), with K a finite extension of E. The type of a factor is the pair (m,[K:E]). Match the two lists by these types. If the multiplicities differ, there is no ordinary transporter. Indeed an isotopy between unital associative algebras yields an algebra isomorphism by evaluating on the two unit arguments, as shown below. When they agree, explicit isomorphisms of the center fields are found by factoring one defining polynomial over the other field and choosing a root. This gives an actual ordinary transporter for the original tensors, by composing the decompositions, their factor matching and the two input identifications. Compute the norms of its three physical determinants by fast exponentiation.

## Compute all corrections without automorphism search

For any unital associative algebra A, an autotopism satisfies F(x)G(y)=H(xy). Set a=F(1) and b=G(1). The relations H=R_b F=L_a G make a and b units. In a finite-dimensional unital algebra, surjectivity of left or right multiplication gives a one-sided inverse, and finite dimensionality gives the other inverse. Then α=L_a⁻¹ R_b⁻¹ H preserves the unit and multiplication. Conversely all triples

    (L_a α, R_b α, L_a R_b α)

are autotopisms, for arbitrary units a,b and algebra automorphism α. The same proof for an isotopy from one algebra to another makes α an algebra isomorphism between the two.

On M_m(K), the left multiplication determinant over E is N_(K/E)(det_K a)^m, since left multiplication acts on each of m columns. The same formula holds on the right by rows. After taking the norm to F, the values range exactly over the m-th powers in F×, by surjectivity of the field norm and the matrix determinant. Across factors, generate a subgroup D of F× from these power images. This handles units in both input modes. The two choices of unit are independent.

An E-algebra automorphism of a product permutes isomorphic simple factors and restricts to a semilinear algebra automorphism on each. Indeed it permutes the primitive central idempotents. On a simple factor its restriction to the center is a power of Frobenius. After removing this action it is inner by Skolem–Noether. Inner conjugation has determinant 1, by the left and right formulas with reciprocal units. The entrywise Frobenius generator on M_m(K) has determinant (−1)^(m²([K:E]−1)), by using a normal basis in K. Swapping a pair of equal simple factors contributes (−1)^(m²[K:E]), with identical block coordinates. Norm these signs to F and generate a subgroup C of F× from the resulting signs for all available generators. This accounts for every algebra automorphism and each generator is realized.

Thus the exact norm determinant image of the stabilizer in bilinear-map convention is

    { (x d, y d, x y d) : x,y∈D, d∈C }.

Multiply by the reference norm tuple and invert the e-th power on F× to recover the complete base profile. If the tensor is written as an element of a triple tensor product, dualize the two inputs and reciprocate their determinants. Over the field of three elements this does not change the signs.

The matrix multiplication example that forces exponentially many projective points is covered by this theorem, as are products of simple factors whose eigenlines cannot be used to construct spanning lists. Arbitrary raw tensors need not be semisimple multiplication isotopes. This is an informal exact algorithm for the promised class, and priority for the determinant-profile calculation has not been established.
