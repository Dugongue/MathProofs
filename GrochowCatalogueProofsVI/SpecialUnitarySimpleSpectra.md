# Exact special-unitary tensor transport on split simple spectra

## GP-0274

Let $K=\mathbb F_{q^2}$ with involution $\overline z=z^q$. For a three-tensor with all three Hermitian Gram matrices having pairwise distinct characteristic roots in $K$, one can decide product-special-unitary equivalence against every target in expected polynomial bit time. The claim includes characteristic two and roots outside $\mathbb F_q$. More generally one can test any prescribed triple of local determinants, compute the size of the stabilizer determinant image, and count exactly how many special-unitary orbits lie in the full product-unitary orbit. No discrete logarithm or primitive element computation is required. This extends the use of determinant characters and norm-one equations to a common three-mode finite-field transport problem. [Classical groups](https://arxiv.org/html/2306.03135v2) · [Earlier Smith equations in quadratic norm-one groups](https://github.com/Dugongue/MathProofs/blob/a32630798eebd129ef621986ca4e0b8ce5edfcf3/AlpogeGrochowFurtherTransfers/QuadraticNormOneDescent.md)

### Matching the eigenspaces

For the mode-$i$ flattening $T_{(i)}$, put $C_i(T)=T_{(i)}T_{(i)}^*$, with $*$ the conjugate transpose. Under a product-unitary action this matrix changes by conjugation by the $i$th local factor, since the tensor product of the other unitary factors is unitary. Under the promise, every distinct eigenvalue labels a unique line. Check that the target has the same characteristic polynomials, then take arbitrary bases $B_i,B'_i$ of eigenvectors in matching eigenvalue order. These exist because the polynomials split simply. Standard finite-field factoring and linear algebra give the bases in expected polynomial bit time. Simple splitting can itself be checked by square-free gcd and reduction of $x^{q^2}-x$ modulo the characteristic polynomial. For fixed $q$, factoring here also follows by evaluating at every element of the fixed field, giving a deterministic polynomial-time algorithm.

Any local candidate has the form $B'_i\operatorname{diag}(z_{ij})B_i^{-1}$ with $z_{ij}\in K^\times$. Put $H_i=B_i^*B_i$ and $H'_i=(B'_i)^*B'_i$. Check matching zero patterns in each pair. The complete local unitary conditions on nonzero entries are
$$
z_{ij}^{\,q}z_{ik}=(H_i)_{jk}/(H'_i)_{jk}.
$$
They follow by comparing the Hermitian matrices in the chosen coordinates. This form of the equations works even when an eigenline is isotropic and pairs nontrivially with a different line. No normalization of the eigenvectors is required.

Express the two tensors in their respective bases. Their supports must coincide, and each nonzero coefficient gives the equation that the product of its three corresponding $z$-variables is the target/source coefficient ratio. A prescribed determinant $\delta_i$ in mode $i$ gives the further equation
$$
\prod_j z_{ij}=\delta_i\,\det(B_i)/\det(B'_i).
$$
These equations are necessary and sufficient by substitution. Taking all $\delta_i=1$ decides the special-unitary problem.

### Solving and counting without discrete logarithms

All the resulting equations are monomial equations in the cyclic group $K^\times$ of order $m=q^2-1$. Apply polynomial-bit integer Smith normal form, keeping the unimodular row and column transforms of the exponent matrix. Row transformations are implemented on the multiplicative right-hand sides by powers and products. Column transformations are invertible monomial changes of unknowns. In the diagonal system $u^s=b$, solvability is exactly $b^{m/\gcd(m,s)}=1$. A zero row requires its right-hand side to be one. This gives a uniform test by field exponentiation, with no need to produce any logarithms or roots.

For $T$ compared with itself in the same frames, the system without determinant equations is homogeneous in multiplicative notation. Let $E$ be its exponent matrix on $N$ variables, and let $D$ be the three rows $\sum_j \mathbf e_{ij}$ giving the products of the phases in each mode. For any integer matrix $A$ of rank $r$ with nonzero Smith entries $s_1,\ldots,s_r$, define
$$
k_m(A)=m^{N-r}\prod_{\ell=1}^r\gcd(m,s_\ell).
$$
This is the exact size of the kernel of its monomial map on $(K^\times)^N$. The determinant homomorphism on the stabilizer has image size $k_m(E)/k_m(\begin{smallmatrix}E\\D\end{smallmatrix})$, by the homomorphism theorem. The group determinant map from the product of unitary groups onto the three copies of the norm-one scalars is surjective, by scaling one vector in an orthonormal basis in each mode. Product-special-unitary is its kernel. Because the kernel is normal, the number of its orbits in the full orbit is the index of the stabilizer determinant image, giving the exact number by dividing $(q+1)^3$ by the image size. Prescribed image membership uses the same exponent test. All counts have polynomial bit lengths.

### An explicit determinant obstruction

For $q>2$, choose $a\in K^\times$ with norm different from one, using surjectivity of the field norm, and take
$$
T=e_0\otimes e_0\otimes e_0+a\,e_1\otimes e_1\otimes e_1 .
$$
The three Gram matrices are diagonal with distinct entries $1$ and $a\overline a$. All stabilizers are diagonal in these coordinates. The tensor equations require the three first-coordinate phases to have product one and separately the three second-coordinate phases to have product one. Thus their determinant triples form exactly the subgroup with product one. There are exactly $q+1$ special-unitary orbits in the unitary orbit. In particular multiplying $e_0$ in mode one by a nontrivial norm-one $\eta$ gives a tensor equivalent under product unitary but not under product special unitary. The product of its three transporter determinants is always $\eta$, and scalar changes with product one leave that determinant product unchanged.

The proof covers the split-simple Hermitian Gram class. It makes no decision claim for repeated or nonsplit characteristic factors.
