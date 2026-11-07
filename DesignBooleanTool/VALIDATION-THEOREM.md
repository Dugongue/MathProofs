# A complete Walsh certificate validates the design

This elementary finite-Fourier argument justifies the certificate-first validation strategy in version 0.2.0. It is an informal proof, independently checked by all four workers. It introduces no promise that an input is already a design.

## Statement

Let X = F₂^m, N = 2^m, and let f:X→F₂ have Walsh transform

$$
W_f(u)=\sum_{x\in X}(-1)^{f(x)+u\cdot x}.
$$

Let S be its complete nonzero Walsh support, with |S|=v, and suppose every nonzero coefficient is ±A for a positive integer A. Let the row labels φ_p be a bijection from the input points to S and the column labels β_b a bijection from the input blocks to X. Suppose g_p∈F₂ satisfies W_f(φ_p)=A(−1)^{g_p}, and verify every input bit through

$$
M_{p,b}=\phi_p\cdot\beta_b+f(\beta_b)+g_p\pmod2.
\tag{1}
$$

If S affinely spans X, then M is a simple 2-design with constant block size

$$
k=\frac{v-N/A}{2}
$$

and point-pair multiplicity

$$
\lambda=\frac{N-2A}{4}.
$$

The formulas are assertions in the supported nondegenerate parameter range, where these are the positive integers specified by the original characterization. The argument also computes the common replication number (N−A)/2.

## Proof

Write s_p(x)=(−1)^(φ_p·x+f(x)+g_p). Its sum over x is (−1)^{g_p}W_f(φ_p)=A. Therefore each row has (N−A)/2 ones.

For distinct points p,q, their frequencies are distinct. The product s_p(x)s_q(x) cancels f(x), so its sum over X is zero by character orthogonality. The number of columns incident with both points is consequently

$$
\sum_x\frac{1-s_p(x)}2\frac{1-s_q(x)}2
=\frac{N-A-A+0}{4}=\lambda.
$$

For a fixed x, Walsh inversion gives

$$
\sum_p s_p(x)
=(-1)^{f(x)}\frac1A\sum_{u\in S}W_f(u)(-1)^{u\cdot x}
=\frac NA.
$$

Thus each column has (v−N/A)/2 ones.

Finally, suppose two columns labeled x,y have equal entries. Subtracting (1) says φ_p·(x+y)=f(x)+f(y) for every p. If x≠y, the nonzero linear functional u↦u·(x+y) is constant on S, so S lies in a proper affine hyperplane, contradicting its full affine span. Hence x=y, and the bijection β makes the original block indices equal. The design is simple. This proves every required design axiom.

## Executable consequence

The native recognizer can first construct the candidate labels and function, then check the entire Walsh spectrum, support, signs, all incidence bits and affine support rank. These checks establish all the design conditions by the theorem. It does not need a separate quadratic loop over point pairs.

The native `explicit` strategy retains that loop for differential testing and timing. The default `certificate` strategy derives the conditions from the verified witness. Both recognize the same family; failed early candidates do not receive a `design_validated` claim.

Checking (1) by packed coordinate-row XORs still checks every incidence bit. It changes the implementation cost, not the verified identity. No random sampling, approximate arithmetic or omitted pair promise is involved.

## Relationship to the original proof

The construction of β, φ, f and g follows `PlateauedDesign.linearize`; the full Walsh-support realization contract is `PlateauedDesign.Realization`. The argument above makes explicit why that contract is also an executable certificate of the input design axioms. Its ingredients are Walsh inversion, character orthogonality and affine-span separation. No novelty or new open-problem closure is claimed for this optimization theorem.
