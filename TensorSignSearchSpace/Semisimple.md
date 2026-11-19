# Semisimple witnesses for the determinant image of a tensor stabilizer

Let \(T\in V_1\otimes V_2\otimes V_3\) be an explicit three-tensor over \(\mathbb F_q\), with positive side dimensions \(n_i\). Write \(n=\max_i n_i\), \(G=\prod_i\mathrm{GL}(V_i)\), and \(H=\operatorname{Stab}_G(T)\). Let \(D(T)\le(\mathbb F_q^\times)^3\) be the determinant image of \(H\). The computations below have constants depending on the fixed field.

**Theorem.** For each prime \(\ell\mid q-1\), the \(\ell\)-primary part of \(D(T)\) is realized by semisimple elements whose orders are powers of \(\ell\) at most \(C_q n\), for a field-dependent constant \(C_q\). One can express all these determinant tests using \(n^{O_q(\log(2+n))}\) tests of the following form. Does the ordinary \(G\)-orbit of \(T\) meet an explicitly specified linear space of tensors? Each linear space is a fixed space of three prescribed matrices. A supplied ordinary transporter from \(T\) to \(S\), together with these tests on \(T\), suffices to decide every prescribed determinant tuple for the pair. The linear-space intersection test is a separate primitive here.

Over \(\mathbb F_3\) the order bound is exactly \(4n\). There are concise field multiplication tensors of arbitrarily large dimension \(n\) for which a particular stabilizer determinant triple can only be witnessed by elements with order divisible by \(4n\). Hence limiting the order to any constant, including restricting to involutions, can lose valid determinant tuples.

## Extracting one primary part

If \(h\in H\) has order \(\ell^a s\), with \(\gcd(s,\ell)=1\), then \(h^e\) with \(e=0\bmod s\) and \(e=1\bmod\ell^a\) has order dividing \(\ell^a\). Its determinant is exactly the \(\ell\)-primary component of \(\det(h)\). Each tuple in the \(\ell\)-primary part of \(D(T)\) has some lift \(h\), so extraction gives a witness. Conversely every \(\ell\)-element of \(H\) has \(\ell\)-primary determinant. These tests therefore give the full primary subgroup rather than just some of its generators.

For \(\ell=2\) and \(q=3\), one can simply choose \(e\) to be the odd part of \(|h|\), since the determinant signs themselves have order at most two. When \(q=2\), every determinant is already one and \(D(T)\) is trivial.

The polynomial \(x^{\ell^a}-1\) has no repeated roots in characteristic \(p\) because \(\ell\ne p\). Every component of \(h^e\) is thus semisimple. Its rational conjugacy class is determined by the multiplicities of its irreducible eigenvalue polynomials.

## A small list of rational conjugacy types

For primitive roots of unity of order \(\ell^k\), their irreducible polynomial degree is \(d_k=\operatorname{ord}_{\ell^k}(q)\). This follows by iterating Frobenius \(\lambda\mapsto\lambda^q\) on each primitive root. There are \(\varphi(\ell^k)/d_k\) distinct irreducible factors of the corresponding cyclotomic polynomial.

For odd \(\ell\), and also for \(\ell=2\) if \(q=1\bmod4\), write \(a=v_\ell(q-1)\). Then \(d_k=\ell^{\max(0,k-a)}\). Indeed \(v_\ell(q^m-1)=a+v_\ell(m)\), by lifting the exponent. For \(q=3\bmod4,\ \ell=2\), put \(b=v_2(q+1)\). One has \(d_1=1\) and \(d_k=2^{\max(1,k-b)}\) for \(k\ge2\). Here an odd \(m\) gives valuation one and an even \(m\) gives \(v_2(q^m-1)=b+v_2(m)\). In every case the number of factors per fixed \(k\) is \(O_q(1)\), and \(d_k\le n\) implies \(\ell^k\le C_q n\).

For \(q=3\) specifically, the factors for eigenvalue orders \(1,2,4\) are \(x-1,x+1,x^2+1\), respectively. Each order \(2^k\) with \(k\ge3\) has two irreducible factors of degree \(2^{k-2}\). Their companion blocks both have determinant \(-1\). In fact the determinant is the norm of a primitive root \(\zeta\), which is \(\zeta^{(3^{2^{k-2}}-1)/2}=-1\), because the exponent has valuation \(k-1\). The order-four block has determinant \(+1\).

To obtain all candidate matrices in a mode, use nonnegative multiplicities of the listed irreducible companion blocks with total dimension \(n_i\). There are \(O_q(\log(2+n))\) multiplicities per mode, each at most \(n\). Enumerating all feasible triples has size
\[
(n+1)^{O_q(\log(2+n))}.
\]
This includes all witness types, even when the stabilizer is not supplied and its order is unknown. The list and the ensuing spaces are constructive. The cyclotomic polynomials involved have degree \(O_q(n)\) and can be factored deterministically in polynomial time over a fixed finite field by Berlekamp's algorithm. For an elementary implementation, the solutions of \(f^q=f\) in the square-free quotient algebra constitute a direct product of copies of the base field. Gaussian elimination finds a basis, and gcds with basis elements minus the finitely many field scalars separate the factors. [Berlekamp's factoring paper](https://doi.org/10.1002/j.1538-7305.1967.tb03174.x)

## The exact intersection tests

For each triple \((A_1,A_2,A_3)\) from the list, form the linear subspace
\[
W_A=\ker(A_1\otimes A_2\otimes A_3-I).
\]
Writing a basis of \(W_A\) takes polynomial time in the dense tensor dimensions. If \(gT\in W_A\), then \(g^{-1}Ag\in H\) is a witness with the same determinant tuple as \(A\). If \(h\in H\) witnesses the tuple, its primary part is conjugate in \(G\) to a listed triple \(A\). Conjugating \(T\) by the same \(g\) places it in \(W_A\). Taking the determinant values for precisely the nonempty intersections recovers the desired primary subgroup. Combining the primary subgroups recovers \(D(T)\).

Equivalently, over a splitting field, \(W_A\) consists of tensors supported only on triples of eigenspaces whose eigenvalues multiply to one. This describes a grading with a fixed finite cyclic group of size \(O_q(n)\). Its rational linear space above does not require outputting the splitting field.

If \(g_0T=S\), the determinant tuples for the pair are exactly \(\det(g_0)D(T)\). The supplied transporter gives the translate and the linear-space tests determine the subgroup. This separates finding the translate from deciding which stabilizer corrections are possible. An ordinary oracle for isomorphism of two specified tensors does not directly provide these orbit–linear-space intersections.

## Why order \(4n\) is necessary over \(\mathbb F_3\)

Let \(n=2^r\ge2\) and \(K=\mathbb F_{3^n}\). Use the multiplication tensor \(T(x,y)=xy\), with autotopisms defined by \(A(x)B(y)=C(xy)\). This corresponds to the tensor convention via inverses or duals, which preserve the signs. The tensor is concise because it has a unit and has zero annihilator in either input.

Set \(a=A(1)\), \(b=B(1)\). Both are nonzero. Evaluating the identity at \((x,1)\) and \((1,y)\) shows that \(A=L_a\phi,\ B=L_b\phi,\ C=L_{ab}\phi\) for a single linear bijection \(\phi\) fixing 1. Substitution in the autotopism equation shows that \(\phi\) is a field automorphism, hence a power of the Frobenius \(x\mapsto x^3\). Conversely each such choice is an autotopism. Here \(L_a\) denotes multiplication by \(a\). Its determinant is the norm from \(K\) to \(\mathbb F_3\).

Write \(\phi=\mathrm{Frob}^j\). A normal basis makes Frobenius into an \(n\)-cycle, so \(\det\phi=(-1)^j\) since \(n\) is even. The product of the three signs is exactly \(\det\phi\), since the two norm contributions appear squared. Consequently the sign triple \((-1,-1,+1)\) forces \(j\) even and both norms \(N(a),N(b)\) equal to \(-1\).

Let \(d=\gcd(n,j)\) and \(m=n/d\), using \(d=n\) when \(\phi=1\). Then \(d\ge2\) and the fixed field of \(\phi\) is \(\mathbb F_{3^d}\). The \(m\)-th power of \(A\) is multiplication by the relative norm \(a'\) of \(a\) to this field. By transitivity \(a'\) has base-field norm \(-1\). Since \(v_2(3^d-1)=2+v_2(d)\), a field element of norm \(-1\) has order divisible by \(4d\). Indeed the norm exponent is \((3^d-1)/2\), which kills every element whose order has smaller 2-part. Also \(m\) divides the order of \(A\), since conjugation by \(A\) on the group of nonzero multiplication maps induces \(\phi\). Thus if \(o\) is the order of \(A\), the order of \(A^m\) is \(o/m\), proving \(4n\mid o\).

The signs \((-1,-1,+1)\) occur with \(\phi=1\) and \(a=b\) a primitive element of the 2-primary subgroup of \(K^\times\). This gives a witness of order exactly \(4n\). In particular the linear bound cannot be improved even on this simple growing tensor family.

The witness theorem and sharpness argument are informal. They address the determinant-image subgroup for every raw tensor. A method for calibrating the translate on arbitrary input pairs or compiling the intersection tests into ordinary TI remains a separate task. The known narrow determinant compilations are related through that translate. [Published SL-TI question](https://arxiv.org/html/2306.03135v2#S1.SS5)
