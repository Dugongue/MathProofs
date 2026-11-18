# Linearizing bounded finite-difference degree over finite abelian groups

Fix a prime \(p\), an exponent bound \(p^e\), an arity bound, and a finite-difference degree bound \(r\). Consider named structures on explicitly presented finite abelian \(p\)-groups of exponent dividing \(p^e\). In addition to the additive groups, the structures can have named operations between products of sorts, given by polynomial-time evaluable descriptions. Assume that each such operation \(f:C\to B\), on the product group \(C\), satisfies
\[
\Delta_{h_1}\cdots\Delta_{h_{r+1}}f(x)=0
\]
for every choice of \(x,h_i\in C\), where \(\Delta_h f(x)=f(x+h)-f(x)\). Constants are also allowed. There is a polynomial-size fully faithful encoding of these structures and their additive operation-preserving homomorphisms into finite-dimensional linear structures over \(\mathbb F_p\), using only linear and bilinear structure maps and distinguished vectors. In particular their isomorphism problems reduce in polynomial time to ordinary 3-tensor isomorphism over \(\mathbb F_p\).

This combines the earlier prime-power carry construction with the named tensor-system compiler. The additional step proves that bounded *finite-difference degree*, even for operations that are nonlinear and not multilinear, is sufficient for linearization.

## The truncated group algebra

Write \(k=\mathbb F_p\), \(D=p^{e-1}\), \(H_L(C)=k[C]/I^{L+1}\), where \(I\) is the augmentation ideal of the group algebra. Also keep \(K_L(C)\), the tensor square with terms of total augmentation order greater than \(L\) removed. Record multiplication, the augmentation, the quotient bilinear map \(q\) to \(K_L\), the coproduct \(\Delta([x])=[x]\otimes[x]\) into \(K_L\), and the unit. For every \(L\ge D\), the solutions \(g\) to \(\epsilon(g)=1\), \(\Delta(g)=q(g,g)\) are exactly \(j_L(x)=[x]\bmod I^{L+1}\) for \(x\in C\), with distinct \(x\) giving distinct elements.

For completeness, decompose \(C\) into cyclic groups of orders \(p^{a_i}\) and put \(X_i=[e_i]-1\) for the cyclic generators. The monomial basis consists of total degrees at most \(L\) with each exponent below \(p^{a_i}\). The smallest nonzero cyclic digit of \(x\) gives a nonzero coefficient on one of the pure powers \(X_i^{p^j}\) in \(j_L(x)-1\), proving injectivity. For a putative group-like \(g\), take the first nonzero homogeneous part of \(g-1\). The defining equation makes it primitive for the coproduct \(X_i\mapsto X_i\otimes1+1\otimes X_i\) on that degree. A monomial with several variables has a surviving mixed term obtained by putting all powers of one variable on the left and the rest on the right. A pure power with exponent other than a power of \(p\) has a surviving mixed binomial coefficient by base-\(p\) expansion. Distinct original monomials cannot produce the same output monomial. Thus the primitive part is a combination of the retained \(p\)-powers, all with degrees at most \(D\). Choose an \(x\) with exactly those cyclic digits and divide \(g\) by \(j_L(x)\). Both the coproduct and the tensor-square operation on a single element respect multiplication, so the remainder is group-like with higher first degree. Iteration finishes the proof.

Any collection of linear maps preserving this structure restricts to an additive homomorphism on these points. Conversely an additive homomorphism extends by the group algebra and the truncations. The extension is unique since the \(j_L(x)\) span \(H_L\) and the image of \(q\) spans \(K_L\). The monomial basis above has polynomial size in the number of cyclic coordinates for fixed \(L\).

## Degree bound for the linearization of an arbitrary operation

Choose \(L=\max(D,rD)\). The linear map \([x]\mapsto j_D(f(x))\) on \(k[C]\) kills \(I^{L+1}\), so it gives a linear map \(H_L(C)\to H_D(B)\). Indeed, write \(h_I=\sum_{i\in I}h_i\) for any subset of \(s>L\) difference directions, and use the discrete expansion
\[
f(x+h_I)=\sum_{J\subseteq I}g_J,\qquad
g_J=\Big(\prod_{j\in J}\Delta_{h_j}\Big)f(x).
\]
Every \(g_J\) with \(|J|>r\) vanishes. Apply \(j_D\), which sends group addition to multiplication, and expand the nonempty-\(J\) factors as \(1+(j_D(g_J)-1)\). The alternating sum over \(I\) annihilates every resulting term whose chosen \(J\)'s do not cover all \(s\) directions. A term that covers all \(s\) uses more than \(D\) of the nonconstant factors, each in the augmentation ideal, hence also vanishes. Products \([x]\prod_{i=1}^s([h_i]-1)\) span the augmentation powers, proving the claim.

Store both truncations for every sort, with their natural projection. For each operation on a product of sorts use the same structure on the product group, with its coordinate projection maps, and add the displayed linearized operation. These conditions force every additive map on the product sort to be the product of its named component maps. Preservation of the linearized operation on the spanning group-like elements is exactly preservation of \(f\), because \(j_D\) is injective. All maps on auxiliary sorts are thereby uniquely determined, which proves full faithfulness. A monomial of degree at most \(L\) expands as a linear combination of at most \(2^L\) group elements, so assembling each linearized map column uses polynomially many evaluations in the stated model. The ordinary named linear-structure compiler then gives one 3-tensor pair for the isomorphism decision.

## Several primes and polynomial operations over rings

If several primes occur, an operation of bounded finite-difference degree splits into its independent prime components. To see this, project the output to its \(p\)-primary component and fix all but the input along a \(q\)-primary direction \(h\) with \(q\ne p\). On the span over \(\mathbb Z/p^e\mathbb Z\) of the translates of the output function, \(T_h=1+\Delta_h\) and \(\Delta_h^{r+1}=0\). If \(h\) has order \(a\), then
\[
0=T_h^a-1=\Delta_h\left(a+\text{a polynomial in }\Delta_h\text{ with zero constant term}\right).
\]
The second factor is invertible by nilpotence because \(a\) is prime to \(p\). Thus \(\Delta_h\) acts as zero. The output component is independent of the other primary components, including when the original operation has a constant term. Apply the compiler for each prime separately.

In particular explicit bounded-degree ring-polynomial operations on modules over a fixed finite commutative ring satisfy the hypothesis whenever their coefficients and multilinear primitives are explicitly evaluable. Expanding each product after translation shows that every difference lowers the remaining total degree by at least one. Scalar actions are named unary operations of degree one. Thus the theorem applies to nonlinear systems on nonfree modules and reduces them to one prime-field tensor-isomorphism test per prime. The prior same-prime-support construction combines these tests into one free-module 3-tensor pair over any fixed finite commutative ring with that characteristic prime support. This proof is informal.
