# A counterexample to Loewy-length monotonicity for the J-preorder

Status: informal proof with published inputs and a separate exact finite computation; not Lean verified. The conclusion refutes Conjecture 43 as stated in Helena Jonsson, *J-equivalence for associative algebras*, Beiträge zur Algebra und Geometrie 66 (2025), 539–574. Priority remains unconfirmed: the bounded literature search found no earlier explicit refutation, but the ingredients are classical.

## Statement

Let k be an algebraically closed field of characteristic 2. Let G = A5, let P be a Sylow 2-subgroup of G, so P is isomorphic to C2 × C2, and let e be the principal-block idempotent of kG. Set

A = e(kG),    B = kP.

Then A and B are finite-dimensional connected k-algebras and

A ≥_J B,    LL(A) = 5 > 3 = LL(B).

Thus the implication A ≥_J B ⇒ LL(A) ≤ LL(B) is false, even with connected symmetric algebras and a witness projective on each side.

The exact target and definition are in [Jonsson, Definition 1 and Conjecture 43](https://link.springer.com/article/10.1007/s13366-024-00757-8). The preorder means that the regular A-bimodule is a direct summand of M ⊗_B N for finite-dimensional bimodules M and N.

## Proof of the preorder relation

Write R = kG and q = [G:P] = 15. Choose representatives T for the cosets tP. Since q is invertible in k, the tensor

E = q^(-1) Σ_(t∈T) t ⊗ t^(-1) ∈ R ⊗_B R

is well-defined independently of the representatives. Indeed replacing t by tp replaces its summand by tp ⊗ p^(-1)t^(-1) = t ⊗ t^(-1), using the balancing relation. Multiplication sends E to 1.

For each g ∈ G, write gt = t' p. Reindexing the coset representatives gives

gt ⊗ t^(-1) = t'p ⊗ t^(-1) = t' ⊗ p t^(-1) = t' ⊗ t'^(-1)g.

Therefore gE = Eg, and by linearity rE = Er for all r ∈ R. The map s:R→R⊗_B R given by s(r)=rE is an R-bimodule map split by multiplication.

Now apply the operation X↦eXe to this retraction. Because e is central, eRe=A, and

e(R⊗_B R)e = (eR)⊗_B(Re).

Explicitly, choose M=eR as an A-B-bimodule and N=Re as a B-A-bimodule. For a∈A, s(a)=aE belongs to e(R⊗_B R)e: left multiplication by e fixes it, and aEe=aeE=aE. The restriction of multiplication therefore splits this map as A-bimodule maps. Hence A is a direct summand of M⊗_B N, as required.

Both outer A-actions are regular, so M is free as a left A-module and N free as a right A-module. As B-modules they are direct summands of the free module R, because multiplication by the central idempotent e is B-linear. Thus the witness also satisfies the stronger one-sided projectivity conditions used for separable division.

## Loewy lengths and connectedness

A is a block algebra, hence connected by definition. B has the explicit presentation

B ≅ k[x,y]/(x²,y²),

obtained from x=u−1 and y=v−1 for the two commuting involutions generating P. Its radical is (x,y); its square is k·xy, and its cube is zero. Thus B is local, hence connected, and LL(B)=3.

The principal 2-block of kA5 has Loewy length 5. This standard value is stated explicitly in [Eaton and Livesey, *Loewy lengths of blocks with abelian defect groups*, arXiv:1607.08795, page 1, Introduction](https://arxiv.org/pdf/1607.08795). In particular, its fourth radical power is nonzero and its fifth radical power is zero. This supplies LL(A)=5 and completes the counterexample.

The argument needs only the displayed one-way preorder relation. It does not silently assume that restricting the group/Sylow separable equivalence to an arbitrary block preserves both directions.

## Arbitrarily large additive violations


**Corollary.** For every positive integer r there exist connected finite-dimensional k-algebras A_r and B_r such that

    A_r >=_J B_r,
    LL(A_r)=4r+1,
    LL(B_r)=2r+1.

Thus the proposed monotonicity can fail by an arbitrarily large additive amount.

Take A_r=A tensor_k ... tensor_k A and B_r=B tensor_k ... tensor_k B, with r factors. Tensoring the explicit bimodule splittings from Section 2 gives the required comparison. Equivalently, use G=A_5^r, P=V_4^r, and the block idempotent e tensor ... tensor e; the same coset proof applies because the index 15^r is odd.

Here are the two standard tensor facts, with their needed hypotheses made explicit. For finite-dimensional algebras U,V over algebraically closed k, put I=J(U) tensor V + U tensor J(V). The ideal I is nilpotent. Its quotient is (U/J(U)) tensor (V/J(V)), a product of matrix algebras over k, so semisimple. Hence I=J(U tensor V). If LL(U)=a and LL(V)=b, powers of I show I^(a+b-1)=0, while I^(a+b-2) contains the nonzero subspace J(U)^(a-1) tensor J(V)^(b-1). Therefore LL(U tensor V)=a+b-1.

Also Z(U tensor V)=Z(U) tensor Z(V): expand in a basis of one factor to impose commuting with the other factor, then reverse the roles. When U,V are connected, their finite-dimensional commutative centers are local and have residue field k. The sum of their tensor-extended maximal ideals is nilpotent with quotient k, so their tensor product center is local. Thus U tensor V is connected. Induction proves both claims for A_r,B_r.

This amplification is our elementary deduction from the counterexample; no independent priority is asserted.


## Separate exact computational check

The companion Python program constructs SL2(F4), a group of order 60 isomorphic to A5, and its group algebra over F2. It uses the representation map

F2[G] → F2 ⊕ Mat_2(F4) ⊕ Mat_4(F2).

The components are the trivial representation, the natural representation over F4, and the augmentation summand of the five-point permutation representation on the projective line. Its image has F2-dimension 25, the full dimension of the semisimple target. Its kernel I has dimension 35, and exact multiplication gives

(dim R, dim I, dim I², dim I³, dim I⁴, dim I⁵) = (60,35,27,17,9,0).

The nilpotent kernel and semisimple quotient identify I with the Jacobson radical. This independently verifies Loewy length 5 for the full group algebra. The computation is corroboration, not the replacement for the published principal-block statement. No floating point arithmetic, probabilistic tests, or unproved rank estimates are used. An explicit nonzero product of four listed radical basis elements equals the sum of all 60 group elements.

## Novelty and attribution

The counterexample combines established modular representation theory with an explicit elementary separability retraction. The Loewy-length value and group/Sylow separability are not new discoveries. The potentially new observation is their incompatibility with the precise published Conjecture 43 after retaining connectedness through the principal block.

Searches checked the article title with correction and counterexample, the conjecture number with Jonsson and Loewy, J-equivalence with A5 and radical, and separable equivalence with Loewy length. The publisher version still states the conjecture. No earlier explicit refutation was located in those searches. This is evidence from a bounded search, not proof of publication priority.

The counterexample is a short representation-theory result. It is not a solution to TI versus SL-TI, and it should not be described as a major general complexity breakthrough.
