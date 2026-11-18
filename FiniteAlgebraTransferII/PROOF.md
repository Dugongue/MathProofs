# Counting homomorphisms by affine lifts over a quotient

Let \(B\) be a fixed finite target algebra, with a fixed quotient \(B\to Q\). Give each nonempty fiber a finite abelian group coordinate system. Suppose that on every tuple of fibers each basic operation of \(B\) is an affine map, a constant plus a sum of homomorphisms from the input fibers to the output fiber. Suppose also that onto homomorphisms from an explicit source \(S\) to \(Q\) can be listed in polynomial time. Then onto homomorphisms \(S\to B\) can be found in polynomial time, and all homomorphic lifts of any specified quotient map can be counted exactly in polynomial time.

Exact counting of **onto** maps is also polynomial under either of the following additional hypotheses.

1. Each maximal proper subalgebra of \(B\) intersects every fiber either in the empty set or in a coset of a subgroup in its abelian coordinates.
2. The source admits a binary quasigroup law given by a term with named source constants.

The first condition includes all fibers of cardinality at most two. It also includes arbitrarily large abelian fibers when a single ternary term without named constants restricts to \(x-y+z\) on each fiber. The second condition is on the source alone. This combines exact enumeration to a quotient, affine lifting, and the constant preimage multiplicity used in earlier group counting.

## The common affine system

For each onto \(\psi:S\to Q\), give a variable \(z_s\) the coordinate group of the fiber over \(\psi(s)\). For a basic operation \(g\) and every input tuple \(\mathbf s\), impose
\[
z_{g(\mathbf s)}=c_{\psi(\mathbf s)}+\sum_i L_{\psi(\mathbf s),i}(z_{s_i}),
\]
where the constant and the homomorphisms are those of the target operation on this tuple of fibers. This gives exactly the lifts over \(\psi\). For constant operations the sum is empty. The domain of the system is a product of finite abelian groups. Smith normal form in cyclic coordinates counts the solutions as the size of a fiber of a homomorphism, returning zero when the offset is inconsistent. It also supplies a solution when one exists.

To decide surjectivity, fix a generating tuple of \(B\) and enumerate a preimage for each entry. Prescribe its coordinate in the system, rejecting pins to the wrong fiber. Every resulting lift has image containing the generating tuple and is therefore onto. Conversely an onto lift gives some such preimages. The tuple length is bounded since \(B\) is fixed. This gives search and decision in every case.

## Counting by restrictions to maximal subalgebras

For a nonempty source, the image of a homomorphism that is not onto is contained in some maximal proper subalgebra of \(B\). Use inclusion–exclusion over this fixed finite list. For a subcollection, the additional constraint is that every image lies in the intersection of its subalgebras. If any required fiber intersection is empty the count is zero. Otherwise the intersection in each fiber is again a coset, since any intersection of cosets of subgroups that contains a point is the translate by that point of the intersection of the subgroups. Restriction to these cosets adds only affine congruences. This yields the exact number of onto lifts over each \(\psi\). A nonempty subset closed under \(x-y+z\) is a coset by translating any chosen point of the subset to zero, proving the term criterion for the first hypothesis.

## Counting with uniform source fibers

If the source admits a quasigroup term, then any onto homomorphism \(f:S\to B\) has fibers of equal size. The term with the images of the constants defines a quasigroup law on the finite target because each translation is surjective by lifting both the fixed argument and the desired output to the source. Given two target fibers, choose a target left translation taking the first value to the second. A lift of its left multiplier gives a bijective source translation. It restricts to a bijection on these fibers by the cancellation of the target translation. Thus every onto \(f\) has fibers of size \(|S|/|B|\).

Count the pinned affine systems as above, now with multiplicities. If the chosen target generating tuple has length \(d\), each onto \(f\) contributes exactly \((|S|/|B|)^d\) times for its unique quotient map, because the preimages are chosen independently. Dividing by this integer gives the exact count, or returning zero immediately if divisibility fails.

In the block algebra of a left- and right-permutive radius-one cellular automaton, fixing the middle block gives such a source quasigroup. Number the three input blocks consecutively from position 0 and use block length \(N\). Each output coordinate \(j\), \(0\le j<N\), depends only on initial positions \(j,\ldots,2N+j\). The local permutivity at an extreme propagates to the corresponding extreme through every time step. With the middle and right blocks fixed, recover the left block in decreasing order from the output coordinates. With the left and middle blocks fixed, recover the right block in increasing order. Both translations are bijective. This applies the uniform-fiber count to exact surjective coarse-graining for these sources and arbitrary fixed affine-fiber targets with enumerable quotient maps. This proof is informal.
