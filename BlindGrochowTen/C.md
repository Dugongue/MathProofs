# Multiplication transports and weighted trace tensors

The two theorem statements in [C.lean](C.lean) address full equivalence problems.

## Multiplication isotopies

Over any commutative scalar semiring, let $A,B$ be unital associative algebras. Let $X,Y,Z$ be linear equivalences from $A$ to $B$ satisfying $Z(xy)=X(x)Y(y)$. Then there is an algebra equivalence $\sigma:A\to B$ and two units $a,b\in B^\times$ with
$$
X(x)=a\sigma(x),\qquad Y(x)=\sigma(x)b,\qquad Z(x)=a\sigma(x)b.
$$
Every such choice gives an isotopy. The normal form is unique since $a=X(1)$ and $b=Y(1)$, which then specify $\sigma$. In particular this describes the stabilizers as well as the equivalence classes of multiplication tensors.

To obtain the units, transport along $Z$ to a preimage $t$ of $1$. Substitution at $1$ shows that multiplication on the left by $a$ and on the right by $b$ are bijective. We have $aY(t)=1$ and $X(t)b=1$. Injectivity gives the other inverse identities. Normalize $Z$ to $x\mapsto a^{-1} Z(x)b^{-1}$. The original isotopy then identifies the product of two normalized images with the normalized image of their product. Associativity suffices. Albert proved the underlying unital-isotopy result over fields. [Albert, *Non-associative algebras I*](https://doi.org/10.2307/1968960)

## Common-basis equivalence of weighted trilinear trace forms

Let $A,B$ be commutative algebras over a commutative ring $R$. Assume the trace pairing on $B$ is nondegenerate. For units $a\in A^\times$ and $b\in B^\times$, a common linear equivalence on all three variables identifies
$$
(x,y,z)\longmapsto \operatorname{Tr}_{A/R}(axyz),
\qquad
(x',y',z')\longmapsto \operatorname{Tr}_{B/R}(bx'y'z')
$$
exactly when there are an $R$-algebra equivalence $\sigma$ and a unit $u$ of $B$ with $\sigma(a)=b u^3$.

Compare the triples $(x,y,z)$ and $(xy,1,z)$ and use surjectivity in the third slot. Trace-pairing separation and cancellation of the weight unit give $T(x)T(y)=T(1)T(xy)$. Choosing $T(v)=1$ makes $T(v^2)$ an inverse for $T(1)$. Hence $T$ is $u\sigma$ with $u=T(1)$. Comparing the triples $(x,1,1)$ and using trace invariance under algebra equivalence recovers the transported weights by nondegeneracy. The reverse implication uses $T=u\sigma$. The proof applies to trilinear forms in characteristics two and three. Harrison and Pareigis already proved the finite separable field version under the assumption that the characteristic does not divide the factorial of the degree. [Harrison and Pareigis, Theorem 3.12](https://epub.ub.uni-muenchen.de/7099/1/7099.pdf)

For a concrete distinction, the forms $xyz$ and $2xyz$ over $\mathbb F_7$ become equivalent when the first variable can be rescaled independently. A common change of basis would scale by a cube. The nonzero cubes in this field are $1$ and $-1$, so that common change cannot exist.

## Discovery evidence

The anonymous list was frozen with seed 372133 and limit 180. Revealed match 164 contains handles 27777 (isomorphism transport) and 44782 (a duality bound). Match 163 contains handle 35002 (scalar cancellation). Together they suggested comparing algebra transports using dual separation and cancelling the image of the unit. The matching ports seed the route, and the complete proofs use the sources in this package. [Frozen numeric list](C-Frozen.json)
