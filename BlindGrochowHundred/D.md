# Compressing a panel of linear tests

A panel is a family of linear maps on a common space. Its joint kernel records which differences the panel cannot detect. The results apply to linear constraints on tensor slices or transporters once the linear maps and the space of unknowns have been fixed.

## Exact finite compression

Let $P$ be a subspace of a finite-dimensional vector space, and let $H$ be the joint kernel of an arbitrary panel. A subpanel of at most $\dim P-\dim(P\cap H)$ components has the same kernel on $P$. At each step choose a component that detects a surviving vector outside $H$. Its kernel strictly lowers the surviving dimension, and the final kernel still contains $P\cap H$. The theorem places no cardinality restriction on the original panel. Choosing the same components for two panels costs at most the sum of their joint ranks, by taking the union of the two selected sets.

When each probe is scalar-valued, the rank bound is exact. A panel with $r$ scalar entries has joint rank at most $r$, so any complete scalar subpanel needs at least the original joint rank many probes. The formal theorem supplies an attaining finite set and this lower bound.

## Decoding and orbit equivalence

For a retained linear observation $f$, a second observation $g$ can be recovered linearly from the actual image of $f$ exactly when $\ker f\subseteq\ker g$. The decoder is unique on that image. Equality of the kernels gives unique transport between the images. In a common output vector space, this transport extends to an ambient linear automorphism for finite-rank maps. A joint observation containing a redundant component has a graph as its image. The source also covers products of probes and input changes of basis.

## Exact rank increments

For a pair $(f,g)$ with finite-dimensional domain, the joint rank equals the rank of $f$ plus the rank of $g$ restricted to $\ker f$. An increase therefore has a single-vector witness. Another formula measures the rank overlap as the dimension of the common quotient by $\ker f+\ker g$. If each component is surjective, joint surjectivity holds exactly when this common quotient is zero.

These results use standard quotient linear algebra and rank-nullity. The contribution here is the package of finite compression, transport and decision certificates in one model. The blind queue suggested the model through handles 436252 and 324094 for quantitative cokernel and kernel dimension, 222662 for finite separating charts, 461852 and 327410 for comparison by common kernels and exact descent, and 3152 for combining multilinear inputs. The reasoning and choice of statements followed the identifier reveal. [Frozen queue](queues/worker-4.json) · [Lean proof](D.lean)
