# Complexity dichotomy for pure mixed tensor signatures

## GP-0256

For a fixed number of factors and fixed nonnegative integers $a_i,b_i$, consider the single mixed tensor
$$
\bigotimes_{i=1}^k X_i^{\otimes a_i}\otimes(X_i^*)^{\otimes b_i}
$$
under the product of the corresponding general linear groups, with dimensions varying and complex acting field. If any $a_i\ne b_i$, orbit-closure intersection is trivial. If all $a_i=b_i$ and $\sum_i a_i\le1$, it is decidable in polynomial bit time on rational complex inputs. In every other case, it is TOCI-complete under efficient algebraic reductions. The dichotomy also extends to all tuples of individually balanced signatures. A further class of tuples with unbalanced signatures reduces to its balanced subtuple by a common central degeneration.

The base missing from the general single-tensor classification is one balanced pair in each of two different factors. We show directly that
$$
\bigl(\operatorname{End}(X)\otimes\operatorname{End}(Y),
      \mathrm{GL}(X)\times\mathrm{GL}(Y)\bigr)
$$
is TOCI-complete. This is orbit-closure intersection for the 2D PEPS gauge action at physical dimension one. Lysikov and Walter established completeness at physical dimension three, which is the starting problem below. [Lysikov–Walter, Theorem V.11](https://arxiv.org/html/2411.04639v2#S5.SS1) · [Marked-fiber argument](PureMixedQuarticTOCI.md)

### Recover both color partitions from one tensor

Let $\widehat X$ consist of six coordinate copies of $X$ and $\widehat Y$ of six coordinate copies of $Y$. Let $D_X$ and $D_Y$ have successive distinct scalar blocks $-5,-3,-1,1,3,5$ on the respective copies. Both matrices have trace zero. We work in $\operatorname{End}(\widehat X\otimes\widehat Y)$ with conjugation by $g\otimes h$.

Write $J^X_{ij}$ for the coordinate identity from copy $j$ to copy $i$, extended by zero on all other input blocks. Define $J^Y_{ij}$ similarly. Use the tensor
$$
A=D_X\otimes I_{\widehat Y}+I_{\widehat X}\otimes D_Y
 +\sum_{i=2}^6\bigl(J^X_{i1}\otimes J^Y_{21}+(J^X_{i1}\otimes J^Y_{21})^*\bigr)
 +\sum_{j=3}^6\bigl(J^X_{21}\otimes J^Y_{j1}+(J^X_{21}\otimes J^Y_{j1})^*\bigr).
$$
The adjoints here are computed in the fixed standard coordinate inner product. The array entries are rational. Each bridge term is off diagonal in both color partitions, so either partial trace kills it. Normalized partial traces of $A$ return $D_X,D_Y$.

For each $r=1,2,3$, encode an endomorphism of $X$ as the same map on copy $2r-1$ and its negative on copy $2r$, both diagonally, and zero otherwise. Call the encoding $E^X_r$, and define $E^Y_r$ similarly. These maps are linear and injective, with trace-zero images. For an input triple $(Q_1,Q_2,Q_3)$ of elements of $\operatorname{End}(X)\otimes\operatorname{End}(Y)$, output
$$
T=A+\sum_{r=1}^3(E^X_r\otimes E^Y_r)(Q_r).
$$
The data terms have both partial traces zero. The two normalized partial traces therefore recover the colors. Evaluate Lagrange polynomials at those traces to obtain the color projectors as polynomial functions of $T$. Each data term occupies exactly four sectors, diagonal on a pair of selected colors in each axis. The three $r$-families of sectors are disjoint. For a globally equivariant regular map $\pi$, subtract those sectors of
$$
T-D_X(T)\otimes I_{\widehat Y}-I_{\widehat X}\otimes D_Y(T)
$$
from $T$, where $D_X(T),D_Y(T)$ are the normalized traces for arbitrary $T$. Off-diagonal bridges lie in none of the subtracted sectors. This map satisfies $\pi(T)=A$ on all encoded points. The orbit of $A$ is closed because it is self-adjoint and the derivative of product conjugation is a commutator, whose Hermitian moment functional at $A$ vanishes. This is the same Kempf–Ness calculation as for the single diagonal mixed quartic.

### Recovery of exactly the same two actions

An element of the stabilizer of $A$ fixes its normalized traces, so its two components are block diagonal. For every $i=2,\ldots,6$, preservation of the $X$ bridge from color $1$ to $i$, paired with the $Y$ bridge from color $1$ to $2$, gives equality of a nonzero pure tensor to the tensor product of the two original coordinate identifications. The maps on $X$ colors $1$ and $i$ must therefore agree up to scalar. The corresponding $Y$ maps on colors $1,2$ agree up to scalar. The second family of bridges gives the same conclusion for the remaining $Y$ colors. The scalar relationships imposed by the bridges have no effect on each diagonal sector, where conjugation cancels the scalar. Therefore the stabilizer acts on all three encoded data coordinates by the same original pair of conjugations. Every original pair acts by repeating each of its two maps on its six copies. The encoded affine data subspace is closed and stable for this action. The marked-fiber argument applied to $\pi$ now proves closure-equivalence reflection and preservation.

The reduction has rational affine-linear formulas and enlarges each dimension by six. It proves completeness for the one-tensor double-conjugation action, including the hard case with both tensor variances occurring only once in each of the two labels. Zero-dimensional inputs of the source are trivial.

### The dichotomy

If any $a_i-b_i$ is nonzero, the scalar center of that single group supplies a one-parameter group scaling all coordinates of the whole input by a positive power of its parameter, using the inverse parameter when needed. Every orbit then has zero in its closure.

For balanced signatures the sum zero gives equality of scalar entries. Sum one gives ordinary conjugation of one matrix. Its closed orbit representative is determined by its characteristic polynomial. Indeed a Jordan form degenerates by diagonal changes of basis to the diagonal with these eigenvalues, and the characteristic polynomial is constant on the closure. Polynomial-bit computation of that polynomial decides the problem.

For balanced sum at least two, first suppose some label occurs at least twice on each side. The [single diagonal mixed quartic](PureMixedQuarticTOCI.md) embeds by tensoring identity pairs on all additional legs. If instead the occurrences are spread among distinct labels each of balanced multiplicity one, use the one-tensor two-label result just proved. In both embeddings normalized partial traces on the added pairs give an equivariant retraction, so enlargement preserves and reflects closure equivalence. This establishes the claimed dichotomy.

### Tuples of individually balanced signatures

The same dichotomy decides the complexity of any fixed tuple of balanced signatures. If one component has balanced sum at least two, embed that component and set all others to zero. The equivariant inclusion and projection give an exact reduction, so the tuple problem is TOCI-complete. Otherwise every non-scalar component is an endomorphism for one label. For each label, compare closure intersection of its simultaneous conjugation tuple independently.

Here is an explicit polynomial bit algorithm for that comparison. The simultaneous conjugation invariant ring is generated by traces of words, by the characteristic-zero matrix invariant theorem. Hence two tuples $(A_1,\ldots,A_m)$ and $(B_1,\ldots,B_m)$ have intersecting orbit closures exactly when those traces agree. Form $C_i=\operatorname{diag}(A_i,B_i)$ and compute the span of all products of the $C_i$. Start at the identity and repeatedly right-multiply each retained basis element by the generators, retaining a new product only when it is independent. When the span becomes stable under all right multiplications, it contains all words. Its dimension is at most twice the square of the side length, and the retained matrices can be chosen as words of length at most this dimension. The difference of the two block traces vanishes on every word exactly when it vanishes on this basis. Word lengths are polynomially bounded, so exact Gaussian elimination over the Gaussian rationals uses polynomial bit complexity. Scalar components are compared directly. [Trace invariants and simultaneous conjugation](https://arxiv.org/html/2411.04639v2#S1.SS1)

More generally, suppose all the nonzero central weights $\mathbf a-\mathbf b$ of the tuple lie in one open linear half-space through the origin, so that an integral linear functional is positive on every one of them. The corresponding central one-parameter subgroup degenerates every unbalanced component simultaneously to zero while fixing the balanced subtuple. Projection to the balanced subtuple is equivariant, and closure equivalence of the projected points also implies closure equivalence of the original points by this degeneration. The balanced-tuple dichotomy therefore also covers this case. The remaining signatures with mutually balancing nonzero central weights are outside this classification unless a single balanced hard component already gives completeness.
