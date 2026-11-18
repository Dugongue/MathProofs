# The sixteen unresolved elementary coarse-graining rules

In the Song–Grochow elementary setting, an exact coarse-graining at block size \(N\) is a nonconstant map \(h: \mathbb F_2^N\to\mathbb F_2\) intertwining one \(N\)-step block update with one step of a target elementary rule. Use the census convention \(N\ge2\). None of the sixteen source rules left unresolved in the historical census admits such a coarse-graining to any elementary target. More generally they are the only elementary source rules with no outgoing nonconstant coarse-graining at any permitted block size. This second assertion concerns existence of some target. [Song–Grochow, §§II, IV–V](https://arxiv.org/html/2012.12153) · [Israeli–Goldenfeld historical census](https://guava.physics.ucsd.edu/~nigel/REPRINTS/2006/Israeli%20Coarse-graining%20of%20cellular%20automata%20PRE%202006%20%28PDF%29.pdf)

## The all-size obstruction

Work over \(\mathbb F_2\). Suppose the source rule has the form \(A(l,c,r)=l+g(c,r)\) where \(g\) is nonlinear. Then \(g(c,r)=cr+\alpha c+\gamma r+\delta\) with binary constants. Reflection interchanges left and right, so this handles both nonlinear one-sided permutive cases.

Use input blocks \(L,C,R\) on positions \(-N,\ldots,-1\), \(0,\ldots,N-1\), and \(N,\ldots,2N-1\). Let \(F_i=(A^N x)_i\) for \(0\le i<N\). A site after \(t\) steps is permutive in its leftmost input at distance \(t\): follow the unique extreme path recursively, on which every left derivative is 1. Hence for fixed \(C,R\), the block map from \(L\) to the evolved center block \(F\) is bijective, by triangular recovery starting with the rightmost input in \(L\). A nonconstant binary \(h\) is onto. The equation
\[
h(F)=B(h(L),h(C),h(R))
\]
then forces \(B\) to be left permutive, for every fixed target center and right bit, since varying \(L\) makes the left side attain both values. Thus \(B(l,c,r)=l+g_B(c,r)\), without requiring \(g_B\) to be nonlinear.

Let \(j\) be the largest essential coordinate of \(h\), counting from 0. Take the Boolean derivative in the input coordinate \(x_{j+N}\). Only \(F_j\) among \(F_0,\ldots,F_j\) depends on that coordinate, and the unique far-right path yields
\[
\Delta_{x_{j+N}}F_j=\Phi(x)=
\prod_{t=0}^{N-1}\big((A^t x)_{j+N-1-t}+\gamma\big).
\]
Each factor uses the center state next to the extreme path at that step. That center does not depend on the toggled coordinate because its rightmost possible input is \(j+N-1\). The earliest input of factor \(t\) is \(j+N-1-2t\), and the factor is permutive in it. These pivots are distinct and decreasing as \(t\) increases. Choose them in this order to achieve \(\Phi=1\), keeping all earlier factors fixed.

The left derivative in the coarse-graining equation is
\[
\Phi(x)\cdot \Delta_j h(F_0,\ldots,F_{j-1}).
\]
The right derivative is independent of \(L\), since the \(h(L)\) term cancels. At a configuration with \(\Phi=1\) freely change the left inputs \(x_{s-N}\) for \(0\le s<j\). The earliest possible input of any factor of \(\Phi\) is \(j-N+1\), so \(\Phi\) is unchanged. These left inputs realize every prefix \((F_0,\ldots,F_{j-1})\) by the same triangular permutivity. Thus \(\Delta_j h\) is constant. Since \(j\) is essential it is 1.

Consequently the right derivative is exactly \(\Delta_r g_B(h(C))\), independent of the whole right block, while the left derivative is \(\Phi\). If \(j\ge1\), start at a configuration with \(\Phi=1\) and toggle \(x_{j+N-1}\) in the right block. This flips factor \(t=0\) to zero, contradicting independence of the right block. Hence \(j=0\), so \(h(x)=x_0+c\) for a fixed bit. If \(N\ge2\), start again with \(\Phi=1\) and toggle \(x_{N-1}\). This flips the first factor to zero while leaving \(h(C)\) unchanged. This final contradiction proves the all-size obstruction. All steps allow arbitrary target rules.

## Checking the historical rules and the positive side

The eight nonlinear rules of the displayed left-permutive form have rule numbers \(30,45,75,120,135,180,210,225\). Reflection gives \(86,89,101,106,149,154,166,169\). This follows directly by reading the eight truth values in Wolfram order and requiring nonzero coefficient of \(cr\) in \(g\). The historical list comprises the symmetry classes represented by 30, 45, 106 and 154. The list is reproduced by the finite checker beside this proof.

All remaining source rules have a coarse-graining. For a reportable finite check, compute the range language of a one-step source update with a four-state labeled graph. Its vertices are the pairs of bits, and the edge \((a,b)\to(b,c)\) is labeled \(A(a,b,c)\). Start from all four states. Follow subset transitions on output bits. A word is missing precisely if it reaches the empty subset, since the input segment extends to a full configuration. Breadth-first search of the sixteen subsets decides this and returns a missing word when one exists. The replay establishes that the surjective rules are exactly the fourteen nonconstant affine rules and the sixteen obstructed rules. Every nonsurjective rule has a missing word \(w\), which can be padded to length at least two. Use block size equal to its length and \(h\) the indicator of the word. Every block output after any positive number of source steps belongs to the one-step range, so \(h\) sends all evolved blocks to zero. This is a nonconstant coarse-graining to the constant-zero rule. In particular the four extra source rules \(37,91,164,218\) that were unresolved through size seven have witnesses at size nine.

For a nonconstant affine source write its update as \(a+P(S)\) with \(S\) the shift operator and Laurent polynomial \(P(S)=a_-S^{-1}+a_0+a_+S\). Then \(P(S)^2=P(S^2)\), so the block projection to the first coordinate at \(N=2\) gives an affine elementary rule, with the same linear coefficients and the appropriate iterated constant. Constant rules also coarse-grain at every size. Together these cases establish the full outgoing-existence census, with 240 positive and 16 negative sources.

## All block sizes and all targets for affine sources

If \(P=0\), the only targets are constant rules, and each is possible. If \(P\) has one term, the only targets are the same shift or same stay, possibly followed by a complement. The uncomplemented option works at every size \(N\ge2\) by parity of two block coordinates. The complemented option works exactly when the source has \(a=1\) and \(N\) is odd, by projection to one coordinate. These limitations follow because after \(N\) steps the output block is just the corresponding input block, possibly complemented.

Suppose \(P\) has two or three terms. At least two input slots of the block update have invertible linear action. Both extremes are triangular invertible when present. In the case of an extreme and a stay, the extreme block is triangular invertible, and the center block is triangular with diagonal coefficient 1 because the Laurent support lies to one side and the stay coefficient is 1. Permutivity transfers to the same two target slots by surjectivity of \(h\), forcing the binary target to be affine. Fix the third block and vary the two active blocks. Their separate invertible contributions to the evolved block, together with the affine target, imply an equation \(h(x+y+z)=f(x)+g(y)+b\) for all \(x,y\) and fixed \(z,b\). Subtracting the instances with one argument zero gives the additive Cauchy equation for \(h-h(0)\), so \(h\) is affine.

Write its nonzero coefficient row as \(H(S)\) and its offset as \(c\). Comparing the linear parts of the two updates gives \(H(S)P(S)^N=P_B(S^N)H(S)\). Cancel the nonzero Laurent polynomial \(H\). Put \(N=2^r s\) with \(s\) odd and remove the common Frobenius power. If \(s>1\), a nonzero root of \(P\) has multiplicity at least \(s\) in \(P^s\). Such a root exists because \(P\) has at least two terms. Every nonzero root of \(P_B(S^s)\) has multiplicity at most two, since \(P_B\) has Laurent width at most two and the map \(S\mapsto S^s\) is separable away from zero. This contradiction proves \(s=1\) and then \(P_B=P\).

Finally the affine offset must satisfy
\[
a_B=(1+P(1))c+H(1)a\sum_{j=0}^{N-1}P(1)^j.
\]
When \(P\) has two terms, \(P(1)=0\), so either target offset is attainable by the choice of \(c\). When it has three terms, \(P(1)=1\) and \(N\) is an even power of two, so the target offset is zero. These conditions suffice by substitution in the same identity. This resolves all target and size possibilities for affine sources. The all-size criterion for arbitrary negative pairs with nonsurjective source and a specified nonconstant target is a separate question. The proofs here are informal.

## Unary fixed-block decision cannot be NEXP-hard

Use the literal elementary model with two fixed-width rule codes and a unary block length. At each string length there are at most \(256^2\) well-formed instances, so the yes language is sparse. If this language were NEXP-hard under deterministic polynomial-time many-one reductions, then it would be NP-hard. The sparse-hard-set form of Mahaney's theorem yields \(\mathsf{P}=\mathsf{NP}\). This form requires no membership assumption on the target language. The standard proof prunes a SAT self-reduction list with the reductions of \(\varphi_1\lor\varphi_i\). Duplicate images allow removal of one of the redundant \(\varphi_i\). More distinct images than the sparsity bound implies that one disjunction is unsatisfiable, allowing removal of \(\varphi_1\). [Sparse NP-hard sets and Mahaney's theorem](https://arxiv.org/abs/1610.05825)

The sparse target is in \(\mathsf{P/poly}\) by listing its polynomially many yes strings as advice. Therefore NEXP-hardness also gives \(\mathsf{EXP}\subseteq\mathsf{P/poly}\). The Babai–Fortnow–Lund collapse yields \(\mathsf{EXP}=\mathsf{MA}\). Since \(\mathsf{MA}\subseteq\mathsf{PH}\) and \(\mathsf{P}=\mathsf{NP}\) collapses \(\mathsf{PH}\) to \(\mathsf{P}\), this contradicts the deterministic time hierarchy. Hence the unary elementary language cannot be NEXP-complete under the indicated reductions. Together with deterministic exponential time from the expanded block table and Boolean-algebra homomorphism algorithm, this answers the unary alternatives of the fixed-block question. The sparsity proof uses the fixed binary rule alphabets and unary input length. [Babai–Fortnow–Lund collapse, restated as Theorem 3](https://eccc.weizmann.ac.il/report/2002/055/revision/1/download/) · [Boolean structure homomorphisms](https://arxiv.org/abs/2010.04958)
