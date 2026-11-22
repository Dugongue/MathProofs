# Polynomial Calculus degree under arbitrary tensor direct sums

Let $k$ be any field, and write $T,S$ for equal-format three-tensors with no isomorphism over an algebraic closure. Use the literal cubic action and quadratic two-sided inverse equations from Galesi–Grochow–Pitassi–She. Denote the tensors' largest flattening rank by $n$, allowing $n=0$ for the zero tensor. Split their supported tensors into indecomposable direct summands over the algebraic closure. Let $D$ be the maximum of the ordinary Polynomial Calculus degrees of the nonisomorphic, equal-format pairs of these summands, over the algebraic closure, with $D=0$ if there are none.

**Theorem.** The original TI equations have a Polynomial Calculus refutation, without field equations, of degree
$$
\max\{D+2,\ O(n+1)\}.
$$
In characteristic zero, and in characteristic greater than $n$, the bound improves to $\max\{D+2,\ O(1)\}$. The constants are absolute. The argument permits nilpotents in the centroid of every summand. As a consequence, any fixed bound on one flattening rank in each indecomposable summand of the source gives a polynomial-in-rank upper bound for its comparison with arbitrary targets. The bounded mode may vary between summands.

This result uses degree falls in ordinary Polynomial Calculus. It is a sufficient case for Question 7.1 for a summably closed class. [Galesi–Grochow–Pitassi–She, Question 7.1](https://arxiv.org/abs/2305.19320)

## 1. Supported tensors and the three-mode centroid

Adapt constant bases to the flattening supports, separately on the two inputs. Apply inverses in the other two modes to the action equation and cancel their inverse products. The equations that remain on rows outside the target support assert that the corresponding rows of the action map vanish when composed with the fixed source flattening. A constant right inverse of the full-row-rank supported flattening shows that the bottom left block of the action map vanishes. Apply the reverse action to obtain the same statement for the inverse map. Supported blocks of the two inverse equations are now actual two-sided inverses, with the rectangular version if support ranks differ, by removing terms multiplied by the vanished blocks. All these are ordinary PC derivations in constant degree: substitution of constant linear forms, addition, and multiplication by a bounded number of variable entries suffice. Unequal supported dimensions give a refutation in degree $O(n+1)$ by applying Cauchy–Binet to the larger identity, or in constant degree by comparing traces when the dimension difference is a nonzero scalar in $k$. If both tensors have zero support they are both zero, which is a positive comparison. Henceforth consider concise tensors of equal supported format.

For $T\in V_1\otimes V_2\otimes V_3$, write $A^{[i]}$ for the action of $A\in\operatorname{End}(V_i)$ in slot $i$ only. Define the centroid
$$
C_T=\bigl\{(A_1,A_2,A_3):A_1^{[1]}T=A_2^{[2]}T=A_3^{[3]}T\bigr\}.
$$
These constant linear equations define a space that commutes with scalar extension. Conciseness makes $A\mapsto A^{[i]}T$ injective in each slot, by contracting against the other slots. Each centroid component representation is therefore faithful. The centroid is a commutative, unital algebra with componentwise composition. To see commutativity, for any centroid elements $A,B$ move $B^{[1]}$ to slot 2, commute $A^{[1]}$ past it and move $A^{[1]}$ to slot 3. Commute the two remaining operators and move $B^{[2]}$ back to slot 1. Moving $A^{[3]}$ on $T$ back to slot 1 gives $A_1B_1$ and $B_1A_1$ acting equally on $T$. Injectivity gives equality on $V_1$, and the same argument works for the other slots. Closure under componentwise multiplication follows by moving both operators to the same other slot, commuting across slots, and using the just established componentwise commutativity.

An idempotent $e=(e^{(1)},e^{(2)},e^{(3)})$ of $C_T$ gives a tensor direct sum by splitting each $V_i$ into its image and kernel. In fact $e^{[1]}T=e^{[2]}T=e^{[3]}T$ belongs to all three image supports, and the complementary action belongs to all three kernels. Conversely each such direct sum gives a centroid idempotent. A nonzero idempotent has nonzero image in each mode by faithfulness. Over an algebraically closed field the finite-dimensional commutative algebra $C_T$ is a product of local algebras with residue field $k$. Its primitive idempotents thus give exactly the indecomposable tensor blocks, independent of any decomposition chosen at the outset. In particular, isomorphism of the whole supported tensors is equivalent to equality of the two multisets of geometric block isomorphism classes: any transporter conjugates the centroid and permutes primitive idempotents, and conversely compatible block transporters assemble by direct sum.

## 2. Transport the centroid in constant proof degree

Write $P_i,P'_i$ for the forward and inverse variables, and define $\Phi(A)_i=P_i A_i P'_i$ and $\Psi(B)_i=P'_i B_i P_i$. They transport $C_T$ and $C_S$ in both directions modulo consequences of constant degree of the TI equations. For example, apply $\Phi(A)$ in a given slot to $S=(P_1\otimes P_2\otimes P_3)T$ and cancel $P'_iP_i$. The result is $(P_1\otimes P_2\otimes P_3)A_i^{[i]}T$ and is independent of $i$. For each constant linear system defining a centroid, choose a projection onto its kernel. Any vector minus its projection is a fixed linear image of the residual of the system, by restricting to a complement of its kernel. Hence one can replace all transported coefficients by polynomials in the fixed centroid bases, with their linear-expression identities derivable in constant degree. Work with these projected maps from here on.

The forward and reverse maps preserve multiplication and the unit, and are mutually inverse, with coordinate identities derivable in constant degree. For products, use adjacent inverse equations to cancel the middle pair in each slot of $\Phi(A)\Phi(B)$, using the projection equations to compare the basis expressions. For inverse composition cancel on both the left and right. Every calculation involves only a bounded number of matrix products with entries of degree at most two and substitutions into fixed linear equations. Thus all identities continue to be derivable in constant degree when their constant arguments are replaced by bounded-degree polynomials in fixed centroid bases.

We can pass to a finite extension where the two centroids have all their geometric primitive idempotents. Their finite-dimensional algebras are defined over $k$, so the decompositions are given by finitely many algebraic coefficients. Work there and continue to write $k$ during the argument.

## 3. Degree-falling removal of the centroid radical

Let $e_i$ be the primitive idempotents of $C_T$, and let $f_j$ be those of $C_S$. The Jacobson radical $J$ of $C_S$ is a fixed nilpotent ideal, and the product decomposition identifies $C_S/J$ with one copy of $k$ per $f_j$. The residue coordinates $\alpha_{ji}$ of $\Phi(e_i)$ are polynomials of degree at most two. By the multiplication identities their entries are idempotents modulo the TI equations. Fix $i$ and abbreviate
$$
F=\Phi(e_i),\qquad
G=\sum_j\alpha_{ji}f_j,\qquad
h=F-G.
$$
The fixed residue-coordinate projection makes $h$ a polynomial with coefficients in $J$ identically. Both $F,G$ are idempotent with constant-degree proofs. In a commutative algebra the difference of two idempotents satisfies $h^3=h$, in every characteristic. This follows by expanding $(F-G)^3$ and using $F^2=F,\ G^2=G$, and all coordinates have constant-degree derivations on the original system.

Use a basis adapted to the filtration $C_S\supset J\supset J^2\supset\cdots\supset 0$. Suppose the degree-at-most-two coordinates of $h$ outside $J^a$ have already been derived as zero. Replace $h$ by its fixed projection $h_a$ onto $J^a$ in $h^3$, using the telescoping difference of the cubes, or expanding and subtracting products containing an already zero coordinate. The multipliers have degree at most four. Thus $h=h_a^3$ is derivable in the same absolute degree bound at each stage. The coordinates of $h_a^3$ outside $J^{3a}$ are identically zero. Deduce the degree-at-most-two zero coordinates of $h$ outside $J^{3a}$, and repeat starting at $a=1$. Nilpotence ends the induction. The low-degree coordinate lines are used immediately at each step, so no growing exponent is expanded. This proves
$$
\Phi(e_i)=\sum_j\alpha_{ji} f_j
$$
in absolute constant ordinary PC degree. The same proof gives $\Psi(f_j)=\sum_i\beta_{ij}e_i$, where $\beta_{ij}$ are again degree at most two.

By transporting units, products, and orthogonality of primitive idempotents, derive
$$
\sum_i\alpha_{ji}=1,\qquad \alpha_{ji}\alpha_{ji'}=0\ (i\ne i'),\qquad \alpha_{ji}^2=\alpha_{ji}
$$
and the corresponding equations for $\beta$. Comparing $\Psi(f_j\Phi(e_i))$ in the $e_i$ coordinate gives $\beta_{ij}=\alpha_{ji}\beta_{ij}$, and the reverse comparison gives $\alpha_{ji}=\alpha_{ji}\beta_{ij}$. Thus $\beta_{ij}=\alpha_{ji}$ in constant degree. In particular the rows and columns of $\alpha$ have sum one and pairwise orthogonal entries.

## 4. Discharge incompatible pairs one at a time

Fix one source block $i$ and one target block $j$, and abbreviate $a=\alpha_{ji}$. In each mode restrict the forward map to source $i$ and project to target $j$, obtaining a matrix $U$, and restrict and project the inverse similarly, obtaining $V$. The two transported-projector equations give
$$
UV=aI_{\text{target }j},\qquad VU=aI_{\text{source }i}.
$$
For example, in the full coordinates the first product is $f_j^{(s)}P_s e_i^{(s)}P'_s f_j^{(s)}$, which is $af_j^{(s)}$ by the conjugation of projectors in mode $s$. The second uses $\Psi$ and $\beta_{ij}=a$.

If the block dimensions differ in that mode, take the trace difference when it is a nonzero scalar. Otherwise take the determinant of the larger rectangular product. It vanishes identically by Cauchy–Binet, and telescoping the determinant difference gives a certificate for $a^h=0$, where $h$ is the larger dimension, using degree $O(h+1)$. Derive $a=0$ in that degree from $a^2=a$. More precisely, in characteristic $p>0$ one may use the coefficient of $t^{p^{v_p(u-v)}}$ in the Sylvester determinant identity $\det(I+t UV)=\det(I+t VU)$, where $u,v$ are the two dimensions. Cauchy–Binet gives this coefficient identity by equality of the sums of corresponding square minors. The difference of the two binomial coefficients of that order is nonzero, by the first differing base-$p$ digit of $u,v$. The certificate uses degree $O(1+p^{v_p(u-v)})$.

Suppose the shapes agree and the two blocks are nonisomorphic. Let $U_s,V_s$ be these restricted matrices in mode $s$. The compositions already give $a(U_sV_s-I)=a(V_sU_s-I)=0$ via $a^2=a$. For the block action, first observe that the target projection of $P_s e_i^{(s)}$ is $a f_j^{(s)}P_s$, by the projector equation and cancellation of the adjacent inverse variables. Apply this in each slot of
$$
(U_1\otimes U_2\otimes U_3)T_i
  = (f_j^{(1)}P_1 e_i^{(1)}\otimes
     f_j^{(2)}P_2 e_i^{(2)}\otimes
     f_j^{(3)}P_3 e_i^{(3)}) T .
$$
The result is $a^3 S_j$ by the global action. Multiply the local action by $a$ and use idempotence so this gives $a((U_1\otimes U_2\otimes U_3)T_i-S_j)=0$. All the initial multiplied equations have absolute-constant degree proofs.

Take a degree-at-most-$D$ ordinary PC refutation of this block pair. Substitute the indicated block matrices for its witness variables, which are linear forms in global witness variables. Simulate each line multiplied by $a$, using the initial multiplied equations just derived. Linear combinations are unchanged and multiplication by a local variable is simulated by multiplication by its substituted linear form, using additions and variable multiplications. Thus every simulated line has degree at most $D+2$, and final line is $a=0$. This is an ordinary PC derivation and does not assume a Nullstellensatz certificate for the local refutation.

Do this separately for all incompatible pairs. If a geometric isomorphism class has different multiplicities on the two sides, restrict the rectangular matrix $\alpha$ to the rows and columns of that class. All incompatible entries vanish so the restriction has ones for all its row and column sums, with unchanged row and column orthogonality and degree-two entries. When the difference in multiplicities is a nonzero scalar, subtract the sum of all row sums from the sum of all column sums. Otherwise the matrix times its transpose, in either order, is the corresponding identity. Cauchy–Binet applied to the larger identity refutes the system in degree $O(n+1)$, since there are no more than $n$ nonzero blocks in either tensor. The case where the class is absent on one side also follows immediately from a row or column sum. If every class has equal multiplicity, the whole tensor comparison is positive by the centroid decomposition theorem, contrary to hypothesis. This completes the refutation over the splitting field.

A bounded-degree PC proof over an extension descends to the base field without increasing degree. Choose a base-field vector space basis of the finite extension containing $1$. For each proof line derive all its coordinate polynomials over the base field, by simulating extension-field linear combinations by the constant multiplication table in the basis. Multiplication by an indeterminate acts independently on coordinates. The final component at $1$ equals $1$. If more algebraic coefficients were used in selecting local refutations, enlarge the finite extension to contain them before this simulation.

## 5. Polynomial rank bound for independently bounded modes

A tensor of ordinary or geometric border rank at most $r$ has every flattening support of dimension at most $r$, by the determinantal rank conditions. Every indecomposable direct summand is obtained by projection in all three modes, so it has at most these support dimensions as well.

Suppose the source has the following property after passage to an algebraic closure: in every indecomposable direct summand, at least one mode has dimension at most $s$, for fixed $s$. For two blocks of equal format paired in Section 4, both then have a mode of dimension at most $s$ in the same mode. The earlier fixed-mode Nullstellensatz proof gives degree $(2+3r)^{O(s^2+1)}$ on that pair, with the literal TI axioms. The theorem above uses these local proofs with no additional field equations and gives the same polynomial-in-$r$ exponent for the full comparison. The theorem covers arbitrarily many blocks, varying positions of the small mode, and arbitrary nilpotent structure in the centroid. It also transfers any stronger local bounds proved by ordinary PC, in contrast to a method requiring bounded-degree Nullstellensatz representations of all local proofs. [Earlier fixed-mode proof](https://github.com/Dugongue/MathProofs/blob/fa1001c4a32d65711c2864f4bdfa1257a44e333b/NavierStokesGrochowTransfers/BoundedModeTensorPC.md)

## 6. A degree bound for Laurent binomial systems

This statement provides a separate way to handle a transporter once its remaining unknowns act by scalar weights. Let $x_1,\ldots,x_m$ have named inverses $y_1,\ldots,y_m$, with axioms $x_i y_i-1=0$. For $a\in\mathbb Z^m$, let $M(a)=\prod_i x_i^{\max(a_i,0)} y_i^{\max(-a_i,0)}$. Assume $m,d\ge1$ and let the remaining equations be $M(a_j)=c_j$ with $c_j\ne0$ and $\|a_j\|_1\le d$. If there is no solution over the algebraic closure, the literal equations have a degree-at-most-$\max\{(m+1)d,2\}$ ordinary PC refutation without any field axioms.

Indeed, the assignment $a_j\mapsto c_j$ fails to extend multiplicatively to the subgroup $L=\sum_j\mathbb Z a_j$. Otherwise use Smith normal form to choose bases in which $L$ is generated by integer multiples of coordinate vectors. The homomorphism $L\to\overline k^\times$ then extends to all of $\mathbb Z^m$ by taking roots over the algebraic closure. Such an extension gives a torus solution, in any characteristic. Thus there are integers $z_j$ with $\sum_j z_j a_j=0$ but $\prod_j c_j^{z_j}\ne1$. When one $a_j$ is zero and its scalar is not $1$, that axiom already refutes the system.

Write the relation as a sequence of signed steps $b_1,\ldots,b_M$, where each step is $a_j$ or $-a_j$ with the corresponding weight $c_j$ or $c_j^{-1}$ and with the prescribed multiplicity. By the Steinitz rearrangement theorem for the $\ell_1$ norm, the signed steps can be ordered so that each partial sum $s_i=\sum_{\ell\le i}b_\ell$ has $\|s_i\|_1\le md$. The number of occurrences of a step need not be small. [Grinberg and Sevast'yanov, Value of the Steinitz constant](https://doi.org/10.1007/BF01086559)

A negative step equation is derived by multiplying $M(a_j)-c_j$ by $M(-a_j)$ and canceling inverse pairs, in degree at most $2d$. Proceed along the walk, deriving at position $i$ that $M(s_i)$ equals the product of the first $i$ weights. Multiply the previous relation by $M(b_i)$ and use the current step relation. Cancel inverse pairs one at a time by subtracting monomial multiples of $x_i y_i-1$. No intermediate degree exceeds $\|s_{i-1}\|_1+\|b_i\|_1\le(m+1)d$. Since $s_M=0$ but the total scalar weight is different from one, the last line is a nonzero constant. For a binomial $M(u_j)=c_j M(v_j)$ with both monomials of degree at most $d$, the normalized step $M(u_j-v_j)=c_j$ is derivable in degree $2d$ by first multiplying by $M(-v_j)$ and canceling. The normalized steps then have norm at most $2d$, so this more general input encoding has degree bound $2(m+1)d$.

The number of proof lines can also be bounded independently of the multiplicities in the original relation. If the walk repeats an exponent with the same cumulative scalar before the first inconsistent repetition, delete the segment between those two visits. Subsequent exponents and cumulative scalars remain unchanged. If instead a repeated exponent has different cumulative scalars, their two derived lines contradict immediately. Therefore at most one more than the number of integral points of $\ell_1$ norm at most $md$ need be visited. This number is at most $2^m\binom{md+m}{m}\le (2e(d+1))^m$, by choosing signs and counting nonnegative coordinate magnitudes with sum at most $md$. The binomial derivations above use a polynomial number of two-term lines per step, so the sparse proof size is at most $(2e(d+1))^m\operatorname{poly}(m,d)$ for normalized steps. In particular it is singly exponential with constant base for fixed $d$.

These are written arguments. The bounded small-mode corollary and the degree-falling compositionality theorem are scoped answers to Question 7.1. In particular when the supported tensor is indecomposable, its local comparison can still be the entire original question.
