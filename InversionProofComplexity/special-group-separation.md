# A single charged inversion separates proof size for succinct group isomorphism

This is an informal proof. The isomorphism variables in this result describe linear maps on the central quotient and the center of the groups.

**Theorem.** Fix a prime $p$. There are explicit pairs of nonisomorphic special $p$-groups of equal order $p^d$, with equal center and derived-subgroup orders, for infinitely many $d$. If $p$ is odd the groups have exponent $p$. If $p=2$ they have exponent four. In the quadratic inverse-witness equations for their succinct isomorphism problem over $\mathbb F_p$, every ordinary Polynomial Calculus (PC) refutation has degree $\Omega_p(d)$ and at least $2^{\Omega_p(d)}$ monomial occurrences. The same equations have PC+INV refutations of polynomial sparse size and degree at most five. Each refutation uses a single inversion whose matrices are written explicitly and have only zero or an original variable in each entry. The polynomial size includes those matrices and all premise references. With field axioms included the lower bounds still hold and the upper degree is at most $\max(5,p)$.

The underlying geometric statement about the equations remains valid after extension to any field of characteristic $p$ if field axioms are omitted. The bounds concern the commutator-map or square-map equations of a succinct presentation. A Cayley-table permutation encoding would have a different witness and size parameter.

## 1. Two group blocks

Let $J_{2a}$ be the direct sum of $a$ copies of the alternating form on a coordinate pair defined by $x_{2i-1}y_{2i}-x_{2i}y_{2i-1}$. Its rank is $2a$ in every characteristic. Each of the two block types has domain of dimension eight and central output of dimension two, with two separate alternating forms taking values in the two central coordinate lines.

- Type $K$ has $J_2$ and $J_6$ on disjoint coordinate subspaces.
- Type $L$ has $J_4$ and $J_4$ on disjoint coordinate subspaces.

Fix the order of coordinates as written. Choose a power $q=p^a\ge 3$, put $r=4q$ and $s=3q$, and take the direct-sum brackets $\beta_A$ and $\beta_B$ with respectively $r$ copies of $K$ and $s$ copies of $L$, and $s$ copies of $K$ and $r$ copies of $L$. Denote their domains by $V_A,V_B$ and their outputs by $C_A,C_B$. Over $\mathbb F_p$ the order exponent of either eventual group is $d=10(r+s)=70q$.

The groups have underlying set $V_A\oplus C_A$ or $V_B\oplus C_B$. For odd $p$ use
$$
(x,z)(y,w)=(x+y,z+w+\tfrac12\beta(x,y)).
$$
For $p=2$, replace the last term by the bilinear map $\gamma(x,y)$ that uses $x_{2i-1}y_{2i}$ in each chosen coordinate pair, taking values in its assigned central axis. This has polar commutator $\gamma(x,y)+\gamma(y,x)=\beta(x,y)$ and square map $Q(x)=\gamma(x,x)$. Bilinearity gives associativity in both cases, and the common radical of the central forms is zero because the bracket is nondegenerate on each of its complementary domain blocks. Also the bracket spans the entire central output. Thus both the center and the derived subgroup are precisely the elementary abelian central coordinates. The Frattini subgroup equals them because the quotient is elementary abelian and the derived subgroup already equals the center. For odd $p$ the powers are computed by $(x,z)^a=(ax,az)$ since the alternating bracket has zero diagonal. For $p=2$ the displayed square map is nonzero and its image is central elementary abelian, giving exponent four.

Every group isomorphism induces a pair of linear invertible maps $P:V_A\to V_B$ and $S:C_A\to C_B$. For odd $p$ it is necessary and sufficient to have
$$
S\beta_A(x,y)=\beta_B(Px,Py).
\tag{1}
$$
Necessity follows by taking commutators. Sufficiency follows from the displayed group law. For $p=2$ necessity is preservation of squares, and the exact condition is $S Q_A(x)=Q_B(Px)$. For sufficiency let $D(x,y)=S\gamma_A(x,y)-\gamma_B(Px,Py)$. This is bilinear with zero diagonal and hence symmetric in characteristic two. The polynomial $t(x)=\sum_{i<j}x_i x_j D(e_i,e_j)$ has polar form $D$. Then $(x,z)\mapsto(Px,Sz-t(x))$ is a group isomorphism by direct substitution in the group law. Equality of homogeneous quadratic coefficient polynomials in $x$ is equivalent to equality as functions over $\mathbb F_2$. Evaluations on single basis vectors and sums of two basis vectors recover all coefficients. Polarizing the square equation gives (1) by linear combination of coefficients, also over any extension field.

Use the coefficients of (1), or of the square-map equation in characteristic two, together with two-sided inverse equations for $P,S$ and their inverse witnesses $P',S'$. All these equations are at most quadratic in the formal witness variables. The field-axiom variant also includes $u^p-u=0$ for all witness entries $u$.

## 2. Short annotated refutation

Write $\beta_{A,i}$ and $\beta_{B,j}$ for the scalar forms named by the central coordinates. Fix a rank-two source channel $i$ and set $\lambda_j=S'_{ij}$. Multiplying (1) in the input modes by $P'$ and then in the output mode by $S'$ gives
$$
\beta_{A,i}(P'x,P'y)=\sum_j \lambda_j\beta_{B,j}(x,y).
\tag{2}
$$
This notation represents coefficient equations on target basis pairs. Expanding and reducing the inverse products gives an ordinary-PC derivation of degree at most five. Specifically, the two contractions by $P'$ multiply (1) by two entries of $P'$ at a time and reduce the products $PP'$. Multiplying the resulting identities by the entries of $S'$ and reducing $S'S$ gives (2). Each product expands to polynomially many monomials because the number of factors is bounded.

The left form of (2) has entries $a_u b_v-b_u a_v$, where $a$ and $b$ are the two rows of $P'$ for the symplectic pair of source channel $i$. For every four distinct target coordinates $u,v,w,z$, its Pfaffian identity is
$$
(a_u b_v-b_u a_v)(a_w b_z-b_w a_z)
-
(a_u b_w-b_u a_w)(a_v b_z-b_v a_z)
+
(a_u b_z-b_u a_z)(a_v b_w-b_v a_w)=0.
$$
The polynomial on the left cancels term by term, including in characteristic two. One factor replacement at a time in each of the three products, using the corresponding coefficient equation from (2), derives the Pfaffian equation for the right form in (2). The additional multipliers are single entries of the left or right form and have degree at most two. The proof-line degree of these replacements is at most four.

For any distinct $j,k$, use two coordinates forming the first symplectic pair of target channel $j$ and two forming the first pair of channel $k$. The target channels have disjoint coordinate supports. On these four coordinates the right form in (2) has the two isolated alternating pairs with weights $\lambda_j,\lambda_k$. Its Pfaffian is $\lambda_j\lambda_k$. This derives $\lambda_j\lambda_k=0$ for distinct $j,k$. For any target channel $k$ of rank at least four, choose the first two symplectic pairs in that same channel. Its Pfaffian is $\lambda_k^2$, so $\lambda_k^2=0$ is also derived.

The inverse equation in row and column $i$ of $S'S$ is $\sum_j \lambda_j S_{ji}=1$. Multiply by $\lambda_k$ for any channel $k$ of rank at least four. The preceding zero-product identities kill each summand, using the square identity at $j=k$ and the mixed identities elsewhere. This derives the linear equation $\lambda_k=0$ even without field axioms. The last calculation incurs degree at most three. Do this for each rank-two row $i$. It follows that the submatrix of $S'$ on the $r$ rank-two source rows has support only on the $s$ rank-two target columns.

Let $R$ be that $r$-by-$s$ submatrix and let $T$ be the opposite $s$-by-$r$ submatrix of $S$. The associated block of $S'S=I$ reduces to $RT=I_r$ upon deleting the just-proved zero terms. These equations alone imply nonisomorphism over any extension field by the rank inequality. In PC+INV use
$$
A_0=[\,R\mid 0\,],\qquad B_0=\begin{bmatrix}T\\0\end{bmatrix}.
$$
All entries of $A_0B_0-I_r$ are the proved $RT-I_r$ entries. A diagonal entry of $B_0A_0-I_r$ beyond the first $s$ positions equals $-1$. The inversion rule derives that entry and rescaling derives $1$. The two annotated matrices have $O(d^2)$ explicitly listed entries and $O(d^2)$ premise references. All entries are zero or an original variable. The preceding algebraic derivations use a constant number of factors per summand and a polynomial number of index choices, so the entire certificate including the annotation has polynomial sparse size. [PC+INV inference rule, Galesi–Grochow–Pitassi–She §2.3](https://arxiv.org/html/2305.19320#S2.SS3)

## 3. Sparse lower bound

Let $B_{r,s}$ be the rectangular bijection equations. The $r$-by-$s$ variable matrix $U=(u_{ij})$ has row and column sums one, Boolean entries, and zero products of two different entries of the same row or column. Assign the isomorphism variables the coordinate substitutions
$$
P\mapsto\operatorname{diag}(U^{\mathsf T}\otimes I_8,U\otimes I_8),\qquad
S\mapsto\operatorname{diag}(U^{\mathsf T}\otimes I_2,U\otimes I_2).
$$
Assign the inverses the transposes of the same matrices. The first rectangular block sends the $r$ source copies of type $K$ to the $s$ target copies of type $K$, and the second sends the $s$ source copies of type $L$ to the $r$ target copies of type $L$. The products in each substituted inverse equation are Gram blocks $U^{\mathsf T}U$ or $UU^{\mathsf T}$ tensored with identities. Off-diagonal entries vanish by collision axioms and diagonal entries equal one by the corresponding sums and Boolean axioms.

For an equation from (1) in a target channel, denote the entry of the corresponding copy-intertwiner block by $h_{ji}$ for target copy $j$ and source copy $i$. Inputs from distinct block types give zero on both sides by block support. Inputs from distinct copies of the same type give zero on the left, and each relevant right-hand coefficient has product $h_{ji}h_{j\ell}$ with $i\ne\ell$, hence vanishes by the rectangular collisions. For two inputs in the same copy $i$, the row-channel structure constant on the left has a factor $h_{ji}$, and on the right the same structure constant has a factor $h_{ji}^2$. These are equal by Boolean idempotence. In characteristic two the square-map coefficient equations have exactly the same accounting. Every nonzero monomial of the square map is one coordinate product within one block, and substituting $Px$ produces either repeated $h_{ji}$ factors in that block or the same products from distinct copies killed by collisions. The scalar-output map uses the same copy coefficients. Every projected bracket or square-map axiom thus has an ordinary-PC derivation with degree at most two and polynomial sparse size. A field axiom projects to zero or to a multiple of $u_{ij}^2-u_{ij}$ derived in degree at most $p$.

The substitution replaces witness variables by $0,1$ or individual rectangular variables. It never expands a monomial. Replaying an ordinary-PC refutation after the substitution and deriving the image axioms once would yield a rectangular bijection refutation of essentially the same sparse size up to polynomial overhead, with degree at most the larger of the original degree and a fixed constant depending on whether field axioms were included. The rectangular system $B_{4q,3q}$ has ordinary-PC degree $\Omega(q)$ and ordinary-PC sparse size $2^{\Omega(q)}$ in characteristic $p$. Its degree lower bound is the transpose of Riis's rectangular obstruction. Its sparse lower bound uses the random partial-matching restriction: fix $q$ rows by an injective matching, normalize by the Boolean and collision axioms, and apply Riis's degree lower bound to the remaining $3q$-by-$2q$ rectangle. A squarefree matching monomial of support $k$ survives with probability at most $(5/6)^k$, so a proof with fewer than $(6/5)^{q-1}$ monomials restricts to degree at most $q-1$, a contradiction. This is the previously established sparse-size lemma for these exact rectangles. Since $d=70q$, the two desired lower bounds follow. [Riis, Lemma 14.1](https://arxiv.org/html/2611.07280v1) · [Sparse rectangle lemma](https://github.com/Dugongue/MathProofs/blob/main/TensorSparsePCBounds/Proof.md)

## 4. Provenance and scope

Grochow and Qiao use the classical Baer correspondence between alternating commutator maps and class-two exponent-$p$ groups for odd $p$ in their succinct group-isomorphism completeness results. The constructions here use two fixed types of direct-product group blocks. The new step is making the rank-two label count available to low-degree PC with Pfaffian relations and an existing inverse witness. The exact same groups then realize the sparse lower bound from rectangular bijections and the explicit one-inversion certificate. This shows a charged proof-size separation within this succinct model, with no assumption about circuit hardness or annotation search. The proof is informal and publication priority is unestablished. [Grochow–Qiao, tensor isomorphism completeness and the Baer correspondence](https://arxiv.org/abs/1907.00309)
