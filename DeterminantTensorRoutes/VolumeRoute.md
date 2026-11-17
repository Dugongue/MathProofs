# Determinant pins from translated and Frobenius-deflated Pfaffians

We give a one-instance reduction to ordinary tensor isomorphism for the explicit classes below. The first result removes the sparse-polynomial requirement from the apolar volume pin. The second works deterministically on raw alternating tensors of unbounded widths over $\mathbb F_3$.

## 1. Recover apolar structure from polynomial evaluations

Let $F=\mathbb F_q$ have characteristic $p$. Let $Q\ne0$ be a homogeneous polynomial of degree $d$ on a vector space $S$, given by a polynomial-time evaluation procedure over extensions of $F$. Assume that the degree of $Q$ in each coordinate of its supplied basis is less than $p$. Its ordinary apolar algebra and top functional are
$$
 B_Q=\operatorname{Sym}(S)/\{D:D(\partial)Q=0\},\qquad
 \ell_Q([D])=(D(\partial)Q)(0).
$$
A monomial derivative of total degree $d$ detects a nonzero coefficient with an invertible factorial multiplier, so $\ell_Q\ne0$. Assume $h=\dim B_Q\le H$ for a supplied polynomial bound $H$. The multiplication table, generator map $S\to B_Q$, and functional $\ell_Q$ can be computed in randomized polynomial time with arbitrarily small inverse-polynomial error. The algorithm uses evaluations of $Q$.

**Translation basis.** Identify $B_Q$ as a vector space with the derivative span by $[D]\mapsto D(\partial)Q$. Write $T_i f(x)=f(x+e_i)$ and $D_i=\partial_i$. The coordinate degree bound gives
$$
             T_i=\sum_{j=0}^{p-1}D_i^j/j!,\qquad
             D_i=\sum_{j=1}^{p-1}(-1)^{j+1}(T_i-1)^j/j.
$$
Indeed $D_i^p=0$, and the exponential and logarithm identities modulo degree $p$ have invertible denominators. Terms beyond $d$ vanish. The derivative span is thus the span of the reachable translates $Q(x+a)$ under repeated unit-coordinate shifts, since the operators commute. Starting at $a=0$, shift every accepted basis vector in each coordinate and accept independent results. Each accepted vector is represented by its shift. At termination the accepted span is translation-stable and hence derivative-stable. It equals the full derivative span.

**Reconstruction and error bound.** Choose $H$ random evaluation points in a finite extension $K/F$. The evaluation matrix of a fixed true derivative basis at $h$ formal points has a nonzero determinant of degree at most $dh$. Independent evaluation functionals can be chosen one by one over the algebraic closure because a nonzero polynomial has a nonzero evaluation there. Thus injectivity on the entire derivative span fails with probability at most $dh/|K|$ by Schwartz–Zippel, covering all adaptive tests with one event. To make the bound at most $\varepsilon$, take a field of size at least $B=\max(2,\lceil dH/\varepsilon\rceil)$. If $q\ge B$, use $F$. Otherwise use an extension of the least degree with $q^{[K:F]}\ge B$. Testing monic polynomials for irreducibility by Frobenius takes polynomial time here because there are fewer than $qB\le B^2$ candidates. The field $F$ is supplied with an explicit representation.

On injectivity, the accepted translates form an exact $F$-basis. Their unique coordinates computed over $K$ for $F$-defined elements lie in $F$. For shifts $a,b$, the operator $\tau_a=\prod_i\exp(a_iD_i)$ represents $Q(x+a)$, and $\tau_a\tau_b=\tau_{a+b}$. Evaluate $Q(x+a+b)$ at the chosen points to recover the multiplication coefficients. Evaluate $Q(a)$ for $\ell_Q(\tau_a)$. Recover the coordinates of $D_i$ by applying the logarithm formula to the unit, using the needed coordinate shifts. The total bit cost is polynomial in $H,d,\dim S,\log q,1/\varepsilon$. On a fixed input, a successful injectivity event yields an exact result. Upon failure the algorithm can abort or produce an incorrect result, including either direction of error in the subsequent reduction. [Macaulay inverse systems](https://arxiv.org/abs/1705.05686) · [Schwartz, polynomial identity testing](https://doi.org/10.1145/322217.322225)

## 2. Frobenius deflation and a size bound for ordinary apolar pins

Suppose the Pfaffian $P$ of a raw alternating pencil satisfies $P=Q^{p^k}\ne 0$ as a formal polynomial, with $k$ supplied. Its root $Q$ is unique. Evaluate $Q$ in any finite extension by applying inverse $p^k$-Frobenius to the evaluated Pfaffian. Thus §1 applies when the deflated $Q$ has the stated degree and dimension bounds. The coordinate-degree bound follows if $\deg Q<p$. It also follows when every coefficient alternating matrix of $P$ has rank less than $2p^{k+1}$. A coefficient matrix of rank $2r$ can be put in alternating block form by congruence. A Pfaffian matching then uses at most $r$ entries from that coefficient matrix, so the degree in its coordinate is at most $r$, and deflation divides this bound by $p^k$. Evaluating a Pfaffian at a point takes polynomial time by elimination. The identity $\operatorname{Pf}(gAg^{\mathsf T})=\det(g)\operatorname{Pf}(A)$ holds in every characteristic. [Lauret–Oscari](https://arxiv.org/abs/1209.3060)

For any homogeneous $P$ of degree $m$ with ordinary differential functional $\ell_P\ne0$, the dimension of its ordinary derivative span is at least $p^{m/(p-1)}$. Indeed the remainder $\bar P$ modulo $(x_i^p)_i$ is nonzero, because a top-degree ordinary derivative requires a coefficient surviving this quotient. Reduction commutes with ordinary differentiation in characteristic $p$. Take a leading monomial $x^e$ of the remainder. Every derivative with multi-index $0\le a_i\le e_i<p$ has the distinct leading monomial $x^{e-a}$ with nonzero coefficient, so these derivatives are independent. This gives the lower bound $\prod_i(e_i+1)\ge p^{m/(p-1)}$, by concavity of the logarithm on $[1,p]$. Thus ordinary differentiation in fixed characteristic either loses the top functional or requires an exponential-in-degree space. Frobenius deflation can keep the functional at low degree.

## 3. Enforce the product of determinants along covariant flags

Suppose a tensor mode $V$ has a flag $0=U_0\subset U_1\subset\cdots\subset U_t=V$ recovered in polynomial time and covariant under every ordinary transporter of the input pair. Write $W_j=U_j/U_{j-1}$. Suppose we also recover covariant alternating form spaces $S_j\subseteq\Lambda^2 W_j^*$ with nonzero Pfaffians satisfying §§1–2. If the flags and pencils are supplied as extra structure without this covariance guarantee, the theorem concerns transporters that preserve the supplied structure.

Write $g_j:W_j\to W'_j$ and $s_j:S_j\to S'_j$ for the maps induced by a tensor transporter $g$. For $P_j=Q_j^{p^{k_j}}$, the pullback formula $g_j^{\mathsf T}S'_j(s_jx)g_j=S_j(x)$ implies
$$
             Q'_j(s_j x)=\det(g_j)^{-p^{-k_j}} Q_j(x),
$$
where $p^{-k_j}$ means inverse Frobenius on $F$. The chain rule gives an induced algebra isomorphism $\phi_j:B_{Q_j}\to B_{Q'_j}$, with
$$
             \ell_{Q'_j}\phi_j=\det(g_j)^{-p^{-k_j}}\ell_{Q_j}.
$$
The marked generator map forces $\phi_j$, since its image generates the unital ordinary apolar algebra. An invertible multiplicative map preserves the unit. Treat $\ell_{Q_j}$ as a map to an auxiliary one-dimensional module. Its scalar action is forced to be $\det(g_j)^{-p^{-k_j}}$, because the functional is nonzero.

Standard bilinear multiplication maps of one-dimensional modules impose that the output-line action is the product of the input-line actions. Use repeated squaring and multiplication to raise each functional line action to $p^{k_j}$, then multiply all $\det(g_j)^{-1}$ along an ordered chain. Fix the initial and final scalar lines. If $A,A'$ are the matrices of lifted quotient bases in the raw source and target bases, respectively, then
$$
             \det(g)=\frac{\det A'}{\det A}\prod_j\det(g_j).
$$
This follows from the block-triangular map in those bases. Prescribing raw determinant $\delta$ therefore requires the final inverse product $\det A'/(\delta\det A)$. Only the total product is prescribed. A logarithmic-dimension quotient can also use its explicit full exterior algebra and the action on its top line. Several modes can use independent product chains in the same instance.

**One ordinary TI instance.** Pack flag levels, quotient modules, pencil spaces, apolar algebras, and scalar lines in direct sums by relation type. Take a split label algebra $E=F^b$, its actions projecting onto the indexed summands, and a directed-path endomorphism of $E$ on its primitive idempotents. Algebra automorphisms permute the idempotents, and a permutation commuting with a directed path fixes them all. Thus the packed maps respect each index. Use one linear shift map to encode consecutive inclusions in each flag, one packed quotient map, and a fixed terminal map to each raw mode. Use componentwise apolar multiplication, and pack the generator, functional, and form-evaluation maps by type. One bilinear map on the packed scalar lines records all indexed multiplication triples, including repeated inputs for squares.

The number of module and relation types is constant. Compile these data to a partitioned 3-tensor with the original tensor as another relation. A linear map has one scalar padding slot. A bilinear map has two dual inputs and a covariant output, and a trilinear scalar evaluation has three dual slots. Reserve a scalar anchor line per mode whose actions have product one, enforced by their scalar tensor entry. For each sort put covariant and dual cores in each mode. Padded identity entries joining opposite variance and different modes form a six-cycle, synchronizing the normalized covariant maps and their inverse-transpose dual maps. Normalization divides by the same-mode anchor action. Every relation uses fresh non-scalar slot copies linked to the corresponding cores. This gives the exact shared action. Remove partitions in turn by the constant-part construction of Part V, Theorem 3.12. Its reverse extracts the data blocks in the other modes, and its forward extends them block diagonally. Thus restrictions on untreated modes persist. Each query tensor has polynomial explicit size and is over the original $F$. The randomized construction has two-sided error at most the chosen bound by a union bound over the source and target pencils. [Grochow–Qiao–Stange–Sun, Theorem 3.12](https://arxiv.org/html/2611.00735v1#S3.SS3.SSS2)

## 4. A deterministic raw all-mode reduction over F₃ with unbounded widths

Let $T\in V\otimes V\otimes U$ have alternating slices $A_x$ on its two $V$ modes in the supplied common coordinate frame. Suppose $\dim V=2m$, $m=3^k$, and $\dim U$ is odd. Require
$$
          \{D\in\operatorname{End}(V):D A=A D^{\mathsf T}
                       \text{ for every slice }A\}=F_3 I .
$$
Let $S$ be the span of the slices. Assume its formal Pfaffian is the nonzero $3^k$-th power of a linear form $L$ on $S$. For both raw tensors satisfying these promises, determinant-one TI in all three modes reduces deterministically to one ordinary TI instance over $\mathbb F_3$ in polynomial time. The Pfaffian condition is a formal polynomial promise. Alternation, dimensions and the scalar condition are checkable by linear algebra. The identity $P=L^{3^k}$ is certified algebraically for the explicit family below. For arbitrary candidate inputs the difference can also be tested by random evaluations in a sufficiently large extension, giving a one-sided test for the promise.

For an ordinary transporter $(g,h,u)$, alternation of the target slices gives $g A h^{\mathsf T}=h A g^{\mathsf T}$ for every source slice. Multiplying by $g^{-1}$ and $g^{-\mathsf T}$ gives the scalar condition for $D=g^{-1}h$. Thus $h=\lambda g$ and $\det h=\det g$, since $2m$ is even and $\lambda\in F_3^\times$. Also $gSg^{\mathsf T}=S'$, because multiplication by $\lambda\ne0$ leaves the span unchanged. Therefore the raw slice span is covariant as a bivector space on the first mode for every ordinary transporter.

Recover $L$ in any computed basis $A_i$ of $S$ by $L(A_i)=\operatorname{Pf}(A_i)$, since Frobenius acts trivially on $F_3$. Covariance and formal root uniqueness give
$$
                  L'(gAg^{\mathsf T})=\det(g)L(A).
$$
Append the bivector-space evaluation relation on the first mode and the pin $L'\circ s=L$ on the induced slice-space map $s$. These are a trilinear and a linear relation and use the compiler in §3. The evaluation relation forces $s$, and the pin holds exactly when $\det g=1$. This enforces $\det h=1$ as well. If $\det u=-1$, replace the triple by $(-g,h,-u)$. It is still a transporter, its first determinant is unchanged, and its third determinant switches sign. In reverse every all-mode determinant-one transporter extends to the appended relations. The reduction is deterministic under the two-sided raw promise.

**Explicit family.** For $m=3^k\ge3$, take the alternating slice space of all
$$
         \begin{pmatrix}
         0 & x I_m+N\\
         -(x I_m+N)^{\mathsf T} & C
         \end{pmatrix},
$$
with $N$ strictly upper triangular and $C$ alternating. Use independent slices, so the third dimension is $1+m(m-1)$, which is odd. The Pfaffian is a fixed sign times $\det(xI_m+N)=x^m$, since every perfect matching pairs all the first $m$ coordinates with the last $m$. To check the scalar condition, write $D$ in four $m\times m$ blocks. The lower-right alternating slices force the upper-right block of $D$ to vanish and its lower-right block to be scalar. Substituting $C=E_{ij}-E_{ji}$ and reading rows outside $i,j$ gives all off-diagonal entries zero, and reading the $i,j$ entry equates diagonal entries. The slice with $x=1$ and $N=C=0$ forces the same scalar in the upper-left block and makes the lower-left block $Z$ alternating. Substitution of $N=E_{ij}$ for $i<j$ gives $Z E_{ij}=-E_{ji}Z^{\mathsf T}$. The $j$-th column and the diagonal entry force $Ze_i=0$, using odd characteristic. Thus the first $m-1$ columns of $Z$ vanish, and alternation forces the last to vanish. All three mode widths grow without bound. This family demonstrates the size of the raw scope. The sufficient hypotheses do not cover arbitrary tensors.
