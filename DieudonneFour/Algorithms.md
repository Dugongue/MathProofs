# Exact isomorphisms and transporter counts for finite Dieudonné modules

Let $k=\mathbb F_{p^u}$ be a specified finite field, let $W(k)$ be its Witt ring, and let $\sigma$ be Witt Frobenius. A finite Dieudonné module here is a finite-length $W(k)$-module with additive $F,V$ that are respectively $\sigma,\sigma^{-1}$-semilinear and satisfy $FV=VF=p$. The input consists of explicit cyclic additive coordinates and the matrices of the named operators. All isomorphisms are over the specified $k$. By Cartier–Dieudonné theory this also compares the corresponding finite commutative group schemes of $p$-power order once their Dieudonné data are supplied. [Mondal, Dieudonné theory via cohomology](https://doi.org/10.1017/fms.2021.77) · [Illusie, Dieudonné theory over a perfect field](https://www.imo.universite-paris-saclay.fr/~luc.illusie/Illusie-Pisa5.pdf)

**Theorem.** Given two such modules, one can decide isomorphism, construct an isomorphism when one exists, and compute the exact number of isomorphisms in deterministic polynomial bit time. The bound is polynomial in the explicit operator and marker data, the number of additive coordinates, and the full precision $e\log p$, where $p^e$ kills both modules. It permits a specified list of labelled subgroups, each given by additive generators, with isomorphisms carrying every marked subgroup onto its counterpart. The same algorithm applies to finite abelian $p$-groups with any common list of named additive endomorphisms.

The counting algorithm recovers the sizes and multiplicities of the simple matrix factors in a semisimple endomorphism quotient. It uses modular linear equations, the deterministic associative radical algorithm, and linear algebra over $\mathbb F_p$. It requires no finite-field polynomial factorization, construction of primitive idempotents, or enumeration of group elements. In particular the dependence is on $\log p$ at fixed precision exponent, with no assumption that $p$ is small.

## 1. Compute liftable reductions of endomorphisms

The additive presentation of a module is $N=\bigoplus_{i=1}^n\mathbb Z/p^{e_i}\mathbb Z$ with one matrix each for the scalar action of a lift $\theta$ of a field generator, $F$, and $V$. The element $\theta$ generates $W_e(k)$ over $\mathbb Z/p^e\mathbb Z$. Indeed $1,\theta,\ldots,\theta^{u-1}$ reduce to a basis of $k/\mathbb F_p$ and are a basis of the unramified ring by reduction modulo $p$. Thus commutation with the three matrices is exactly $W(k)$-linearity and commutation with $F,V$. Their semilinearity in Witt coordinates poses no additional constraint after passage to the additive coordinates.

A presentation by Witt summands $W_{e_i}(k)$ and semilinear coefficient matrices also gives these data in polynomial time. Present the unramified ring by a monic lift of a defining polynomial for the named realization of $k$. In that presentation $\sigma(\theta)$ is the unique root of this polynomial with residue $\bar\theta^p$, obtainable by successive Hensel lifts, since the derivative at that residue is nonzero. Use $\sigma^{-1}=\sigma^{u-1}$ for $V$. Evaluating on $1,\theta,\ldots,\theta^{u-1}$ in each summand gives the additive matrices. This input convention charges for the precision $e\log p$.

For isomorphism, take $N=X\oplus Y$ with the block-diagonal named operators. Its labelled subgroups, when present, are $\Lambda_i^X\oplus\Lambda_i^Y$. Let $E$ be the ring of endomorphisms of $N$ commuting with all named operators and preserving each labelled subgroup. Write a proposed endomorphism as entries $z_{ij}$ modulo $p^{e_i}$, and impose
$$
 p^{e_j}z_{ij}\equiv0\pmod{p^{e_i}},
 \qquad (ZT-TZ)_{ij}\equiv0\pmod{p^{e_i}}
$$
for each named matrix $T$. Preservation of a subgroup with generator list $\Lambda$ is the linear condition $\pi_\Lambda Zx=0$ on each generator $x$, where $\pi_\Lambda:N\to N/\Lambda$ is found by additive Smith reduction. This avoids introducing a different presentation of the endomorphism for each subgroup.

Use variables modulo $p^e$, where $e=\max_i e_i$. Multiply each constraint by the appropriate power of $p$ to read it modulo $p^e$. Modular Smith elimination obtains generators of the solution group and its order. Explicitly, a nonzero pivot of minimum valuation divides every remaining entry. Scale it to $p^v$, clear its row and column, and continue. An equation $p^v x=0\bmod p^e$ leaves $p^v$ possible values. Free variables contribute $p^e$. Each endomorphism has exactly $\prod_{i,j}p^{e-e_i}$ representatives modulo the common modulus, so dividing by that factor gives $|E|$. Reducing a generator list of the solutions gives additive generators of $E$. Each matrix and congruence has polynomial bit size. [Ciocănea-Teodorescu, finite-ring module isomorphism](https://arxiv.org/abs/1512.08365) · [Kannan–Bachem on integer normal forms](https://doi.org/10.1137/0208040)

There is a computable surjective ring map onto its image
$$
 \rho:E\longrightarrow A:=\rho(E)\subseteq
 \operatorname{End}_{\mathbb F_p}(N/pN).
$$
Reduce the generators of $E$ and retain a basis of their span. Store one lift for each basis element. This makes the multiplication of $A$, or a lift of any element of $A$, available by ordinary matrix and linear operations. In general $A$ is the image of **actual** endomorphisms under reduction. The full commutant of the reduced operators alone can be bigger.

Write $I=\ker\rho$. Each member of $I$ sends $N$ into $pN$ and sends $p^jN$ into $p^{j+1}N$. Therefore $I^e=0$. The quotient maps on unit groups are surjective, and the kernel of $E^\times\to A^\times$ is $1+I$. Indeed, lifting both a unit and its inverse produces products that differ from $1$ by elements of $I$, which one inverts by a finite geometric series. This also shows explicitly that every lift of an invertible reduced endomorphism is a unit.

## 2. Search through right ideals over the prime field

Let $e_X,e_Y\in A$ be the images of the two direct-sum projections, and use the right $A$-modules $e_XA,e_YA$. Obtain matrices for right multiplication by an algebra basis of $A$ on both ideals. A constructive deterministic finite-field module-isomorphism algorithm tests whether these two ideals are isomorphic and returns a witness. They have dimensions at most $n^2$ over $\mathbb F_p$. [Brooksbank–Luks, Theorem 3.5](https://ix.cs.uoregon.edu/~luks/ModIso.pdf)

A right-module isomorphism is left multiplication by $a\in e_YAe_X$. Its inverse is left multiplication by $b\in e_XAe_Y$, with $ba=e_X$ and $ab=e_Y$. These elements are the images of the respective generators $e_X,e_Y$ under the module maps. Arbitrary lifts in $E$, multiplied by the actual direct-sum projections on either side, give named-operator intertwiners $X\to Y$ and $Y\to X$. They give inverse linear maps after reducing modulo $p$. An additive map surjective modulo $p$ is surjective because its finite $p$-group cokernel equals $p$ times itself and vanishes. The two lifts are therefore bijective. Write $g:X\to Y$, $g':Y\to X$ for the lifts. The product $g'g$ is the identity modulo $p$ and is a unit of the marked endomorphism ring of $X$, by the nilpotent argument. Thus the inverse $(g'g)^{-1}g'$ respects the marks, and $g$ carries the marked subgroups onto their counterparts. Conversely an actual module isomorphism and its inverse give the corner elements and therefore right-module isomorphisms. The zero modules can be compared directly.

This constructive isomorphism conclusion is a specialization of known finite-ring module-isomorphism results. For example, one may use the finite additive ring of operators generated in $\operatorname{End}(N)$, growing its additive span by products with the named generators. The reduction above also supplies precisely the quotient used for counting. [Ciocănea-Teodorescu](https://arxiv.org/abs/1512.08365)

## 3. Count units without splitting the semisimple factors

For counting, run Section 1 on $N=X$ alone. Use the deterministic associative radical algorithm on the finite-dimensional $\mathbb F_p$-algebra $A$, and form $S=A/J(A)$ from the resulting basis. By Wedderburn–Artin and the finite division-ring theorem, $S$ is a product of factors $M_n(\mathbb F_{p^f})$. The following steps read the numerical factor types without constructing this product isomorphism. [Friedl–Rónyai, Theorem 1.5A](https://www.cs.uoregon.edu/Reports/TR-1985-003.pdf)

**Recover the matrix sizes from the center.** Compute $C=Z(S)$ by the linear equations for commutation. It is abstractly a product of the center fields. Let $W$ be a finite $C$-module given by action matrices over $\mathbb F_p$. For $v\in W$ the annihilator $\operatorname{Ann}_C(v)$ is an ideal, computed as a linear kernel. Every ideal of $C$ has its own identity idempotent. Find it by solving $u x=x$ for each basis element $x$ of the ideal, with $u$ constrained to belong to the ideal. Existence follows from the product-of-fields structure, and the constraints force uniqueness.

Start with $v=0$, then process an $\mathbb F_p$-basis $w$ of $W$. At each step add $u w$ to $v$, where $u$ is the identity of $\operatorname{Ann}_C(v)$ for the current $v$. In the abstract product, this keeps the already nonzero components of $v$ unchanged and adds the current basis vector on the slots where $v$ vanishes. At the end $v$ is nonzero in every component of $W$ that occurs. The complementary idempotent $1-u$ is the identity on precisely those components, and $Cv$ has dimension one over each field that occurs there. Quotient $W$ by $Cv$, compute the induced $C$-action, and repeat until $W=0$.

Apply this procedure starting at $W=S$ under central multiplication. Let $\eta_i$ be the computed support idempotent at the $i$-th step, and put $\eta_i=0$ after termination. A factor $M_n(\mathbb F_{p^f})$ has dimension $n^2$ over its center. Thus $\eta_i-\eta_{i+1}$ is the central idempotent selecting factors whose matrix size squared is exactly $i$. The supports are intrinsic even though the cyclic vectors used to compute them can vary.

**Recover the field degrees on each stratum.** Put $C_i=(\eta_i-\eta_{i+1})C$, write $B=\dim_{\mathbb F_p} C_i$, and let $m_f$ count its field factors of degree $f$. On this commutative algebra the map $\Phi:x\mapsto x^p$ is $\mathbb F_p$-linear and obtained by repeated squaring on basis vectors. For $1\le j\le B$, compute
$$
 b_j=\dim_{\mathbb F_p}\ker(\Phi^j-1)
    =\sum_{f=1}^B m_f\gcd(j,f).
$$
A finite field of degree $f$ contributes the fixed field of degree $\gcd(j,f)$. Write $a_d=\sum_{m\ge1}m_{md}$. Then
$$
 b_j=\sum_{d\mid j}\varphi(d)a_d
$$
by $\gcd(j,f)=\sum_{d\mid j,\,d\mid f}\varphi(d)$. Recover the $a_j$ in increasing $j$, subtracting the proper divisor terms and dividing by $\varphi(j)$. Recover $m_f$ in decreasing $f$ by subtracting the higher multiples. All integer indices are bounded by $B$, so straightforward divisor tabulation suffices. This gives all multiplicities $\nu_{n,f}$ of the simple factors.

Finally $E^\times\to S^\times$ is surjective with fibers of cardinality $|E|/|S|$, by the nilpotent kernel first for $E\to A$ and then for $A\to S$. Thus
$$
 |E^\times|=
 \frac{|E|}{|S|}
 \prod_{n,f}
 \left(\prod_{j=0}^{n-1}(p^{fn}-p^{fj})\right)^{\nu_{n,f}} .
$$
The inner product counts ordered bases over $\mathbb F_{p^f}$. If $X\cong Y$, composition with one isomorphism is a bijection from $\operatorname{Aut}(X)$ to the transporter. Otherwise its count is zero. The number of support steps is at most $\dim_{\mathbb F_p} S$, all algebras have dimension at most $n^2$, and the integer output has at most $en^2\log_2 p+1$ bits. Each stated operation therefore has polynomial bit complexity.

## 4. Finite-field controls and scope

- **One geometric $BT_1$ type, two rational classes.** Over $\mathbb F_3$, take generators $x,y$ with $Fx=y$, $Vx=cy$, and $Fy=Vy=0$, with $c=1$ or $2$. Over $\overline{\mathbb F}_3$, rescaling $x'=a x$, $y'=a^p y$ gives coefficient $c a^{1/p-p}$ in $Vx'$, and this can be made $1$. Both modules have Kraft word $fv$. Over $\mathbb F_3$ the two operators are linear and $V=c F$, so $c$ is an isomorphism invariant. Enumeration of the $3^4$ matrices gave six automorphisms of either module and zero isomorphisms between them. [Pries–Ulmer, Section 3](https://math.arizona.edu/~ulmer/research/papers/2021c.pdf) · [Pink–Wedhorn–Ziegler, $F$-zips](https://arxiv.org/abs/1208.3547)
- **Reduction loses integral information.** On $\mathbb Z/4\mathbb Z$ compare $F=1$ and $F=3$, each with $V=2$. The reduced modules agree. The cross maps commuting with $F$ are the two even multipliers, and neither is an isomorphism.
- **Mixed cyclic lengths.** On $N=\mathbb Z/4\mathbb Z\oplus\mathbb F_2$ with $F=1,V=2$, the endomorphism matrices have the form $\left(\begin{smallmatrix}a&2b\\c&d\end{smallmatrix}\right)$, with $a\bmod4$ and $b,c,d\bmod2$. Enumeration gave $32$ endomorphisms and $8$ automorphisms.
- **Two different simple factor types.** On $(\mathbb Z/4\mathbb Z)^4$, take $F=I_2\oplus C$ with $C$ the companion of $t^2+t+1$, and $V=2F^{-1}$. The cross blocks vanish as $C-I_2$ is a unit, and the two diagonal endomorphism factors are $M_2(\mathbb Z/4\mathbb Z)$ and $(\mathbb Z/4\mathbb Z)[t]/(t^2+t+1)$. Exhaustive block calculations gave $|E|=4096$ and $|E^\times|=1152$. The semisimple quotient is $M_2(\mathbb F_2)\times\mathbb F_4$, and the formula gives $64\cdot6\cdot3=1152$.

The computational problem starts from Dieudonné operator coordinates over a common named finite field. Conversion from arbitrary Hopf algebra presentations is a separate task. The bounds use named operators and keep those marks throughout, in the spirit of the distinction between simultaneous matrix problems and tensor actions that also move generator coordinates. Grochow–Qiao's counting-to-decision results address substantially larger isomorphism actions. [Grochow–Qiao, counting-to-decision](https://doi.org/10.1145/3625308) · [Grochow–Qiao, commutative rings](https://doi.org/10.1145/3717823.3718286)

General module isomorphism and arithmetic on finite endomorphism rings have substantial prior algorithms. Full effective decompositions of semisimple algebras may invoke factoring, and Skresanov's unit-generator theorem allows polynomial dependence on $p$. The specific comparison here is exact transporter **counts** from numerical types in polynomial time in $\log p$, using elementary center-module stripping and Frobenius fixed-space dimensions after computing the radical. Publication priority for this counting combination remains unverified. The proof is in prose. [Eberly–Giesbrecht, Wedderburn decomposition](https://cs.uwaterloo.ca/~mwg/files/wedderburn_issac.pdf) · [Skresanov, Theorem 1.6](https://arxiv.org/abs/2602.15497)
