# Characteristic-two ordered tuple isometry with a commutative adjoint quotient

**Informal theorem.** Let $A$ be an explicitly presented finite-dimensional unital algebra over a finite field of characteristic two, with involution $*$ and Jacobson radical $J$. Given a self-adjoint unit $c$, if $A/J$ is commutative, one can determine whether $u^*u=c$ and return a solution and the exact number of solutions in Las Vegas polynomial bit time. No bound on the nilpotency index of $J$ is needed. The involution may act nontrivially on a residue field or exchange field factors. After a radical basis and a split presentation of $A/J$ have been obtained, the lifting algorithm is deterministic.

Consequently, for ordered matrix tuples over a finite characteristic-two field, the isometry problem is in Las Vegas polynomial time on the checkable subclass with commutative semisimple adjoint quotient. The raw matrices are the inputs. This extends the characteristic-two case of Grochow, Qiao, Stange and Sun's question in Part V, §1.4, beyond bounded radical length. The paper asks for polynomial time for arbitrary matrix tuples over fields of characteristic two. [Part V](https://arxiv.org/html/2611.00735v1#S1.SS4).

## 1. Exact radical fibers

For a unit $w$, use the right action $a^w=w^*aw$. Let $U=1+J$. It acts trivially on every $J^k/J^{k+1}$. For self-adjoint $b$ set
$$
K_k=\{w\in U:b^w\equiv b\bmod J^k\}.
$$
For $w\in K_k$, the map $\delta_k(w)=b^w-b\bmod J^{k+1}$ is an additive homomorphism to $J^k/J^{k+1}$. Indeed the right-action identity gives $\delta_k(wv)=\delta_k(w)^v+\delta_k(v)$, and $v$ acts trivially on the grade. Its kernel is $K_{k+1}$.

Given $a\equiv b\bmod J$, start at $w=1$ and $K_1=U$. If $a^w\equiv b\bmod J^k$, all current candidates are $wK_k$. To advance, solve
$$
\delta_k(v)=-(a^w-b)\pmod {J^{k+1}},\qquad v\in K_k.
$$
If feasible replace $w$ by $wv$ and $K_k$ by its kernel. This gives one radical lift and the stabilizer of all such lifts at every requested depth. As needed, a supplied residue $s$ is handled by taking an arbitrary lift $h$ and running this routine on $a^h,b$. Such a lift is a unit because its quotient is a unit. This routine works for every radical, with commutativity of $A/J$ irrelevant.

Here are explicit polynomial group operations for the routine. Refine the descending chain of powers of $J$ by additive $\mathbb F_2$ flags into $J=J_1\supset\cdots\supset J_{M+1}=0$ with index two at each step and $JJ_i+J_iJ\subseteq J_{i+1}$. Then the groups $1+J_i$ constitute a central series of index two. Every group element other than $1$ has a first nonzero position in this flag. A generating sequence uses at most one element $g_i$ for each first position $i$. Sift an element by removing its leading position using $g_i$, inserting its residual at the first missing position. Begin with the supplied generators, and sift squares and pairwise commutators of installed entries, restarting the tests when an entry is added. At most $M$ insertions occur. On completion an induction up the flag gives unique binary normal forms: the deeper entries generate the tail subgroup, the commutator tests ensure the next entry normalizes the tail, and the square test places its square in the tail. A leading position prevents two distinct normal forms from agreeing. In particular the sequence length is the binary logarithm of the generated subgroup's order.

For a homomorphism to an elementary abelian group, the images of the current entries are columns of a binary matrix. Solve preimages by Gaussian elimination and multiply the specified entries. For the kernel, form an echelon basis of the binary nullspace and convert each row to its normal-form group product. These kernel elements have distinct leading positions. Repeated leading-position removal generates the whole kernel, because the normal form of any kernel element lies in the nullspace. Thus computing kernels does not cause exponential growth of the generator lists. A generating sequence for $U$ itself is given by one $1+x$ with $x\in J_i\setminus J_{i+1}$ at every flag step.

The same proof works for an explicit finite $\mathbb Z/2^e\mathbb Z$-algebra in additive module coordinates. The element $2$ lies in $J$, so $J^k/J^{k+1}$ is an elementary abelian 2-group and the same flags exist. Compute products, kernels, submodule spans and quotient coordinates using integer module linear algebra. The number of flag steps is at most $\log_2|A|$, polynomial in the explicit module model. Sun's Appendix A uses unipotent vector transport and radical cosets for matrix tuples over $\mathbb Z/p^\tau\mathbb Z$. The fixed-residue principle overlaps that method. The selection of all viable residues without enumeration below is the additional step. [Sun, Lemma A.24 and Appendix A](https://arxiv.org/pdf/2611.05920).

## 2. The residue group's action on the defect

Assume $S=A/J$ is commutative. Compute $J$ and present $S$ as a product of finite fields $E_i$. The involution defines an involution $i\mapsto i^*$ on the index set and a field isomorphism $E_i\to E_{i^*}$. Write $C=U(S,*)$. A self-dual field with identity involution contributes a trivial factor, since $s^2=1$ has a unique solution. A self-dual field with nontrivial involution contributes the norm-one torus. An exchanged pair contributes $E_i^\times$, with the second component determined by the involution and the inverse of the first. Thus $C$ is a product of odd-order groups, with the indicated concrete field coordinates.

The residue equation $\bar a^*\bar a=\bar c$ always has a solution. In a self-dual field take the square root in its fixed field. In an exchanged pair choose one coordinate to be 1 and solve the other coordinate. Lift such an $\bar a$ and replace $c$ by $(a^*)^{-1}ca^{-1}$ to arrange $c\equiv1\bmod J$. Multiply any solution on the right by $a$ to recover the original solution.

Let $G$ be the preimage of $C$ in $A^\times$. For a lifting grade $k$, define
$$
H_k=\{h\in G:c^h\equiv c\bmod J^k\},\quad
C_k=\operatorname{im}(H_k\to C),\quad
M=J^k/J^{k+1}.
$$
The kernel is the group $K_k$ from Section 1, with $b=c$. The involution on $M$ is compatible with its $S$-bimodule structure. Put $M^+=\{x:x^*=x\}$ and $T(M)=\{x+x^*:x\in M\}$. The image $R$ of $K_k$ under $\delta_k$ contains $T(M)$, by using $1+x$ for $x\in J^k$ and $c\equiv1\bmod J$. The subspace $R$ is stable under $C_k$. In fact if $h\in H_k$ lifts $s$, the cocycle identity yields $\delta_k(h^{-1}vh)=\delta_k(v)^s$ for $v\in K_k$. On $W=M^+/R$ the map $\delta_k$ consequently defines a computable right cocycle
$$
d(st)=d(s)^t+d(t),\qquad d(s)\in W,
$$
on $C_k$. Each evaluation uses a lift of $s$ into $H_k$, constructed by Section 1. Different lifts give the same value in $W$.

We describe the $C$-module $M^+/T(M)$ before quotienting by the additional subspace $R/T(M)$. The involution interchanges the Peirce blocks $e_iMe_j$ and $e_{j^*}Me_{i^*}$. A pair of distinct blocks contributes zero to the quotient, since a fixed sum across the pair equals the trace of one of its terms. In a fixed block $e_iMe_{i^*}$ identify its right center with $E_i$ by $b\mapsto b^*$. Its twist spaces are
$$
M_\theta=\{x:xa^*=\theta(a)x\text{ for every }a\in E_i\},
$$
indexed by the field automorphisms of $E_i$ over $\mathbb F_2$. They give a direct sum, since $E_i\otimes_{\mathbb F_2}E_i$ splits into these field factors. The involution swaps the $\theta$ and $\theta^{-1}$ spaces and acts $\theta^{-1}$-semilinearly on left scalars. Distinct inverse twists disappear from the trace quotient as above. For $\theta=\theta^{-1}\ne1$, choose $b$ with $b+\theta(b)=1$. A fixed vector $x$ is the trace of $bx$, so this twist also disappears.

The surviving twist is $\theta=1$. The star is $E_i$-linear on it, and its fixed/trace quotient is an $E_i$-vector space. A residue unitary acts there by multiplication by $s_i^{-2}$: on the left $(s^*)_i=s_i^{-1}$, and on the right the element $s_{i^*}$ is identified with the same scalar. For an exchanged pair, choose the first field as coordinates on both sides. The two surviving blocks have scalar actions $u^{-2}$ and $u^2$ for the one free parameter $u\in E_i^\times$. Thus each nontrivial torus factor acts only on its own summands. Every nonidentity parameter acts without fixed nonzero vectors on those summands.

All these descriptions are computable using bases and linear equations over $\mathbb F_2$. In particular one can test the twist equations for every basis scalar and enumerate every Frobenius automorphism of an explicit finite field. This avoids any need to compute a primitive multiplicative generator.
## 3. Selection of all viable residue coordinates

We maintain that $C_k$ is a product of some of the full nontrivial factors of $C$, with every other coordinate pinned to identity. At $k=1$ this is true since $c\equiv1\bmod J$.

For a factor free in $C_k$, let $V_i$ be the sum of its one or two nontrivial summands of $M^+/T(M)$, as just described. All other summands are trivial for $C_k$. This decomposition descends to $W$. To see this, choose one nonidentity residue $u_i$ in the free factor. Its linear action minus the identity vanishes on every other summand and is invertible on $V_i$. Therefore the projection to $V_i$ is a polynomial in that difference over $\mathbb F_2$. For example take a polynomial multiple of $X$ congruent to $1$ modulo the minimal polynomial of the invertible restriction, whose constant term is nonzero. The $C_k$-invariant subspace $R/T(M)$ is stable under the projection and hence splits into these components. One can compute the projectors directly by linear algebra, or form the component quotients using intersections with $R/T(M)$. Denote the corresponding quotient again by $W_i$. The remaining quotient $W_0$ has trivial action.

On $W_0$ the cocycle is zero, since it is a homomorphism from an odd-order group to a 2-group. On $W_i$ the cocycle vanishes for coordinates other than $i$ for the same reason. For the $i$-coordinate, evaluate the cocycle at the chosen $u_i$. The coordinate is available without constructing a multiplicative generator. In an exchanged factor take any field unit other than 1. In a nontrivial self-dual norm-one torus, take $x/x^*$ for some $x$ outside the fixed field. Solve $z_i^{u_i}-z_i=d(u_i)_i$ in $W_i$, which is possible and unique since $u_i-1$ is invertible there. Commutativity gives
$$
d(s)^{u_i}-d(s)=d(u_i)^s-d(u_i),
$$
so $d(s)_i=z_i^s-z_i$ for every $s$. With the trivial component zero, let $z=\sum_i z_i$. Then $d(s)=z^s-z$. This recovers the affine shift from one residue-fiber query per free factor.

Now suppose $a=1^w$ matches $c$ modulo $J^k$ for a current candidate $w\in G$. Write $e=a-c\bmod J^{k+1}$, an element of $M^+$. A residue $s\in C_k$ permits advancement exactly when
$$
(e+z)^s=z\quad\text{in }W.
$$
Indeed $a^h-c$ at the next grade is $e^s+\delta_k(h)$ for a lift $h$ into $H_k$, and its class in $W$ is $e^s+z^s-z$. If the class is zero, use a radical element $v\in K_k$ to cancel the grade in $R$ by the elementary-abelian homomorphism computation in Section 1. The new candidate is $whv$. Failure of the equation for all $s$ gives a correct rejection, since every solution at the old grade is in $wH_k$.

The equation in $W$ is solvable factor by factor. On $W_0$ it just requires $e=0$. On $W_i$ it is a scalar matching problem, with the following details when the two reciprocal characters occur together.

- A self-dual nontrivial torus lives in $E=\mathbb F_{2^{2d}}$ and has order $2^d+1$. Its image under $u\mapsto u^{-2}$ is the same torus, which spans $E$ over $\mathbb F_2$. The span is a subfield because it is closed under multiplication. No proper subfield has enough nonzero elements to contain the torus. Thus invariant subspaces, and the resulting quotient, are $E$-linear.
- For an exchanged pair with $E=\mathbb F_{2^d}$, each of the two scalar action types spans its entire copy of $E$. For $d\ge3$ they are inequivalent simple $\mathbb F_2$ representations of $E^\times$. An equivalence would make inversion on $E^\times$ a field automorphism, which would require $2^d-1$ to divide $2^j+1$ for some $0\le j<d$. This is impossible. Semisimplicity for the odd-order group splits an invariant subspace across these two types, so the quotient splits too. For $d=2$, applying Frobenius to one summand identifies the reciprocal action with the same scalar action on both components. For $d=1$ the group is trivial.

The $E$-linear scalar equation in any nonzero vector component is injective as a linear equation in the multiplier. Compute the unique multiplier by linear algebra over $\mathbb F_2$, take the corresponding inverse square root or square root, and check membership in the required torus and all other components. If a component has zero source vector it requires zero target vector. Thus the full system either rejects, allows every parameter in a free factor, or fixes a unique parameter.

The next group image satisfies $C_{k+1}=\{s\in C_k:d(s)=0\}$. This follows from the same radical correction with $e=0$. On $W_i$ every nonidentity $s_i$ has no nonzero fixed vectors, so the equation $z_i^{s_i}=z_i$ either pins that coordinate to 1 or allows the whole torus. This proves the induction hypothesis for the next grade. Begin with $w=1$ at $k=1$ and continue until the grade with $J^k=0$. There are at most $1+\log_2|J|$ grades. Each grade uses a polynomial number of fixed-fiber queries, field-linear operations, and integer module operations where applicable.

The final solutions are a coset of $H_k$. Its exact size is $|K_k|\prod_{i\ \mathrm{free}}|C_i|$, with $|K_k|$ computed from the binary normal forms. This counts the witnesses without enumerating any torus. The arbitrary-radical argument also applies to an explicit finite $\mathbb Z/2^e\mathbb Z$-algebra with the same commutative semisimple-quotient hypothesis. The additive module and multiplication presentation suffice. Its Jacobson radical can be computed as the preimage of the radical of $A/2A$, since $2A$ is a nilpotent ideal.

## 4. From raw ordered tuples to the norm problem

For tuples $(A_i)$ and $(B_i)$ over a finite field, append their transposes and use module isomorphism for the associated Kronecker representation to find a left–right equivalence $X^tA_iY=B_i$. Reject if none exists. Form
$$
\mathcal A=\{(L,R):L^tA_i=A_iR\ \text{ for all }i\},
$$
with multiplication $(L,R)(L',R')=(LL',R'R)$ and involution $(L,R)^*=(R,L)$. The transpose closure makes it an algebra with involution. Set $D=YX^{-1}$ and $c=(D,D)$. The equivalence equations and their transposes show that $D^tA_i=A_iD$, so $c$ is a self-adjoint unit. A norm solution has $RL=D$ and gives the isometry $P=LX$, since
$$
P^tA_iP=X^tA_iRLX=X^tA_iY=B_i.
$$
Conversely an isometry $P$ determines the norm solution $(PX^{-1},YP^{-1})$. These maps are inverse, and so the norm count is the isometry count.

The algebra $\mathcal A$ is computed by linear equations and its structure constants by multiplying basis elements. Finite-field module isomorphism and semisimple decomposition have Las Vegas polynomial-time algorithms. Compute the Jacobson radical and the matrices for the induced involution, test whether the quotient is commutative, and use the algorithm above on that class. The extra randomization is in these standard preprocessing routines, with the lifting and counting procedures deterministic. [Ivanyos–Qiao on the adjoint reduction](https://arxiv.org/abs/1708.03495), [Rónyai on explicit finite algebra decomposition](https://doi.org/10.1016/S0747-7171(08)80017-X).

## 5. Two other cases with no radical depth bound

**A residue unitary 2-group.** More generally, if $U(A/J,*)$ is a 2-group and a polynomial-size list of its generators and one residue norm solution are supplied, the norm problem and exact count are polynomial-time. Normalize the target by that solution as above. Lift a generator list of the residue group and adjoin generators of $1+J$, giving the entire preimage $G$. This is a 2-group. Its faithful left regular representation and the congruence representation both have invariant flags with trivial quotients, found by solving common fixed-vector systems successively on the quotients. Every 2-group over characteristic two has a common fixed vector in every nonzero module, by the action on its underlying finite additive space. In an upper unitriangular faithful representation, refine superdiagonals into a central series of index two and use the group arithmetic of Section 1. Use the congruence invariant flag to impose successive target coordinates. At each coordinate the stabilizer of the previous coordinates acts by an additive defect homomorphism, exactly as in the radical fiber routine. This gives one transporter and generators and order of its stabilizer. Applying Sun's unipotent transporter algorithm to $G$ gives another route. The explicit generator promise is automatic for quotients whose nontrivial factors are first-kind, nonalternating symmetric 2-by-2 factors. Over a finite perfect field of characteristic two their isometries are the symplectic isometries in dimension two fixing the canonical nonzero characteristic vector, an additive field group. [Sun, Appendix A](https://arxiv.org/pdf/2611.05920).

**Surjective grade traces.** Suppose each map $x\mapsto x+x^*$ on $J^k/J^{k+1}$ surjects onto the self-adjoint part of that grade. This condition is checkable by linear algebra. Then every residue norm solution lifts, regardless of matrix-factor sizes. Normalize by any lift of a residue solution and suppose the current norm is correct modulo $J^k$. Congruence by $1+x$ with $x\in J^k$ changes its next grade by $x+x^*$; solve the corresponding linear system and iterate. A central $b$ with $b+b^*=1$ suffices for grade trace surjectivity, by choosing $x=be$ for each fixed error $e$. Existence of such a central $b$ is itself a linear test. A supplied involution-preserving algebra section $A/J\to A$ gives a different sufficient condition for full residue selection. After normalization every unitary residue has a unitary lift via the section, so the norm problem reduces to the identity radical fiber. This section condition does not assert surjectivity of the norm map on $1+J$.

Sun already gives the general radical and unipotent transporter machinery, including an algorithm for matrix tuples that enumerates semisimple quotient candidates. The new step proved here avoids semisimple enumeration for every commutative adjoint quotient, including arbitrary involution and radical length. This is a restricted answer to the published characteristic-two polynomial-time question. The general semisimple matrix-factor case may produce stabilizer images more complicated than independent tori, and requires an additional selection argument. Publication priority for the restricted all-depth result has not been established.
