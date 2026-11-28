# Deterministic isomorphism tests for étale algebras

The algorithms assemble classical polynomial factorization results and the trace-tensor reconstruction.

## 1. Theorem A: étale-algebra isomorphism is in P (classical)

**Theorem A.** Given two étale $\mathbb Q$-algebras $A,B$, by multiplication tables or as products of $\mathbb Q[x]/(f_i)$, one can decide $A\cong B$ in deterministic polynomial time, and output an isomorphism when one exists. No hypothesis on Galois groups is needed.

*Proof.*

1. **Primitive element.** Let $n=\dim A$ and let $b_1,\dots,b_n$ be the given basis. Put $\theta(c)=\sum_i c^{i-1}b_i$ for $c\in\mathbb Z$. Over $\overline{\mathbb Q}$, $A$ has $n$ distinct algebra maps $\lambda_j$. For $j\ne k$, $\lambda_j(\theta(c))-\lambda_k(\theta(c))$ is a polynomial in $c$ of degree at most $n-1$. It is nonzero because $\lambda_j\ne\lambda_k$ on some $b_i$. Hence at most $(n-1)\binom n2$ integers $c$ are bad. Trying $c=0,1,\dots,n^3$, the first $c$ whose characteristic polynomial $\chi(c)$ is squarefree (a gcd test) gives a generator. Then $A\cong\mathbb Q[x]/(\chi)$. Bit sizes are polynomial.
2. **Field factors.** Factor $\chi$ over $\mathbb Q$ by LLL (Lenstra–Lenstra–Lovász 1982). The factors $g_i$ give $A\cong\prod_i\mathbb Q[x]/(g_i)$, together with the idempotents.
3. **Field isomorphism.** $K=\mathbb Q[x]/(g)\cong L=\mathbb Q[x]/(h)$ if and only if $\deg g=\deg h$ and $h$ has a root in $K$. Decide the latter by factoring $h$ over $K$ in polynomial time (A. K. Lenstra, EUROCAL 1983; Landau, SIAM J. Comput. 14 (1985) 184–195). A root gives the isomorphism.
4. **Matching.** Isomorphism is an equivalence relation. Partition the factor fields of $A$ and $B$ into classes using $O(n^2)$ tests. Then $A\cong B$ if and only if each class has equal multiplicity on both sides, because an étale algebra is uniquely a product of fields. ∎

**Prior art and status.**
- Step 3 is the standard number-field isomorphism test; see Cohen, *A Course in Computational Algebraic Number Theory*, §4.5.
- The decomposition can also be done with Friedl–Rónyai (STOC 1985) or Lenstra–Silverberg ([arXiv:1509.08843](https://arxiv.org/abs/1509.08843)).
- We found no claim that number-field isomorphism is GI-hard. The GI-hardness results in this area concern **finite** rings (Kayal–Saxena, *Complexity of ring morphism problems*, Comput. Complexity 15 (2006)) and non-semisimple commutative algebras (Agrawal–Saxena, STACS 2006, where cubic-form equivalence enters through nilpotent parts).
- We could not locate an Arvind–Kurur paper on number-field isomorphism. Their number-field work concerns unit groups.
- **Conclusion: (1) of the target is classical and holds for all Galois groups. Kronecker–Weber, conductors and GRH play no role.** Conductor computations would actually be harmful: computing the conductor of an abelian field requires factoring its discriminant, which is not known to be possible in polynomial time.

---

## 2. Theorem B: TI for geometrically diagonal tensors is in P (folklore composition)

Call a rational $n\times n\times n$ tensor **geometrically diagonal** if it is $\mathrm{GL}_n(\overline{\mathbb Q})^3$-equivalent to the unit tensor $\langle n\rangle$.

**Theorem B.** There is a deterministic polynomial-time algorithm that, given rational tensors $T,S$, does three things:
- (i) decides whether $T$ is geometrically diagonal;
- (ii) if so, outputs an étale $\mathbb Q$-algebra $E_T$ with $T\cong_{\mathbb Q}\mu_{E_T}$, the multiplication tensor;
- (iii) decides $T\cong_{\mathbb Q}S$ whenever $T$ or $S$ is geometrically diagonal.

The same holds for trace tensors $t_E(x,y,z)=\mathrm{Tr}(xyz)$. There is no restriction on the splitting field.

*Proof.*

1. **Regular elements.** View $T$ as a bilinear map $U\times V\to W$. If $T$ is geometrically diagonal, then $\det T(u,\cdot)$ is a nonzero constant times $\prod_{i=1}^n\ell_i(u)$, with the $\ell_i$ nonzero linear forms over $\overline{\mathbb Q}$. On the moment curve $m(t)=(1,t,\dots,t^{n-1})$, each $\ell_i(m(t))$ is a nonzero polynomial of degree at most $n-1$. So some $t\in\{0,\dots,n(n-1)\}$ gives an invertible $L=T(u_0,\cdot)$. Likewise some $v_0$ gives an invertible $R=T(\cdot,v_0)$. If either search fails, $T$ is not geometrically diagonal. Answer (i) negatively. *We never need a general PIT for symbolic determinants: failure of this specific search certifies non-diagonality.*
2. **Isotope.** Put $x*y=T(R^{-1}x,L^{-1}y)$. Then $T(x,y)=R(x)*L(y)$, so $T$ is $\mathbb Q$-isotopic to $(W,*)$, and $e=T(u_0,v_0)$ is a two-sided unit. Test commutativity and associativity, and test nondegeneracy of the trace form $\mathrm{Tr}(L_{x*y})$ by a determinant.
   - If all tests pass, $(W,*)$ is étale and $T\cong\mu_{(W,*)}$, which settles (i) and (ii).
   - If $T$ is geometrically diagonal, then in diagonal coordinates $c_i*c_j=\delta_{ij}\lambda_i^{-1}c_i$, where $e=\sum\lambda_ic_i$ with all $\lambda_i\ne0$. So $(W,*)\otimes\overline{\mathbb Q}\cong\overline{\mathbb Q}^n$ and the tests pass. This shows the tests are exact.
3. **Uniqueness of the algebra.** Tensor isomorphism of unital associative algebras is algebra isomorphism. Given $R(xy)=P(x)Q(y)$, the elements $a=P(1)$ and $b=Q(1)$ are units, and $x\mapsto a^{-1}R(x)b^{-1}$ is an algebra isomorphism (JointPrimeCounts §1; portfolio A34; classically Albert 1942 on isotopy). Hence $T\cong S$ if and only if $S$ passes (i) and $E_T\cong E_S$. Decide the latter by Theorem A.
4. **Trace tensors.** $t_E(x,y,z)=\beta(xy,z)$, where $\beta$ is the nondegenerate trace form. Composing the third slot with $\beta^\flat:E\to E^*$ is an invertible linear map, so under three independent $\mathrm{GL}$ actions $t_E\cong\mu_E$. Theorem 1 of ti-hasse.md follows at once over $\mathbb Q$. ∎

**Novelty.** None in substance. The ingredients are Albert's isotopy normalisation, the forms of $\langle n\rangle$ being étale algebras ($H^1$ of the quasi-trivial torus vanishes), and Theorem A. We have not seen "TI for forms of the unit tensor is in P" stated in the Grochow–Qiao literature. It may be worth one sentence in a briefing, labelled folklore. **Abelian splitting and GRH are irrelevant to P-membership.**

---
