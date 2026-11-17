# Hidden extension-linear matrix code equivalence over finite and number fields

Couvreur, Debris-Alazard, and Gaborit developed algorithms for one-sided matrix-code equivalence and for two-sided equivalence of codes with a hidden extension-field structure. Their conclusion asks about carrying these questions to arbitrary fields, and their seminar slides explicitly ask about characteristic zero. Both structured problems have deterministic polynomial bit-time search algorithms over number fields. The same argument gives a deterministic polynomial bit-time bound over every finite field, removing the randomized factorization dependence in their finite-field upper bound. It also repairs the center-automorphism step in Proposition 32. [Paper and open question](https://arxiv.org/html/2011.04611v2#S6) · [Seminar slides, final slide](https://www.ce.cit.tum.de/fileadmin/w00cgn/lnt/news/slides_couvreur.pdf#page=56)

Throughout, $k$ is the base field and matrix codes $C,D\subseteq k^{m\times n}$ are supplied by $k$-bases. A two-sided transporter is a pair $(P,Q)\in\mathrm{GL}_m(k)\times\mathrm{GL}_n(k)$ such that $PCQ=D$. A right transporter has $P=I$. The hidden extension-field hypothesis is that each left stabilizer contains a unital field extension of $k$ of degree $m$, acting on the $m$-dimensional column space. This is equivalent to the input codes being coordinate expansions of extension-linear vector codes in hidden bases. The two hidden fields may coincide, as they do in the source's finite-field problem. The proof also permits them to differ.

## Right equivalence is a module isomorphism problem

Use column space $V=k^m$ and row space $W=k^{1\times n}$. For a code $C$, take the direct sum $C\oplus W$, the projector $(c,w)\mapsto(c,0)$, and the $m$ maps $(c,w)\mapsto(0,r_i(c))$, where $r_i$ extracts row $i$. These are the action matrices of a representation of the two-vertex quiver with $m$ arrows, all directed from the code vertex to the row-space vertex. The quiver's path algebra has dimension $m+2$, since paths have length at most one. The actions are computed directly from the code basis.

An isomorphism of these modules has the form $S\oplus R$, with $S:C\to D$ and $R:W\to W$ invertible, by commutation with the projector. The arrow equations state $r_i(Sc)=R(r_i(c))$ for every $i$. Write $R(w)=wQ$. The equations are precisely $Sc=cQ$, so module isomorphism and right equivalence give the same witnesses. Transposing every code matrix treats left equivalence. The reduction includes zero codes. Codes of unequal dimension are rejected by dimension alone.

Brooksbank and Luks's constructive module isomorphism theorem uses polynomially many basic field operations and applies over arbitrary fields. It supplies deterministic polynomial bit time over a finite field in its standard representation. For the number-field bit model, use Chistov–Ivanyos–Karpinski's Corollary 3, which states the constructive polynomial bound in the input bit size of bases and primitive-element coordinates. [Brooksbank–Luks, Theorem 3.5](https://ix.cs.uoregon.edu/~luks/ModIso.pdf) · [Chistov–Ivanyos–Karpinski, Corollary 3](https://theory.cs.uni-bonn.de/marek/publications/85169-cs.pdf)

## The center determines the left stabilizer

For $C$ put
$$
A_C=\{T\in\operatorname{End}_k(V)\mid TC\subseteq C\},
\qquad E_C=\operatorname{End}_{A_C}(V).
$$
Their bases are found by linear systems. For $A_C$, impose that the images of the supplied code basis still lie in $C$. For $E_C$, impose commutation with a basis of $A_C$.

Let $K\subseteq A_C$ be a hidden degree-$m$ extension field. Then $V$ is one-dimensional as a $K$-space. In particular $V$ is a simple $A_C$-module. Its commutant $E_C$ is a division ring by Schur's lemma and lies in the commutant of $K$. The latter is $K$ itself, because every $K$-linear map on its one-dimensional regular module is multiplication by a scalar. Therefore $E_C$ is a commutative field. By Jacobson density applied to the finite-dimensional simple module,
$$
                      A_C=\operatorname{End}_{E_C}(V).
$$
For this application, an $E_C$-basis of $V$ is finite, so the simultaneous interpolation in the density theorem realizes each $E_C$-linear map on the whole basis. In particular $E_C=Z(A_C)$. The same holds for $D$. The algorithm uses the computed centers and their action.

## Enumerating maps on the centers is sufficient

If $PCQ=D$, then $PA_CP^{-1}=A_D$, by applying the defining inclusion for $A_C$ and then its inverse. Conjugation by $P$ thus gives a $k$-isomorphism $\sigma:E_C\to E_D$. For each such $\sigma$, choose any $E_C$-basis $v_1,\ldots,v_s$ and $E_D$-basis $w_1,\ldots,w_s$ of $V$. Form the $k$-linear isomorphism
$$
        P_\sigma\Big(\sum_i a_i v_i\Big)=\sum_i \sigma(a_i)w_i .
$$
These bases are computed by greedy rank tests with the known field bases. Then $P_\sigma e P_\sigma^{-1}=\sigma(e)$. Every $P$ giving the same $\sigma$ has $P P_\sigma^{-1}\in\operatorname{End}_{E_D}(V)^\times=A_D^\times$. An invertible member of $A_D$ maps $D$ onto itself by the equality of dimensions. Consequently
$$
        \exists P,Q\ \ PCQ=D
        \quad\Longleftrightarrow\quad
        \exists \sigma,Q\ \ P_\sigma C Q=D .
$$
For the forward direction multiply $PCQ=D$ on the left by $(P P_\sigma^{-1})^{-1}$. The reverse direction uses $P_\sigma$ itself. Thus try each $\sigma$ and run the right-equivalence algorithm.

Reject unequal $k$-dimensions of $E_C,E_D$. There are at most $[E_C:k]\le m$ embeddings, and each is an isomorphism when the dimensions agree. The following are three ways to list them.

- **Finite base fields.** Compute multiplication tables of $E_C,E_D$ over the underlying prime field by multiplying their matrix bases and solving for coordinates. Lenstra's deterministic isomorphism algorithm for explicitly presented finite fields produces one prime-field isomorphism in time polynomial in the table size and $\log p$. Enumerate its compositions with the prime Frobenius powers of $E_D$, and keep those fixing the named copy of $k$. The number of compositions is $\dim_{\mathbb F_p} E_D\le m\dim_{\mathbb F_p} k$. Frobenius on each basis element is computed by repeated squaring. [Lenstra, *Finding Isomorphisms Between Finite Fields*](https://pub.math.leidenuniv.nl/~lenstrahw/PUBLICATIONS/1991b/art.pdf)
- **Number fields.** Compute a relative primitive element for $E_C/k$ and an absolute primitive element for $E_D/\mathbb Q$. For a separable extension with basis $b_1,\ldots,b_h$, among integer values of $t$ at most $(h-1)\binom h2$ make $\sum_{i=1}^h b_i t^{i-1}$ take the same value under two distinct embeddings over the base. Search that many values plus one using linear independence of powers as a certificate. All coefficients and powers used have polynomial bit-length, by bounded-degree multiplication in the explicit number-field coordinates. The absolute basis for $E_D$ is obtained by expanding the $k$-basis over $\mathbb Q$. Convert its minimal polynomial to a monic integral one by multiplying the generator by a common denominator. Factor the relative minimal polynomial of the generator of $E_C$ over $E_D$. The linear factors give exactly the images for each $k$-embedding, which are isomorphisms when the relative degrees agree. Lenstra's factorization theorem supplies the deterministic polynomial bit bound for this step. The linear systems and changes of basis throughout are polynomial-bit operations on the field representations. [Lenstra, *Factoring Polynomials over Algebraic Number Fields*](https://ir.cwi.nl/pub/2541/2541D.pdf)
- **Arbitrary fields with a root procedure.** Give an oracle the multiplication table of $E_D$ over $k$ and a polynomial over $E_D$, and request all its roots lying in $E_D$. Build a tower for $E_C/k$ by adjoining its basis elements one at a time. At each stage compute the new minimal polynomial by linear dependence of powers over the previously generated subfield. For each embedding already found, transport the coefficients and enumerate the roots in $E_D$ to obtain all its extensions. All stages can use $k$-linear systems by expanding known subfield bases. The root counts multiply to at most the total relative degree at each level, so at most $m$ embeddings are maintained at a stage. This works for inseparable extensions as well. The number of field operations and oracle calls is polynomial.

Together with the right-equivalence routine, this proves the deterministic polynomial bit-time theorem over algebraic number fields and finite fields, and the oracle-model theorem over arbitrary fields. The two-sided algorithm is for hidden extension-linear codes. The one-sided algorithm needs no hypothesis on the code.

## A counterexample to dropping the center automorphisms

The source's Proposition 32 asserts that left-equivalent codes with the same left stabilizer algebra $M_{m/\ell}(\mathbb F_{q^\ell})$, in its proper-stabilizer case, must coincide. Its argument applies Skolem–Noether to an automorphism that may act nontrivially on the center. The automorphism must fix the center pointwise for the cited innerness conclusion. [Couvreur–Debris-Alazard–Gaborit, §5.3](https://arxiv.org/html/2011.04611v2#S5.SS3)

Take $k=\mathbb F_2$, $E=\mathbb F_{16}$, and $K=\mathbb F_{256}$. Let $\alpha\in E$ have degree four over $k$, for example a root of $x^4+x+1$. Identify an $8\times 2$ matrix with a pair of columns in $K$. Consider the expanded $K$-linear codes
$$
           C_\alpha=\{(v,\alpha v)\mid v\in K\},
   \qquad  C_{\alpha^2}=\{(v,\alpha^2v)\mid v\in K\}.
$$
The left stabilizer of $C_\alpha$ consists exactly of the $k$-linear endomorphisms of $K$ commuting with multiplication by $\alpha$, since preserving the displayed graph means $T(\alpha v)=\alpha T(v)$ for all $v$. This is $\operatorname{End}_E(K)\cong M_2(E)$, strictly larger than the embedded $K$. Multiplication by $\alpha^2$ also generates $E$, so both codes have this same left stabilizer. The Frobenius $v\mapsto v^2$ carries $C_\alpha$ to $C_{\alpha^2}$ by left multiplication. The two codes are distinct since $\alpha\ne\alpha^2$.

Moreover they are not right equivalent. For $Q=\begin{pmatrix}a&b\\c&d\end{pmatrix}$ right multiplication has columns $((a+c\alpha)v,(b+d\alpha)v)$. Equality with $C_{\alpha^2}$ would require
$$
                   (a+c\alpha)\alpha^2=b+d\alpha .
$$
This forces $a=b=c=d=0$, by the independence of $1,\alpha,\alpha^2,\alpha^3$. Thus arbitrarily aligning the centers and testing only one right-equivalence instance can fail. Testing all induced center maps as above restores the criterion.

## Why the number-field bit model matters

There is no uniform bounded field-operation and equality-test algorithm for two-sided equivalence of hidden extension-linear codes, even over $\mathbb Q$ at fixed matrix dimensions and with a fixed common hidden extension field. The following example separates that model from the polynomial bit-time result.

For any nonsquare $a\in\mathbb Q^\times$, put $E_a=\mathbb Q[x]/(x^2-a)$. Identify its regular representation inside $M_2(\mathbb Q)$ with the span of $I_2$ and $\left(\begin{smallmatrix}0&a\\1&0\end{smallmatrix}\right)$. Use the code $C_a=M_2(E_a)\subseteq M_4(\mathbb Q)$ by replacing each field entry with its regular $2\times2$ block. Its displayed basis has entries polynomial in $a$, and its left stabilizer is $C_a$ itself, since $I_4\in C_a$ and $C_a$ is an algebra. Restrict the inputs to $a=2r^2$ or $a=3r^2$ for positive integers $r$. In both cases $E_a$ embeds in the fixed field $K=\mathbb Q(\sqrt2,\sqrt3)$, with $[K:E_a]=2$. By taking an $E_a$-basis of $K$, its multiplication maps realize a degree-four regular field inside $C_a=\operatorname{End}_{E_a}(E_a^2)$. Therefore all input pairs $(C_a,C_2)$ meet the hidden extension-linearity promise with the same field $K$.

If $PC_aQ=C_2$, then $PQ$ is an invertible element of $C_2$ because $I_4\in C_a$. Its inverse lies in $C_2$ by Cayley–Hamilton. This gives $PC_aP^{-1}=C_2$. The centers must be isomorphic, so $E_a\cong E_2$. Conversely when $a=2r^2$, conjugation of each regular block by $\operatorname{diag}(1,r)$ maps the field matrices for $E_a$ to those for $E_2$, and hence conjugates the algebras. When $a=3r^2$, the centers are $\mathbb Q(\sqrt3)$ and $\mathbb Q(\sqrt2)$, which are nonisomorphic since $3/2$ is not a rational square.

A bounded computation using rational field operations and equality tests has finitely many executions at this fixed matrix size. On each execution its intermediate registers are rational functions of $a$. Each equality test has the same outcome outside a finite set unless the tested difference is identically zero, in which case the equality always holds when defined. Denominators with nonidentically zero values also exclude only finitely many parameters. Following the generic outcome of each test determines one execution that applies outside a finite exceptional set of allowed values of $a$. It must give the same answer on almost all $2r^2$ and $3r^2$, which is impossible. Bit algorithms can access the finite encodings of these coefficients, as the number-field factoring algorithm does.

## General two-sided equivalence and the Hamming reduction

The source also reduces monomial Hamming code equivalence to unrestricted two-sided matrix-code equivalence by putting codewords on the diagonal. The same reduction works over every infinite field. A matrix transporter induces a Hamming-weight-preserving linear isomorphism $f$ of the two codes, since the rank of a diagonal matrix is its number of nonzero entries. On the source code, consider the multiset of restricted coordinate functionals and the multiset of functionals from the target pulled back along $f$. Weight preservation means that for each vector the two multisets have the same number of vanishing functionals. Choose a vector avoiding the union of all kernels of nonzero functionals, which is possible over an infinite field. It gives equality of the number of identically zero coordinates. For each hyperplane in either multiset, choose a point on it avoiding the other hyperplanes. This gives equality of the multiplicity of that kernel after subtracting the common number of zero coordinates. Nonzero functionals with the same kernel are proportional. Consequently a permutation and nonzero coordinate scalings realize $f$, including arbitrary nonzero scalings on the paired zero coordinates. The dimension-zero case has only zero coordinates. In the other direction a monomial transformation immediately gives left and right transporters of diagonal matrices.

This extends the source's hardness comparison to characteristic zero. The polynomial upper bounds above concern unrestricted one-sided equivalence and two-sided equivalence under hidden extension-linearity. The complexity of two-sided equivalence on arbitrary matrix codes over number fields is a separate problem. [Couvreur–Debris-Alazard–Gaborit, Proposition 13](https://arxiv.org/html/2011.04611v2#S3.SS3)

## Attribution and verification

The right-equivalence algorithm is an application of the cited module isomorphism theorems. The finite-field upper bound for hidden extension-linear codes combines a stabilizer strategy originating in Couvreur–Debris-Alazard–Gaborit with the center-map iteration, Lenstra's field isomorphism theorem and the module transporter. A targeted literature check located these antecedents and did not locate the counterexample, the deterministic finite-field bound for hidden extension-linear codes, or a prior resolution of the characteristic-zero versions above. Publication priority remains unverified.
