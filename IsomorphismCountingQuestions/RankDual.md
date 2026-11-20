# The LRS, ATLRS and TZ-type separation for arbitrary evaluation sets

Santonastaso and Zullo ask in §6 of *Invariants for sum-rank metric codes* whether Theorem 5.20 still holds after removing the cyclic subgroup assumption on the evaluation sets. The answer is yes. The three inequivalence assertions hold for arbitrary evaluation sets satisfying the defining constraints, for every integer $3\le k\le tm-3$. This covers the two numerical ranges in the published theorem and also the integer between them when $tm$ is odd. Equivalence means the paper’s strong equivalence, which allows block permutations, invertible left and right multipliers, and blockwise field automorphisms. Publication priority for the extension is unverified. [Santonastaso and Zullo, definitions in §3.1, Theorem 5.20 and question in §6](https://link.springer.com/article/10.1007/s10231-025-01640-6)

## 1. Calculate the idealizers directly

Write $K=\mathbb F_{q^m}$, $N=tm$, $\theta$ for a generator of $\operatorname{Gal}(K/\mathbb F_q)$, and $R=K[x;\theta]$ with $xa=\theta(a)x$. For the nonzero distinct evaluation values $\Lambda\subseteq\mathbb F_q^\times$, set $H_\Lambda=\prod_{\lambda\in\Lambda}(x^m-\lambda)$ and $A=R/(H_\Lambda)$. This central polynomial is monic of degree $N$ and has a nonzero constant. Canonical representatives have degree below $N$, and $x$ is a unit. The paper identifies $A$ with the componentwise matrix algebra of $t$ square blocks. The left and right idealizers consist of multipliers stabilizing the code on the respective side.

For LRS the code is the space of polynomials of degree below $k$. A left idealizer element $g$ lies in the code since $1$ does. All the elements $gx^j$ for $0\le j<k$ lie in the code. At each step the unreduced degree increases by one, to at most $k<N$, and so no reduction occurs. At $j=k-1$ this forces $g$ to be constant. The right idealizer proof uses $x^jg$. All constants preserve the code on both sides.

For ATLRS with $\eta\ne0$, the constant coefficient $a$ and the coefficient of $x^k$ are linked by $a_k=\eta\tau(a)$, and the coefficients of $x,\ldots,x^{k-1}$ are arbitrary. Put $h=gx$ for $g$ in the left idealizer. The elements $h,hx,\ldots,hx^{k-2}$ all belong to the code. At any step the ordinary product by $x$ has degree at most $k+1<N$, so reduction does not occur. Since $h x$ belongs to the code, the coefficient of $x^k$ in $h$ is zero. The link then makes the constant coefficient of $h$ zero. All shifted members have constant coefficient zero, hence degree at most $k-1$. At the last shift this forces $\deg h\le1$. Thus $h=ax$ and $g=a$ is constant. The argument for a right idealizer starts with $h=xg$. Substitution into the link gives, respectively, $\tau(a)=a$ and $\tau(a)=\theta^k(a)$. The idealizers are exactly those two fixed fields.

For TZ-type TLRS put $L=\mathbb F_{q^\ell}$ with $m=2\ell$. The constant coefficient is in $L$ and the coefficient of $x^k$ is in $\gamma L$, where $\operatorname{N}_{K/\mathbb F_q}(\gamma)$ is a nonsquare. Since $1$ lies in the code, a left idealizer $g$ has degree at most $k$. The same consecutive multiplication by $x$ up to $gx^{k-1}$ occurs without reduction and leaves $\deg g\le1$. Multiplying by $\gamma x^k$ forces the linear coefficient of $g$ to vanish, again because $k+1<N$. The identical right-shift argument forces right multipliers to be constant. The constants allowed on either side are exactly $L$.

These arguments use only the indicated strict degree bounds and the nonzero constant of $H_\Lambda$. They establish the idealizer formulas independently of cyclicity.

## 2. Derive the comparisons, including the printed exceptional case

Under strong equivalence the left and right idealizers are preserved up to ring isomorphism. The formulas give Theorem 5.20(1) and (2) directly. They also give (3) unless $\tau=\theta^\ell$ and $m\mid k$. Indeed, both ATLRS fixed fields have order $q^\ell$ only if $\tau$ and $\tau^{-1}\theta^k$ are both the unique order-two automorphism of $K$. The printed statement of (3) uses $k\nmid m$. The following argument covers the exceptional case as well, so the proof does not require changing the printed condition.

Assume for contradiction that the ATLRS and TZ-type codes are strongly equivalent, with $\tau=\theta^\ell$ and $k=dm$. All evaluations are elements of $\mathbb F_q^\times$. Denote the proposed matched evaluations by $\lambda_i$ and $\mu_i$, with the block permutation absorbed into the indexing. Write $\bar a=\tau(a)$ and let $N_L$ and $\operatorname{Tr}_L$ denote the norm and trace from $K$ to $L$. The TZ norm condition forces odd characteristic and $\gamma\notin L$. Both left and right idealizers of both codes are the diagonal copy of $L$ acting by multiplication on each $K$ block.

Choose any $d-1$ blocks, shorten to codewords that are zero in those blocks, and delete the zero blocks. Equivalence induces an equivalence of the shortened codes. Zero at a block means divisibility by its central factor $x^m-\lambda_i$. Divide by their product, which is monic and has nonzero constant in $\mathbb F_q$. On every remaining block this is only multiplication by a nonzero scalar. The shortened ATLRS has cutoff $m$, with parameter $\eta$ changed by a nonzero factor in $\mathbb F_q$. The shortened TLRS has cutoff $m$ and the same $\gamma$. They have $t'=t-d+1\ge 2$ blocks and dimension $m^2$ over $\mathbb F_q$. They have minimum distance $t'm-m+1$. The original distance is $tm-k+1$ by equivalence to a TZ-type MSRD code. Shortening cannot lower that distance, and the Singleton bound for the shortened dimension gives the reverse inequality. [Neri, *Twisted Linearized Reed–Solomon Codes*, Theorem 7.2](https://arxiv.org/abs/2105.10451) The ambient comparison still normalizes the diagonal copies of $L$ inherited from the original codes.

For each surviving $\lambda_i$ choose $\alpha_i\in K^\times$ of norm $\lambda_i$ to $\mathbb F_q$. Use the model of its block with $x\mapsto M_{\alpha_i}\theta$, where $M_a$ denotes multiplication by $a$. Thus $x^r$ has coefficient $s_{i,r}=\prod_{v=0}^{r-1}\theta^v(\alpha_i)$ in front of $\theta^r$. In particular $s_{i,m}=\lambda_i$ and $N_L(s_{i,\ell})=\lambda_i$. The same notation with primes refers to the target generators and evaluations. All these changes of coordinate preserve the relevant strong equivalence.

## 3. Recover the multiplication space from two block determinants

As $L$-bimodules, each code splits into the grades $r\bmod\ell$, according to the automorphism of $L$ used by its operators. For $r>0$ with $r<\ell$, the common coefficient pair $(a,b)\in K^2$ describes at each block the operator
$$
M_{s_{i,r}a}\theta^r+M_{s_{i,r+\ell}b}\theta^{r+\ell}.
$$
The grade $0$ consists of operators
$$
M_{a+\lambda_i\eta\bar a}+M_{s_{i,\ell}b}\tau
$$
on the ATLRS side, with $a,b\in K$. On the TLRS side that grade consists of
$$
M_{u+\mu_i\gamma v}+M_{s'_{i,\ell}b'}\tau
$$
with $u,v\in L$ and $b'\in K$. All coefficient parameters displayed in each grade vary freely in the stated spaces.

For any two blocks consider, on one grade, their two $L$-determinant quadratic forms after composing each $\theta^r$-semilinear operator with $\theta^{-r}$. For $A,B\in K$, the determinant over $L$ of $M_A+M_B\tau$ is $N_L(A)-N_L(B)$. This follows by extending scalars from $L$ to $K$ and using the two embeddings of $K$ over $L$, so the resulting matrix has diagonal entries $A,\bar A$ and off-diagonal entries $B,\bar B$. In a free grade the two determinant forms are nonzero multiples of
$$
N_L(a)-\lambda_i N_L(b),\qquad N_L(a)-\lambda_j N_L(b).
$$
To get the ratio in this formula use $s_{i,r+\ell}=s_{i,r}\theta^r(s_{i,\ell})$. The norm forms on each of the two coefficient planes are nonsingular. Thus at exactly two projective parameters in the pencil of determinants the radical has dimension two, one parameter killing each summand.

For ATLRS grade zero put $c=N_L(\eta)$ and $S(a)=\operatorname{Tr}_L(\eta\bar a^2)$. The determinant at block $i$ is
$$
Q_i(a,b)=(1+c\lambda_i^2)N_L(a)+\lambda_i S(a)-\lambda_i N_L(b).
$$
The MSRD condition implies $c\lambda_i\lambda_j\ne1$ for distinct $i,j$. Otherwise $Q_i/\lambda_i=Q_j/\lambda_j$. For any $a\ne0$ there is $b$ with $Q_i(a,b)=0$, by surjectivity of the norm, including the value zero. This produces a nonzero word deficient by at least $\ell$ in each of two blocks. Their total rank deficit is at least $m$, exceeding the MSRD maximum $m-1$. In addition $a\mapsto a+\lambda_i\eta\bar a$ is invertible. If $c\lambda_i^2=1$, then $(I+\lambda_iM_\eta\tau)(I-\lambda_iM_\eta\tau)=0$, and the second operator is nonzero since $\tau$ is nontrivial. A nonzero kernel vector with $b=0$ would give a missing entire block, again a deficit of $m$.

The forms $N_L$ and $S$ are linearly independent, as is seen in the two embedding coordinates over $K$, where they are a product and a nonzero linear combination of squares. Since $c\lambda_i\lambda_j\ne1$, the two $a$-parts of $Q_i,Q_j$ are linearly independent. In the pencil there is therefore exactly one parameter with a two-dimensional radical. It kills the coefficient of $N_L(b)$, leaves a nonzero multiple of $N_L(a)$, and its radical is the $b$-plane.

An ambient equivalence has block maps $X\mapsto R_i X S_i$ after writing each entrywise base-field automorphism as conjugation by a semilinear map. The maps $R_i,S_i$ are semilinear over $L$ because they normalize its left and right diagonal copies, with the corresponding automorphisms of $L$ independent of $i$. Consequently the equivalence permutes the $L$-bimodule grades uniformly. It preserves the number and dimensions of the radicals in their two-block quadratic pencils. In fact, composing with the indicated powers of $\theta$ and its target analogue transforms each determinant by the same automorphism of $L$ and a nonzero scalar specific to that block. Radical dimensions are therefore unchanged under the induced semilinear map on the grade.

The only grade on the TLRS side that can have exactly one two-dimensional radical is its grade zero. Its unique radical, when the number is one, must be its $b'$-plane. To see this, take the combination canceling the $N_L(b')$ coefficient. The remaining quadratic on $(u,v)$ is a nonzero multiple of $u^2-\mu_i\mu_j N_L(\gamma)v^2$, which is nonsingular in odd characteristic. Thus the proposed equivalence maps grade zero to grade zero and each block’s subspace $M_K\tau$ to the corresponding $M_K\tau$. The polar orthogonal complement of that subspace for the determinant on $\operatorname{End}_L(K)$ is $M_K$. This proves that every block map also preserves $M_K$. This inference can use any pair containing the block, since every single-block projection is invertible on the two grade-zero planes.

## 4. Recover the scalar multipliers and contradict the endpoint relation

Since $R_i M_K S_i=M_K$, write $R_i=M_{p_i}\sigma_i$ and $S_i=\sigma_i^{-1}M_{q_i}$ with $\sigma_i$ an automorphism of $K$ and $p_i,q_i\in K^\times$. This follows by using $R_iS_i\in M_K^\times$ and conjugating the multiplication algebra. Put $c_i=p_iq_i$. Each absolute Frobenius exponent $\theta^r$ is then preserved. Its target index $r'$ is defined by $\theta'^{\,r'}=\theta^r$. Since $d$ was shortened to one, each nonzero absolute exponent has one freely varying common coefficient $b\in K$. Comparing the images at every surviving block gives
$$
p_i\,\sigma_i(s_{i,r})\,\theta^r(q_i)\,\sigma_i(b)
  =s'_{i,r'}\,D_r(b),
$$
where $D_r(b)$ is a common target coefficient. Taking $b=1$ first shows the ratios of the other factors are a nonzero constant $\delta_r$ independent of the block. Then varying $b$ shows that all $\sigma_i$ are the same $\sigma$. The exponent $r=\ell$ has target index $\ell$. Taking $N_L$ there gives
$$
N_L(c_i)\,\sigma(\lambda_i)=C\,\mu_i
$$
for a common nonzero constant $C$.

If $m\ge4$, let $j\in\{1,\ldots,m-1\}$ satisfy $\theta'^j=\theta$. Both source exponents $1,2$ are free, and their target indices are $j$ and $2j\bmod m$. Multiply the coefficient identity for exponent $1$ by its $\theta$-image and compare with exponent $2$. On the source side the product of its two coefficient factors is $\theta(c_i)$ times the exponent $2$ factor. On the target side the wrap at $m$ contributes $\mu_i^\epsilon$ with $\epsilon=\lfloor 2j/m\rfloor$, since $x'^m=\mu_i$ in block $i$. It follows that $\theta(c_i)=C'\mu_i^\epsilon$ for another common constant. If $\epsilon=0$, then $c_i=c_*$ and $\mu_i=D\,\sigma(\lambda_i)$ for common nonzero $c_*,D$. If $\epsilon=1$, then $c_i=c_*\mu_i$ and $\mu_i\,\sigma(\lambda_i)=D$. In the second case the norm equation uses $N_L(\mu_i)=\mu_i^2$.

Because the multiplication subspace is preserved, the ATLRS source part with parameter $a\in K$ and no $\tau$-term goes to a TLRS part with common $u,v\in L$ and no $\tau$-term. For every surviving block it satisfies
$$
c_i\,\sigma(a+\lambda_i\eta\bar a)=u+\mu_i\gamma v.
$$
With $\epsilon=0$, comparison at two distinct $\mu_i$ forces $u=c_*\,\sigma(a)$ for every $a$. With $\epsilon=1$ it forces $u=c_*D\,\sigma(\eta\bar a)$ for every $a$. Each expression ranges over $K$. This contradicts $u\in L$.

If $m=2$, then $L=\mathbb F_q$, and $k\le tm-3$ with $k$ even ensures $t'\ge3$. After applying the common automorphism $\sigma$ to source parameters, the same equations of multiplication components identify the ATLRS coefficient plane $K$ linearly with the TLRS parameter plane $L^2$. Take norms and divide by $\mu_i$, using $N_L(c_i)\sigma(\lambda_i)=C\mu_i$. It follows that, under one linear change on these planes and one common scalar, the respective sets of normalized quadratic forms must agree. On ATLRS these are
$$
  (\lambda_i^{-1}+c\lambda_i)N_L(a)+S(a)
$$
with the common field automorphism understood. They lie on one affine line. On TLRS they are
$$
  \mu_i^{-1}u^2+\operatorname{Tr}_L(\gamma)uv
       +\mu_i N_L(\gamma)v^2.
$$
Any three at distinct nonzero $\mu_i$ are affinely independent. Projecting to the diagonal coefficients reduces this to noncollinearity of three distinct points $(\mu_i^{-1},\mu_i)$ on the hyperbola, since a line intersects it in at most two points. This is a contradiction.

Thus the exceptional ATLRS and TZ-type codes are inequivalent as well. The argument is informal.
