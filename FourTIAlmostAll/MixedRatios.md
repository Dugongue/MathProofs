# Mixed inverse ratios for ordinary binary four-tensor isomorphism

Let $T$ have four ordered modes of dimension $n$ over $\mathbb F_2$. A cut $p$ splits its modes into two pairs $L,R$. Write $F_p(T)\colon V_R^*\to V_L$ for the corresponding $n^2$-by-$n^2$ matrix, with $V_L,V_R$ denoting the two tensor products. Invert $F_q(T)$ at any invertible cut $q$ and view its entries as a tensor $S_q$ in the four dual modes. When regrouped at cut $p$, that tensor is a map $B_p(S_q)\colon V_L\to V_R^*$. In these conventions, $B_q(S_q)=F_q(T)^{-1}$. For $q\ne p$ define
$$
A_{p,q}(T)=F_p(T) B_p(S_q)\in\operatorname{End}(V_L).
$$

Fix one cut $p$. Suppose all three flattenings are invertible, and let $d(T)$ be the dimension of the common commutant of the two matrices $A_{p,q}(T)$, $q\ne p$. For every fixed $C$, there is an exact deterministic polynomial-time search and decision algorithm for this source against **every** target whenever $d(T)\le C\log_2 n$.

Under a mode change $g_1\otimes g_2\otimes g_3\otimes g_4$, write $P$ and $Q$ for the paired Kronecker products on $L,R$. The base matrix transforms as $F'_p=P F_p Q^{\mathsf T}$. The inverse tensor transforms contragrediently on each mode, so $B'_p=Q^{-\mathsf T} B_p P^{-1}$. Thus $A'_{p,q}=P A_{p,q}P^{-1}$. This argument works in any fixed finite field.

The algorithm verifies the source promise by elimination and first rejects a target whose invertibility pattern differs. Otherwise it computes both target ratios and solves the simultaneous linear equations $X A_{p,q}=A'_{p,q} X$ for $X$. If these equations have an invertible solution $X_0$, their full space is $X_0$ times the source commutant, and hence has dimension $d(T)$. Reject if the dimensions differ. Enumerate the at most $2^{d(T)}$ candidates $X$ and retain the invertible ones that are Kronecker products. To test this, realign the indices $(i,j),(k,l)$ to $(i,k),(j,l)$ and test rank one. Factoring a rank-one matrix produces the two factors, necessarily invertible when $X$ is invertible. For each retained candidate compute $Y^{\mathsf T}=F_p(T)^{-1}X^{-1}F_p(T')$ and use the same Kronecker test on $Y$. Verify the resulting mode maps on the entire source. Every genuine equivalence supplies an enumerated $X=P$ and gives $Y=Q$, so the procedure is complete. Verification makes it sound. The input and every matrix and linear system have polynomial dimensions. The logarithmic bound makes the enumeration polynomial as well.

The accompanying exact binary control generated uniform arrays and retained those with all three flattenings invertible. With seed 514, the fixed cut $12\mid34$ had scalar common commutant on all 100 retained samples at each $n=3,4,5,6$. The numbers of sampled arrays were $4053,3439,3957,4744$, respectively. The checker also tests the simultaneous conjugation equations after random invertible changes of basis. These finite experiments do not establish the asymptotic coverage. The open distributional estimate for this route is
$$
\Pr[d(T)>C\log_2 n\mid\text{all three pair flattenings invertible}]=o(1)
$$
for some fixed $C$. This estimate and the singular-flattening theorem would give $1-o(1)$ coverage at polynomial cost.
