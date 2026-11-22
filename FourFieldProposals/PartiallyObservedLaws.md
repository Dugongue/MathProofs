# Geometry of partially observed laws

**Field statement.** Study which laws of a parameterized mathematical response survive when the underlying system is known only through specified observations. The object of study is the entire family of responses consistent with the observations. The invariants measure which laws the observations force, which failures are possible, and the least amount of joint observation needed to settle a law. The same questions apply to classical probability, operator systems and finite experiments.

## Objects, transformations and invariants

A system consists of a state space $\mathcal M$, a family of observation maps $P_i\colon\mathcal M\to Y_i$, a parameter space $U$, and a response map $F\colon\mathcal M\to\mathbb R^U$. For classical probability take $\mathcal M=\mathcal P(X)$, $P_i(\mu)=(\pi_i)_*\mu$ for measurable probes $\pi_i$, and $F(\mu)(u)=\int K(u,\omega)\,d\mu(\omega)$. For finite-dimensional quantum states take $\mathcal M$ to be the density operators, use partial traces for the $P_i$, and take the response to be the expectation of a parameterized observable. A family of allowed simultaneous probes specifies which maps can be used together. A cost can count the largest subsystems observed jointly.

For observations $I$ and a feasible value $\tau$, define the response family
$$
\mathcal C_I(\tau)=\{F(M): M\in\mathcal M,\ P_i(M)=\tau_i\text{ for }i\in I\}.
$$
A law is a property $\mathcal L\subseteq\mathbb R^U$, such as concavity, an exact identity between evaluations or a metric inequality. The trace forces the law if $\mathcal C_I(\tau)\subseteq\mathcal L$. It rules out the law if $\mathcal C_I(\tau)\cap\mathcal L$ is empty. Otherwise it leaves the law undetermined. The resulting profile assigns this three-valued verdict to every feasible trace, law and allowed probe family. Minimal certificates and minimal failure supports are further invariants. In particular, for observations indexed by coordinate subsets, the arity of a law at a trace is the smallest $k$ at which the observations on all $k$-subsets force the law.

Recoding state, observation and parameter spaces induces equivalence when the probe refinements and costs are preserved and the laws are carried along by the parameter recoding. A simulation in one direction consists of a state map that converts each target observation to a postprocessing of permitted source observations, together with a pullback rule for responses. Such simulations transfer observations and can transfer law certificates when the pullback preserves the law. Refinement shrinks every compatible family. Products of systems permit two distinct constructions, with independent completions or with arbitrary joint fillings of the same local traces. Comparing the two constructions is one of the main mathematical problems.

## An obstruction realization theorem

Fix $m\ge2$, $n\ge2m$, and a random unit complex vector $\xi=(\xi_i)_{i=1}^n$. Assume that every $2m-1$ coordinate marginal is product Haar measure. Study the response on the nonnegative orthant
$$
F_\mu(x)=\mathbb E_\mu\left|\sum_i x_i^{1/(2m)}\xi_i\right|^{2m}.
$$
Let $F_0$ be the response for independent Haar coordinates. There are real coefficients $c_J$, indexed by the $2m$-subsets $J$ of $\{1,\ldots,n\}$, with
$$
F_\mu(x)=F_0(x)+\sum_{|J|=2m}c_J\prod_{j\in J}x_j^{1/(2m)}.
$$
The response is concave if and only if every $c_J\ge0$. The inclusion-minimal coordinate faces where concavity fails are precisely the faces indexed by $J$ with $c_J<0$. Every $2m$-uniform hypergraph occurs as this family of minimal failure faces, even for laws with smooth strictly positive densities arbitrarily close to product Haar in total variation. All the even moments of orders less than $2m$ also agree for all amplitudes. The least observation arity that guarantees concavity under product-Haar marginals is exactly $2m$.

**Proof.** Expand the response as
$$
\sum_{|\alpha|=|\beta|=m}\binom m\alpha\binom m\beta
   \prod_i x_i^{(\alpha_i+\beta_i)/(2m)}
   \mathbb E_\mu[\xi^\alpha\overline{\xi}^{\,\beta}].
$$
The terms with $\alpha=\beta$ give $F_0$, a nonnegative linear combination of weighted geometric means and thus concave. For $\alpha\ne\beta$, the marginal condition makes the expectation zero if the support of $\alpha-\beta$ has size less than $2m$. The support can have size $2m$ only if the positive and negative charges each occupy $m$ distinct coordinates with individual magnitude one. Each such term yields a scalar times the indicated geometric mean, with coefficient $(m!)^2$ times its Fourier moment. Conjugate pairs make the sum real. At smaller even orders every nonzero charge has support below the observation threshold, so its expectation vanishes and the responses coincide with the independent response.

Nonnegative $c_J$ preserve concavity. To prove necessity, restrict to the face indexed by any $J$ with $c_J<0$, hold the other $2m-1$ coordinates of this face at one, and take the remaining coordinate $t$ down to zero. The term $c_J t^{1/(2m)}$ has positive second derivative of order $t^{1/(2m)-2}$, which dominates the second derivatives in $F_0$. In the independent expansion each nonconstant exponent of $t$ is at least $1/m$. A face containing none of these negative supports still has a sum of nonnegative concave terms. This proves the minimal-face assertion.

For each $2m$-set $J$ choose a balanced charge $v_J\in\mathbb Z^n$ whose coordinates on $J$ are $m$ entries $+1$ and $m$ entries $-1$, with zeros elsewhere. Relative to product Haar measure, take the density
$$
1+\sum_J t_J\cos(v_J\cdot\theta),\qquad \sum_J|t_J|<1 .
$$
It is smooth and strictly positive, integrates to one, and each proper subprobe of $J$ kills its corresponding term on integration. The required $2m-1$ marginals are therefore product Haar. Fourier orthogonality yields $c_J=(m!)^2 t_J$. Choose small $t_J<0$ on the desired hyperedges and zero otherwise. Scaling the coefficients proves the total variation assertion. This gives the lower bound on arity. For the upper bound, every monomial in the moment expansion involves at most $2m$ variables, so product-Haar $2m$-marginals force the independent response exactly.

## What the definition opens up

One foundational question is a representation theorem for minimal obstruction families. The theorem above realizes every uniform hypergraph even with smooth positive laws and jointly fixed lower marginals. It is natural to ask which nonuniform obstruction families can be realized under a fixed canonical response, and how the families transform under independent products and conditional observation.

A second question asks for quantitative certification in families of exact laws. The theorem shows that agreement on every proper subprobe of an interaction can hide an arbitrarily small perturbation that changes concavity. One can ask for more informative probe notions that give quantitative Hessian or Jensen stability, and for the norm or resource price of a sufficient probe.

A third question asks when certificates compose. Finite classical observation problems with one linear inequality in the response are covered by the duality of multistochastic transport. The field hypothesis concerns an entire parameterized response, compares regional laws and their minimal certifying observation structures, and asks whether a common certificate mechanism extends across classical, quantum and combinatorial systems. To count as a distinct field in practice, this hypothesis would need such common theorems in several systems.

The nearest analytic work already studies moment bounds under limited independence. The portfolio's phase-average proof gives Hessian comparisons under independence. The opening written results characterize and realize minimal curvature failures directly from the unobserved Fourier terms. Publication priority is provisional. [Limited-independence Khintchine inequalities](https://arxiv.org/abs/1708.08775) · [Multistochastic Monge–Kantorovich duality](https://arxiv.org/abs/2008.07926) · [Jenkins–Tkocz on many-function Hanner inequalities](https://arxiv.org/abs/2207.09122) · [Portfolio Hanner argument](https://github.com/Dugongue/MathProofs/blob/d6933df162f8e998f27e007a42b8b6e55bb4858b/CrossBranchResolutions/HANNER.md)
