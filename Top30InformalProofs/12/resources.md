# Halting in quantum resource families

The reductions concern the particular resource tests and states defined below.

## 0. Two structural lemmas

Write $\rho=\sum_\ell p_\ell\,\beta_\ell\otimes|\ell\rangle\langle\ell|_C$. Here $C$ is the register of internal sites, which is classical in the product basis, and $\beta_\ell=(I\otimes V_{h(\ell)})\beta(\delta_\ell)(I\otimes V_{h(\ell)})^*$.

**Lemma A (resources detectable on a block transfer).** Suppose a resource has a free set $\mathcal F$ such that (i) $\mathcal F$ is closed under mixtures and under appending a classical flag on a side that is allowed to read it, and (ii) the projection $\Pi_\ell$ onto one flag value (renormalised) is a free operation. Then $\rho$ is free iff every $\beta_\ell$ is free. The "if" direction is (i). The "only if" direction applies (ii) to $\rho$. This covers NPT and separability (flags on Bob's side; $\Pi_\ell$ is a local filter), steering with the trusted party holding the flags, the stabilizer polytope (a $Z$-measurement of flag qubits is a stabilizer operation), and entanglement breaking via the Choi state.

**Lemma B (averaged resources do not transfer).** Suppose the quantity relevant to the resource is $\sum_\ell p_\ell\,\phi(\beta_\ell)$, with one fixed choice on the side that cannot read $\ell$, and $\phi$ affine in $\delta$. Then the witness block, which has weight $\le q^{-m}\cdot\mathrm{poly}$, is swamped. Indeed $\mathbb E_\ell[J_t(k)]$ under the multinomial law is an explicit polynomial in $m$ (multinomial moments). Its sign for large $m$ is computable, so no halting information survives. This kills bipartite CHSH and unassisted quantum capacity (below).

---

## 1. Bell nonlocality (CHSH)

**Block family (new, rational, full rank, both marginals $I/2$).**
$$\beta_{\rm B}(\delta)=\tfrac14\Big(I+\tfrac45\,X\!\otimes\!X-\tfrac35(1+\delta)\,Y\!\otimes\!Y+\tfrac35\,Z\!\otimes\!Z\Big).$$
$Y\otimes Y=-(XZ)\otimes(XZ)$ is real. Its eigenvalues on $\Phi^+,\Phi^-,\Psi^+,\Psi^-$ are $\tfrac34+\tfrac{3\delta}{20}$, $\tfrac1{20}-\tfrac{3\delta}{20}$, $\tfrac3{20}-\tfrac{3\delta}{20}$, $\tfrac1{20}+\tfrac{3\delta}{20}$. All are positive for $|\delta|<1/3$, and they sum to $1$. The correlation matrix is $T=\mathrm{diag}(4/5,-\tfrac35(1+\delta),3/5)$. The Horodecki quantity (sum of the two largest $t_i^2$) is
$$M(\delta)=\tfrac{16}{25}+\tfrac9{25}\max\big(1,(1+\delta)^2\big)=1+\tfrac9{25}\max(0,2\delta+\delta^2).$$
So the maximal CHSH value $2\sqrt{M}$ is $>2$ iff $\delta>0$. The value is exactly $2$, attained, for every non-witness block. Non-witness blocks are entangled but CHSH-local, since $\lambda_{\Phi^+}>1/2$. [Horodecki³ 1995, PLA 200, 340.]

**Theorem 1 (event-ready / tripartite).** Use the scenario $A$ = left qubit (2 binary settings), $B$ = right qubit (2 binary settings), $C$ = all internal sites (one setting, arbitrary POVM). The set $\{t:\exists m,\ \rho_{t,m}$ has a nonlocal correlation in this scenario$\}$ is c.e.-complete. If $t$ halts, $\rho_{t,m}$ is nonlocal at all $m\ge m_0(t)$. The bulk is fixed and commuting, and all proper marginals are maximally mixed.

*Proof.* (⇐) Let $C$ measure in its basis. If $P(a,\ell,b|x,y)=p_\ell P_\ell(ab|xy)$ has a local model $\int\mu(\lambda)P_A P_C(\ell|\lambda)P_B$, then $P_\ell$ has the local model with weight $\mu(\lambda)P_C(\ell|\lambda)/p_\ell$. The conditioning is legitimate because $C$ has one setting. Hence a witness block with $M>1$, measured with its Horodecki-optimal settings, gives nonlocality. (⇒) If every $M(\beta_\ell)\le1$, then each $P_\ell$ (any binary POVMs, which are contractions, so CHSH $\le 2\sqrt M$) satisfies all CHSH inequalities. It is therefore local by Fine's theorem [Fine 1982, PRL 48, 291]. For any POVM $E$ of $C$, $P(c|\ell)=\langle\ell|E_c|\ell\rangle$ because $\rho$ is block diagonal. So $\lambda'=(\ell,\lambda_\ell)$ is a local model. Membership in c.e.: per $m$ the condition is "some $\delta_{t,w}>0$", which is exactly testable. Hardness and padding are as in [N]. ∎

**Bipartite cut (A | everything else): the reduction fails.** Bob's ±1 observables enter only through their block compressions (contractions), while Alice's settings are fixed across blocks. In the key-undone frame, by concavity, CHSH $\le 2\sqrt{\tfrac{16}{25}\alpha_1^2+\tfrac9{25}\mathbb E(1+\delta)^2\alpha_2^2+\tfrac9{25}\alpha_3^2}$ along each Alice direction. Here $\mathbb E\delta=\mathbb E J/(8Lb^m)<0$ once $P(\text{witness})<1/2$, and $\mathbb E\delta^2=O(m^{2D}b^{-2m})$, so for large $m$ there is no violation even when $t$ halts. Non-halting $t$ gives no violation at any $m$. This is Lemma B. Heralding by Bob's flag measurement is the asymmetric detection loophole, with efficiency $\approx q^{-m}\ll 1/2$ [Brunner–Gisin–Scarani–Simon, PRL 98, 220403 (2007)]; compare the hidden nonlocality of Popescu 1995 (PRL 74, 2619). **Open:** whether bipartite CHSH violation at some length is c.e.-hard for fixed-bulk families (the problem is in Σ⁰₁ by Tarski at each $m$).

## 2. EPR steering (A untrusted → rest trusted)

**Block:** $\beta_{\rm S}(\delta)=\sigma(5/8+\delta)$ (isotropic, so Werner up to a local unitary), with Werner weight $p=(4F-1)/3>1/2\iff\delta>0$. It is full rank and both marginals are $I/2$.

**Theorem 2.** $\{t:\exists m$, the first qubit of $\rho_{t,m}$ steers the rest$\}$ is c.e.-complete. This holds both for all projective measurements and for all POVMs. The cut is genuinely **bipartite**, the bulk is fixed and commuting, all proper marginals are maximally mixed, and steerability persists at all large $m$.

*Proof.* Flag lemma: suppose $\sigma_{a|x}=\sum_\lambda D(a|x,\lambda)\tau_\lambda$ on the trusted side. Compressing by the trusted projector $\Pi_\ell$ gives $p_\ell\sigma^\ell_{a|x}=\sum_\lambda D(a|x,\lambda)\Pi_\ell\tau_\lambda\Pi_\ell$, which is an LHS model for block $\ell$. Conversely, block models combine with $\lambda'=(\ell,\lambda)$. The two-qubit Werner state is unsteerable iff $p\le1/2$: for projective measurements [Wiseman–Jones–Doherty, PRL 98, 140402 (2007)], and for POVMs [Zhang–Chitambar, arXiv:2309.09960] (I checked the abstract only, not the proof). Bob undoes $V_h$ locally. ∎ The reverse direction (the flag holder untrusted) has the same detection-loophole obstruction as §1.

## 3. Distillability, separated from entanglement

(a) **Base family.** Two-qubit entangled ⇒ distillable [Horodecki³, PRL 78, 574 (1997)]. Bob reads the flags, announces the witness copies over LOCC, and undoes the key. So distillability at some length is c.e.-complete, with $1$-distillability at a single copy: take $P_A=I$ and $P_B$ the rank-2 projector onto one witness block.

(b) **Theorem 3 (bound entangled vs distillable).** Let the right endpoint be 4 qubits ($\mathbb C^{16}$) and set
$$\beta_{\rm D}(\delta)=\tfrac14\,Q\ \oplus_B\ \tfrac14\,(X\!\otimes\! I)Q(X\!\otimes\! I)\ \oplus_B\ \tfrac12\,\sigma(\tfrac12+\delta)\ \oplus_B\ 0_{6},$$
a direct sum over orthogonal Bob subspaces. Here $Q=\sigma_{b}$ is Horodecki's $2\times4$ PPT entangled state with $b=3/5$: prefactor $1/(7b+1)$, $\sqrt{1-b^2}/2=2/5$, all entries rational [P. Horodecki, PLA 232, 333 (1997), §IV.B; matrix checked via ar5iv]. $Q_A=\mathrm{diag}(4b,1+3b)/(7b+1)$ is diagonal, so the $X$-paired copy makes the Alice marginal of $\beta_{\rm D}$ equal to $I/2$. Keys are real 4-qubit Paulis.
- If $t$ never halts, every $\rho_{t,m}$ is **PPT and entangled**, i.e. bound entangled at every length. It is PPT blockwise. It is entangled because Bob's local projector onto a $Q$-block gives $Q$.
- If $t$ halts, $\rho_{t,m}$ is NPT and 1-distillable for all $m\ge m_0$.

Hence "distillable at some length" is c.e.-complete while "entangled" is trivially true. PPT ⇒ undistillable [Horodecki³, PRL 80, 5239 (1998)]. This avoids the NPT-bound-entanglement problem, because every NPT block is two-qubit. *Caveats:* $\beta_{\rm D}$ is singular, since $Q$ has rank 5 of 8, so positive definiteness is lost. Marginals omitting an internal site are maximally mixed. The marginal omitting the left qubit is $t$-independent but not maximally mixed. Restoring full rank needs an explicit witness for $(1-\varepsilon)Q+\varepsilon I/8$ (gap G1).

## 4. Channels

$\rho_{t,m}$ has Alice marginal $I/2$, so it is the normalised Choi state of a unique CPTP map $\mathcal N_{t,m}:\mathbb C^2\to\mathbb C^2\otimes\mathbb C^{q^m}$, $\mathcal N(X)=2\operatorname{Tr}_A[(X^T\otimes I)\rho]$. With [N]'s block, it is a classically flagged, key-rotated depolarising channel.

**Theorem 4.** (a) $\{t:\exists m,\ \mathcal N_{t,m}$ not entanglement breaking$\}$ is c.e.-complete. EB ⇔ the Choi state is separable [Horodecki–Shor–Ruskai, RMP 15, 629 (2003)]. (b) The same holds for $\{t:\exists m,\ Q_2(\mathcal N_{t,m})>0\}$ (two-way-assisted capacity). If the channel is EB it is simulable by measure-and-prepare plus LOCC, so $Q_2=0$. Otherwise $Q_2\ge D_\leftrightarrow(\text{Choi})>0$ by §3. (c) With §3(b)'s Choi states, the channels are **never** EB (they are PPT-binding), yet $Q_2>0$ iff $t$ halts.

**Unassisted $Q$ does not transfer (Lemma B, rigorous for erasure blocks).** Take blocks that are erasure channels $\mathcal E_{\varepsilon_w}$, $\varepsilon_w=\tfrac12-\delta_w$, with receiver-visible flags. Given the erasure bit, the flag is input-independent, so the receiver can resample it. The flagged channel is therefore interconvertible with $\mathcal E_{\bar\varepsilon}$, which gives $Q=\max(0,1-2\bar\varepsilon)=\max(0,2\,\mathbb E\delta_w)$ [Bennett–DiVincenzo–Smolin, PRL 78, 3217 (1997)]. Here $\mathbb E\delta_w=\mathbb E_{\rm mult}[J_t]/(8L_tb^m)$, a computable polynomial in $m$ over $b^m$. So "$Q>0$ at some length" is **decidable** for this family. For depolarising blocks, $Q$ itself is unknown.

## 5. Magic and coherence

**Theorem 5 (magic, c.e.-complete).** Make the internal sites qubits (pad the alphabet to a power of 2) and drop the left endpoint. The right endpoint qubit has block $\tau(\delta)=\tfrac12\big(I+\tfrac{1+\delta}2(X+Z)\big)$. It is real and full rank ($|r|=(1+\delta)/\sqrt2<1$), and $|r|_1=1+\delta$. A one-qubit state is in the stabilizer hull iff $|r|_1\le1$ (octahedron) [Bravyi–Kitaev, PRA 71, 022316 (2005)]. $\rho_{t,m}\notin\mathrm{STAB}_{m+1}$ iff some $\delta_{t,w}>0$. For the "only if" direction: a $Z$-basis projection of a mixture of pure stabilizer states yields stabilizer states, and $V_h$ is Clifford. **All** proper marginals are maximally mixed. The analogous result for odd $d$ with Wigner negativity holds because the flag Wigner functions have disjoint supports.

**Theorem 6 (coherence: no transfer, decidable).** For any rational MPO family and fixed site-product basis, set $a_m=\operatorname{Tr}\rho_m^2-\sum_x\langle x|\rho_m|x\rangle^2$. This is a rational linear recurrence sequence (transfer matrices), and coherent at $m$ ⇔ $a_m\neq0$. By Skolem–Mahler–Lech with effective periodic part (Berstel–Mignotte 1976), "coherent at some length", "at infinitely many lengths" and "at all large lengths" are all **decidable**. "Coherent at every length" is exactly an instance of the **Skolem problem** (decidability open). Reason: the incoherent set has empty interior, so no threshold sign can be planted. *Unverified:* whether every LRS arises this way (Skolem-hardness).

## 6. Arithmetic hierarchy

Let $E_\exists,E_\infty,E_{\rm cof},E_\forall$ mean entangled at some / infinitely many / all large / all lengths. Per length, entanglement of a rational state is decidable (Tarski; for these families PPT), which gives the upper bounds $\Sigma_1,\Pi_2,\Sigma_2,\Pi_1$.

- **Padded family [N]:** a witness at $m_0$ pads to every $m\ge m_0$, so $E_\exists=E_\infty=E_{\rm cof}$, all Σ⁰₁-complete.
- **Exact length, commuting bulk.** Make letter $0$ count too ($A_0$ a translation), and use the bijective iterated Cantor packing $\pi:\mathbb N^r\to\mathbb N$ with $\pi(y)\ge\sum y$. Take $J=1-2V(t,y)^2-2(|k|-\pi(y))^2$, giving entangled at $m$ ⇔ $\pi^{-1}(m)$ solves $V$; or $J=V^2(1-2(|k|-\pi(y))^2)$, giving entangled at $m$ ⇔ $\pi^{-1}(m)$ does not solve $V$. Then $E_\forall$ is **Π⁰₁-complete**. **Theorem 7:** for any letter-count architecture, each length contains finitely many $k$, so $E_\infty\equiv_m\textsf{InfSol}$ (polynomial equations with infinitely many solutions). InfSol is Σ⁰₁-hard and in Π⁰₂. It is Π⁰₂-complete if Matiyasevich's finite-fold conjecture holds. Its exact degree appears open (Davis 1972 not checked; Tyszka's conjectures would make it c.e.).
- **Non-commuting fixed bulk (Theorem 8, sketch).** The word is the unique, deterministic, clocked history (configurations growing one cell per step) of a universal machine deciding "stage $s$ of $W_t$ adds an element". A weighted automaton computes $S(w)=[\text{DFA reject}]+\sum_i(N(\tau c_i)-N(c_{i+1}))^2+(N(\text{prefix})-N_t)^2$, using $N(x)=\sum d_jB^{-j}$ with nonzero digits and a sequential transducer $\tau$. Then $J=1-2B^{2m}S\in\mathbb Z$, $|J|\le C^m$. This is closed under Cauchy/Hadamard products [Schützenberger 1961], and $t$ enters only through $N_t$ in the left row. Each true $s$ gives exactly one entangled word, so $E_\infty\iff W_t$ infinite, which is **Π⁰₂-complete**. With histories $H_j$ that check that the window of stages $[j/2,j]$ adds nothing, clocked to $|H_j|=(j+|t|+1)^c$, plus marked padding $\le|H_j|$, $E_{\rm cof}\iff W_t$ finite, which is **Σ⁰₂-complete**. Key marginal hiding survives. Internal permutation invariance and commutation are lost.
