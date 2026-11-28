# Robust halting in matrix-product families

The scope is the stated families and the classical-flag architecture.

## 0. Two elementary facts used throughout

**(F1) Negativity lower-bounds the distance to PPT, and hence to SEP.** Let $\Gamma$ be the partial transpose on a qubit $L$. For PSD $Y$ on $L\otimes R$ we have $\|Y^\Gamma\|_1\le 2\operatorname{Tr}Y$. For a pure state with Schmidt coefficients $p_i$, $\|Y^\Gamma\|_1=(\sum_i\sqrt{p_i})^2\le 2$, and mixtures follow by convexity. Writing a Hermitian $X$ as $X_+-X_-$ gives $\|X^\Gamma\|_1\le2\|X\|_1$. For PPT $\tau$, $\|\tau^\Gamma\|_1=1$, so
$$2N(\rho)=\|\rho^\Gamma\|_1-1\le\|\rho^\Gamma-\tau^\Gamma\|_1\le2\|\rho-\tau\|_1 .$$
It follows that $\operatorname{dist}_1(\rho,\mathrm{SEP}_{\rm full})\ge\operatorname{dist}_1(\rho,\mathrm{PPT}_{L|{\rm rest}})\ge N_{L|{\rm rest}}(\rho)$.

**(F2) Classical-flag states.** Let $\rho=\sum_w|w\rangle\langle w|\otimes X_w$, where the flags $w$ label a product basis of the internal sites and $X_w\succeq0$ acts on the endpoints $L,R$. Then:
(i) $\rho^{\Gamma_L}$ is block diagonal, so $N_{L|{\rm rest}}(\rho)=\sum_w N(X_w)$, where $N$ is extended homogeneously to unnormalised operators.
(ii) If $\rho$ is fully separable, then every $X_w$ is separable. Applying the product of local projectors $|w_i\rangle\langle w_i|$ maps the separable cone into itself and outputs $|w\rangle\langle w|\otimes X_w$.
(iii) If each $X_w$ is separable, then $\rho$ is fully separable: tensor each decomposition with the product flag projector.
(iv) Let $d(\sigma)=\min_{\tau\in\mathrm{SEP}(L{:}R)}\|\sigma-\tau\|_1$. Then $N(\rho)\le\operatorname{dist}_1(\rho,\mathrm{SEP}_{\rm full})\le\sum_w\operatorname{Tr}X_w\, d(X_w/\operatorname{Tr}X_w)$. The first inequality is F1. For the second, use the competitor $\sum_w|w\rangle\langle w|\otimes(\operatorname{Tr}X_w)\tau_w$.
(v) $N(\sigma)\le d(\sigma)$, by F1 with two parties.

---

## 1. Theorem A: a robust-in-length construction

**Alphabet.** Each internal site has basis labels $(a,g)$ with $a\in\Sigma=\{1,\dots,s,\$\}$ and $g\in G=(\mathbb Z/2)^2$, so the site dimension is $q=4(s+1)$. For a word $w$, let $\pi(w)$ be its maximal $\$$-free prefix and set $\ell(w)=|\pi(w)|$. Here $\pi(w)=w$ if $w$ contains no $\$$. Let $k(w)\in\mathbb N^s$ be the letter counts of $\pi(w)$. Define
$$F_{t,w}=\frac12+\frac{J_t(k(w))}{8L_t\,b^{\ell(w)}} .$$
Every monomial satisfies $|k^\alpha|\le\max(1,\ell)^{D}\le 2^{D\ell}$, so $|J_t(k)|\le L_t2^{D\ell}$ and $|F_{t,w}-\tfrac12|\le 2^{-\ell}/8\le1/8$. Moreover $F_{t,w}>\tfrac12$ iff $U(t,k(w))=0$; otherwise $J_t\le-1$.

**State.** Exactly as in the base construction,
$$\rho_{t,m}=q^{-m}\sum_{(a_i,g_i)}|a,g\rangle\langle a,g|\otimes(I\otimes V_h)\sigma(F_{t,a})(I\otimes V_h)^*,\qquad h=\textstyle\sum_ig_i .$$

**MPO realisation (fixed rational translation-invariant bulk).** The virtual space is (copy index $(i,j)\in\{0,1\}^2$) ⊗ (key register $\mathbb C^4$) ⊗ $\big[\mathbb C\ (\text{constant branch})\ \oplus\ (\mathbb C^{n_D}\oplus\mathbb C)\ (\text{polynomial branch: active monomial row} \oplus \text{frozen scalar})\big]$. Write $S_g$ for the base's key shifts, $A_a$ for the base's commuting monomial-translation matrices, and $v(0)$ for the monomial column at $0$. The bulk matrix for the diagonal physical entry $(a,g)$, with all off-diagonal entries zero, is:

* $a\in\{1..s\}$: $\tfrac1q S_g\otimes\big(1\oplus\begin{psmallmatrix}A_a/b&0\\0&1\end{psmallmatrix}\big)$;
* $a=\$$: $\tfrac1q S_g\otimes\big(1\oplus\begin{psmallmatrix}0&v(0)\\0&1\end{psmallmatrix}\big)$, acting on row vectors: $(r_{\rm act},r_{\rm fr})\mapsto(0,\ r_{\rm act}v(0)+r_{\rm fr})$.

The left end for copy $(i,j)$ is $e_0^\top\otimes(1\oplus(c_t,0))$, where $c_t$ is the coefficient row of $J_t/(8L_t)$. It is computable from $t$, and it is the only input-dependent datum. The right end is the base's right column with polynomial part $(E_h)_{ir,jl}\,(v(0);1)$.

*Contraction check.* Suppose the first $\$$ is at position $\ell+1$. After the prefix, the active row is $c_tA_{\pi}/b^\ell$. At the $\$$ it becomes the frozen scalar $c_t v(k)/b^\ell$, using commutativity of the $A_a$ and $A_av(x)=v(x+e_a)$. Later sites multiply it by $1$, and the right end multiplies by $1$. If the word contains no $\$$, the right end contracts the active row with $v(0)$. In both cases the result is $q^{-m}\big[(C_h)+(F_{t,w}-\tfrac12)(E_h)\big]_{ir,jl}$. The bulk dimension depends only on $s$ and $D$. The letter matrices no longer commute with the $\$$ matrix.

**Theorem A.** For every $t$ and $m\ge1$:
1. $\rho_{t,m}$ is a positive definite rational density matrix. Every proper physical-site marginal is exactly maximally mixed.
2. If $t\notin K$, then $\rho_{t,m}$ is fully separable for every $m$.
3. If $t\in K$ with a witness $k^\*$ of size $\ell^\*=\sum_ik^\*_i$, then for all $m\ge\ell^\*+1$
$$\operatorname{dist}_1(\rho_{t,m},\mathrm{SEP}_{\rm full})\ \ge\ N_{L|{\rm rest}}(\rho_{t,m})\ \ge\ c_t:=\frac{(s+1)^{-(\ell^\*+1)}}{8L_t\,b^{\ell^\*}}>0 .$$
4. The set $\{t:\exists m,\ \rho_{t,m}\text{ entangled}\}$ is c.e.-complete. The promise problem "$\exists$ gap $\ge c_t$ at all large $m$" versus "separable at all $m$" is therefore undecidable.
5. (Upper bound) $\|\rho_{t,m}-\tau_m\|_1\le\mathbb E[2^{-\ell}]/4\le\frac1{2(s+2)}$, where $\tau_m$ is the $t$-independent separable reference with $F\equiv\frac12$.

*Proof.*
(1) The eigenvalues of $\sigma(F)$ are $F$ and $(1-F)/3$, both in $[1/8,5/8]$. The flag law is uniform because every block has trace $q^{-m}$. The marginal argument of the base construction is used verbatim, since it never uses how $F$ depends on the word. Erasing an internal site averages its uniform key, which fully depolarises $R$, so each block becomes $I_4/4$. Erasing an endpoint leaves $I_2/2$ in every block. In both cases the remaining flags are uniform.
(2) $J_t\le-1$ everywhere, so $F<\frac12$, every block is separable by Horodecki PPT, and F2(iii) applies.
(3) Conjugation by $I\otimes V_h$ commutes with $\Gamma_L$ up to unitary equivalence, so by F2(i) $N(\rho)=q^{-m}\sum\max(0,F_{t,w}-\tfrac12)$, which uses $N(\sigma(F))=\max(0,F-\tfrac12)$. Every word whose $\$$-free prefix is an arrangement of $k^\*$ followed by $\$$ has $F-\tfrac12=1/(8L_tb^{\ell^\*})$. These words have letter-probability at least $(s+1)^{-(\ell^\*+1)}$, with keys free, and all other terms are $\ge0$. Then apply F1.
(4) Membership: at a fixed length, entanglement is decided by exact rational tests on finitely many blocks. Hardness follows from (2) and (3).
(5) Each block contributes $2|F-\frac12|\le2^{-\ell}/4$. The prefix length is geometric with $\Pr[\ell=j]=(s/(s+1))^j/(s+1)$ (truncated at $m$), so $\mathbb E[2^{-\ell}]\le2/(s+2)$. ∎

**What changed relative to the base.** The base needed damping by $b^{-m}$ because its readout used the counts of the whole word. Theorem A damps by $b^{-\ell}$, where $\ell$ is the length of the prefix. A witness then sits in a prefix of fixed length $\ell^\*+1$, whose probability $(s+1)^{-(\ell^\*+1)}$ does not decay with $m$. The exponential smallness moves from $m$ into $t$.

---

## 2. Proposition B: count-exact readouts with permutation symmetry decay

Suppose the internal flags are uniform i.i.d. over an alphabet of size $A=s+1$ (keys may be added freely). Suppose also that $X_w$ is non-separable only when $(k_1,\dots,k_s)(w)\in Z(P_{t})$, where $P_t\not\equiv0$ has degree $\le d$. Then $\operatorname{dist}_1(\rho_{t,m},\mathrm{SEP})\le 2\Pr[k\in Z(P_t)]=O_{s}(d(\log m)^{(s-1)/2}m^{-1/2})$.

*Proof.* Replace each bad block by a separable state; F2(iv) then gives the first inequality. Let $B$ be the box of half-width $r\sqrt m$, with $r=\sqrt{\log m}$, around the mean $m/A\cdot\mathbf 1$.
* Outside $B$: by Hoeffding the mass is $\le2se^{-2r^2}=O(m^{-2})$.
* Inside $B$: by Schwartz–Zippel (DeMillo–Lipton–Schwartz–Zippel), $|Z(P_t)\cap B\cap\mathbb Z^s|\le d(2r\sqrt m+1)^{s-1}$. Every multinomial point mass is $\le C_A m^{-s/2}$ (local limit bound).

Multiply and add. ∎

Every permutation-invariant classical-flag MPO has $X_w$ depending only on the count vector of the whole word. With uniform flags, the base's DPRM readout is of exactly this type. The base construction can therefore not be made robust at all while staying permutation-invariant with that readout. A permutation-invariant design with a "fat" sign-condition readout is not excluded by Proposition B. It is, however, excluded from having a *computable* gap by Theorem C.

---

## 3. Theorem C: no uniform gap in the classical-flag architecture

**Setting.** We are given fixed matrices $M_a\in\mathbb Q(i)^{D\times D}$ for $a\in[q]$, a fixed right end $r^{(k,l)}$ with $k,l\in[d_R]$, and computable left ends $\ell_t^{(i,j)}$ with $i,j\in[d_L]$. These define $(X_{t,w})_{(i,k),(j,l)}=\ell_t^{(i,j)}M_{w_1}\cdots M_{w_m}r^{(k,l)}$ and $\rho_{t,m}=\sum_{|w|=m}|w\rangle\langle w|\otimes X_{t,w}$. Assume $\rho_{t,m}\succeq0$ and $\operatorname{Tr}X_{t,w}=q^{-m}$ (uniform flags). Uniform flags hold whenever all proper marginals are maximally mixed, because the internal $m$-site marginal is $\sum_w\operatorname{Tr}X_w|w\rangle\langle w|$. Neither commutativity nor positivity of entries is assumed. The base construction and Theorem A both satisfy the hypotheses.

**Theorem C.** Fix $c>0$. There is no such family with: $t\in K\Rightarrow\operatorname{dist}_1(\rho_{t,m},\mathrm{SEP}_{\rm full})\ge c$ for all sufficiently large $m$, and $t\notin K\Rightarrow\rho_{t,m}$ fully separable for all $m$. The same holds with $N_{L|\rm rest}$ in place of the distance, and with "PPT across $L|$rest" in the non-halting case.

*Proof.* Suppose such a family exists; we decide $K$. Put $\sigma_w=q^mX_{t,w}$, a normalised state. By F2(ii),(iv),(v), the quantity $\Delta_m:=\mathbb E_w\, d(\sigma_w)$ (with $w$ uniform) satisfies two conditions. In the halting case $\Delta_m\ge c$ for large $m$. In the non-halting case $\Delta_m=0$ for all $m$. For the negativity variant, use $\mathbb E_w N(\sigma_w)=N(\rho)$ directly.

The function $d$ is continuous on the compact set of states. Fix, depending only on $c,d_L,d_R$, a real polynomial $\Pi$ with rational coefficients in the real and imaginary parts of the entries such that $|\Pi-d|\le c/4$ on states. This polynomial exists by Weierstrass. Set $E_m=\mathbb E_w\Pi(\sigma_w)$. Then $|E_m-\Delta_m|\le c/4$ for all $m$. Write $\operatorname{Re}z=(z+\bar z)/2$. A degree-$j$ monomial in entries and their conjugates contributes
$$q^{m(j-1)}\sum_w\prod_{i=1}^j u_iM^{(i)}_{w}v_i=q^{m(j-1)}\Big(\bigotimes_iu_i\Big)\Big(\sum_a\bigotimes_iM_a^{(i)}\Big)^m\Big(\bigotimes_iv_i\Big),\qquad M^{(i)}\in\{M,\bar M\}.$$
Hence $E_m=\mathbf u_t^\top T^m\mathbf v$, where $\mathbf u_t,T,\mathbf v$ have entries in $\mathbb Q(i)$ computable from $t$ and $T$ is independent of $t$. So $E_m=\sum_\theta p_\theta(m)\theta^m$ with algebraic $\theta$, and this closed form is computable exactly from Jordan data.

*Lemma.* A bounded exponential polynomial has $p_\theta=0$ for $|\theta|>1$ and $p_\theta$ constant ($=c_\theta$) for $|\theta|=1$. Moreover $\frac1M\sum_{m<M}|E_m|^2\to\sum_{|\theta|=1}|c_\theta|^2$.
*Proof.* Let $R$ be the largest modulus with $p_\theta\ne0$ and $k$ the top degree among those terms. Then $E_m/(m^kR^m)=\sum a_\theta(\theta/R)^m+o(1)$. Distinct unimodular ratios give a Cesàro mean square of $\sum|a_\theta|^2>0$. If $R>1$, or if $R=1$ and $k\ge1$, this contradicts boundedness. The limit of the mean square follows from the same orthogonality, since terms with $|\theta|<1$ vanish. ∎

$E_m$ is bounded because $d\le2$. In the halting case $|E_m|\ge3c/4$ eventually, so the limit is $\ge9c^2/16$. In the non-halting case $|E_m|\le c/4$, so the limit is $\le c^2/16$. The algebraic number $\sum_{|\theta|=1}|c_\theta|^2$ can be computed exactly: identify the unimodular eigenvalues and take $c_\theta=\mathbf u_t^\top\Pi_\theta\mathbf v$ with the spectral projector $\Pi_\theta$. Comparing it with $c^2/4$ decides $K$, which is a contradiction. ∎

**Remarks.**
(a) The same proof works with a computable $c(t)$, provided $\Pi$ is constructed from $c(t)$; $d$ is a computable function, and Bernstein approximation works. So Theorem A's $c_t$ admits no computable lower bound. The witness size $\ell^\*$ already shows this for that construction specifically.
(b) The decision procedure in fact separates the *Cesàro mean square* of the gap. Any version in which the gap holds on a set of lengths of positive upper density is also excluded.
(c) The essential hypotheses are diagonal internal sites, uniform flags (so that the average is linear in tensor powers), fixed endpoint dimensions, and a translation-invariant bulk. With non-uniform flag weights $p_w=\operatorname{Tr}X_w$, the average $\sum_wp_w\,\Pi(X_w/p_w)$ is no longer a linear recurrence, and the proof breaks down. That route sacrifices maximally mixed marginals, and it is open whether it permits a uniform gap.

---
