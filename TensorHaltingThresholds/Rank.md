# Rational tensor rank after a fixed quadratic catalyst

This is an informal theorem conditional on a Diophantine definition of the integers in the rationals. Tensor products below are three-way Kronecker products, denoted by \(\boxtimes\). Write \(S\to T\) if three rational linear maps, one in each mode, take \(S\) to \(T\). Let \(\Delta_r=\sum_{i=1}^r e_i\otimes e_i\otimes e_i\), so \(\Delta_r\to T\) means ordinary tensor rank at most \(r\).

**Theorem.** There are fixed dimensions, a fixed positive integer \(r\), an integral tensor \(T_0\), and one coordinate unit tensor \(E\) with the following properties. For \(T(n)=T_0+nE\), \(n\ge 0\), deciding \(\operatorname{rank}_{\mathbb Q} T(n)=r\) is computably many-one equivalent to the halting problem. Every input has rational rank either \(r\) or \(r+1\). It has rank exactly \(r\) over the reals, every \(\mathbb Q_p\), and each of the fields
\[
\mathbb Q(\sqrt{13}),\quad \mathbb Q(\sqrt{17}),\quad
\mathbb Q(\sqrt{221}),\quad \mathbb Q(\sqrt[3]{2}).
\]

Let \(C\) be the fixed \(2\times2\times2\) rational multiplication tensor of \(\mathbb Q(\sqrt{13})\). Explicit rational linear maps witnessing
\[
\Delta_r\boxtimes C\longrightarrow T(n)\boxtimes C
\]
can be computed in polynomial time in the binary length of \(n\). Deciding whether the same restriction holds after removing \(C\) from both sides is still halting-complete, even when the maps above accompany the input. For every \(k\ge1\), \(\operatorname{rank}_{\mathbb Q}(T(n)^{\boxtimes k})\le 3r^k\).

## A single moving scalar

Fix an effective numbering of machines and the halting set \(H\) for that numbering. By the Davis–Putnam–Robinson–Matiyasevich theorem, \(H\) has an existential polynomial presentation over the integers (nonnegative variables, if used, can be replaced by sums of four squares). Given a fixed existential polynomial definition of \(\mathbb Z\) in \(\mathbb Q\), constrain each integer variable with a fresh copy of that definition and combine simultaneous equations by a sum of squares over \(\mathbb Q\). This gives a fixed \(F_0(t,x)\) and, for every \(m\ge0\), \(m\in H\) exactly when \(F_0(m,x)=0\) has a rational solution. Set \(F(t,x)=t F_0(t-1,x)\). The modified predicate is true at zero and represents halting at \(t=m+1\). The arithmetic premise is the one claimed in [Glazer's manuscript and supporting repository](https://github.com/elliotglazer/diophantine-z-q).

Define
\[
G(t,x,z)=F(t,x)(z^2-13)(z^2-17)(z^2-221)(z^3-2).
\]
The extra factors have no rational roots. Each of the four displayed number fields supplies an explicit root of one factor. Over the reals \(\sqrt{13}\) works. At an odd prime outside \(13,17\), if both 13 and 17 are nonsquare units, their product is a square unit, by reduction mod \(p\) and Hensel lifting. At \(p=13\), \(17\equiv4\); at \(p=17\), \(13\equiv8^2\). At 2, \(17\equiv1\bmod 8\) is a square in \(\mathbb Q_2\). Thus \(G(n,x,z)=0\) has a solution at every completion for every \(n\), even with \(x=0\).

Apply the fixed arithmetic gate construction of [Rank-two matrix completion, Sections 1–2](https://github.com/Dugongue/MathProofs/blob/main/RankTwoAndRingUniversality/RankTwoCompletion.md) to \(G(t,x,z)=0\), treating \(t\) as an independent input. It represents each scalar \(u\) by the difference \(u^+-u^-\) of two nonzero labels. It realizes each nonzero label \(v\) by a row \((v,1)\) paired with a fixed identity anchor. Prescribe the first anchor pairing for \(t^-\) to be 1 and for \(t^+\) to be \(n+1\). All other specified entries are fixed zeros or ones. Variables of the input circuit are given distinct labels before applying its gates. Both pins are nonzero in every characteristic-zero field. Once these two labels are fixed, each remaining auxiliary shift independently avoids at most seven forbidden values, as in the cited construction.

This yields partial matrices \(A(n)\) of fixed shape with a fixed blank set, differing at one specified entry. The identity anchor forces rank at least two. Over every field considered, a rank-two completion exists exactly when \(G(n,x,z)=0\) has a solution. At \(n=0\) choose one rational rank-two completion. Change its varying specified entry to \(n+1\) and leave all other entries untouched. This gives a completion of rank at most three at every \(n\).

## From completion to ordinary rank

Let \(A_0(n)\) fill all \(b\) blanks with zeros and let \(E_1,\ldots,E_b\) be their distinct matrix units. Put
\[
T(n)= A_0(n)\otimes e_0 + \sum_{j=1}^{b} E_j\otimes e_j.
\]
This varies at one tensor entry. For every field \(K\),
\[
\operatorname{rank}_K T(n)=b+\min_{s\in K^b}\operatorname{rank}_K
\left(A_0(n)+\sum_j s_j E_j\right).
\]
For the upper bound, use a rank decomposition of a minimizing completion in the \(e_0\) slice and add \(E_j\otimes(e_j-s_j e_0)\) for each blank. For the lower bound, take a decomposition with \(m\) simple summands. Their third vectors span modulo \(K e_0\), since any nonzero functional on this quotient contracts \(T(n)\) to a nonzero linear combination of the independent \(E_j\). Choose \(b\) third vectors independent modulo \(K e_0\). A linear functional taking value one on \(e_0\) and vanishing on those vectors contracts \(T(n)\) to a completion of rank at most \(m-b\). This is the slice substitution argument underlying [Shitov's tensor-rank universality](https://arxiv.org/abs/1611.01559).

Take \(r=b+2\). The claimed ranks follow. The map \(m\mapsto m+1\) reduces halting to the rank-\(r\) case, and rational rank at most \(r\) is computably enumerable by enumerating rank decompositions. These give both computable reductions.

## Why a single fixed catalyst suffices

Let \(K=\mathbb Q(\sqrt{13})\). Regard \(T\) as a bilinear map on rational inputs with rational vector output. After extending scalars to \(K\), a rank-\(r\) decomposition computes that map by \(r\) scalar multiplications in \(K\), with \(K\)-linear input and output maps. In the rational basis \(1,\sqrt{13}\), those maps become rational linear maps, and each multiplication becomes \(C\). The extended bilinear map viewed over \(\mathbb Q\) is precisely \(T\boxtimes C\), as is seen on pure inputs \(u\otimes a,v\otimes b\) with output \(T(u,v)\otimes ab\). Dualizing the two input maps gives the asserted ordinary tensor restriction.

The maps can also be supplied effectively. Choose \(x=0,z=\sqrt{13}\), evaluate the fixed arithmetic circuit, split free labels by testing a fixed finite list, then choose each auxiliary shift from \(1,\ldots,8\). The referenced compiler constructs the paired rows and columns using field operations and inverses of explicitly nonzero values. Their factorization yields a rank-two completion and the slice construction above gives the \(K\)-decomposition with \(r\) summands. All loops have fixed bounds independent of \(n\). A fixed number of field operations in the fixed quadratic extension on coordinates initially of \(O(\log(n+2))\) bits produces rationals of \(O(\log(n+2))\) bits. This proves polynomial bit time, with no practical bound claimed for the constants.

Finally, \(T(n)^{\boxtimes k}\) has rank at most \(r^k\) over the same \(K\). Apply that algorithm to rational inputs and project each \(K\)-valued output to its rational coordinate along 1. Quadratic multiplication uses three rational multiplications, giving the bound \(3r^k\) and asymptotic rational rank at most \(r\). The decision question here concerns exact rank of a single rational tensor. No tensor-isomorphism undecidability or priority claim follows.
