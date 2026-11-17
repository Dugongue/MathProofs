# Fixed determinant markers with central or small kernels

Use the fixed marker model in [GapOneSeparation.md](GapOneSeparation.md), over a fixed finite field $F=\mathbb F_q$ with $q>2$. Let $\Gamma$ be its finite group of automorphisms obeying the output determinant restrictions and preserving the designated source spaces or flags. Suppose that projection to the source spaces maps $\Gamma$ onto exactly
$$
K=\prod_{i=1}^k\mathrm{SL}_{n_i}(F), \qquad n_i\ge5.
$$
Write $N$ for the kernel of this projection. Measuring $N$ in this restricted automorphism group is part of the statement. The standard action is required on the designated source spaces.

If the induced map $K\to\operatorname{Out}(N)$ is trivial, the coherent-lift hypothesis in the marker lower bound follows automatically. Consequently all of its bounds hold under this assumption. Two sufficient conditions are that $N$ is central in $\Gamma$, or that
$$
|\operatorname{Out}(N)|<\min_i|\mathrm{PSL}_{n_i}(F)|.
$$

## Proof

Conjugation of $N$ gives a homomorphism $\Gamma\to\operatorname{Aut}(N)$. Elements of $N$ act by inner automorphisms, so the outer action factors through $K$. If this action is trivial, each $\gamma\in\Gamma$ has the same action on $N$ as some element of $N$. Multiplying $\gamma$ by the inverse of that element gives a member of $C_\Gamma(N)$ with the same image in $K$. Thus $C_\Gamma(N)$ maps onto $K$ and has central kernel $N\cap C_\Gamma(N)=Z(N)$.

Every factor $\mathrm{SL}_{n_i}(F)$ with $n_i\ge5$ is perfect and has trivial Schur multiplier, so every central extension of it splits. Use the restrictions of this central extension to get a section on each factor. The images of distinct factors commute: their commutators lie in the central kernel, and for a fixed element from one factor the commutator with elements from the other factor is a homomorphism into that abelian kernel. A perfect factor admits no nontrivial such homomorphism. Multiplying the factor sections gives a coherent lift of the whole product. The centrally closed result used here is the stable-rank case of [Steinberg’s theorem on Schur multipliers, Theorem 1.1](https://www-users.cse.umn.edu/~reiner/REU/REU2019notes/steinberg-covering-groups.pdf).

A nontrivial homomorphism from $\mathrm{SL}_{n_i}(F)$ has image of size at least $|\mathrm{PSL}_{n_i}(F)|$. In fact the latter is simple, and if a normal subgroup of $\mathrm{SL}_{n_i}(F)$ surjects onto it, the residual quotient of the special linear group is abelian. Perfectness then makes that normal subgroup the whole group. Thus every proper kernel lies in the center. Applying this to each factor proves the sufficient condition involving $\operatorname{Out}(N)$.

As a numerical consequence, if all $n_i\ge n$ and the field is fixed, any marker evading the exponential dimension bound by avoiding the coherent lift must have a kernel of size $2^{\Omega(n)}$. A finite group of order $M$ has a generating list of at most $\log_2 M$ elements, since adding a new generator outside the current subgroup at least doubles its size. Therefore $|\operatorname{Out}(N)|\le M^{\log_2 M}$. Meanwhile $|\mathrm{PSL}_{n_i}(F)|$ is $q^{\Theta(n_i^2)}$ by the elementary order formula. A nontrivial outer action requires $(\log_2 M)^2=\Omega(n^2)$.

This conclusion concerns the size of the kernel of a fixed marker construction. Such a kernel can be exponentially large when represented on polynomial-dimensional spaces. The statement therefore does not extend the lower bound to all fixed markers or all reductions.

## Solvable kernels of order coprime to the field characteristic

Assume the lifting kernel $N$ is solvable and $p=\operatorname{char} F$ does not divide its order. Then the fixed marker has exponential total dimension even if there is no prescribed coherent lift. More precisely, either the coherent dimension bound applies or the total dimension is at least
$$
\sqrt{(q^{\min_i n_i-1}-1)\log_q 2}.
$$

Choose a characteristic series of $N$ with elementary abelian factors. For example refine the derived series by the primary decomposition and the successive prime-power subgroups of each abelian factor. Each layer is a vector space in some characteristic $\ell\ne p$. The group of automorphisms of $N$ acting trivially on all layers has order coprime to $p$. To prove this by induction, use the largest proper term $M$ in the series. Restriction to $M$ has image of order coprime to $p$ by induction. An automorphism $\alpha$ in its kernel fixes $M$ pointwise and acts trivially on $N/M$. For every $x\in N$, $\alpha(x)x^{-1}\in Z(M)$, because $\alpha(x)$ and $x$ have the same conjugation on $M$. These coordinates give an injective group map of the kernel into the product of $|N|$ copies of $Z(M)$. The kernel and hence the entire group have order coprime to $p$.

Consider one factor $\mathrm{SL}_{n_i}(F)$ and write $n=n_i$. In that factor take the elementary abelian subgroup $U$ of matrices with an arbitrary off-diagonal first row and otherwise identity. It has order $q^{n-1}$. A Sylow $p$-subgroup $P$ of the preimage of $U$ in $\Gamma$ maps isomorphically onto $U$, since the kernel has order coprime to $p$. The embedded $\mathrm{SL}_{n-1}(F)$ normalizes $U$. Each of its elements has a lift to $\Gamma$, and that lift sends $P$ to another Sylow subgroup of the preimage of $U$. Conjugate it back to $P$ by an element of this preimage. This adjustment does not change the induced conjugation action on $U$, which is abelian. Thus the normalizer of $P$ in $\Gamma$ acts on its characters as $\mathrm{SL}_{n-1}(F)$ does on the dual of the additive group $F^{n-1}$.

If $P$ acts nontrivially on any elementary abelian layer of $N$, decompose its linear action after extending that layer's coefficient field to an algebraic closure. This is possible because $\ell\ne p$. The weight of one nontrivial character occurs. The normalizer just constructed forces the occurrence of all $q^{n-1}-1$ nontrivial characters, using the identification with dual vectors by the field trace. Each requires a nonzero weight space, so the layer has dimension at least $q^{n-1}-1$ and $|N|\ge 2^{q^{n-1}-1}$. The embedding of $N$ into the product of the full linear groups on the labelled spaces bounds $|N|$ above by $q^{\sum_j(\dim W_j)^2}$. This gives the claimed total dimension lower bound.

If the layer actions are all trivial, this $P$ centralizes $N$ because its conjugation action is a $p$-group contained in the previously computed automorphism kernel of order coprime to $p$. The image of $C_\Gamma(N)$ is normal in $K$ and contains $U$, hence contains the entire $\mathrm{SL}_{n_i}(F)$ factor by the elementary transvections. Therefore if this holds for each factor, the outer action of $K$ is trivial and the coherent lower bound applies.

## Nilpotent kernels of arbitrary order over F3

Suppose $N$ is nilpotent over $F=\mathbb F_3$. Write $N=N_3\times N_{3'}$ as the direct product of its Sylow $3$-subgroup and its subgroup of order coprime to $3$. These two groups are characteristic in $N$. Apply the previous layer argument just to the action on $N_{3'}$. For this argument use a Sylow $3$-subgroup of the preimage of $U$ in $\Gamma/N_3$, whose kernel over $U$ is $N_{3'}$. The quotient acts on $N_{3'}$ by conjugation because $N_3$ centralizes it. Either some layer is exponentially large as above, or the induced outer action on $N_{3'}$ is trivial. In the latter case $C=C_\Gamma(N_{3'})$ projects onto $K$, with kernel $N_3\times Z(N_{3'})$. The quotient $C/N_3$ is a central extension of $K$ and so splits. The preimage in $C$ of the image of a section is a subgroup of genuine marker automorphisms that projects onto $K$ with kernel $N_3$ of odd order. The Sylow-diagonal proof in [GapTwoSeparation.md](GapTwoSeparation.md) uses only such a subgroup, so its exponential bound applies. Thus arbitrary nilpotent lifting kernels also require exponential total dimension over F3 under the fixed-marker assumptions.
