# Polynomial-time canonical Cayley tables for Fitting-free groups

**Theorem.** A deterministic polynomial-time algorithm takes the Cayley table of any finite group $G$ with no nontrivial abelian normal subgroup and returns a numbered multiplication table isomorphic to $G$. Two inputs yield identical tables exactly when their groups are isomorphic. The algorithm also returns an explicit isomorphism from each input table to its output. Write $n=|G|$, $N=\operatorname{Soc}(G)$, $Q=G/N$, and $L=\max(2,\lceil\log_2 n\rceil)$. The proof combines Wiebking's permutation-group canonization with a faithful action of the outer automorphism group of the socle of degree $O(\log |G|)$. The proof and complexity analysis are informal.

## 1. Extracting the characteristic socle

Handle the trivial group by returning its one-entry table. For every remaining input, compute the normal closure in $G$ of each nonidentity element by generating the subgroup of its conjugates. The inclusion-minimal distinct groups in this list are exactly the minimal nontrivial normal subgroups. Indeed, every minimal nontrivial normal subgroup is the normal closure of any of its nonidentity elements, and every nontrivial normal subgroup contains a normal closure from the list. The calculation uses polynomially many table operations, including subgroup generation and comparisons of element lists. The same routine in each minimal normal subgroup computes its minimal normal factors.

If $U$ is minimal normal in $G$, take a minimal nontrivial normal subgroup $T$ of $U$. Distinct $G$-conjugates of $T$ are distinct minimal normal subgroups of $U$, so their intersections are trivial and they commute. Their product is nontrivial and normal in $G$ and lies inside $U$, so it is $U$. If $T$ were abelian, this product would be abelian, contrary to the hypothesis on $G$. Its center is normal in $U$, and minimality gives $Z(T)=1$. Its intersection with the product of the other conjugates lies in $Z(T)$, so the product is direct. Any normal subgroup of $T$ is then normal in $U$, which proves $T$ simple. Distinct minimal normal subgroups of $G$ also commute, and each has trivial center. Their product is direct by the same intersection argument. This gives a computed factorization $N=\prod_i S_i$ into nonabelian simple factors.

The centralizer $C_G(N)$ is normal and intersects $N$ in $Z(N)=1$. A nontrivial $C_G(N)$ would contain a minimal normal subgroup of $G$, which belongs to $N$. Hence $C_G(N)=1$. Conjugation embeds $G$ into $\operatorname{Aut}(N)$ and takes $N$ onto $\operatorname{Inn}(N)$. Thus, writing $\pi:\operatorname{Aut}(N)\to\operatorname{Out}(N)$ for the quotient, the image of $G$ is $\pi^{-1}(\overline Q)$, where $\overline Q\cong Q$ is its image in $\operatorname{Out}(N)$. The normal-closure computation also tests the input promise in polynomial time. Every nontrivial abelian normal subgroup contains an abelian minimal normal subgroup.

## 2. Computing a small faithful outer action

For each simple factor, enumerate the ordered generating pairs. Each pair orders the elements by breadth-first search from the identity with a fixed ordered list of the two generators and their inverses. Take the least encoded multiplication table among those orders. This gives a representative $S$ of the simple isomorphism type, plus an isomorphism from the factor to $S$. The two-generation theorem guarantees a generating pair. Compute $\operatorname{Aut}(S)$ by trying possible images of one fixed generating pair. For each proposal, evaluate the discovery words, then test bijectivity and the multiplication table. This enumerates at most $|S|^2$ automorphisms. Conjugation by the elements of $S$ gives $\operatorname{Inn}(S)$. Compute the multiplication table of $A_S=\operatorname{Out}(S)$ as the quotient, and order its elements by their least representative permutations of the numbered table of $S$. Every computation so far is polynomial in $n$. [Babai, Codenotti, Grochow and Qiao, SODA 2011](https://people.cs.uchicago.edu/~laci/papers/soda11.pdf).

The $S_i$ are exactly the minimal normal subgroups of $N$. From a nonidentity coordinate $x_i$ of an element of a normal subgroup of $N$, taking a commutator with an element of $S_i$ produces a nonidentity element in its intersection with $S_i$. This uses $Z(S_i)=1$. That intersection is normal in $S_i$ and equals $S_i$. Consequently every automorphism of $N$ permutes factors of each isomorphism type, and its coordinate maps are arbitrary automorphisms of the corresponding representative $S$. Inner automorphisms act independently within factors. If $r_S$ denotes the number of factors of type $S$, this identifies
$$
W=\operatorname{Out}(N)
  =\prod_S\bigl(A_S^{r_S}\rtimes\operatorname{Sym}(r_S)\bigr).
$$

Use the faithful permutation action of $W$ on $P=\coprod_i(\{i\}\times A_{S_i})$. An element represented by a factor permutation $\sigma$ and coordinate outer maps $a_i$ sends $(i,x)$ to $(\sigma(i),a_i x)$. This is faithful because the block images give $\sigma$ and the images of the identity points give the $a_i$. Record each $g\in G$ in this action by evaluating its conjugation on each factor, using the computed representative identifications, and replacing each coordinate automorphism by its outer coset. Deduplicate the resulting permutations to obtain the complete list $\overline Q$. Changing the initial factor numbering and identifications conjugates this list by an element of $W$.

The degree is
$$
w=|P|=\sum_i|\operatorname{Out}(S_i)|
  =O\!\left(\sum_i\log |S_i|\right)=O(L).
$$
The logarithmic estimate for each simple factor is due to Kohl. It applies to the full outer group. The argument allows arbitrary factor permutation orbits and arbitrary subgroups $\overline Q$. [Kohl, A bound on the order of the outer automorphism group of a finite simple group of given order, Theorem 1](https://stefan-kohl.github.io/preprints/outbound.pdf).

Two groups with the same simple-type multiplicities are isomorphic exactly when their two subgroups $\overline Q$ are conjugate by $W$. An isomorphism of the groups restricts to an isomorphism of their characteristic socles, so it conjugates the images in the outer group. Conversely, a conjugator in $W$ lifts to $\operatorname{Aut}(N)$. It conjugates the inverse images under $\pi$, which are the two embedded groups.

## 3. Canonizing the outer image in the allowed coordinates

Fix the canonical type order and the orders on the representative outer groups from Section 2. Number the $r_S$ block positions for each type in this standard model. Let $\rho:P\to[w]$ be the resulting fixed numbering of the outer-action domain. The initial identification of the input factors with the numbered positions was arbitrary, and all its possible changes are precisely $W$. Put
$$
 C=\{\rho\circ u:u\in W\}.
$$
This is the labeling coset for the permitted coordinate changes. All isomorphic inputs give the same standard model, and their copies of $\overline Q$ there are conjugate by $W$.

Represent $W$ by generators as a permutation group on $P$. Take the left translations within each block, using one for each member of the block's outer group, and the swaps of adjacent same-type blocks with no changes inside the blocks. They generate $W$, and there are $O(w)$ such generators. The explicit list of permutations $\overline Q$ has at most $n$ members. Greedily adjoining a member outside the subgroup so far generated at least doubles its order, so one obtains at most $\lceil\log_2|\overline Q|\rceil$ generators. All of these calculations are polynomial in $n$ using the explicit list. Thus both permutation-generator descriptions have length polynomial in $\log n$.

Apply Wiebking's algorithm from Problem 8 and Theorem 9 to the pair $(\overline Q,C)$, taking the permutation coset input to be the group $\overline Q$ itself. In function-composition notation the two needed guarantees are as follows. The output labelings form a coset $\Lambda$ of the form
$$
 \Lambda=\{\lambda\circ h:h\in N_W(\overline Q)\}
$$
for each $\lambda\in\Lambda$. If a change of labels $\varphi$ transports the input pair, it transports these output labelings by $\lambda\mapsto\lambda\circ\varphi^{-1}$. The running time is $\binom{2w}{k}^{O(1)}\le 2^{O(w)}$, where $k$ is the largest $W$-orbit size on $P$. Here $k=\max_S r_S|A_S|$ because $W$ acts transitively within the union of blocks of each type. The theorem accepts the possibly intransitive ambient group and arbitrary $\overline Q$. [Wiebking, Normalizers and permutational isomorphisms in simply-exponential time, Problem 8 and Theorem 9](https://arxiv.org/pdf/1904.10454).

The following coordinate normalization uses exactly those two guarantees. Choose any coset representative $\lambda\in\Lambda$ and form the numbered group and numbered coset
$$
 Q_0=\lambda\overline Q\lambda^{-1},
 \qquad
 C_0=\{\ell\circ\lambda^{-1}:\ell\in C\}.
$$
They are independent of the choice of $\lambda$. In fact, replacing $\lambda$ by $\lambda\circ h$ with $h\in N_W(\overline Q)$ preserves the first object, and the equality $C h^{-1}=C$ preserves the second. If $\overline Q$ changes to $u\overline Q u^{-1}$ for $u\in W$, the input labeling coset remains $C$. Functoriality permits replacing $\lambda$ by $\lambda\circ u^{-1}$, which gives exactly the same $Q_0$ and $C_0$.

Take the lexicographically least permutation $\gamma$ in the numbered coset $C_0$. This is a polynomial-time operation in $w$. The coset can be presented as $D\theta$, where $D=\rho W\rho^{-1}$ and $\theta=\rho\circ\lambda^{-1}$ are given by generators and a representative. At the first input point, compute the images allowed in the coset by taking the orbit of the representative's image under $D$. Move that image to its least allowed value, update the coset representative, and replace $D$ by the stabilizer of the selected image. Repeat at each subsequent input point. The remaining coset is exactly the set of permutations agreeing with the minimal prefix already fixed. Computing orbits, transporters, and stabilizer generators uses standard polynomial-time permutation-group algorithms. [Wiebking, §2, permutation-group primitives](https://arxiv.org/pdf/1904.10454).

Since $\gamma\in C_0$, the map $u_{\mathrm{lift}}=\rho^{-1}\circ\gamma\circ\lambda$ lies in $W$. The subgroup
$$
 Q_{\mathrm{can}}=\rho^{-1}\gamma Q_0\gamma^{-1}\rho
                 =u_{\mathrm{lift}}\,\overline Q\,u_{\mathrm{lift}}^{-1}
$$
is in the original coordinate model. The first expression is canonical, and the second provides an explicit allowed conjugator. In particular the decoding has a lift to automorphisms of the socle. This normalization works from the coset and functoriality guarantees alone.

## 4. Recovering a canonical multiplication table and a witness

Use the ordered direct product of the canonical simple tables as the numbered socle model. Enumerate $Q_{\mathrm{can}}$ as a lexicographically ordered list of permutations. Its order is at most $n$, and it is explicitly available by applying the conjugator to the old list. Each $v\in Q_{\mathrm{can}}$ determines a permutation of same-type factors and a coordinate outer automorphism in each block. Choose in each coordinate the least automorphism representative of its outer coset, and combine them with the factor permutation to get a lift $\widehat v\in\operatorname{Aut}(N)$. Enumerate
$$
 \left\{\operatorname{inn}(z)\widehat v : v\in Q_{\mathrm{can}},\ z\in N\right\}
$$
in the order of the quotient permutation list and then the lexicographic order of the product coordinates of $z$. The elements are distinct because $Z(N)=1$ and different quotient elements have different images in $W$. The list is the full inverse image of $Q_{\mathrm{can}}$. Compose its automorphisms as permutations of the at most $n$ elements of $N$, and identify each product in the list. This produces the numbered Cayley table in polynomial time.

To output the isomorphism, lift $u_{\mathrm{lift}}$ to $\operatorname{Aut}(N)$ by choosing coordinate representatives just as above. Conjugate the computed action of each $g\in G$ on $N$ by this lift and read off its label in the output list. Conjugation identifies $\pi^{-1}(\overline Q)$ with $\pi^{-1}(Q_{\mathrm{can}})$. The input group was identified with $\pi^{-1}(\overline Q)$ in Section 1, so the resulting bijection respects multiplication. Equal simple-type data and equal $Q_{\mathrm{can}}$ give exactly the same numbered table. Conversely equality of output tables implies isomorphism by the witness construction.

All steps outside the call to Wiebking's algorithm take $n^{O(1)}$ time, where $n=|G|$. That call takes $2^{O(w)}=n^{O(1)}$ time by the bound in Section 2. For $n\ge2$ the input table has $\Theta(n^2\log n)$ bits. Therefore the claimed complexity is polynomial in the input length and includes the cost of writing the full output table and the witness.

## Relation to the literature and retrieved Lean sources

Babai, Codenotti and Qiao already decide isomorphism for all Fitting-free Cayley-table groups in polynomial time. Their Theorem 3 treats transitive permutation transporters, and Corollary 1 lists all isomorphisms for groups with a unique minimal normal subgroup. Grochow and Levet describe parallel canonization for bounded-generator coprime extensions and direct products, and ask about the Weisfeiler–Leman dimension of Fitting-free groups in Question 8.2. Their later work gives an $\mathsf{AC}^3$ isomorphism test for all Fitting-free Cayley-table groups. The construction here supplies the stronger output contract of an explicit canonical table for every Fitting-free group, as a consequence of published canonization and group-theoretic results. The comparison here is limited to these references and does not establish publication priority. Grochow and Qiao's Open Problem 8.1 concerns groups with general abelian solvable radical, which lies outside this result. [Babai, Codenotti and Qiao, ICALP 2012](https://people.cs.uchicago.edu/~laci/papers/icalp12.pdf) · [Grochow and Levet, §8](https://arxiv.org/pdf/2112.11487) · [Parallel and first-order Fitting-free isomorphism](https://arxiv.org/abs/2504.19777) · [Grochow and Qiao, §8.1](https://arxiv.org/pdf/1309.1776).

The current pinned CFSG source supplies `CFSGComparator.classification` in `Comparator/Solution.lean`. The separately pinned two-generation package supplies `CFSGCorollary.exists_closure_pair_eq_top` in its `Comparator/Solution.lean`. Its conclusion is the existence of $a,b$ with $\operatorname{closure}\{a,b\}=\top$ for every finite simple group. The same file gives the conditional version `CFSGCorollary.exists_closure_pair_eq_top_of_classification`, and the catalogue step is `CFSGCorollary.twoGenerated_cfsgIndex`. These are source-level references in their respective pinned environments. The algorithm invokes the classical two-generation theorem and Kohl's bound. The new construction and run-time proof have informal verification status. [CFSG solution at 965a0775](https://github.com/AxiomMath/CFSG/blob/965a0775e82217494217503621b843e1b0e1e337/Comparator/Solution.lean) · [Two-generation solution at 161b0c2d](https://github.com/AxiomMath/CFSGCorollary/blob/161b0c2db2288330b16f347a844cc75a53f11b55/Comparator/Solution.lean) · [Two-generation catalogue at 161b0c2d](https://github.com/AxiomMath/CFSGCorollary/blob/161b0c2db2288330b16f347a844cc75a53f11b55/CFSGCorollary/CFSGIndex.lean).
