# Parallel transversals for permutation groups of arbitrary order

**Theorem.** Let $H\le G\le\operatorname{Sym}(m)$ be given by explicit lists of generating permutations. A logspace-uniform family of Boolean circuits computes a right or left transversal for $H$ in $G$ on the promise that the index has a known upper bound $K$. If $M$ is the binary input length, the circuits have size $(M+K)^{O(1)}$ and depth $(\log(M+K))^{O(1)}$. In particular, for every fixed polynomial index bound, Transversal belongs to functional $\mathsf{NC}$ for arbitrary $G$. This answers Michael Levet's Question 8.2 affirmatively in the formulation of §2.4. [Statement of the question and input promise](https://arxiv.org/html/2604.13953v1#S8) · [Definition and preceding bound](https://arxiv.org/html/2604.13953v1#S2.SS4).

## The traversal word

Write $s_0,\ldots,s_{a-1}$ for the input generators of $G$. Pad the list by an identity generator if needed so $a\ge1$. Take $d=2a$ ports, with port $2i$ acting by $s_i$ and port $2i+1$ by $s_i^{-1}$. Write $u_j$ for the permutation at port $j$ and $\pi(j)$ for its paired port, exchanging $2i$ and $2i+1$. The pairing is determined by positions, so it works with repeated generators or involutions.

Consider the right cosets $Hg$. From $Hg$, port $j$ leads to $Hgu_j$. This is well-defined under replacement of $g$ by another representative. Its reverse port is always $\pi(j)$ because $u_{\pi(j)}=u_j^{-1}$. This gives a $d$-regular undirected Schreier multigraph whose rotation sends
$$
 (Hg,j)\longmapsto(Hgu_j,\pi(j)).
$$
The graph is connected because the generators and inverses generate $G$. It has $[G:H]$ vertices. The $\pi$-consistent labeling condition and the allowance for loops and parallel edges are part of Reingold's rotation model. [Reingold, §2.2 and Definition 5.1](https://omereingold.wordpress.com/wp-content/uploads/2014/10/sl.pdf).

For each $1<k\le K$, Reingold's Theorem 5.4 constructs a sequence of absolute ports $j_{k,1},\ldots,j_{k,L_k}$ that visits all vertices of every connected $d$-regular graph of order $k$ with this port pairing, from any start. The constructor is a deterministic logspace transducer on unary $k$ and the port permutation $\pi$, so $L_k$ is polynomial in $k+d$. The word for $k=1$ can be empty. The coset graph is used only in the correctness argument. The construction of each direction sequence depends on $k,d,\pi$, which are known without enumerating any cosets. [Reingold, Theorem 5.4](https://omereingold.wordpress.com/wp-content/uploads/2014/10/sl.pdf).

## Parallel evaluation and exact output

For every $k$ and every prefix length $0\le t\le L_k$, compute the permutation
$$
 w_{k,t}=u_{j_{k,1}}\cdots u_{j_{k,t}},
$$
with the empty prefix giving the identity. Each list represents a walk starting afresh at $H$. In the list for $k=[G:H]$, the cosets $Hw_{k,t}$ visit every vertex. Every candidate from every list belongs to $G$, so pooling the lists for all $k\le K$ gives a duplicate-allowed cover of the right cosets without requiring the exact index as input.

Compute permutation inverses and products with ordinary Boolean circuits. For example, in permutation-matrix coordinates composition is the Boolean matrix product, with the disjunction over the intermediate point. Compute each prefix product by its own balanced binary tree. There are at most $K(\max_k L_k+1)$ candidates. These trees have bounded-fan-in depth $O((\log(M+K))^2)$ and polynomial total size in $M+K$. A logspace circuit constructor can rerun Reingold's transducer to read the port at any position and wire that leaf to the corresponding input generator or its inverse. This use of logspace is in uniformity, so the product trees evaluate all prefixes in parallel.

Fix an ordering of the pooled candidates, say $w_0,w_1,\ldots$. For every pair compute
$$
  Hw_i=Hw_j\quad\Longleftrightarrow\quad w_iw_j^{-1}\in H.
$$
Use the uniform $\mathsf{NC}$ algorithm for membership in a permutation group given by generators, instantiated on $H$, for all pairs in parallel. Keep $w_i$ if every earlier $w_j$ has a different coset. This retains exactly one representative per right coset. For an ordinary compact output list, compute the prefix sums of the keep bits with balanced binary addition, and multiplex each retained permutation to its indicated array position. Return the count and permit padding past that count in the fixed-width circuit output. Inverting the retained permutations gives the left transversal. [Babai–Luks–Seress, Permutation Groups in NC](https://ix.cs.uoregon.edu/~luks/NC.pdf).

The circuit bounds use the total binary input length and the numerical index bound. For the standard polynomial-index promise $K=m^c$ with fixed $c$, $K$ can be chosen by the logspace uniformity machine. The result applies even when $|G|$ is exponential in $m$ and $H$ is nonnormal.

## Consequences and provenance

The same method returns the explicit right action on the coset labels. For each representative $w_i$ and generator $s$, find the unique retained $w_j$ for which $w_i s w_j^{-1}\in H$, using another parallel bank of membership tests. This constructs the numbered Schreier graph if desired.

In the small-domain regime of Levet's Lemma 2.7, the permutation degree is $O(\log n)$, and the allowed index bound is $(\log n)^{O(\log\log n)}$. With the $m^{O(1)}$-size generator lists at the small-domain permutation-group interface, $\log(M+K)=\operatorname{poly}(\log\log n)$ and $(M+K)^{O(1)}\le\operatorname{poly}(n)$. Thus the transversal subroutine there has depth $\operatorname{poly}(\log\log n)$ wherever the stated index cap holds. The conclusion following Question 8.2 identifies this call as one factor in the depth for small code equivalence. A full transfer requires an independent justification of that index cap at the recursion's transitive steps. The general order theorem for primitive groups with bounded nonabelian composition factors does not give a uniform quasipolynomial bound when the composition-factor parameter is allowed to grow with the degree. The natural action of $\operatorname{Sym}(m)$ illustrates the distinction. [Levet, Lemma 2.7, Proposition 3.3 and Question 8.2](https://arxiv.org/html/2604.13953v1#S8) · [Babai–Cameron–Pálfy order theorem](https://doi.org/10.1016/0021-8693(82)90323-4).

Kantor, Luks and Mark proved the earlier small-$|G|$ result and announced a general $\mathsf{NC}$ solution in an in-preparation work by Kantor and Luks. Levet flagged that he could not locate the stronger proof. A targeted search did not locate a published proof of the general statement. The argument here is an independent deduction from Reingold's universal traversal theorem and the standard permutation-group membership algorithm. Publication priority remains unestablished. [Kantor–Luks–Mark, Sylow Subgroups in Parallel, §3.5 and reference KL2](https://darkwing.uoregon.edu/~kantor/PAPERS/klmFINAL.pdf).

Verification status is informal.
