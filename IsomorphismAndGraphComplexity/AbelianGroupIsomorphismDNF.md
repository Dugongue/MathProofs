# Abelian Group Isomorphism requires quasipolynomial-size DNFs

This is an affirmative answer to Grochow, Kardeş and Levet's [Question 7.3](https://arxiv.org/html/2608.26257v2#S7), in its valid multiplication-table promise model. The proof also gives the same lower bound when each literal can be replaced by a parity of arbitrary table bits. It uses their rank-to-Cayley-table construction and the classical dimension bound on affine spaces of invertible matrices.

## Theorem

For groups of order $n=2^{2k}$, any DNF deciding isomorphism on pairs of valid Abelian Cayley tables has at least
$$
\prod_{i=1}^k(2^i-1)\ \ge\ n^{(\log_2 n)/8+1/4}\,/\,4
$$
terms. The lower bound holds for a disjunction of conjunctions of affine Boolean forms of the binary table bits. It already holds with the second table fixed to one table of $(\mathbb Z/4)^k$.

## Proof

For $M\in \operatorname{Mat}_k(\mathbb F_2)$, put a multiplication on pairs in $\mathbb F_2^k\oplus\mathbb F_2^k$ by
$$
(u,z)(v,w)=(u+v,z+w+M(u\odot v)),
$$
where $\odot$ denotes entrywise multiplication. Bilinearity of $(u,v)\mapsto M(u\odot v)$ gives associativity, symmetry gives commutativity, and $(0,0)$ is the identity. Each element squares to $(0,Mu)$ and its fourth power is the identity, so the tables are valid Abelian group tables for all $M$. Write the resulting group as $G_M$.

The subgroup of squares has order $2^{\operatorname{rank} M}$. An Abelian group of order $2^{2k}$ and exponent dividing four has the form $(\mathbb Z/4)^r\times(\mathbb Z/2)^{2k-2r}$, with $r$ given by the base-two logarithm of the order of the square subgroup. Therefore
$$
G_M\cong G_{I_k}\quad\Longleftrightarrow\quad M\in\operatorname{GL}_k(\mathbb F_2).
$$
Encode group element labels by the $2k$ bits $(u,z)$, as in Proposition 4.5 of the source. For fixed table indices each output label bit is an affine form of the coordinates of $M$. Under this restriction an AND of affine Boolean forms is an affine system of equations in $M$. Its set of accepted matrices is empty or an affine subspace. For a correct DNF, every one of those sets is contained in $\operatorname{GL}_k(\mathbb F_2)$, and together they cover $\operatorname{GL}_k(\mathbb F_2)$.

Let $A+V$ be a nonempty accepting affine subspace, where $A$ is invertible and $V$ is linear. After left multiplication by $A^{-1}$ the subspace is $I_k+A^{-1}V$, still all invertible. Thus no matrix of $A^{-1}V$ has eigenvalue $1$, which is the only nonzero field element. The dimension theorem for trivial-spectrum spaces over an arbitrary field gives $\dim V\le\binom{k}{2}$. The theorem for this dimension bound explicitly includes $\mathbb F_2$. [de Seguins Pazzis, Theorem 1, citing Quinlan and de Seguins Pazzis](https://arxiv.org/pdf/1102.2493#page=4)

Consequently each term covers at most $2^{\binom{k}{2}}$ matrices. Counting ordered bases and dividing gives
$$
\frac{|\operatorname{GL}_k(\mathbb F_2)|}{2^{\binom{k}{2}}}
=\prod_{i=1}^k(2^i-1)
=2^{k(k+1)/2}\prod_{i=1}^k(1-2^{-i}).
$$
The first factor in the last product is $1/2$, and the product of the remaining factors is at least $1-\sum_{i=2}^k 2^{-i}\ge 1/2$. This proves the displayed lower bound.

## Exact count on the matrix-generated family

On the restricted instances $(G_M,G_{I_k})$, the same number of ordinary DNF terms suffices. Let $U$ be the group of unit upper triangular binary matrices, and use one conjunction per right coset $U A$ in $\operatorname{GL}_k(\mathbb F_2)$. The condition for a term is that $M A^{-1}$ is unit upper triangular. Its defining equations each prescribe a dot product of a single row of $M$ with a fixed vector $x$. That dot product is one of the label bits of $(x,0)(x,0)=(0,Mx)$ in the first Cayley table, so each defining equation is one table-bit literal. The cosets partition all invertible matrices and have size $2^{\binom{k}{2}}$. This gives equality for the restricted family.

## Scope

The source's CNF-of-XOR lower bound fixes a group corresponding to rank $k-1$ and bounds falsifying sets of clauses. For the DNF question, fixing the group corresponding to rank $k$ instead makes the satisfying set of each term an affine space of invertible matrices. This argument uses only valid Abelian group tables. The conclusion covers DNF and disjunctions of conjunctions of affine Boolean forms.

Source: [Grochow, Kardeş and Levet, Group Isomorphism and the Polylogarithmic-Time Hierarchy](https://arxiv.org/html/2608.26257v2), Proposition 4.5 and Question 7.3.
