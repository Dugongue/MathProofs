# High powers of low-width ROABPs have width-one roots

**Status:** AI-assisted informal proof recorded by [Dugongue](https://github.com/Dugongue), 31 October 2026. Internally reviewed; independent human review, novelty assessment and Lean formalization are pending.

**Main theorem.** Let \(K\) be any field of characteristic zero, let \(d\ge1\), and suppose \(g^d\) has a read-once oblivious algebraic branching program (ROABP) of width at most \(w\) in a variable order \(\pi\). If \(d\ge w\), then \(g\) has width one in the same order. Equivalently,

\[
g(x_1,\ldots,x_n)=c\prod_{i=1}^n g_i(x_i)
\]

for univariate polynomials \(g_i\in K[x_i]\) and a scalar \(c\in K\).

This establishes a sufficient root-closure theorem for the high-exponent regime. It addresses part of the root question in Section 6 of Andrews et al., *On Closure Properties of Read-Once Oblivious Algebraic Branching Programs*, ITCS 2026. It does **not** resolve that question when \(d<w\), and does not claim a new general factor-closure theorem or a separation of complexity classes.

## Definitions

For disjoint variable blocks \(X,Y\), the separation rank \(\operatorname{sr}_{X\mid Y}(F)\) of a polynomial \(F\in K[X,Y]\) is the least \(r\) such that

\[
F(X,Y)=\sum_{i=1}^{r}A_i(X)B_i(Y).
\]

It is also the rank over \(K\) of the finite coefficient matrix with rows indexed by monomials in \(X\) and columns indexed by monomials in \(Y\). Zero has rank zero. A nonzero polynomial has rank one precisely when it is a product of one polynomial from each block.

An ROABP in order \(x_{\pi(1)},\ldots,x_{\pi(n)}\) is a product of univariate polynomial matrices in that order, with a scalar output. Its width bounds the intermediate matrix dimensions. At every prefix/suffix cut, multiplication of the two matrix products expresses the output as a sum of at most \(w\) separated products. Its separation rank at that cut is therefore at most \(w\).

## Lemma 1: a mixed factor forces rank above its multiplicity

Let \(0\ne F\in K[X,Y]\), and let an irreducible factor \(h\) depend on variables from both blocks. If \(h^d\mid F\), then

\[
\operatorname{sr}_{X\mid Y}(F)\ge d+1.
\]

**Proof.** Choose a variable \(y\in Y\) on which \(h\) depends, and put \(E=K(Y\setminus\{y\})\). Regard all other variables of \(Y\) as elements of this coefficient field.

Localization preserves the irreducibility of \(h\) in \(E[X,y]\): the irreducible polynomial \(h\) cannot divide a nonzero polynomial involving only \(Y\setminus\{y\}\), and cannot become a unit because it depends on \(y\). Since it has positive \(y\)-degree, its content over \(E[X]\) is a unit. Gauss's lemma therefore makes it irreducible in \(E(X)[y]\).

Moreover, \(h\) is not associate in \(E(X)[y]\) to a polynomial in \(E[y]\). Such an association, together with primitivity over \(E[X]\), would make it independent of \(X\), contrary to its mixed dependence.

Let \(\alpha\) be a root of \(h\) in an algebraic closure of \(E(X)\). It is transcendental over \(E\). Otherwise its minimal polynomial over \(E\) would share a root with the irreducible \(h\), making \(h\) associate to that polynomial in \(E(X)[y]\), a contradiction.

Suppose a separated representation has \(r\le d\) terms. After passing to \(E\), choose a basis \(B_1(y),\ldots,B_t(y)\) for the span of its right-hand polynomials and combine the left-hand coefficients. Thus

\[
F=\sum_{i=1}^{t}C_i(X)B_i(y),\qquad t\le r\le d,
\]

where the \(B_i\in E[y]\) are linearly independent and some \(C_i\in E[X]\) is nonzero.

Their Wronskian

\[
W(y)=\det\left(B_i^{(j)}(y)\right)_{0\le j<t,\ 1\le i\le t}
\]

is nonzero. To see this directly, change basis so the polynomials have distinct degrees \(e_1<\cdots<e_t\). The leading determinant coefficient is the product of their leading coefficients times the Vandermonde product \(\prod_{i<j}(e_j-e_i)\), which is nonzero in characteristic zero.

Because \(h^d\mid F\), the root \(\alpha\) has multiplicity at least \(d\) in \(F\) as a polynomial in \(y\). The derivatives of orders \(0,\ldots,t-1\) vanish there, giving

\[
\left(B_i^{(j)}(\alpha)\right)_{j,i}
\begin{pmatrix}C_1(X)\\\vdots\\C_t(X)\end{pmatrix}=0.
\]

But \(W(\alpha)\ne0\): a nonzero polynomial over \(E\) cannot vanish at an element transcendental over \(E\). The matrix is invertible, contradicting the nonzero coefficient vector. Hence \(r\ge d+1\). \(\square\)

## Lemma 2: low rank of a power forces a separated root

If \(0\ne g\in K[X,Y]\) and \(\operatorname{sr}_{X\mid Y}(g^d)\le d\), then \(g=A(X)B(Y)\).

**Proof.** Factor \(g\) in the polynomial unique factorization domain. A mixed irreducible factor would occur in \(g^d\) with multiplicity at least \(d\), contradicting Lemma 1. Every irreducible factor therefore belongs entirely to one block; grouping the factors gives the required product. \(\square\)

## Proof of the main theorem

Assume first that \(g\ne0\), and rename the supplied variable order to \(x_1,\ldots,x_n\). At every prefix/suffix cut, the width-\(w\) representation of \(g^d\) gives separation rank at most \(w\le d\). Lemma 2 shows that \(g\) has rank one at each cut.

At the first cut, write \(g=g_1(x_1)G_2(x_2,\ldots,x_n)\). At each later cut, multiplication of the left coefficient space by the nonzero polynomial \(g_1\) is injective, so it preserves separation rank. Thus \(G_2\) has rank one at each of its cuts. Repeating proves \(g=c\prod_i g_i(x_i)\), which is a width-one ROABP in the supplied order. Restoring the names gives the theorem for \(\pi\).

The zero polynomial has a trivial width-one representation. Constants and the one-variable case are immediate. \(\square\)

## Scope and evidence

The proof is structural over every characteristic-zero field. It assumes neither PIT nor an oracle for factors. It does not assert an algorithm for literal root coefficients over an arbitrary abstract field. Characteristic zero is used in the nonvanishing Wronskian argument.

The accompanying `verify.py` checks exact rational coefficient-matrix ranks on 300 finite bivariate power examples. These checks are supporting controls, not a proof of the universal theorem or of novelty. Run `python verify.py` from this directory; the script uses only the Python standard library. The recorded result is in `CHECKS.json`.

Wronskians, unique factorization and the ROABP cut-rank bound are classical. This document supplies the argument above; priority relative to all existing literature has not been established. It should be described as an informal sufficient result addressing the \(d\ge w\) case of the stated question, rather than a complete solution of that question.

## References and attribution

Robert Andrews, Jules Armand, Prateek Dwivedi, Magnus Rahbek Dalgaard Hansen, Nutan Limaye, Srikanth Srinivasan and Sébastien Tavenas, *On Closure Properties of Read-Once Oblivious Algebraic Branching Programs*, ITCS 2026, Article 9, DOI [10.4230/LIPIcs.ITCS.2026.9](https://doi.org/10.4230/LIPIcs.ITCS.2026.9). The root question appears in [Section 6](https://drops.dagstuhl.de/storage/00lipics/lipics-vol362-itcs2026/html/LIPIcs.ITCS.2026.9/LIPIcs.ITCS.2026.9.html#S6); the full version is [arXiv:2509.10725](https://arxiv.org/abs/2509.10725).

The cited paper's authors are credited for the motivating question and surrounding ROABP results. Its published article is CC BY 4.0. This package redistributes no upstream source code or manuscript passages. The proof was developed with AI assistance in the MathProof project; it is not a Lean certificate and is pending independent review.
