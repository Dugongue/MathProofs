# Positive-promise approximation of fixed-target epimorphisms

## GP-0370

Fix any finite nonabelian simple group $S$. For input given by an arbitrary finite presentation, approximating the number of surjections onto $S$ to any fixed multiplicative factor on the promise of at least one surjection is possible in randomized polynomial time if and only if $\mathsf{RP}=\mathsf{NP}$. The same equivalence holds for existence of an FPRAS.

Write $E(P)=|\operatorname{Epi}(P,S)|$ and $a=|\operatorname{Aut}(S)|$. For $j\ge1$,
$$
   E(P^j\times S)=jE(P)+a.
$$
Surjectivity makes each direct factor image normal in $S$, because it commutes with all other factor images. Simplicity makes at least one factor surject, and the trivial center forces all other factor images to be trivial. This identifies the surjections bijectively and proves the formula. A presentation for the product consists of tagged generator copies, copied relators and all cross-factor generator commutators. It has polynomial size for fixed $j$.

The postcomposition action of $\operatorname{Aut}(S)$ on surjections is free. Hence the new count equals $a$ in the negative case, and is at least $(j+1)a$ in the positive case. Both cases satisfy the positive-count promise. For a fixed approximation factor $C\ge1$, choose an integer $j$ with $j+1>C^2$. The two possible intervals of successful estimates are then disjoint. Kuperberg and Samperton's hardness for deciding surjectivity onto $S$ gives a randomized decision procedure for SAT. Amplify before running the ordinary SAT bit-fixing self-reduction and accept only if the resulting assignment passes the deterministic verifier. This gives $\mathsf{SAT}\in\mathsf{RP}$, so $\mathsf{RP}=\mathsf{NP}$.

In the reverse direction the count is a $\#\mathsf P$ function. A witness is one image for each generator. Evaluate the relators in the fixed group and test whether the images generate $S$. Stockmeyer's approximate-counting algorithm runs in randomized polynomial time with an NP oracle, including polynomial dependence on the inverse relative error. Under $\mathsf{RP}=\mathsf{NP}$ amplify each simulated NP query enough for a union bound over the polynomial adaptive computation, yielding an FPRAS.

The product uses the commuting-factor principles in the portfolio's finite-group epimorphism notes, and the presentation model is essential to the hardness reduction. [Finite Cayley-table counting, an earlier model](https://github.com/Dugongue/MathProofs/blob/d7366c4348bc03f0e93cb8674db191de32ba58bf/GroupIsomorphismAndEpimorphisms/ConstantTargetEpimorphisms.md) · [Kuperberg–Samperton](https://msp.org/gt/2018/22-6/gt-v22-n6-p10-p.pdf) · [Stockmeyer](https://doi.org/10.1145/800061.808740)
