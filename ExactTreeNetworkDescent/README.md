# Exact Tree Network Descent

[Ten statements and proofs](PROOFS.md)

A tensor whose entries are homogeneous polynomials in two parameters can be given by a compressed tree of rational-function cores. The main theorem gives deterministic polynomial-time conversion to polynomial cores, with the smallest possible width at every edge and with an explicit total-degree bound. Over the rationals the runtime bound is in binary input length. It also decides the input's homogeneity and integrality promise without expanding the physical tensor.

The paper candidate connects three ingredients. Saturated cut modules retain exact coefficient information. Tensor products of their localizations assemble the modules on the tree. Coefficient-vector message bases let the algorithm operate on the compressed input. Further theorems give a sharp three-parameter limit inherited from Cohn's matrix example, and a sharp one-state allowance with ideal-class cancellation over Dedekind domains.

The proofs credit the classical matrix results and related tensor-network and weighted-automata work. The new tree and compressed algorithm claims are informal, with provisional priority.

Run `python check_examples.py` to reproduce the exact homogeneous width-two branching example and the integral two-copy factorization over the quadratic integer ring. These checks exercise concrete examples used in the proofs. The general algorithm and bounds are given in the proof document.
