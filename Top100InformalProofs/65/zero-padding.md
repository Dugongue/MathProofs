# Tensor isomorphism reduces to special-linear tensor isomorphism

This is a readable proof of the reduction formalized in [JouxNarayanan54.lean](../../JouxNarayanan54.lean).

Let $V$ have dimension $n>0$ over any field. Embed $V$ as the first direct summand of $W=V\oplus V$ and pad $T\in V^{\otimes3}$ by zero on every other triple of indices. Each $A\in\mathrm{GL}(V)$ extends to an element of $\mathrm{SL}(W)$ by using a diagonal transformation with determinant $(\det A)^{-1}$ on the unused summand. This proves preservation.

For reflection, the minimal support in a mode of a tensor is the image of the contraction map from the dual of the other two modes. It is contained in the original copy of $V$ for a padded tensor. If three automorphisms of $W$ carry the padded $T$ to the padded $S$, each automorphism maps the corresponding support of $T$ isomorphically onto that of $S$. Extend those three support isomorphisms to automorphisms of $V$ by choosing complementary bases. Each extension has the same restriction on the support as the original transformation. Since the tensor lies in the product of its three supports, the extensions carry $T$ to $S$.

The dimension-zero input is trivial. The padding is a coordinate projection with zeros and doubles the side length.
