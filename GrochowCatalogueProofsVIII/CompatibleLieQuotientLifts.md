# Lifting two compatible quotient isomorphisms through abelian ideals

## GP-0414

Given finite-dimensional Lie algebras over an explicit finite field, two specified abelian ideals in each algebra, and isomorphisms on the two corresponding pairs of quotients, there is a deterministic polynomial-bit algorithm deciding and constructing a single Lie isomorphism inducing both given maps. The intersection of the two ideals need not be central. In particular this applies to the associated compact Lie presentations of exponent-$p$ groups in the Lazard range. [Effective Lazard correspondence](https://doi.org/10.1016/j.jalgebra.2011.12.009)

### The one prescribed quotient

Write the marked ideals as $A,B$ and $A',B'$. Check that the supplied isomorphisms take the images of the other ideals to the corresponding images, and that the induced maps on the quotients by $A+B$ and $A'+B'$ agree. These are linear and bracket tests. An algebra modulo $A\cap B$ is the fiber product of its two quotients over the quotient by $A+B$. The map into the fiber product is injective. A compatible pair of residues has representatives differing by an element of $A+B$, so changing them by elements of $A$ and $B$ makes them agree. This proves surjectivity and hence the fiber-product assertion. Thus the checks give one prescribed isomorphism on the quotients by $A\cap B$ and $A'\cap B'$. Any lift inducing that isomorphism induces both original maps.

### A linear category for lifts

Identify the two quotient algebras with $Q$ by that map. The kernels $I,I'$ are abelian because each is contained in an abelian ideal. Choose vector-space sections and write the extension models as $E=I\oplus Q$ and $E'=I'\oplus Q$, with actions $\rho,\rho'$ of $Q$ and bracket defects $c,c'$. A block linear map from $E$ to $E'$ whose quotient map is scalar multiplication by $\lambda$ has the form
$$
(u,x)\longmapsto(Tu+f(x),\lambda x).
$$
Retain it when
$$
\begin{aligned}
 T\rho(x)&=\rho'(x)T,\\
 T c(x,y)+f([x,y])&=\lambda c'(x,y)+\rho'(x)f(y)-\rho'(y)f(x).
\end{aligned}
$$
These are linear equations in $(T,f,\lambda)$. For $\lambda=1$ they are exactly the condition of preserving the bracket, by expanding on $I\times I$, $I\times Q$ and $Q\times Q$.

Define the analogous spaces in both directions and for each algebra with itself. They contain identities and are closed under composition. In fact for consecutive maps $(T_1,f_1,\lambda_1)$ and $(T_2,f_2,\lambda_2)$ the composite has parameters $(T_2T_1,T_2f_1+\lambda_1f_2,\lambda_2\lambda_1)$. Substituting the equations for the two maps yields precisely the equations for this composite. Thus the four computed spaces form the blocks of an explicit finite-dimensional associative algebra $D$ on $E\oplus E'$. Compute a basis and its structure constants by linear algebra. Let $e,e'$ be its two block identities.

The right $D$-modules $eD$ and $e'D$ are isomorphic if and only if there are mutually inverse retained maps between $E$ and $E'$. Indeed the image of $e$ under a right-module isomorphism is an element $z\in e'De$, and its inverse gives $w\in eDe'$ with $zw=e'$ and $wz=e$. Conversely these identities give inverse module maps by left multiplication. Apply deterministic finite-field module isomorphism constructively to the supplied matrices of right multiplication. Its output gives such a $z$. If $Q\ne0$, invertibility forces $\lambda\ne0$, and scaling the linear solution by $\lambda^{-1}$ gives a bracket-preserving isomorphism with quotient identity. If $Q=0$, both extensions are abelian and linear isomorphism suffices. All matrix and module dimensions are polynomial in the input dimensions. The reduction constructs a lift whenever one exists, including for nontrivial quotient actions on the abelian kernel. [Constructive module isomorphism](https://ix.cs.uoregon.edu/~luks/ModIso.pdf)
