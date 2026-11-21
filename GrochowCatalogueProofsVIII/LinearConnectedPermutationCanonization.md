# Linear canonization of connected permutation tuples with a cycle anchor

## GP-0863

Let an ordered tuple of $a$ permutations on $n$ points generate a transitive action, with its permutations given as arrays. There is a deterministic $O(an)$ word-time canonical representative whenever at least one displayed permutation is an $n$-cycle. The same bound holds whenever some vertex uniquely minimizes the vector of its cycle lengths in the displayed permutations. The arity is unrestricted and both hypotheses can be checked within the running time.

### One transitive displayed permutation

Use the first displayed $n$-cycle $\sigma$. This choice is preserved under simultaneous conjugacy. Starting at any point $v_0$, put $v_i=\sigma^i(v_0)$ and record the position of each point. At position $i$ form the tuple
$$
d_i=\bigl(\operatorname{pos}(\pi_j(v_i))-i\bmod n\bigr)_{j=1}^a .
$$
Choosing another start replaces the sequence $(d_0,\ldots,d_{n-1})$ by a cyclic rotation. Conversely, two such named tuples are simultaneously conjugate exactly when their sequences are cyclic rotations: a conjugator carrying the chosen cycle to the other one sends $v_i$ to $v'_{i+s}$, and the displacement identity is precisely the relation for each remaining generator. This argument also shows that the centralizer acts on the point set by the period rotations of the sequence.

Find a lexicographically least rotation by Booth's linear algorithm. It uses $O(n)$ symbol comparisons, and a comparison of two tuple symbols costs $O(a)$ word operations. Use the resulting rotation to output the permutations in cycle coordinates. If several rotations attain the minimum, their displacement strings agree and so do the output arrays. The preprocessing, output and rotation search take $O(an)$ time. [Booth, lexicographically least circular substrings](https://doi.org/10.1016/0020-0190(80)90149-0)

### A point distinguished by cycle lengths

Find each displayed permutation's cycles and record the length of the cycle containing each point. Comparing all $n$ vectors to the best so far costs $O(an)$. If the least vector occurs once, its point is fixed by every isomorphism of input tuples. Starting there, traverse the generator action by breadth-first search, processing the generators in their given order and numbering new points on first encounter. Positive powers of finite permutations also reach their inverses, so transitivity gives every point. The numbered arrays are canonical by the order of the traversal, which takes $O(an)$ time.

This condition can hold even when every individual generator's smallest cycle length occurs at several points. For even $n\ge6$, take two involutions with fixed sets $\{1,2\}$ and $\{1,3\}$. Pair the other points in the first by $(3,4),(5,6),\ldots,(n-1,n)$, and in the second by $(2,n),(4,5),(6,7),\ldots,(n-2,n-1)$. Together these pairs form a path through the points other than $1$. A third involution, pairing $1$ with $2$ and all other points arbitrarily, makes the tuple connected. Only point $1$ is fixed by both first involutions, and no displayed generator is transitive. Further fixed-point-free involutions preserve the unique joint minimum. These two sufficient conditions leave connected tuples without a cycle anchor or a unique minimum outside the claim. [General simultaneous-conjugacy context](https://arxiv.org/abs/2008.01616)
