# Linear canonical assembly for disconnected permutation tuples

## GP-0864

For an ordered tuple of permutations given as arrays, canonical assembly from connected-component canonical representatives takes deterministic linear time in their total input length $L$ in the word-RAM model, even with arbitrarily long common prefixes, repeated components and unbounded tuple arity. More precisely, for canonical connected cost $T(a,n)$, arbitrary tuples on component sizes $n_i$ have canonical cost
$$
O\!\left(L+\sum_i T(a,n_i)\right).
$$
In particular linear-time connected canonization is equivalent to linear-time unrestricted canonization. The assembly also identifies exactly the isomorphism classes of the connected components, grouping all duplicates.

Traverse the point orbits in the generator graph in time $O(L)$ and form the restricted arrays in local coordinates. Any simultaneous conjugator preserves connected orbits and restricts to a conjugator on each one. Conversely any matching of isomorphic component tuples extends, by taking their component conjugators together. Thus the component multiset is a complete invariant.

Use the connected canonizer on each component. Encode its output by its size followed by its arrays in a fixed order. All tokens are positive integers at most the total number of points plus one. Form one text by appending each component string followed by the same zero separator. The text has length $O(L)$ when the point count is charged to the input. Its integer alphabet has size $O(L)$. Construct a suffix array in linear time. In its ordering retain only suffixes whose positions are actual component starts. If two components first differ before a separator their suffix order is their component-string order. If one is a strict prefix, its separator zero occurs opposite a positive token, again giving that order. Equal component strings may be ordered by later text, but they form a contiguous block among the retained starts. Thus the retained sequence sorts the component strings without a comparison-sort cost. [Linear-work suffix arrays on integer alphabets](https://alumni.cs.ucr.edu/~rakthant/cs234/06_KSB_Linear%20Work%20Suffix%20Array%20Construction.pdf)

Compare consecutive retained component strings for equality, stopping at their separators. The sum of the costs is linear because each component's length is charged at most twice. Lay out the components in the resulting order, using each one's provided canonical numbering and adding the running point offset. The order within an equal block does not affect these arrays. This constructs a canonical tuple and its duplicate-component multiplicities. The connected specialization gives the reverse implication for linear-time canonization. [Permutation-tuple conjugacy context](https://arxiv.org/abs/2008.01616)
