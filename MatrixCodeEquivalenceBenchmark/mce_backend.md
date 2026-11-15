# Packed binary matrix-code solver

The packed C++ backend covers binary matrix-code pairs with matrix sides up to 128 and code dimension up to 16, subject to explicit search limits. It uses the witness convention $L A_i R = B(S e_i)$ and checks all generators. The prime-field solver reports the inverse right factor, so its convention is $L A_i = B(S e_i)R$. The two conventions define the same equivalence.

For $x$ in the binary coefficient space let $c(x)$ be the rank of $A(x)$. The table is cheap to construct by walking binary Gray order and updating a packed matrix by XOR with one basis matrix. For each pair of ranks $i,j$, the integer correlation at a shift $h$ counts the coefficient words $x$ such that $c(x)=i$ and $c(x+h)=j$. Any linear rank-preserving coefficient map transports these counts to its image of $h$. Exact Walsh transforms compute the correlations as an additive convolution on the binary coefficient space.

Uniform ranks give uniform rank correlations. On suitable rectangular cases with code dimension at most eight, the backend also looks at the rank of the stack of two matrices whose coefficient vectors span a plane. The rank is independent of the plane basis by invertible block row operations, and is preserved under the common left and right maps. These counts distinguish coefficient points in some cases where ranks and their correlations are constant. The lift uses linear equations and checks invertible factors. A bounded or unsupported lift reports unknown unless another exact certificate decides the instance. [Rank and lift proofs](RankProfiles.md)

```powershell
g++ -std=c++20 -O3 -march=native mce_backend.cpp -o mce_backend.exe
python mce_backend_controls.py --output reproduced-binary.json
```

The controls generate the inputs, verify positive witnesses independently in Python, and time the persistent solver through verification. The forty-eight square positives and negatives use six square formats and four inputs of each label per format. The remaining twenty-four generated inputs use three rectangular formats with the same per-label count. A separate exhaustive test compares all 630 pairs of the 35 dimension-two subspaces in the binary 2 × 2 matrix space, whose GL orbits number five. Two inequivalent 6 × 6 pencils with identical rank profiles exercise all six binary projective coefficient maps. [Raw benchmark and ablation](mce_backend_results.json)
