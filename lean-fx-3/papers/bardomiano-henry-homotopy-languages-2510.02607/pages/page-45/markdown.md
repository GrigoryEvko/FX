The picture we should have in mind on the dependency of types is the usual one about simplices. A 1-simplex depend on two 0-simplicies, a 2-simplex consist of three 0-simplicies and three 1-simplicies connecting them, and so forth.

One can see that the faces of an $n$-simplex are obtained via the dependencies, or context in which is defined. However, we can still adopt the usual notation for faces. Specifically, for each $n \in \mathbb{N}$ one has the faces $d_i(\sigma_{0123...(i-1)i(i+1)...n}) := \sigma_{0123...(i-1)(i+1)...n}$ is the $(n-1)$-simplex “opposite” to the $i$-th vertex of $\sigma_{012...n}$. This simplex is already defined, and it is used in the construction of $\sigma_{012...n}$. We emphasize that this is not part of the theory, but just a convenient and familiar shortcut.

The degeneracy operator is part of the theory and needs to be introduced:

$$\sigma_{0123...(i-1)i(i+1)...n} : n\text{-simplex} \vdash s_i(\sigma_{0123...(i-1)i(i+1)...n}) : (n+1)\text{-simplex}$$

where $s_i(\sigma_{0123...(i-1)i(i+1)...n}) := \sigma_{0123...(i-1)i(i+1)...n}$ is the $(n+1)$-simplex that contains $\sigma_{0123...(i-1)i(i+1)...n}$ as its $i$-th and $(i+1)$-faces. We have one of such operations for $0 \le i \le n$. The way we have introduced this operation is not completely correct as we are missing the dependencies for $n$-simplex and $(n+1)$-simplex and the context, nevertheless we can infer them. For example:

$$x, y : 0\text{-simplex}, f : 1\text{-simplex}(x, y) \vdash s_1(f) : 2\text{-simplex}(x, y, y, f, s_0(y), f)$$

where $s_0(y)$ is the degeneracy of $y$ or the “identity of $y$” and is constructed previously.

We also expect the simplicial identities to be satisfied. However, we do not need to postulate all of them as axioms of the theory since some of them are given via dependencies or by the typing of the operations. The only equation we postulate is $s_i s_j = s_{j+1} s_i$ for $i \le j$. On the one hand, the usual equation $d_i d_j = d_{j-1} d_i$ for $i < j$ only involves faces, therefore everything is encoded in the dependency. On the other hand, the equation

$$d_i s_j = \begin{cases} s_{j-1} d_i, & i < j \\ Id, & i = j, j+1 \\ s_j d_{i-1}, & i > j+1 \end{cases}$$

is valid from the definition of degeneracies and dependency of the faces.

We should note again that there is no visible difference in the language of the Joyal model structure and the language of the Kan-Quillen model structure as these have the same cofibrations. The only difference is that

45