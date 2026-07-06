### 3.8 Segal spaces

We denote $\mathbf{ssSet} := [\Delta^{\mathrm{op}}, \mathbf{sSet}] = [\Delta^{\mathrm{op}} \times \Delta^{\mathrm{op}}, \mathbf{Set}]$ as the category of simplicial spaces, or bisimplicial sets. This category has two model structures that are obtained as left Bousfield localizations of the Reedy model structure. For both of these localizations, we use the Kan–Quillen model structure from the previous section. Recall that this model structure is cofibrantly generated. The set of generating cofibrations is the set of boundary inclusions. We will use the following facts and notation.

- There is an adjunction of two variables $\square : \mathbf{sSet} \times \mathbf{sSet} \rightarrow \mathbf{ssSet}$ defined as $(X \square Y)_{mn} := X_m \times Y_n$ for each $m, n \in \mathbb{N}$. This is called the box product.
- $\mathbf{sSet}$ can be seen as vertically embedded into $\mathbf{ssSet}$. If $X \in \mathbf{sSet}$, then it can be seen as a simplicial space $X \square \Delta[0]$. There is also a horizontal embedding by setting $\Delta[0] \square X$.
- For $[m] \in \Delta$ we write $F(n) := \Delta[n] \square \Delta[0]$ and $\partial F(n) := \partial \Delta[n] \square \Delta[0]$.
- The simplicial spaces $F(n)$ represent the $n$-th mapping space functors, respectively $Map(F(n), X) = X_n$.

There is map $\iota : F(1) \coprod_{F(0)} \cdots \coprod_{F(0)} F(1) \rightarrow F(n)$, where the colimit on left has $n$ factors. The following two model category structures were constructed by Rezk [Rez01].

**Theorem 3.33.** *The category admits a unique simplicial model category structure such that:*

1. *The cofibrations are the monomorphisms.*
2. *Fibrant objects are simplicial spaces $X$ such that the map*

$$X_n \rightarrow X_1 \times_{X_0} \cdots \times_{X_0} X_1$$

*induced by $\iota$ is a Kan equivalence. The fibrant objects are called Segal spaces.*

3. *The weak equivalences are the maps $f : X \rightarrow Y \in \mathbf{ssSet}$ such that*

$$Map(f, W) : Map(Y, W) \rightarrow Map(X, W)$$

*is a Kan equivalence for every Segal space $W$.*

49