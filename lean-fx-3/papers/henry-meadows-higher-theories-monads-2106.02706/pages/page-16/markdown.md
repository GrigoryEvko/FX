$\text{Fun}(K, -)$ preserves products, it is immediate that the corresponding functors to $\mathbf{Cat}_{\infty}$ satisfies the “Segal conditions” of Definition 3.1 and Definition 3.2. This immediately proves the result. $\square$

**Lemma 3.8.** *We have natural equivalences (in fact isomorphisms) of $\infty$-categories:*

$$\begin{array}{ccc} \mathbf{LMod}(F_K \mathcal{X}^*) & \simeq & \text{Fun}(K, \mathbf{LMod}(\mathcal{X})) \\ \downarrow & & \downarrow \\ \mathbf{Mon}(F_K \mathcal{M}^*) & \simeq & \text{Fun}(K, \mathbf{Mon}(\mathcal{M})) \end{array}$$

*compatible to the forgetful functor as represented in the diagram above.*

*Proof.* By construction of $F_K$, or rather by the second point of Proposition 2.7, the simplicial set of sections of $F_K \mathcal{X}^* \to N(\Delta^{op}) \times \Delta^1$ is equivalent to the simplicial set of maps $K \times N(\Delta^{op}) \times \Delta^1 \to \mathcal{X}^*$. This, in turn, is isomorphic to the simplicial set of maps from $K$ to the simplicial set of sections of $\mathcal{X}^* \to N(\Delta^{op}) \times \Delta^1$. The same can be said for $\mathcal{M}^* \to N(\Delta^{op})$, and these identification are compatible with the “forgetful functors”, i.e. the restriction along $N(\Delta^{op}) \times \{1\} \to N(\Delta^{op}) \times \Delta^1$.

The $\infty$-categories mentioned in the lemma are full subcategories of these simplicial sets. To conclude the proof we just need to show that they are preserved by these isomorphisms. The proofs for monoids and module objects are exactly the same. On the side of $\mathbf{LMod}(F_K \mathcal{X}^*)$ we are looking at the full subcategory of sections that send any inert arrow to a coCartesian lift. Though the series of isomorphisms mentioned at the beginning, these corresponds to the dotted section in

$$\begin{array}{ccc} & & \text{Fun}(K, \mathcal{X}^*) \\ & \downarrow & \\ N(\Delta^{op}) \times \Delta^1 & \longrightarrow & \text{Fun}(K, N(\Delta^{op}) \times \Delta^1) \end{array}$$

that sends inert edges to coCartesian edges. The coCartesian edges with respect to the coCartesian fibration $\text{Fun}(K, \mathcal{X}^*) \to \text{Fun}(K, N(\Delta^{op}) \times \Delta^1)$ are exactly the natural transformations that are coCartesian when evaluated at each object $k \in K$ (see [15, Proposition 3.1.2.1]). Thus, it follows that through the series of isomorphisms above, a section of $F_K \mathcal{X}^* \to N(\Delta^{op}) \times \Delta^1$

16