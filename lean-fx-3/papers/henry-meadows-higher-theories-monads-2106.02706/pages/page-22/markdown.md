**Proposition 3.19.** *If $U : \mathcal{D} \to \mathcal{C}$ is a functor with a left adjoint $F$, then $U \circ F : \mathcal{C} \to \mathcal{C}$ endowed with the map $U \circ F \circ U \to U$ given by applying $U$ to the unit of adjunction is an endomorphisms monad for $U$.*

We can construct a functor $\mathbf{Mnd}_{\mathcal{C}}^{op} \to \mathbf{Cat}_{\infty}$ that sends $T$ to $\mathcal{C}^T$ by applying straightening to the Cartesian fibration $\mathbf{LMod}(\mathrm{End}(\mathcal{C})) \to \mathbf{Mon}(\mathrm{End}(\mathcal{C}))$ associated to the action in Construction 3.11.

**Proposition 3.20.** *The functor*

$$\begin{array}{ccc} (\mathbf{Mnd}_{\mathcal{C}})^{op} & \to & (\mathbf{Cat}_{\infty})_{/\mathcal{C}} \\ T & \mapsto & \mathcal{C}^T \end{array}$$

*Corestricted to the full subcategory of right adjoint functors admit a left adjoint that sends a right adjoint functor $U : \mathcal{D} \to \mathcal{C}$ to its endomorphism monad.*

*Proof.* To show the existence of the adjoint, it suffices to show that the functor $T \mapsto \mathrm{Map}_{(\mathbf{Cat}_{\infty})_{/\mathcal{C}}}(\mathcal{D}, \mathcal{C}^T)$ is representable by $\underline{\mathrm{End}}(U)$. By applying 3.15 to the action of $\mathrm{End}(\mathcal{C})$ on $(\mathbf{Cat}_{\infty})_{/\mathcal{C}}$ given by 3.11, and applying 3.12, we get equivalences (natural in $T$)

$$\mathrm{Map}_{\mathbf{Mnd}_{\mathcal{C}}}(T, \underline{\mathrm{End}}(U)) \simeq \mathrm{Map}_{\mathbf{Cat}_{\infty}}^{U}(\mathcal{D}, \mathcal{C})^T \simeq \mathrm{Map}_{\mathbf{Cat}_{\infty}}^{U}(\mathcal{D}, \mathcal{C}^T)$$

where $\mathrm{Map}_{\mathbf{Cat}_{\infty}}^{U}(\mathcal{D}, \mathcal{C})^T$ and $\mathrm{Map}_{\mathbf{Cat}_{\infty}}^{U}(\mathcal{D}, \mathcal{C}^T)$ are the (homotopy) fibers of $\mathrm{Map}_{\mathbf{Cat}_{\infty}}(\mathcal{D}, \mathcal{C})^T$ and $\mathrm{Map}_{\mathbf{Cat}_{\infty}}(\mathcal{D}, \mathcal{C}^T)$ over $U \in \mathrm{Map}_{\mathbf{Cat}_{\infty}}(\mathcal{D}, \mathcal{C})$. By the description of mapping spaces in a slice $\infty$-category from [15, Proposition 5.5.5.12], one has an equivalence $\mathrm{Map}_{\mathbf{Cat}_{\infty}}^{U}(\mathcal{D}, \mathcal{C}^T) \simeq \mathrm{Map}_{(\mathbf{Cat}_{\infty})_{/\mathcal{C}}}(\mathcal{D}, \mathcal{C}^T)$, which in total gives an equivalence natural in $T$:

$$\mathrm{Map}_{\mathbf{Mnd}_{\mathcal{C}}}(T, \underline{\mathrm{End}}(U)) \simeq \mathrm{Map}_{(\mathbf{Cat}_{\infty})_{/\mathcal{C}}}(\mathcal{D}, \mathcal{C}^T)$$

$\square$

**Lemma 3.21.** *Let $U : \mathcal{D} \to \mathcal{C}$ be a functor of $\infty$-categories. The unit of the adjunction of Proposition 3.20 can be identified with the canonical map $\mathcal{D} \to \mathcal{C}^{\underline{\mathrm{End}}(U)}$ determined by the action of $\underline{\mathrm{End}}(U)$ on $U$, through the equivalence $\mathrm{Fun}(\mathcal{D}, \mathcal{C}^{\underline{\mathrm{End}}(U)}) \simeq \mathrm{Fun}(\mathcal{D}, \mathcal{C})^{\underline{\mathrm{End}}(U)}$ of Lemma 3.12.*

22