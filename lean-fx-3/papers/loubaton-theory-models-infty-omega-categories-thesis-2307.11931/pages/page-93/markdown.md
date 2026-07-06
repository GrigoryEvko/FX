2.2. THE COMPLICIAL MODEL

are colimit preserving. Furthermore, for every acyclic cofibration $K \to L$, the morphism $K \stackrel{co}{\star} X \to L \stackrel{co}{\star} X$ is the horizontal colimit of the diagram:

$$\begin{array}{c} K \amalg X \longleftarrow X \otimes \partial[1] \otimes K \longrightarrow X \otimes [1] \otimes K \\ \downarrow \qquad \qquad \qquad \downarrow \qquad \qquad \qquad \downarrow \\ L \amalg X \longleftarrow X \otimes \partial[1] \otimes L \longrightarrow X \otimes [1] \otimes K \end{array}$$

However, these two horizontal colimits are homotopy colimits, and all the horizontal maps of the previous diagram are weak equivalences. This morphism is then an acyclic cofibration. This shows that $\_ \stackrel{co}{\star} X$ is a left Quillen functor. We show analogously that $X \stackrel{co}{\star} \_ \_ \_$ is a left Quillen functor.

**2.2.2.19.** Let $X$ be a simplicial set. We define the *wedge* of $\Sigma X$ and $[1]$, noted by $\Sigma X \vee [1]$, as the colimit of the following diagram:

$$\begin{array}{c} X \otimes [0, 1] \longrightarrow X \otimes [2]_t \longleftarrow X \otimes [1, 2] \\ \downarrow \qquad \qquad \qquad \downarrow \qquad \qquad \qquad \downarrow \\ \Sigma X \longrightarrow X \vee [1] \longleftarrow [1, 2] \end{array}$$

This assignation defines a cocontinuous functor $\_ \vee [1] : \mathrm{mPsh}(\Delta) \to \mathrm{mPsh}(\Delta)_{[0]\amalg[1]/}$. For every acyclic cofibration $K \to L$, the morphism $K \vee [1] \to L \vee [1]$ is the horizontal colimit of the diagram:

$$\begin{array}{c} [0] \coprod[1] \longleftarrow K \otimes ([0] \coprod[1, 2]) \longrightarrow K \otimes [2]_t \\ \downarrow \qquad \qquad \qquad \downarrow \qquad \qquad \qquad \downarrow \\ K \otimes [2]_t \longleftarrow L \otimes [2]_t \longrightarrow L \otimes [2]_t \end{array}$$

However, these two horizontal colimits are homotopy colimits, and all the horizontal maps of the previous diagram are weak equivalences. This morphism is then an acyclic cofibration. This shows that this functor is a left Quillen functor. We denote by

$$\nabla : \Sigma X \to \Sigma X \vee [1]$$

the morphism induced by the inclusion $X \otimes [0, 2] \subset X \otimes [2]_t$ and

$$\Sigma X \hookrightarrow \Sigma X \vee [1]$$

the morphism induced by the inclusion $X \otimes [1, 2] \subset X \otimes [2]_t$. We define similarly the left Quillen functor

$$[1] \vee \_ : \mathrm{mPsh}(\Delta) \to \mathrm{mPsh}(\Delta)_{[1]\amalg[0]/}$$

and the morphisms

$$\nabla : \Sigma X \to [1] \vee \Sigma X \quad \text{and} \quad \Sigma X \hookrightarrow [1] \vee \Sigma X.$$

83