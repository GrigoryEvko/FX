That is there is a correspondence between natural transformation $X \circ R \rightarrow Y$ and $X \rightarrow Y \circ L$. Indeed, given a natural transformation $v: X \rightarrow Y \circ L$, one obtain a natural transformation

$$XR \xrightarrow{vR} YLR \xrightarrow{Y(\eta)} Y$$

where $\eta: LR \rightarrow Id$ is the counit of adjunction. The inverse construction is obtained from the counit and the unit-counit relation shows that these are inverses of each other.

We refer to section 2.4 of [15] for the general theory of Cartesian and coCartesian fibrations. The following construction allows us to describe how the coCartesian fibration classified by $F: \mathcal{C} \rightarrow \mathbf{Cat}_{\infty}$ relates to the coCartesian fibration classified by $\text{Fun}(K, F(-)): \mathcal{C} \rightarrow \mathbf{Cat}_{\infty}$ for a fixed $\infty$-category $K$:

**Definition 2.6.** Let $\mathcal{E} \rightarrow \mathcal{B}$ be a map of simplicial sets and $K$ any simplicial set. We denote by $F_K(\mathcal{E})$ the simplicial set obtained as the pullback:

$$\begin{array}{ccc} F_K(\mathcal{E}) & \longrightarrow & \mathcal{E}^K \\ \downarrow & \downarrow & \downarrow \\ \mathcal{B} & \longrightarrow & \mathcal{B}^K, \end{array}$$

where the bottom map is the diagonal map.

**Proposition 2.7.** 1. If $\mathcal{E} \rightarrow \mathcal{B}$ is a Cartesian or coCartesian fibration, then $F_K\mathcal{E} \rightarrow \mathcal{B}$ is as well.

2. The construction $\mathcal{E} \mapsto F_K\mathcal{E}$ is right adjoint to $\mathcal{E} \mapsto \mathcal{E} \times K$ in the $\infty$-categories of Cartesian fibrations over $\mathcal{B}$ and of coCartesian fibrations over $\mathcal{B}$.
3. If $\mathcal{E} \rightarrow \mathcal{B}$ is a coCartesian fibration, then the functor $\mathcal{B} \rightarrow \mathbf{Cat}_{\infty}$ classifying $F_K(\mathcal{E})$ is equivalent to the composite of the functor $\mathcal{B} \rightarrow \mathbf{Cat}_{\infty}$ classifying $\mathcal{E} \rightarrow \mathcal{B}$ with $\text{Fun}(\mathcal{K}, -): \mathbf{Cat}_{\infty} \rightarrow \mathbf{Cat}_{\infty}$.

*Proof.* The first point for Cartesian fibrations follows immediately from Proposition 3.1.2.1 of [15], which claims that $\mathcal{E}^K \rightarrow \mathcal{B}^K$ is a cartesian fibration when $\mathcal{E} \rightarrow \mathcal{B}$ is, and the fact that a pullback of a cartesian fibration is a cartesian

10