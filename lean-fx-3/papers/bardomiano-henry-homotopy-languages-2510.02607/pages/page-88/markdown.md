**Theorem 4.52.** Given $F : \mathcal{M} \rightleftarrows \mathcal{N}$ be a left Quillen equivalence between weak model categories. Then, we have a diagram of weak model categories

$$\begin{array}{c} \mathcal{M}^J \xrightarrow{H} \mathcal{N}_F^I \\ B \Big\downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \mathcal{M}_{\overline{(Id_{\mathcal{M}},F)}} \xrightarrow{\mathcal{M}} \mathcal{N}, \end{array}$$

where $\pi_1$ and $\pi_2$ are Barton trivial fibrations.

*Proof.* The work we have done produces a diagram as on the left below, and the action of the functors on objects is spelled out on the right:

$$\begin{array}{ccc} \mathcal{M}^J & \xrightarrow{H} & \mathcal{N}_F^I \\ B \Big\downarrow & & \Big\downarrow_{(\pi_1,\pi_2)} \\ \mathcal{M}_{\overline{(Id_{\mathcal{M}},F)}} \xrightarrow{\mathcal{M}} \mathcal{N} & & X_a \Rightarrow X_b \rightarrow X_c \xmapsto{H} FX_a \Rightarrow FX_b \\ & & B \Big\downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ & & & X_a \longmapsto (X_a, FX_a) \end{array}$$

We have shown in theorem 4.47 and theorem 4.51 that both projections are Barton trivial fibrations. $\square$

It will be essential to highlight that there is a diagonal functor which is a Barton trivial fibration, making the lower triangle commutative.

**Corollary 4.53.** Let $F : \mathcal{M} \rightarrow \mathcal{M}$ be a left Quillen equivalence. There exists a Barton trivial fibration $P : \mathcal{N}_F^I \rightarrow \mathcal{M}$.

*Proof.* Theorem 4.52 can be further specialized to a diagram

$$\begin{array}{ccc} \mathcal{M}^J & \longrightarrow & \mathcal{N}_F^I \\ \Big\downarrow & & \Big\downarrow^{\pi_1} \\ \mathcal{M}_{\overline{(Id_{\mathcal{M}})}} \xrightarrow{\mathcal{M}} \mathcal{M} \end{array}$$

from which we see that there is a functor $P : \mathcal{N}_F^I \rightarrow \mathcal{M}$. This is an immediate consequence of theorem 4.52. $\square$

#### 4.4 Proof of main theorem

**Theorem 4.54.** Let $F : \mathcal{M} \rightleftarrows \mathcal{N} : G$ a Quillen equivalence. Then, for any cofibrant object $A \in \mathcal{M}$. The induced map $h \mathbb{L} F_A : h \mathbb{L}_\lambda^{\mathcal{M}}(A) \rightarrow h \mathbb{L}_\lambda^{\mathcal{N}}(FA)$ is an isomorphism.

88