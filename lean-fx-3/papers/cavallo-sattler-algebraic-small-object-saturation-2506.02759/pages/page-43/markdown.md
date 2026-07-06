$\alpha$ such that $A_\alpha$ contains $\mathbb{I}$ must be a successor ordinal $\alpha = \beta + 1$, and so we have a pushout square

$$\begin{array}{c} \coprod_{i \in I} C_i \xrightarrow{[c_i]_{i \in I}} A_\beta \\ \coprod_{i \in I} f_i \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \\ \coprod_{i \in I} D_i \xrightarrow{[d_i]_{i \in I}} W_\lambda \end{array}$$

where the maps $f_i$ belong to $S$. There must be exactly one $i \in I$ such that the image of $d_i$ contains the image of $q: \coprod_\lambda(\mathbb{I} \times \mathbb{I}) \to W_\lambda$, in which case we have a lower bound $\#\mathrm{PSh}(\square_{\mathrm{DM}})(\mathbb{I}^2, D_i) \geq \lambda$ on the number of 2-cubes in $D_i$. But while $\lambda$ was arbitrary, the set $\{\#\mathrm{PSh}(\square_{\mathrm{DM}})(\mathbb{I}^2, D) \mid (f: C \to D) \in S\}$ is bounded by some fixed cardinal; thus we have a contradiction.

In Theorem 4.1.17 below we shall construct the uniform fibration AWFS on any finitary configuration. We first need to establish the existence of the density comonad for $\mathsf{box}_I^t$.

**Notation 4.1.8.** The functor $\phi^t$ of Definition 4.1.2 decomposes as a sequence of left adjoints:

$$\mathcal{E}/\mathbb{F} \xrightarrow{\mathrm{id}_{(-)}/\mathbb{F}} \mathcal{E}^\neg/\mathrm{id}_{\mathbb{F}} \xrightarrow{(t, \mathrm{id}_{\mathbb{F}})^*} \mathcal{E}^\neg/t \xrightarrow{\sum_t} \mathcal{E}^\neg.$$

We write $\nu^t: \mathcal{E}^\neg \to \mathcal{E}/\mathbb{F}$ for its right adjoint, which is thus given by the composite

$$\mathcal{E}^\neg \xrightarrow{(-) \times t} \mathcal{E}^\neg/t \xrightarrow{(t, \mathrm{id}_{\mathbb{F}})_*} \mathcal{E}^\neg/\mathrm{id}_{\mathbb{F}} \xrightarrow{\mathrm{dom}/\mathrm{id}_{\mathbb{F}}} \mathcal{E}/\mathbb{F}.$$

**Lemma 4.1.9.** Let $F: \mathcal{C} \xleftrightarrow{\mathcal{D}}: G$ and let $u: \mathcal{J} \to \mathcal{C}$ be a diagram whose density comonad $D_u$ is defined. Then $F D_u G$ is the density comonad of $Fu$.

*Proof.* We have $\mathrm{Lan}_{Fu}(Fu) \cong F(\mathrm{Lan}_{Fu} u)$ because left adjoints preserve left Kan extensions [Mac98, Theorem X.5.1], and $\mathrm{Lan}_{Fu} u \cong (\mathrm{Lan}_u u)G$ by the isomorphism of comma categories $Fu \downarrow D \cong u \downarrow GD$ natural in $D \in \mathcal{D}$. $\square$

**Corollary 4.1.10.** For any $t: 1 \mapsto \mathbb{F}$ in $\mathcal{E} = \mathrm{PSh}(\mathcal{C})$, the density comonad of $u^t$ is $\phi^t \nu^t: \mathcal{E}^\neg \to \mathcal{E}^\neg$.

*Proof.* The Yoneda embedding $\mathcal{X}: \int_{\mathcal{C}} \mathbb{F} \to \mathcal{E}/\mathbb{F}$ is a dense functor, so its density comonad is the identity [Mac98, Proposition 1 and Corollary 3]. Since $u^t = \phi^t \mathcal{X}$ by definition, it follows from Lemma 4.1.9 that $\phi^t D_{\mathcal{X}} \nu^t$ is the density comonad of $u^t$. $\square$

**Lemma 4.1.11.** Let $S$ be a set and $u_i: \mathcal{J}_i \to \mathcal{C}$ for $i \in S$ be a family of diagrams in a cocomplete category $\mathcal{E}$. If $u: \coprod_{i \in S} \mathcal{J} \to \mathcal{C}$ is the induced map from the coproduct, then the density comonad of $u$ is the functor $C \mapsto \coprod_{i \in S} D_{u_i} C$.

*Proof.* The density comonad $D_u$ is computed at $C \in \mathcal{C}$ by the colimit

$$\begin{aligned} D_u(C) &\cong \mathrm{colim}\left(u \downarrow C \xrightarrow{\pi} \coprod_{i \in S} \mathcal{J}_i \xrightarrow{u} \mathcal{E}\right) \\ &\cong \coprod_{i \in S} \mathrm{colim}\left(u_i \downarrow C \xrightarrow{\pi} \mathcal{J} \xrightarrow{u_i} \mathcal{E}\right) \\ &\cong \coprod_{i \in S} D_{u_i}(C). \end{aligned}$$

**Corollary 4.1.12.** For a uniform fibration configuration $(t, I)$ on a presheaf category $\mathcal{E}$, the density comonad associated to $\mathsf{box}_I^t: \mathcal{E}^\neg \to \mathcal{E}^\neg$ is given by $D_{\mathsf{box}_I^t} f \cong \delta^0 D_{u^t}(\tilde{\partial}_0(f)) \sqcup \delta^1 D_{u^t}(\tilde{\partial}_1(f))$.

*Proof.* By Lemmas 4.1.9 and 4.1.11 and Corollary 4.1.10. $\square$

We also need to know that $D_{\mathsf{box}_I^t}$ interacts well with levelwise complemented monomorphisms.

43