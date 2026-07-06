**Notation 2.2.2.** For ordinals $\alpha, \beta$, we write $\alpha < \beta$ to mean $\alpha \in \beta$. We write $\alpha \preceq \beta$ to mean that either $\alpha < \beta$ or $\alpha = \beta$. An $\alpha$-chain is a diagram indexed by the poset $(\alpha, \preceq)$.

We say $\alpha$ is a *limit* ordinal when for every family $(\beta_i < \alpha)_{i \in I}$ indexed by an finite inhabited set $I$ we have some $\beta < \alpha$ with $\beta_i < \beta$ for all $i$ (*cf.* Pitts and Steenkamp [PS22, Definition 3.2]). Classically, this agrees with the usual definition.

For a well-pointed endofunctor $\mathsf{S}$, the forgetful functor $U_{\mathsf{S}}: \mathsf{S}$-Alg $\to \mathcal{E}$ is a fully faithful inclusion: $\mathsf{S}$-Alg consists of those $A \in \mathcal{E}$ for which $\sigma_A$ is invertible, in which case the algebra map is $\sigma_A^{-1}: SA \to A$ [Wol78, Proposition 1.5 and Corollary 1.6]. We want to construct the left adjoint to $U_{\mathsf{S}}$ as the colimit in the category of pointed endofunctors on $\mathcal{E}$ of the $\kappa$-chain

$$\text{\text}a\text{\textId}_\mathcal{E} \xrightarrow{\sigma} S \xrightarrow{\sigma S} S^2 \xrightarrow{\sigma S^2} \dots \text{\texttexttextir}}. \quad (2.1)$$

To define the diagram (2.1) in a constructively acceptable way, we cannot distinguish between successor and limit ordinal cases. We adapt a construction for non-pointed endofunctors due to Pitts and Steenkamp [PS22]. Benno van den Berg explained a similar argument for pointed endofunctors to us in personal communication, and we follow him in using Koubek and Reiterman's language of *algebraized* (or *algebraic*) chains [KR79]. Koubek and Reiterman use algebraized chains to obtain free algebras for non-pointed endofunctors, and Bourke [Bou19, §A] describes an analogue for pointed endofunctors; both distinguish between limit and successor cases, so are not wholly constructive.

**Definition 2.2.3.** Given a pointed endofunctor $\mathsf{T} = (T, \tau)$ on a category $\mathcal{E}$ and an ordinal $\kappa$, we define the *category* $\mathsf{T}$-AlgChain$_\kappa$ *of* $\mathsf{T}$-*algebraized* $\kappa$-*chains* in $\mathcal{E}$ as follows:

(i) An object $(X, x)$ is a $\kappa$-chain $X: (\kappa, \preceq) \to \mathcal{E}$ together with morphisms $x_{\beta < \alpha}: TX_\beta \to X_\alpha$ for each $\beta < \alpha < \kappa$, such that

- (a) for all $\beta < \alpha < \kappa$ we have $x_{\beta < \alpha}\tau_\beta = X_{\beta \preceq \alpha}$;
- (b) for all $\alpha, \alpha', \beta, \beta' < \kappa$ standing in the relations

$$\begin{array}{ccc} \beta & \preceq & \beta' \\ \wedge & & \wedge \\ \alpha & \preceq & \alpha', \end{array}$$

the square

$$\begin{array}{ccc} TX_\beta & \xrightarrow{TX_{\beta \preceq \beta'}} & TX_{\beta'} \\ x_{\beta < \alpha} \downarrow & & \downarrow x_{\beta' < \alpha'} \\ X_\alpha & \xrightarrow{X_{\alpha \preceq \alpha'}} & X_{\alpha'} \end{array}$$

commutes.

(ii) A morphism $\varphi: (X, x) \to (Y, y)$ is a natural transformation $\varphi: X \to Y$ with the property that $y_{\beta < \alpha} \circ T\varphi_\beta = \varphi_\alpha \circ x_{\beta < \alpha}$ for $\beta < \alpha < \kappa$.

**Definition 2.2.4.** A $\mathsf{T}$-algebraized $\kappa$-chain $(X, x)$ is *colimiting* when for every $\beta < \kappa$ the cocone $(x_{\gamma < \beta}: TX_\gamma \to X_\beta)_{\gamma < \beta}$ under the restricted diagram $X \upharpoonright \beta: (\beta, \preceq) \to \mathcal{E}$ is colimiting.

We now define the category of configurations for the free monad construction.

**Definition 2.2.5.** Let $\mathcal{M}$ be a wide subcategory of a category $\mathcal{E}$. For a given diagram shape $\mathcal{J}$, we say that $\mathcal{M}$ has $\mathcal{J}$-*indexed colimits in* $\mathcal{E}$ when $\mathcal{M}$ (as a category) has these colimits and the inclusion into $\mathcal{E}$ preserves them.

11