1:4

M. SHULMAN

Vol. 19:2

Secondly, we use the free $\mathbb{D}$-category on a sketch to show that any morphism of doctrines $\mathfrak{F}: \mathbb{D}_1 \to \mathbb{D}_2$ induces a pseudo 2-adjunction between $\mathbb{D}_1$-categories and $\mathbb{D}_2$-categories. That is, any $\mathbb{D}_2$-category $\mathcal{T}$ has an underlying $\mathbb{D}_1$-category $\mathfrak{F}^*\mathcal{T}$, and any $\mathbb{D}_1$-category $\mathcal{S}$ generates a free $\mathbb{D}_2$-category $\mathfrak{F}_*\mathcal{S}$. Thus, LNL doctrines also supply a uniform way to relate different sorts of monoidal category, potentially with exponential monads and comonads.

## 2. LNL POLYCATEGORIES

The different kinds of multicategories mentioned in Section 1, corresponding to logics with different structural rules, are all instances of a well-developed theory of “generalized multicategories” parametrized by a monad on a bicategory or double category of spans or profunctors.$^1$ This theory was used for instance in [HT21] to begin defining an analogue of LNL polycategories for intuitionistic linear logic (see our discussion of “LNL multicategories” below). LNL polycategories ought to be an instance of a similar theory of “generalized polycategories”, but unfortunately, no such general theory has been formulated yet (though [Gar08] provides strong evidence for its existence). Thus, in this paper we simply give the definitions explicitly.

**Definition 2.1.** A **linear-nonlinear (LNL) polycategory $\mathcal{P}$** consists of:

- (i) A set of **nonlinear objects**, which we denote by letters near the end of the Roman alphabet such as $X, Y, Z$. We denote finite lists of nonlinear objects by the Greek letters $\Theta, \Upsilon$. If $(X_1, \dots, X_m)$ is such a list and $\sigma: \{1, \dots, n\} \to \{1, \dots, m\}$ is a function, we write $\sigma: (X_1, \dots, X_m) \to (X_{\sigma 1}, \dots, X_{\sigma n})$ and call it a **structural map**.
- (ii) For each $\Theta, X$, a **nonlinear hom-set $\mathcal{P}(\Theta; X)$** containing **nonlinear morphisms**, with a functorial action by any structural map $\sigma: \Theta \to \Upsilon$:

$$(-)^\sigma: \mathcal{P}(\Upsilon; X) \to \mathcal{P}(\Theta; X).$$

- (iii) Compositions and identities for the nonlinear hom-sets

$$\circ_X: \mathcal{P}(\Theta_1, X, \Theta_2; Y) \times \mathcal{P}(\Upsilon; X) \to \mathcal{P}(\Theta_1, \Upsilon, \Theta_2; Y) \quad 1_X \in \mathcal{P}(X; X)$$

satisfying the multicategory axioms and equivariant for the structural actions.

- (iv) A set of **linear objects**, which we denote by letters near the beginning of the Roman alphabet such as $A, B, C$. We denote finite lists of linear objects by the Greek letters $\Gamma, \Delta$. If $(A_1, \dots, A_n)$ is such a list and $\tau: \{1, \dots, n\} \xrightarrow{\sim} \{1, \dots, n\}$ is a permutation, we write $\tau: (A_1, \dots, A_n) \xrightarrow{\sim} (A_{\sigma 1}, \dots, A_{\sigma n})$ and call it a **structural permutation**.
- (v) For each $\Theta$ and $\Gamma, \Delta$, a **linear hom-set $\mathcal{P}(\Theta \mid \Gamma; \Delta)$** containing **linear morphisms**, with a functorial action by a structural map $\sigma: \Theta' \to \Theta$ and structural permutations $\tau: \Gamma' \to \Gamma$ and $\rho: \Delta \to \Delta'$:

$$^\rho(-)^{\sigma|\tau}: \mathcal{P}(\Theta \mid \Gamma; \Delta) \to \mathcal{P}(\Theta' \mid \Gamma'; \Delta').$$

- (vi) For each $A$ an identity morphism $1_A \in \mathcal{P}(\mid A; A)$.

- (vii) Composition morphisms

$$\begin{aligned} \circ_A: \mathcal{P}(\Theta \mid \Gamma_1, A, \Gamma_2; \Delta) \times \mathcal{P}(\Theta' \mid \Gamma'; \Delta'_1, A, \Delta'_2) \\ \longrightarrow \mathcal{P}(\Theta, \Theta' \mid \Gamma_1, \Gamma', \Gamma_2; \Delta'_1, \Delta, \Delta'_2) \\ \circ_X: \mathcal{P}(\Theta_1, X, \Theta_2 \mid \Gamma; \Delta) \times \mathcal{P}(\Upsilon; X) \longrightarrow \mathcal{P}(\Theta_1, \Upsilon, \Theta_2 \mid \Gamma; \Delta) \end{aligned}$$

$^1$See [CS10] for a general framework, building on much prior work cited therein.