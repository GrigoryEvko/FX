$\widetilde{I}(s_\gamma)$ for all $0 < \gamma \leq \mu$. This exactly establishes $\langle \widetilde{I}(s_\beta) \rangle_{\beta < \mu} \approx \langle \widetilde{I}(t_\beta) \rangle_{\beta < \mu}$.

We have seen that the definition of $\mathbb{C}(I)$ give us the correct objects and morphisms. Now we show that it is indeed a contextual functor.

**Lemma B.13.** *Let $I : T \rightarrow T'$ be a morphism in $\kappa$-GAT. Then the map $\mathbb{C}(I) : \mathbb{C}_T \rightarrow \mathbb{C}_{T'}$ is a contextual functor.*

*Proof.* The map is a functor trivially. That it preserves the grading and restricts to a functor between the display subcategories $Dis(\mathbb{C}_T)$ and $Dis(\mathbb{C}_{T'})$ is also immediate. To prove it preserves canonical pullbacks, consider the following pullback square in the category $\mathbb{C}_T$:

$$\begin{array}{ccc} [\{x_\alpha : \Delta_\alpha, x_\gamma : \Omega_\gamma [t_\beta \mid x_\beta]_{\beta < \mu}\} \xrightarrow[\mu \leq \gamma < \mu + \varepsilon]{\{(t_\beta, x_\gamma) \quad \beta < \mu, \quad \}} & [\{x_\beta : \Omega_\beta\}_{\beta < \mu + \varepsilon}] \\ [\{x_\alpha\}_{\alpha < \kappa}] \downarrow & & \downarrow [\{x_\beta\}_{\beta < \mu}] \\ [\{x_\alpha : \Delta_\alpha\}_{\alpha < \kappa}] & \xrightarrow{[\{t_\beta\}_{\beta < \mu}]} & [\{x_\beta : \Omega_\beta\}_{\beta < \mu}] \end{array}$$

Then a straightforward computation, using the definition of $\mathbb{C}(I)$, shows that this is sent to a pullback square in the category $\mathbb{C}_{T'}$.

**Corollary B.14.** *There is a functor $\mathbb{C} : \kappa\text{-GAT} \rightarrow \kappa\text{-CON}$.*

### B.3.2 The functor $U : \kappa\text{-CON} \rightarrow \kappa\text{-GAT}$

We now turn to construct a functor that associates a generalized $\kappa$-algebraic theory $U(\mathcal{C})$ to each $\kappa$-contextual category $\mathcal{C}$. This is part of [Car78, Section 2.4]. We will use the notation introduced in theorem B.4. This means we identify each object by its height, say $B_\lambda$, and write display maps as $p_\alpha : B_\lambda \rightarrow B_\alpha$ if $\lambda > 0$ and $\alpha < \lambda$. If $\alpha = 0$ then $B_0 = 1$ the terminal object. A morphism $f : A_\lambda \rightarrow B_\mu$ is trivial when $B_\mu$ is trivial, *i.e.*, $\mu = 0$.

**Definition B.15.** We define $U(\mathcal{C}) \in \kappa\text{-GAT}$ as:

1. For each non-trivial object $B_\mu$ with $\mu = \lambda + 1$, there is a type symbol $\overline{B_\mu}$ with the introductory rule: $\{x_\beta : \overline{B_\beta}\}_{\beta < \mu} \vdash \overline{B_\mu}(x_\beta)_{\beta < \mu}$ Type. The notation emphasizes the fact that $\overline{B_\mu}$ depends on the indicated variables.
2. If $f : A_\lambda \rightarrow B_\mu$ is morphism of $\mathcal{C}$ with $\mu = \nu + 1$, we get an operator symbol $\overline{f}$. It has the introductory rule:

118