We now return to show the $4^{th}$ invariance theorem for the case in which the functor is a Barton trivial fibration. First, we observe that extensible functors always induce a surjection between the languages of clans.

**Lemma 4.15.** *Let $F : \mathcal{M} \to \mathcal{N}$ be an extensible morphism between $\kappa$-clans and $\Gamma \in \mathcal{M}$. Then, any formula $\Phi \in \mathbb{L}_{\lambda}^{\mathcal{N}}(F\Gamma)$ is the image under $F$ of a formula $\Phi_0 \in \mathbb{L}_{\lambda}^{\mathcal{M}}(\Gamma)$.*

*Proof.* Since every $\kappa$-clan is of the form $\mathbb{C}_T$ for some $T$ generalized $\kappa$-algebraic theory, it is enough to show the result is valid for the syntactic definition of language as in theorem 2.1. We prove by induction on formulas $\Phi \in \mathbb{L}_{\lambda}^{\mathcal{N}}(\Delta)$ that, given any context $\Gamma$ and $f : \Delta \cong F(\Gamma)$, there is a formula $\Phi_0 \in \mathbb{L}_{\lambda}^{\mathcal{M}}(\Gamma)$ such that $f^*(F\Phi_0) = \Phi$.

1. When $\Phi = \top$ or $\Phi = \bot$, then this can clearly be lifted to $\top$ and $\bot$.
2. If $\Phi = \neg\Psi$ or $\Phi = \bigvee_{i \in I} \Psi_i$ or $\Phi = \bigwedge_{i \in I} \Psi_i$ then it is also clear that $\Phi$ can be lifted. Indeed, we can simply use the inductive hypothesis to lift each $\Psi_i$ and then use the boolean algebra structure to conclude.
3. Suppose that $\Phi$ is of the form $\exists_{\pi}\Psi$ or $\forall_{\pi}\Psi$ for some fibration $\pi : \Gamma' \twoheadrightarrow F(\Gamma)$. The formula $\Psi \in \mathbb{L}_{\lambda}^{\mathcal{N}}(\Gamma')$, so $\Phi \in \mathbb{L}_{\lambda}^{\mathcal{N}}(F\Gamma)$. Furthermore, we assume that $\Psi$ can be lifted. Since $F$ is extensible, there is a lift $\bar{\pi} : \bar{\Gamma}' \to \Gamma \in \mathcal{M}$ of $\pi : \Gamma' \twoheadrightarrow F(\Gamma)$, which comes with an isomorphism $g : \Gamma' \cong F(\bar{\Gamma}')$ such that the following triangle commutes

$$\begin{array}{c} \Gamma' \xrightarrow{\pi} F(\Gamma) \\ \cong \Biggl\downarrow g \quad \nearrow \\ F(\bar{\Gamma}'). \end{array}$$

Therefore, we get a commutative square as in the left below, and at the level of languages as on the right below

$$\begin{array}{ccc} \Gamma' \xrightarrow{\pi'} \Delta & & \mathbb{L}_{\lambda}^{\mathcal{N}}(F(\bar{\Gamma}')) \xrightarrow{\exists_{\pi'}} \mathbb{L}_{\lambda}^{\mathcal{N}}(F(\Gamma)) \\ \cong \Biggl\downarrow g \quad f \Biggl\downarrow \cong & & g^* \Biggl\downarrow \quad \Biggl\downarrow f^* \\ F(\bar{\Gamma}') \xrightarrow[F(\bar{\pi})]{} F(\Gamma) & & \mathbb{L}_{\lambda}^{\mathcal{N}}(\Gamma') \xrightarrow{\exists_{F(\bar{\pi})}} \mathbb{L}_{\lambda}^{\mathcal{N}}(\Delta). \end{array}$$

By assumption $\psi \in \mathbb{L}_{\lambda}^{\mathcal{N}}(\Gamma')$ can be lifted. Hence, there is a formula $\Psi_0 \in \mathbb{L}_{\lambda}^{\mathcal{M}}(\bar{\Gamma}')$ such that $g^*(F\Psi_0) = \Psi$. Using the right hand square above, one can see that $\exists_{\bar{\pi}}\Psi_0$ is a lift for $\Phi$.

66