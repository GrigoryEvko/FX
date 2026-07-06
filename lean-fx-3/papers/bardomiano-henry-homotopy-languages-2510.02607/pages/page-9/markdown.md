Since we aim to do infinitary logic, we enhance Cartmell's notion of generalized algebraic theory to what we call *generalized $\kappa$-algebraic theory* for $\kappa$ a regular cardinal, which we develop in detail in section A. Nevertheless, this generalization is straightforward and a reader familiar with Cartmell's formalism should be able to guess how it works and read this section directly. The main difference to keep in mind is that our contexts are sequences of typed variables indexed by ordinals less than $\kappa$ instead of finite sequences. A consequence of this is that we need to use more heavily the "generalized display maps" that correspond to "projections" from a context $(x_i : X_i)_{i<\gamma}$ to $(x_i : X_i)_{i<\beta}$ for arbitrary $\beta < \gamma < \kappa$, where the classical theory uses the display maps that corresponds to projections that only forget the last variable.

In what follows, we fix $\kappa$, $\lambda$ two regular cardinals and $T$ a generalized $\kappa$-algebraic theory. We will define the first-order language of $T$ with $\lambda$-small conjunction and disjunction, denoted $\mathcal{L}_\lambda^T$ or $\mathcal{L}_{\lambda,\kappa}^T$.

More precisely, for each context $\Gamma$ of $T$, we will define a set $\mathcal{L}_\lambda^T(\Gamma)$ of "$T$-formulas in context $\Gamma$". Essentially, these are first-order formulas with $\lambda$-small conjunctions and disjunctions whose free variables are the variables of the context $\Gamma$, in particular, they have less than $\kappa$-variables.

**Definition 2.1.** The sets $\mathcal{L}_\lambda^T(\Gamma)$ of $T$-formulas in context $\Gamma$ are defined inductively using the following rules:

1. For each context $\Gamma$, the true formula $\top$ and false formula $\bot$ are in $\mathcal{L}_\lambda^T(\Gamma)$.
2. If $\Phi \in \mathcal{L}_\lambda^T(\Gamma)$ then $\neg\Phi \in \mathcal{L}_\lambda^T(\Gamma)$.
3. For each collection of formulas $\Phi_i \in \mathcal{L}_\lambda^T(\Gamma)$, indexed by a $\lambda$-small set $I$, the conjunction and disjunction

$$\bigvee_{i \in I} \Phi_i \qquad \bigwedge_{i \in I} \Phi_i$$

are in $\mathcal{L}_\lambda^T(\Gamma)$.

4. Given two ordinals $\gamma < \alpha < \kappa$: If $\Gamma' \equiv \{x_\beta : \Gamma_\beta\}_{\beta<\alpha}$ is a context of length $\alpha$, and $\Gamma \equiv \{x_\beta : \Gamma_\beta\}_{\beta<\gamma}$ is the subcontext of length $\gamma$, then for any formula $\Phi \in \mathcal{L}_\lambda^T(\Gamma')$ we have formulas

$$\exists\{x_\beta : \Gamma_\beta\}_{\gamma \leqslant \beta < \alpha} \Phi \qquad \forall\{x_\beta : \Gamma_\beta\}_{\gamma \leqslant \beta < \alpha} \Phi$$

in $\mathcal{L}_\lambda^T(\Gamma)$.

9