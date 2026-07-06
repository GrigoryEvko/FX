Morphisms of $\lambda$-boolean algebras over $\mathcal{C}$ are natural transformations that commute with the $\exists_\pi$. We call weak morphisms the natural transformations with no additional conditions.

*Remark 2.21.* If $\mathcal{B}$ is a $\lambda$-boolean algebra over $\mathcal{C}$, then for each $X \in \mathcal{C}$, the negation $\neg : \mathcal{B}(X) \rightarrow \mathcal{B}(X)^{op}$ is a contravariant equivalence. Therefore, if $\pi : Z \rightarrow X$ is a fibration, then the map $\pi^* : \mathcal{B}(X) \rightarrow \mathcal{B}(Z)$ also has a right adjoint defined by:

$$\forall_\pi(\phi) := \neg(\exists_\pi \neg \phi).$$

From this definition, we immediately have the other Beck-Chevalley condition $f^*(\forall_\pi) = \forall_\pi f^*$ and the fact that morphisms of boolean algebras over $\mathcal{C}$ are also compatible with $\forall_\pi$, simply because $f^*$ is compatible with both $\exists_\pi$ and the negation.

*Remark 2.22.* Theorem 2.20 will in practice be applied to $\mathcal{C}$ a $\kappa$-clan (and not just a clan). The only reason it is stated like that is because the definition actually does not explicitly involve $\kappa$. This is related to the fact that the dependencies in $\kappa$ of the language defined in the previous subsection are only through the choice of which context can our variables (including bound variables) be taken from: taking a larger $\kappa$ means we can quantify over more variables at the same time. Similarly, the dependency on $\kappa$ is hidden in the dependency on $\mathcal{C}$, as $\mathcal{C}$ is playing the role of the category of $\kappa$-contexts.

Let us start with our main example of such a boolean algebra over a clan, which is the motivating example for the notion:

**Theorem 2.23.** *Let $T$ be a generalized $\kappa$-algebraic theory and $\mathcal{C}_T$ the corresponding $\kappa$-contextual category, seen as a clan. Then the construction $X \mapsto \mathbb{L}_\lambda^T(X)$ from theorem 2.10 (see also theorem 2.1 and 2.6) is a $\lambda$-boolean algebra over $\mathcal{C}_T$. In fact, it is an initial object in the category of $\lambda$-boolean algebras over $\mathcal{C}_T$.*

*Proof.* We first check that $\mathcal{L}_\lambda^T$ is a $\lambda$-boolean algebra over $\mathcal{C}_T$. We have mentioned in theorem 2.11 that all the logical operations $\vee, \wedge, \neg, \exists$ and so on are compatible with the equivalence relation $\dashv$. Therefore, they all induce operations on the quotient $\mathbb{L}_\lambda^T$. The first four points of theorem 2.6 immediately show that each $\mathbb{L}_\lambda^T(X)$ is a boolean algebra whose order relation is given by $\vdash$, and with $\lambda$-small unions. By theorem 2.5, the map $f^* : \mathcal{L}_\lambda^T(X) \rightarrow \mathcal{L}_\lambda^T(Y)$ is compatible with all the logical operations, so it gives rise to a morphism of boolean algebras $\mathbb{L}_\lambda^T(X) \rightarrow \mathbb{L}_\lambda^T(Y)$. We get a functor $\mathcal{C}_T \rightarrow \mathbf{Bool}_\lambda$, the conditions $(g \circ f)^*(\phi) = f^*g^*(\phi)$ and $id^*(\phi) = \phi$ follow immediately by induction. Next, the last two conditions of theorem 2.6

19