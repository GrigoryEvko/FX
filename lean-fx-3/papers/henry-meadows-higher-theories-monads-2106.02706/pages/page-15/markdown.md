**Definition 3.6.** • If $\mathcal{C}^* \to N(\Delta^{op})$ is a monoidal $\infty$-category, a *monoid object* in $\mathcal{C}$ is a section of this map that send inert edges to inert edges. The $\infty$-category $\mathbf{Mon}(\mathcal{C})$ is defined as the full subcategory of the $\infty$-category of sections on monoid objects.

• If $\mathcal{X}^* \to N(\Delta^{op}) \times \Delta^1$ is a monoidal action, a *module object* in $\mathcal{X}$ is a section of this map that sends inert edges to inert edges. The $\infty$-category $\mathbf{LMod}(\mathcal{X})$ is defined as the full subcategory of the $\infty$-category of sections on module objects.

Obviously, the notion of monoid in $\mathcal{C}$ depends on the whole monoidal structure $\mathcal{C}^* \to N(\Delta^{op})$ and not just on the underlying $\infty$-category $\mathcal{C}$, and the notation $\mathbf{Mon}(\mathcal{C})$ is an abuse. The same applies to module objects.

Here again, the monoidal action $\mathcal{X}^* \to N(\Delta^{op}) \times \Delta^1$ is a pair of a monoidal $\infty$-category $\mathcal{M}$ that acts on an $\infty$-category $\mathcal{X}$. The category $\mathbf{LMod}(\mathcal{X})$ is a category of pairs of a monoid object $M$ in $\mathcal{M}$, together with an object $X$ of $\mathcal{X}$ and an action of $M$ on $X$.

We sometime write $\mathbf{LMod}(\mathcal{X}, \mathcal{M})$ when we want to emphasize the monoidal part of the action $\mathcal{X}^* \to N(\Delta^{op}) \times \Delta^1$.

Similar to the case of $\infty$-categories with finite limits, if $\mathcal{X}$ is an $\infty$-category with an action of a monoidal $\infty$-category $\mathcal{M}$, then there is a forgetful functor $\mathbf{LMod}(\mathcal{X}) \to \mathbf{Mon}(\mathcal{M})$ and Lurie showed that this is a cartesian fibration. If $A$ is a monoid object in $\mathcal{M}$ we denote by $\mathbf{LMod}^A(\mathcal{X})$ the fibre over $A$ of this fibration. We call it the category of $A$-modules in $\mathcal{X}$. The full subcategory whose objects are actions of $A$ on $B \in \mathcal{X}$ is denoted by $\mathbf{LMod}_B^A(\mathcal{X})$.

Before moving further, we quickly look at how these notions interact with the functions $F_K$ of Definition 2.6. Let $\mathcal{M}^* \to N(\Delta^{op})$ be a monoidal $\infty$-category and $\mathcal{X}^* \to N(\Delta^{op}) \times \Delta^1$ a monoidal action of $\mathcal{M}$ on an $\infty$-category $\mathcal{X}$. For $K$ an $\infty$-category, we can apply the construction $F_K$ of Definition 2.6 to these functors to get new functors $F_K\mathcal{M}^* \to N(\Delta^{op})$ and $F_K\mathcal{X}^* \to N(\Delta^{op}) \times \Delta^1$. We have:

**Lemma 3.7.** $F_K\mathcal{M}^* \to N(\Delta^{op})$ and $F_K\mathcal{X}^* \to N(\Delta^{op}) \times \Delta^1$ are a monoidal $\infty$-category and a monoidal action. They correspond, respectively, to a monoidal structure on $\operatorname{Fun}(K, \mathcal{M})$ and a monoidal action of $\operatorname{Fun}(K, \mathcal{M})$ on $\operatorname{Fun}(K, \mathcal{X})$.

*Proof.* By Proposition 2.7 these are coCartesian fibration classified by the postcomposition of the functor classifying $\mathcal{M}^*$ and $\mathcal{X}^*$ with $\operatorname{Fun}(K, -)$. As

15