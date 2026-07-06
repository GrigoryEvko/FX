**Definition 3.2.** A module object in an $\infty$-category $\mathcal{C}$ with finite products, is a functor $X : N(\Delta^{op}) \times \Delta^1 \to \mathcal{C}$ such that:

- The restriction of $X$ to $N(\Delta^{op}) \times \{1\} \simeq N(\Delta^{op})$ is a monoid object in the sense of Definition 3.1.
- The maps $X([n], 0) \to X([n], 1) \times X([0], 0)$ induced by the maps $[0] \simeq \{n\} \subset [n]$ and obvious map $(0, [n]) \to (1, [n])$ are equivalences.

The $\infty$-category $\mathbf{LMod}(\mathcal{C})$ of modules is the full subcategory of functors $\mathcal{C}^{N(\Delta^{op}) \times \Delta^1}$ on module objects.

The category $\mathbf{LMod}(\mathcal{C})$ should be thought of as a category of pairs of a monoid $M$ with an $M$-module $X$. The module $M$ is the restriction of $X$ to $N(\Delta^{op}) \times \{1\}$ which is a monoid by the first assumption. The “underlying” object $X$ is obtained as $X = X(0, [0])$, and the action map $M \times X \to X$ is induced by $X([1], 0) \simeq X([1], 1) \times X([0], 0) = M \times X \to X([0], 0)$ induced by the unique edge $[0] \to [1]$ in $N(\Delta)$.

This intuition that $\mathbf{LMod}(\mathcal{C})$ is a “category of pairs” is made formal by the following:

**Proposition 3.3.** *The forgetful functor from $\mathbf{LMod}(\mathcal{C}) \to \mathbf{Mon}(\mathcal{C})$ that restricts to $N(\Delta^{op}) \times \{1\}$ is a Cartesian fibration. Its fiber over a monoid $T \in \mathbf{Mon}(\mathcal{C})$ is called the category of $T$-modules and is denoted $\mathbf{LMod}^T(\mathcal{C})$.*

Henceforth, when we say that $X$ is an $M$-module we mean that $X$ is an object of $\mathbf{LMod}(\mathcal{C})$ over $M$. We call an action of $M$ on an object $X \in \mathcal{C}$ the data of a $M$-module whose underlying object is $X$.

This allows to define a *monoidal $\infty$-category* $\mathcal{M}$ to be a monoid in $\mathbf{Cat}_{\infty}$. A *monoidal action* of such a monoidal $\infty$-category $\mathcal{M}$ on an $\infty$-category $\mathcal{C}$ is an action in $\mathbf{Cat}_{\infty}$ in the sense above.

We will generally work with monoidal $\infty$-categories and monoidal action from “the other side” of the straightening/unstraightening equivalences. Instead of defining a monoidal $\infty$-category as a functor $N(\Delta^{op}) \to \mathbf{Cat}_{\infty}$, we define a monoidal $\infty$-category $\mathcal{M}$ to be a coCartesian fibration $\mathcal{M}^* \to N(\Delta^{op})$ which is classified by a functor satisfying the Segal conditions as in Definition 3.1. Similarly, an action of $\mathcal{M}$ on an $\infty$-category $\mathcal{C}$ is defined as a coCartesian fibration $\mathcal{C}^* \to N(\Delta^{op}) \times \Delta^1$ classified by a functor to $\mathbf{Cat}_{\infty}$ satisfying the conditions of Definition 3.2.

13