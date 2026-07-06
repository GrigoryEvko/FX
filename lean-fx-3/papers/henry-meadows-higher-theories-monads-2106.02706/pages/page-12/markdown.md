monadic right adjoint functors to $\mathcal{C}$. This result is mentioned without proof by Lurie in Remark 4.7.3.8 of [16].

Lurie's definition works as follows: given an $\infty$-category $\mathcal{C}$, he constructs a monoidal $\infty$-category of endofunctor $\text{End}(\mathcal{C})$ that acts on $\mathcal{C}$. The category $\mathbf{Mnd}_{\mathcal{C}}$ of monads on $\mathcal{C}$ is then defined as the category of monoids in $\text{End}(\mathcal{C})$. As $\text{End}(\mathcal{C})$ acts on $\mathcal{C}$, given a monad $T$ on $\mathcal{C}$ we can look at the category $\mathcal{C}^T$ of objects of $\mathcal{C}$ endowed with an action of $T$ (the left $T$-modules) and this is what we call the $\infty$-category of $T$-algebras, or the Eilenberg-Moore category of $T$.

In [16] Lurie make sense of these notions of monoids and algebras (or rather modules in the general terminology) using his formalism of $\infty$-operads. In fact, [16] developed two formalisms that allow one to do this: one can use the formalism of (symmetric) $\infty$-operads, or the formalism of planar (non-symmetric) $\infty$-operads. They are shown to be equivalent in [16, Proposition 4.1.2.11] and [16, Theorem 2.3.3.23], but lead to different combinatorics for the concrete description of monads. Here we will recall all of the relevant definitions in the formalism of planar operads, in a way as unpacked as possible.

**Definition 3.1.** A *monoid object* $M$ in an $\infty$-category $\mathcal{C}$ with finite products is a functor $M : N(\Delta^{op}) \to \mathcal{C}$ which satisfies the Segal conditions:

- $M([0])$ is a terminal object of $\mathcal{C}$.
- For each $n$, the map $M([n]) \to M([1])^n$, induced by the maps $[1] \simeq \{i, i+1\} \subset [n]$ for $i = 0 \dots, n-1$ is an equivalence.

The category $\mathbf{Mon}(\mathcal{C})$ of monoids in $\mathcal{C}$ is the full subcategory of $\mathcal{C}^{\Delta^{op}}$ on monoids. $M([1])$ is called the underlying object of $M$.

For example, if $M = M([1])$ is the underlying object of a monoid, the multiplication map $M^2 \to M$ is obtained as the map $M^2 \simeq M([2]) \to M([1])$ induced by $[1] \simeq \{0, 2\} \subset \{0, 1, 2\}$. The associativity and higher coherence conditions are obtained by looking at the maps between the $M([k])$ for $k \geqslant 3$.

Note that this is the definition of monoid *with respect to the cartesian product*. We will later give a definition of monoids with respect to a monoidal structure, which is different (they are equivalent when the monoidal structure is cartesian by (3) of [16, Corollary 2.4.1.8] and [16, Proposition 2.4.2.5]). The same remarks apply to the next definition as well:

12