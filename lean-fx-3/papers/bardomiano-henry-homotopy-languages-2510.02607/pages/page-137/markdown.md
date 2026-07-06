As is usual, maps in $\mathrm{COF}(\mathcal{C})$ are called *cofibrations* and they are indicated by arrows “$\rightharpoonup$”.

Dually, a category $\mathcal{C}$ is $\kappa$-*clan* if $\mathcal{C}^{op}$ is a $\kappa$-coclan. The distinguished maps are called *fibrations* and they are denoted by $\mathrm{FIB}(\mathcal{C})$. The fibrations are indicated by arrows “$\rightharpoonup$”. When working with $\kappa$-clans we keep the terminology “transfinite compositions” from $\kappa$-coclans as there is no risk of confusion.

*Observation B.56.* The $\kappa$-contextual category $\mathbb{C}_T$ associated to a generalized $\kappa$-algebraic theory $T$ has a natural $\kappa$-clan structure. Indeed, we can take $\mathrm{FIB}(\mathbb{C}_T)$ as the set of display maps. All the axioms are easily verified. Moreover, this is true for any $\kappa$-contextual category not only for $\mathbb{C}_T$.

Recall that a *comprehension category* consists of a category $\mathcal{C}$, a fibration $p: \mathcal{E} \to \mathcal{C}$ and a functor $F: \mathcal{E} \to \mathcal{C}^{\to}$ such that:

1. \(\partial_0F = p\)
2. If \( f \) is a cartesian arrow in \( \mathcal{E} \), then \( Ff \) is a pullback in \( \mathcal{C} \); equivalently, \( Ff \) is a cartesian arrow with respect to the codomain functor \( \partial_0: \mathcal{C}^{\rightarrow} \rightarrow \mathcal{C} \).

The fibration $p$ is *cloven* if it comes with a choice of cartesian lifts. The comprehension category is said to be *split* is $p$ is a split fibration. We also say that is *full* if $F$ is fully faithful, we use the notation $(\mathcal{C}, \mathcal{E}, p, F)$ for a comprehension category.

The following example appears in [Jac93, Example 4.5], we rewrite it in our setting of $\kappa$-clans. Let us fix a $\kappa$-clan $\mathcal{C}$, then the inclusion functor $\iota: \mathrm{FIB}(\mathcal{C}) \hookrightarrow \mathcal{C}^{\to}$ and $P = \partial_0 \iota$ form a full comprehension category. More precisely: $\mathrm{FIB}(\mathcal{C})$ has objects fibrations in $\mathcal{C}$ and arrows between two fibrations $\alpha: f \to g$ are commutative squares of the form

$$
\begin{array}{c}
A \xrightarrow{k} B \\
f \downarrow \qquad \qquad \qquad \downarrow g \\
\Delta \xrightarrow{l} \Gamma.
\end{array}
$$

Hence, an object in $\mathrm{FIB}(\mathcal{C})_{\Gamma}$ over $\Gamma \in \mathcal{C}$ is a fibration $A \twoheadrightarrow \Gamma$. Observe that an arrow $\alpha: f \to g$ as above is cartesian if and only if it is a pullback square in $\mathcal{C}$. In conclusion, for an arrow $l: \Delta \to \Gamma$ and $g: B \twoheadrightarrow \Gamma \in \mathrm{FIB}(\mathcal{C})_{\Gamma}$, a

137