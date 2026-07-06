It is immediate from point 3. that a locally positive fiberwise closed sublocale of a complete locale is also complete.

**3.3.13. Proposition :** *If $X$ is a pre-metric locale in a topos $\mathcal{T}$ and $f : \mathcal{E} \to \mathcal{T}$ is an open (or proper) surjection such that $f^\#(X)$ is complete then $X$ is complete.*

**Proof :**

The pull-back along $f$ of the canonical map $X \to \tilde{X}$ is the canonical map $f^\#(X) \to f^\#(\tilde{X})$. Hence as $f^\#$ is a descent functor for the categories of locales, it is in particular conservative and if the pull-back map is an isomorphism, the map $X \to \tilde{X}$ is also an isomorphism. $\square$

An immediate corollary of this result is that if $\mathcal{C}(\mathcal{T})$ is the category of complete metric locales and metric maps between them then objects of $\mathcal{C}$ descend along open surjections. Indeed, it is a full subcategory of the category of pre-metric locales, for which open surjections are descent morphisms as observed in 3.1.13, and this just states that $(X', d')$ is complete if it descends from a complete locale $(X, d)$.

**3.3.14. Proposition :** *Let $X$ be a pre-metric locale and let $X_d$ be the regular image of $X$ into $\tilde{X}$ then $\mathcal{O}(X_d)$ identifies with the set of $U \in \mathcal{O}(X)$ such that*

$$U = \bigvee_{V \triangleleft U} V$$

*and any map compatible with $\triangleleft$ from $X$ to a metric locale $Y$ factors into $X_d$.*

**Proof :**

The regular image of $i : X \to \tilde{X}$ is identified as a frame with the image of $i^* : \mathcal{O}(\tilde{X}) \to \mathcal{O}(X)$ which is clearly (by 3.3.8) the set of open sublocales defined in the proposition. If one has any map $f$ from $X$ to a metric locale $Y$ compatible with $\triangleleft$ then for any $U \in \mathcal{O}(Y)$,

$$U = \bigvee_{V \triangleleft U} V$$

Hence,

$$f^*(U) = \bigvee_{V \triangleleft U} f(V)^*$$

as $f^*(V) \leqslant f^*(U)$ this proves that $f^*(U) \in \mathcal{O}(X_d)$. Hence $f$ factors into $X_d$. $\square$

41