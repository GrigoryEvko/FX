3.3.6. Let $X$ be a pre-metric locale, and $B$ be a metric basis on $X$, the theory of regular $B$-Cauchy filters as defined in 3.3.2 is clearly a propositional geometric theory with basic propositions indexed by $B$. Hence it has a classifying space $\tilde{X}_B$.

If $X$ is a pre-metric locale in a topos $\mathcal{T}$ and if $f : \mathcal{E} \rightarrow \mathcal{T}$ is a geometric morphism, then $f^\#(\tilde{X}_B) \simeq f^\#(\tilde{X})_{f^*(B)}$ because the pull-back of a classifying locale classifies the pull-back of the theory and the pull-back of the theory of regular $B$-Cauchy filter is exactly the theory of regular $f^*(B)$-Cauchy filter on $f^\#(X)$. But by 3.3.5 the points of $\tilde{X}_B$ do not depend on $B$, and hence by the observations we just made, their points on any topos over the base topos do not depend on $B$, and all the $\tilde{X}_B$ are isomorphic.

**Definition :** *The completion $\tilde{X}$ of $X$ is defined as the classifying locale $\tilde{X}_B$ of the theory of regular $B$-Cauchy filters on $X$ for any metric basis $B$ of $X$.*

Also if $U$ is any positive open sublocale of $X$ we denote by $U^\sim$ the open sublocale of $\tilde{X}$ corresponding to the proposition “$U \in \mathcal{F}$”. It is a general fact about classifying spaces that the $U^\sim$ form a pre-basis of the topology of $X$, but the axiom (CF2) show that for any metric basis $B$ of $X$, the $U^\sim$ with $U \in B$ form a basis of $\tilde{X}$. If $U$ is not necessarily positive, one can still defined $U^\sim$ by

$$U^\sim = \bigvee_{\substack{V \leqslant U \\ V > \emptyset}} V^\sim.$$

When $U > \emptyset$, the two possible definitions of $U^\sim$ are compatible because

$$\bigvee_{\substack{V \leqslant U \\ V > \emptyset}} V^\sim = U^\sim$$

3.3.7. **Proposition :** *Let $Y$ be a locale, a morphism $f$ from $Y$ to $\tilde{X}$ corresponds to a map $\tau : B \rightarrow \mathcal{O}(Y)$ such that:*

1. $\tau$ is non-decreasing.
2. $\tau(U) \wedge \tau(V) \leqslant \bigvee_{\substack{W \in B \\ W \leqslant U \wedge V}} \tau(W)$
3. $\bigvee_{\substack{U \in B \\ \delta(U) < \eta}} (\tau(U)) = Y$
4. $\tau(U) \leqslant \bigvee_{\substack{V \in B \\ V \leqslant U}} \tau(V)$

*Moreover this correspondence is characterized by the relation $\tau(U) = f^*(U^\sim)$. Also if $\tau$ only satisfies the first three properties, then there exists a unique $\tau^r$ such that $\tau^r$ satisfy the four properties and $\tau^r \leqslant \tau$ for the pointwise ordering and one has*

35