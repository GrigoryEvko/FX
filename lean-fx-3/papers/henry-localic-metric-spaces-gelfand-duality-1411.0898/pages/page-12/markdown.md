**2.3.17. Proposition :** *Let $X$ be a locally positive locale (of the base topos), then there exists a topos $\mathcal{T}$ (even a locale) such that the canonical geometric morphism $p : \mathcal{T} \rightarrow \ast$ is an open surjection and such that $p^\#(X)$ is weakly spatial in $\mathcal{T}$.*

This result will be extremely important in the rest of this paper: indeed weak spatiality will play the same role as spatiality for complete metric spaces (see 3.6), and as locales descend along open surjections this result will roughly allow us to assume whenever needed that all the metric locales involved come from metric sets.

**Proof :**

Thanks to the previous lemma, one can construct a locale $\mathcal{L}$ in which one has a basis $(U_i)_{i \in I}$ of positive open sublocales of $p^\#(X)$ indexed by a set with decidable equality. By 2.3.7:

$$Y = \prod_{i \in I} U_i$$

is a positive locally positive locale, and corresponds to an open surjection (also denoted $p$) $p : \mathsf{Sh}_{\mathcal{L}}(Y) \rightarrow \mathcal{L} \rightarrow \ast$. We will now prove that $p^\#(X)$ is weakly spatial.

Internally in $\mathcal{L}$, there is a canonical map $s_i : Y \rightarrow X \times Y$ defined as the composition of the i-th projection and the inclusion of $U_i$ into $X$ on the first component and the identity of $Y$ on the second component. This defines a map of locale over $Y$:

$$s : \prod_{i \in I} Y \rightarrow X \times Y = p^\#(X)$$

which internally in $\mathsf{Sh}_{\mathcal{L}}(Y)$ gives a map $s$ from $f^*(I)$ to $p^\#(X)$ such that for each $i$, $s(i)$ is a point of $U_i$. As any positive open sublocale of $p^\#(X)$ contains one of the $U_i$, it shows that $p^\#(X)$ is weakly spatial. $\square$

## 2.4 Descent theory

Let $\mathcal{C}$ be a functor from the 2-category of toposes to the 2-category of categories, like for example the functor which sends every topos $\mathcal{T}$ to the category of internal locales of $\mathcal{T}$, and any geometric morphism $f$ to the functor $f^\sharp$. We will denote by $f^*$ the action of a geometric morphism $f$ on $\mathcal{C}$.

Let $f : \mathcal{E} \rightarrow \mathcal{T}$ be a geometric morphism, and let $c \in |\mathcal{C}(\mathcal{E})|$. A descent data on $c$ is the data of an isomorphism $\epsilon : \pi_1^*(c) \rightarrow \pi_2^*(c) \in \mathcal{C}(\mathcal{E} \times_{\mathcal{T}} \mathcal{E})$, such that if $\Delta$ denotes the diagonal map $\Delta : \mathcal{E} \rightarrow \mathcal{E} \times_{\mathcal{T}} \mathcal{E}$ then $\Delta^*(\epsilon)$ identifies with the identity map of $c$, and if $\pi_{1,2}, \pi_{1,3}$ and $\pi_{2,3}$ denote the three projections $\mathcal{E} \times_{\mathcal{T}} \mathcal{E} \times_{\mathcal{T}} \mathcal{E} \rightarrow \mathcal{E} \times_{\mathcal{T}} \mathcal{E}$ and $\pi_1, \pi_2$ and $\pi_3$ the three projections from $\mathcal{E} \times_{\mathcal{T}} \mathcal{E} \times_{\mathcal{T}} \mathcal{E}$ to $\mathcal{E}$ then one has a commutative diagram:

12