3.1.13. We also note that if we define $\mathcal{C}(\mathcal{T})$ to be the category of pre-metric locales and metric maps internal to $\mathcal{T}$, then open surjections are descent morphisms for $\mathcal{C}$ (see 2.4): If $f: \mathcal{E} \to \mathcal{T}$ is an open surjection and $(X, d)$ is a pre-metric locale in $\mathcal{E}$ endowed with a descent data then it is in particular a descent data on $X$ as a locale, so as locale descend along open surjections, $X$ comes from a locale $X'$ in $\mathcal{T}$. As the $\epsilon: \pi_1^* X \to \pi_2^* X$ is an isomorphism in the category of metric maps it is an isometric map and hence the distance is a morphism in $Des(f, \mathcal{C})$ and hence also descends into a function $d': X' \times X' \to \overbrace{\mathbb{R}_+^\infty}^\infty$. All the axioms defining a pre-distance are equality relations (and inequality for the specialisation order), hence as they are satisfied by the pull-back of $(X', d')$ along an open surjection they are also satisfied by $(X', d')$. Hence $(X, d)$ is the pull-back of the pre-metric locale $(X', d')$. This proves that the functor $\mathcal{T} \to Des(f, \mathcal{C})$ is essentially surjective, but it is also fully faithful for similar reasons: a metric map commuting to descent data is in particular a map of locales commuting to descent data, and as $f$ is an open surjection a map $h$ is metric if and only if $f^*(h)$ is metric.

## 3.2 Metric locales

3.2.1. If $(X, d)$ is a pre-metric locale, then the various properties given in 3.1.4 show that, essentially, the "topology defined by $d$" (whatever the precise meaning of this is) is coarser than the topology of $X$, but nothing forces them to agree. For example, a metric set in the usual sense (with a distance function taking value in $\overbrace{\mathbb{R}_+^\infty}^\infty$), gives a pre-distance on a discrete locale, and the topology defined by $d$ can disagree with the discrete topology. That is why we require the following additional property:

Definition: A Metric locale is a pre-metric locale $X$ such that for all $U \in \mathcal{O}(X)$,

$$U = \bigvee_{\substack{V \in \mathcal{O}(X) \\ V \triangleleft U}} V.$$

This definition is equivalent to the fact that the family $(B_q V)_{V \in \mathcal{O}(X), q \in \mathbb{Q}_+^\infty}$ forms a basis of the topology. Indeed $V \triangleleft_q U$ is equivalent to $B_q V \leqslant U$ and $B_q V = \bigvee B_{q'} V$ for $q' < q$, hence this asserts that the open balls form a basis of the topology.

Also if $X$ is metric and $f$ is a geometric morphism then $f^\#(X)$ is also metric because the $B_q V$ for $V \in f^*(\mathcal{O}(X))$ form a basis of $f^\#(X)$.

Proposition: A Metric locale satisfies the following separation axiom: the diagonal embedding

$$X \to \bigwedge_q \Delta_q$$

is an isomorphism (where the intersection is an intersection of sublocale).

The intuitive reason for this is that if we consider two points $(x, y)$ in $\bigwedge_q \Delta_q$ then by definition $d(x, y) = 0$. If the open balls form a basis of the topology

29