to be *decidable*, if its diagonal embedding $X \rightarrow X \times X$ is complemented. A set $X$ (or an object of a topos) is said to be *inhabited* if it satisfies (internally) $\exists x \in X$. It is said to be *finite* if it is Kuratowski finite (see [12, D5.4]), i.e. if $\exists n \in \mathbb{N}, x_1, \dots, x_n \in X$ such that $\forall x \in X, \exists i, x = x_i$. Note that in particular (as $\mathbb{N}$ is decidable) a finite set is either empty or inhabited.

When considering product $E_1 \times \dots \times E_n$ of objects of any kind (generally locales) we will denote by $\pi_i$ the projection onto $E_i$, by $\pi_{i,j}$ the projection onto $E_i \times E_j$, etc... We generally do not specify the domain of definition and we hope that it will be clear from the context. For example one has: $\pi_1 \circ \pi_{i,j} = \pi_i$ and $\pi_2 \circ \pi_{i,j} = \pi_j$ because in these formulas $\pi_1$ and $\pi_2$ denote the two projections from $E_i \times E_j$ to $E_i$ and $E_j$ respectively.

## 2.2 The category of locales

We will start by briefly introducing the notion of locale, essentially in order to fix the notation and the vocabulary. A short introduction to this subject can be found in the first two sections of [2], a more complete one in part $C$ (especially in $C1$) of [12] and an extremely complete (but non constructive) one in [17].

2.2.1. A *frame* is an ordered set which admit arbitrary supremums and such that binary infimums distribute over arbitrary supremums. A morphism of frame is a non-decreasing map which preserve both arbitrary supremum and finite infimum.

2.2.2. The category of *locales* is defined as the opposite category of the category of frames. But we will adopt “topological” notations for them:

- If $X$ is a locale, the corresponding frame is denoted by $\mathcal{O}(X)$.
- If $f: X \rightarrow Y$ is a morphism of locales, we denote by $f^*$ the corresponding frame homomorphism from $\mathcal{O}(Y)$ to $\mathcal{O}(X)$.
- An element $U \in \mathcal{O}(X)$ is called an open sublocale of $X$, the top element of $\mathcal{O}(X)$ is denoted $X$.
- As $f^*$ commutes to arbitrary supremums, it has a right adjoint denoted $f^*$.

Also we will tend to call unions and intersections the supremums and infimums in $\mathcal{O}(X)$.

4