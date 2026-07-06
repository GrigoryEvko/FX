# 3.1.1. **Definition :** *A pre-distance $d$ on a locale $X$ is a function*

$$d : X \times X \rightarrow \overleftarrow{\mathbb{R}_+^\infty}$$

*which is symmetric ($d(x, y) = d(y, x)$), satisfies the triangular inequality $d(x, y) \leqslant d(x, z) + d(z, y)$ and such that $d(x, x) = 0$*

*A pre-metric locale is a locally positive locale $X$ endowed with a pre-distance.*

We insist on the fact that our pre-metric locale are always assumed to be locally positive. We do not know exactly which parts of the theory of metric locales it is possible to develop without this hypothesis (without it, one should at least avoid everything which uses the construction $B_q \mathcal{L}$ of 3.1.2 but it seems that what is left is relatively well behaved without it). In any case, the theory is at least easier, and probably nicer with this local positivity assumption. Theorem 2.6.5 shows that this case is enough for the Gelfand duality, and as locale positivity descend along open surjections and is automatic for metric sets it is also enough to obtain good descent properties.

Of course, the formulas $d(x, y) = d(y, x)$ and $d(x, y) \leqslant d(x, z) + d(z, y)$ have to be interpreted in a diagrammatic way or in terms of generalized points. In particular, if we define

$$\Delta_q := \{(x, y) | d(x, y) < q\} = d^* \left( \overleftarrow{[0, q]} \right)$$

then the symmetry means that $\Delta_q$ is invariant by exchange of the two factors, $d(x, x) = 0$ means that for all $q$, $\Delta_q$ contains the diagonal embeddings of $X$, and finally the triangular inequality means that:

$$\pi_{1,2}^*(\Delta_q) \wedge \pi_{2,3}^*(\Delta_{q'}) \leqslant \pi_{1,3}^*(\Delta_{q+q'})$$

Where $\pi_{i,j}$ denote the various projections from $X^3$ to $X^2$.

# 3.1.2. **Definition :** *Let $X$ be a pre-metric locale, and $\mathcal{L}$ and $\mathcal{M}$ be two sublocales of $X$. then*

- *We say that $\delta(\mathcal{L}) < q$ if $\mathcal{L} \times \mathcal{L} \subseteq \Delta_{q'}$ for some positive rational number $q' < q$. One easily sees that $\delta(\mathcal{L})$ is indeed an element of $\overleftarrow{\mathbb{R}_+^\infty}$;*
- *We say that $\mathcal{L} \triangleleft_q \mathcal{M}$ if $\pi_1^*(\mathcal{L}) \wedge \Delta_q \leqslant \pi_2^*(\mathcal{M})$. We say that $\mathcal{L} \triangleleft \mathcal{M}$ if $\mathcal{L} \triangleleft_q \mathcal{M}$ for some positive rational $q$;*
- *if $q$ is a positive rational number then $B_q \mathcal{L} = (\pi_2)! (\pi_1^*(\mathcal{L}) \wedge \Delta_q)$.*

These should be interpreted as: $\delta$ is the diameter of a sublocale, $B_q$ is the $q$ neighborhood of a sublocale and $\mathcal{L} \triangleleft_q \mathcal{M}$ means that the $q$ neighborhood of $\mathcal{L}$ is included in $\mathcal{M}$.

19