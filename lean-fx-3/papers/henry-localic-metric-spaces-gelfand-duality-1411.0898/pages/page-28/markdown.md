3.1.12. We now consider two toposes $\mathcal{E}$ and $\mathcal{T}$, a geometric morphism $f: \mathcal{E} \to \mathcal{T}$ and $X$ a pre-metric locale in $\mathcal{T}$. As $f^\#$ is a functor from locale in $\mathcal{T}$ to locale in $\mathcal{E}$ commuting to projective limit and $f^\#(\widehat{\mathbb{R}_+^\infty}_\mathcal{T}) \simeq \widehat{\mathbb{R}_+^\infty}_\mathcal{E}$, we obtain a map $f^\#(d): f^\#(X) \times f^\#(X) \to \widehat{\mathbb{R}_+^\infty}$. Moreover all the axioms asserting that $d$ is a pre-distance can be pulled back turning $f^\#(X)$ into a pre-metric locale.

**Proposition :** Let $\mathcal{L}, \mathcal{M}$ be a sublocales of $X$, then (as sublocales of the pre-metric locale $f^\#(X)$) one has:

- If $\delta(\mathcal{L}) < q$ then $\delta(f^\#(\mathcal{L})) < q$.
- If $\mathcal{L} \triangleleft_q \mathcal{M}$ then $f^\#(\mathcal{L}) \triangleleft_q f^\#(\mathcal{M})$.
- If $\mathcal{L}$ is locally positive then $B_q f^\#(\mathcal{L}) = f^\#(B_q \mathcal{L})$.

**Proof :**

$f^\#$ is a functor commuting to all projective limits, in particular pull-backs, products and intersections, and by definition of the metric $f^\#(\Delta_q) = \Delta_q$ hence

$$\mathcal{L} \times \mathcal{L} \subseteq \Delta_{q'}$$

implies

$$f^\#(\mathcal{L}) \times f^\#(\mathcal{L}) \subseteq \Delta_{q'}$$

and

$$\pi_1^*(\mathcal{L}) \wedge \Delta_q \subseteq \pi_2^*(\mathcal{M})$$

implies

$$\pi_1^*(f^\#(\mathcal{L})) \wedge \Delta_q \subseteq \pi_2^*(f^\#(\mathcal{M}))$$

which proves the first two points.

The third point is harder because in general the pull-back $f^\#$ does not commute with the direct image functor $(\pi_2)_!$. But if we assume that $\mathcal{L}$ is locally positive, then the map

$$\pi_1^*(\mathcal{L}) \wedge \Delta_q \to B_q \mathcal{L}$$

is the restriction of the projection from $\mathcal{L} \times X$ to $X$ and hence is an open map. In particular (as we know that it is a surjection by definition) it is an open surjection and hence its pull-back by $f^\#$ is again an open surjection. In particular, the maps

$$\pi_1^*(f^\#(\mathcal{L})) \wedge \Delta_q \to f^\#(B_q \mathcal{L}) \to f^\#(X)$$

form a factorisation surjection/inclusion and, by uniqueness of such a factorisation, we obtain the third point. $\square$

28