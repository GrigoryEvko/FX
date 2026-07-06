### 3.4 Product of metric locales

3.4.1. Let $\mathcal{L}$ and $\mathcal{M}$ be two pre-metric locales, one defines a pre-distance on $\mathcal{L} \times \mathcal{M}$ in the following way: $\Delta_q^{\mathcal{L} \times \mathcal{M}} \subset (\mathcal{L} \times \mathcal{M}) \times (\mathcal{L} \times \mathcal{M})$ is the intersection of the pull-back $\pi_{1,3}^*(\Delta_q^{\mathcal{L}})$ and $\pi_{2,4}^*(\Delta_q^{\mathcal{M}})$ (where the exponent on $\Delta$ indicate to which locale it is related). This corresponds to taking $d((l, m), (l', m')) = \max(d(l, l'), d(m, m'))$, and the classical argument can be adapted (in terms of generalised points) to prove that this is indeed a pre-distance on $\mathcal{L} \times \mathcal{M}$.

**Proposition :** $\mathcal{M} \times \mathcal{L}$ endowed with the previously constructed distance function is the categorical product of $\mathcal{M}$ and $\mathcal{L}$ in the category of pre-metric locales and metric maps.

**Proof :**

The projection $\pi_1 : \mathcal{L} \times \mathcal{M} \to \mathcal{L}$ satisfies $\Delta_q \subset \pi_1^*(\Delta_q)$ by construction of the distance function on $\mathcal{L} \times \mathcal{M}$, hence it is a metric map. In particular if $f : X \to \mathcal{M} \times \mathcal{L}$ is a metric map then the two component $f_1$ and $f_2$ are metric maps. Conversely, assume that $f_1$ and $f_2$ are metric maps. Then

$$(f \times f)^*(\Delta_q^{\mathcal{L} \times \mathcal{M}}) = (f \times f)^*(\pi_{1,3}^*(\Delta_q^{\mathcal{L}}) \wedge \pi_{2,4}^*(\Delta_q^{\mathcal{M}})).$$

But $\pi_{1,3}(f \times f) = f_1 \times f_1$ and $\pi_{2,4}(f \times f) = f_2 \times f_2$, hence,

$$(f \times f)^*(\Delta_q^{\mathcal{L} \times \mathcal{M}}) = (f_1 \times f_1)^*(\Delta_q^{\mathcal{L}}) \wedge (f_2 \times f_2)^*(\Delta_q^{\mathcal{M}})$$

As we assume that both $f_1$ and $f_2$ are metric,

$$\Delta_q^X \subset (f_1 \times f_1)^*(\Delta_q^{\mathcal{L}}) \wedge (f_2 \times f_2)^*(\Delta_q^{\mathcal{M}}).$$

This proves that $f$ is also metric and concludes the proof of the proposition. $\square$

3.4.2. **Proposition :** *The product of two complete metric locales is a complete metric locale. More generally the completion of $\mathcal{L} \times \mathcal{M}$ is canonically isomorphic to $\widetilde{\mathcal{L}} \times \widetilde{\mathcal{M}}$.*

**Proof :**

Assume that $\mathcal{L}$ and $\mathcal{M}$ are complete. Let $S \to Y$ be a strongly dense map, and let $f : S \to \mathcal{L} \times \mathcal{M}$ be an isometric map. Then by the previous result and Proposition 3.3.11 there is a map $\widetilde{f} : Y \to \mathcal{L} \times \mathcal{M}$ extending $f$. Hence $\mathcal{L} \times \mathcal{M}$ is complete.

For the second part, $\mathcal{L} \times \mathcal{M} \to \widetilde{\mathcal{L}} \times \widetilde{\mathcal{M}}$ is a fiberwise dense isometric map with $\widetilde{\mathcal{L}} \times \widetilde{\mathcal{M}}$ complete, hence $\widetilde{\mathcal{L}} \times \widetilde{\mathcal{M}}$ is the completion of $\mathcal{L} \times \mathcal{M}$. $\square$

42