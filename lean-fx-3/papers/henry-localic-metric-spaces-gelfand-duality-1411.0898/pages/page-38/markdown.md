which proves that this formula defines a function $d : \widetilde{X} \times \widetilde{X} \to \overleftarrow{\mathbb{R}_+^\infty}$. This function is clearly symmetric, and the diagonal embeddings factor into $\Delta_q$ because the $U^\sim$ with $\delta(U) < q$ cover $\widetilde{X}$ by axiom (CF3). The last point to check is the triangular inequality, but:

$$\pi_{1,2}^*(\Delta_q) \wedge \pi_{2,3}^*(\Delta_{q'}) = \bigvee_{\substack{\delta(U) < q \\ \delta(U') < q'}} U^\sim \times (U^\sim \wedge U'^\sim) \times U'^\sim$$
$$(\pi_{1,3})! \left( \pi_{1,2}^*(\Delta_q) \wedge \pi_{2,3}^*(\Delta_{q'}) \right) = \bigvee_{\substack{\delta(U) < q \\ \delta(U') < q' \\ U \wedge U' > \emptyset}} U^\sim \times U'^\sim.$$

Since $U^\sim \times U'^\sim \leqslant (U \vee U')^\sim \times (U \vee U')^\sim$ and as we are restricted to the case $U \wedge U' > \emptyset$, one has $\delta(U \vee U') < q + q'$ by point 6 of 3.1.4, hence $U^\sim \times U'^\sim \subset \Delta_{q+q'}$ and

$$(\pi_{1,3})! \left( \pi_{1,2}^*(\Delta_q) \wedge \pi_{2,3}^*(\Delta_{q'}) \right) \leqslant \Delta_{q+q'},$$

which is the triangular inequality. The last point to prove is that this pre-distance is a distance. This a consequence of the following lemma. $\square$

**Lemma :** For any $U \in \mathcal{O}(X)$ one has $B_q(U^\sim) \leqslant (B_q U)^\sim$. In particular, if $U \triangleleft_q V$ then $U^\sim \triangleleft_q V^\sim$.

**Proof :**

Indeed, for any $W \in \mathcal{O}(X)$ such that $\delta(W) < q$ and $U^\sim \wedge W^\sim$ is positive, (CF2) proves that $U \wedge W$ is positive, hence, from the definition of $\Delta_q$:

$$B_q(U^\sim) = (\pi_2)! (\pi_1^*(U^\sim)\Delta_q) = \left( \bigvee_{\substack{\delta(W) < q \\ U^\sim \wedge W^\sim > \emptyset}} W^\sim \right) \leqslant (B_q U)^\sim$$

which concludes the proof of the lemma. $\square$

This lemma allows to finish the proof of the proposition, indeed, by (CF4), $V^\sim = \bigvee_{U \triangleleft V} U^\sim$, hence any $V \in \mathcal{O}(\widetilde{X})$ can be written as

$$V = \bigvee_{U^\sim \leqslant V} U^\sim = \bigvee_{A^\sim \triangleleft U^\sim \leqslant V} A^\sim.$$

**3.3.11. Proposition :** Let $S \to Y$ be a fiberwise dense isometric map between two pre-metric locales, let $X$ be any pre-metric locale and $f : S \to \widetilde{X}$ be a uniform map. Then there exists a unique extension $\widetilde{f} : Y \to \widetilde{X}$.

**Proof :**

38