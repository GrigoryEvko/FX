4. Let $V \in B$, let $W$ appearing in the union defining $\tau(V)$, i.e. there exists a positive rational $q$, and a $V' \in B$ such that $\delta(W) < q$ and $V' \triangleleft_q V$.

But, there exists a positive rational number $\epsilon$ such that $\delta(W) < q - \epsilon$, and $V' \triangleleft_{q-\epsilon} B_{q-\epsilon} V' \triangleleft_\epsilon V$. Hence

$$W \leqslant \tau(B_{q-\epsilon} V' \leqslant \bigvee_{\substack{U \in B \\ U \triangleleft V}} \tau(U).$$

Finally, we obtain

$$\tau(V) \leqslant \bigvee_{\substack{U \in B \\ U \triangleleft V}} \tau(U).$$

The fact that the map $f$ induced by $\tau_p$ is metric follows from axiom (MM6) using the characterization (c) of metric maps given in 3.1.8, hence this concludes the proof of theorem 3.5.2.

### 3.6 Case of metric sets

3.6.1. We define a (pre)metric set as set $X$ endowed with a distance function $d: X \times X \to \overleftarrow{\mathbb{R}_+^\infty}$ satisfying the usual axioms for a (pre)distance:

- $d(x, x) = 0$
- $d(x, y) = d(y, x)$
- $d(x, z) \leqslant d(x, y) + d(y, z)$

With additionally, $d(x, y) = 0 \Rightarrow x = y$ for a metric set.

A (pre)metric set can be seen as a pre-metric locale by seeing its underlying set as a discrete locale. It is in general not a metric locale even if we start with a metric set.

3.6.2. We will say that a metric set $(X, d)$ is complete if the natural map $i: X \to \widetilde{X}$ identifies $X$ with the points of $\widetilde{X}$. As points of $\widetilde{X}$ identify with regular Cauchy filters one easily checks that this is equivalent to the usual (Cauchy filter based) definition of completeness.

48