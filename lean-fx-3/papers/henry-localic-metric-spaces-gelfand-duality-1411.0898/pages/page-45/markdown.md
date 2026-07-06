As $\tau$ is positive (the presentation of $X$ is assumed to be locally positive) and $V_1 \sim \wedge V_2$ is covered by the $V^\sim$ for $V \subseteq V_1 \wedge V_2$ this concludes the proof of (MM5).

We now prove (MM6). Let $U, V$ and $V'$ such that $U \wedge f^*(V^\sim) > \emptyset$ and $U \wedge f^*(V'^\sim) > \emptyset$. Let $q$ and $q'$ such that $\delta(V) < q$ and $\delta(V') < q'$. Let also $\epsilon$ be a positive rational number such that $\delta(V) < q - 2\epsilon$ and $\delta(V') < q' - 2\epsilon$. Let $W = B_\epsilon V$ and $W' = B_\epsilon V'$, in particular $\delta(W) < q$ and $\delta(W') < q'$.

One has, by the assumption on $V$ and $V'$ and the fact that $f$ is metric (see 3.1.8 proposition (c)):

$$\delta(W^\sim \vee W'^\sim) \subseteq \delta(W^\sim) + \delta(W'^\sim) + \delta(U)$$

Let $i$ be the isometric map $Y \rightarrow \tilde{Y}$ of 3.3.8, i.e.

$$i^*(V^\sim) = \bigvee_{U \in V} U.$$

In particular, as $W$ and $W'$ are open balls, one has $i^*(W^\sim) = W$ and $i^*(W'^\sim) = W'$, and $i^*(W^\sim \vee W'^\sim) = W \vee W'$, and as $i$ is isometric, this implies that $\delta(W \vee W') \leqslant \delta(W^\sim \vee W'^\sim)$.

Moreover since $\delta(W) < q$ then by definition of the distance on $\tilde{Y}$, $W^\sim \times W^\sim \subseteq \Delta_q$, and hence $\delta(W^\sim) \leqslant q$. One deduces from this that

$$\delta(V \vee V') \leqslant \delta(W \vee W') \leqslant \delta(W^\sim \vee W'^\sim) \leqslant \delta(W^\sim) + \delta(W'^\sim) + \delta(U) \leqslant q + q' + \delta(U),$$

which concludes the proof as it has been done for arbitrary $q$ and $q'$ bigger than $\delta(V)$ and $\delta(V')$.

3.5.5. **Definition :** *To any point $p$ of $[X_A, Y_B]_1$ we associate the function $\tau_p : B \rightarrow \mathcal{O}(X)$ defined by:*

$$\tau_p(V) := \bigvee_{\substack{\delta(W) < q \\ V' \in \mathbb{N}^p \\ p \in (W, V')}} W$$

where $V'$ runs through elements of $B$, $W$ through elements of $A$, and $q$ through positive rational numbers.

**Proposition :** *If $f$ is a metric map from $X$ to $\tilde{Y}$ and $p$ is the point of $[X_A, Y_B]$ associated to $f$ in 3.5.4 then*

$$\tau_p(V) = f^*(V^\sim).$$

**Proof :**

45