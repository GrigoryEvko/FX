3.1.10. **Definition :** A map between two pre-metric locales is said to be “compatible with $\triangleleft$” if $U \triangleleft V$ implies $f^*U \triangleleft f^*V$.

Metric maps and uniform maps are in particular compatible with $\triangleleft$ because if $f$ is uniform and if $\pi_1^*U \wedge \Delta_\epsilon \leqslant \pi_2^*(V)$ then, letting $\eta$ such that

$$\Delta_\eta \leqslant (f \times f)^* \Delta_\epsilon$$

as we have

$$(f \times f)^*(\pi_1^*(U) \wedge \Delta_\epsilon) \leqslant (f \times f)^* \pi_2^* V$$

we obtain

$$\pi_1^*(f^*U) \wedge \Delta_\eta \leqslant \pi_1^*(f^*U)) \wedge (f \times f)^* \Delta_\epsilon \leqslant \pi_2^* f^*V$$

i.e. $f^*U \triangleleft_\eta f^*V$

3.1.11. **Definition :** A map $f : X \to Y$ between two pre-metric locales is called an isometric map if $d(f(x), f(y)) = d(x, y)$, i.e. if $\Delta_q = (f \times f)^*(\Delta_q)$.

We can easily see (by the same kind of argument that 3.1.8) that this is equivalent to the fact that $\delta(\mathcal{L}) = \delta(f_!\mathcal{L})$ for all sublocales of $X$.

**Lemma :** If $f$ is an isometric map $X \to Y$ then for any locally positive sublocale $\mathcal{L}$ of $X$

$$\mathcal{L} \leqslant f^*(B_q f_! \mathcal{L}) \leqslant B_q \mathcal{L}$$

**Proof :**

The first inequality immediately follows from the fact that $f_!\mathcal{L} \leqslant B_q f_!\mathcal{L}$. For the second, as $f_!(\mathcal{L})$ is locally positive (because of 2.3.12) one can write that

$$B_q f_! \mathcal{L} = \bigvee_{\substack{v \in \mathcal{O}(Y) < q \\ v \wedge f_!(\mathcal{L}) > \emptyset}} v.$$

By 2.3.11, $v \wedge f_!(\mathcal{L})$ is positive if and only if $f^*(v) \wedge \mathcal{L}$ is. Also, as $f$ is isometric, for any $v \in \mathcal{O}(Y)^{<q}$, one has $f^*(v) \in \mathcal{O}(X)^{<q}$. Finally

$$f^*(B_q f_! \mathcal{L}) = \bigvee_{\substack{v \in \mathcal{O}(Y) < q \\ f^*(v) \wedge \mathcal{L} > \emptyset}} f^*(v) \leqslant \bigvee_{\substack{w \in \mathcal{O}(X) < q \\ w \wedge \mathcal{L} > \emptyset}} w = B_q \mathcal{L}.$$

$\square$

27