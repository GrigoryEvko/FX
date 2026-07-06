3.1.8. Proposition : Let $f : X \to Y$ be a map between two pre-metric locales. Then the following conditions are equivalent:

- (a) For any positive rational $q$, $\Delta_q \subseteq (f \times f)^*(\Delta_q)$
- (b) For any locally positive sublocale $\mathcal{L}$ of $X$, $\delta(f_!\mathcal{L}) \leqslant \delta(\mathcal{L})$.
- (c) For any $U \in \mathcal{O}(X)^{<q_1}$, $v_1 \in \mathcal{O}(Y)^{<q_2}$, $v_2 \in \mathcal{O}(Y)^{<q_3}$ such that $f^*(v_1) \wedge U$ and $f^*(v_2) \wedge U$ are positive, one has $\delta(v_1 \vee v_2) < q_1 + q_2 + q_3$.
- (d) For any $U \in \mathcal{O}(X)$ and any positive rational $q$:

$$\delta(B_q f_! U) \leqslant \delta(U) + 2q.$$

- (e) For any open sublocale $U$ of $X$ such that $\delta(U) < q$ there exists an open sublocale $V$ of $Y$ such that $\delta(V) < q$ and $U \subseteq f^*(V)$.

A map satisfying these conditions is called a metric map.

Of course, condition (a) is the point free formulation of the usual $d(f(x), f(y)) \leqslant d(x, y)$.

Proof :

- (a) $\Rightarrow$ (b) Let $q$ such that $\delta(\mathcal{L}) < q$, i.e. there exists $q' < q$ such that $\mathcal{L} \times \mathcal{L} \subseteq \Delta_{q'}$. Hence,

$$\mathcal{L} \times \mathcal{L} \subseteq (f \times f)^*(\Delta_{q'})$$

This proves that the image $(f \times f)_!(\mathcal{L} \times \mathcal{L})$ in $X \times X$ is included in $\Delta_{q'}$. Unfortunately, as a product of surjections may fail to be a surjection, it is not enough to conclude directly that $f_!(\mathcal{L}) \times f_!(\mathcal{L}) \subseteq \Delta_{q'}$. But we can still conclude using the fact that as $\mathcal{L}$ and $f_!(\mathcal{L})$ are both locally positive, then by 2.3.14 (applied twice) the map $f : \mathcal{L} \times \mathcal{L} \to f_!(\mathcal{L}) \times f_!(\mathcal{L})$ is always fiberwise dense. This implies that $\Delta_{q'}$ is fiberwise dense in $f_!(\mathcal{L}) \times f_!(\mathcal{L})$, and by 3.1.5 that:

$$f_!(\mathcal{L}) \times f_!(\mathcal{L}) \subseteq \overline{\Delta_{q'}} \subseteq \Delta_q$$

which concludes the proof.

- (b) $\Rightarrow$ (c) by 2.3.12 $\mathcal{L} = f_!(U)$ is locally positive because $U$ is and $f : U \to f_!(U)$ is a surjection. Also, $\delta(f_!(U)) < q_1$ by (b). Hence one obtains (c) by applying point 7 of 3.1.4 (with n=2), together with the fact that $f^*v \wedge U > \emptyset$ is equivalent to $v \wedge f_!U > \emptyset$ because $f : U \to f_!U$ is a surjection and hence in particular a fiberwise dense map.

- (c) $\Rightarrow$ (d) One has

$$B_q f_! U = \bigvee_{\substack{v \in \mathcal{O}(Y)^{<q} \\ f^*(v) \wedge U > \emptyset}} v$$

The same argument as given for point 12 of 3.1.4 allow one to conclude.

25