But, still by the previous point, an open sublocale $v$ of $X$ satisfies $v \wedge B_{q'}\mathcal{L} > \emptyset$ if and only if there exists $v' \in \mathcal{O}(X)^{<q'}$ such that $v' \wedge \mathcal{L} > \emptyset$ and $v \wedge v' > \emptyset$. For any open sublocale of this sort, one has $\delta(v \vee v') < q + q'$ by point 6. Hence $v \vee v'$ is a positive open sublocale such that $\delta(v \vee v') < q + q'$ and $(v \vee v') \wedge \mathcal{L} > \emptyset$. In particular $v \leqslant v \vee v' \leqslant B_{q+q'}\mathcal{L}$.

This proves that $B_q(B_{q'}\mathcal{L}) \leqslant B_{q+q'}\mathcal{L}$.

12. From point 10 one has

$$B_q\mathcal{L} = \bigvee_{\substack{v \in \mathcal{O}(X) < q \\ v \wedge \mathcal{L} > \emptyset}} v.$$

Hence from point 5 one has

$$\delta(B_q\mathcal{L}) = \sup_{\substack{v, v' \in \mathcal{O}(X) < q \\ v \wedge \mathcal{L}, v' \wedge \mathcal{L} > \emptyset}} \delta(v \vee v').$$

But for any two such $v, v'$ one has by point 7: $\delta(v \vee v') \leqslant \delta(v \vee v' \vee \mathcal{L}) \leqslant \delta(\mathcal{L}) + \delta(v) + \delta(v') \leqslant \delta(\mathcal{L}) + 2q$. One obtains the result by taking the supremum.

3.1.5. Usually, the distance function $d: X \times X \to \overleftarrow{\mathbb{R}_+^\infty}$ is expected to be in fact a continuous map from $X \times X$ to $\mathbb{R}$, and not only a semi-continuous map as our definition of distance suggest it. The reason for our choice is that we know (see for example [5]) that the norm on a Banach space has to take value in $\overleftarrow{\mathbb{R}_+^\infty}$, even if we want to think of it as a function which is continuous$^8$. Classically, the continuity is a consequence of the triangular inequality, and the following proposition gives a constructive interpretation of this result, restoring a form of "fiberwise continuity" of $d$.

Proposition: Let $\overline{\Delta_q}$ be the fiberwise closure of $\Delta_q$ in $X \times X$. Then for all $q < q'$ one has $\overline{\Delta_q} \subseteq \Delta_{q'}$.

Proof:

Let $q'$ be a rational such that $q < q'$ and let $\epsilon = \frac{q' - q}{2}$. As $\Delta_q$ is by definition fiberwise dense in $\overline{\Delta_q}$, Proposition 2.3.11 implies that $\overline{\Delta_q}$ is locally positive, and in particular one can write that

$$\overline{\Delta_q} \leqslant \bigvee_{\substack{v, v' \in \mathcal{O}(X) < \epsilon \\ v \times v' \wedge \overline{\Delta_q} > \emptyset}} v \times v'.$$

But, still by 2.3.11 and by fiberwise density of $\Delta_q$ in $\overline{\Delta_q}$, for any two such $v, v'$ one has $v \times v' \wedge \Delta_q > \emptyset$ and hence there exists $U$ such that $\delta(U) < q$ and $(v \times v') \wedge (U \times U)$ is positive. This implies that $v \wedge U$ and $v' \wedge U$ are positive and hence, by point 7 of 3.1.4, that $\delta(v \vee v') \leqslant \delta(v) + \delta(v') + \Delta(U) < q + 2\epsilon = q'$.

$^8$as opposed to semi-continuous.

23