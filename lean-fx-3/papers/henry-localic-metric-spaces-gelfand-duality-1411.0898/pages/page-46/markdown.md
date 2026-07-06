One has by definition:

$$\tau_{p}(V) = \bigvee_{\substack{\delta(W) < q \\ V' \triangleleft_{q} V \\ f^{*}(V'^{\sim}) \wedge W > \emptyset}} W.$$

Hence, as for any $W$ appearing in the supremum one has $W \leqslant f^{*}(V^{\sim})$, we obtain that $\tau_{p}(V) \leqslant f^{*}(V^{\sim})$.

Conversely,

$$f^{*}(V^{\sim}) = \bigvee_{V' \triangleleft_{q} V} f^{*}(V'^{\sim}) = \left( \bigvee_{\substack{V' \triangleleft_{q} V \\ \emptyset < W \leqslant f^{*}(V'^{\sim}) \\ \delta(W) < q}} W \right) \leqslant \tau_{p}(V'^{\sim}).$$

3.5.6. Lemma : Let $p$ be any point of $[X_A, Y_B]_1$, then:

$$p \in (U, V) \Leftrightarrow U \wedge \tau_{p}(V) > \emptyset$$

Proof :

Assume first that $\tau_{p}(V) \wedge U > \emptyset$. Then there exists $W$ and $V'$ such that $\delta(W) < q$, $V' \triangleleft_{q} V$, $(W, V')$ and $W \wedge U > \emptyset$. Applying (MM5), one obtains that there exists $V'' \leqslant V$ such that $p \in (W \wedge U, V'')$ and hence $p \in (U, V)$.

Conversely assume that $p \in (U, V)$, then (by (MM4)) there exists $V' \in B$ and a positive $q$ such that $V' \triangleleft_{q} V$ and $p \in (U, V')$. Also by (MM2) there exists $W \in A$ such that $\delta(W) < q$ and $p \in (W, V')$. But this implies that $W \leqslant \tau_{p}(V)$ and as $W \leqslant U$ and $W > \emptyset$ one concludes that $U \wedge \tau_{p}(V) > \emptyset$. $\square$

3.5.7. At this point, all that remains to be checked in order to prove 3.5.2 is that for any point $p$, $\tau_{p}$ extends into a map from $X \to \widetilde{Y}$ and that this map is indeed metric.

Proposition : The map $\tau_{p}: B \to \mathcal{O}(X)$ satisfies the four conditions of 3.3.7 and in particular there is a (unique) map $f: X \to \widetilde{Y}$ such that $f^{*}(V^{\sim}) = \tau_{p}(V)$.

Proof :

We recall that

$$\tau_{p}(V) := \bigvee_{\substack{\delta(W) < q \\ V' \triangleleft_{q} V \\ p \in (W, V')}} W$$

Also the point $p$ being fixed, we will write $\tau$ instead of $\tau_{p}$ and $(U, V)$ instead of $p \in (U, V)$.

46