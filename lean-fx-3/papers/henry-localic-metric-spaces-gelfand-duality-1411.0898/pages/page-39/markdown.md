The uniqueness of the extension follows from the fact that $\tilde{X}$ is metric (3.3.10) and the result of 3.2.3, so we only have to prove the existence. We will use 3.3.7 for this. Let $\tau : \mathcal{O}(X)^+ \rightarrow \mathcal{O}(Y)$ defined by:

$$\tau(U) = i_* f^*(U^\sim)$$

where $i$ denote the embeddings of $S$ into $Y$.

We will first check that $\tau$ satisfies the first three properties of 3.3.7:

1. $i_*, f^*$ and $U \mapsto U^\sim$ are all order preserving. Hence $\tau$ is order preserving.
2. One has $U^\sim \wedge V^\sim = (U \wedge V)^\sim$ (essentially by (CF2)) hence as $i_*$ and $f^*$ also commute to binary intersection one has: $\tau(U) \wedge \tau(V) = \tau(U \wedge V)$. This is not enough to conclude immediately the proof of this point because $U \wedge V$ might fail to be positive. Fortunately, if one assumes that $\tau(W) = i_* f^*(W^\sim)$ is positive, then $i^* i_* f^*(W^\sim)$ is also positive because $i$ is fiberwise dense, which implies that $f^*(W^\sim)$ is positive (because it is bigger than $i^* i_* f^*(W^\sim)$) and hence that $W^\sim$ is positive, which finally implies that $W$ is positive (by 3.3.9 and 3.3.8). Hence one can write that

$$\tau(U) \wedge \tau(V) = \tau(U \wedge V) = \bigvee_{\tau(U \wedge V) > \emptyset} \tau(U \wedge V) \leqslant \bigvee_{U \wedge V > \emptyset} \tau(U \wedge V),$$

which proves points 2.

3. We fix $q$ a positive rational number, and (as $f$ is uniform) $\eta$ such that $\Delta_\eta \leqslant (f \times f)^* \Delta_{q/3}$ (see 3.1.9).

Let $U \in \mathcal{O}(S)^{+, <\eta}$ then (by 3.1.9) there exists $W \in \mathcal{O}(\tilde{X})^{<q/3}$ such that $U \leqslant f^*(W)$.

In particular $W$ is also positive and hence, by (CF3) and the fact that the $V^\sim$ form a basis of $\tilde{X}$, there exists $V_0 \in \mathcal{O}(X)^{+, <q/3}$ such that $V_0^\sim \leqslant W$. We define $V = B_{q/3} V_0$. One has $\delta(V) < q$ (by 3.1.4.12) and $W \leqslant V^\sim$ (by the lemma proved in 3.3.10), in particular $U \leqslant f^*(V^\sim)$. This proves that

$$\bigvee_{U \in \mathcal{O}(S)^{+, <\eta}} i_* U \leqslant \bigvee_{V \in \mathcal{O}(X)^{+, <\eta}} i_* f^*(V^\sim) = \bigvee_{V \in \mathcal{O}(X)^{+, <\eta}} \tau(V), \quad (2)$$

Finally

$$Y = \bigvee_{V \in \mathcal{O}(Y)^{+, <\eta}} V \leqslant \bigvee_{V \in \mathcal{O}(Y)^{+, <\eta}} i_* i^* V = Y.$$

As $i$ is an isometric map, for any $V \in \mathcal{O}(Y)^{<\eta}$ one has $i^* V \in \mathcal{O}(S)^{<\eta}$. Hence

$$Y = \bigvee_{V \in \mathcal{O}(Y)^{+, <\eta}} i_* i^* V \leqslant \bigvee_{U \in \mathcal{O}(S)^{+, <\eta}} i_* U. \quad (3)$$

The inequalities (2) and (3) together conclude the proof of the third point.

39