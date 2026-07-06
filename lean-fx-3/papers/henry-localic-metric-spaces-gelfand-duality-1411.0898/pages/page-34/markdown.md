Hence regular Cauchy filters correspond to the notion of minimal Cauchy filter, this explains why we will later construct the completion of a locale as the classifying space of regular Cauchy filters, by analogy with the classical construction of the completion of a uniform space as a uniform structure on the set of minimal Cauchy filters (see [3, Chap. II.7]).

**3.3.4. Lemma :** *Let $X$ be a pre-metric locale endowed with a metric basis $B$, and let $\mathcal{F}$ be a regular Cauchy filter on $X$. Then for any $U \in \mathcal{F}$, there exists $V \in B \wedge \mathcal{F}$ such that $V \leqslant U$.*

**Proof :**

Let $U \in \mathcal{F}$, by (CF4) there exists $U' \triangleleft_q U$ such that $U' \in \mathcal{F}$. Also by (CF3) there exists an element $W \in \mathcal{F}$ such that $\delta(W) < (q/3)$ and as $B$ is a basis and $W$ is positive there exists $b \leqslant W$ with $b \in B$. Let $V = B_{q/3}b$, then, by the point 12 of 3.1.4, one has $\delta(V) < q$, also $V \in B$ because $B$ is metric, $W \leqslant V$ because $b \wedge W = b$ is positive and $\delta(W) < q/3$ and hence $V \in \mathcal{F}$. Also by (CF2) there exists $V' \in \mathcal{F}$ such that $V' \leqslant V \wedge U'$, as $V'$ is positive this implies that $V \leqslant B_q U' \leqslant U$. As $V \in B \wedge \mathcal{F}$, this concludes the proof. $\square$

**3.3.5. Corollary :** *The map $\mathcal{F} \to B \wedge \mathcal{F}$ induces a bijection between the set of regular Cauchy filters on $X$ and the set of regular $B$-Cauchy filters on $X$.*

We also mention that, as the following proof will show, this proposition holds for any family $B$ satisfying the conclusion of the previous lemma (3.3.4) even if it is not a metric basis or even if it is not a basis at all.

**Proof :**

Let $\mathcal{F}$ be a regular Cauchy filter on $X$. We will first prove that $\mathcal{F}' = \mathcal{F} \wedge B$ is a regular $B$-Cauchy filter, this is essentially immediate by Lemma 3.3.4:

- If $U \leqslant V$ with $V \in \mathcal{F}'$ and $U \in B$ then $U \in \mathcal{F}$ and hence $U \in \mathcal{F}'$ because $\mathcal{F}$ satisfy (CF1).
- If $U, V \in \mathcal{F}'$ then there exists $W \in \mathcal{F}$ such that $W \leqslant U \wedge V$ and by the lemma there exists $W' \in \mathcal{F}'$ such that $W' \leqslant W \leqslant U, V$.
- There exists $U \in \mathcal{F}$ such that $\delta(U) < q$ and (by the lemma) a $U' \leqslant U$ such that $U' \in \mathcal{F}'$, hence $\delta(U') < q$.
- Let $U \in \mathcal{F}'$, there exists $V \in \mathcal{F}$ such that $V \triangleleft U$, then any $V' \leqslant V$ with $V' \in \mathcal{F}'$ (again given by the lemma) works.

Now $\mathcal{F}$ can be reconstructed from $\mathcal{F}'$ by the lemma together with (CF1) :

$$\mathcal{F} = \{U | \exists U' \in \mathcal{F}', U' \leqslant U\}.$$

And if you take $\mathcal{F}'$ to be any regular $B$-Cauchy filter, then the previous formula defines a $\mathcal{F} \subseteq \mathcal{O}(X)^+$ which is easily checked to be a regular Cauchy filter as well, and by (CF1) $\mathcal{F}' = \mathcal{F} \wedge B$. This concludes the proof. $\square$

34