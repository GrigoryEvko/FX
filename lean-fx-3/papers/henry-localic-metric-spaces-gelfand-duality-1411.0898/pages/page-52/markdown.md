5. From the previous result, $B_q\{0\}$ identifies with $p_!(\{0\} \times B_q0)$ but $p$ acts on $\{0\} \times B_q0$ as the inclusion of $B_q0$ in $\mathcal{H}$ (this is the definition of 0 being the neutral element), hence $p_!(\{0\} \times B_q0) = B_q0$ and this concludes the proof.

□

4.1.3. **Proposition :** *Let $\mathcal{H}$ be a pre-Banach locale, the following conditions are equivalent:*

*(LB1) The open sublocales $B_q0$ form a basis of neighborhoods of 0.*

*(LB2) $\mathcal{H}$ is metric for the distance induced by $\|.\|$.*

A pre-Banach locale satisfying either *(LB1)* or *(LB2)* is called a Banach locale, we will soon see that there is no need for a completeness assumption: it will be automatic.

**Proof :**

We will use the same notation $s, p$ as in proposition 4.1.2. Assume *(LB1)*, and let $U$ be any open of $\mathcal{H}$. Consider the open sublocale $p^*U \subset \mathcal{H} \times \mathcal{H}$, and decompose it as a union of basic open sublocales

$$p^*U = \bigvee_{i \in I} A_i \times B_i$$

where $A_i$ and $B_i$ are open sublocales of $\mathcal{H}$. Let $i$ such that $(A_i \times B_i) \wedge U \times \{0\}$ is positive. Then $B_i \wedge \{0\}$ is also positive, hence $0 \in B_i$, and from the hypothesis, there exists $q$ such that $B_q0 \leqslant B_i$. This implies that for each $i$ such that $0 \in B_i$, as $A_i \times B_q0 \leqslant p^*U$ one has $B_qA_i = p_!(A_i \times B_q0) \leqslant U$ hence $A_i \triangleleft_q U$.

Now as $U \times \{0\}$ is locally positive and a subset of $p^*(U)$:

$$U \times \{0\} \leqslant \bigvee_{\substack{i \in I \\ (A_i \times B_i) \wedge (U \times \{0\}) > \emptyset}} \leqslant \bigvee_{\substack{i \in I \\ 0 \in B_i}} A_i \times B_i$$

Applying $\pi_1$ one gets (as any $B_i$ having a point is positive) that

$$U \leqslant \bigvee_{\substack{i \in I \\ 0 \in B_i}} A_i \leqslant \bigvee_{\substack{i \in I \\ A_i \triangleleft U}} A_i,$$

which concludes the proof of the first implication.

Assume now *(LB2)*, let $U$ be an arbitrary neighborhood of 0, then as $\mathcal{H}$ is metric, there exists an open sublocale $V$ such that $0 \in V$ and $V \triangleleft U$. In particular, there exists $q$ such that $B_qV \leqslant U$, and as $0 \in V$ one has:

$$B_q0 \subset B_qV \subset U$$

which proves *(LB1)* and concludes the proof of the proposition.

□

52