### 3.5 The locale $[X, Y]_1$ of metric maps

In this subsection we show that it is possible to construct a classifying space $[X, Y]_1$ of metric maps between two metric locales $X$ and $Y$, at least when $Y$ is complete. The key observation underlying this construction is that (in a classical settings) on the set of metric functions the topology of point-wise convergence on any dense subsets is equivalent to the compact-open topology, and that when we endow this set of metric functions with this topology the composition law is bi-continuous. This suggests that this topology classifies metric functions. The general idea of this section is to give a point-free formulation of this topology, by replacing the basic open “$f(x) \in V$” by “$U \wedge f^{-1}(V) > \emptyset$” for $U$ a small neighborhood of $x$.

#### 3.5.1. Definition :

Let $X$ and $Y$ be two pre-metric locales. Let $A$ be a basis$^9$ of positive open of $X$ and $B$ be a metric basis of $Y$. We define $[X_A, Y_B]_1$ as the classifying space of the propositional geometric theory on propositions $(U, V)$ for $U \in A$ and $V \in B$ with the axioms:

(MM1) For all $U' \leqslant U$ and $V' \leqslant V$

$$(U', V') \vdash (U, V)$$

(MM2) For all $V \in B, U \in A$ and any positive rational number $q$ one has

$$(U, V) \vdash \bigvee_{\substack{u \leqslant U \\ \delta(u) < q}} (u, V);$$

(MM3) For all $U \in A$ and all $q$ positive:

$$\vdash \bigvee_{\substack{V \in B \\ \delta(V) < q}} (U, V);$$

(MM4) For all $U \in A, V \in B$

$$(U, V) \vdash \bigvee_{\substack{V' \in B \\ V' < V}} (U, V');$$

(MM5) Let $W_1, W_2, \tau \in A, q_1, q_2 \in \mathbb{Q}, V_1, V_2, V_1', V_2' \in B$ such that

$$\begin{array}{l} \delta(W_1) < q_1 \quad \delta(W_2) < q_2 \\ V_1' \triangleleft_{q_1} V_1 \quad V_2' \triangleleft_{q_2} V_2 \\ \tau \leqslant W_1 \quad \tau \leqslant W_2 \end{array}$$

then

$$(W_1, V_1') \wedge (W_2, V_2') \vdash \bigvee_{\substack{V \in B \\ V \leqslant V_1 \wedge V_2}} (\tau, V)$$

$^9$One can actually see that we do not even need $A$ to be a basis. All we need is that for all positive rational $q$ the set of $a \in A$ such that $\delta(a) < q$ cover $X$.

43