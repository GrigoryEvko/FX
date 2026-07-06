(MM6)

$$(U, V) \wedge (U, V') \vdash \delta(V \vee V') \leqslant \delta(U) + \delta(V) + \delta(V').$$

### 3.5.2. The main result of this section is

**Theorem :** *The locale $[X_A, Y_B]_1$ we just constructed does not depend on $A$ and $B$ and classifies metric maps between $X$ and $\tilde{Y}$. With the propositions $(U, V)$ corresponding to $U \wedge f^*(V^\sim) > \emptyset$. This locale will be denoted $[X, Y]_1$*

Its proof will occupy us for the rest of this subsection.

3.5.3. If $f$ is a geometric morphism from $\mathcal{E}$ to $\mathcal{T}$, then, by the same argument as in 3.3.6:

$$f^\#([X_A, Y_B]_1) \simeq [f^\#(X)_{f^*(A)}, f^\#(Y)_{f^*(B')}]_1$$

So it suffices to show that the points of $[X_A, Y_B]_1$ correspond to metric functions from $X$ to $\tilde{Y}$ to obtain the announced result.

3.5.4. **Proposition :** *Let $f : X \rightarrow \tilde{Y}$ be a metric map and let:*

$$(U, V)_f := \text{“}U \wedge f^*(V^\sim) > \emptyset\text{”}$$

*For $U \in A$ and $V \in B$. Then this defines a point of $[X_A, Y_B]_1$.*

#### Proof :

Axiom (MM1) is immediate. (MM2) holds because for any $V \in B, U \in A$, if $f^*(V^\sim) \wedge U$ is positive then one can write $U$ as a union of $u \in A$ such that $u \leqslant U$ and $\delta(u) < q$ and the locale positivity of $X$ allows one to conclude. Axiom (MM3) and (MM4) hold because the corresponding unions holds in $\tilde{Y}$.

We now prove axiom (MM5). Let $W_1, W_2, \tau, q_1, q_2, V_1, V_1', 2_2, V_2'$ satisfying the hypothesis of (MM5). We also assume that $(W_1, V_1')_f$ and $(W_2, V_2')_f$ holds. Then as $f$ is metric and $V_i' \triangleleft_{q_i} V_i$ then $V_i'^\sim \triangleleft_{q_i} V_i^\sim$ one has

$$f^*(V_i'^\sim) \triangleleft_{q_i} f^*(V_i^\sim).$$

As $\delta(W_i) < q_i$ and $W_i \wedge f^*(V_i) > \emptyset$ this implies that

$$W_i \subseteq f^*(V_i^\sim),$$

and hence, as $\tau \leqslant W_1 \wedge W_2$, that

$$\tau \subseteq f^*(V_1^\sim \wedge V_2^\sim).$$

44