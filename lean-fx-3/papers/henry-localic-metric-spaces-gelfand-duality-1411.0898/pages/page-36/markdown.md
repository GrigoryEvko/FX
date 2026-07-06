$$\tau^r(U) = \bigvee_{\substack{V \in B \\ V \triangleleft U}} \tau(V)$$

# **Proof :**

A morphism from $Y$ to $\tilde{X}$ is the data of a regular Cauchy filter on $X$ in the internal logic of $Y$. i.e. for each $U \in B$ one should have a proposition $\tau(U) := \text{“}U \in \mathcal{F}$” satisfying (internally) the axiom $(CF1 - 5)$. The four properties given for $\tau$ corresponds exactly to the externalisation of the four axioms $(CF1 - 4)$ (in the right order).

If $\tau$ only satisfies the first three properties then it is just a $B$-Cauchy filter on $X$ and in this case one can apply 3.3.3 and there is a unique regular $B$-Cauchy filter $\tau^r \leqslant \tau$ and it is indeed given by

$$\tau^r(U) = \bigvee_{\substack{V \in B \\ V \triangleleft U}} \tau(V)$$

which is the direct translation of $U \in \tau^r$ if there exists $V \triangleleft U$ with $V \in \tau$.  
□

Of course, the inequalities in the axioms 2. and 4. are in fact equalities because the axiom 1. implies the reverse inequalities.

# **3.3.8. Proposition :** *There is a map $i$ from $X$ to $\tilde{X}$ defined by*

$$i^*(U^\sim) = \bigvee_{V \triangleleft U} V.$$

*Moreover, for any $U \in \mathcal{O}(X)$,*

$$i^*(U) = U^\sim$$

# **Proof :**

The inclusion map $e : \mathcal{O}(X)^+ \rightarrow \mathcal{O}(X)$ clearly satisfies the first three points of 3.3.7. Hence the map

$$e^r(U) = \bigvee_{V \triangleleft U} V$$

satisfies the four points of 3.3.7 and hence there is a map $i : X \rightarrow \tilde{X}$ such that for any $U \in \mathcal{O}(X)^+$ one has $i^*(U^\sim) = e^r(U)$. But as $U^\sim$ is defined as $\bigvee_{\substack{V \leqslant U \\ V > 0}} V^\sim$ this formula immediately extends to an arbitrary $U$.

We still have to prove that $i^*(U) = U^\sim$. As $i^*(U^\sim) \leqslant U$, one has $U^\sim \leqslant i^*(U)$. Let $V$ an arbitrary open sublocale of $X$ such that $V^\sim \leqslant i^*U$ hence,

$$\bigvee_{V' \triangleleft V} V' \leqslant U$$

36