then for any open $U$, $x \in U$ if and only if $y \in U$, but for points of a locale this implies that $x = y$. The following proof is just the translation of this argument in terms of generalized points.

# **Proof :**

Consider $f : Y \rightarrow \bigwedge_q \Delta_q$ a map, and let $f_1$ and $f_2$ be the two components $Y \rightarrow X$ of $f$. Let $U, V$ be two open sublocales of $X$ such that $U \triangleleft_q V$. Then

$$\pi_1^*(U) \wedge \Delta_q \leqslant \pi_2^*(V).$$

Applying $f^*$ to each side gives

$$f_1^*(U) \wedge f^*(\Delta_q) \leqslant f_2^*(V),$$

and as $f^*(\Delta_q) = Y$ by hypothesis, one has $f_1^*(U) \leqslant f_2^*(V)$.

Finally, writing $V = \bigvee_{U \in V} U$ one has:

$$f_1^*(V) = \bigvee_{U \in V} f_1^*(U) \leqslant f_2^*(V).$$

The converse inequality follows by symmetry and hence $f_1 = f_2$ i.e. $f$ factors into the diagonal embedding, and this concludes the proof. $\square$

In particular, as by 3.1.5,

$$\bigwedge \Delta_q = \bigwedge \overline{\Delta_q}$$

The diagonal embedding of a metric locale is fiberwise closed, one says that metric locales are *fiberwise separated*.

**3.2.2. Proposition :** Let $X$ be a metric locale, and $Y$ a pre-metric locale. Let $f : X \rightarrow Y$ be an isometric map. Then $X$ is a sublocale of $Y$ i.e. $f^*$ is onto. More generally, if we only assume that $X$ is pre-metric then we obtain the inequalities

$$\forall U \in \mathcal{O}(X), \bigvee_{V \in U} V \leqslant f^* f^*(U) \leqslant U$$

The proposition follows from Lemma 3.1.11:

# **Proof :**

Let $U$ be any open sublocale of $X$, such that

$$U = \bigvee_{V \in U} V$$

For any $V \triangleleft_q U$ one has by Lemma 3.1.11

$$V \leqslant f^*(B_q f, V) \leqslant U$$

30