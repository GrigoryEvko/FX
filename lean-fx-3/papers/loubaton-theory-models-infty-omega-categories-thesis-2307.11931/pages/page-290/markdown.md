CHAPTER 5. THE \((\infty,1)\)-CATEGORY OF MARKED \((\infty,\omega)\)-CATEGORIES

We then have to show that for any integer $n$, any diagram of shape

$$\begin{array}{c} \lambda \mathbf {D} _ {n} \otimes \{0 \} \cup \lambda \partial \mathbf {D} _ {n} \otimes [ 1 ] \xrightarrow {g} 1 \stackrel {{\circ}} {{\star}} \lambda C \\ \Big \downarrow \qquad \qquad \qquad \qquad \qquad \qquad \qquad \Big \downarrow \\ \lambda \mathbf {D} _ {n} \otimes [ 1 ] \xrightarrow [ f ]{} \Sigma \lambda C \end{array}$$

with $f(e_n \otimes [1])$ and $f(e_k^\alpha \otimes [1])$ for $\alpha \in \{-, +\}$ and $k < n$ corresponding to a marked cell, admits a unique lifting $l$ with the following extra condition: if $n > 0$, if $f(e_n \otimes [1])$ is null and if $g(e_n \otimes \{0\})$ corresponds to a marked cell, then $l(e_n \otimes [1])$ is null and $l(e_n \otimes \{1\})$ corresponds to a marked cell.

Suppose first that $n = 0$. We set $l_0: \lambda(\mathbf{D}_0 \otimes [1])_0 \to (1 \stackrel{\circ}{\star} \lambda C)_0$ as the unique group morphism extending $g_0$ and such that

$$l _ {0} (e _ {0} \otimes \{1 \}) := \partial s _ {1} (f _ {1} (e _ {0} \otimes [ 1 ]) + g _ {0} (e _ {0} \otimes \{1 \}).$$

We also define $l_1: \lambda(\mathbf{D}_0 \otimes [1])_1 \to (1 \stackrel{\circ}{\star} \lambda C)_1$ as the group morphism characterized by:

$$l _ {1} (e _ {0} \otimes [ 1 ]) := s _ {1} (f _ {1} (e _ {0} \otimes [ 1 ])).$$

For $k > 1$, we set $l_k: \lambda(\mathbf{D}_0 \otimes [1])_k \to (1 \stackrel{\circ}{\star} \lambda C)_k$ as the constant morphism on 0. We directly deduce the equality $\partial l = l\partial$. We then have defined the desired lifting, which is obviously the unique one possible.

Suppose now that $n > 0$. We set $l_k := g_k: \lambda(\mathbf{D}_n \otimes [1])_k \to (1 \stackrel{\circ}{\star} \lambda C)_k$ for $k < n$ and $l_n: \lambda(\mathbf{D}_n \otimes [1])_n \to (1 \stackrel{\circ}{\star} \lambda C)_n$ as the unique group morphism extending $g_n$ and such that

$$l _ {n} (e _ {n} \otimes \{1 \}) := (- 1) ^ {\alpha} \partial s _ {n + 1} (f (e _ {n} \otimes [ 1 ])) - (- 1) ^ {\alpha} s _ {n} (f ((\partial e _ {n}) \otimes [ 1 ])) + g _ {n} (e _ {n} \otimes \{0 \})$$

where $\alpha$ is $+$ if $n$ is even and $-$ if not. We define $l_{n+1}: \lambda(\mathbf{D}_n \otimes [1])_{n+1} \to (1 \stackrel{\circ}{\star} \lambda C)_{n+1}$ as the group morphism characterized by:

$$l _ {n + 1} (e _ {n} \otimes [ 1 ]) := s _ {n + 1} (f _ {n + 1} (e _ {n} \otimes [ 1 ])).$$

Eventually, for $k > n$, we set $l_k: \lambda(\mathbf{D}_n \otimes [1])_k \to (1 \stackrel{\circ}{\star} \lambda C)_k$ as the constant morphism on 0.

For an integer $k < n$ and $\alpha \in \{-, +\}$, as the $(k + 1)$-cell corresponding to $g_{k + 1}(e_k^\alpha \otimes [1])$ is marked, we have an equality

$$g _ {k + 1} (e _ {k} ^ {\alpha} \otimes [ 1 ]) = s _ {k + 1} f _ {k + 1} (e _ {k} ^ {\alpha} \otimes [ 1 ]).$$

This then implies the equalities

$$\partial (l _ {n + 1} (e _ {n} \otimes [ 1 ])) = l _ {n + 1} (\partial (e _ {n} \otimes [ 1 ]))$$

$$\partial (l _ {n} (e _ {n} \otimes \{1 \})) = g _ {n - 1} (\partial e _ {n} \otimes \{1 \})$$

280