**3.17 Definition.** Let $a$ be an $(n+1)$-arrow in a $m$-marked $\infty$-category $C$. An *inverse* for $a$ is an arrow $a^{-1}$ such that there exist two marked arrows:

$$\epsilon: a\#_n a^{-1} \rightarrow \mathbb{I} \quad \nu: a^{-1}\#_n a \rightarrow \mathbb{I}.$$

An arrow is *invertible* if it has an inverse.

**3.18 Definition.** An $m$-marked $\infty$-category $C$ is *prefibrant* if

(1) marked arrows of $C$ are invertible and their inverses are marked,
(2) whenever $a$ and $c: a \rightarrow b$ are marked in $C$, so is $b$.

This directly implies that if $b$ and $c: a \rightarrow b$ are marked, so is $b$.

This notion is purely temporary: we will show in Proposition 3.25 that an object is fibrant for the left semi-model structure of Theorem 2.43 if and only if it is prefibrant.

**3.19 Proposition.** Let $0 < k \leq n$ be two integers. If $C$ is *prefibrant*, then equations $\mathbf{eq}_{k,n}^{\circ \circ \circ}$ and $\mathbf{eq}_{k,n}^{\circ \circ \circ}$ have weakly unique solutions in $C$.

*Proof.* We show the result by decreasing induction on $k \leq n$. The initialization corresponds to $k = n$. In this case, the data of a morphism $\mathbf{A}\mathbf{E}\mathbf{q}_{n,n}^{\circ \circ \circ} \rightarrow C$ corresponds to two $n$-arrows $a$ and $b$ sharing the same source and such that $a$ is marked. Let $\nu: a^{-1}\#_n a \rightarrow \mathbb{I}$. If we define $x: = a^{-1}\#_n b$ and $y: \psi\#_n b: a\#_n x \rightarrow b$, the couple $(x, y)$ is a solution of $\mathbf{eq}_{n,n}^{\circ \circ}$. If $b$ is marked, so is $x$. We now show the weak uniqueness of the solution. Let $(\bar{x}, \bar{y})$ be another solution. We then have a marked arrow:

$$z: \bar{x} \xrightarrow{\nu^{-1}} a^{-1}\#_n a\#_n \bar{x} \xrightarrow{\bar{y}} a^{-1}\#_n b.$$

The assertion for $\mathbf{eq}_{n,n}^{\circ \circ \circ}$ is similar.

Suppose now the result is true for $k+1$. We start by showing that solutions of $\mathbf{eq}_{k,n}^{\circ \circ}$ and $\mathbf{eq}_{k,n}^{\circ \circ \circ}$ are weakly unique in $C$. The data of a morphism $\mathbf{A}\mathbf{E}\mathbf{q}_{k,n}^{\circ \circ} \rightarrow C$ corresponds to an $n$-arrow $x: s \rightarrow t$, a $k$-invertible arrow $a$ such that $\pi_k^+ a = \pi_k^- x$, and an arrow $b: a\#_{k-1} s \rightarrow a\#_k t$. Let $(x, y: a\#_{k-1} x \rightarrow b)$ be a solution of this equation. Let $\nu: a^{-1}\#_{k-1} a \rightarrow \mathbb{I}_{\pi_k^+ a}$ be a marked $(k+1)$-arrow. We recall that the interchange rule implies that

$$\begin{aligned} (\nu\#_{k-1} s)\#_k x &= (\nu\#_{k-1} \mathbb{I}_s) \#_k (\mathbb{I}_{\pi_k^+ a} \#_k x) \\ &= (\nu\#_k \mathbb{I}_{\pi_k^+ a}) \#_{k-1} (\mathbb{I}_s \#_k x) \\ &= \nu\#_{k-1} x \\ &= (\mathbb{I}_{a^{-1}\#_{k-1} a} \#_k \nu) \#_{k-1} (x \#_k \mathbb{I}_t) \\ &= (\mathbb{I}_{a^{-1}\#_{k-1} a} \#_k - 1) \#_k (\mathbb{I}_t \#_k - 1) \nu) \\ &= (a^{-1}\#_{k-1} a\#_{k-1} x) \#_k (\nu\#_{k-1} t) \end{aligned}$$

The arrow $x$ is then also a solution of $\mathbf{eq}_{k+1,n}^{\circ \circ}$:

$$(\nu\#_{k-1} s)\#_k x = (a^{-1}\#_{k-1} a\#_{k-1} x) \#_k (\nu\#_{k-1} t)^{\frac{(a^{-1}\#_{k-1} y)\#_k (\nu\#_{k-1} t)}{2}} (a^{-1}\#_{k-1} b) \#_k (\nu\#_{k-1} t)$$

27