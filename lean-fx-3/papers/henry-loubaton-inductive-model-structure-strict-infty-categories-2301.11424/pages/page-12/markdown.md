## 2.2 Marked $\infty$-Categories

For the rest of the article, we fix an $m \in \mathbb{N} \cup \{\infty\}$.

**2.15 Definition.** An $m$-marked $\infty$-category is an $\infty$-category $X$, together with a set $M \subset \prod_{k>0} X(k)$ of arrows of positive dimension called *marked* arrows such that:

- All identity arrows $\mathbb{I}_x$ are marked.
- All arrows of dimension strictly greater than $m$ are marked.
- If $x$ and $y$ are marked $n$-arrows and $x\#_k y$ is defined, then $x\#_k y$ is marked.

A morphism of $m$-marked $\infty$-categories is a morphism between the underlying $\infty$-categories that sends marked arrows to marked arrows. The category of $m$-marked $\infty$-categories is denoted $\infty$-Cat$^{+m}$.

Note that if $m = \infty$, then the second condition of the definition simply disappears; this is the main case we are interested in.

**2.16 Example.** If $X$ is an $\infty$-category, we denote by $X^\#$ the $m$-marked $\infty$-category $(X, X_{>0})$ where all arrows of positive dimension are marked. We denote by $X^\flat$ the $m$-marked $\infty$-category where only identity arrows and $k$-arrows for $k > m$ are marked.

**2.17 Notation.** To simplify notation and when there is no confusion, the marked $\infty$-category $X^\flat$ will simply be denoted as $X$.

**2.18 Construction.** If $X$ is an $\infty$-category and $M \subset \prod_{k>0} X_k$ is a set of arrows of $X$, we denote by $\overline{M}$ the smallest set of arrows such that $M \subset \overline{M}$ and $(X, \overline{M})$ is an $m$-marked $\infty$-category. That is, $\overline{M}$ is the union of the set of arrows of dimension strictly greater than $m$ and the set of all $n$-arrows that can be written as iterated composites of $n$-arrows in $M$ and arrows of the form $\mathbb{I}_x$ for $x$ an $(n-1)$-arrow. For example, $X^\flat = (X, \emptyset)$.

**2.19 Construction.** The category of $m$-marked $\infty$-categories has all colimits, and they are easily described in terms of colimits of $\infty$-categories and of Construction 2.18: if $(X_i, M_i)_{i \in I}$ is a diagram of $m$-marked $\infty$-categories indexed by a category $I$, then:

$$\operatorname{Colim}_{i \in I}(X_i, M_i) = \left( \operatorname{Colim}_{i \in I} X_i, \overline{\cup_i f_i(M_i)} \right)$$

where $f_i$ denotes the canonical map $f_i: X_i \rightarrow \operatorname{Colim}_{i \in I} X_i$ and $f_i(M_i)$ is simply the set of arrows of the form $f_i(x)$ for $x \in M_i$.

This is easily shown by checking that the right-hand side has the universal property of the colimit.

**2.20 Remark.** Theorem 1.12 of [10] identifies a small full subcategory of $\infty$-Cat, denoted $\Theta$, which is dense. We denote by $\Theta^{+m}$ the full subcategory of $\infty$-Cat$^{+m}$ whose objects are of the form $(C, M)$ with $C$ in $\Theta$. From the description of colimits of $m$-marked $\infty$-categories given in Construction 2.19, it follows that $\Theta^{+m}$ is dense in $\infty$-Cat$^{+m}$. Moreover, as objects of $\Theta^{+m}$ have a finite number of non trivial cells, they are $\omega$-small. It follows that $\infty$-Cat$^{+m}$ is locally finitely presentable.

12