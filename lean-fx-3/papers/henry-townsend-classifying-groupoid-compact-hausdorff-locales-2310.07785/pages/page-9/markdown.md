functor $f : [n] \to [m]$ induces a geometric morphism $\mathbb{S}_n \to \mathbb{S}_m$ whose inverse image functor $f^* : \mathbf{Set}^{[m]} \to \mathbf{Set}^{[n]}$ is composition with $f$. For any locale $X$, we have a groupoid:

$$\operatorname{Prin}_{\mathbb{G}}^{\Delta}(X)([n]) := \operatorname{Prin}_{\mathbb{G}}(\mathbb{S}_n \times X).$$

As this is natural in $[n]$, we have define a simplicial groupoid $\operatorname{Prin}_{\mathbb{G}}^{\Delta}(X)$; that is, a functor from $\Delta^{op}$ to the category of groupoids.

**Definition 5.2** *For a category $\mathcal{C}$, we define a simplicial groupoid $N^{gpd}(\mathcal{C})$, such that $N^{gpd}(\mathcal{C})([n])$ is the groupoid of functors $[n] \to \mathcal{C}$ with natural isomorphisms between them.*

The following is a well known result for $\infty$-categories which immediately reduces to a theorem about ordinary categories (and for which it is possible to give a direct proof without going through the theory of $\infty$-categories):

**Proposition 5.3** *$N^{gpd}$ is a fully faithful functor from the 2-category of categories, functors and natural isomorphisms, to the 2-category of simplicial groupoids, pseudo-natural transformations and pseudo-natural modifications.*

**Remark 5.4** *While we will not need it, the essential image of $N^{gpd}$ can be characterized explicitly as those simplicial groupoids $X : \Delta^{op} \to \mathfrak{GPD}$ that satisfy the following three conditions:*

- $X$ satisfies the Segal condition; that is, for each $n > 1$, is the map

$$X([n]) \to X([1]) \times_{X([0])} X([1]) \times_{X([0])} \cdots \times_{X([0])} X_1$$

induced by the maps $[1] \simeq \{i, i+1\} \to [n]$ is an equivalence of groupoids (where the pullbacks are pseudo-pullbacks).

- $X$ satisfies the Rezk (or completeness) condition. That is, if we define $X^{iso} \subset X([1])$ the full subgroupoid of the $x \in X([1])$ that “admit an inverse” in the sense that there is an element $y \in X([2])$, such that the image of $y$ under $[1] \simeq \{0, 1\} \subset [2]$ is (isomorphic to) $x$ and the image of $y$ under $[1] \simeq \{0, 2\} \subset [2]$ is (isomorphic to) a degenerate object (an object in the image of $X([0]) \to X([1])$). Then the natural map $X([0]) \to X^{iso}$ induced by $X([0]) \to X([1])$ is an equivalence of groupoids.
- The functor $X([n]) \to X([0])^{n+1}$ induced by all the maps $[0] \to [n]$ is fully faithful.

Indeed the first two conditions essentially correspond to the definition of complete Segal spaces (or Rezk spaces) which (when used in the setting of $\infty$-categories and $\infty$-groupoids) are a way to define $(\infty, 1)$-categories. The last condition is important to make sure that the object we get is really a 1-category and not some special $(\infty, 1)$-category.

9