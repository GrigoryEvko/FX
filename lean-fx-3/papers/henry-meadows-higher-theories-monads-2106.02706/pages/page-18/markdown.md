**Construction 3.11.** Let $\mathcal{C}$ and $\mathcal{D}$ be two $\infty$-categories. In [16], Lurie construct an action of $\operatorname{End}(\mathcal{C})$ on $\operatorname{Fun}(\mathcal{D}, \mathcal{C})$ by looking at the strict action of the simplicial monoid $\operatorname{End}(\mathcal{C})$ on the simplicial set $\operatorname{Fun}(\mathcal{D}, \mathcal{C})$.

This is however equivalent to the construction we discussed above by combining the action of $\operatorname{Fun}(\mathcal{D}, \operatorname{End}(\mathcal{C}))$ on $\operatorname{Fun}(\mathcal{D}, \mathcal{D})$ obtained from Lemma 3.7 and the monoidal functor $\operatorname{End}(\mathcal{C}) \rightarrow \operatorname{Fun}(\mathcal{D}, \operatorname{End}(\mathcal{C}))$ from Lemma 3.9.

Indeed, we start from the strict action of $\operatorname{End}(\mathcal{C})$ on $\mathcal{C}$, which can be encoded by a functor $\Delta^{op} \times \Delta^1 \rightarrow \operatorname{Set}_{\Delta}$ as discussed in Remark 3.4, and our construction in Lemma 3.7 using $F_K$ is known (by Proposition 2.7) to be equivalent to post-composing this functor by $\operatorname{Fun}(K, -)$. But this is precisely the strict action considered in the first paragraph.

From the discussion of 3.10 and 3.8 above we obtain

**Lemma 3.12.** *The natural functor*

$$\operatorname{Fun}(K, \mathcal{C})^T \rightarrow \operatorname{Fun}(K, \mathcal{C}^T)$$

*is an equivalence of $\infty$-categories, compatible to the forgetful functor to $\operatorname{Fun}(K, \mathcal{C})$.*

The final ingredient to Lurie's theory of monads is the notion of *endomorphism object*. Given a monoidal $\infty$-category $\mathcal{C}$ acting on an $\infty$-category $\mathcal{X}$ and $X \in \mathcal{X}$ any object, Lurie considers the $\infty$-category $\mathcal{C}[X]$ which can informally be described as the $\infty$-category of object $Y \in \mathcal{C}$ endowed with a map $Y \otimes X \rightarrow X$ in $\mathcal{X}$ (see Definition 4.7.1.1 in [16] for a more formal statement).

**Definition 3.13.** Let $\mathcal{C}$ be a monoidal $\infty$-category and $\mathcal{X}$ an $\infty$-category with an action of $\mathcal{C}$. An *endomorphism object* for an object $X \in \mathcal{X}$ is (if it exists) a terminal object in the category $\mathcal{C}[X]$.

As usual, we will, in an abuse of language, say that an object $\operatorname{End}(X) \in \mathcal{C}$ is an endomorphisms object of $X$ if it is the image of a terminal object in $\mathcal{C}[X]$ by the forgetful functor $\mathcal{C}[X] \rightarrow \mathcal{C}$. Lurie also shows in [16, Remark 4.7.1.33 and Proposition 4.7.1.34] that:

**Proposition 3.14.** *In the situation above, the $\infty$-category $\mathcal{C}[X]$ admits a monoidal structure for which the forgetful functor $\mathcal{C}[X] \rightarrow \mathcal{C}$ is monoidal.*

18