Theorem 3.22. The only exception to this is Lemma 3.25 that will be used in the proof of Theorem 6.3.

In particular, any theory of monads for which Theorem 3.22 and Lemma 3.25 are valid can be used instead of Lurie's theory of monads. We suspect this should apply for example to Riehl-Verity theory of monads on $\infty$-categories from [18].

## 4 Partial adjoints and functoriality of the Kleisli category

**Definition 4.1.** If $T$ is a monad on an $\infty$-category $\mathcal{C}$, we denote by $\mathcal{C}_T$ the full subcategory of the $\infty$-category $\mathcal{C}^T$ of $T$-algebras on free $T$-algebras. That is, those $T$-algebras in the essential image of the free $T$-algebra functor $\mathcal{C} \rightarrow \mathcal{C}^T$. $\mathcal{C}_T$ is called the *Kleisli category* of $\mathcal{C}$.

As the title suggests, the goal of this section is to study the functoriality properties of the construction $T \mapsto \mathcal{C}_T$. While $T \mapsto \mathcal{C}^T$ has a contravariant functoriality, the Kleisli category has a covariant functoriality essentially given by taking the left adjoint $f_!$ to $f^*$ for $f: T \rightarrow M$ a morphism of monads. However (even in ordinary category theory) the existence of a left adjoint $f_! \dashv f^*$ is in general not guaranteed, and when it exists its construction generally requires a complicated transfinite construction or an application of the special adjoint functor theorem. In particular, given that we have not proven at this point that the $\infty$-category of algebras $\mathcal{C}^T$ has colimits or is a presentable category it would not be reasonable to assume that such a left adjoint exists. Instead we need to consider $f_!$ as a 'partial left adjoint' in the following sense:

**Definition 4.2.** Let $R: \mathcal{C} \rightarrow \mathcal{D}$ be a functor between $\infty$-categories. Let $\mathcal{D}' \subset \mathcal{D}$ be a full subcategory. One says that $R$ has a *partial left adjoint* on $\mathcal{D}'$ if for all $X \in \mathcal{D}'$, the functor:

$$\begin{aligned} \mathcal{C} &\rightarrow \mathcal{S} \\ Y &\mapsto \text{Map}_{\mathcal{D}}(X, R(Y)) \end{aligned}$$

is representable. If $\mathcal{C}' \subset \mathcal{C}$ is a full subcategory of $\mathcal{C}$, one says that $R$ has a partial left adjoint from $\mathcal{D}' \rightarrow \mathcal{C}'$ if for all $X \in \mathcal{D}'$ the object $Y$ as above is in $\mathcal{C}'$. We define *partial right adjoint* in the dual way.

26