Given an $\mathcal{A}$-pretheory $\mathcal{A} \rightarrow \mathcal{K}$ one defines the category of $\mathcal{K}$-models in $\mathcal{E}$ as objects $X \in \mathcal{E}$ whose restricted Yoneda embeddings in $\Pr(\mathcal{A})$ have an extension to a presheaf on $\mathcal{K}$. That is, it can be expressed as a pullback square:

$$\begin{array}{ccc} \text{Mod}_{\mathcal{E}}(\mathcal{K}) & \longrightarrow & \Pr(\mathcal{K}) \\ \downarrow & \downarrow & \downarrow \\ \mathcal{E} & \longrightarrow & \Pr(\mathcal{A}) \end{array}$$

Now, Bourke and Garner show that under the assumption that $\mathcal{E}$ is locally presentable, the functor $\text{Mod}_{\mathcal{E}}(\mathcal{K}) \rightarrow \mathcal{E}$ is a monadic right adjoint. In particular, it gives a monad $\mu^{\mathcal{K}}$ associated to $\mathcal{K}$ which is characterized by the property that $\mu^{\mathcal{K}}$-algebras are the same as $\mathcal{K}$-models.

Finally, they show that these two constructions (from monads to pretheory and pretheory to monads) are adjoint to each other and form an idempotent adjunction, i.e. induces an equivalence of categories between their essential images. The object in the images are respectively called $\mathcal{A}$-theories, and $\mathcal{A}$-Nervous monads, as they are exactly the monads that satisfy the conclusion of the nerve theorem.

In the present paper, we will generalize these results to the $\infty$-categorical context. While Bourke and Garner generalize all this to an enriched setting (where $\mathcal{E}$, $\mathcal{A}$ and $\mathcal{K}$ are all $V$-enriched categories and $M$ is a $V$-enriched monad for $V$ a nice enough monoidal category), we will restrict to the unenriched setting (as presented above) as we feel the theory of enriched $\infty$-categories is not yet developed enough for this.

In Section 7 we also show that the category of monads on an $\infty$-category $\mathcal{C}$ is equivalent (though the construction of the Kleisli category) with the $\infty$-category of essentially surjective left adjoint functors $\mathcal{C} \rightarrow \mathcal{K}$. This result is not directly related to the main goals of the paper, but it follows from the methods developed in the paper and is fairly similar to the construction of the Monad-theory adjunction. This result produce a much simpler description of the $\infty$-category of monads, which is why we decided to include it.

The main kind of application of our results is to deduce several structural theorems about monads, such as the existence of colimits of monads and colimits in the $\infty$-category of algebras for a monad, by looking instead at colimits of theories and colimits in the category of models of a theory. In

3