category, then $X^K$ is also an $\infty$-category and we write often write $\text{Fun}(K, X)$, to emphasize that this is the $\infty$-category of functors from $K$ to $X$.

By a *simplicial category*, we mean a simplicially enriched category. Given a simplicial category $\mathcal{C}$, we will write $N(\mathcal{C})$ for its homotopy coherent nerve (see [15, Definition 1.1.5]). It should be noted that in the case we regard an ordinary category as an enriched category with discrete mapping spaces, this recovers the ordinary nerve construction.

Recall that a *natural transformation* of maps of $\infty$-categories $f, g : \mathcal{C} \rightarrow \mathcal{D}$ is just a map $T : \mathcal{C} \times \Delta^1 \rightarrow \mathcal{D}$ so that $T|_{\mathcal{C} \times \{0\}} = f, T|_{\mathcal{C} \times \{1\}} = g$. This is the same as a morphism in the functor $\infty$-category $\text{Fun}(\mathcal{C}, \mathcal{D})$. A natural transformation $T$ is called a *natural isomorphism* if corresponds to an invertible morphism in $\text{Fun}(\mathcal{C}, \mathcal{D})$. We often write $T_x = T|_{\{x\} \times \Delta^1}$ which is an arrow in $f(x) \rightarrow g(x)$ in $\mathcal{D}$, and is called the *component of $T$ at $x$*. We recall that:

**Lemma 2.1.** *Suppose that $T : \mathcal{C} \times \Delta^1 \rightarrow \mathcal{D}$ is a natural transformation. The following are equivalent:*

1. $T$ is a natural isomorphism.
2. For each $x \in \mathcal{C}$, $T_x$ is an equivalence.

*In other words, a natural transformation is a natural isomorphism iff each component is an equivalence.*

*Proof.* This follows from [15, Corollary 5.1.2.3] as an object $y$ is equivalent to an object $x$ in an $\infty$-category $\mathcal{C}$ iff $y$ is a (co)limit of $x : \Delta^0 \rightarrow \mathcal{C}$. $\square$

We denote by $\mathcal{S}$ the $\infty$-category of spaces and by $\text{Pr}(\mathcal{C})$ the $\infty$-category of presheaves of spaces on an $\infty$-category $\mathcal{C}$, that is $\text{Pr}(\mathcal{C}) = \text{Fun}(\mathcal{C}^{op}, \mathcal{S})$. We will write $y_{\mathcal{C}} : \mathcal{C} \rightarrow \text{Pr}(\mathcal{C})$ for the Yoneda embedding.

We refer the reader to [15, Section 5.2.2] for the theory of adjoint functors, as well as related concepts such as counit transformations. In classical category theory, one can verify that functors form an adjoint pair by specifying the unit and counit of the adjunction, and verifying that they satisfy the triangle identities. The $\infty$-categorical counterpart of this statement, which follows, will be used several times throughout the paper:

7