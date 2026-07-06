Taking opposite categories on both sides gives us the first natural transformation mentioned in the proposition:

$$\mathcal{X}_d^{op} \rightarrow \text{Fun}(\mathcal{X}^d, \mathcal{S}),$$

which is levelwise given by the restriction of the Yoneda embedding. The second one can be obtained formally from the first ones: informally, a natural transformation $(\mathcal{X}_d)^{op} \rightarrow \text{Fun}(\mathcal{X}^d, \mathcal{S})$ can be seen as a dinatural transformation $(\mathcal{X}_d)^{op} \times \mathcal{X}^d \rightarrow \mathcal{S}$. This, in turn, can be seen as a natural transformation $\mathcal{X}^d \rightarrow \text{Fun}(\mathcal{X}_d^{op}, \mathcal{S})$ which is the second one. To avoid the use of dinatural transformations in this argument (which to the authors' knowledge have not been formalized in the $\infty$-categorical framework), one can use Proposition 5.1 of [8] or Proposition 2.3 of [10]. These assert that for any pairs of functors $F, G : \mathcal{C} \rightarrow \mathcal{D}$ the space of natural transformation from $F$ to $G$ can be described as the end$^{3}$:

$$\text{Map}(F, G) \simeq \int_{c \in \mathcal{C}} \text{Map}(F(c), G(c)).$$

In both cases a natural transformation $\lambda : F \rightarrow G$ corresponds to an element of the end whose component in $\text{Map}(F(c), G(c))$ is simply $\lambda_c : F(c) \rightarrow G(c)$.

Using this (and the functoriality of ends) we have isomorphisms:

$$\begin{aligned} \int_{d \in \mathcal{D}} \text{Fun}(\mathcal{X}_d^{op}, \text{Fun}(\mathcal{X}^d, \mathcal{S})) &\simeq \int_{d \in \mathcal{D}} \text{Fun}(\mathcal{X}_d^{op} \times \mathcal{X}^d, \mathcal{S}) \\ &\simeq \int_{d \in \mathcal{D}} \text{Fun}(\mathcal{X}^d, \text{Fun}(\mathcal{X}_d^{op}, \mathcal{S})). \end{aligned}$$

Through these isomorphisms, we hence obtain a natural transformation $\mathcal{X}^d \rightarrow \text{Fun}(\mathcal{X}_d^{op}, \mathcal{S})$ that for each $d$ is given by the restricted Yoneda embedding.

Applying this to the $\infty$-category of monads, we obtain:

**Corollary 4.10.** *The restricted Yoneda embeddings $\mathcal{C}^T \rightarrow \text{Pr}(\mathcal{C}_T)$ can be equipped with the structure of a natural transformation between functors $(\text{Mnd}_\mathcal{C})^{op} \rightarrow \text{Cat}_\infty$.*

$^{3}$The end of a functor $\mathcal{C} \times \mathcal{C}^{op} \rightarrow \mathcal{D}$ is the limit indexed by the twisted arrow category $\text{Tw}(\mathcal{C}) \rightarrow \mathcal{C} \times \mathcal{C}^{op}$. See [8] or [10]

31