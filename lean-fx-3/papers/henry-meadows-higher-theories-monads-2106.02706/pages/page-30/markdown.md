$$\mathcal{X}^d \rightarrow \text{Fun}(\mathcal{X}_d^{op}, \mathcal{S})$$

*which are levelwise the restriction of the Yoneda embeddings. Here, $X_d$ has its covariant functoriality from Proposition 4.5, $X^d$ has its original contravariant functoriality and we use the contravariant functoriality of $\text{Fun}(-,\mathcal{S})$ given by restriction of presheaves to make the right hand side into functors with the appropriate variance.*

*Proof.* $\text{Fun}(-,\mathcal{S})$ has two different functorialities. Firstly, it has the natural contravariant functoriality used in the statement of the proposition, where each induced map $f^*: \text{Fun}(\mathcal{X}^d, \mathcal{S}) \rightarrow \text{Fun}(\mathcal{X}^{d'}, \mathcal{S})$ induced by $f: X^{d'} \rightarrow X^d$ has a right adjoint. The second functoriality is then given by applying Proposition 4.5 to obtain a covariant functoriality $\mathcal{C} \mapsto \text{Fun}(\mathcal{C}, \mathcal{S})$, where morphisms acts as the left adjoint to the reindexing functors given by the contravariant functoriality. It was shown in section 6 of [12] that the Yoneda embeddings $\mathcal{C} \rightarrow \text{Pr}(\mathcal{C})$ can be made into a natural transformation when $\text{Pr}(\mathcal{C}) = \text{Fun}(\mathcal{C}^{op}, \mathcal{S})$ is endowed with this second functoriality.

In particular, we have a natural transformation $(\mathcal{X}^d)^{op} \rightarrow \text{Fun}(\mathcal{X}^d, \mathcal{S})$, or equivalently $\mathcal{X}^d \rightarrow \text{Fun}(\mathcal{X}^d, \mathcal{S})^{op}$ where on the right hand side $\text{Fun}(-,\mathcal{S})$ has its covariant (i.e. left adjoint) functoriality.

One can then apply Proposition 4.5 to $\mathcal{X}_d \subset (\mathcal{X}^d)$ to recover the covariant functoriality of $\mathcal{X}_d$ (given by the $(f_!)^{op}$) and to $d \mapsto \text{Fun}(\mathcal{X}^d, \mathcal{S})^{op}$ to recover its usual “precomposition” functoriality as in the proposition. Hence, Proposition 4.8 shows that the Yoneda embedding can be assembled into a natural transformation

$$(\mathcal{X}_d) \rightarrow \text{Fun}(\mathcal{X}^d, \mathcal{S})^{op}.$$

The first condition 1 is vacuous in this case given that the subcategories used on the right hand side are the whole category, and the second condition is easy to check. Indeed, the natural transformation between the left adjoint coming from the naturality square along a map $f: d \rightarrow d' \in \mathcal{D}$ is, for each $X \in \mathcal{X}_d$, the map in $(\text{Fun}(\mathcal{X}^{d'}, \mathcal{S}))^{op}$, which, when evaluated on a $Y \in \mathcal{X}^{d'}$ is the map

$$\text{Map}(f_!(X), Y) \rightarrow \text{Map}(X, f^*(Y))$$

obtained by applying the $f^*$ functoriality and precomposing with the unit $X \rightarrow f^* f_! X$. But essentially by definition, this map is an equivalence.

30