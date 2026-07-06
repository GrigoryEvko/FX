Let $M_1, M_2$ be the monads associated to the left and right vertical maps of $G$, respectively. Since the horizontal maps are fully faithful, we can without loss of generality treat the horizontal maps as inclusions of full subcategories. The restriction of the counit of $H_2 \dashv F_2$ gives the counit of the adjunction $H_2|_{\mathcal{B}} : \mathcal{B} \leftrightarrows Alg_{\mathcal{O}^\otimes}(\mathcal{B}) : F_1$, since $H_2$ takes objects of $\mathcal{B}$ to $Alg_{\mathcal{O}^\otimes}(\mathcal{B})$. Consider the composites

$$\text{Fin} \subseteq \mathcal{B} \xrightarrow{H_2|_{\mathcal{B}}} Alg_{\mathcal{O}^\otimes}(\mathcal{B}) \quad \text{Fin} \subseteq \mathcal{S} \xrightarrow{H_2} Alg_{\mathcal{O}^\otimes}(\mathcal{S})$$

the essential images of which correspond to $\text{Th}_{\mathcal{B}}(M_1), \text{Th}_{\mathcal{S}}(M_2)$. These composites are the same, since $\text{Fin} \subseteq \mathcal{B}$. We will denote the composite by $\text{Fin} \rightarrow \mathcal{K}$.

But by 8.7, $M_1, M_2$ are both Fin-Nervous, so that $M_1 \cong \mu_{\mathcal{B}}^{\text{Th}(M_1)} \cong \mu_{\mathcal{B}}^{\mathcal{K}}$, $M_2 \cong \mu_{\mathcal{S}}^{\text{Th}(M_2)} \cong \mu_{\mathcal{S}}^{\mathcal{K}}$.

*Remark 8.11.* In the situation of 8.9 the proof implies that $\text{Free}_{\mathcal{O}}^{\mathcal{B}}$ can be identified with $\text{Free}_{\mathcal{O}}^{\mathcal{S}}|_{\mathcal{B}}$. Thus, we can think of $\text{Free}_{\mathcal{O}}^{\mathcal{S}}$ as extending $\text{Free}_{\mathcal{O}}^{\mathcal{B}}$.

**Example 8.12.** Let $E_1^\otimes$ be the $E_1$-operad studied in [16, Chapter 5]. Using [16, Example 5.1.0.7] we can identify this with the associative operad $\text{Assoc}^\otimes$. By [16, Proposition 4.1.1.18], the free monad functor $\mathcal{S} \rightarrow \text{Alg}_{E_1^\otimes}(\mathcal{S})$ takes $C$ to an algebra with underlying object $\coprod_{n \in \mathbb{N}} C^n$. Since (co)products in the $\infty$-category of spaces can be identified with ordinary (co)products, the free algebra functor preserves the property of having the homotopy type of a set.

Thus, we can apply 8.9 with $\mathcal{B} = \text{Set}, \mathcal{O}^\otimes = E_1^\otimes$ and 8.11, to conclude that the “free-$E_1$-space”-monad on $\mathcal{S}$ extends the “free monoid monad” on sets.

By the rectification result of [16, Theorem 4.1.8.4], $Alg_{\text{Assoc}^\otimes}(\text{Set}) \rightarrow \text{Set}$ can be identified with the forgetful functor $\text{Monoid} \rightarrow \text{Set}$, which takes a monoid in the classical sense to its underlying set. Thus, the ‘free monoid monad’ constructed above can be identified with the classical free monoid monad from [4, Example 9]). Moreover, if $\mathcal{K}$ is the classical algebraic theory from [4] whose set-valued models are monoids, then its models in $\mathcal{S}$ can be identified with the $E_1$-spaces.

**Lemma 8.13.** *Let $\text{Comm}^\otimes$ be the commutative (or $E_\infty$) operad studied in [16, Example 2.1.1.8]. The free algebra functor $\mathcal{S} \rightarrow \text{Alg}_{\text{Comm}^\otimes}(\mathcal{S})$ takes elements of $\text{Gpd}$ to elements of $\text{Alg}_{\text{Comm}^\otimes}(\text{Gpd})$.*

49