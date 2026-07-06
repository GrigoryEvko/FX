**Lemma 8.6.** *For each $s \in \mathcal{S}$, the category $\mathrm{Fin}_{/s}$ is sifted.*

*Proof.* Coproducts in $\mathcal{S}_{/s}$ are computed as coproducts in $\mathcal{S}$, in particular $\mathrm{Fin}_{/s}$, seen as a full subcategory of $\mathcal{S}_{/s}$ is closed under finite coproducts because Fin is closed under finite coproducts in $\mathcal{S}$. The result then follows from Lemma 8.3. $\square$

**Theorem 8.7.** *Suppose that $\mathcal{B} = \mathcal{S}$, Gdp or Set. Let $\mathcal{O}^{\otimes}$ be a non-colored $\infty$-operad. Then the monad on $\mathcal{B}$ corresponding the forgetful functor $\mathrm{Alg}_{\mathcal{O}^{\otimes}}(\mathcal{B}) \rightarrow \mathcal{B}$ is Fin-nervous.*

*Proof.* We will show more precisely that this monad, which we denote $M$, has arities in Fin, in the sense of Definition 6.2, which implies the result by 6.4. It suffices to show that the functor

$$\mathcal{B} \xrightarrow{M} \mathcal{B} \xrightarrow{i} \mathrm{Pr}(\mathrm{Fin})$$

preserves $\mathrm{colim}_{a \in \mathrm{Fin}/X}(a)$ for each $X \in \mathcal{B}$. By 8.6, it suffices to show that $M$ and $i$ preserve sifted colimits. The monad $M$ is the composite of the left adjoint $\mathrm{Free}_{\mathcal{O}}^{\mathcal{B}}$, which preserves all colimits, and the forgetful functor $\mathrm{Alg}_{\mathcal{O}^{\otimes}}(\mathcal{B}) \rightarrow \mathcal{B}$ which preserves sifted colimits by Lemma 8.4. Hence $M$ preserves sifted colimits.

It suffices to show that the restricted Yoneda embedding $i$ preserves sifted colimits. Since colimits in $\mathrm{Pr}(\mathcal{A})$ are calculated pointwise, it suffices to show that for each $K \in \mathrm{Fin}$ and sifted $\infty$-category I, the natural map

$$\mathrm{colim}_{i \in I} \mathrm{Map}_{\mathcal{S}}(K, a_i) \rightarrow \mathrm{Map}_{\mathcal{S}}(K, \mathrm{colim}_{i \in I} a_i)$$

is an equivalence. This can be identified with the map

$$\prod_{j \in K} (\mathrm{colim}_{i \in I} a_i) \rightarrow \mathrm{colim}_{i \in I} \prod_{j \in K} a_i$$

In other words, we want to show that sifted colimits preserve finite products in $\mathcal{B}$, which follows from $\mathcal{B}$ being cartesian closed and [15, Proposition 5.5.8.6 and Lemma 5.5.8.11]. $\square$

**Lemma 8.8.** *Suppose that $G : \mathcal{C} \rightarrow \mathcal{D}$ is a fully faithful functor of $\infty$-categories, and $\mathcal{E}$ be an $\infty$-category. Then $\mathrm{Fun}(\mathcal{E}, \mathcal{C}) \rightarrow \mathrm{Fun}(\mathcal{E}, \mathcal{D})$ is fully faithful.*

47