any symmetric monoidal $\infty$-category $\mathcal{B}$ (or more generally any $\mathcal{O}$-monoidal $\infty$-category).

The goal of the next few paragraphs is to show that given a non-colored $\infty$-operad $\mathcal{O}^\otimes$, then the forgetful functor $\mathrm{Alg}_{\mathcal{O}^\otimes}(\mathcal{B}) \rightarrow \mathcal{B}$ where $\mathcal{B}$ is one of the (cartesian) symmetric monoidal $\infty$-categories Set, Gdp or $\mathcal{S}$, is monadic and the associated monad is Fin-nervous, where $\mathrm{Fin} \subset \mathcal{B}$ is the full subcategory of finite sets.

Recall that the $\infty$-category of spaces $\mathcal{S}$, as well as its full subcategory Set and Gpd of sets (i.e. discrete spaces) and groupoids (i.e. 1-truncated spaces), are cartesian closed locally presentable $\infty$-categories. In particular Lemma 8.4 and Lemma 8.5 below can be applied to them.

**Lemma 8.4.** *Let $\mathcal{O}^\otimes$ be a non-colored $\infty$-operad and $\mathcal{C}$ a locally presentable cartesian closed symmetric monoidal $\infty$-category.*

*Then $\infty$-category $\mathrm{Alg}_{\mathcal{O}^\otimes}(\mathcal{S})$ has all sifted colimits and the forgetful functor $\mathrm{Alg}_{\mathcal{O}^\otimes}(\mathcal{C}) \rightarrow \mathrm{Fun}(\mathcal{O}, \mathcal{C}) \simeq \mathcal{C}$ preserves sifted colimits.*

*Proof.* For the first statement [16, Proposition 3.2.3.1] implies that it suffices to show that for $n \in \mathbb{N}$, the induced map $\mathcal{C}_{[n]}^\otimes \rightarrow \mathcal{C}_{[1]}^\otimes$ (see [16, Remark 2.1.2.6]), preserves sifted colimits separately in each variable. Because $\mathcal{C}$ is cartesian, this functor can be identified with the functor $\mathcal{C}^n \rightarrow \mathcal{C}$ that takes a collection of objects to their n-fold product. But since $\mathcal{C}$, is cartesian closed, products preserve sifted colimits separately in each variable, hence the result.

The fact that the forgetful functor preserves all sifted colimits follows from another application of [16, Proposition 3.2.3.1].

□

The left adjoint of the forgetful functor $\mathrm{Alg}_{\mathcal{O}^\otimes}(\mathcal{C}) \rightarrow \mathcal{C}$ (if it exists) is called the *free $\mathcal{O}$-algebra functor* and is denoted $\mathrm{Free}_{\mathcal{O}}^\mathcal{C}$.

**Lemma 8.5.** *Let $\mathcal{O}^\otimes$ and $\mathcal{C}$ as in Lemma 8.4. Then the forgetful functor $\mathrm{Alg}_{\mathcal{O}^\otimes}(\mathcal{C}) \rightarrow \mathcal{C}$ is a monadic right adjoint functor.*

*Proof.* We verify the three hypotheses of Barr-Beck-Lurie. Since colimits in $\mathcal{C}$ are preserved by the products and $\mathcal{C}$ is presentable, it follows from [16, Example 3.1.3.6] and Lemma 8.4 that the functor is a right adjoint. Since $N(\Delta^{\mathrm{op}})$ is sifted ([15, Lemma 5.5.8.3]), 8.4 implies that it preserves colimits of split simplicial objects. The functor reflects limits ([16, Corollary 3.2.2.5]) and hence reflects equivalences; the limit of a diagram $X : \Delta^0 \rightarrow \mathcal{C}$ is just an object equivalent to $X$.

□

46