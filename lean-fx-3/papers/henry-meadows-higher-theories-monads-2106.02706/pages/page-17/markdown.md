corresponds to a module object if and only the corresponding functor from $K$ to the simplicial set of section of $\mathcal{X}^* \to N(\Delta^{op}) \times \Delta^1$ sends each object of $k \in K$ to a module object. This concludes the proof.

**Lemma 3.9.** *If $\mathcal{M}$ is a monoidal $\infty$-category and $K$ any $\infty$-category, then the diagonal functor $\mathcal{M} \to \operatorname{Fun}(K, \mathcal{M})$ admits a structure of monoidal functor.*

*Proof.* This follows immediately from the fact that $\mathcal{M} \to \operatorname{Fun}(K, \mathcal{M})$ is natural in $\mathcal{M}$ and that the monoidal structure on $\operatorname{Fun}(K, \mathcal{M})$ is obtained by postcomposing the functor $N(\Delta^{op}) \to \mathbf{Cat}_{\infty}$ classifying the monoidal structure of $\mathcal{M}$ with $\operatorname{Fun}(K, -)$. $\square$

*Remark 3.10.* We fix $\mathcal{M}$ a monoidal $\infty$-category with an action on an $\infty$-category $\mathcal{X}$, and $K$ any $\infty$-category. For $M$ any monoid object in $\mathcal{M}$, one can use the monoidal functor of Lemma 3.9 to see $M$ as a “constant” monoid object in $\operatorname{Fun}(K, \mathcal{M})$. Through the monoidal action of $\operatorname{Fun}(K, \mathcal{M})$ on $\operatorname{Fun}(K, \mathcal{X})$ introduced by Lemma 3.7, we can look at the $\infty$-category

$$\mathbf{LMod}^M(\operatorname{Fun}(K, \mathcal{X}))$$

of $M$-modules in $\operatorname{Fun}(K, \mathcal{X})$. We then have, as a special case of Lemma 3.8 an equivalence (in fact an isomorphism)

$$\mathbf{LMod}^M(\operatorname{Fun}(K, \mathcal{X})) \simeq \operatorname{Fun}(K, \mathbf{LMod}^M(\mathcal{X})).$$

Indeed, the left hand side corresponds to the fiber of $\mathbf{LMod}(\operatorname{Fun}(K, \mathcal{X})) \simeq \operatorname{Fun}(K, \mathbf{LMod}(\mathcal{X}))$ over $M \in \operatorname{Fun}(K, \mathbf{Mon}(\mathcal{M}))$. However, given that $M$ is in $\mathbf{Mon}(\mathcal{M})$ this actually is a fiber of $F_K(\mathbf{LMod}(\mathcal{X}))$, and hence can be identified with the simplicial set of functors from $K$ to the fiber of $\mathbf{LMod}(\mathcal{X})$ as explained in Proposition 2.7. This also shows that these equivalences are natural in $M$.

We will write $\operatorname{End}(\mathcal{C})$ for the simplicial monoid of endomorphisms of an $\infty$-category $C$. By 3.4, it has the structure of a monoidal $\infty$-category. In [16] Lurie defines the *category of monads on $\mathcal{C}$*, which we denote by $\mathbf{Mnd}_{\mathcal{C}}$, to be the category of monoid objects in $\operatorname{End}(\mathcal{C})$. Given a monad $M \in \mathbf{Mnd}_{\mathcal{C}}$ acting on a category $\mathcal{E}$, and a monad $T$ on $\mathcal{C}$, we write $\mathcal{E}^T$ for the category of $T$-modules.

17