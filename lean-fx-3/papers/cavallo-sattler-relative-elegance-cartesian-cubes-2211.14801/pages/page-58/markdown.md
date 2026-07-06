58

E. Cavallo and C. Sattler

- a weak test category if $i_{\mathbf{C}}^{*}\mathbf{D}$ is aspheric for every $\mathbf{D}$ with a terminal object;
- a local test category if $\mathbf{C}/a$ is a weak test category for all $a \in \mathbf{C}$;
- a test category if it is both a weak and local test category.

Proposition 7.13 (Cis06, Corollaire 4.2.18) Let $\mathbf{C}$ be a local test category. There is a model structure on $\mathrm{PSh}(\mathbf{C})$ in which

- the cofibrations are the monomorphisms;
- the weak equivalences are the maps sent by $N_{\Delta}i_{\mathbf{C}}$ to a weak equivalence of $\widehat{\Delta}^{\mathrm{kq}}$.

We write $\widehat{\mathbf{C}}^{\mathrm{test}}$ for this model category.

Remark 7.14 The test model structure $\widehat{\Delta}^{\mathrm{test}}$ coincides with $\widehat{\Delta}^{\mathrm{kq}}$. A proof is contained in the proof of [Cis06, Corollaire 4.2.19]: the class of weak equivalences of $\widehat{\Delta}^{\mathrm{test}}$ is by definition the preimage $N_{\Delta}^{-1}\mathcal{W}_{\infty}$, which is the minimal test $\Delta$-localizer by Théorème 4.2.15, and said localizer is the class of weak equivalences of $\widehat{\Delta}^{\mathrm{kq}}$ by Corollaire 2.1.21 and Proposition 3.4.25.

Note that whereas cubical-type model structures come with explicit characterizations of their cofibrations and fibrations (or rather generating trivial cofibrations), the test model structure comes with explicit descriptions of its cofibrations and weak equivalences. In general, $\widehat{\mathbf{C}}^{\mathrm{test}}$ is Quillen equivalent to a slice of $\widehat{\Delta}^{\mathrm{kq}}$, namely $\widehat{\Delta}^{\mathrm{kq}}/N_{\Delta}\mathbf{C}$ [Cis06, Corollaire 4.4.20]. When $\mathbf{C}$ is a test category, $N_{\Delta}\mathbf{C}$ is weakly contractible, and so we have an equivalence to $\widehat{\Delta}^{\mathrm{kq}}$ itself.

We recall the argument used by Buchholtz and Morehouse [BM17, Theorem 1] to show that $\square_{\vee}$ is a test category—actually a strict test category.

Definition 7.15 (Cis06, §4.3.1, Proposition 4.3.2, §4.3.3) We say a category $\mathbf{C}$ is totally aspheric if it is non-empty and $\nless a \times \nless b$ is aspheric for every $a, b \in \mathbf{C}$. A test category that is totally aspheric is called a strict test category.

Any representable is aspheric: the category $i_{\mathbf{C}}(\nless a)$ has a terminal object, thus a natural transformation from its identity functor to a constant functor, and this induces a contracting homotopy on $N_{\Delta}i_{\mathbf{C}}(\nless a)$. Thus, any category with binary products is totally aspheric.

The following result originates in [Gro83, Section 44(c)] and is invoked in [BM17] for a broad class of cube categories.

Proposition 7.16 (Cis06, Proposition 4.3.4) Let $\mathbf{C}$ be a totally aspheric category. If $\mathrm{PSh}(\mathbf{C})$ contains an aspheric presheaf $I$ with disjoint maps $e_0, e_1: 1 \to I$, then $\mathbf{C}$ is a strict test category.

In particular, both $\square_{\vee}$ and $\overline{\square}_{\vee}$ are strict test categories. To relate their test model structures to $\widehat{\Delta}^{\mathrm{kq}}$, we recall the notion of aspheric functor.

2025/10/16 00:43