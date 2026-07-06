**Definition 2.2.6.** Let $\kappa > 0$ be a limit ordinal. The (large) category $\text{ConfMnd}_{\text{wp}}^{\kappa}$ of *configurations for the free monad sequence on a well-pointed endofunctor* is defined as follows:

- (i) An object is a tuple $(\mathcal{E}, \mathcal{M}, \mathcal{S})$ of a category $\mathcal{E}$, a wide subcategory $\mathcal{M} \hookrightarrow \mathcal{E}$, and a well-pointed endofunctor $\mathcal{S} = (S, \sigma)$ on $\mathcal{E}$ such that:
  - (a) $\sigma$ is valued in $\mathcal{M}$;
  - (b) $\mathcal{M}$ has colimits of $(1 + \alpha)$-chains in $\mathcal{E}$ for $\alpha < \kappa$;
  - (c) if $(X, x)$ is an $\mathcal{S}$-algebraized $\kappa$-chain such that $X$ and $x$ factor through $\mathcal{M}$, then $X$ admits a colimit in $\mathcal{E}$ and this colimit is preserved by $S$.
- (ii) A morphism $(\mathcal{E}_1, \mathcal{M}_1, \mathcal{S}_1) \rightarrow (\mathcal{E}_2, \mathcal{M}_2, \mathcal{S}_2)$ is a map $(F, \gamma): (\mathcal{E}_1, \mathcal{S}_1) \rightarrow (\mathcal{E}_2, \mathcal{S}_2)$ in $\mathbf{PtdEndo}_s$ such that $F$ sends $\mathcal{M}_1$ into $\mathcal{M}_2$, preserves colimits of $(1 + \alpha)$-chains in $\mathcal{M}_1$ for $\alpha < \kappa$, and preserves colimits of $\mathcal{S}$-algebraized $\kappa$-chains in $\mathcal{M}_1$.

**Remark 2.2.7.** Conditions 2.2.6(b) asks that each $(1 + \alpha)$-chain in $\mathcal{M}$ admits a cocone in $\mathcal{M}$ that is colimiting both in $\mathcal{M}$ and in $\mathcal{E}$. In contrast, 2.2.6(c) requires only that each (algebraic) $\kappa$-chain has a colimit in $\mathcal{E}$.

This distinction accommodates cases such as where $\mathcal{E}$ is a category with coproducts and $\mathcal{M}$ is the class of complemented monomorphisms. These examples are important when working in constructive metatheories, as discussed in Appendix A. Given an $\omega$-chain $A_0 \mapsto A_1 \mapsto \cdots$ of complemented monomorphisms, its colimit in $\mathcal{E}$ can be computed without quotienting as the coproduct $\prod_{n < \omega} A_n \setminus A_{n-1}$ of complements (setting $A_{-1} := 0$). However, this need not be a colimit in the wide subcategory of complemented monomorphisms: given a family of compatible inclusions $A_n \mapsto B$ for $n < \omega$, we do get an inclusion $\text{colim}_n A_n \mapsto B$, but the latter may not be complemented.

We take care to only ask for colimits of *algebraic* chains in 2.2.6(c) because we will use this assumption in the reduction of the pointed to the well-pointed case; see Lemma 2.3.23.

We now show that the forgetful functor $U_{\mathcal{S}}: \mathcal{S}\text{-Alg} \rightarrow \mathcal{E}$ associated to a configuration $(\mathcal{E}, \mathcal{M}, \mathcal{S})$ admits a left adjoint, functorially in the configuration. There are two aspects to this theorem. The first is to ensure that free algebras exist for any fixed configuration; we construct these explicitly following Kelly. This already ensures that the functor $\text{ConfMnd}_{\text{wp}}^{\kappa} \rightarrow \mathbf{Fun}_s$ lifts to through the category $\mathbf{Adj}_{l/s}$ defined as $\mathbf{Adj}_s$ in Definition 2.1.2 but without requiring the $\alpha: F_2U \rightarrow VF_1$ in the definition of morphisms to be invertible, since the projection $\mathbf{Adj}_{l/s} \rightarrow \mathbf{Fun}_s$ of the right adjoint is fully faithful.

The second is to show that this $\text{ConfMnd}_{\text{wp}}^{\kappa} \rightarrow \mathbf{Adj}_s$ lifts through the inclusion $\mathbf{Adj}_s \rightarrow \mathbf{Adj}_{l/s}$, *i.e.*, to show that the $\alpha$-components of the action of $\text{ConfMnd}_{\text{wp}}^{\kappa} \rightarrow \mathbf{Adj}$ on morphisms are invertible. This corresponds to showing that the colimits invoked in constructing free algebras are preserved by the mediating functor; the morphisms in $\text{ConfMnd}_{\text{wp}}^{\kappa}$ are defined so as to ensure this.

**Lemma 2.2.8.** Let $\mathcal{T}$ be a pointed endofunctor on a category $\mathcal{E}$, let $\kappa$ be a limit ordinal, and let $(X, x)$ be a $\mathcal{T}$-algebraized $\kappa$-chain. If $X$ admits a colimit $X_\kappa \in \mathcal{E}$ and $\mathcal{T}$ preserves this colimit, then $X_\kappa$ admits a $\mathcal{T}$-algebra structure.

*Proof.* Write $(v_\alpha: X_\alpha \rightarrow X_\kappa)_{\alpha < \kappa}$ for the colimit cocone under $X$. For each $\alpha < \kappa$, we have a choice of $\alpha < \alpha' < \kappa$ by assumption that $\kappa$ is a limit ordinal; write $t_\alpha: TX_\alpha \rightarrow X_\kappa$ for the composite

$$TX_\alpha \xrightarrow{x_{\alpha < \alpha'}} X_{\alpha'} \xrightarrow{v_{\alpha'}} X_\kappa.$$

12