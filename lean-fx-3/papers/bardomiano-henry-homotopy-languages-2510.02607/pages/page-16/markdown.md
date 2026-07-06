2. Isomorphisms are fibrations, the composite of two fibrations is a fibration,
3. Pullback of fibrations exist and are fibrations.

For $\kappa$ a regular cardinal, a $\kappa$-clan is a clan which further satisfies:

4 For any ordinal $\lambda < \kappa$, if $A_{\bullet} : \lambda^{\text{op}} \rightarrow \mathcal{C}$ is a diagram in which all the transition maps $A_{\beta} \rightarrow A_{\alpha}$ for $\alpha < \beta$ are fibrations, then the limits

$$\text{Lim}_{\alpha < \lambda} A_{\alpha}$$

exist, and all the projection maps $\pi_{\beta} : \text{Lim}_{\alpha < \lambda} A_{\alpha} \rightarrow A_{\beta}$ are fibrations. We refer to these as *limits of $\kappa$-small chains of fibrations*.

A *morphism of clans* is a functor that sends fibrations to fibrations, preserves the terminal object and pullbacks of fibrations. A *morphism of $\kappa$-clans* is in addition required to preserve the limits of $\kappa$-small chains of fibrations.

A *model* of a $\kappa$-clan $\mathcal{C}$ is a morphism of $\kappa$-clans $\mathcal{C} \rightarrow \mathbf{Set}$, where $\mathbf{Set}$ has the $\kappa$-clan structure where every map is a fibration.

*Remark 2.17.* For a generalized $\kappa$-algebraic theory $T$, the syntactic category $\mathbb{C}_T$ is an example of a $\kappa$-clan, and we show in section B that every $\kappa$-clan is equivalent to such a syntactic category $\mathbb{C}_T$. As discussed in theorem B.52 and theorem B.54, models of a generalized algebraic theory $T$ are closely related to models of the $\kappa$-clan $\mathbb{C}_T$, but they are not the same thing in general. It can be shown they agree, in the case of theories without type equality axioms, but not in general. Replacing the notion of model of a theory by that of models of a clan everywhere in the paper has no consequences anywhere and the reader should feel free to do so. The cofibration/anodyne fibrations weak factorization on $\text{Mod}(T)$ can be defined in the exact same way (using the Yoneda embedding) on the category $\text{Mod}(\mathcal{C})$ of models of a clan.

*Remark 2.18.* In the special case $\kappa = \omega$, this weak factorization was defined in [Hen16, Definition 2.4.2] and extensively studied in [Fre25] in the context of models of clans. In particular, Jonas Frey gave in [Fre25] a complete characterization of which pairs of a category and a weak factorization system can be obtained in this way from an $\omega$-clan – or equivalently from a generalized algebraic theory with no type equality axioms (see the discussion in theorem B.52 and theorem B.54). The methods used by Frey can be extended to the $\kappa$-case to obtain a similar characterization. Frey also shows

16