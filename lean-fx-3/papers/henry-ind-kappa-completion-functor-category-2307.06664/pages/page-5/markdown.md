(2) $I$-indexed ends, seen as functors:

$$\int_I : \mathbf{Sets}^{I^{\mathrm{op}} \times I} \to \mathbf{Sets}$$

preserves $\kappa$-filtered colimits.

(3) For any category $A$ with $\kappa$-filtered colimits, a functor $I \to A_\kappa$ is $\kappa$-presentable when seen as an object of $A^I$.
(4) For any locally $\kappa$-presentable category $A$, a functor $I \to A_\kappa$ is $\kappa$-presentable when seen as an object of $A^I$.

Moreover, all these condition holds when $I$ is an essentially $\kappa$-small category.

Note that, at least in the case $\kappa = \omega$, the conditions of the proposition are much weaker than $I$ being $\omega$-small, that is finite. For example, any finitely generated category can be shown to satisfies these conditions. I do not know if for $\kappa$ uncountable there are such example of non-$\kappa$-small categories satisfying these conditions. We refer to [8] for general material about ends.

Proof. The equivalence of conditions (1) and (2) is immediate because of the natural isomorphism:

$$\int_I A(x, x) \simeq \operatorname{Nat}(\operatorname{Hom}(x, y), A(x, y))$$

And the fact that Hom being $\kappa$-presentable means that the functor $\operatorname{Nat}(\operatorname{Hom}(x, y), \_)$ preserve $\kappa$-filtered colimits. Condition (2) implies (3) because of the expression of the morphism in the category of functors $A^I$ as:

$$\operatorname{Hom}_{A^I}(F, G) \simeq \int_{i \in I} \operatorname{Hom}_A(F(i), G(i))$$

Hence given any filtered diagram $(G_j)_{j \in J}$ and $F : I \to A_\kappa$ a functor, we have an isomorphism

$$\begin{array}{rcl} \operatorname{Hom}_{A^I}(F, \operatorname{Colim}_j G_j) & \simeq & \int_{i \in I} \operatorname{Hom}_A(F(i), \operatorname{Colim}_j G_j(i)) \\ & \simeq & \int_{i \in I} \operatorname{Colim}_j \operatorname{Hom}_A(F(i), G_j(i)) \\ & \simeq & \operatorname{Colim}_j \int_{i \in I} \operatorname{Hom}_A(F(i), G_j(i)) \\ & \simeq & \operatorname{Colim}_j \operatorname{Hom}_{A^I}(F, G_j) \end{array}$$

showing that $F$ is indeed $\kappa$-presentable.

The implication $(3) \Rightarrow (4)$ is tautological, and finally $(4) \Rightarrow (1)$ follows from the identification

$$\operatorname{Fun}(I, \mathbf{Sets}^{I^{\mathrm{op}}}) \simeq \operatorname{Fun}(I^{\mathrm{op}} \times I, \mathbf{Sets}).$$

The category $\mathbf{Sets}^{I^{\mathrm{op}}}$ is locally $\kappa$-presentable, with the representable object being $\kappa$-presentable (this holds for any $\kappa$), hence by condition (4), the Yoneda embeddings $I \to \mathbf{Sets}^{I^{\mathrm{op}}}$ is a $\kappa$-presentable object of this functor category, and through the equivalence above, this corresponds to the functor $\operatorname{Hom} : I^{\mathrm{op}} \times I \to \mathbf{Sets}$, hence concluding the proof.

Finally, if $I$ is a $\kappa$-small category, then the end involved in (2) can be rewritten as a limit indexed by the twisted arrow category of $I$, which is a $\kappa$-small limits, and hence it preserves $\kappa$-filtered colimits.

5