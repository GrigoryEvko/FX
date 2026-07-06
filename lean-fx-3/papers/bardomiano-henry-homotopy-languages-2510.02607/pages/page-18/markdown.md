## 2.3 The Category theoretic approach: The first-order language of a $\kappa$-clans

In this section we present another equivalent approach to the definition of the language, which is more categorical in spirit, and strongly inspired from Lawvere's theory of hyperdoctrines ([Law69], [Law70]). This approach, while much more abstract, has several advantages over the syntactic one. Mainly, it allows working directly with the category $\text{Mod}(T)$ of models equipped with the weak factorization system on the category of models constructed in the previous subsection, without referring to the theory $T$ at all, and to generalize it to an arbitrary category with a weak factorization system. This will be useful later on to define the language of a model category without having to build explicitly a syntax for it.

As before, we fix $\lambda$ a regular cardinal. A $\lambda$-boolean algebra is a boolean algebra which admits joins (and hence intersections) of $\lambda$-small families. We denote by $\mathbf{Bool}_{\lambda}$ the category whose objects are $\lambda$-boolean algebras and whose morphisms are boolean algebra morphisms preserving $\lambda$-small joins (and hence intersections).

We introduce the notion of $\lambda$-boolean algebra over a clan $\mathcal{C}$, which we can think of as an axiomatization of the structure that the $\mathbb{L}_{\lambda}^{T}$ from section 2.1 have over the contextual category of $T$.

**Definition 2.20.** Given $\mathcal{C}$ a clan and $\lambda$ a regular cardinal, a $\lambda$-boolean algebra over $\mathcal{C}$ is a functor

$$\mathcal{B} : \mathcal{C}^{op} \to \mathbf{Bool}_{\lambda}$$

such that:

1. For each fibration $\pi : Z \to X$ in $\mathcal{C}$, $\pi^* : \mathcal{B}(X) \to \mathcal{B}(Z)$ has a left adjoint:

$$\exists_{\pi} : \mathcal{B}(Z) \leftrightarrows \mathcal{B}(X) : \pi^*.$$

2. The Beck-Chevalley condition holds for each pullback square along a fibration. That is, given any pullback square:

$$\begin{array}{ccc} Z' & \xrightarrow{f'} & Z \\ \pi' \downarrow & \downarrow^{\perp} & \downarrow^{\pi} \\ X' & \xrightarrow{f} & X \end{array}$$

with $\pi$ a fibration, we have $f^* \exists_{\pi} = \exists_{\pi'} f'^*$.

18