Note that in the definitions above, we do mean equality of sets. Alternatively, we can give a more categorical definition by asking for some compatible isomorphisms and identify objects that have isomorphism compatible to the map to $\mathcal{U}$, or we can give an inductive presentation of the notion, but this makes the exposition slightly more complicated.

Morphisms in $\mathbf{Fam}_{\kappa}$ between two objects $X$ and $Y$ of height $\alpha$ and $\beta$, respectively, are just functions $X_{\alpha} \rightarrow Y_{\beta}$. We call $X_{\alpha}$ and the underlying set of $X$: by construction, this underlying set gives us a functor $\mathbf{Fam}_{\kappa} \rightarrow \mathbf{Set}$, which is an equivalence of categories (or at last a fully faithful functor depending on $\mathcal{U}$). Display maps are functions from $X$ to the restriction of $X$ to an ordinal $\beta \leqslant \alpha$ given by the obvious map $X_{\alpha} \rightarrow X_{\beta}$.

Given a map $v: X_{\alpha} \rightarrow Y_{\beta}$ and a display map $Y_{\beta+\lambda} \rightarrow Y_{\beta}$, we can extend $X$ from $X_{\alpha}$ to $X_{\alpha+\lambda}$ with pullback squares

$$\begin{array}{ccc} X_{\alpha+\lambda} & \longrightarrow & Y_{\beta+\lambda} \\ \downarrow & & \downarrow \\ X_{\alpha} & \stackrel{v}{\longrightarrow} & Y_{\beta} \end{array}$$

where at each successor stage, we condition that the composite function $X_{\alpha+\lambda} \rightarrow Y_{\beta+\lambda} \rightarrow \mathcal{U}$ to define $X_{\alpha+\lambda+1}$, and at a limit stage we just define $X$ to be the limit.

One can easily check that $\mathbf{Fam}_{\kappa}$ and the datum specified above, constitute a $\kappa$-contextual category.

**Definition B.49.** Let $T$ be a generalized $\kappa$-algebraic theory. A *model* for $T$ is a $\kappa$-contextual functor $M: \mathbb{C}_T \rightarrow \mathbf{Fam}_{\kappa}$.

*Remark B.50.* Our definition of model might seem ad hoc; however, thanks to theorem B.48, in order to specify such a model we just need to specify how the axioms of $T$ are interpreted in $\mathbf{Fam}_{\kappa}$, and this corresponds to the naive notion of model—a structure where types are interpreted as sets, terms as functions and all equation axioms are valid. In other words, a model for a theory $T$ is really an interpretation of its axioms into the contextual category $\mathbf{Fam}_{\kappa}$.

Recall that a context $\Gamma \in \mathbb{C}_T$ has an associated length or height. If $\Gamma$ is a context of height $\alpha$, then we extend it by adding a fresh variable to obtain a context of height $\alpha+1$. Moreover, we saw that a context whose height is a limit ordinal is obtained as a limit of generalized display maps. Throughout section 2, and particularly in theorem 2.8, we use the notion of model of a generalized $\kappa$-algebraic theory. We take the time explain the notation used there.

134