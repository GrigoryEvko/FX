*Remark B.48.* In theorem B.26 we defined a map $T \to U(\mathbb{C}_T)$ simply by interpreting the axioms of the theory $T$ *i.e.*, by defining an interpretation sending axioms of the theory $T$ to derived rules of $U(\mathbb{C}_T)$. In the same way, given a $\kappa$-contextual category $\mathcal{C}$, we can define a map $T \to U(\mathcal{C})$ by sending axioms of $T$ to derived rules in $U(\mathcal{C})$. It follows that we have a $\kappa$-contextual functor $\mathbb{C}_T \to \mathcal{C}$.

### B.4 Models of a generalized Cartmell theory

In this section, we aim to make precise what we mean by a model of a generalized $\kappa$-algebraic theory $T$. Furthermore, if we were to prove a theorem in the same spirit of Lawvere's Functorial semantics, we would prove that there is an equivalence of categories

$$T\text{-}\mathbf{Alg}_\kappa \cong [\mathbb{C}_T, \mathbf{Fam}_\kappa]$$

where $T\text{-}\mathbf{Alg}_\kappa$ is the category of models of the theory $T$ and $\mathbf{Fam}_\kappa$ is a certain $\kappa$-contextual category of 'sets' or rather families of sets, and $[\mathbb{C}_T, \mathbf{Fam}_\kappa]$ is the category of $\kappa$-contextual functors between these two $\kappa$-contextual categories. Since in the paper we do not use the category $T\text{-}\mathbf{Alg}_\kappa$, we are simply interested in constructing the (large) $\kappa$-contextual category $\mathbf{Fam}_\kappa$. Then we can define a model of the theory $T$ simply as a $\kappa$-contextual functor $M : \mathbb{C}_T \to \mathbf{Fam}_\kappa$. Once more, this is a straightforward generalization of Cartmell's construction of the contextual category $\mathbf{Fam}$ [Car78, Section 2.2 pag. 2.9].

We fix a set of sets $\mathcal{U}$, which will play the role of the set of all sets. Ideally, $\mathcal{U}$ is a Grothendieck universe and in some places we will assume this, though this is technically not needed for the definition to make sense.

An object $X$ of $\mathbf{Fam}_\kappa$ of height $\alpha$ is a functor $X : (\alpha + 1)^{\mathrm{op}} \to \mathcal{U}$, such that:

- $X_0 = 1$,
- For each $\beta < \alpha$ there is map $f : X_\beta \to \mathcal{U}$ such that

$$X_{\beta+1} = \coprod_{x \in X_\beta} f(x)$$

where the map $X_{\beta+1} \to X_\beta$ is the canonical map $\coprod_{x \in X_\beta} f(x) \to X_\beta$,

- For each limit ordinal $\beta$, $X_\beta = \lim_{\gamma < \beta} X_\gamma$.

133