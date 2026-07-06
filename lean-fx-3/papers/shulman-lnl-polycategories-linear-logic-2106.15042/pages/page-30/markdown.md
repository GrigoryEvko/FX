1:30

M. SHULMAN

Vol. 19:2

*Proof.* We prove (i); the others are analogous. Because the vertex $T^+$ of $\mathcal{C}olim_{\mathcal{A}}^{\mathrm{L}}$ is linear and positive, $(T^-, \Psi)$ is admissible just when $\Psi$ contains no positive nonlinear objects. An extension of $G : \mathcal{C}olim_{\mathcal{A}}^{\mathrm{L}} \to \mathcal{P}$ to some pre-expansion $\partial((\mathcal{C}olim_{\mathcal{A}}^{\mathrm{L}})_{/\Psi})$ thus consists of a list $\Theta$ of nonlinear objects of $\mathcal{P}$, lists $\Gamma$ and $\Delta$ of linear objects of $\mathcal{P}$, and a morphism $\bar{f}_i \in \mathcal{P}(\Theta \mid \Gamma, GA_i; \Delta)$ for each object $A_i \in \mathcal{A}$, such that $\bar{f}_i \circ Gg = \bar{f}_j$ for each morphism $g : A_j \to A_i$ in $\mathcal{A}$. This is precisely an element of $\lim_i \mathcal{P}(\Theta \mid \Gamma, A_i; \Delta)$, the right-hand side of (2.4).

A further extension to the expansion $(\mathcal{C}olim_{\mathcal{A}}^{\mathrm{L}})_{/\Psi}$ is then determined by a morphism $\chi \in \mathcal{P}(\Theta \mid \Gamma, GT; \Delta)$ such that $\chi \circ_{GT} f_i = \bar{f}_i$ for all $A_i \in \mathcal{A}$. To say that there is a unique such morphism is thus precisely to say that the natural map from left-to-right in (2.4) is a bijection. $\square$

**Definition 4.20.** If $H : \mathcal{C} \to \mathcal{Q}$ is a concrete cone, we say that $\pi : \mathcal{P} \to \mathcal{Q}$ **has extremal lifts of $H$** if for any lift $G : \partial \mathcal{C} \to \mathcal{P}$ of the reduct of $\mathcal{C}$ to $\mathcal{P}$, there exists a compatible lift of $H$ that is $\pi$-extremal:

$$\begin{array}{ccc} \partial \mathcal{C} & \xrightarrow[G]{G} & \mathcal{P} \\ \downarrow & \xrightarrow{\pi\text{-ext}} & \downarrow\pi \\ \mathcal{C} & \xrightarrow[H]{} & \mathcal{Q} \end{array}$$

**Example 4.21.** By Proposition 4.17, $\pi$ is a bifibration if and only if it has extremal lifts of all the abstract cartesianness cones from Definition 4.16.

**Definition 4.22.** We say that an LNL polycategory is **bicomplete** if its unique map to the terminal object has extremal lifts of all concrete cones for the abstract limit and colimit cones from Definition 4.18 (where $\mathcal{A}$ is small).

By Proposition 4.19, bicompleteness is equivalent to having all small limits and colimits of both kinds of objects, in the sense described in Section 2.

As pointed out by a referee, the generalization of Definition 4.22 to a relative notion over an arbitrary base $\mathcal{Q}$ is a little subtle: there are at least two natural-seeming possibilities.

**Definition 4.23.** Let $\pi : \mathcal{P} \to \mathcal{Q}$ be a functor of LNL polycategories.

- (i) We say $\pi$ is **relatively bicomplete** if it has extremal lifts of all concrete cones $H : \mathcal{C} \to \mathcal{Q}$ where $\mathcal{C}$ is one of the abstract cones from Definition 4.18 (where $\mathcal{A}$ is small).
- (ii) We say $\pi$ is **fiberwise bicomplete** if it has extremal lifts only of such cones that have the additional property that $H$ factors through the terminal object (equivalently, its image contains only identity maps).

The two coincide in the “absolute” case when $\mathcal{Q}$ is terminal, or more generally when it satisfies the following condition.

**Proposition 4.24.** *If $\mathcal{Q}$ contains no nonidentity unary co-unary morphisms between two objects of the same sort (linear or nonlinear), then a functor $\pi : \mathcal{P} \to \mathcal{Q}$ is relatively bicomplete if and only if it is fiberwise bicomplete. In particular, this is the case when $\mathcal{Q}$ is subterminal.* $\square$

**Example 4.25.** As noted in Section 2, an LNL multicategory cannot have a terminal linear object or an initial linear or nonlinear object when considered as an LNL polycategory. However, while a concrete cone $G : \mathcal{C} \to \mathcal{P}$ of such a shape in an LNL multicategory cannot be