Now set $U_\kappa := \mathfrak{F}^\kappa(\varpi)$ and form the pullback

$$\begin{array}{ccc} \dot{U}_\kappa & \longrightarrow & \dot{V}_\kappa \\ \pi \downarrow & \downarrow^\perp & \downarrow^\varpi \\ U_\kappa & \xrightarrow[\psi_\varpi]{} & V_\kappa. \end{array}$$

As a special case of Lemma 2.1.4(i):

**Lemma 2.3.4.** *The map $\pi: \dot{U}_\kappa \to U_\kappa$ is canonically an $\mathfrak{F}^\kappa$-algebra.*

**Proposition 2.3.5.** *Let $\mathfrak{F}$ be a locally representable notion of fibred structure on a presheaf topos. For sufficiently large regular cardinals $\kappa$, the $\mathfrak{F}^\kappa$-algebra $\pi: \dot{U}_\kappa \to U_\kappa$ is a universe for $\mathfrak{F}^\kappa$.*

*Proof.* Construction 2.3.3 defines the $\mathfrak{F}^\kappa$-algebra classifier as the pullback

$$\begin{array}{ccc} \mathsf{E}(-, U_\kappa) & \xrightarrow{\psi_\varpi} & \mathsf{E}(-, V_\kappa) \\ \pi \downarrow & \downarrow^\perp & \downarrow^\varpi \\ \mathfrak{F}^\kappa & \longrightarrow & \mathfrak{C}^\kappa. \end{array}$$

Note that this strict pullback is also a bicategorical pullback, as $\mathfrak{F}^\kappa \to \mathfrak{C}^\kappa$ is a strict discrete fibration. Since the Hofmann–Streicher classifier $\varpi: \dot{V}_\kappa \to V_\kappa$ is a universe, the right-hand vertical map is an acyclic fibration, whence its bicategorical pullback is as well. $\square$

For size reasons, multiple universes will be required to classify all maps belonging to a given notion of fibred structure. So that the maps classified by a given universe are closed under various categorical operations, we now assume that the cardinals $\kappa$ are inaccessible so that the corresponding Hofmann–Streicher universes $\varpi: \dot{V}_\kappa \to V_\kappa$ can be thought of as internalized Grothendieck universes.

**Definition 2.3.6.** A pullback-stable class of maps $\mathcal{P}$ in a presheaf topos **has universes** if for any cardinal $\lambda$, there exists an inaccessible cardinal $\kappa \geq \lambda$ and a universe $\pi: \dot{U}_\kappa \to U_\kappa$ for a relatively acyclic notion of fibred structure whose underlying maps are the $\kappa$-small maps in $\mathcal{P}$.

In particular, each $\kappa$-small map in $\mathcal{P}$ is a pullback of $\pi: \dot{U}_\kappa \to U_\kappa$, by Proposition 2.3.2.

We now make a standing assumption that there exist arbitrarily large inaccessible cardinals. Proposition 2.3.5 then provides universes for the class of maps underlying any locally representable and relatively acyclic notion of fibred structure on a presheaf topos. See [Shu19] or [GSS22b] for a treatment of universe levels in more general categorical settings.

**Notation 2.3.7.** In the setting of Definition 2.3.6, it is often not necessary to disambiguate between the inaccessible cardinals indexing universe levels. Thus, we typically write $\pi: \dot{U} \to U$ for a generic member of the classifying family of universes, without explicitly designating the cardinal bound.

### 3. CYLINDRICAL MODEL STRUCTURES

In this section, we lay the theoretical groundwork for the construction of our two models of homotopy type theory, proving our results at a level of generality that ensures that they will apply to both cubical sets and cubical species while also enabling their use elsewhere. In §3.1, we introduce the notion of cylindrical premodel structure [Sat20], also used in [CS25], which provides the familiar structures of abstract homotopy theory in a setting where the weak equivalences are not yet known to satisfy the 2-of-3 property. In particular, these axioms provide fibred mapping path space factorizations that are stable under slicing, the basic properties of which we establish in §3.2.

In §3.3, we state and prove the equivalence extension property in a locally cartesian closed cylindrical premodel category in which the cofibrations are the monomorphisms and these are stable

24