Since $V$ is a fibred functor, the images of these cocones by $V$ land in $\mathcal{E}_{\mathcal{B}\text{-cart}}$. By 4.3.4(b), then, they are also colimit cocones; since $Vd^{\dagger} \circ \text{pull}_P\beta = \pi_1 \circ \text{pull}_P\beta: \mathcal{K} \times \mathcal{E}_{b_0} \to \mathcal{E}$, this means that $Vf_0 \cong P^*b_0: \mathcal{E}_{b_0} \to \mathcal{E}$. Since $V$ is an isofibration, we can assume without loss of generality that $Vf_0 = P^*b_0$ and that $V\phi = \text{lift}_P\beta$. In this case, $f_0$ and $\phi$ correspond (using the description of Proposition 4.3.7) to an object $f_0^{\dagger} \in \overline{\prod}_P V$ and cocone $\phi^{\dagger}: d \to \Delta f_0^{\dagger}$.

It remains to check that $\phi^{\dagger}$ is a colimit cocone. Let $\xi: d \to \Delta x$ be a cocone under $d$. Write $b_x = P_{\text{c}}V(x) \in \mathcal{B}$ and $\beta' = P_{\text{c}}V \circ \xi: b \to \Delta b_x$; we have a unique morphism $[\beta']\colon b_0 \to b_x$ with $\Delta[\beta'] \circ \beta' = \beta$. By Proposition 4.3.7, $\xi$ corresponds to a transformation $\xi^{\dagger}: d^{\dagger} \circ \text{pull}_P\beta' \to x^{\dagger}\pi_1$ with $V\xi^{\dagger} = \text{lift}_P\beta'$. By the universal properties of $\phi(-, [\beta']^*e)$ for $e \in \mathcal{E}_{b_x}$, $\xi^{\dagger}$ induces a natural transformation $f_0[\beta']^* \to x^{\dagger}$, valued in $Q$-cartesian morphisms, which transposes to the desired morphism $f_0^{\dagger} \to x$ in $\overline{\prod}_P V$ over $[\beta']$. $\square$

### 4.3.2 Saturation for extension operations

**Definition 4.3.11.** Given a Grothendieck fibration $P: \mathcal{F} \to \mathcal{E}$, write $\mathcal{F}^{\rightarrow} \hookrightarrow \mathcal{F}^{\rightarrow}$ for the full subcategory of $\mathcal{F}^{\rightarrow}$ consisting of the $P$-cartesian morphisms and $P^{\rightarrow}: \mathcal{F}^{\rightarrow} \to \mathcal{E}^{\rightarrow}$ for the restriction of $P$ to this category.

**Proposition 4.3.12.** If $P: \mathcal{F} \to \mathcal{E}$ is a Grothendieck fibration, then $P^{\rightarrow}: \mathcal{F}^{\rightarrow} \to \mathcal{E}^{\rightarrow}$ is also a Grothendieck fibration.

*Proof.* By the cancellation properties of cartesian morphisms (if $g$ is cartesian and $gf$ is cartesian, then $f$ is cartesian). $\square$

**Definition 4.3.13** (Category of extension operations). Given a Grothendieck fibration $P: \mathcal{F} \to \mathcal{E}$, define $U_P^{\downarrow}: \text{Ext}_P \to \mathcal{E}^{\rightarrow}$ to be the cartesian pushforward

$$\begin{array}{ccc} \mathcal{F}^{\rightarrow} & \overline{\prod}_{\pi_0} \widetilde{\text{dom}}(P) & \\ \widetilde{\text{dom}}(P) \downarrow & & \downarrow \\ \mathcal{E}^{\rightarrow} \times_{\mathcal{E}} \mathcal{F} & \xrightarrow{\pi_0} & \mathcal{E}^{\rightarrow} \end{array}$$

of $\widetilde{\text{dom}}(P) := \langle P^{\rightarrow}, \text{dom} \rangle: \mathcal{F}^{\rightarrow} \to \mathcal{E}^{\rightarrow} \times_{\mathcal{E}} \mathcal{F}$, seen as a fibred functor between the Grothendieck fibrations $P^{\rightarrow}: \mathcal{F}^{\rightarrow} \to \mathcal{E}^{\rightarrow}$ and $\pi_0: \mathcal{E}^{\rightarrow} \times_{\mathcal{E}} \mathcal{F} \to \mathcal{E}^{\rightarrow}$.

An object of $\text{Ext}_P$ over a morphism $f: A \to B$ in $\mathcal{E}^{\rightarrow}$ thus corresponds to a section $f: \mathcal{F}_A \to \mathcal{F}_f^{\rightarrow}$ of the domain projection $\text{dom}: \mathcal{F}_f^{\rightarrow} \to \mathcal{F}_A$, *i.e.*, a functor that extends any $\mathcal{F}$-structure over $A$ to an $\mathcal{F}$-structure over $B$ together with a $P$-cartesian morphism over $f$ from the input to the output structure.

**Definition 4.3.14** (Double category of extension operations). Let $P: \mathcal{F} \to \mathcal{E}$ be a Grothendieck fibration. We extend $U_P^{\downarrow}: \text{Ext}_P \to \mathcal{E}^{\rightarrow}$ of Definition 4.3.13 to a notion of composable structure $U_P: \text{Ext}_P \to \text{Sq}(\mathcal{E})$ by taking the vertical identity functor $\mathbf{id}_{(-)}: \mathcal{E} \to \text{Ext}_P$ to be the transpose of the diagram

$$\begin{array}{ccc} \mathcal{F} & \xrightarrow{\text{id}_{(-)}} & \mathcal{F}^{\rightarrow} \\ \langle \text{id}_{P(-)}, \text{Id}_{\mathcal{F}} \rangle & \xrightarrow{\mathcal{E}^{\rightarrow} \times_{\mathcal{E}} \mathcal{F}} & \widetilde{\text{dom}}(P) \end{array}$$

51