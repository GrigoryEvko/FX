STRICT UNIVERSES FOR GROTHENDIECK TOPOI

11

The functorial action on morphisms of $z' \longrightarrow z : \mathcal{C}_{/C}$ is obtained from the fact that each $\beta_D(z \cdot x)$ is isomorphic to $\chi_D(z \cdot x)(\mathbf{id}_D)$, which is a fiber of a $\mathbf{v}$-valued presheaf and hence has the needed functorial action. To check that $\check{\beta}$ restricts along $\phi$ to $\alpha$, we fix $z: D \longrightarrow C$ and compute:

$$\begin{array}{l} \check{\beta}_C(\phi_C(x))(z) = \beta_D(z \cdot \phi_D(x)) \\ = \beta_D(\phi_C(z \cdot x)) \\ = \hat{\alpha}_D(z \cdot x) \\ = \alpha_D(z \cdot x)(\mathbf{id}_D) \\ = \alpha_C(x)(z) \end{array}$$

2.2.5. THEOREM. The class of morphisms $\hat{\mathcal{S}}_{\mathsf{V}}$ in $\Pr(\mathcal{C})$ is a universe satisfying (U1–8).

2.3. STREICHER'S UNIVERSE OF SHEAVES. Fixing a Grothendieck topology $J$ on $\mathcal{C}$, we show that the universe $\hat{\mathcal{S}}_{\mathsf{V}}$ induces a universe on $\operatorname{Sh}(\mathcal{C}, J)$. Let $i: \operatorname{Sh}(\mathcal{C}, J) \to \Pr(\mathcal{C})$ denote the inclusion geometric morphism, so that $i_*$ is the inclusion functor and $i^*$ is sheafification.

2.3.1. DEFINITION. We define $\tilde{\mathcal{S}}_{\mathsf{V}}$ to be the collection of all maps $f$ such that $i_* f \in \hat{\mathcal{S}}_{\mathsf{V}}$.

This collection of maps is easily shown to satisfy (U1–4) because $i_*$ preserves finite limits. The existence of a generic map (U5) has been the source of controversy within the type-theoretic literature; one potential candidate is the restriction of $\pi_{\hat{\mathcal{S}}_{\mathsf{V}}}$ to the presheaf of pointwise V-small sheaves, but this is not actually a sheaf as pointed out by Xu and Escardó [XE16]. Streicher [Str05] proposed a more direct approach: the generic map for $\tilde{\mathcal{S}}_{\mathsf{V}}$ is the sheafification of the generic map for $\hat{\mathcal{S}}_{\mathsf{V}}$. To prove this, we recall Proposition 5.4.4 of van den Berg [vdB11]:

2.3.2. PROPOSITION. If $f \in \hat{\mathcal{S}}_{\mathsf{V}}$ then $i^* f \in \tilde{\mathcal{S}}_{\mathsf{V}}$.

With this to hand, we immediately conclude that $i^* \varpi \in \tilde{\mathcal{S}}_{\mathsf{V}}$.

2.3.3. COROLLARY. The family $i^* \varpi$ is generic for $\tilde{\mathcal{S}}_{\mathsf{V}}$.

PROOF. Fix $f: X \longrightarrow Y \in \tilde{\mathcal{S}}_{\mathsf{V}}$. By definition, $i_* f \in \hat{\mathcal{S}}_{\mathsf{V}}$ so by (U5) the following cartesian square exists:

$$\begin{array}{c} i_* X \longrightarrow \widetilde{\mathrm{U}} \\ \downarrow \quad \downarrow \\ i_* Y \longrightarrow \mathrm{U} \end{array} \tag{5}$$

The image of this cartesian square under $i^*$ remains cartesian and thus shows that $f \cong i^* i_* f$ is classified by $i^* \varpi$.