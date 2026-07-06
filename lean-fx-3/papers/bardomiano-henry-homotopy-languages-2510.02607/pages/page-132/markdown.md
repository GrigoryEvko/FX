Observation B.41. Let $\langle t_\beta \rangle_{\beta < \mu} : \{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \to \{x_\beta : \Omega_\beta\}_{\beta < \mu}$ be a map, then there are maps $\{g_\beta : \mathcal{J}(r_{\Delta_\lambda}) \to \mathcal{J}(r_{\Omega_\beta})\}_{\beta < \mu}$ with $\delta_{g_\beta} = \mathcal{J}(r_{t_b \text{eta}})$ and $pg_{\beta+1} = g_\beta$. This is a consequence of theorem B.40 and theorem B.11. Therefore, there exists a unique $g : \mathcal{J}(r_{\Delta_\lambda}) \to \mathcal{J}(r_{\Omega_\mu})$ such that for all $\beta < \mu$ we have $\delta_{pg} = \mathcal{J}(r_{t_\beta})$ where $p : \mathcal{J}(r_{\Delta_\lambda}) \to \mathcal{J}(r_{\Omega_\beta})$.

**Definition B.42.** We define a function

$$\xi_{\mathcal{C}} : \mathcal{C}_{U(\mathcal{C})} \to \mathcal{C}$$

by:

1. For an object $[\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}] \in \mathcal{C}_{U(\mathcal{C})}$,

$$\xi([\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}]) := \mathcal{J}(r_{\Delta_\lambda}).$$

2. For a morphism $[\langle t_\beta \rangle_{\beta < \mu}] : [\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}] \to [\{x_\beta : \Omega_\beta\}_{\beta < \mu}]$

$$\xi([\langle t_\beta \rangle_{\beta < \mu}]) := g,$$

where $g : \mathcal{J}(r_{\Delta_\lambda}) \to \mathcal{J}(r_{\Omega_\mu})$ is the unique map from theorem B.41.

**Lemma B.43.** 1. If $\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash \Delta_\lambda$ Type is a derived rule of $U(\mathcal{C})$ then for all $\alpha \leq \lambda$, $\{x_\gamma : \Delta_\gamma\}_{\gamma < \lambda} \vdash \Delta_\alpha \equiv \mathcal{J}(r_{\Delta_\alpha})(x_\gamma)_{\gamma < \alpha}$ is a derived rule of $U(\mathcal{C})$.

2. If $\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash t_\lambda : \Delta_\lambda$ is a derived rule of $U(\mathcal{C})$ then $\{x_\gamma : \Delta_\gamma\}_{\gamma < \lambda} \vdash t \equiv \mathcal{J}(r_{t_\lambda})(x_\alpha)_{\alpha < \lambda}$ is a derived rule of $U(\mathcal{C})$.

Proof. See [Car78, Lemma 15 pp. 2.74].

**Corollary B.44.** As functions, we have that $\eta_{\mathcal{C}}\xi_{\mathcal{C}} = id_{\mathcal{C}_{U(\mathcal{C})}}$ and $\xi_{\mathcal{C}}\eta_{\mathcal{C}} = Id_{\mathcal{C}}$

The results needed for this have been introduced throughout the section. Using that we have a bijection and that $\eta_{\mathcal{C}}$ is already a functor, it follows:

**Corollary B.45.** The function $\xi_{\mathcal{C}} : \mathcal{C}_{U(\mathcal{C})} \to \mathcal{C}$ is a contextual functor.

The main result that is of our interest is:

**Theorem B.46.** There is a natural isomorphism $\mathbb{C}_- \circ U \cong Id_{\kappa\text{-}CON}$.

Finally,

**Corollary B.47.** The categories $\kappa$-CON of $\kappa$-contextual categories and $\kappa$-GAT of $\kappa$-algebraic theories are equivalent.

132