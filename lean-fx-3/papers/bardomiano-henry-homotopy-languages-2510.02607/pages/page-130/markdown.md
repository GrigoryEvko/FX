The burden of the proof falls into showing that the function $\mathcal{J}$ is well-defined. The proof is by induction on the derived rules of $U(\mathcal{C})$. We will focus on writing down the inductive hypothesis $H$ as in [Car78] for this induction.

- For rules $r_{\Omega_\mu}$ of the form $\{x_\beta : \Omega_\beta\}_{\beta < \mu} \vdash \Omega_\mu \text{ Type}$ then $H(r_{\Omega_\mu})$ is either:

1. If the premise of $r_{\Omega_\mu}$ is a non-empty context then $H(r_{\Omega_\beta})$ for all $\beta < \mu$.
2. If $r_{\Omega_\mu}$ is the rule $\vdash \Delta \text{ Type}$ then $ht(\mathcal{J}(r_{\Omega_\mu})) = 1$. Otherwise, for all $\beta < \mu$ we have $ht(\mathcal{J}(r_{\Omega_\beta})) < ht(\mathcal{J}(r_{\Omega_\mu}))$.
3. For a map $\langle t_\beta \rangle_{\beta < \mu} : \{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \to \{x_\beta : \Omega_\beta\}_{\beta < \mu}$. If for each $\beta + 1 < \mu$ we have $\mathcal{J}(r_{t_\beta + 1}) \in \Gamma(\mathcal{J}(r_{\Omega_{\beta + 1}[t_\gamma|x_\gamma]_{\gamma \leq \beta}}))$ where $r_{\Omega_{\beta + 1}[t_\gamma|x_\gamma]_{\gamma \leq \beta}}$ is the rule $\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash \Omega_{\beta + 1}[t_\gamma|x_\gamma]_{\gamma \leq \beta} \text{ Type}$ then

$$\mathcal{J}(r_{\Omega_\mu[t_\beta|x_\beta]_{\beta < \mu}}) = (\mathcal{J}(t_\beta)_{\beta < \mu})^* \mathcal{J}(r_{\Omega_\mu})$$

- For rules $r_{t_\mu}$ of the form $\{x_\beta : \Omega_\beta\}_{\beta < \mu} \vdash t_\mu : \Omega_\mu$ then $H(r_{t_\mu})$ is either:

1. $H(r_{\Omega_\mu})$.
2. $\mathcal{J}(r_{t_\mu}) \in \Gamma(\mathcal{J}(r_{\Omega_\mu}))$.
3. For a map $\langle t_\beta \rangle_{\beta < \mu} : \{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \to \{x_\beta : \Omega_\beta\}_{\beta < \mu}$. If for each $\beta + 1 < \mu$ we have $\mathcal{J}(r_{t_\beta + 1}) \in \Gamma(\mathcal{J}(r_{\Omega_{\beta + 1}[t_\gamma|x_\gamma]_{\gamma \leq \beta}}))$ then

$$\mathcal{J}(r_{t_\mu[t_\beta|x_\beta]_{\beta < \mu}}) = (\mathcal{J}(t_\beta)_{\beta < \mu})^* \mathcal{J}(r_{t_\mu})$$

where $r_{t_\mu[t_\beta|x_\beta]_{\beta < \mu}}$ is the rule $\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash t_\mu[t_\beta|x_\beta]_{\beta < \mu} : \Omega_\mu[t_\beta|x_\beta]_{\beta < \mu}$.

- For rules $r_\equiv$ or of the form $\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash \Delta \equiv \Delta'$, the hypothesis $H(r_\equiv)$ is either:

1. $H(r_{\Delta'})$ and $\mathcal{J}(r_\Delta) = \mathcal{J}(r_{\Delta'})$.
2. $H(r_\Delta)$ and $\mathcal{J}(r_\Delta) = \mathcal{J}(r_{\Delta'})$.

- For rules $r_\epsilon$ or of the form $\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash t \equiv_\Delta t'$, the hypothesis $H(r_\epsilon)$ is either:

1. $H(r_t)$ and $\mathcal{J}(r_t) = \mathcal{J}(r_{t'})$.
2. $H(r_{t'})$ and $\mathcal{J}(r_t) = \mathcal{J}(r_{t'})$.

130