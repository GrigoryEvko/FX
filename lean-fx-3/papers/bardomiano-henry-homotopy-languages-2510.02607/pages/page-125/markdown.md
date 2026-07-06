Proof. We use theorem A.29. It will therefore be enough to test the commutativity of the diagram on type element judgments. Let $\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash t : \Delta_\lambda$ a type element judgment of $T$. For any $\alpha \leq \lambda$ we denote $A_\alpha := [\{x_\delta : \Delta_\delta\}_{\delta \leq \alpha}]$. It follows from theorem B.25 that

$$\widehat{\varphi_T} \left( \frac{\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}}{t : \Delta_\lambda} \right) \approx \frac{\{x_\alpha : \overline{A_\alpha}\}_{\alpha < \lambda}}{[\langle x_\alpha, t \rangle_{\alpha < \lambda}] : \overline{A_\lambda}(x_\alpha)_{\alpha < \lambda}}.$$

We conclude that

$$U(\mathbb{C}(I)) \left( \widehat{\varphi_T} \left( \frac{\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}}{t : \Delta_\lambda} \right) \right) \approx \frac{\{x_\alpha : \overline{\mathbb{C}(I)(A_\alpha)}\}_{\alpha < \lambda}}{\overline{\mathbb{C}(I)([\langle x_\alpha, t \rangle_{\alpha < \lambda}]) : \overline{\mathbb{C}(I)(A_\lambda)}(x_\alpha)_{\alpha < \lambda}}}.$$

Looking at the other composition: we get

$$\widehat{I} \left( \frac{\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}}{t : \Delta_\lambda} \right) = \frac{\{x_\alpha : \widetilde{I}(\Delta_\alpha)\}_{\alpha < \lambda}}{\widetilde{I}(t) : \widetilde{I}(\Delta_\lambda)}.$$

A second use of theorem B.25 give us that

$$\widehat{\varphi_{T'}} \left( \widehat{I} \left( \frac{\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}}{t : \Delta_\lambda} \right) \right) \approx \frac{\{x_\alpha : \overline{B_\alpha}\}_{\alpha < \lambda}}{[\langle x_\alpha, \widetilde{I}(t) \rangle_{\alpha < \lambda}] : \overline{B_\lambda}(x_\alpha)_{\alpha < \lambda}},$$

where for $\alpha \leq \lambda$, $B_\alpha := [\{x_\delta : \widetilde{I}(\Delta_\delta)\}_{\delta \leq \alpha}]$. However, by definition we have $\mathbb{C}(I)(A_\alpha) = B_\alpha$ for $\alpha \leq \lambda$. This completes our verification.

Remains to show that $[\varphi_T]$ is an isomorphism, and natural in $T$. We proceed to give an inverse $\psi_T : U(\mathbb{C}_T) \to T$. Recall that a type symbol of $U(\mathbb{C}_T)$ is of the form $\overline{A_\lambda} = [\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}]$. If $\lambda = \nu + 1$, then by choosing a representative of this equivalence class of the context we can define $\psi_T(\overline{A_\lambda}) := \Delta_\nu$.

If $\lambda$ is a limit ordinal, once we chose a representative, $\Delta_\lambda = \{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}$. Then we know that $[\Delta_\lambda] = \lim_{\alpha < \lambda} [\Delta_\alpha]$ in $\mathbb{C}_T$, and this limit is unique. In this case, the value of $\psi_T$ is determined by non-limit ordinals $\alpha < \lambda$, which are $\psi_T(\overline{\Delta_\alpha}) = \Delta_\alpha$. Therefore, we define $\psi_T([\overline{\Delta_\lambda}]) := \Delta_\lambda$ for some choice of a representative of the equivalence class. However, note that the successor case determinate the limit case.

Operator symbols of $U(\mathbb{C}_T)$ come from morphisms of $\mathbb{C}_T$. Therefore, for a morphism $\overline{f} := [\langle t_\beta \rangle_{\beta < \mu}] : [\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda}] \to [\{x_\beta : \Omega_\beta\}_{\beta < \mu}]$ in order to define $\psi_T$ on the associated operator, it is enough to assume that $\mu$ is a successor ordinal. Firstly, we need to make choices for the contexts and

125