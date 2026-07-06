morphism. However, the definition does not depend on these choices because of (1) from theorem A.22. This allows us to define $\psi_T$ as

$$\psi_T(\overline{f}) := t_\mu$$

where $t_\mu : \Omega_\mu[t_\beta|x_\beta]_{\beta<\mu}$.

**Lemma B.29.** *The function $\psi_T$ is an interpretation from $U(\mathbb{C}_T) \to T$.*

*Proof.* We need to check that rules and axioms are preserved by $\psi_T$. It will be enough to deal with the case where $\lambda = \nu + 1$. Suppose that $\overline{A_\lambda}$ has

$$\frac{\{x_\alpha : \overline{A_\alpha}(x_\delta)_{\delta<\alpha}\}_{\alpha<\nu}}{\overline{A_\nu}(x_\alpha)_{\alpha<\nu} \text{ Type}}$$

Furthermore, we assume that $\{x_\alpha : \Delta_\alpha\}_{\alpha<\lambda}$ is such that $A_\lambda = [\{x_\alpha : \Delta_\alpha\}_{\alpha<\lambda}]$. By definition,

$$\widehat{\psi_T} \left( \frac{\{x_\alpha : \overline{A_\alpha}(x_\delta)_{\delta<\alpha}\}_{\alpha<\nu}}{\overline{A_\lambda}(x_\alpha)_{\alpha<\lambda} \text{ Type}} \right) = \frac{\{x_\alpha : \Delta_\alpha\}_{\alpha<\nu}}{\Delta_\nu \text{ Type}}.$$

This is obviously a derived rule of $T$. Preservation of the rule for operator symbols is straightforward.

**Lemma B.30.** *For any generalized $\kappa$-algebraic theory $T$ we have $\psi_T \circ \varphi_T \approx Id_T$.*

*Proof.* From theorem A.29 it is enough to verify the statement on type element judgments. Let $\{x_\alpha : \Delta_\alpha\}_{\alpha<\lambda} \vdash t : \Delta_\lambda$ a type element judgment. For any $\alpha \le \lambda$ we denote $A_\alpha := [\{x_\delta : \Delta_\delta\}_{\delta\le\alpha}]$. It follows from theorem B.25 that

$$\widehat{\varphi_T} \left( \frac{\{x_\alpha : \Delta_\alpha\}_{\alpha<\lambda}}{t : \Delta_\lambda} \right) \approx \frac{\{x_\alpha : \overline{A_\alpha}\}_{\alpha<\lambda}}{[\langle x_\alpha, t \rangle_{\alpha<\lambda}] : \overline{A_\lambda}(x_\alpha)_{\alpha<\lambda}}.$$

Hence

$$\widehat{\psi_T} \left( \widehat{\varphi_T} \left( \frac{\{x_\alpha : \Delta_\alpha\}_{\alpha<\lambda}}{t : \Delta_\lambda} \right) \right) \approx \widehat{\psi_T} \left( \frac{\{x_\alpha : \overline{A_\alpha}\}_{\alpha<\lambda}}{[\langle x_\alpha, t \rangle_{\alpha<\lambda}] : \overline{A_\lambda}(x_\alpha)_{\alpha<\lambda}} \right) = \frac{\{x_\alpha : \Delta_\alpha\}_{\alpha<\lambda}}{t : \Delta_\lambda}.$$

$\square$

**Lemma B.31.** *For any generalized $\kappa$-algebraic theory $T$ we have $\psi_T \circ \varphi_T \approx Id_T$.*

126