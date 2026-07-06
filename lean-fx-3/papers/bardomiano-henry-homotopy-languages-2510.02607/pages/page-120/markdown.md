2. For a morphism $f: A_\lambda \to B_{\mu+1}$, the operator $\overline{f}$ is interpreted as

$$U(F)(\overline{f}) := \overline{F(f)}(x_\alpha)_{\alpha < \lambda}.$$

The next step is to prove that this is indeed a map between the generalized $\kappa$-algebraic theories, this is done in [Car78, pp 2.29]. For this, it is enough to show that rules and axioms of $U(\mathcal{C})$ are sent to rules of $U(\mathcal{D})$. The functoriality of $U: \kappa$-CON $\to \kappa$-GAT is also immediate from its definition. This is tested on each type and operator symbol. It is then enough to take the equivalence class $[U(F)]$.

### B.3.3 The natural isomorphism $U \circ \mathbb{C} \cong Id_{\kappa-GAT}$

For each $T \in \kappa$-GAT we want to define an interpretation $[\varphi_T]: T \to U(\mathbb{C}_T)$, we do this by defining a preinterpretation $\varphi_T: Exp(T) \to Exp(U(\mathbb{C}_T))$:

1. If $\Delta$ is a type symbol of $T$ with introduction rule

$$\{x_\alpha : \Delta_\beta\}_{\beta < \mu} \vdash \Delta(x_\beta)_{\beta < \mu} \text{ Type}$$

then

$$\varphi_T(\Delta) := \overline{[\{x_\beta : \Delta_\beta, x_\delta : \Delta(x_\beta)_{\beta < \mu}\}_{\beta < \mu}]}(x_\beta)_{\beta < \mu}$$

2. If $f$ is an operator symbol with introductory rule

$$\{x_\alpha : \Delta_\beta\}_{\beta < \mu} \vdash f(x_\beta)_{\beta < \mu}: \Delta,$$

then

$$\varphi_T(f) := \overline{[\langle x_\beta, f(x_\beta)_{\beta < \mu} \rangle_{\beta < \mu}]}(x_\beta)_{\beta < \mu},$$

where $\langle x_\beta, f(x_\beta)_{\beta < \mu} \rangle_{\beta < \mu}$ is the morphism $\{x_\alpha : \Delta_\beta\}_{\beta < \mu} \to \{x_\alpha : \Delta_\beta, x_\delta : \Delta\}_{\beta < \mu}$.

We proceed to verify that as defined $\varphi_T: T \to U(\mathbb{C}_T)$ is an interpretation as defined. This is a crucial point in the proof, so we spell out some details in theorem B.26. The results below are the technical steps towards it.

Lemma B.18. If $\mathcal{C}$ is a contextual category, objects $A_\lambda$, $B_\mu$ and $f: A_\lambda \to B_\mu$ is map with $\mu = \nu + 1$ (in particular it is non-trivial), then the rule

$$\{x_\alpha : \overline{A}_\alpha(x_\gamma)_{\gamma < \alpha}\}_{\alpha < \lambda} \vdash \overline{f}(x_\alpha)_{\alpha < \lambda}: \overline{B_\mu}(\overline{p_\beta \circ f}(x_\alpha)_{\alpha < \lambda})_{\beta < \mu}$$

is a derived rule of $U(\mathcal{C})$.

120