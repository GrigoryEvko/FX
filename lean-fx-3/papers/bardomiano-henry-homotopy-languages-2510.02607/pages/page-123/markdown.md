**Corollary B.24.** If $T$ is a generalized $\kappa$-algebraic theory, $\{x_\beta : B_\beta\}_{\beta < \mu}$ is a context, $\nu < \mu$ and

$$f_\nu := [\langle t_\beta \rangle_{\beta < \nu} ] : [\{x_\alpha : A_\alpha\}_{\alpha < \lambda}] \to [\{x_\beta : B_\beta\}_{\beta < \nu}]$$

is a map in $\mathbb{C}_T$ then;

1.

$$\frac{\{x_\alpha : \overline{A_\alpha}(x_\delta)_{\delta < \alpha}\}_{\alpha < \lambda}}{[\{x_\alpha, x_\gamma : B_\gamma[t_\delta|x_\delta]_{\delta < \gamma}\}_{\substack{\alpha < \lambda \\ \nu \leq \gamma < \mu}}\}(x_\alpha)_{\alpha < \lambda} \equiv [\{x_\beta : B_\beta\}_{\beta < \nu}](\overline{g_\beta}(x_\alpha)_{\alpha < \lambda})_{\beta < \nu}}$$

where for each $\beta < \nu$ the map $g_\beta := [\langle x_\alpha, t_\beta \rangle_{\alpha < \lambda}]$.

2. If for all $\gamma$, with $\nu < \gamma < \mu$, the rule

$$\{x_\beta : B_\beta\}_{\beta < \nu}, \{t_{\gamma'} : B_{\gamma'}\}_{\gamma' < \gamma} \vdash t_\gamma : B_\gamma$$

is a derived rule then

$$\{x_\alpha : \overline{A_\alpha}(x_\delta)_{\delta < \alpha}\}_{\alpha < \lambda} \vdash [\langle x_\alpha, t_\gamma[t_{\gamma'} \mid x_{\gamma'}]_{\gamma' < \gamma} \rangle_{\substack{\alpha < \lambda \\ \nu < \gamma < \mu}}\equiv \overline{h}(\overline{g_\beta}(x_\alpha)_{\alpha < \lambda})_{\beta < \nu}$$

where $g_\beta$ is defined as in the previous point and $h := [\langle x_\beta, t_\gamma \rangle_{\substack{\beta < \nu \\ \nu < \gamma < \mu}}]$.

Proof. This is a direct application of theorem B.23. We remark that the assumption of point (2) simply gives us an element of $\Gamma(B_\nu^\mu)$ and the map on the left depends on variables that, according to our convention, we leave implicit. □

The following lemma is key to prove that we have an interpretation $\varphi_T : T \to U(\mathbb{C}_T)$, the results above are used to prove:

**Lemma B.25.** If $T$ is a generalized $\kappa$-algebraic theory then:

1. If $\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash \Delta$ Type is a type judgment of $T$, then the rule

$$\{x_\alpha : \overline{A_\alpha}(x_\delta)_{\delta < \alpha}\}_{\alpha < \lambda} \vdash \overline{A}(x_\alpha)_{\alpha < \lambda + 1} \equiv \widetilde{\varphi_T}(\Delta)$$

is a derived rule of $U(\mathbb{C}_T)$ where $A := \{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda + 1}$ and $A_\alpha := \{x_\delta : \Delta_\delta\}_{\delta \leq \alpha}$.

2. If $\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash t : \Delta$ is a type element judgment of $T$, then the rule

$$\{x_\alpha : \overline{A_\alpha}(x_\delta)_{\delta < \alpha}\}_{\alpha < \lambda} \vdash \overline{\langle x_\alpha, t \rangle_{\alpha < \lambda}}(x_\alpha)_{\alpha < \lambda + 1} \equiv_{\overline{A}(x_\alpha)_{\alpha < \lambda}} \widetilde{\varphi_T}(t)$$

is a derived rule of $U(\mathbb{C}_T)$.

123