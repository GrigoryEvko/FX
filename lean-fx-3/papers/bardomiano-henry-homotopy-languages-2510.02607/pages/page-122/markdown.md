Proof. This by induction on the height of $p_\nu$. When it is a successor ordinal, this is the previous lemma. When it is a limit ordinal $B_\mu$ is a limit object, therefore the result reduces to the inductive hypothesis, which is the successor case again. □

Recall from section B.2 we defined the set of maps $\Gamma(B)$. It follows from the previous result that

Corollary B.21. If $\mathcal{C}$ is a $\kappa$-contextual category and $f: A_\lambda \to B_\mu$ is a map in $\mathcal{C}$, then for all $\nu < \mu$

$$\{x_\alpha: A_\alpha(x_\delta)_{\delta < \alpha}\}_{\alpha < \lambda} \vdash \overline{\delta_f^\nu}(x_\alpha)_{\alpha < \lambda} \equiv \overline{f}(x_\alpha)_{\alpha < \lambda}.$$

is a derived rule of $U(\mathcal{C})$.

If we specialize theorem B.21 to the syntactic $\kappa$-contextual category of a generalized $\kappa$-algebraic theory $T$, then

Corollary B.22. Assume that $\{x_\beta: B_\beta\}_{\beta < \mu}$ is a context, $\nu < \mu$ and

$$f_\nu := [\langle t_\beta \rangle_{\beta < \nu}]: [\{x_\alpha: A_\alpha\}_{\alpha < \lambda}] \to [\{x_\beta: B_\beta\}_{\beta < \nu}]$$

a map in $\mathbb{C}_T$ then

$$\{x_\alpha: \overline{A_\alpha}(x_\gamma)_{\gamma < \alpha}\}_{\alpha < \lambda} \vdash [\langle x_\alpha, t_\varepsilon \rangle_{\substack{\alpha < \lambda \\ \nu \leq \varepsilon < \mu}}] \equiv [\langle t_\beta, t_\varepsilon \rangle_{\beta < \nu \leq \varepsilon < \mu}]$$

is a derived rule of $U(\mathbb{C}_T)$.

Proof. This follows from theorem B.21 and the explicit description of $\delta_{f_\nu}^\nu$ given in theorem B.9. □

Lemma B.23. If $A_\lambda, B_\mu$ are objects and $f_\nu: A_\lambda \to B_\nu$, with $\nu < \mu$, is a map in a $\kappa$-contextual category $\mathcal{C}$, then:

1. The rule

$$\{x_\alpha: \overline{A_\alpha}(x_\delta)_{\delta < \alpha}\}_{\alpha < \lambda} \vdash \overline{f_\nu^* B_\mu}(x_\alpha)_{\alpha < \lambda} \equiv \overline{B}(\delta_{(p_\gamma f)}^\gamma(x_\alpha)_{\alpha < \lambda})_{\gamma < \nu}$$

is a derived rule of $U(\mathcal{C})$.

2. If $g: \Gamma(B_\nu^\mu)$ then the rule

$$\{x_\alpha: \overline{A_\alpha}(x_\delta)_{\delta < \alpha}\}_{\alpha < \lambda} \vdash \overline{\delta_{gf}^\nu}(x_\alpha)_{\alpha < \lambda} \equiv \overline{\delta_g^\nu}(\overline{\delta_{p_\gamma f}}^\gamma(x_\alpha)_{\alpha < \lambda})_{\gamma < \nu}$$

is a derived rule of $U(\mathcal{C})$.

122