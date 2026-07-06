- If $f: A_\lambda \to B_{\mu+1}$, let $\rho_\mu: B_{\mu+1} \twoheadrightarrow B_\mu$ be the display map. Then the operator symbol has introductory rule:

$$\{x_\alpha: \overline{A}_\alpha\}_{\alpha<\lambda} \vdash \overline{f}(x_\alpha)_{\alpha<\lambda}: \overline{(\rho_\mu f)^* B_{\mu+1}}(x_\alpha)_{\alpha<\lambda}.$$

This does not clash with the notation from the previous point since it always refer to an object of $\mathcal{C}$ and in this case refers to a map.

Subject to the following axioms in $U(\mathcal{C})$:

1. Let $A_\lambda, B_\mu, C_{\nu+1}$ be objects of $\mathcal{C}$ and maps $f: A_\lambda \to B_\mu, g: B_\mu \to C_{\nu+1}$:

$$\{x_\alpha: \overline{A}_\alpha\}_{\alpha<\lambda} \vdash \overline{gf}(x_\alpha)_{\alpha<\lambda} \equiv_{\overline{(p_\nu gf)^* C_{\nu+1}}(x_\alpha)_{\alpha<\lambda}} \overline{g}(\overline{p_\beta f}(x_\alpha)_{\alpha<\lambda})_{\beta<\mu}.$$

2. Let $B_\mu$ be a non-trivial object of $\mathcal{C}$. For each $\delta < \mu$ we have

$$\{x_\beta: \overline{B}_\beta\}_{\beta<\mu} \vdash \overline{p_\delta}(x_\beta)_{\beta<\mu} \equiv_{\overline{B}_\delta(x_\beta)_{\beta<\delta}} x_\delta.$$

3. Let $A_\lambda, B_{\mu+1}$ objects of $\mathcal{C}$ and a map $f: A_\lambda \to B_\mu$ then

$$\{x_\alpha: \overline{A}_\alpha\}_{\alpha<\lambda} \vdash \overline{f^* B_{\mu+1}}(x_\alpha)_{\alpha<\lambda} \equiv \overline{B_{\mu+1}}(\overline{p_\beta f}(x_\alpha)_{\alpha<\lambda})_{\beta<\mu}$$

and

$$\{x_\alpha: \overline{A}_\alpha, x_\delta: \overline{f^* B_{\mu+1}}(x_\alpha)_{\alpha<\lambda}\}_{\alpha<\lambda} \vdash \overline{q(f, B_{\mu+1})}(x_\alpha, x_\delta)_{\alpha<\lambda} \equiv_{\overline{f^* B_\mu}(x_\alpha)_{\alpha<\lambda}} x_\delta.$$

Observation B.16. It is immediate to observe that $U(\mathcal{C})$ as defined is a $\kappa$-pretheory. We have type and operator symbols introduced by the type and type element judgments respectively. Note that the list of axioms we provided are well-formed rules. This is because the premise of each axiom is by definition a context.

Remark B.17. If $f: A_\lambda \to B_\mu$ is a map in $\mathcal{C}$, where $\mu$ is a limit ordinal, i.e., $B_\mu$ is a limit object, then we get a family of maps $\{f_\nu: A_\lambda \to B_\nu\}_{\nu<\mu}$. Therefore, the associated operator $\overline{f}$ is uniquely determined by the family of operators $\overline{f_\nu}$, for which in this case we can assume that $\nu$ is a successor ordinal.

If $F: \mathcal{C} \to \mathcal{D}$ is a functor between $\kappa$-contextual categories, then we need an interpretation $U(F): U(\mathcal{C}) \to U(\mathcal{D})$;

1. For an object $A_\lambda$, the interpretation is defined as

$$U(F)(\overline{A_\lambda}) := \overline{FA_\lambda}(x_\alpha)_{\alpha<\lambda}.$$

119