1. If $\{x_\beta : \Omega_\beta\}_{\beta < \mu} \vdash \Omega \text{ Type}$ and $\{x_\beta : \Omega'_\beta\}_{\beta < \mu} \vdash \Omega' \text{ Type}$ are derived judgment of the theory such that

$$\{x_\beta : \Omega_\beta, x_\mu : \Omega\}_{\beta < \mu} \approx \{x_\beta : \Omega'_\beta, x_\mu : \Omega'\}_{\beta < \mu}$$

then

$$\{x_\alpha : \Delta_\alpha, x_\mu : \Omega[t_\beta|x_\beta]_{\beta < \mu}\}_{\alpha < \lambda} \approx \{x_\alpha : \Delta'_\alpha, x_\mu : \Omega'[t'_\beta|x'_\beta]_{\beta < \mu}\}_{\alpha < \lambda}$$

This follows by unwinding the relation $\approx$ and applying the principle 12 in theorem A.4. This simply means that we can extend contexts by a fresh variable. Moreover, there is a more general result:

For all $\varepsilon > 0$, if $\{x_\beta : \Omega_\beta\}_{\beta < \mu + \varepsilon}$ and $\{x_\beta : \Omega'_\beta\}_{\beta < \mu + \varepsilon}$ are contexts then

$$\{x_\alpha : \Delta_\alpha, x_\beta : \Omega_\beta[t_\gamma|x_\gamma]_{\gamma < \beta}\}_{\substack{\alpha < \lambda, \\ \mu \leq \beta < \mu + \varepsilon}} \approx \{x_\alpha : \Delta'_\alpha, x_\beta : \Omega'_\beta[t'_\gamma|x_\gamma]_{\gamma < \beta}\}_{\substack{\alpha < \lambda, \\ \mu \leq \beta < \mu + \varepsilon}}$$

2. If $\{x_\beta : \Omega_\beta\}_{\beta < \mu} \vdash s : \Omega$ and $\{x_\beta : \Omega'_\beta\}_{\beta < \mu} \vdash s' : \Omega'$ are derived judgment such that

$$\{x_\beta : \Omega_\beta\}_{\beta < \mu} \vdash s \equiv_\Omega s'.$$

Then

$$\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \vdash s[t_\beta|x_\beta]_{\beta < \mu} \equiv_{\Omega[t_\beta|x_\beta]_{\beta < \mu}} s'[t'_\beta|x_\beta]_{\beta < \mu}.$$

Observe that the principle 13 from theorem A.4 implies this result.

*Remark A.22.* 1. Let $\langle t_\beta \rangle_{\beta < \mu} : \{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \to \{x_\beta : \Omega_\beta\}_{\beta < \mu}$ be a morphism between two contexts. If

$$\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \approx \{x'_\alpha : \Delta'_\alpha\}_{\alpha < \lambda} \text{ and } \{x_\beta : \Omega_\beta\}_{\beta < \mu} \approx \{x'_\beta : \Omega'_\beta\}_{\beta < \mu}$$

then $\langle t_\beta \rangle_{\beta < \mu} : \{x'_\alpha : \Delta'_\alpha\}_{\alpha < \lambda} \to \{x'_\beta : \Omega'_\beta\}_{\beta < \mu}$ is also a morphism between these contexts.

2. If we have a context $\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda + 1}$ and $\{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \approx \{x'_\alpha : \Delta'_\alpha\}_{\alpha < \lambda}$ then we can extend the context $\{x'_\alpha : \Delta'_\alpha\}_{\alpha < \lambda}$ to $\{x'_\alpha : \Delta'_\alpha\}_{\alpha < \lambda + 1}$ such that $x'_\alpha : \Delta'_\alpha$ is $x_\lambda : \Delta_\lambda$.

*Remark A.23.* Let $\langle t_\beta \rangle_{\beta < \mu + 1} : \{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \to \{x_\beta : \Omega_\beta\}_{\beta < \mu + 1}$ and $\langle s_\beta \rangle_{\beta < \mu} : \{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \to \{x_\beta : \Omega_\beta\}_{\beta < \mu}$ be morphisms between contexts. Then we have a morphism

$$\langle s_\beta \rangle_{\beta < \mu + 1} : \{x_\alpha : \Delta_\alpha\}_{\alpha < \lambda} \to \{x_\beta : \Omega_\beta\}_{\beta < \mu + 1}$$

where $s_\mu \equiv t_\mu$, and such that $\{s_\beta\}_{\beta < \mu + 1} \approx \{t_\beta\}_{\beta < \mu + 1}$.

101