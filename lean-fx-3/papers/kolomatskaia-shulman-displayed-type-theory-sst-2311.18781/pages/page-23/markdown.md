$$\frac{\Gamma \vdash \Upsilon \text{ tel}_{\ell_0} \quad \Gamma \mid \Upsilon \vdash \Phi \text{ tel}_{\ell_1}}{\Gamma \vdash (\Upsilon \mid \Phi) \text{ tel}_{\ell_0 \sqcup \ell_1}} \quad \frac{\Gamma \vdash \sigma : \Upsilon \quad \Gamma \vdash \delta : \Phi [1_\Gamma \mid \sigma]}{\Gamma \vdash [\sigma \mid \delta] : (\Upsilon \mid \Phi)} \quad \frac{\Gamma \vdash \theta : (\Upsilon \mid \Phi)}{\Gamma \vdash \theta_0 : \Upsilon}$$

$$\frac{\Gamma \vdash \theta : (\Upsilon \mid \Phi)}{\Gamma \vdash \theta_1 : \Phi \theta_0} \quad [\sigma \mid \delta]_0 \equiv \sigma \quad [\sigma \mid \delta]_1 \equiv \delta \quad [\theta_0 \mid \theta_1] \equiv \theta$$

$$(\Gamma \mid (\Upsilon \mid \Phi)) \equiv ((\Gamma \mid \Upsilon) \mid \Phi) \quad (\Upsilon \mid ()_p) \equiv \Upsilon \quad (\Upsilon \mid (\Phi, x :^\mu A)) \equiv ((\Upsilon \mid \Phi), x :^\mu A)$$

Note that to be at the right universe level, in the rule $(\Upsilon \mid ()_p) \equiv \Upsilon$, the right-hand side '$\Upsilon$' must be implicitly lifted to $\ell_0 \sqcup \ell_1$.

### 2.5.3 $\Pi$-telescopes

To define the copointed endofunctors whose coalgebras are display inductive types, we will need $\Pi$-telescopes. For simplicity, we require that the codomain be a strict telescope; this suffices for our application. The basic rules are just like those for $\Pi$-types.

$$\frac{\Gamma \vdash \Upsilon \text{ tel}_{\ell_0} \quad \Gamma \mid (v : \Upsilon) \vdash \Theta \text{ stel}_{\ell_1}}{\Gamma \vdash (v : \Upsilon) \rightarrow \Theta \text{ stel}_{\ell_0 \sqcup \ell_1}} \quad \frac{\Gamma \mid (v : \Upsilon) \vdash \theta : \Theta}{\Gamma \vdash \lambda v. \theta : (v : \Upsilon) \rightarrow \Theta}$$

$$\frac{\Gamma \vdash \delta : (v : \Upsilon) \rightarrow \Theta \quad \Gamma \vdash \sigma : \Upsilon}{\Gamma \vdash \delta \sigma : \Theta [1_\Gamma \mid \sigma]} \quad \frac{\Gamma \mid (v : \Upsilon) \vdash \theta : \Theta \quad \Gamma \vdash \sigma : \Upsilon}{\Gamma \vdash (\lambda v. \theta) \sigma \equiv \theta [1_\Gamma \mid \sigma]}$$

$$\frac{\Gamma \vdash \delta : (v : \Upsilon) \rightarrow \Theta \quad \Gamma \vdash \delta' : (v : \Upsilon) \rightarrow \Theta \quad \Gamma \mid (v : \Upsilon) \vdash \delta v \equiv \delta' v}{\Gamma \vdash \delta \equiv \delta'}$$

In addition, we assert computation laws for $\Pi$-telescopes when the domain or codomain is an extension.

$$\frac{\Gamma \vdash \Upsilon \text{ tel}_\ell}{((v : \Upsilon) \rightarrow ()_p) \equiv ()_p} \quad \frac{\Gamma \vdash \Theta \text{ stel}_\ell}{((\xi : ()_p) \rightarrow \Theta) \equiv \Theta}$$

$$\lambda v. []_p \equiv []_p \quad \lambda (v : ()_p). \theta \equiv \theta$$

$$\frac{\Gamma \vdash \Upsilon \text{ tel}_{\ell_0} \quad \Gamma \mid (v : \Upsilon) \vdash \Theta \text{ stel}_{\ell_1} \quad \Gamma \mid (v : \Upsilon) \mid (\theta : \Theta) \vdash B \text{ type}_{\ell_2}}{((v : \Upsilon) \rightarrow (\Theta, y : B)) \equiv (\delta : (v : \Upsilon) \rightarrow \Theta, \epsilon : (v : \Upsilon) \rightarrow B [1_\Gamma \mid v \mid \delta v])}$$

$$\lambda v. [\theta, b] \equiv [\lambda v. \theta, \lambda v. b]$$

$$\frac{\Gamma \vdash_q \Upsilon \text{ tel}_{\ell_0} \quad \Gamma \mid (v : \Upsilon), \text{ }_\mu \vdash_p A \text{ type}_{\ell_1} \quad \Gamma \mid (v : \Upsilon), x :^\mu A \vdash_q \Theta \text{ tel}_{\ell_2}}{((v : \Upsilon, x :^\mu A) \rightarrow \Theta) \equiv ((v : \Upsilon) \rightarrow (x :^\mu A) \rightarrow \Theta)}$$

$$\lambda (v : (\Upsilon \mid A)). \theta \equiv \lambda v. \lambda x. \theta$$

23