$$\frac{\Gamma, \mathbf{\Omega}_{\triangle\square} \mid \Upsilon \vdash_{\mathrm{sm}} \Phi \operatorname{tel}_{\ell_1} \quad \Gamma, \mathbf{\Omega}_{\triangle\square} \vdash_{\mathrm{sm}} \sigma : \Upsilon \quad \Gamma, \mathbf{\Omega}_{\triangle\square} \vdash_{\mathrm{sm}} \delta : \Phi \left[ 1_\Gamma, \mathbf{\Omega}_{\triangle\square} \mid \sigma \right]}{\left[ \sigma \mid \delta \right]^D \equiv \left[ \sigma^D \mid \delta^D \right]} \tag{2.3}$$

$$\frac{\Gamma, \mathbf{\Omega}_{\triangle\square} \mid \Theta \vdash_{\mathrm{sm}} \Upsilon \operatorname{tel}_{\ell_1} \quad \Gamma, \mathbf{\Omega}_{\triangle\square} \mid \Theta \mid \Upsilon \vdash_{\mathrm{sm}} \Phi \operatorname{tel}_{\ell_2}}{\left( \left( (\Upsilon \mid \Phi) \right) \right)_{\theta : \Theta}^D \equiv \left( \left( (\upsilon^+ : (\Upsilon))_{\theta : \Theta}^D \theta^+) \mid (\Phi)_{\theta : \Theta, \upsilon : \Upsilon}^D \theta^+ \upsilon^+ \right) \right)_{\theta^+ : \Theta^D}}$$

$$\frac{\Gamma, \mathbf{\Omega}_{\triangle\square} \mid \Theta \vdash_{\mathrm{sm}} \sigma : \Upsilon \quad \Gamma, \mathbf{\Omega}_{\triangle\square} \mid \Theta \vdash_{\mathrm{sm}} \delta : \Phi \left[ 1_\Gamma, \mathbf{\Omega}_{\triangle\square} \mid 1_\Theta \mid \sigma \right]}{\left[ \left[ \sigma \mid \delta \right] \right]_{\theta : \Theta}^D \equiv \left[ \left[ \left[ \sigma \right] \right]_{\theta : \Theta}^D \theta^+ \mid \left[ \left[ \delta \right] \right]_{\theta : \Theta}^D \theta^+ \right]_{\theta^+ : \Theta^D}}$$

Note that in (2.2) we have to meta-abstract $\Phi$ in order to apply décalage, since $\Phi$ itself is not in a $\triangle\square$-locked context. In (2.3), $\delta^D$ is supposed to inhabit $(\Phi)_{\upsilon : \Upsilon}^D \sigma^D$, but by (2.1) and $\beta$-reduction for meta-abstractions this is equal to $(\Phi \left[ 1_\Gamma \mid \sigma \right])^D$, which is the natural type of $\delta^D$. The last two equations are similar.

**Remark 2.4.** The rules for telescope décalage from section 2.4.2 and this section should be compared with the 'local theory' from [ACKS24], with telescopes and telescope concatenation replacing types and $\Sigma$-types. The $\Upsilon^D$ from section 2.4.2 corresponds to their $\forall A$, while the $(\Phi)_{\Upsilon}^D$ from this section corresponds to their $\forall d(x, B)$. The $\sigma^D$ from section 2.4.2 corresponds to their R (although with an added modal lock), while the $[\delta]_{\upsilon : \Upsilon}^D$ from this section corresponds to their apd (with modal lock). We don't have their ap represented explicitly, but one of their rules says it is equivalent to apd in a constant family. Our $e^v$ is their k (in the unary case, so k = 0), and we do not have their S; as discussed before, the modal guards make symmetry unnecessary. And, of course, we don't have $\Pi$-telescopes or a universe; we have those only for display, which is indexed.

### 2.6.2 Computing meta-abstracted décalage

Like ordinary décalage, meta-abstracted décalage computes on telescopes that are made out of types. For brevity we omit the typing premises of these equalities, but we emphasize that all the meta-variables on the left-hand sides such as $\Theta, A, \sigma, t$ can depend nontrivially on the abstraction variables $\upsilon$ or $\upsilon^+$.

$$\left( \left( \theta : \Theta, x : A \right) \right)_{\upsilon : \Upsilon}^D \equiv \left( \left( \theta^+ : \left( \left( \Theta \right) \right)_{\upsilon : \Upsilon}^D \upsilon^+, x : A \left[ \mathbf{\Omega}_{\mathbf{e}}^{\triangle\square \leqslant 1_{\mathrm{sm}}} \mid \upsilon^{+\mathrm{ev}} \mid \theta^{+\mathrm{ev}} \right. \right. \right. \cup^+,$$

$$x' : \left( \left( A \right) \right)_{\upsilon : \Upsilon \mid \theta : \Theta}^d \upsilon^+ \theta^+ x \right) \right)_{\upsilon^+ : \Upsilon^D}$$

$$\left[ \left[ \sigma, t \right] \right]_{\upsilon : \Upsilon}^D \equiv \left[ \left[ \left[ \sigma \right] \right]_{\upsilon : \Upsilon}^D \upsilon^+, \left[ \left[ t \right] \right]_{\upsilon : \Upsilon} \upsilon^{+\mathrm{ev}}, \left[ \left[ t \right] \right]_{\upsilon : \Upsilon}^d \upsilon^+ \right]_{\upsilon^+ : \Upsilon^D}$$

$$\left[ \left[ \sigma^+, t, t' \right] \right]_{\upsilon^+ : \Upsilon^D}^{\mathrm{ev}} \equiv \left[ \left[ \sigma^{+\mathrm{ev}}, t \right] \right]_{\upsilon^+ : \Upsilon^D}$$

$$\left( \left( \theta : \Theta, x :^{\triangle\circ\mu} A \right) \right)_{\upsilon : \Upsilon}^D \equiv \left( \left( \theta^+ : \left( \left( \Theta \right) \right)_{\upsilon : \Upsilon}^D \upsilon^+, \right. \right.$$

$$x :^{\triangle\circ\mu} A \left[ \mathbf{\Omega}_{\mathbf{e}}^{\triangle\square \leqslant 1_{\mathrm{sm}}} \mid \upsilon^{+\mathrm{ev}} \mid \theta^{+\mathrm{ev}} \right. \left. \left. \mathbf{\Omega}_{\triangle\circ\mu} \right] \right) \right)_{\upsilon^+ : \Upsilon^D}$$

$$\left[ \left[ \sigma, t \right] \right]_{\upsilon : \Upsilon}^D \equiv \left[ \left[ \left[ \sigma \right] \right]_{\upsilon : \Upsilon}^D \upsilon^+, \left[ \left[ t \right] \right]_{\upsilon : \Upsilon} \upsilon^{+\mathrm{ev}} \right]_{\upsilon^+ : \Upsilon^D}$$

$$\left[ \left[ \sigma^+, t \right] \right]_{\upsilon^+ : \Upsilon^D}^{\mathrm{ev}} \equiv \left[ \left[ \sigma^{+\mathrm{ev}}, t \right] \right]_{\upsilon^+ : \Upsilon^D}$$

◁

25