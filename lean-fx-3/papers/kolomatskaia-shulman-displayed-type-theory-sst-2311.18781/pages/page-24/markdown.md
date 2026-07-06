$$\frac{\Gamma \vdash \Upsilon \operatorname{tel}_{\ell_0} \quad \Gamma \mid (\upsilon : \Upsilon) \vdash \Theta \operatorname{tel}_{\ell_1} \quad \Gamma \mid (\upsilon : \Upsilon) \mid (\theta : \Theta) \vdash \Phi \operatorname{tel}_{\ell_2}}{((\upsilon : \Upsilon) \rightarrow (\Theta \mid \Phi)) \equiv (\delta : (\upsilon : \Upsilon) \rightarrow \Theta \mid \epsilon : (\upsilon : \Upsilon) \rightarrow (\Phi \mid 1_\Gamma \mid \upsilon \mid \delta \upsilon \mid))}$$

$$\lambda \upsilon. [\theta \mid \phi] \equiv [\lambda \upsilon. \theta \mid \lambda \upsilon. \phi]$$

When telescopes are definitionally lists of types, these rules suffice to compute any $\Pi$-telescope in terms of $\Pi$-types. Note that in the rule $((\xi : ()_p) \rightarrow \Theta) \equiv \Theta$, the '$\Theta$' on the right-hand side must be implicitly lifted to the maximum of the levels of $()_p$ and $\Theta$.

## 2.6 DISPLAYED TELESCOPES

The structure in section 2.4, with display acting on types and décalage on telescopes, is sufficient to determine the behavior of display. However, in practice we will also need a notion of dependent décalage and display for telescopes. When telescopes are lists of types, this is determined (like ordinary décalage) by display for types.

### 2.6.1 Meta-abstracted décalage

$$\frac{\Gamma, \widehat{\mathbf{Q}}_{\triangle\square} \vdash_{\mathrm{sm}} \Phi \operatorname{tel}_{\ell_1 / \upsilon : \Upsilon}}{\Gamma \vdash_{\mathrm{sm}} \Phi^D \operatorname{tel}_{\ell_1 / \upsilon^+ : \Upsilon^D}} \quad \frac{\Gamma, \widehat{\mathbf{Q}}_{\triangle\square} \vdash_{\mathrm{sm}} \Phi \operatorname{tel}_{\ell_1 / \upsilon : \Upsilon} \quad \Gamma, \widehat{\mathbf{Q}}_{\triangle\square} \vdash_{\mathrm{sm}} \tau : \Phi}{\Gamma \vdash_{\mathrm{sm}} \tau^D : \Phi^D}$$

$$\frac{\Gamma, \widehat{\mathbf{Q}}_{\triangle\square} \vdash_{\mathrm{sm}} \Phi \operatorname{tel}_{\ell_1 / \upsilon : \Upsilon} \quad \Gamma \vdash_{\mathrm{sm}} \tau^+ : \Phi^D}{\Gamma \vdash_{\mathrm{sm}} \tau^{+\mathrm{ev}} : \left( \left( \Phi \mid \widehat{\mathbf{Q}}_{\triangle\square \in 1_{\mathrm{sm}}} \right) \right)_{\upsilon^+ : \Upsilon^D}}$$

$$\frac{\Gamma, \widehat{\mathbf{Q}}_{\triangle\square} \vdash_{\mathrm{sm}} \Phi \operatorname{tel}_{\ell_1 / \upsilon : \Upsilon} \quad \Gamma, \widehat{\mathbf{Q}}_{\triangle\square} \vdash_{\mathrm{sm}} \sigma : \Upsilon}{\Gamma \vdash_{\mathrm{sm}} \Phi^D \sigma^D \equiv (\Phi \sigma)^D} \tag{2.1}$$

$$\frac{\Gamma, \widehat{\mathbf{Q}}_{\triangle\square} \vdash_{\mathrm{sm}} \Phi \operatorname{tel}_{\ell_1 / \upsilon : \Upsilon} \quad \Gamma, \widehat{\mathbf{Q}}_{\triangle\square} \vdash_{\mathrm{sm}} \sigma : \Upsilon \quad \Gamma, \widehat{\mathbf{Q}}_{\triangle\square} \vdash_{\mathrm{sm}} \tau : \Phi}{\Gamma \vdash_{\mathrm{sm}} \tau^D \sigma^D \equiv (\tau \sigma)^D}$$

$$\frac{\Gamma, \widehat{\mathbf{Q}}_{\triangle\square} \vdash_{\mathrm{sm}} \Phi \operatorname{tel}_{\ell_1 / \upsilon : \Upsilon} \quad \Gamma \vdash_{\mathrm{sm}} \sigma^+ : \Upsilon^D \quad \Gamma \vdash_{\mathrm{sm}} \tau : \Phi}{\Gamma \vdash_{\mathrm{sm}} \tau^{D \cdot \mathrm{ev}} \sigma^+ \equiv \tau \sigma^{+\mathrm{ev}}}$$

We also require that this operation reduce to ordinary décalage on constant meta-abstractions, and commute appropriately with telescope concatenation, both globally and inside further meta-abstractions.

$$\frac{\Gamma, \widehat{\mathbf{Q}}_{\triangle\square} \vdash_{\mathrm{sm}} \Upsilon \operatorname{tel}_{\ell_0} \quad \Gamma, \widehat{\mathbf{Q}}_{\triangle\square} \vdash_{\mathrm{sm}} \Phi \operatorname{tel}_{\ell_1} \quad \Gamma \vdash_{\mathrm{sm}} \sigma^+ : \Upsilon^D}{\Gamma \vdash_{\mathrm{sm}} ((\Phi))_{\upsilon : \Upsilon^D} \sigma^+ \equiv \Phi^D}$$

$$\frac{\Gamma, \widehat{\mathbf{Q}}_{\triangle\square} \vdash_{\mathrm{sm}} \Upsilon \operatorname{tel}_{\ell_0} \quad \Gamma, \widehat{\mathbf{Q}}_{\triangle\square} \vdash_{\mathrm{sm}} \Phi \operatorname{tel}_{\ell_1} \quad \Gamma \vdash_{\mathrm{sm}} \sigma^+ : \Upsilon^D \quad \Gamma \vdash_{\mathrm{sm}} \delta : \Phi}{\Gamma \vdash_{\mathrm{sm}} [\![ \delta ]\!]_{\upsilon : \Upsilon^D} \sigma^+ \equiv \delta^D}$$

$$\frac{\Gamma, \widehat{\mathbf{Q}}_{\triangle\square} \vdash_{\mathrm{sm}} \Upsilon \operatorname{tel}_{\ell_0} \quad \Gamma, \widehat{\mathbf{Q}}_{\triangle\square} \mid \Upsilon \vdash_{\mathrm{sm}} \Phi \operatorname{tel}_{\ell_1}}{(\Upsilon \mid \Phi)^D \equiv \left( (\upsilon^+ : \Upsilon^D) \mid ((\Phi))_{\upsilon : \Upsilon^D} \upsilon^+ \right)} \tag{2.2}$$

24