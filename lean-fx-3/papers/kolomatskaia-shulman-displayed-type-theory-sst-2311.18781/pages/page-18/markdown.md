This gives a simple way to ensure that partial substitutions are uniquely determined by their components: their equality is detected by equality of the induced substitutions.

$$\frac{\Gamma \vdash_{\mathrm{p}} \sigma : \Upsilon \qquad \Gamma \vdash_{\mathrm{p}} \tau : \Upsilon \qquad [1_{\Gamma} \mid \sigma] \equiv [1_{\Gamma} \mid \tau] : \Gamma \Rightarrow_{\mathrm{p}} (\Gamma \mid \Upsilon)}{\Gamma \vdash_{\mathrm{p}} \sigma \equiv \tau : \Upsilon}$$

Note that a partial substitution does, in fact, have 'components': given $\Gamma \vdash_{\mathrm{q}} \sigma : (\Upsilon, x :^{\mu} A)$ we have

$$[1_{\Gamma} \mid \sigma, x, \mathbf{\Omega}_{\mu}] : (\Gamma, \mathbf{\Omega}_{\mu}) \rightarrow (\Gamma \mid \Upsilon, x :^{\mu} A, \mathbf{\Omega}_{\mu})$$

$$\Gamma \mid \Upsilon, x :^{\mu} A, \mathbf{\Omega}_{\mu} \vdash x : A$$

$$\Gamma, \mathbf{\Omega}_{\mu} \vdash x [1_{\Gamma} \mid \sigma, x, \mathbf{\Omega}_{\mu}] : A$$

We also have a notion of weakening for telescopes. As before, we omit the equations that this must satisfy.

$$\frac{\Gamma \vdash \Theta \operatorname{tel}_{\ell}}{\uparrow^{\Theta} : (\Gamma \mid \Theta) \Rightarrow \Gamma} \qquad \uparrow^{(\cdot)_{\mathrm{p}}} \equiv 1_{\Gamma} \qquad \uparrow^{\Theta, x :^{\mu} A} \equiv \uparrow^{\Theta} \circ \uparrow^{x :^{\mu} A} \qquad \triangleleft$$

### 2.3.3 Meta-abstracted types and terms

We now introduce a new judgement form $\Gamma \vdash_{\mathrm{p}} A \operatorname{type}_{\ell_1} /_{\upsilon : \Upsilon}$, where $\Gamma \vdash \Upsilon \operatorname{tel}_{\ell_0}$. This should be thought of saying that $A$ is a type depending on the variables $\upsilon$ in $\Upsilon$, i.e. belonging to a 'framework-level $\Pi$-type' $A : (\upsilon : \Upsilon) \rightarrow \operatorname{type}_{\ell_1}$. Accordingly, elements of this judgment are introduced by binding and eliminated by application, with a $\beta$ and $\eta$-rule.

$$\frac{\Gamma \mid (\upsilon : \Upsilon) \vdash_{\mathrm{p}} A \operatorname{type}_{\ell_1}}{\Gamma \vdash_{\mathrm{p}} ((A))_{\upsilon : \Upsilon} \operatorname{type}_{\ell_1} /_{\upsilon : \Upsilon}} \qquad \frac{\Gamma \vdash_{\mathrm{p}} A \operatorname{type}_{\ell_1} /_{\upsilon : \Upsilon} \qquad \Gamma \vdash_{\mathrm{p}} \sigma : \Upsilon}{\Gamma \vdash_{\mathrm{p}} A \sigma \operatorname{type}_{\ell_1}}$$

$$\frac{\Gamma \mid (\upsilon : \Upsilon) \vdash_{\mathrm{p}} A \operatorname{type}_{\ell_1} \qquad \Gamma \vdash_{\mathrm{p}} \sigma : \Upsilon}{\Gamma \vdash_{\mathrm{p}} ((A))_{\upsilon : \Upsilon} \sigma \equiv A [1_{\Gamma} \mid \sigma]}$$

$$\frac{\Gamma \vdash_{\mathrm{p}} A \operatorname{type}_{\ell_1} /_{\upsilon : \Upsilon} \qquad \Gamma \vdash_{\mathrm{p}} B \operatorname{type}_{\ell_1} /_{\upsilon : \Upsilon} \qquad \Gamma \mid (\upsilon : \Upsilon) \vdash_{\mathrm{p}} A \upsilon \equiv B \upsilon}{\Gamma \vdash_{\mathrm{p}} A \equiv B}$$

We also regard $A \operatorname{type}_{\ell_1} /_{\upsilon : \Upsilon}$ as standing in for its own $\Pi$-type '$(\upsilon : \Upsilon) \rightarrow A \upsilon$'. Thus, such an $A$ can have its own terms belonging to it, which are also introduced by binding and eliminated by application, with a $\beta$ and $\eta$-rule.

$$\frac{\Gamma \vdash_{\mathrm{p}} A \operatorname{type}_{\ell_1} /_{\upsilon : \Upsilon} \qquad \Gamma \mid (\upsilon : \Upsilon) \vdash_{\mathrm{p}} t : A \upsilon}{\Gamma \vdash_{\mathrm{p}} [t]_{\upsilon : \Upsilon} : ((A))_{\upsilon : \Upsilon}}$$

$$\frac{\Gamma \vdash_{\mathrm{p}} A \operatorname{type}_{\ell_1} /_{\upsilon : \Upsilon} \qquad \Gamma \vdash_{\mathrm{p}} t : A \qquad \Gamma \vdash_{\mathrm{p}} \sigma : \Upsilon}{\Gamma \vdash_{\mathrm{p}} t \sigma : A \sigma \operatorname{type}_{\ell_1}}$$

$$\frac{\Gamma \vdash_{\mathrm{p}} A \operatorname{type}_{\ell_1} /_{\upsilon : \Upsilon} \qquad \Gamma \mid (\upsilon : \Upsilon) \vdash_{\mathrm{p}} t : A \upsilon \qquad \Gamma \vdash_{\mathrm{p}} \sigma : \Upsilon}{\Gamma \vdash_{\mathrm{p}} [t]_{\upsilon : \Upsilon} \sigma \equiv t [1_{\Gamma} \mid \sigma]}$$

$$\frac{\Gamma \vdash_{\mathrm{p}} A \operatorname{type}_{\ell_1} /_{\upsilon : \Upsilon} \qquad \Gamma \vdash_{\mathrm{p}} t : A \qquad \Gamma \vdash_{\mathrm{p}} s : A \qquad \Gamma \mid (\upsilon : \Upsilon) \vdash_{\mathrm{p}} t \upsilon \equiv s \upsilon}{\Gamma \vdash_{\mathrm{p}} t \equiv s} \qquad \triangleleft$$

18