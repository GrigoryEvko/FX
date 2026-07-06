And we have computation rules for telescope extensions:

$$\frac{\Gamma, \mathbf{\Omega}_{\triangle\square} \vdash_{\mathrm{sm}} \Upsilon \operatorname{tel}_{\ell_0}}{\Gamma, \mathbf{\Omega}_{\triangle\square} \mid \Upsilon \vdash_{\mathrm{sm}} \Phi \operatorname{tel}_{\ell_1} \quad \Gamma \vdash_{\mathrm{sm}} \sigma : \Upsilon [ \mathbf{a}_{\mathbf{\Phi}}^{\triangle\square \leqslant 1_{\mathrm{sm}}} ] \quad \Gamma \vdash_{\mathrm{sm}} \delta : \Phi [ \mathbf{a}_{\mathbf{\Phi}}^{\triangle\square \leqslant 1_{\mathrm{sm}}} \mid \sigma ]} (\Upsilon \mid \Phi)^d \sigma \delta \equiv ((\upsilon' : \Upsilon^d \sigma) \mid ((\Phi))_{\upsilon : \Upsilon^d} \langle \sigma, \upsilon' \rangle \delta)$$

$$\frac{\Gamma, \mathbf{\Omega}_{\triangle\square} \mid \Upsilon \vdash_{\mathrm{sm}} \Phi \operatorname{tel}_{\ell_1} \quad \Gamma, \mathbf{\Omega}_{\triangle\square} \vdash_{\mathrm{sm}} \Upsilon \operatorname{tel}_{\ell_0}}{[ \sigma \mid \delta ]^d \equiv [ \sigma^d \mid \delta^d ]}$$

$$\frac{\Gamma, \mathbf{\Omega}_{\triangle\square} \mid \Theta \vdash_{\mathrm{sm}} \Upsilon \operatorname{tel}_{\ell_0} \quad \Gamma, \mathbf{\Omega}_{\triangle\square} \mid \Theta \mid \Upsilon \vdash_{\mathrm{sm}} \Phi \operatorname{tel}_{\ell_1}}{(((\Upsilon \mid \Phi)))_{\theta : \Theta^d} \equiv (((\upsilon' : ((\Upsilon))_{\theta : \Theta^d} \theta^+ \upsilon) \mid ((\Phi))_{\theta : \Theta, \upsilon : \Upsilon^d} \theta^+ \langle \upsilon, \upsilon' \rangle \phi))_{\theta^+ : \Theta^D, \upsilon : \Upsilon, \phi : \Phi}}$$

$$\frac{\Gamma, \mathbf{\Omega}_{\triangle\square} \mid \Theta \vdash_{\mathrm{sm}} \sigma : \Upsilon \quad \Gamma, \mathbf{\Omega}_{\triangle\square} \mid \Theta \vdash_{\mathrm{sm}} \delta : \Phi [ 1_\Gamma, \mathbf{\Omega}_{\triangle\square} \mid 1_\Theta \mid \sigma ]}{[ [ \sigma \mid \delta ]]_{\theta : \Theta^d} \equiv [ [ [ \sigma ]]_{\theta : \Theta^d} \theta^+ \mid [ [ \delta ]]_{\theta : \Theta^d} \theta^+ ]_{\theta^+ : \Theta^D}} \triangleleft$$

### 2.6.5 Computing meta-abstracted telescope display

These computation rules are analogous to the previous ones, first in the non-modal case:

$$((\theta : \Theta, x : A))_{\upsilon : \Upsilon^d} [ \sigma^+ \mid \delta, t ] \equiv (\theta' : ((\Theta))_{\upsilon : \Upsilon^d} \sigma^+ \delta,$$

$$x' : ((\mathcal{A}))_{\upsilon : \Upsilon, \theta : \Theta^d} \sigma \langle \delta, \theta' \rangle t)$$

$$[ [ \delta, t ]]_{\upsilon : \Upsilon^d} \sigma^+ \equiv [ [ [ \delta ]]_{\upsilon : \Upsilon^d} \sigma^+, [ [ t ]]_{\upsilon : \Upsilon^d} \sigma^+ ]$$

$$[ [ \delta^+, t, t']]_{\upsilon^+ : \Upsilon^D^{od}} \sigma^+ \equiv [ [ [ \delta^+ ]]_{\upsilon^+ : \Upsilon^D^{od}} \sigma^+, [ [ t']]_{\upsilon^+ : \Upsilon^D} \sigma^+ ]$$

$$\langle [ [ \delta, t ]]_{\upsilon^+ : \Upsilon^D}, [ [ \delta', t']]_{\upsilon^+ : \Upsilon^D} \rangle \sigma^+ \equiv [ \langle [ [ \delta ]]_{\upsilon^+ : \Upsilon^D}, [ [ \delta']]_{\upsilon^+ : \Upsilon^D} \rangle \sigma^+,$$

$$[ [ t ]]_{\upsilon^+ : \Upsilon^D} \sigma^+, [ [ t']]_{\upsilon^+ : \Upsilon^D} \sigma^+ ]$$

and then the modal case:

$$((\theta : \Theta, x : \triangle\circ\mu \mathcal{A}))_{\upsilon : \Upsilon^d} [ \sigma^+ \mid \delta, t ] \equiv ((\Theta))_{\upsilon : \Upsilon^d} \sigma^+ \delta$$

$$[ [ \delta, t ]]_{\upsilon : \Upsilon^d} \sigma^+ \equiv [ [ \delta ]]_{\upsilon : \Upsilon^d} \sigma^+$$

$$[ [ \delta, t ]]_{\upsilon^+ : \Upsilon^D^{od}} \sigma^+ \equiv [ [ \delta ]]_{\upsilon^+ : \Upsilon^D^{od}} \sigma^+$$

$$\langle [ [ \delta, t ]]_{\upsilon^+ : \Upsilon^D}, [ [ \delta']]_{\upsilon^+ : \Upsilon^D} \rangle \sigma^+ \equiv [ \langle [ [ \delta ]]_{\upsilon^+ : \Upsilon^D}, [ [ \delta']]_{\upsilon^+ : \Upsilon^D} \rangle \sigma^+,$$

$$[ [ t ]]_{\upsilon^+ : \Upsilon^D} \sigma^+ ]$$

### 2.6.6 Computing display on $\Pi$-telescopes

Finally, we give the following rules for computing display and meta-abstracted display of a $\Pi$-telescope. These are consistent with the rules for computing display on telescopes extended by a type.

$$((\phi : \Phi) \to \Theta \phi)^d \delta \equiv (\phi^+ : \Phi^D) \to \Theta^d \phi^{+ev} (\delta \phi^{+ev})$$

$$((\phi : \Phi \upsilon) \to \Theta \upsilon \phi))_{\upsilon : \Upsilon^d}$$

$$\equiv ((\phi^+ : \Phi^D \upsilon^+) \to \Theta^d \upsilon^+ \phi^+ (\delta \phi^{+ev}))_{\upsilon^+ : \Upsilon^D, \delta : (\phi : \Phi \upsilon^{+ev}) \to \Theta \upsilon^{+ev} \phi}$$

28