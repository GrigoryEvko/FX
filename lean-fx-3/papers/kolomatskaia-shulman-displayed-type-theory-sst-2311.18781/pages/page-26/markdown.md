### 2.6.3 Telescope display

We also need a notion of indexed display for telescopes. Note that this always gives a strict telescope, even if its input is not.

$$\frac{\Gamma, \widehat{\mathbf{\Omega}}_{\triangle\square} \vdash_{\mathrm{sm}} \Upsilon \operatorname{tel}_{\ell} \qquad \Gamma \vdash_{\mathrm{sm}} \sigma : \Upsilon [ \mathbf{\mathcal{Q}}^{\triangle\square \leqslant 1_{\mathrm{sm}}} ]}{\Gamma \vdash_{\mathrm{sm}} (\Upsilon^{\mathrm{d}} \sigma) \operatorname{stel}_{\ell}} \qquad \frac{\Gamma, \widehat{\mathbf{\Omega}}_{\triangle\square} \vdash_{\mathrm{sm}} \Upsilon \operatorname{tel}_{\ell} \qquad \Gamma, \widehat{\mathbf{\Omega}}_{\triangle\square} \vdash_{\mathrm{sm}} \sigma : \Upsilon}{\Gamma \vdash_{\mathrm{sm}} \sigma^{\mathrm{d}} : (\Upsilon^{\mathrm{d}} (\sigma [ \mathbf{\mathcal{Q}}^{\triangle\square \leqslant 1_{\mathrm{sm}}} ]))}$$

Like décalage, telescope display computes on empty telescopes, and on telescopes extended by a type:

$$()_{\mathrm{sm}}^{\mathrm{d}} [ ]_{\mathrm{sm}} \equiv ()_{\mathrm{sm}}$$

$$[ ]_{\mathrm{sm}}^{\mathrm{d}} \equiv [ ]_{\mathrm{sm}}$$

$$(\theta : \Theta, x : A)^{\mathrm{d}} [ \sigma, t ] \equiv (\theta' : \Theta^{\mathrm{d}} \sigma, x' : (( A ))_{\theta : \Theta^{\mathrm{d}}} \langle \sigma, \theta' \rangle t)$$

$$[ \sigma, t ]^{\mathrm{d}} \equiv [ \sigma^{\mathrm{d}}, t^{\mathrm{d}} ] \quad (\text{for a non-modal variable})$$

$$(\theta : \Theta, x : ^{\triangle\circ\mu} A)^{\mathrm{d}} [ \sigma, t ] \equiv \Theta^{\mathrm{d}} \sigma$$

$$[ \sigma, t ]^{\mathrm{d}} \equiv \sigma^{\mathrm{d}} \quad (\text{for a modal variable})$$

As promised, this is the reason that the empty telescope must exist at all levels: if $\Upsilon$ consists only of modal variables, then $\Upsilon^{\mathrm{d}}$ is empty, but it must be at the same level as $\Upsilon$.

Note that compared to décalage, telescope display reorders the variables. For instance, we have

$$(x : A, y : B)^{\mathrm{D}} \equiv (x : A, x' : A^{\mathrm{d}} x, y : B, y' : B^{\mathrm{d}} y)$$

$$(x : A, y : B)^{\mathrm{d}} \equiv (( x' : A^{\mathrm{d}} x, y' : B^{\mathrm{d}} y ))_{x : A, y : B}$$

$$(x : A, y : B) \mid (x : A, y : B)^{\mathrm{d}} \equiv (x : A, y : b, x' : A^{\mathrm{d}} x, y' : B^{\mathrm{d}} y)$$

$$\not\equiv (x : A, y : B)^{\mathrm{D}}.$$

Thus, we instead relate telescope display to décalage by an 'odds' operation that picks out the elements of displayed types, and a 'pairing' operation that interleaves them together, such that evens and odds together form an isomorphism with pairing as inverse.

$$\frac{\Gamma \vdash_{\mathrm{sm}} \sigma^{+} : \Upsilon^{\mathrm{D}}}{\Gamma \vdash_{\mathrm{sm}} \sigma^{+\mathrm{od}} : \Upsilon^{\mathrm{d}} \sigma^{\mathrm{ev}}} \qquad \frac{\Gamma \vdash_{\mathrm{sm}} \sigma : \Upsilon [ \mathbf{\mathcal{Q}}^{\triangle\square \leqslant 1_{\mathrm{sm}}} ] \qquad \Gamma \vdash_{\mathrm{sm}} \sigma' : \Upsilon^{\mathrm{d}} \sigma}{\Gamma \vdash_{\mathrm{sm}} \langle \sigma, \sigma' \rangle : \Upsilon^{\mathrm{D}}}$$

$$\sigma^{+} \equiv \langle \sigma^{+\mathrm{ev}}, \sigma^{+\mathrm{od}} \rangle \qquad \langle \sigma, \sigma' \rangle^{\mathrm{ev}} \equiv \sigma \qquad \langle \sigma, \sigma' \rangle^{\mathrm{od}} \equiv \sigma'$$

$$\sigma^{\mathrm{D \, od}} \equiv \sigma^{\mathrm{d}} \qquad \langle \sigma [ \mathbf{\mathcal{Q}}^{\triangle\square \leqslant 1_{\mathrm{sm}}} ], \sigma^{\mathrm{d}} \rangle \equiv \sigma^{\mathrm{D}}$$

These operations also compute on empty telescopes and on telescopes extended by a type:

$$[ ]_{\mathrm{sm}}^{\mathrm{od}} \equiv [ ]_{\mathrm{sm}}$$

$$\langle [ ]_{\mathrm{sm}}, [ ]_{\mathrm{sm}} \rangle \equiv [ ]_{\mathrm{sm}}$$

$$[ \sigma^{+}, t, t' ]^{\mathrm{od}} \equiv [ \sigma^{+\mathrm{od}}, t' ] \quad (\text{for a non-modal variable})$$

$$\langle [ \sigma, t ], [ \sigma', t' ] \rangle \equiv [ \langle \sigma, \sigma' \rangle, t, t' ] \quad (\text{for a non-modal variable})$$

$$[ \sigma^{+}, t ]^{\mathrm{od}} \equiv \sigma^{+\mathrm{od}} \quad (\text{for a modal variable})$$

$$\langle [ \sigma, t ], \sigma' \rangle \equiv [ \langle \sigma, \sigma' \rangle, t ] \quad (\text{for a modal variable})$$

26