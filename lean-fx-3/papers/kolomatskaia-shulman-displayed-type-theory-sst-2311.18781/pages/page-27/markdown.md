# 2.6.4 Meta-abstracted telescope display

Unsurprisingly, we generalise telescope display to apply to meta-abstracted telescopes as well, with rules combining those of sections 2.4.3 and 2.6.3. First we have the basic rules:

$$\frac{\Gamma, \widehat{\mathbf{a}}_{\triangle \square} \vdash_{\mathrm{sm}} \Phi \operatorname{tel}_{\ell_1 / \nu : \Upsilon}}{\Gamma \vdash_{\mathrm{sm}} \Phi^{\mathrm{d}} \operatorname{stel}_{\ell_1 / \nu^{+} : \Upsilon^{\mathrm{D}}, \Phi : \Phi [ \mathbf{a}_{\mathbf{c}}^{\triangle \square \leqslant 1_{\mathrm{sm}}} ] \nu^{+\mathrm{ev}}}$$

$$\frac{\Gamma, \widehat{\mathbf{a}}_{\triangle \square} \vdash_{\mathrm{sm}} \Phi \operatorname{tel}_{\ell_1 / \nu : \Upsilon} \quad \Gamma, \widehat{\mathbf{a}}_{\triangle \square} \vdash_{\mathrm{sm}} \delta : \Phi}{\Gamma \vdash_{\mathrm{sm}} \delta^{\mathrm{d}} : \left( \left( \Phi^{\mathrm{d}} \nu^{+} (\delta \nu^{+\mathrm{ev}}) \right) \right)_{\nu^{+} : \Upsilon^{\mathrm{D}}}}$$

$$\frac{\Gamma, \widehat{\mathbf{a}}_{\triangle \square} \vdash_{\mathrm{sm}} \Phi \operatorname{tel}_{\ell_1 / \nu : \Upsilon} \quad \Gamma, \widehat{\mathbf{a}}_{\triangle \square} \vdash_{\mathrm{sm}} \sigma : \Upsilon \quad \Gamma \vdash_{\mathrm{sm}} t : (\Phi \sigma) [ \mathbf{a}_{\mathbf{c}}^{\triangle \square \leqslant 1_{\mathrm{sm}}} ]}{\Gamma \vdash_{\mathrm{sm}} \Phi^{\mathrm{d}} \sigma^{\mathrm{D}} t \equiv (\Phi \sigma)^{\mathrm{d}} t}$$

$$\frac{\Gamma, \widehat{\mathbf{a}}_{\triangle \square} \vdash_{\mathrm{sm}} \Phi \operatorname{tel}_{\ell_1 / \nu : \Upsilon} \quad \Gamma, \widehat{\mathbf{a}}_{\triangle \square} \vdash_{\mathrm{sm}} \sigma : \Upsilon \quad \Gamma, \widehat{\mathbf{a}}_{\triangle \square} \vdash_{\mathrm{sm}} t : \Phi}{\Gamma \vdash_{\mathrm{sm}} t^{\mathrm{d}} \sigma^{\mathrm{D}} \equiv (t \sigma)^{\mathrm{d}}}$$

Then we have the odds/pairing isomorphism:

$$\frac{\Gamma, \widehat{\mathbf{a}}_{\triangle \square} \vdash_{\mathrm{sm}} \Phi \operatorname{tel}_{\ell_1 / \nu : \Upsilon} \quad \Gamma \vdash_{\mathrm{sm}} \delta^{+} : \Phi^{\mathrm{D}}}{\Gamma \vdash_{\mathrm{sm}} \delta^{+\mathrm{od}} : \left( \left( \Phi^{\mathrm{d}} \nu^{+} (\delta^{+\mathrm{ev}} \nu^{+}) \right) \right)_{\nu^{+} : \Upsilon^{\mathrm{D}}}}$$

$$\frac{\Gamma, \widehat{\mathbf{a}}_{\triangle \square} \vdash_{\mathrm{sm}} \Phi \operatorname{tel}_{\ell_1 / \nu : \Upsilon}}{\Gamma \vdash_{\mathrm{sm}} \delta : \left( \left( \Phi [ \mathbf{a}_{\mathbf{c}}^{\triangle \square \leqslant 1_{\mathrm{sm}}} ] \nu^{+\mathrm{ev}} \right) \right)_{\nu^{+} : \Upsilon^{\mathrm{D}}} \quad \Gamma \vdash_{\mathrm{sm}} \delta' : \left( \left( \Phi^{\mathrm{d}} \nu^{+} (\delta \nu^{+}) \right) \right)_{\nu^{+} : \Upsilon^{\mathrm{D}}}}{\Gamma \vdash_{\mathrm{sm}} \langle \delta, \delta' \rangle : \Phi^{\mathrm{D}}}$$

$$\delta \equiv \langle \delta^{\mathrm{ev}}, \delta^{\mathrm{od}} \rangle \quad \langle \delta, \delta' \rangle^{\mathrm{ev}} \equiv \delta \quad \langle \delta, \delta' \rangle^{\mathrm{od}} \equiv \delta'$$

$$\delta^{\mathrm{D \, od}} \equiv \delta^{\mathrm{d}} \quad \langle \delta [ \mathbf{a}_{\mathbf{c}}^{\triangle \square \leqslant 1_{\mathrm{sm}}} ], \delta^{\mathrm{d}} \rangle \equiv \delta^{\mathrm{D}}$$

On constant meta-abstractions, this reduces to ordinary telescope display:

$$\frac{\Gamma, \widehat{\mathbf{a}}_{\triangle \square} \vdash_{\mathrm{sm}} \Upsilon \operatorname{tel}_{\ell_0}}{\Gamma, \widehat{\mathbf{a}}_{\triangle \square} \vdash_{\mathrm{sm}} \Phi \operatorname{tel}_{\ell_1} \quad \Gamma \vdash_{\mathrm{sm}} \sigma^{+} : \Upsilon^{\mathrm{D}} \quad \Gamma \vdash_{\mathrm{sm}} \delta : \Phi [ \mathbf{a}_{\mathbf{c}}^{\triangle \square \leqslant 1_{\mathrm{sm}}} ] \sigma^{+} ]}{\Gamma \vdash_{\mathrm{sm}} \left( (\Phi) \right)_{\nu : \Upsilon^{\mathrm{d}}} \sigma^{+} \delta \equiv \Phi^{\mathrm{d}} \delta}$$

$$\frac{\Gamma, \widehat{\mathbf{a}}_{\triangle \square} \vdash_{\mathrm{sm}} \Upsilon \operatorname{tel}_{\ell_0}}{\Gamma, \widehat{\mathbf{a}}_{\triangle \square} \vdash_{\mathrm{sm}} \Phi \operatorname{tel}_{\ell_1} \quad \Gamma \vdash_{\mathrm{sm}} \sigma^{+} : \Upsilon^{\mathrm{D}} \quad \Gamma \vdash_{\mathrm{sm}} \delta : \Phi [ \mathbf{a}_{\mathbf{c}}^{\triangle \square \leqslant 1_{\mathrm{sm}}} ] \sigma^{+} ]}{\Gamma \vdash_{\mathrm{sm}} \left[ \left[ \delta \right] \right]_{\nu : \Upsilon^{\mathrm{d}}} \sigma^{+} \equiv \delta^{\mathrm{d}}}$$

27