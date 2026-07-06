### 4.3.5 Modal Types

Displayed Type Theory has two modal type formers that we need to model (recall that we omit $\triangle$ at present):

$$\frac{\gamma : \Gamma, \mathbf{\Omega}_{\diamond}^{+} \vdash_{\mathrm{sm}_{+}} A \gamma \text{ type}_{\ell}}{\gamma : \Gamma \vdash_{\mathrm{dm}} \diamond A \gamma \text{ type}_{\ell}}$$

$$\frac{\gamma : \Gamma, \mathbf{\Omega}_{\square}^{+} \vdash_{\mathrm{sm}_{+}} A \gamma \text{ type}_{\ell}}{\gamma : \Gamma \vdash_{\mathrm{dm}} \square A \gamma \text{ type}_{\ell}}$$

These come with the following intro and elimination forms:

$$\frac{\gamma : \Gamma, \mathbf{\Omega}_{\diamond}^{+} \vdash_{\mathrm{sm}_{+}} t \gamma : A \gamma}{\gamma : \Gamma \vdash_{\mathrm{dm}} \diamond t \gamma : \diamond A \gamma}$$

$$\frac{\gamma : \Gamma \vdash_{\mathrm{dm}} t \gamma : \diamond A \gamma}{\gamma : \text{in}_{\mathrm{dm}} \Gamma \vdash_{\mathrm{sm}_{+}} \blacklozenge^{A} t \gamma : A \gamma}$$

$$\frac{\gamma : \Gamma, \mathbf{\Omega}_{\square}^{+} \vdash_{\mathrm{sm}_{+}} t \gamma : A \gamma}{\gamma : \Gamma \vdash_{\mathrm{dm}} \square t \gamma : \square A \gamma}$$

$$\frac{\gamma : \Gamma, \mathbf{\Omega}_{\triangle}^{+} \vdash_{\mathrm{dm}} t \gamma : \square A \gamma}{\gamma : \Gamma \vdash_{\mathrm{sm}_{+}} \blacksquare^{A} t \gamma : A [\mathbf{\alpha}_{\Gamma}^{\triangle\square\leqslant 1_{\mathrm{sm}_{+}}} \gamma]}$$

Note that there is an asymmetry between the statements of laws for $\blacklozenge$ and $\blacksquare$. To clear up this confusion, we could have instead written:

$$\frac{\Gamma \text{ flat } \quad \gamma : \Gamma, \mathbf{\Omega}_{\triangle}^{+} \vdash_{\mathrm{dm}} t \gamma : \diamond A \gamma}{\gamma : \Gamma \vdash_{\mathrm{sm}_{+}} \blacklozenge^{A} t \gamma : A [\mathbf{\alpha}_{\Gamma}^{\triangle\diamond\diamond 1_{\mathrm{sm}_{+}}} \gamma]}$$

But this is entirely equivalent, because the semantic-side definition of the predicate $\Gamma$ flat is that $\Gamma$ is of the form $\text{in}_{\mathrm{dm}} \Delta$, in which case we have $((\text{in}_{\mathrm{dm}} \Delta), \mathbf{\Omega}_{\triangle}^{+}) \equiv \Delta$ by definition. Note that the key $\mathbf{\alpha}_{\Gamma}^{\triangle\diamond\diamond 1_{\mathrm{sm}_{+}}}$ does not arise from a natural transformation and is only defined when $\Gamma \equiv \text{in}_{\mathrm{dm}} \Delta$, in which case we simply have $\mathbf{\alpha}_{\text{in}_{\mathrm{dm}} \Delta}^{\triangle\diamond\diamond 1_{\mathrm{sm}_{+}}} \equiv \text{in}_{\mathrm{dm}} 1_{\Delta}$. The first definition can thus be seen as a proof-relevant pattern match along the flat predicate.

The definition of $\diamond$ and its introduction and elimination rules are done by shuffling around discrete information and inclusions:

$$\begin{array}{l} \diamond (\text{in}_{\mathrm{dm}} A) \equiv A \\ \diamond (\text{in}_{\mathrm{dm}} t) \equiv t \\ \blacklozenge^{A} t \equiv \text{in}_{\mathrm{dm}} t. \end{array}$$

For $\square$, we fall back to our prior construction for the type former and intro rule:

$$\begin{array}{l} \square (\text{in}_{\mathrm{sm}} A) \equiv \square_{\mathrm{sm}} A \\ \square (\text{in}_{\mathrm{sm}} t) \equiv \square_{\mathrm{sm}} t \end{array}$$

For the eliminator, we split on whether or not $\Gamma$ is flat:

$$\blacksquare^{\text{in}_{\mathrm{sm}} A} t \equiv \begin{cases} \text{in}_{\mathrm{dm}} (\blacksquare_{\mathrm{dm}}^{A} t) & \text{for } \text{in}_{\mathrm{dm}} \Gamma \\ \text{in}_{\mathrm{sm}} (\blacksquare_{\mathrm{dm}}^{A} t) & \text{for } \text{in}_{\mathrm{sm}} \Gamma \end{cases}$$

where the discrete case above is as follows:

$$\frac{\Gamma \text{ ob}_{\mathrm{dm}} \quad \gamma : \Gamma \vdash_{\mathrm{dm}} t \gamma : \lim A_{\square} \gamma}{\gamma : \Gamma \vdash_{\mathrm{dm}} \blacksquare_{\mathrm{dm}}^{A} t \gamma : A_{-1} \gamma}$$

It is defined by:

$$\blacksquare^{\text{in}_{\mathrm{sm}} A} t \equiv \text{res}^{-1} \gamma a$$

$\triangle$

71