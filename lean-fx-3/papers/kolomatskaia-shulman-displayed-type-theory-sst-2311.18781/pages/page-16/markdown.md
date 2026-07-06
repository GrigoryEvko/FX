and an 'exceptional' one arising, like the exceptional key $\mathbf{a}_{\bullet}^{\triangle\diamond\geqslant1_{sm}}$, from the fact that $\mathbf{a}_{\triangle\diamond}$ acts as the identity on flat contexts.

$$\frac{\mu \leqslant \text{locks}(\Theta)}{\Gamma, x:^{\mu}A, \Theta \vdash_q x: A [1_\Gamma, \uparrow_{\mu}^{x:^{\mu}A, \Theta}]}$$

$$\frac{\Gamma \text{ flat } \quad \text{locks}(\Theta) = 1_{sm}}{\Gamma, x:^{\triangle\diamond}A, \Theta \vdash_{sm} x: A [1_\Gamma, \uparrow_{\triangle\diamond}^{x:^{\triangle\diamond}A, \Theta}] [\mathbf{a}_{\bullet}^{\triangle\diamond\geqslant1_{sm}}]}$$

For $\Pi$-types, we have (as in MTT):

$$\frac{\Gamma, x:^{\mu}A \vdash_q t: B}{\Gamma \vdash_q \lambda x.t: (x:^{\mu}A) \to B}$$

$$\frac{\Gamma \vdash_q f: (x:^{\mu}A) \to B \quad \Gamma, \mathbf{a}_{\mu} \vdash_p a: A}{\Gamma \vdash_q f a: B [a/x]}$$

For universes, we have a coding function:

$$\frac{\Gamma \vdash_{dm} A \text{ type}_\ell}{\Gamma \vdash_{dm} \text{Code } A: \text{Disc}_\ell}$$

$$\frac{\Gamma \vdash_{sm} A \text{ type}_\ell}{\Gamma \vdash_{sm} \text{Code } A: \text{Type}_\ell}$$

For the modal operators, we have an introduction rule and negative 'Fitch-style' elimination rules. Following [GCK$^+$22], we formulate these using parametric adjoints in the mode theory. As noted in section 2.1, the safe modalities have actual left adjoints, so their rules simplify as in [Shu23]. And for $\mathbf{a}_{\diamond}$, we have observed that its parametric left adjoint is defined on the flat contexts, and on those it coincides with $\mathbf{a}_{\triangle}$.

$$\frac{\Gamma, \mathbf{a}_{\square} \vdash_{sm} t: A}{\Gamma \vdash_{dm} \square t: \square A}$$

$$\frac{\Gamma, \mathbf{a}_{\triangle} \vdash_{dm} t: A}{\Gamma \vdash_{sm} \triangle t: \triangle A}$$

$$\frac{\Gamma, \mathbf{a}_{\diamond} \vdash_{sm} t: A}{\Gamma \vdash_{dm} \diamond t: \diamond A}$$

$$\frac{\Gamma, \mathbf{a}_{\triangle} \vdash_{dm} t: \square A}{\Gamma \vdash_{sm} \blacksquare^A t: A [\mathbf{a}_{\bullet}^{\triangle\square\leqslant1_{sm}}]}$$

$$\frac{\Gamma, \mathbf{a}_{\diamond} \vdash_{sm} t: \triangle A}{\Gamma \vdash_{dm} \blacktriangle^A t: A}$$

$$\frac{\Gamma \text{ flat } \quad \Gamma, \mathbf{a}_{\triangle} \vdash_{dm} t: \diamond A}{\Gamma \vdash_{sm} \blacklozenge^A t: A [\mathbf{a}_{\bullet}^{\triangle\diamond\geqslant1_{sm}}]}$$

Finally, we have terms that arise from substitution:

$$\frac{\theta: \Gamma \Rightarrow_p \Theta \quad \Theta \vdash_p t: A}{\Gamma \vdash_p t [\theta]: A [\theta]}$$

## 2.3 TELESCOPES AND META-ABSTRACTIONS, I

### 2.3.1 Telescopes

Telescopes are suffixes of contexts, with the restriction that they may not contain locks. The judgement $\Gamma \vdash_p \Theta \text{tel}_\ell$ denotes that $\Theta$ is a telescope in context $\Gamma$ of 'level $\ell$', where the latter means that $\ell$ is greater than or equal to the level of the types occurring in $\Theta$. We allow it to be strictly greater, and in particular allow an empty telescope to exist at all universe levels, for a reason to be explained in section 2.6.3. Formally, telescopes are an additional level-indexed sort of the GAT, with formation rules saying that there is an empty one and they can be built by concatenating types.

$$\frac{\Gamma \text{ctx}_p}{\Gamma \vdash_p ()_p \text{tel}_\ell}$$

$$\frac{\mu: p \to q \quad \Gamma \vdash_q \Theta \text{tel}_\ell \quad \Gamma \mid \Theta, \mathbf{a}_{\mu} \vdash_p A \text{type}_{\ell'} \quad \ell' \leqslant \ell}{\Gamma \vdash_q (\Theta, x:^{\mu}A) \text{tel}_\ell}$$

16