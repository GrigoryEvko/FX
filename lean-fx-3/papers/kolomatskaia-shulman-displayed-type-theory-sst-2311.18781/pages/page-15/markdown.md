With the exceptional rule $\mathcal{Q}^{\triangle\diamond\geqslant 1_{sm}}$, which represents the fact that semantically $\mathcal{Q}_{\triangle\diamond}$ acts as the identity on flat contexts:

$$\frac{\Gamma \text{ flat}}{\mathcal{Q}^{\triangle\diamond\geqslant 1_{sm}} : \Gamma \Rightarrow_{\text{sm}} (\Gamma, \mathcal{Q}_{\triangle\diamond})}$$

In practice, it is useful to iterate the weakening rule and combine it with the lock and key rules to obtain the following rule:

$$\frac{\theta : \Gamma \Rightarrow_q \Theta \quad \mu \leqslant \text{locks}(\Upsilon)}{[\theta, \uparrow_\mu^\Upsilon] : (\Gamma, \Upsilon) \Rightarrow_p (\Theta, \mathcal{Q}_\mu)}$$

In fact, we will generally use named variables and leave weakening implicit.

◁

### 2.2.3 Types

These are defined by several classes of type formers, including, at the most basic level: $\Pi$-types (parametrised by a modality, as in MTT), universes (at each mode), and modal operators.

$$\frac{\Gamma, \mathcal{Q}_\mu \vdash_p A \text{ type}_{\ell_1} \quad \Gamma, x :^\mu A \vdash_q B \text{ type}_{\ell_2}}{\Gamma \vdash_q (x :^\mu A) \to B \text{ type}_{\ell_1 \sqcup \ell_2}}$$

$$\frac{\ell \text{ level}}{\Gamma \vdash_{dm} \text{Disc}_\ell \text{ type}_{\text{lsuc } \ell}}$$

$$\frac{\ell \text{ level}}{\Gamma \vdash_{sm} \text{Type}_\ell \text{ type}_{\text{lsuc } \ell}}$$

$$\frac{\Gamma, \mathcal{Q}_\square \vdash_{sm} A \text{ type}_\ell}{\Gamma \vdash_{dm} \square A \text{ type}_\ell}$$

$$\frac{\Gamma, \mathcal{Q}_\triangle \vdash_{dm} A \text{ type}_\ell}{\Gamma \vdash_{sm} \triangle A \text{ type}_\ell}$$

$$\frac{\Gamma, \mathcal{Q}_\diamond \vdash_{sm} A \text{ type}_\ell}{\Gamma \vdash_{dm} \diamond A \text{ type}_\ell}$$

We don't bother with primitive modal operators $\triangle\diamond$ or $\triangle\square$, since they can be obtained up to isomorphism by composing the others.

We will work with Tarski style universes, and thus require a decoding operation:

$$\frac{\Gamma \vdash_{dm} A : \text{Disc}_\ell}{\Gamma \vdash_{dm} \text{EI } A \text{ type}_\ell}$$

$$\frac{\Gamma \vdash_{sm} A : \text{Type}_\ell}{\Gamma \vdash_{sm} \text{EI } A \text{ type}_\ell}$$

Finally, we also have types that arise from substitution:

$$\frac{\theta : \Gamma \Rightarrow_p \Theta \quad \Theta \vdash_p A \text{ type}_\ell}{\Gamma \vdash_p A [\theta] \text{ type}_\ell}$$

As usual, substitution will be 'eliminable' in that $A [\theta]$ is always equal to something not involving $[\theta]$, but in the GAT presentation it is one of the generating rules like the others. ◁

### 2.2.4 Terms

Terms are defined for each class of type former through introduction and elimination rules. But first, we have variables. There are two rules for variables: the ordinary one from MTT,

15