**Definition 4.36.** Let $\mathcal{C}: \mathcal{M}^{\text{coop}} \to \mathcal{C}at$ be a dTT natural model with telescopes. We say $\mathcal{C}$ has type display if it is equipped with

1. An internal strict CwF morphism:

$$(-)^d: (\widehat{\mathbf{\Theta}}_{\triangle\square})^*\text{Tel}_{sm,1} \to \text{Tel}^2_{sm}$$

2. An equality between the composite $(\widehat{\mathbf{\Theta}}_{\triangle\square})^*\text{Tel}_{sm} \xrightarrow{(-)^d} \text{Tel}^2_{sm} \xrightarrow{(-)_o} \text{Tel}_{sm}$ and the key transformation $(-)[\widehat{\mathbf{\Theta}}_{\triangle\square} \leqslant 1_{sm}]: (\widehat{\mathbf{\Theta}}_{\triangle\square})^*\text{Tel}_{sm} \to \text{Tel}_{sm}$.
3. If a length-1 telescope $A$ is non-modal, then the telescope $A^d$ is a single non-modal type.
4. If a length-1 telescope $A$ is nontrivially modal, then the telescope $A^d$ is empty.

Note that, like definition 4.35, this definition includes décalage. It represents the rules for display from sections 2.4.1 and 2.4.3, and the rules for computing décalage on a telescope extended by a type from section 2.4.4. Of course, with both telescope display and type display we want them to be compatible.

**Definition 4.37.** Let $\mathcal{C}: \mathcal{M}^{\text{coop}} \to \mathcal{C}at$ be a dTT natural model with telescope display. We say it has complete display if the restriction of $(-)^d: (\widehat{\mathbf{\Theta}}_{\triangle\square})^*\text{Tel}_{sm} \to \text{Tel}^2_{sm}$ to $(\widehat{\mathbf{\Theta}}_{\triangle\square})^*\text{Tel}_{sm,1}$ is an internal strict CwF morphism such that

- Items 3 and 4 of definition 4.36 hold.
- The rules in section 2.6.2 for computing meta-abstracted décalage in terms of type display hold.
- The rules in section 2.6.5 for computing meta-abstracted telescope display in terms of type display hold.

Finally, we add the compatibility conditions with type-formers:

**Definition 4.38.** Let $\mathcal{C}: \mathcal{M}^{\text{coop}} \to \mathcal{C}at$ be a dTT natural model with telescopes, décalage, telescope display, and type display. We say that display respects $\Pi$-types (respectively universes) if the rules in section 2.4.5 hold.

This completes the description of the abstract categorical semantics of the theory of section 2: it is a dTT natural model with telescopes and complete display that respects $\Pi$-types and universes. However, as noted in section 2, when telescopes are lists of types, as they almost always are, much of this structure can be deduced from the rest.

**Theorem 4.39.** Let $\mathcal{C}$ be a dTT natural model, with telescopes defined from types as in theorem 4.7, and with type display defined relative to these telescopes. Then there is a unique way to extend this type display on $\mathcal{C}$ to complete display.

*Proof.* The rules in section 2.6 for computing telescope display and décalage in terms of type display uniquely determine those operations when telescopes are defined as lists of types. $\square$

78