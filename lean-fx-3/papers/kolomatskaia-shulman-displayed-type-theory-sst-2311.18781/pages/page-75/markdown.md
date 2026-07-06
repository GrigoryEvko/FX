Our primary example is, of course, the following.

**Theorem 4.31.** *The simplicial model of sections 4.2 and 4.3 is a dTT natural model.*

*Proof.* Of course, we use the extended simplicial model along with the discrete model. We showed explicitly in section 4.3 that this yields a modal context structure for our $\mathcal{M}$. In the notation of that section, the object $1 \cdot \bullet$ referred to above is $((), \bullet) \equiv \text{in}_{\text{dm}}()$. The definition of the category $\text{sm}_+$ implies immediately that this object is subterminal and its slice category is the replete image (and even the literal image) of $\bullet$. Finally, in section 4.3.5 we verified the rules of $[\text{GCK}^+ 22]$ for $\diamond$ and $\square$, which as shown in *loc. cit.* are equivalent to their being dependent right adjoints of $\bullet$ and $\bullet$.

### 4.4.2 Telescopes

Modal telescopes generalise ordinary telescopes to modal natural models in a straightforward way. Let $\mathcal{M}$ be a 2-category.

**Definition 4.32.** A modal natural model $\mathcal{C} : \mathcal{M}^{\text{coop}} \to \mathcal{Cat}$ has telescopes if it is equipped with:

- For each $p \in \mathcal{M}$, a representable natural transformation $\text{tpr}_p : \text{PSub}_p \to \text{Tel}_p$, whose comprehensions we write as $(\gamma : \Gamma \mid \theta : \Theta \gamma)$.
- For each $p$, a morphism of polynomial functors $()_p : 1_{\mathcal{C}_p} \to \text{P}_{\text{tpr}_p}$.
- For any $\mu : p \to q$, a morphism of polynomial functors $\text{P}_{\text{tpr}_q} \circ \text{P}_{\bullet_{p} \circ \text{P}_{\text{p}}} \to \text{P}_{\text{tpr}_q}$ that we write as $(\theta : \Theta, x :^\mu A \theta)$.
- The rules $(\gamma : \Gamma \mid ()) = \Gamma$ and $(\gamma : \Gamma \mid (\upsilon : \Upsilon \gamma, x :^\mu A \gamma \upsilon)) = ((\gamma : \Gamma \mid \upsilon : \Upsilon), x :^\mu A \gamma \upsilon)$ from section 2.3.1 hold.
- A morphism of polynomial functors $\text{P}_{\text{tpr}} \circ \text{P}_{\text{tpr}} \to \text{P}_{\text{tpr}}$, which we write as $\Upsilon \mid \Phi$. (This says how to concatenate telescopes.)
- The rules $(\gamma : \Gamma \mid (\upsilon : \Upsilon \gamma \mid \phi : \Phi \gamma \upsilon)) = ((\gamma : \Gamma \mid \upsilon : \Upsilon \gamma) \mid \phi : \Phi \gamma \upsilon)$ and $(\upsilon : \Upsilon \mid ()) = \Upsilon$ and $(\upsilon : \Upsilon \mid (\phi : \Phi \upsilon, x :^\mu A \upsilon \phi)) = ((\upsilon : \Upsilon \mid \phi : \Phi \upsilon), x :^\mu A \upsilon \phi)$ from section 2.5.2 hold.

In addition, we say $\mathcal{C}$ has $\Pi$-telescopes if for each $p$ there is a pullback square

$$\begin{array}{ccc} \text{P}_{\text{tpr}_p}(\text{PSub}_p) & \longrightarrow & \text{PSub}_p \\ \downarrow_{\text{P}_{\text{tpr}_p}(\text{tpr}_p)} & \downarrow_{\Pi} & \downarrow_{\text{tpr}_p} \\ \text{P}_{\text{tpr}_p}(\text{Tel}_p) & \xrightarrow[\Pi]{} & \text{Tel}_p, \end{array}$$

such that the computation rules from section 2.5.3 hold.

As in sections 4.1.6 and 4.1.7, we can equip any modal natural model with telescopes and $\Pi$-telescopes, and interpret meta-abstracted types and telescopes automatically, without needing to discuss them explicitly.

75