6.2. YONEDA LEMMA AND APPLICATIONS

According to corollary 6.1.3.34, this data is equivalent to the one of

$$X \times \int_{C^{\iota}} y_{c} \to (\iota \times (C^{\iota})^{\sharp})^{*} \int_{X^{\sharp} \times C^{\iota}} \tilde{g}$$

where $\tilde{g}$ is the morphism defined by currying from $g^{\sharp}: X^{\sharp} \to \widehat{C}$. The proposition 6.2.1.10, and the equivalence (6.2.1.13) then induce an equivalence:

$$\mathrm{Hom}_{(\infty, \omega) \circ \mathrm{cat}_{\mathrm{m} / \widehat{C}^{\sharp}}}(E, \int_{\widehat{C}} \mathrm{hom}_{\widehat{C}}(y_{c}, \underline{\hspace{1cm}})) \sim \mathrm{Hom}_{(\infty, \omega) \circ \mathrm{cat}_{\mathrm{m} / \widehat{C}^{\sharp}}}(E, \int_{\widehat{C}} \mathrm{ev}(c, \underline{\hspace{1cm}}))$$

Walking through all the equivalences, we can easily see that when $E$ is $h_{y_{c}}^{\widehat{C}}$, this equivalence sends the upper horizontal morphism of (6.2.1.15) to the lower horizontal one. We then have an equivalence

$$\int_{\widehat{C}} \mathrm{hom}_{\widehat{C}}(y_{c}, \underline{\hspace{1cm}}) \sim \int_{\widehat{C}} \mathrm{ev}(c, \underline{\hspace{1cm}}).$$

that comes along with the desired commutative square.

**Theorem 6.2.1.16.** *The Yoneda embedding is fully faithful. As a consequence, every morphism $A \to \widehat{C}$ that is pointwise representable uniquely factors through the Yoneda embedding.*

*Proof.* We fix an object $c$ of $C$. By construction of the Yoneda embedding and the evaluation, we have an equivalence $\mathrm{ev}(c, y_{d}) \sim \mathrm{hom}_{C}(c, d)$ natural in $d: C$. Applying the Grothendieck deconstruction to the equivalence given in proposition 6.2.1.14, we then get an equivalence

$$\eta_{d}: \mathrm{hom}_{\widehat{C}}(y_{c}, y_{d}) \sim \mathrm{hom}_{C}(c, d)$$

natural in $d: C$ and that preserves the identity.

We also have a transformation

$$\mathrm{hom}_{y}(c, d): \mathrm{hom}_{C}(c, d) \to \mathrm{hom}_{\widehat{C}}(y_{c}, y_{d})$$

natural in $d: C$, that also preserves the identity. We then have constructed a natural transformation

$$\psi_{c, d}: \mathrm{hom}_{C}(c, d) \xrightarrow{\mathrm{hom}_{y}(c, d)} \mathrm{hom}_{\widehat{C}}(y_{c}, y_{d}) \xrightarrow{\eta_{d}} \mathrm{hom}_{C}(c, d)$$

natural in $d: C$, and which preserves the identity. As the Grothendieck construction of $\mathrm{hom}_{C}(c, \underline{\hspace{1cm}})$ is $\mathbf{F}h_{c}^{C}$ according to proposition 6.2.1.10, the morphism

$$\int_{C} \psi_{c}: \mathbf{F}h_{c}^{C} \to \mathbf{F}h_{c}^{C}$$

is characterized by its value on $\{id_{c}\}$ and is then the identity. This implies that $\psi_{c}$ is the identity. By two out of three, this implies that $\mathrm{hom}_{y}(c, \underline{\hspace{1cm}})$ also is an equivalence, which concludes the proof.

341