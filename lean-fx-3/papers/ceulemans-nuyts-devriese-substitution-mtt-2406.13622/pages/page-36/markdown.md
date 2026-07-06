36

A Substitution Algorithm for Multimode Type Theory: Technical Report

CASE \(\vdash_{\mathrm{ws}}\) id sub(Γ → Γ) @ m (WSMTT-SUB-ID)

By the definition of translation and embedding, we immediately have embed([id]) = id.

CASE \(\vdash_{\mathrm{ws}}\pi \operatorname {sub}(\hat{\Gamma}.\mu \to \hat{\Gamma})@n\) (WSMTT-SUB-WEAKEN)

Now we have that

\[
\operatorname{embed} ([ \pi ]) = \operatorname{embed} (\mathrm{id} \circledast \text { weaken } (\mathrm{id} ^ {\mathrm{a}})) \quad \text {(Definition of [\_ ] and Equation (2))}
\]

\[
= \mathrm{id} \circ (\mathrm{id} \circ \pi). \quad \text {(Definition of embed} (\_))
\]

This last substitution is indeed \(\sigma\)-equivalent to \(\pi\) by WSMTT-EQ-SUB-ID-LEFT.

CASE \(\vdash_{\mathrm{ws}}\sigma \circ \tau \operatorname {sub}(\hat{\Gamma}\to \hat{\Xi})@m\) (WSMTT-SUB-COMPOSE)

Now we compute that  \( \text{embed}([\sigma \circ \tau]) = \text{embed}([\sigma] + [\tau]) \) . Since the embedding of a sequence of atomic SFMTT substitutions is the composition of the embedding of these atomic substitutions and since WSMTT substitution composition is associative up to  \( \sigma \) -equivalence, we have that  \( \text{embed}([\sigma] + [\tau]) \equiv^{\sigma} \text{embed}([\sigma]) \circ \text{embed}([\tau]) \) . From this the result follows via the induction hypothesis applied to  \( \sigma \)  and  \( \tau \) .

CASE \(\vdash_{\mathrm{ws}}\sigma .\widehat{\mathbf{\Omega}}_{\mu}\operatorname {sub}(\hat{\Gamma}.\widehat{\mathbf{\Omega}}_{\mu}\to \hat{\Delta}.\widehat{\mathbf{\Omega}}_{\mu})@m\) (WSMTT-SUB-LOCK)

In this case we get that  \( \text{embed}([\sigma, \widehat{\mathbf{\Omega}}_{\mu}]) = \text{embed}([\sigma], \widehat{\mathbf{\Omega}}_{\mu}) \equiv^{\sigma} \text{embed}([\sigma]) \cdot \widehat{\mathbf{\Omega}}_{\mu} \) , where the last equivalence follows from WSMTT-EQ-SUB-LOCK-ID and WSMTT-EQ-SUB-LOCK-COMPOSE. The desired result is then a consequence of the induction hypothesis applied to  \( \sigma \) .

CASE \(\vdash_{\mathrm{ws}}\mathbf{Q}_{\hat{\Gamma}}^{\alpha \in \Theta \Rightarrow \Psi}\operatorname {sub}(\hat{\Gamma}.\Psi \to \hat{\Gamma}.\Theta)\) @ \(n\) (WSMTT-SUB-KEY)

We can now compute that

\[
\operatorname{embed} \left(\llbracket \mathbf {Q} _ {\hat {\Gamma}} ^ {\alpha \in \Theta \Rightarrow \Psi} \rrbracket\right) = \operatorname{embed} \left(\mathrm{id} \circledast \mathbf {Q} _ {\hat {\Gamma}} ^ {\alpha \in \Theta \Rightarrow \Psi}\right) \quad (\text { Definition   of } [ \_ ])
\]

\[
= \mathrm{id} \circ \mathbf {Q} _ {\hat {\Gamma}} ^ {\alpha \in \Theta \Rightarrow \Psi}, \quad (\text { Definition   of   embed } (\_))
\]

which is indeed \(\sigma\)-equivalent to \(\mathbf{Q}_{\hat{\Gamma}}^{\alpha \in \Theta \Rightarrow \Psi}\) because of WSMTT-EQ-SUB-ID-LEFT

CASE \(\vdash_{\mathrm{ws}}\sigma .t\) sub(Γ → Δ.μ) @ n (WSMTT-SUB-EXTEND)

Expanding the definitions of  \( [\_] \)  and embed( \( \_ \) ), we have that

\[
\operatorname{embed} ([ \sigma . t ]) = \operatorname{embed} \left(\llbracket \sigma \rrbracket^ {+} \circledast (\mathrm{id} ^ {\mathrm{a}}, [ [ t ] ])\right) = \operatorname{embed} \left(\llbracket \sigma \rrbracket^ {+}\right) \circ (\mathrm{id.embed} ([ [ t ] ])).
\]

By Lemma 27 we know that \(\mathsf{embed}\left(\llbracket \sigma \rrbracket^{+}\right) \equiv^{\sigma} \mathsf{embed}(\llbracket \sigma \rrbracket)^{+}\) and combining this with the induction hypothesis for \(\sigma\) and \(t\), we get that

\[
\operatorname{embed} ([ \sigma . t ]) \equiv^ {\sigma} \sigma^ {+} \circ (\mathrm{id}. t).
\]

This last substitution can be proven \(\sigma\)-equivalent to \(\sigma.t\) by the rules WSMTT-EQ-SUB-EXTEND-ETA, WSMTT-EQ-SUB-EXTEND-WEAKEN and WSMTT-EQ-EXPR-EXTEND-VAR.

## References

1 Joris Ceulemans, Andreas Nuyts, and Dominique Devriese. A sound and complete substitution algorithm for multimode type theory. In Delia Kesner, Eduardo Hermo Reyes, and Benno van den Berg, editors, 29th International Conference on Types for Proofs and Programs (TYPES 2023), volume 303 of LIPIcs, 2024. to appear.

2 Daniel Gratzer, G. A. Kavvos, Andreas Nuyts, and Lars Birkedal. Multimodal Dependent Type Theory. Logical Methods in Computer Science, Volume 17, Issue 3, July 2021. URL: https://lmcs.episciences.org/7713, doi:10.46298/lmcs-17(3:11)2021.