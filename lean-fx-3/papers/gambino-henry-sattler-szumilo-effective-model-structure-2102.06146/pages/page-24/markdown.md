*Proof.* First, because of Lemma 3.8, all $I_D$-cofibrations are levelwise complemented inclusions, so their image under $F$ are again levelwise complemented inclusions and hence pushouts along them exist. This shows that $\widehat{\mathrm{app}}(\lambda, i)$ always exists when $i$ is an $I_D$-cofibration.

By Proposition 3.17, a general a $I_D$-cofibration is a retract of a sequential composite of pushouts of countable coproducts of the form $E \times A \rightarrow E \times B$ for a map $A \rightarrow B$ in $I_D$ and $E \in \mathcal{E}$. A map $E \times i: E \times A \rightarrow E \times B$ is sent by $\widehat{\mathrm{app}}(\lambda, -)$ to the map $E \times \widehat{\mathrm{app}}(\lambda, i)$, so as we are assuming that for each $i \in I_D$ the map $\widehat{\mathrm{app}}(\lambda, i)$ is an $I_{D'}$-cofibration, it follows that the map of the form $E \times i$ are also sent to $I_{D'}$-cofibration.

Using Lemma 3.19 one concludes that any transfinite composition of pushouts of maps of the form $E \times i$ for $i \in I_D$ is also sent by $\widehat{\mathrm{app}}(\lambda, -)$ to a $I_{D'}$-cofibration. Finally, as $\widehat{\mathrm{app}}(\lambda, -)$ is a functor it preserves retract, and so retracts of such maps are also sent to $I_{D'}$-cofibration, and this concludes the proof as any $I_D$-cofibration is a retract of such a transfinite composition of pushouts. $\square$

**Proposition 3.21.** *Let $j: X \rightarrow Y$ be a morphism of $\mathcal{E}^D$. Under the hypothesis of Theorem 3.14, if $i \times j$ is an $I$-cofibration for all $i \in I$, then $f \times j$ is an $I$-cofibration for all $I$-cofibrations $f$.*

*Proof.* We apply Lemma 3.20 to the natural transformation $- \times j: - \times X \rightarrow - \times Y$ of endofunctors on $\mathcal{E}^D$. Let us check the needed preservation properties of the endofunctor $- \times Z$ on $\mathcal{E}^D$ for $Z \in \mathcal{E}$. Preservation of levelwise complemented inclusions follows from preservation of complemented inclusions in $\mathcal{E}$ under product with a fixed object (a consequence of lextensivity). Preservation of the relevant colimits involving levelwise complemented inclusions is an instance of Corollary 2.12. Preservation of tensors with objects of $\mathcal{E}$ reduces to associativity and commutativity of products in $\mathcal{E}$; this is natural, so the map $- \times j: - \times X \rightarrow - \times Y$ respects the witnessing isomorphism as appropriate. $\square$

## 4 The two weak factorisation systems

In this section we consider a countably lextensive category $\mathcal{E}$. We construct two weak factorisation systems on the category $\mathfrak{s}\mathcal{E}$ of simplicial objects in $\mathcal{E}$ that will be proven to form a model structure in Section 9. Our main goal is to describe the resulting cofibrations in Theorem 4.6 which relies on identification of one of the factorisation systems as a Reedy factorisation system (Proposition 4.3). In our setting, the category $\mathfrak{s}\mathcal{E}$ has relatively few colimits and consequently much of this section is committed to discussion of the Reedy theory under these weak hypotheses.

We will use the enriched small object argument of Theorem 3.14 with the generating sets obtained by applying the partial functor of (2.2) to the sets of boundary inclusions and horn inclusions in (1.6), i.e.,

$$I_{\mathfrak{s}\mathcal{E}} = \{ \underline{\partial \Delta[n]} \rightarrow \underline{\Delta[n]} \mid n \geq 0 \} \text{ and } J_{\mathfrak{s}\mathcal{E}} = \{ \underline{\Lambda^k[n]} \rightarrow \underline{\Delta[n]} \mid n \geq k \geq 0, n > 0 \}.$$

We will refer to $\underline{\Delta[n]}$ as a simplex in $\mathfrak{s}\mathcal{E}$ and similarly for boundaries and horns. We say that a map in $\mathfrak{s}\mathcal{E}$ is a *cofibration* if it is a $I_{\mathfrak{s}\mathcal{E}}$-cofibration and that it is a *trivial cofibration* if it is a $J_{\mathfrak{s}\mathcal{E}}$-cofibration. Moreover, we note that notions of (Kan) fibrations and trivial (Kan) fibrations as introduced in Definition 1.3 coincide with the notions of $J_{\mathfrak{s}\mathcal{E}}$-fibrations and $I_{\mathfrak{s}\mathcal{E}}$-fibration.

**Proposition 4.1.** *Let $f: X \rightarrow Y$ be a map in $\mathfrak{s}\mathcal{E}$.*

- (i) $f$ is a *fibration* if and only if it is a $J_{\mathfrak{s}\mathcal{E}}$-fibration;
- (ii) $f$ is a *trivial fibration* if and only if it is a $I_{\mathfrak{s}\mathcal{E}}$-fibration.

24