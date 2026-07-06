**Proposition 3.4.** Let $i: A \to B$ be a map in $[D^{\text{op}}, \text{Set}]$ between objects that are levelwise countable and finite colimits of representables and let $p: X \to Y$ be a map in $[D^{\text{op}}, \mathcal{E}]$. Then the following are equivalent:

- (i) $\underline{i}: \underline{A} \to \underline{B}$ has the $\mathcal{E}$-enriched left lifting property with respect to $p$,
- (ii) the pullback evaluation $\widehat{\text{ev}}_i(p)$ is a split epimorphism in $\mathcal{E}$.

*Proof.* This is an immediate consequence of part (ii) of Lemma 3.3. $\square$

Proposition 3.4 will be used in Section 4 to relate (trivial) Kan fibrations in $\mathfrak{s}\mathcal{E}$ in the sense of Definition 1.3 with fibrations in the sense of Definition 3.2 with respect to the images in $\mathfrak{s}\mathcal{E}$ of horn inclusions (boundary inclusions, respectively) under the operation $(-): \text{Set} \to \mathcal{E}$.

We now turn our attention to $\text{Psh}\mathcal{E}$-enriched weak factorisation systems.

**Definition 3.5.** A $\text{Psh}\mathcal{E}$-enriched weak factorisation system on $\mathcal{E}^D$ is a pair $(\mathcal{L}, \mathcal{R})$ of classes of morphisms of $\mathcal{E}^D$ such that:

- a morphism belongs to $\mathcal{L}$ if and only if it has the $\text{Psh}\mathcal{E}$-enriched left lifting property with respect to $\mathcal{R}$;
- a morphism belongs to $\mathcal{R}$ if and only if it has the $\text{Psh}\mathcal{E}$-enriched right lifting property with respect to $\mathcal{L}$;
- every morphism of $\mathcal{E}^D$ factors as an $\mathcal{L}$-morphism followed by an $\mathcal{R}$-morphism.

The classes $\mathcal{L}$ and $\mathcal{R}$ in the above definition are closed under retract as they are characterized by $\text{Psh}\mathcal{E}$-enriched lifting properties.

We will abbreviate “$\text{Psh}\mathcal{E}$-enriched lifting property” to “enriched lifting property”, but we will be explicit about cases where it coincides with the $\mathcal{E}$-enriched lifting property.

**Lemma 3.6.** Let $(\mathcal{L}, \mathcal{R})$ be an enriched weak factorisation system.

- (i) A morphism is in $\mathcal{L}$ if and only if it has the ordinary left lifting property with respect to $\mathcal{R}$.
- (ii) A morphism is in $\mathcal{R}$ if and only if it has the ordinary right lifting property with respect to $\mathcal{L}$.

In particular, $(\mathcal{L}, \mathcal{R})$ is also an ordinary weak factorisation system.

*Proof.* For (i), a morphism of $\mathcal{L}$ has the ordinary left lifting property with respect to $\mathcal{R}$ by evaluating the hom-presheaves at $1 \in \mathcal{E}$. Conversely, a morphism with the ordinary lifting property admits a lift against the second factor of its $(\mathcal{L}, \mathcal{R})$-factorisation, thus making it into a retract of the first factor (cf. also the proof of Proposition 3.17). The conclusion follows since $\mathcal{L}$ is closed under retracts. Part (ii) follows by duality. $\square$

We will fix a set $I$ and study a version of the small object argument that produces an enriched weak factorisation system of $I$-cofibrations and $I$-fibrations under suitable assumptions.

17