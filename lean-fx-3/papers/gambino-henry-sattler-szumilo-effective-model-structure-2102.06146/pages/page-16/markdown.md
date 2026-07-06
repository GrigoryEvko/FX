- We say that $i$ has the $\mathcal{E}$-enriched left lifting property with respect to $p$ and that $p$ has the $\mathcal{E}$-enriched right lifting property with respect to $i$ if the induced pullback hom in (3.3) exists and is a split epimorphism in $\mathcal{E}$.

Since the Yoneda embedding is fully faithful and preserves pullbacks, as soon as all relevant $\mathcal{E}$-valued hom-objects exist, the $\text{Psh}\,\mathcal{E}$-enriched left lifting property and $\mathcal{E}$-enriched left lifting property are equivalent and $\text{Prob}_{\text{Psh}\,\mathcal{E}}(i,p)$ is represented by $\text{Prob}_{\mathcal{E}}(i,p)$.

In both $\text{Psh}\,\mathcal{E}$ and $\mathcal{E}$, the class of split epimorphisms is the right class of a weak factorization system, with left class given by complemented inclusions. As such, it enjoys a number of standard closure properties. Our notions of enriched lifting property are defined from this class via the pullback hom. Because of this, the classes of maps defined below by an $\text{Psh}\,\mathcal{E}$-enriched lifting property will inherit corresponding closure properties. For example, split epimorphisms are closed under retracts. Thus, classes of maps defined by an $\text{Psh}\,\mathcal{E}$-enriched lifting property are closed under retracts.

As is usual, we extend the terminology of enriched lifting properties from maps to classes of maps on either side by universal quantification.

**Definition 3.2.** Let $I = \{i : A_i \to B_i\}$ be a set of morphisms of $\mathcal{E}^D$.

- An (enriched) $I$-fibration is a morphism with the enriched right lifting property with respect to $I$.
- An (enriched) $I$-cofibration is a morphism with the enriched left lifting property with respect to $I$-fibrations.

When the left map of a $\text{Psh}\,\mathcal{E}$-enriched lifting problem comes from $\text{Set}^D$ via levelwise application of the operation in (2.2), we may simplify the lifting problem (assuming some technical conditions hold). Indeed, the pullback hom (3.3) reduces to a pullback evaluation. We record this in the next couple of statements, which are phrased using $D^{\text{op}}$ instead of $D$ in order to exploit the language of representable functors. We make use of the evaluation functor $\text{ev}_K : [D^{\text{op}}, \mathcal{E}] \to \mathcal{E}$ defined for finite colimits $K$ of representables by letting:

$$\text{ev}_K(X) = \int_{d \in D^{\text{op}}} X_d^{K_d}.$$

This generalises the evaluation functor defined in Eq. (1.4), which is the case $D = \Delta$. As in Remark 1.1, we may equivalently view $\text{ev}_K(X)$ as the $K$-weighted limit of $X$, which implies that $\text{ev}$ is a (partial) two-variable functor.

**Lemma 3.3.** Let $K \in [D^{\text{op}}, \text{Set}]$ be levelwise countable.

(i) There is an isomorphism $(E \times \underline{K})_d \cong K_d \cdot E$ natural in $K$, $E \in \mathcal{E}$, and $d \in D$.
(ii) Assume that $K$ is a finite colimit of representables. Then the hom-presheaf $\text{Hom}_{\text{Psh}\,\mathcal{E}}(\underline{K}, X)$ is representable for $X \in [D^{\text{op}}, \mathcal{E}]$ and we have an isomorphism $\text{Hom}_{\mathcal{E}}(\underline{K}, X) \cong \text{ev}_K(X)$, natural in $K$ and $X \in [D^{\text{op}}, \mathcal{E}]$.

*Proof.* Part (i) follows from Lemma 2.6. For part (ii), part (i) implies that $\text{Hom}_{\text{Psh}\,\mathcal{E}}(\underline{K}, X)$ is naturally isomorphic to the $\mathcal{E}$-presheaf $E \mapsto \text{Hom}_{\text{Set}}(d \mapsto K_d \cdot E, X)$. A representing object for it is by definition the $K$-weighted limit of $X$, i.e., $\text{ev}_K(X)$. This exists in our setting for $K$ a finite colimit of representables. $\square$

16