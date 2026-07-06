(iii) *pushouts*,
(iv) *colimits of sequences*,
(v) *retracts*.

*Proof.* For $X \in \mathcal{E}^D$, the functor $\operatorname{Hom}_{\operatorname{Psh}\mathcal{E}}(-, X)$ is not necessarily an adjoint. However, since split epimorphisms are closed under limits dual to the colimits listed above, it is sufficient to verify that it carries these colimits to limits. (In the case of tensors this means that $\operatorname{Hom}_{\operatorname{Psh}\mathcal{E}}(F \times A, X) \cong \operatorname{Hom}_{\operatorname{Psh}\mathcal{E}}(A, X)^{\mathcal{E}(-, F)}$ for all $F \in \mathcal{E}$.) This follows directly from these colimits being preserved by the tensors as recorded in Lemma 3.8. $\square$

**Definition 3.10.** Let $A \in \mathcal{E}^D$. We say that $A$ is *finite* if the following hold:

(i) $\operatorname{Hom}_{\mathcal{E}}(A, X)$ exists for every $X \in \mathcal{E}^D$;
(ii) $\operatorname{Hom}_{\mathcal{E}}(A, -)$ preserves colimits of sequences of levelwise complemented inclusions;
(iii) $\operatorname{Hom}_{\mathcal{E}}(A, -)$ sends levelwise complemented inclusions to complemented inclusions.

The next lemma provides a supply of finite objects. For its statement, recall the functor $S \mapsto \underline{S}$ from Section 2. As Lemma 3.3, it is formulated using $D^{\mathrm{op}}$ instead of $D$ for convenience.

**Lemma 3.11.** *Let $D$ be a locally countable category and assume that presheaf $A \in \operatorname{Psh} D$ is a finite colimit of representables. Then $\underline{A} \in [D^{\mathrm{op}}, \mathcal{E}]$ is finite.*

*Proof.* First, note that since $D$ is locally countable, $A$ is levelwise countable and thus $\underline{A}$ exists. By part (ii) of Lemma 3.3, $\operatorname{Hom}_{\mathcal{E}}(\underline{A}, -)$ exists and is given by $\operatorname{ev}_A$ (evaluation at $A$). Call $X \in \operatorname{Psh} D$ $\mathcal{E}$-finite if it satisfies the conditions of Definition 3.10 with $\operatorname{Hom}_{\mathcal{E}}(X, -)$ replaced by $\operatorname{ev}_X$. Our goal then is to show that $A$ is $\mathcal{E}$-finite. This follows from the following observations:

- Representables are $\mathcal{E}$-finite. For this, recall that evaluation at a representable is given by evaluation at the representing object. Part (ii) uses part (ii) of Corollary 2.12 to see that the colimit is computed levelwise.
- $\mathcal{E}$-finite presheaves are closed under finite colimits. For this, we use that the partial two-variable functor $\operatorname{ev}$ sends colimits in its first argument to limits. Part (i) holds since $\mathcal{E}$ has finite limits. Part (ii) holds since finite limits preserve colimits of sequences of complemented inclusions in $\mathcal{E}$ (Lemma 2.11). Part (iii) holds since complemented inclusions in $\mathcal{E}$ are closed under finite limits (part (ii) of Lemma 2.10). $\square$

The hypothesis of finiteness is used in the next result, where we use the notion of an $I$-fibration in the sense of Definition 3.2.

**Lemma 3.12.** *Assume that the domains and codomains of morphisms of $I$ are finite. Let $Y \in \mathcal{E}^D$ and $(X_k \to X_{k+1} \mid k \in \mathbb{N})$ be a sequence of morphisms in $\mathcal{E}^D \downarrow Y$. If every $X_k \to X_{k+1}$ is a levelwise complemented inclusion and each $p_k: X_k \to Y$ has $X_{k+1}$-partial enriched right lifting property with respect to $I$, then $\operatorname{colim}_k X_k \to Y$ is an $I$-fibration.*

19