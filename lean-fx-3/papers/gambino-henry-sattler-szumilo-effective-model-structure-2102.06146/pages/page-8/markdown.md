(F1) $\mathfrak{s}\mathcal{E}$ has a terminal object and all objects are fibrant, which follows directly from the definitions.

(F2) Pullbacks along fibrations exist because $\mathcal{E}$ (and hence $\mathfrak{s}\mathcal{E}$) has all finite limits. Moreover, fibrations and acyclic fibrations are closed under pullback by point (ii) of Lemma 1.5.

(F3) Every morphism factors as a weak equivalence followed by a fibration. By [Bro73, p. 421, Factorization lemma] it suffices to construct a path object, i.e., a factorisation of the diagonal $X \rightarrow X \times X$. Such factorisation is given by the cotensor $X \rightarrow \Delta[1] \pitchfork X \rightarrow X \times X$. Applying $\operatorname{Hom}_{\mathfrak{s}\text{Set}}(E, -)$ to this factorisation gives

$$\operatorname{Hom}_{\mathfrak{s}\text{Set}}(E, X) \rightarrow \Delta[1] \pitchfork \operatorname{Hom}_{\mathfrak{s}\text{Set}}(E, X) \rightarrow \operatorname{Hom}_{\mathfrak{s}\text{Set}}(E, X) \times \operatorname{Hom}_{\mathfrak{s}\text{Set}}(E, X)$$

which is a well known factorisation of the diagonal of $\operatorname{Hom}_{\mathfrak{s}\text{Set}}(E, X)$ into a weak equivalence followed by a fibration in $\mathfrak{s}\text{Set}$ (since $\operatorname{Hom}_{\mathfrak{s}\text{Set}}(E, X)$ is a Kan complex by Proposition 1.4). See, e.g., [GJ99, p. 43]. Hence $X \rightarrow \Delta[1] \pitchfork X \rightarrow X \times X$ is also such factorisation in $\mathfrak{s}\mathcal{E}$.

(F4) Weak equivalences satisfy 2-out-of-6, which follows since this property holds in $\mathfrak{s}\text{Set}$. $\square$

In view of our development in Section 8, we generalise Theorem 1.7 to the case of a slice of $\mathfrak{s}\mathcal{E}$ over a simplicial object $X$, which we write $\mathfrak{s}\mathcal{E} \downarrow X$. We then define $\mathfrak{s}\mathcal{E} \downarrow X$ to be the full subcategory of $\mathfrak{s}\mathcal{E} \downarrow X$ spanned by the fibrations over $X$.

First of all, let us recall that the enrichment of $\mathfrak{s}\mathcal{E}$ in simplicial sets, including the cotensor with finite simplicial sets, descends to its slices. For $(A, f), (B, g) \in \mathfrak{s}\mathcal{E} \downarrow X$, the hom-object $\operatorname{Hom}_{\mathfrak{s}\text{Set}}((A, f), (B, g))$ is the pullback of $\operatorname{Hom}_{\mathfrak{s}\text{Set}}(A, B)$ along the map $f: 1 \rightarrow \operatorname{Hom}_{\mathfrak{s}\text{Set}}(A, X)$. The cotensor of $(A, f) \in \mathfrak{s}\mathcal{E} \downarrow X$ by a finite simplicial set $K$ is the pullback of $K \pitchfork A$ along the map $X \rightarrow K \pitchfork X$ (using the fact that the monoidal unit in $\mathfrak{s}\text{Set}$ is the terminal object). As before, for each $E$, the functor $\operatorname{Hom}_{\mathfrak{s}\text{Set}}(E, -): \mathfrak{s}\mathcal{E} \downarrow X \rightarrow \mathfrak{s}\text{Set} \downarrow \operatorname{Hom}_{\mathfrak{s}\text{Set}}(E, X)$ preserves these cotensors.

**Lemma 1.8.** *Let $X \in \mathfrak{s}\mathcal{E}$. The pullback cotensor properties in part (i) of Lemma 1.5 hold in $\mathfrak{s}\mathcal{E} \downarrow X$ as well.*

*Proof.* This follows from their validity in $\mathfrak{s}\mathcal{E}$, i.e., part (i) of Lemma 1.5 and the stability of fibrations and trivial fibration under pullback, i.e., part (ii) of Lemma 1.5. $\square$

**Theorem 1.9.** *Let $X \in \mathfrak{s}\mathcal{E}$. Then pointwise weak equivalences, fibrations and trivial fibrations equip the category $\mathfrak{s}\mathcal{E} \downarrow X$ with the structure of a fibration category.*

*Proof.* All axioms are verified by the same argument as in the proof of Theorem 1.7. For (F3), we use Lemma 1.8 which is a fiberwise version of part (i) of Lemma 1.5 used in the proof of Theorem 1.7. $\square$

We conclude this section with a basic observation on homotopy equivalences.

**Proposition 1.10.** *Homotopy equivalences in $\mathfrak{s}\mathcal{E}$ (and in particular, in $\mathfrak{s}\mathcal{E} \downarrow X$ for all $X \in \mathfrak{s}\mathcal{E}$) are pointwise weak equivalences.*

*Proof.* The functors $\operatorname{Hom}_{\mathfrak{s}\text{Set}}(E, -)$ preserve homotopies and hence also homotopy equivalences. Thus the conclusion follows from the fact that homotopy equivalences are weak equivalences in $\mathfrak{s}\text{Set}$. $\square$

8